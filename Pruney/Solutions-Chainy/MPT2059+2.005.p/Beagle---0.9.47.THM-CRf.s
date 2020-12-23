%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:36 EST 2020

% Result     : Theorem 3.58s
% Output     : CNFRefutation 3.93s
% Verified   : 
% Statistics : Number of formulae       :  185 (2831 expanded)
%              Number of leaves         :   44 ( 985 expanded)
%              Depth                    :   19
%              Number of atoms          :  583 (11286 expanded)
%              Number of equality atoms :   13 ( 598 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_waybel_7 > v6_waybel_0 > v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_hidden > r1_tarski > m1_subset_1 > l1_waybel_0 > v7_waybel_0 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k3_yellow19 > k2_yellow19 > k10_yellow_6 > #nlpp > u1_struct_0 > k3_yellow_1 > k3_lattice3 > k2_struct_0 > k1_zfmisc_1 > k1_lattice3 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(v2_waybel_0,type,(
    v2_waybel_0: ( $i * $i ) > $o )).

tff(k10_yellow_6,type,(
    k10_yellow_6: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(v7_waybel_0,type,(
    v7_waybel_0: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_lattice3,type,(
    k1_lattice3: $i > $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

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

tff(r2_waybel_7,type,(
    r2_waybel_7: ( $i * $i * $i ) > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_yellow19,type,(
    k3_yellow19: ( $i * $i * $i ) > $i )).

tff(v13_waybel_0,type,(
    v13_waybel_0: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_206,negated_conjecture,(
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
               => ( r2_hidden(C,k10_yellow_6(A,k3_yellow19(A,k2_struct_0(A),B)))
                <=> r2_waybel_7(A,B,C) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_yellow19)).

tff(f_44,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_40,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_52,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_36,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_108,axiom,(
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

tff(f_136,axiom,(
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

tff(f_80,axiom,(
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

tff(f_179,axiom,(
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

tff(f_160,axiom,(
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
             => ( r2_hidden(C,k10_yellow_6(A,B))
              <=> r2_waybel_7(A,k2_yellow19(A,B),C) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_yellow19)).

tff(c_58,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_14,plain,(
    ! [A_9] :
      ( l1_struct_0(A_9)
      | ~ l1_pre_topc(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_81,plain,(
    ! [A_37] :
      ( u1_struct_0(A_37) = k2_struct_0(A_37)
      | ~ l1_struct_0(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_86,plain,(
    ! [A_38] :
      ( u1_struct_0(A_38) = k2_struct_0(A_38)
      | ~ l1_pre_topc(A_38) ) ),
    inference(resolution,[status(thm)],[c_14,c_81])).

tff(c_90,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_58,c_86])).

tff(c_46,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_91,plain,(
    m1_subset_1('#skF_4',k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_46])).

tff(c_64,plain,
    ( ~ r2_waybel_7('#skF_2','#skF_3','#skF_4')
    | ~ r2_hidden('#skF_4',k10_yellow_6('#skF_2',k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_111,plain,(
    ~ r2_hidden('#skF_4',k10_yellow_6('#skF_2',k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_70,plain,
    ( r2_hidden('#skF_4',k10_yellow_6('#skF_2',k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3')))
    | r2_waybel_7('#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_139,plain,(
    r2_waybel_7('#skF_2','#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_111,c_70])).

tff(c_62,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_106,plain,(
    ! [A_43] :
      ( ~ v1_xboole_0(u1_struct_0(A_43))
      | ~ l1_struct_0(A_43)
      | v2_struct_0(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_109,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_2'))
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_106])).

tff(c_110,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_2'))
    | ~ l1_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_109])).

tff(c_112,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_110])).

tff(c_115,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_14,c_112])).

tff(c_119,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_115])).

tff(c_120,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_110])).

tff(c_56,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_121,plain,(
    l1_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_110])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_128,plain,(
    ! [A_46,B_47] :
      ( ~ r2_hidden('#skF_1'(A_46,B_47),B_47)
      | r1_tarski(A_46,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_133,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_128])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(A_6,k1_zfmisc_1(B_7))
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_52,plain,(
    v2_waybel_0('#skF_3',k3_yellow_1(k2_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_50,plain,(
    v13_waybel_0('#skF_3',k3_yellow_1(k2_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_48,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2'))))) ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_196,plain,(
    ! [A_77,B_78,C_79] :
      ( v3_orders_2(k3_yellow19(A_77,B_78,C_79))
      | ~ m1_subset_1(C_79,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_78))))
      | ~ v13_waybel_0(C_79,k3_yellow_1(B_78))
      | ~ v2_waybel_0(C_79,k3_yellow_1(B_78))
      | v1_xboole_0(C_79)
      | ~ m1_subset_1(B_78,k1_zfmisc_1(u1_struct_0(A_77)))
      | v1_xboole_0(B_78)
      | ~ l1_struct_0(A_77)
      | v2_struct_0(A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_201,plain,(
    ! [A_77] :
      ( v3_orders_2(k3_yellow19(A_77,k2_struct_0('#skF_2'),'#skF_3'))
      | ~ v13_waybel_0('#skF_3',k3_yellow_1(k2_struct_0('#skF_2')))
      | ~ v2_waybel_0('#skF_3',k3_yellow_1(k2_struct_0('#skF_2')))
      | v1_xboole_0('#skF_3')
      | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0(A_77)))
      | v1_xboole_0(k2_struct_0('#skF_2'))
      | ~ l1_struct_0(A_77)
      | v2_struct_0(A_77) ) ),
    inference(resolution,[status(thm)],[c_48,c_196])).

tff(c_205,plain,(
    ! [A_77] :
      ( v3_orders_2(k3_yellow19(A_77,k2_struct_0('#skF_2'),'#skF_3'))
      | v1_xboole_0('#skF_3')
      | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0(A_77)))
      | v1_xboole_0(k2_struct_0('#skF_2'))
      | ~ l1_struct_0(A_77)
      | v2_struct_0(A_77) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_201])).

tff(c_207,plain,(
    ! [A_80] :
      ( v3_orders_2(k3_yellow19(A_80,k2_struct_0('#skF_2'),'#skF_3'))
      | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0(A_80)))
      | ~ l1_struct_0(A_80)
      | v2_struct_0(A_80) ) ),
    inference(negUnitSimplification,[status(thm)],[c_120,c_56,c_205])).

tff(c_213,plain,
    ( v3_orders_2(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'))
    | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_2')))
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_207])).

tff(c_216,plain,
    ( v3_orders_2(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'))
    | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_2')))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_213])).

tff(c_217,plain,
    ( v3_orders_2(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'))
    | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_216])).

tff(c_218,plain,(
    ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_217])).

tff(c_221,plain,(
    ~ r1_tarski(k2_struct_0('#skF_2'),k2_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_10,c_218])).

tff(c_225,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_221])).

tff(c_227,plain,(
    m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_217])).

tff(c_60,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_228,plain,(
    ! [A_81,B_82,C_83] :
      ( v4_orders_2(k3_yellow19(A_81,B_82,C_83))
      | ~ m1_subset_1(C_83,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_82))))
      | ~ v13_waybel_0(C_83,k3_yellow_1(B_82))
      | ~ v2_waybel_0(C_83,k3_yellow_1(B_82))
      | v1_xboole_0(C_83)
      | ~ m1_subset_1(B_82,k1_zfmisc_1(u1_struct_0(A_81)))
      | v1_xboole_0(B_82)
      | ~ l1_struct_0(A_81)
      | v2_struct_0(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_233,plain,(
    ! [A_81] :
      ( v4_orders_2(k3_yellow19(A_81,k2_struct_0('#skF_2'),'#skF_3'))
      | ~ v13_waybel_0('#skF_3',k3_yellow_1(k2_struct_0('#skF_2')))
      | ~ v2_waybel_0('#skF_3',k3_yellow_1(k2_struct_0('#skF_2')))
      | v1_xboole_0('#skF_3')
      | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0(A_81)))
      | v1_xboole_0(k2_struct_0('#skF_2'))
      | ~ l1_struct_0(A_81)
      | v2_struct_0(A_81) ) ),
    inference(resolution,[status(thm)],[c_48,c_228])).

tff(c_237,plain,(
    ! [A_81] :
      ( v4_orders_2(k3_yellow19(A_81,k2_struct_0('#skF_2'),'#skF_3'))
      | v1_xboole_0('#skF_3')
      | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0(A_81)))
      | v1_xboole_0(k2_struct_0('#skF_2'))
      | ~ l1_struct_0(A_81)
      | v2_struct_0(A_81) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_233])).

tff(c_256,plain,(
    ! [A_85] :
      ( v4_orders_2(k3_yellow19(A_85,k2_struct_0('#skF_2'),'#skF_3'))
      | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0(A_85)))
      | ~ l1_struct_0(A_85)
      | v2_struct_0(A_85) ) ),
    inference(negUnitSimplification,[status(thm)],[c_120,c_56,c_237])).

tff(c_262,plain,
    ( v4_orders_2(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'))
    | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_2')))
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_256])).

tff(c_265,plain,
    ( v4_orders_2(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_227,c_262])).

tff(c_266,plain,(
    v4_orders_2(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_265])).

tff(c_54,plain,(
    v1_subset_1('#skF_3',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_368,plain,(
    ! [A_102,B_103,C_104] :
      ( v7_waybel_0(k3_yellow19(A_102,B_103,C_104))
      | ~ m1_subset_1(C_104,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_103))))
      | ~ v13_waybel_0(C_104,k3_yellow_1(B_103))
      | ~ v2_waybel_0(C_104,k3_yellow_1(B_103))
      | ~ v1_subset_1(C_104,u1_struct_0(k3_yellow_1(B_103)))
      | v1_xboole_0(C_104)
      | ~ m1_subset_1(B_103,k1_zfmisc_1(u1_struct_0(A_102)))
      | v1_xboole_0(B_103)
      | ~ l1_struct_0(A_102)
      | v2_struct_0(A_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_373,plain,(
    ! [A_102] :
      ( v7_waybel_0(k3_yellow19(A_102,k2_struct_0('#skF_2'),'#skF_3'))
      | ~ v13_waybel_0('#skF_3',k3_yellow_1(k2_struct_0('#skF_2')))
      | ~ v2_waybel_0('#skF_3',k3_yellow_1(k2_struct_0('#skF_2')))
      | ~ v1_subset_1('#skF_3',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2'))))
      | v1_xboole_0('#skF_3')
      | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0(A_102)))
      | v1_xboole_0(k2_struct_0('#skF_2'))
      | ~ l1_struct_0(A_102)
      | v2_struct_0(A_102) ) ),
    inference(resolution,[status(thm)],[c_48,c_368])).

tff(c_377,plain,(
    ! [A_102] :
      ( v7_waybel_0(k3_yellow19(A_102,k2_struct_0('#skF_2'),'#skF_3'))
      | v1_xboole_0('#skF_3')
      | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0(A_102)))
      | v1_xboole_0(k2_struct_0('#skF_2'))
      | ~ l1_struct_0(A_102)
      | v2_struct_0(A_102) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_373])).

tff(c_379,plain,(
    ! [A_105] :
      ( v7_waybel_0(k3_yellow19(A_105,k2_struct_0('#skF_2'),'#skF_3'))
      | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0(A_105)))
      | ~ l1_struct_0(A_105)
      | v2_struct_0(A_105) ) ),
    inference(negUnitSimplification,[status(thm)],[c_120,c_56,c_377])).

tff(c_385,plain,
    ( v7_waybel_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'))
    | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_2')))
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_379])).

tff(c_388,plain,
    ( v7_waybel_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_227,c_385])).

tff(c_389,plain,(
    v7_waybel_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_388])).

tff(c_280,plain,(
    ! [A_87,B_88,C_89] :
      ( l1_waybel_0(k3_yellow19(A_87,B_88,C_89),A_87)
      | ~ m1_subset_1(C_89,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_88))))
      | ~ v13_waybel_0(C_89,k3_yellow_1(B_88))
      | ~ v2_waybel_0(C_89,k3_yellow_1(B_88))
      | v1_xboole_0(C_89)
      | ~ m1_subset_1(B_88,k1_zfmisc_1(u1_struct_0(A_87)))
      | v1_xboole_0(B_88)
      | ~ l1_struct_0(A_87)
      | v2_struct_0(A_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_285,plain,(
    ! [A_87] :
      ( l1_waybel_0(k3_yellow19(A_87,k2_struct_0('#skF_2'),'#skF_3'),A_87)
      | ~ v13_waybel_0('#skF_3',k3_yellow_1(k2_struct_0('#skF_2')))
      | ~ v2_waybel_0('#skF_3',k3_yellow_1(k2_struct_0('#skF_2')))
      | v1_xboole_0('#skF_3')
      | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0(A_87)))
      | v1_xboole_0(k2_struct_0('#skF_2'))
      | ~ l1_struct_0(A_87)
      | v2_struct_0(A_87) ) ),
    inference(resolution,[status(thm)],[c_48,c_280])).

tff(c_289,plain,(
    ! [A_87] :
      ( l1_waybel_0(k3_yellow19(A_87,k2_struct_0('#skF_2'),'#skF_3'),A_87)
      | v1_xboole_0('#skF_3')
      | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0(A_87)))
      | v1_xboole_0(k2_struct_0('#skF_2'))
      | ~ l1_struct_0(A_87)
      | v2_struct_0(A_87) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_285])).

tff(c_291,plain,(
    ! [A_90] :
      ( l1_waybel_0(k3_yellow19(A_90,k2_struct_0('#skF_2'),'#skF_3'),A_90)
      | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0(A_90)))
      | ~ l1_struct_0(A_90)
      | v2_struct_0(A_90) ) ),
    inference(negUnitSimplification,[status(thm)],[c_120,c_56,c_289])).

tff(c_296,plain,
    ( l1_waybel_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'),'#skF_2')
    | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_2')))
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_291])).

tff(c_299,plain,
    ( l1_waybel_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'),'#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_227,c_296])).

tff(c_300,plain,(
    l1_waybel_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_299])).

tff(c_432,plain,(
    ! [A_112,B_113] :
      ( k2_yellow19(A_112,k3_yellow19(A_112,k2_struct_0(A_112),B_113)) = B_113
      | ~ m1_subset_1(B_113,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_112)))))
      | ~ v13_waybel_0(B_113,k3_yellow_1(k2_struct_0(A_112)))
      | ~ v2_waybel_0(B_113,k3_yellow_1(k2_struct_0(A_112)))
      | ~ v1_subset_1(B_113,u1_struct_0(k3_yellow_1(k2_struct_0(A_112))))
      | v1_xboole_0(B_113)
      | ~ l1_struct_0(A_112)
      | v2_struct_0(A_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_437,plain,
    ( k2_yellow19('#skF_2',k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3')) = '#skF_3'
    | ~ v13_waybel_0('#skF_3',k3_yellow_1(k2_struct_0('#skF_2')))
    | ~ v2_waybel_0('#skF_3',k3_yellow_1(k2_struct_0('#skF_2')))
    | ~ v1_subset_1('#skF_3',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2'))))
    | v1_xboole_0('#skF_3')
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_432])).

tff(c_441,plain,
    ( k2_yellow19('#skF_2',k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3')) = '#skF_3'
    | v1_xboole_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_54,c_52,c_50,c_437])).

tff(c_442,plain,(
    k2_yellow19('#skF_2',k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3')) = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_56,c_441])).

tff(c_42,plain,(
    ! [A_21,B_25,C_27] :
      ( r2_waybel_7(A_21,k2_yellow19(A_21,B_25),C_27)
      | ~ r2_hidden(C_27,k10_yellow_6(A_21,B_25))
      | ~ m1_subset_1(C_27,u1_struct_0(A_21))
      | ~ l1_waybel_0(B_25,A_21)
      | ~ v7_waybel_0(B_25)
      | ~ v4_orders_2(B_25)
      | v2_struct_0(B_25)
      | ~ l1_pre_topc(A_21)
      | ~ v2_pre_topc(A_21)
      | v2_struct_0(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_446,plain,(
    ! [C_27] :
      ( r2_waybel_7('#skF_2','#skF_3',C_27)
      | ~ r2_hidden(C_27,k10_yellow_6('#skF_2',k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3')))
      | ~ m1_subset_1(C_27,u1_struct_0('#skF_2'))
      | ~ l1_waybel_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'),'#skF_2')
      | ~ v7_waybel_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'))
      | ~ v4_orders_2(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'))
      | v2_struct_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_442,c_42])).

tff(c_453,plain,(
    ! [C_27] :
      ( r2_waybel_7('#skF_2','#skF_3',C_27)
      | ~ r2_hidden(C_27,k10_yellow_6('#skF_2',k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3')))
      | ~ m1_subset_1(C_27,k2_struct_0('#skF_2'))
      | v2_struct_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_266,c_389,c_300,c_90,c_446])).

tff(c_454,plain,(
    ! [C_27] :
      ( r2_waybel_7('#skF_2','#skF_3',C_27)
      | ~ r2_hidden(C_27,k10_yellow_6('#skF_2',k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3')))
      | ~ m1_subset_1(C_27,k2_struct_0('#skF_2'))
      | v2_struct_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_453])).

tff(c_459,plain,(
    v2_struct_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_454])).

tff(c_32,plain,(
    ! [A_15,B_16,C_17] :
      ( ~ v2_struct_0(k3_yellow19(A_15,B_16,C_17))
      | ~ m1_subset_1(C_17,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_16))))
      | ~ v13_waybel_0(C_17,k3_yellow_1(B_16))
      | ~ v2_waybel_0(C_17,k3_yellow_1(B_16))
      | v1_xboole_0(C_17)
      | ~ m1_subset_1(B_16,k1_zfmisc_1(u1_struct_0(A_15)))
      | v1_xboole_0(B_16)
      | ~ l1_struct_0(A_15)
      | v2_struct_0(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_461,plain,
    ( ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2')))))
    | ~ v13_waybel_0('#skF_3',k3_yellow_1(k2_struct_0('#skF_2')))
    | ~ v2_waybel_0('#skF_3',k3_yellow_1(k2_struct_0('#skF_2')))
    | v1_xboole_0('#skF_3')
    | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v1_xboole_0(k2_struct_0('#skF_2'))
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_459,c_32])).

tff(c_464,plain,
    ( v1_xboole_0('#skF_3')
    | v1_xboole_0(k2_struct_0('#skF_2'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_227,c_90,c_52,c_50,c_48,c_461])).

tff(c_466,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_120,c_56,c_464])).

tff(c_468,plain,(
    ~ v2_struct_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3')) ),
    inference(splitRight,[status(thm)],[c_454])).

tff(c_40,plain,(
    ! [C_27,A_21,B_25] :
      ( r2_hidden(C_27,k10_yellow_6(A_21,B_25))
      | ~ r2_waybel_7(A_21,k2_yellow19(A_21,B_25),C_27)
      | ~ m1_subset_1(C_27,u1_struct_0(A_21))
      | ~ l1_waybel_0(B_25,A_21)
      | ~ v7_waybel_0(B_25)
      | ~ v4_orders_2(B_25)
      | v2_struct_0(B_25)
      | ~ l1_pre_topc(A_21)
      | ~ v2_pre_topc(A_21)
      | v2_struct_0(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_449,plain,(
    ! [C_27] :
      ( r2_hidden(C_27,k10_yellow_6('#skF_2',k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3')))
      | ~ r2_waybel_7('#skF_2','#skF_3',C_27)
      | ~ m1_subset_1(C_27,u1_struct_0('#skF_2'))
      | ~ l1_waybel_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'),'#skF_2')
      | ~ v7_waybel_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'))
      | ~ v4_orders_2(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'))
      | v2_struct_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_442,c_40])).

tff(c_456,plain,(
    ! [C_27] :
      ( r2_hidden(C_27,k10_yellow_6('#skF_2',k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3')))
      | ~ r2_waybel_7('#skF_2','#skF_3',C_27)
      | ~ m1_subset_1(C_27,k2_struct_0('#skF_2'))
      | v2_struct_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_266,c_389,c_300,c_90,c_449])).

tff(c_457,plain,(
    ! [C_27] :
      ( r2_hidden(C_27,k10_yellow_6('#skF_2',k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3')))
      | ~ r2_waybel_7('#skF_2','#skF_3',C_27)
      | ~ m1_subset_1(C_27,k2_struct_0('#skF_2'))
      | v2_struct_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_456])).

tff(c_469,plain,(
    v2_struct_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_457])).

tff(c_470,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_468,c_469])).

tff(c_473,plain,(
    ! [C_114] :
      ( r2_hidden(C_114,k10_yellow_6('#skF_2',k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3')))
      | ~ r2_waybel_7('#skF_2','#skF_3',C_114)
      | ~ m1_subset_1(C_114,k2_struct_0('#skF_2')) ) ),
    inference(splitRight,[status(thm)],[c_457])).

tff(c_476,plain,
    ( ~ r2_waybel_7('#skF_2','#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_4',k2_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_473,c_111])).

tff(c_486,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_139,c_476])).

tff(c_487,plain,(
    ~ r2_waybel_7('#skF_2','#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_504,plain,(
    r2_hidden('#skF_4',k10_yellow_6('#skF_2',k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_487,c_70])).

tff(c_489,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_110])).

tff(c_492,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_14,c_489])).

tff(c_496,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_492])).

tff(c_497,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_110])).

tff(c_498,plain,(
    l1_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_110])).

tff(c_506,plain,(
    ! [A_117,B_118] :
      ( ~ r2_hidden('#skF_1'(A_117,B_118),B_118)
      | r1_tarski(A_117,B_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_511,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_506])).

tff(c_589,plain,(
    ! [A_146,B_147,C_148] :
      ( v3_orders_2(k3_yellow19(A_146,B_147,C_148))
      | ~ m1_subset_1(C_148,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_147))))
      | ~ v13_waybel_0(C_148,k3_yellow_1(B_147))
      | ~ v2_waybel_0(C_148,k3_yellow_1(B_147))
      | v1_xboole_0(C_148)
      | ~ m1_subset_1(B_147,k1_zfmisc_1(u1_struct_0(A_146)))
      | v1_xboole_0(B_147)
      | ~ l1_struct_0(A_146)
      | v2_struct_0(A_146) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_594,plain,(
    ! [A_146] :
      ( v3_orders_2(k3_yellow19(A_146,k2_struct_0('#skF_2'),'#skF_3'))
      | ~ v13_waybel_0('#skF_3',k3_yellow_1(k2_struct_0('#skF_2')))
      | ~ v2_waybel_0('#skF_3',k3_yellow_1(k2_struct_0('#skF_2')))
      | v1_xboole_0('#skF_3')
      | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0(A_146)))
      | v1_xboole_0(k2_struct_0('#skF_2'))
      | ~ l1_struct_0(A_146)
      | v2_struct_0(A_146) ) ),
    inference(resolution,[status(thm)],[c_48,c_589])).

tff(c_598,plain,(
    ! [A_146] :
      ( v3_orders_2(k3_yellow19(A_146,k2_struct_0('#skF_2'),'#skF_3'))
      | v1_xboole_0('#skF_3')
      | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0(A_146)))
      | v1_xboole_0(k2_struct_0('#skF_2'))
      | ~ l1_struct_0(A_146)
      | v2_struct_0(A_146) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_594])).

tff(c_600,plain,(
    ! [A_149] :
      ( v3_orders_2(k3_yellow19(A_149,k2_struct_0('#skF_2'),'#skF_3'))
      | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0(A_149)))
      | ~ l1_struct_0(A_149)
      | v2_struct_0(A_149) ) ),
    inference(negUnitSimplification,[status(thm)],[c_497,c_56,c_598])).

tff(c_606,plain,
    ( v3_orders_2(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'))
    | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_2')))
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_600])).

tff(c_609,plain,
    ( v3_orders_2(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'))
    | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_2')))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_498,c_606])).

tff(c_610,plain,
    ( v3_orders_2(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'))
    | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_609])).

tff(c_611,plain,(
    ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_610])).

tff(c_614,plain,(
    ~ r1_tarski(k2_struct_0('#skF_2'),k2_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_10,c_611])).

tff(c_618,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_511,c_614])).

tff(c_620,plain,(
    m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_610])).

tff(c_626,plain,(
    ! [A_150,B_151,C_152] :
      ( v4_orders_2(k3_yellow19(A_150,B_151,C_152))
      | ~ m1_subset_1(C_152,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_151))))
      | ~ v13_waybel_0(C_152,k3_yellow_1(B_151))
      | ~ v2_waybel_0(C_152,k3_yellow_1(B_151))
      | v1_xboole_0(C_152)
      | ~ m1_subset_1(B_151,k1_zfmisc_1(u1_struct_0(A_150)))
      | v1_xboole_0(B_151)
      | ~ l1_struct_0(A_150)
      | v2_struct_0(A_150) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_631,plain,(
    ! [A_150] :
      ( v4_orders_2(k3_yellow19(A_150,k2_struct_0('#skF_2'),'#skF_3'))
      | ~ v13_waybel_0('#skF_3',k3_yellow_1(k2_struct_0('#skF_2')))
      | ~ v2_waybel_0('#skF_3',k3_yellow_1(k2_struct_0('#skF_2')))
      | v1_xboole_0('#skF_3')
      | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0(A_150)))
      | v1_xboole_0(k2_struct_0('#skF_2'))
      | ~ l1_struct_0(A_150)
      | v2_struct_0(A_150) ) ),
    inference(resolution,[status(thm)],[c_48,c_626])).

tff(c_635,plain,(
    ! [A_150] :
      ( v4_orders_2(k3_yellow19(A_150,k2_struct_0('#skF_2'),'#skF_3'))
      | v1_xboole_0('#skF_3')
      | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0(A_150)))
      | v1_xboole_0(k2_struct_0('#skF_2'))
      | ~ l1_struct_0(A_150)
      | v2_struct_0(A_150) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_631])).

tff(c_649,plain,(
    ! [A_154] :
      ( v4_orders_2(k3_yellow19(A_154,k2_struct_0('#skF_2'),'#skF_3'))
      | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0(A_154)))
      | ~ l1_struct_0(A_154)
      | v2_struct_0(A_154) ) ),
    inference(negUnitSimplification,[status(thm)],[c_497,c_56,c_635])).

tff(c_655,plain,
    ( v4_orders_2(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'))
    | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_2')))
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_649])).

tff(c_658,plain,
    ( v4_orders_2(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_498,c_620,c_655])).

tff(c_659,plain,(
    v4_orders_2(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_658])).

tff(c_965,plain,(
    ! [A_210,B_211,C_212] :
      ( v7_waybel_0(k3_yellow19(A_210,B_211,C_212))
      | ~ m1_subset_1(C_212,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_211))))
      | ~ v13_waybel_0(C_212,k3_yellow_1(B_211))
      | ~ v2_waybel_0(C_212,k3_yellow_1(B_211))
      | ~ v1_subset_1(C_212,u1_struct_0(k3_yellow_1(B_211)))
      | v1_xboole_0(C_212)
      | ~ m1_subset_1(B_211,k1_zfmisc_1(u1_struct_0(A_210)))
      | v1_xboole_0(B_211)
      | ~ l1_struct_0(A_210)
      | v2_struct_0(A_210) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_970,plain,(
    ! [A_210] :
      ( v7_waybel_0(k3_yellow19(A_210,k2_struct_0('#skF_2'),'#skF_3'))
      | ~ v13_waybel_0('#skF_3',k3_yellow_1(k2_struct_0('#skF_2')))
      | ~ v2_waybel_0('#skF_3',k3_yellow_1(k2_struct_0('#skF_2')))
      | ~ v1_subset_1('#skF_3',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2'))))
      | v1_xboole_0('#skF_3')
      | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0(A_210)))
      | v1_xboole_0(k2_struct_0('#skF_2'))
      | ~ l1_struct_0(A_210)
      | v2_struct_0(A_210) ) ),
    inference(resolution,[status(thm)],[c_48,c_965])).

tff(c_974,plain,(
    ! [A_210] :
      ( v7_waybel_0(k3_yellow19(A_210,k2_struct_0('#skF_2'),'#skF_3'))
      | v1_xboole_0('#skF_3')
      | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0(A_210)))
      | v1_xboole_0(k2_struct_0('#skF_2'))
      | ~ l1_struct_0(A_210)
      | v2_struct_0(A_210) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_970])).

tff(c_976,plain,(
    ! [A_213] :
      ( v7_waybel_0(k3_yellow19(A_213,k2_struct_0('#skF_2'),'#skF_3'))
      | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0(A_213)))
      | ~ l1_struct_0(A_213)
      | v2_struct_0(A_213) ) ),
    inference(negUnitSimplification,[status(thm)],[c_497,c_56,c_974])).

tff(c_982,plain,
    ( v7_waybel_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'))
    | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_2')))
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_976])).

tff(c_985,plain,
    ( v7_waybel_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_498,c_620,c_982])).

tff(c_986,plain,(
    v7_waybel_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_985])).

tff(c_780,plain,(
    ! [A_176,B_177,C_178] :
      ( l1_waybel_0(k3_yellow19(A_176,B_177,C_178),A_176)
      | ~ m1_subset_1(C_178,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_177))))
      | ~ v13_waybel_0(C_178,k3_yellow_1(B_177))
      | ~ v2_waybel_0(C_178,k3_yellow_1(B_177))
      | v1_xboole_0(C_178)
      | ~ m1_subset_1(B_177,k1_zfmisc_1(u1_struct_0(A_176)))
      | v1_xboole_0(B_177)
      | ~ l1_struct_0(A_176)
      | v2_struct_0(A_176) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_785,plain,(
    ! [A_176] :
      ( l1_waybel_0(k3_yellow19(A_176,k2_struct_0('#skF_2'),'#skF_3'),A_176)
      | ~ v13_waybel_0('#skF_3',k3_yellow_1(k2_struct_0('#skF_2')))
      | ~ v2_waybel_0('#skF_3',k3_yellow_1(k2_struct_0('#skF_2')))
      | v1_xboole_0('#skF_3')
      | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0(A_176)))
      | v1_xboole_0(k2_struct_0('#skF_2'))
      | ~ l1_struct_0(A_176)
      | v2_struct_0(A_176) ) ),
    inference(resolution,[status(thm)],[c_48,c_780])).

tff(c_789,plain,(
    ! [A_176] :
      ( l1_waybel_0(k3_yellow19(A_176,k2_struct_0('#skF_2'),'#skF_3'),A_176)
      | v1_xboole_0('#skF_3')
      | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0(A_176)))
      | v1_xboole_0(k2_struct_0('#skF_2'))
      | ~ l1_struct_0(A_176)
      | v2_struct_0(A_176) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_785])).

tff(c_791,plain,(
    ! [A_179] :
      ( l1_waybel_0(k3_yellow19(A_179,k2_struct_0('#skF_2'),'#skF_3'),A_179)
      | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0(A_179)))
      | ~ l1_struct_0(A_179)
      | v2_struct_0(A_179) ) ),
    inference(negUnitSimplification,[status(thm)],[c_497,c_56,c_789])).

tff(c_796,plain,
    ( l1_waybel_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'),'#skF_2')
    | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_2')))
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_791])).

tff(c_799,plain,
    ( l1_waybel_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'),'#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_498,c_620,c_796])).

tff(c_800,plain,(
    l1_waybel_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_799])).

tff(c_1020,plain,(
    ! [A_226,B_227] :
      ( k2_yellow19(A_226,k3_yellow19(A_226,k2_struct_0(A_226),B_227)) = B_227
      | ~ m1_subset_1(B_227,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_226)))))
      | ~ v13_waybel_0(B_227,k3_yellow_1(k2_struct_0(A_226)))
      | ~ v2_waybel_0(B_227,k3_yellow_1(k2_struct_0(A_226)))
      | ~ v1_subset_1(B_227,u1_struct_0(k3_yellow_1(k2_struct_0(A_226))))
      | v1_xboole_0(B_227)
      | ~ l1_struct_0(A_226)
      | v2_struct_0(A_226) ) ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_1025,plain,
    ( k2_yellow19('#skF_2',k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3')) = '#skF_3'
    | ~ v13_waybel_0('#skF_3',k3_yellow_1(k2_struct_0('#skF_2')))
    | ~ v2_waybel_0('#skF_3',k3_yellow_1(k2_struct_0('#skF_2')))
    | ~ v1_subset_1('#skF_3',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2'))))
    | v1_xboole_0('#skF_3')
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_1020])).

tff(c_1029,plain,
    ( k2_yellow19('#skF_2',k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3')) = '#skF_3'
    | v1_xboole_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_498,c_54,c_52,c_50,c_1025])).

tff(c_1030,plain,(
    k2_yellow19('#skF_2',k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3')) = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_56,c_1029])).

tff(c_1034,plain,(
    ! [C_27] :
      ( r2_waybel_7('#skF_2','#skF_3',C_27)
      | ~ r2_hidden(C_27,k10_yellow_6('#skF_2',k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3')))
      | ~ m1_subset_1(C_27,u1_struct_0('#skF_2'))
      | ~ l1_waybel_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'),'#skF_2')
      | ~ v7_waybel_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'))
      | ~ v4_orders_2(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'))
      | v2_struct_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1030,c_42])).

tff(c_1041,plain,(
    ! [C_27] :
      ( r2_waybel_7('#skF_2','#skF_3',C_27)
      | ~ r2_hidden(C_27,k10_yellow_6('#skF_2',k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3')))
      | ~ m1_subset_1(C_27,k2_struct_0('#skF_2'))
      | v2_struct_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_659,c_986,c_800,c_90,c_1034])).

tff(c_1042,plain,(
    ! [C_27] :
      ( r2_waybel_7('#skF_2','#skF_3',C_27)
      | ~ r2_hidden(C_27,k10_yellow_6('#skF_2',k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3')))
      | ~ m1_subset_1(C_27,k2_struct_0('#skF_2'))
      | v2_struct_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_1041])).

tff(c_1047,plain,(
    v2_struct_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1042])).

tff(c_1049,plain,
    ( ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2')))))
    | ~ v13_waybel_0('#skF_3',k3_yellow_1(k2_struct_0('#skF_2')))
    | ~ v2_waybel_0('#skF_3',k3_yellow_1(k2_struct_0('#skF_2')))
    | v1_xboole_0('#skF_3')
    | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v1_xboole_0(k2_struct_0('#skF_2'))
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_1047,c_32])).

tff(c_1052,plain,
    ( v1_xboole_0('#skF_3')
    | v1_xboole_0(k2_struct_0('#skF_2'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_498,c_620,c_90,c_52,c_50,c_48,c_1049])).

tff(c_1054,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_497,c_56,c_1052])).

tff(c_1077,plain,(
    ! [C_232] :
      ( r2_waybel_7('#skF_2','#skF_3',C_232)
      | ~ r2_hidden(C_232,k10_yellow_6('#skF_2',k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3')))
      | ~ m1_subset_1(C_232,k2_struct_0('#skF_2')) ) ),
    inference(splitRight,[status(thm)],[c_1042])).

tff(c_1091,plain,
    ( r2_waybel_7('#skF_2','#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_4',k2_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_504,c_1077])).

tff(c_1097,plain,(
    r2_waybel_7('#skF_2','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_1091])).

tff(c_1099,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_487,c_1097])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:22:42 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.58/1.57  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.58/1.59  
% 3.58/1.59  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.58/1.59  %$ r2_waybel_7 > v6_waybel_0 > v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_hidden > r1_tarski > m1_subset_1 > l1_waybel_0 > v7_waybel_0 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k3_yellow19 > k2_yellow19 > k10_yellow_6 > #nlpp > u1_struct_0 > k3_yellow_1 > k3_lattice3 > k2_struct_0 > k1_zfmisc_1 > k1_lattice3 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 3.58/1.59  
% 3.58/1.59  %Foreground sorts:
% 3.58/1.59  
% 3.58/1.59  
% 3.58/1.59  %Background operators:
% 3.58/1.59  
% 3.58/1.59  
% 3.58/1.59  %Foreground operators:
% 3.58/1.59  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.58/1.59  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 3.58/1.59  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.58/1.59  tff(k3_lattice3, type, k3_lattice3: $i > $i).
% 3.58/1.59  tff(v6_waybel_0, type, v6_waybel_0: ($i * $i) > $o).
% 3.58/1.59  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.58/1.59  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 3.58/1.59  tff(k3_yellow_1, type, k3_yellow_1: $i > $i).
% 3.58/1.59  tff(v2_waybel_0, type, v2_waybel_0: ($i * $i) > $o).
% 3.58/1.59  tff(k10_yellow_6, type, k10_yellow_6: ($i * $i) > $i).
% 3.58/1.59  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.58/1.59  tff(v7_waybel_0, type, v7_waybel_0: $i > $o).
% 3.58/1.59  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.58/1.59  tff('#skF_2', type, '#skF_2': $i).
% 3.58/1.59  tff('#skF_3', type, '#skF_3': $i).
% 3.58/1.59  tff(k1_lattice3, type, k1_lattice3: $i > $i).
% 3.58/1.59  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 3.58/1.59  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.58/1.59  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.58/1.59  tff(k2_yellow19, type, k2_yellow19: ($i * $i) > $i).
% 3.58/1.59  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.58/1.59  tff(l1_waybel_0, type, l1_waybel_0: ($i * $i) > $o).
% 3.58/1.59  tff('#skF_4', type, '#skF_4': $i).
% 3.58/1.59  tff(r2_waybel_7, type, r2_waybel_7: ($i * $i * $i) > $o).
% 3.58/1.59  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.58/1.59  tff(k3_yellow19, type, k3_yellow19: ($i * $i * $i) > $i).
% 3.58/1.59  tff(v13_waybel_0, type, v13_waybel_0: ($i * $i) > $o).
% 3.58/1.59  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.58/1.59  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.58/1.59  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.58/1.59  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 3.58/1.59  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.58/1.59  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.58/1.59  
% 3.93/1.62  tff(f_206, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((((~v1_xboole_0(B) & v1_subset_1(B, u1_struct_0(k3_yellow_1(k2_struct_0(A))))) & v2_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & v13_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A)))))) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_hidden(C, k10_yellow_6(A, k3_yellow19(A, k2_struct_0(A), B))) <=> r2_waybel_7(A, B, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_yellow19)).
% 3.93/1.62  tff(f_44, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.93/1.62  tff(f_40, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 3.93/1.62  tff(f_52, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 3.93/1.62  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.93/1.62  tff(f_36, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.93/1.62  tff(f_108, axiom, (![A, B, C]: ((((((((~v2_struct_0(A) & l1_struct_0(A)) & ~v1_xboole_0(B)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) & ~v1_xboole_0(C)) & v2_waybel_0(C, k3_yellow_1(B))) & v13_waybel_0(C, k3_yellow_1(B))) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B))))) => (((~v2_struct_0(k3_yellow19(A, B, C)) & v3_orders_2(k3_yellow19(A, B, C))) & v4_orders_2(k3_yellow19(A, B, C))) & v6_waybel_0(k3_yellow19(A, B, C), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_yellow19)).
% 3.93/1.62  tff(f_136, axiom, (![A, B, C]: (((((((((~v2_struct_0(A) & l1_struct_0(A)) & ~v1_xboole_0(B)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) & ~v1_xboole_0(C)) & v1_subset_1(C, u1_struct_0(k3_yellow_1(B)))) & v2_waybel_0(C, k3_yellow_1(B))) & v13_waybel_0(C, k3_yellow_1(B))) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B))))) => ((~v2_struct_0(k3_yellow19(A, B, C)) & v6_waybel_0(k3_yellow19(A, B, C), A)) & v7_waybel_0(k3_yellow19(A, B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc5_yellow19)).
% 3.93/1.62  tff(f_80, axiom, (![A, B, C]: ((((((((~v2_struct_0(A) & l1_struct_0(A)) & ~v1_xboole_0(B)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) & ~v1_xboole_0(C)) & v2_waybel_0(C, k3_yellow_1(B))) & v13_waybel_0(C, k3_yellow_1(B))) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B))))) => ((~v2_struct_0(k3_yellow19(A, B, C)) & v6_waybel_0(k3_yellow19(A, B, C), A)) & l1_waybel_0(k3_yellow19(A, B, C), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_yellow19)).
% 3.93/1.62  tff(f_179, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: (((((~v1_xboole_0(B) & v1_subset_1(B, u1_struct_0(k3_yellow_1(k2_struct_0(A))))) & v2_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & v13_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A)))))) => (B = k2_yellow19(A, k3_yellow19(A, k2_struct_0(A), B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_yellow19)).
% 3.93/1.62  tff(f_160, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_hidden(C, k10_yellow_6(A, B)) <=> r2_waybel_7(A, k2_yellow19(A, B), C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_yellow19)).
% 3.93/1.62  tff(c_58, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_206])).
% 3.93/1.62  tff(c_14, plain, (![A_9]: (l1_struct_0(A_9) | ~l1_pre_topc(A_9))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.93/1.62  tff(c_81, plain, (![A_37]: (u1_struct_0(A_37)=k2_struct_0(A_37) | ~l1_struct_0(A_37))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.93/1.62  tff(c_86, plain, (![A_38]: (u1_struct_0(A_38)=k2_struct_0(A_38) | ~l1_pre_topc(A_38))), inference(resolution, [status(thm)], [c_14, c_81])).
% 3.93/1.62  tff(c_90, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_58, c_86])).
% 3.93/1.62  tff(c_46, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_206])).
% 3.93/1.62  tff(c_91, plain, (m1_subset_1('#skF_4', k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_46])).
% 3.93/1.62  tff(c_64, plain, (~r2_waybel_7('#skF_2', '#skF_3', '#skF_4') | ~r2_hidden('#skF_4', k10_yellow_6('#skF_2', k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_206])).
% 3.93/1.62  tff(c_111, plain, (~r2_hidden('#skF_4', k10_yellow_6('#skF_2', k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3')))), inference(splitLeft, [status(thm)], [c_64])).
% 3.93/1.62  tff(c_70, plain, (r2_hidden('#skF_4', k10_yellow_6('#skF_2', k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'))) | r2_waybel_7('#skF_2', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_206])).
% 3.93/1.62  tff(c_139, plain, (r2_waybel_7('#skF_2', '#skF_3', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_111, c_70])).
% 3.93/1.62  tff(c_62, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_206])).
% 3.93/1.62  tff(c_106, plain, (![A_43]: (~v1_xboole_0(u1_struct_0(A_43)) | ~l1_struct_0(A_43) | v2_struct_0(A_43))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.93/1.62  tff(c_109, plain, (~v1_xboole_0(k2_struct_0('#skF_2')) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_90, c_106])).
% 3.93/1.62  tff(c_110, plain, (~v1_xboole_0(k2_struct_0('#skF_2')) | ~l1_struct_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_62, c_109])).
% 3.93/1.62  tff(c_112, plain, (~l1_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_110])).
% 3.93/1.62  tff(c_115, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_14, c_112])).
% 3.93/1.62  tff(c_119, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_115])).
% 3.93/1.62  tff(c_120, plain, (~v1_xboole_0(k2_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_110])).
% 3.93/1.62  tff(c_56, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_206])).
% 3.93/1.62  tff(c_121, plain, (l1_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_110])).
% 3.93/1.62  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.93/1.62  tff(c_128, plain, (![A_46, B_47]: (~r2_hidden('#skF_1'(A_46, B_47), B_47) | r1_tarski(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.93/1.62  tff(c_133, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_128])).
% 3.93/1.62  tff(c_10, plain, (![A_6, B_7]: (m1_subset_1(A_6, k1_zfmisc_1(B_7)) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.93/1.62  tff(c_52, plain, (v2_waybel_0('#skF_3', k3_yellow_1(k2_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_206])).
% 3.93/1.62  tff(c_50, plain, (v13_waybel_0('#skF_3', k3_yellow_1(k2_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_206])).
% 3.93/1.62  tff(c_48, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2')))))), inference(cnfTransformation, [status(thm)], [f_206])).
% 3.93/1.62  tff(c_196, plain, (![A_77, B_78, C_79]: (v3_orders_2(k3_yellow19(A_77, B_78, C_79)) | ~m1_subset_1(C_79, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_78)))) | ~v13_waybel_0(C_79, k3_yellow_1(B_78)) | ~v2_waybel_0(C_79, k3_yellow_1(B_78)) | v1_xboole_0(C_79) | ~m1_subset_1(B_78, k1_zfmisc_1(u1_struct_0(A_77))) | v1_xboole_0(B_78) | ~l1_struct_0(A_77) | v2_struct_0(A_77))), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.93/1.62  tff(c_201, plain, (![A_77]: (v3_orders_2(k3_yellow19(A_77, k2_struct_0('#skF_2'), '#skF_3')) | ~v13_waybel_0('#skF_3', k3_yellow_1(k2_struct_0('#skF_2'))) | ~v2_waybel_0('#skF_3', k3_yellow_1(k2_struct_0('#skF_2'))) | v1_xboole_0('#skF_3') | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(u1_struct_0(A_77))) | v1_xboole_0(k2_struct_0('#skF_2')) | ~l1_struct_0(A_77) | v2_struct_0(A_77))), inference(resolution, [status(thm)], [c_48, c_196])).
% 3.93/1.62  tff(c_205, plain, (![A_77]: (v3_orders_2(k3_yellow19(A_77, k2_struct_0('#skF_2'), '#skF_3')) | v1_xboole_0('#skF_3') | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(u1_struct_0(A_77))) | v1_xboole_0(k2_struct_0('#skF_2')) | ~l1_struct_0(A_77) | v2_struct_0(A_77))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_201])).
% 3.93/1.62  tff(c_207, plain, (![A_80]: (v3_orders_2(k3_yellow19(A_80, k2_struct_0('#skF_2'), '#skF_3')) | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(u1_struct_0(A_80))) | ~l1_struct_0(A_80) | v2_struct_0(A_80))), inference(negUnitSimplification, [status(thm)], [c_120, c_56, c_205])).
% 3.93/1.62  tff(c_213, plain, (v3_orders_2(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3')) | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_90, c_207])).
% 3.93/1.62  tff(c_216, plain, (v3_orders_2(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3')) | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_2'))) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_121, c_213])).
% 3.93/1.62  tff(c_217, plain, (v3_orders_2(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3')) | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_62, c_216])).
% 3.93/1.62  tff(c_218, plain, (~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_2')))), inference(splitLeft, [status(thm)], [c_217])).
% 3.93/1.62  tff(c_221, plain, (~r1_tarski(k2_struct_0('#skF_2'), k2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_10, c_218])).
% 3.93/1.62  tff(c_225, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_133, c_221])).
% 3.93/1.62  tff(c_227, plain, (m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_217])).
% 3.93/1.62  tff(c_60, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_206])).
% 3.93/1.62  tff(c_228, plain, (![A_81, B_82, C_83]: (v4_orders_2(k3_yellow19(A_81, B_82, C_83)) | ~m1_subset_1(C_83, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_82)))) | ~v13_waybel_0(C_83, k3_yellow_1(B_82)) | ~v2_waybel_0(C_83, k3_yellow_1(B_82)) | v1_xboole_0(C_83) | ~m1_subset_1(B_82, k1_zfmisc_1(u1_struct_0(A_81))) | v1_xboole_0(B_82) | ~l1_struct_0(A_81) | v2_struct_0(A_81))), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.93/1.62  tff(c_233, plain, (![A_81]: (v4_orders_2(k3_yellow19(A_81, k2_struct_0('#skF_2'), '#skF_3')) | ~v13_waybel_0('#skF_3', k3_yellow_1(k2_struct_0('#skF_2'))) | ~v2_waybel_0('#skF_3', k3_yellow_1(k2_struct_0('#skF_2'))) | v1_xboole_0('#skF_3') | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(u1_struct_0(A_81))) | v1_xboole_0(k2_struct_0('#skF_2')) | ~l1_struct_0(A_81) | v2_struct_0(A_81))), inference(resolution, [status(thm)], [c_48, c_228])).
% 3.93/1.62  tff(c_237, plain, (![A_81]: (v4_orders_2(k3_yellow19(A_81, k2_struct_0('#skF_2'), '#skF_3')) | v1_xboole_0('#skF_3') | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(u1_struct_0(A_81))) | v1_xboole_0(k2_struct_0('#skF_2')) | ~l1_struct_0(A_81) | v2_struct_0(A_81))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_233])).
% 3.93/1.62  tff(c_256, plain, (![A_85]: (v4_orders_2(k3_yellow19(A_85, k2_struct_0('#skF_2'), '#skF_3')) | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(u1_struct_0(A_85))) | ~l1_struct_0(A_85) | v2_struct_0(A_85))), inference(negUnitSimplification, [status(thm)], [c_120, c_56, c_237])).
% 3.93/1.62  tff(c_262, plain, (v4_orders_2(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3')) | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_90, c_256])).
% 3.93/1.62  tff(c_265, plain, (v4_orders_2(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_121, c_227, c_262])).
% 3.93/1.62  tff(c_266, plain, (v4_orders_2(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_62, c_265])).
% 3.93/1.62  tff(c_54, plain, (v1_subset_1('#skF_3', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_206])).
% 3.93/1.62  tff(c_368, plain, (![A_102, B_103, C_104]: (v7_waybel_0(k3_yellow19(A_102, B_103, C_104)) | ~m1_subset_1(C_104, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_103)))) | ~v13_waybel_0(C_104, k3_yellow_1(B_103)) | ~v2_waybel_0(C_104, k3_yellow_1(B_103)) | ~v1_subset_1(C_104, u1_struct_0(k3_yellow_1(B_103))) | v1_xboole_0(C_104) | ~m1_subset_1(B_103, k1_zfmisc_1(u1_struct_0(A_102))) | v1_xboole_0(B_103) | ~l1_struct_0(A_102) | v2_struct_0(A_102))), inference(cnfTransformation, [status(thm)], [f_136])).
% 3.93/1.62  tff(c_373, plain, (![A_102]: (v7_waybel_0(k3_yellow19(A_102, k2_struct_0('#skF_2'), '#skF_3')) | ~v13_waybel_0('#skF_3', k3_yellow_1(k2_struct_0('#skF_2'))) | ~v2_waybel_0('#skF_3', k3_yellow_1(k2_struct_0('#skF_2'))) | ~v1_subset_1('#skF_3', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2')))) | v1_xboole_0('#skF_3') | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(u1_struct_0(A_102))) | v1_xboole_0(k2_struct_0('#skF_2')) | ~l1_struct_0(A_102) | v2_struct_0(A_102))), inference(resolution, [status(thm)], [c_48, c_368])).
% 3.93/1.62  tff(c_377, plain, (![A_102]: (v7_waybel_0(k3_yellow19(A_102, k2_struct_0('#skF_2'), '#skF_3')) | v1_xboole_0('#skF_3') | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(u1_struct_0(A_102))) | v1_xboole_0(k2_struct_0('#skF_2')) | ~l1_struct_0(A_102) | v2_struct_0(A_102))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_373])).
% 3.93/1.62  tff(c_379, plain, (![A_105]: (v7_waybel_0(k3_yellow19(A_105, k2_struct_0('#skF_2'), '#skF_3')) | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(u1_struct_0(A_105))) | ~l1_struct_0(A_105) | v2_struct_0(A_105))), inference(negUnitSimplification, [status(thm)], [c_120, c_56, c_377])).
% 3.93/1.62  tff(c_385, plain, (v7_waybel_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3')) | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_90, c_379])).
% 3.93/1.62  tff(c_388, plain, (v7_waybel_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_121, c_227, c_385])).
% 3.93/1.62  tff(c_389, plain, (v7_waybel_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_62, c_388])).
% 3.93/1.62  tff(c_280, plain, (![A_87, B_88, C_89]: (l1_waybel_0(k3_yellow19(A_87, B_88, C_89), A_87) | ~m1_subset_1(C_89, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_88)))) | ~v13_waybel_0(C_89, k3_yellow_1(B_88)) | ~v2_waybel_0(C_89, k3_yellow_1(B_88)) | v1_xboole_0(C_89) | ~m1_subset_1(B_88, k1_zfmisc_1(u1_struct_0(A_87))) | v1_xboole_0(B_88) | ~l1_struct_0(A_87) | v2_struct_0(A_87))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.93/1.62  tff(c_285, plain, (![A_87]: (l1_waybel_0(k3_yellow19(A_87, k2_struct_0('#skF_2'), '#skF_3'), A_87) | ~v13_waybel_0('#skF_3', k3_yellow_1(k2_struct_0('#skF_2'))) | ~v2_waybel_0('#skF_3', k3_yellow_1(k2_struct_0('#skF_2'))) | v1_xboole_0('#skF_3') | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(u1_struct_0(A_87))) | v1_xboole_0(k2_struct_0('#skF_2')) | ~l1_struct_0(A_87) | v2_struct_0(A_87))), inference(resolution, [status(thm)], [c_48, c_280])).
% 3.93/1.62  tff(c_289, plain, (![A_87]: (l1_waybel_0(k3_yellow19(A_87, k2_struct_0('#skF_2'), '#skF_3'), A_87) | v1_xboole_0('#skF_3') | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(u1_struct_0(A_87))) | v1_xboole_0(k2_struct_0('#skF_2')) | ~l1_struct_0(A_87) | v2_struct_0(A_87))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_285])).
% 3.93/1.62  tff(c_291, plain, (![A_90]: (l1_waybel_0(k3_yellow19(A_90, k2_struct_0('#skF_2'), '#skF_3'), A_90) | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(u1_struct_0(A_90))) | ~l1_struct_0(A_90) | v2_struct_0(A_90))), inference(negUnitSimplification, [status(thm)], [c_120, c_56, c_289])).
% 3.93/1.62  tff(c_296, plain, (l1_waybel_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'), '#skF_2') | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_90, c_291])).
% 3.93/1.62  tff(c_299, plain, (l1_waybel_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'), '#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_121, c_227, c_296])).
% 3.93/1.62  tff(c_300, plain, (l1_waybel_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_62, c_299])).
% 3.93/1.62  tff(c_432, plain, (![A_112, B_113]: (k2_yellow19(A_112, k3_yellow19(A_112, k2_struct_0(A_112), B_113))=B_113 | ~m1_subset_1(B_113, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_112))))) | ~v13_waybel_0(B_113, k3_yellow_1(k2_struct_0(A_112))) | ~v2_waybel_0(B_113, k3_yellow_1(k2_struct_0(A_112))) | ~v1_subset_1(B_113, u1_struct_0(k3_yellow_1(k2_struct_0(A_112)))) | v1_xboole_0(B_113) | ~l1_struct_0(A_112) | v2_struct_0(A_112))), inference(cnfTransformation, [status(thm)], [f_179])).
% 3.93/1.62  tff(c_437, plain, (k2_yellow19('#skF_2', k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'))='#skF_3' | ~v13_waybel_0('#skF_3', k3_yellow_1(k2_struct_0('#skF_2'))) | ~v2_waybel_0('#skF_3', k3_yellow_1(k2_struct_0('#skF_2'))) | ~v1_subset_1('#skF_3', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2')))) | v1_xboole_0('#skF_3') | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_48, c_432])).
% 3.93/1.62  tff(c_441, plain, (k2_yellow19('#skF_2', k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'))='#skF_3' | v1_xboole_0('#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_121, c_54, c_52, c_50, c_437])).
% 3.93/1.62  tff(c_442, plain, (k2_yellow19('#skF_2', k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'))='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_62, c_56, c_441])).
% 3.93/1.62  tff(c_42, plain, (![A_21, B_25, C_27]: (r2_waybel_7(A_21, k2_yellow19(A_21, B_25), C_27) | ~r2_hidden(C_27, k10_yellow_6(A_21, B_25)) | ~m1_subset_1(C_27, u1_struct_0(A_21)) | ~l1_waybel_0(B_25, A_21) | ~v7_waybel_0(B_25) | ~v4_orders_2(B_25) | v2_struct_0(B_25) | ~l1_pre_topc(A_21) | ~v2_pre_topc(A_21) | v2_struct_0(A_21))), inference(cnfTransformation, [status(thm)], [f_160])).
% 3.93/1.62  tff(c_446, plain, (![C_27]: (r2_waybel_7('#skF_2', '#skF_3', C_27) | ~r2_hidden(C_27, k10_yellow_6('#skF_2', k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'))) | ~m1_subset_1(C_27, u1_struct_0('#skF_2')) | ~l1_waybel_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'), '#skF_2') | ~v7_waybel_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3')) | ~v4_orders_2(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3')) | v2_struct_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_442, c_42])).
% 3.93/1.62  tff(c_453, plain, (![C_27]: (r2_waybel_7('#skF_2', '#skF_3', C_27) | ~r2_hidden(C_27, k10_yellow_6('#skF_2', k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'))) | ~m1_subset_1(C_27, k2_struct_0('#skF_2')) | v2_struct_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_266, c_389, c_300, c_90, c_446])).
% 3.93/1.62  tff(c_454, plain, (![C_27]: (r2_waybel_7('#skF_2', '#skF_3', C_27) | ~r2_hidden(C_27, k10_yellow_6('#skF_2', k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'))) | ~m1_subset_1(C_27, k2_struct_0('#skF_2')) | v2_struct_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_62, c_453])).
% 3.93/1.62  tff(c_459, plain, (v2_struct_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'))), inference(splitLeft, [status(thm)], [c_454])).
% 3.93/1.62  tff(c_32, plain, (![A_15, B_16, C_17]: (~v2_struct_0(k3_yellow19(A_15, B_16, C_17)) | ~m1_subset_1(C_17, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_16)))) | ~v13_waybel_0(C_17, k3_yellow_1(B_16)) | ~v2_waybel_0(C_17, k3_yellow_1(B_16)) | v1_xboole_0(C_17) | ~m1_subset_1(B_16, k1_zfmisc_1(u1_struct_0(A_15))) | v1_xboole_0(B_16) | ~l1_struct_0(A_15) | v2_struct_0(A_15))), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.93/1.62  tff(c_461, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2'))))) | ~v13_waybel_0('#skF_3', k3_yellow_1(k2_struct_0('#skF_2'))) | ~v2_waybel_0('#skF_3', k3_yellow_1(k2_struct_0('#skF_2'))) | v1_xboole_0('#skF_3') | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | v1_xboole_0(k2_struct_0('#skF_2')) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_459, c_32])).
% 3.93/1.62  tff(c_464, plain, (v1_xboole_0('#skF_3') | v1_xboole_0(k2_struct_0('#skF_2')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_121, c_227, c_90, c_52, c_50, c_48, c_461])).
% 3.93/1.62  tff(c_466, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_120, c_56, c_464])).
% 3.93/1.62  tff(c_468, plain, (~v2_struct_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'))), inference(splitRight, [status(thm)], [c_454])).
% 3.93/1.62  tff(c_40, plain, (![C_27, A_21, B_25]: (r2_hidden(C_27, k10_yellow_6(A_21, B_25)) | ~r2_waybel_7(A_21, k2_yellow19(A_21, B_25), C_27) | ~m1_subset_1(C_27, u1_struct_0(A_21)) | ~l1_waybel_0(B_25, A_21) | ~v7_waybel_0(B_25) | ~v4_orders_2(B_25) | v2_struct_0(B_25) | ~l1_pre_topc(A_21) | ~v2_pre_topc(A_21) | v2_struct_0(A_21))), inference(cnfTransformation, [status(thm)], [f_160])).
% 3.93/1.62  tff(c_449, plain, (![C_27]: (r2_hidden(C_27, k10_yellow_6('#skF_2', k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'))) | ~r2_waybel_7('#skF_2', '#skF_3', C_27) | ~m1_subset_1(C_27, u1_struct_0('#skF_2')) | ~l1_waybel_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'), '#skF_2') | ~v7_waybel_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3')) | ~v4_orders_2(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3')) | v2_struct_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_442, c_40])).
% 3.93/1.62  tff(c_456, plain, (![C_27]: (r2_hidden(C_27, k10_yellow_6('#skF_2', k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'))) | ~r2_waybel_7('#skF_2', '#skF_3', C_27) | ~m1_subset_1(C_27, k2_struct_0('#skF_2')) | v2_struct_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_266, c_389, c_300, c_90, c_449])).
% 3.93/1.62  tff(c_457, plain, (![C_27]: (r2_hidden(C_27, k10_yellow_6('#skF_2', k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'))) | ~r2_waybel_7('#skF_2', '#skF_3', C_27) | ~m1_subset_1(C_27, k2_struct_0('#skF_2')) | v2_struct_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_62, c_456])).
% 3.93/1.62  tff(c_469, plain, (v2_struct_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'))), inference(splitLeft, [status(thm)], [c_457])).
% 3.93/1.62  tff(c_470, plain, $false, inference(negUnitSimplification, [status(thm)], [c_468, c_469])).
% 3.93/1.62  tff(c_473, plain, (![C_114]: (r2_hidden(C_114, k10_yellow_6('#skF_2', k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'))) | ~r2_waybel_7('#skF_2', '#skF_3', C_114) | ~m1_subset_1(C_114, k2_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_457])).
% 3.93/1.62  tff(c_476, plain, (~r2_waybel_7('#skF_2', '#skF_3', '#skF_4') | ~m1_subset_1('#skF_4', k2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_473, c_111])).
% 3.93/1.62  tff(c_486, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_91, c_139, c_476])).
% 3.93/1.62  tff(c_487, plain, (~r2_waybel_7('#skF_2', '#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_64])).
% 3.93/1.62  tff(c_504, plain, (r2_hidden('#skF_4', k10_yellow_6('#skF_2', k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_487, c_70])).
% 3.93/1.62  tff(c_489, plain, (~l1_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_110])).
% 3.93/1.62  tff(c_492, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_14, c_489])).
% 3.93/1.62  tff(c_496, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_492])).
% 3.93/1.62  tff(c_497, plain, (~v1_xboole_0(k2_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_110])).
% 3.93/1.62  tff(c_498, plain, (l1_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_110])).
% 3.93/1.62  tff(c_506, plain, (![A_117, B_118]: (~r2_hidden('#skF_1'(A_117, B_118), B_118) | r1_tarski(A_117, B_118))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.93/1.62  tff(c_511, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_506])).
% 3.93/1.62  tff(c_589, plain, (![A_146, B_147, C_148]: (v3_orders_2(k3_yellow19(A_146, B_147, C_148)) | ~m1_subset_1(C_148, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_147)))) | ~v13_waybel_0(C_148, k3_yellow_1(B_147)) | ~v2_waybel_0(C_148, k3_yellow_1(B_147)) | v1_xboole_0(C_148) | ~m1_subset_1(B_147, k1_zfmisc_1(u1_struct_0(A_146))) | v1_xboole_0(B_147) | ~l1_struct_0(A_146) | v2_struct_0(A_146))), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.93/1.62  tff(c_594, plain, (![A_146]: (v3_orders_2(k3_yellow19(A_146, k2_struct_0('#skF_2'), '#skF_3')) | ~v13_waybel_0('#skF_3', k3_yellow_1(k2_struct_0('#skF_2'))) | ~v2_waybel_0('#skF_3', k3_yellow_1(k2_struct_0('#skF_2'))) | v1_xboole_0('#skF_3') | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(u1_struct_0(A_146))) | v1_xboole_0(k2_struct_0('#skF_2')) | ~l1_struct_0(A_146) | v2_struct_0(A_146))), inference(resolution, [status(thm)], [c_48, c_589])).
% 3.93/1.62  tff(c_598, plain, (![A_146]: (v3_orders_2(k3_yellow19(A_146, k2_struct_0('#skF_2'), '#skF_3')) | v1_xboole_0('#skF_3') | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(u1_struct_0(A_146))) | v1_xboole_0(k2_struct_0('#skF_2')) | ~l1_struct_0(A_146) | v2_struct_0(A_146))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_594])).
% 3.93/1.62  tff(c_600, plain, (![A_149]: (v3_orders_2(k3_yellow19(A_149, k2_struct_0('#skF_2'), '#skF_3')) | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(u1_struct_0(A_149))) | ~l1_struct_0(A_149) | v2_struct_0(A_149))), inference(negUnitSimplification, [status(thm)], [c_497, c_56, c_598])).
% 3.93/1.62  tff(c_606, plain, (v3_orders_2(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3')) | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_90, c_600])).
% 3.93/1.62  tff(c_609, plain, (v3_orders_2(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3')) | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_2'))) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_498, c_606])).
% 3.93/1.62  tff(c_610, plain, (v3_orders_2(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3')) | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_62, c_609])).
% 3.93/1.62  tff(c_611, plain, (~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_2')))), inference(splitLeft, [status(thm)], [c_610])).
% 3.93/1.62  tff(c_614, plain, (~r1_tarski(k2_struct_0('#skF_2'), k2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_10, c_611])).
% 3.93/1.62  tff(c_618, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_511, c_614])).
% 3.93/1.62  tff(c_620, plain, (m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_610])).
% 3.93/1.62  tff(c_626, plain, (![A_150, B_151, C_152]: (v4_orders_2(k3_yellow19(A_150, B_151, C_152)) | ~m1_subset_1(C_152, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_151)))) | ~v13_waybel_0(C_152, k3_yellow_1(B_151)) | ~v2_waybel_0(C_152, k3_yellow_1(B_151)) | v1_xboole_0(C_152) | ~m1_subset_1(B_151, k1_zfmisc_1(u1_struct_0(A_150))) | v1_xboole_0(B_151) | ~l1_struct_0(A_150) | v2_struct_0(A_150))), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.93/1.62  tff(c_631, plain, (![A_150]: (v4_orders_2(k3_yellow19(A_150, k2_struct_0('#skF_2'), '#skF_3')) | ~v13_waybel_0('#skF_3', k3_yellow_1(k2_struct_0('#skF_2'))) | ~v2_waybel_0('#skF_3', k3_yellow_1(k2_struct_0('#skF_2'))) | v1_xboole_0('#skF_3') | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(u1_struct_0(A_150))) | v1_xboole_0(k2_struct_0('#skF_2')) | ~l1_struct_0(A_150) | v2_struct_0(A_150))), inference(resolution, [status(thm)], [c_48, c_626])).
% 3.93/1.62  tff(c_635, plain, (![A_150]: (v4_orders_2(k3_yellow19(A_150, k2_struct_0('#skF_2'), '#skF_3')) | v1_xboole_0('#skF_3') | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(u1_struct_0(A_150))) | v1_xboole_0(k2_struct_0('#skF_2')) | ~l1_struct_0(A_150) | v2_struct_0(A_150))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_631])).
% 3.93/1.62  tff(c_649, plain, (![A_154]: (v4_orders_2(k3_yellow19(A_154, k2_struct_0('#skF_2'), '#skF_3')) | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(u1_struct_0(A_154))) | ~l1_struct_0(A_154) | v2_struct_0(A_154))), inference(negUnitSimplification, [status(thm)], [c_497, c_56, c_635])).
% 3.93/1.62  tff(c_655, plain, (v4_orders_2(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3')) | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_90, c_649])).
% 3.93/1.62  tff(c_658, plain, (v4_orders_2(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_498, c_620, c_655])).
% 3.93/1.62  tff(c_659, plain, (v4_orders_2(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_62, c_658])).
% 3.93/1.62  tff(c_965, plain, (![A_210, B_211, C_212]: (v7_waybel_0(k3_yellow19(A_210, B_211, C_212)) | ~m1_subset_1(C_212, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_211)))) | ~v13_waybel_0(C_212, k3_yellow_1(B_211)) | ~v2_waybel_0(C_212, k3_yellow_1(B_211)) | ~v1_subset_1(C_212, u1_struct_0(k3_yellow_1(B_211))) | v1_xboole_0(C_212) | ~m1_subset_1(B_211, k1_zfmisc_1(u1_struct_0(A_210))) | v1_xboole_0(B_211) | ~l1_struct_0(A_210) | v2_struct_0(A_210))), inference(cnfTransformation, [status(thm)], [f_136])).
% 3.93/1.62  tff(c_970, plain, (![A_210]: (v7_waybel_0(k3_yellow19(A_210, k2_struct_0('#skF_2'), '#skF_3')) | ~v13_waybel_0('#skF_3', k3_yellow_1(k2_struct_0('#skF_2'))) | ~v2_waybel_0('#skF_3', k3_yellow_1(k2_struct_0('#skF_2'))) | ~v1_subset_1('#skF_3', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2')))) | v1_xboole_0('#skF_3') | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(u1_struct_0(A_210))) | v1_xboole_0(k2_struct_0('#skF_2')) | ~l1_struct_0(A_210) | v2_struct_0(A_210))), inference(resolution, [status(thm)], [c_48, c_965])).
% 3.93/1.62  tff(c_974, plain, (![A_210]: (v7_waybel_0(k3_yellow19(A_210, k2_struct_0('#skF_2'), '#skF_3')) | v1_xboole_0('#skF_3') | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(u1_struct_0(A_210))) | v1_xboole_0(k2_struct_0('#skF_2')) | ~l1_struct_0(A_210) | v2_struct_0(A_210))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_970])).
% 3.93/1.62  tff(c_976, plain, (![A_213]: (v7_waybel_0(k3_yellow19(A_213, k2_struct_0('#skF_2'), '#skF_3')) | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(u1_struct_0(A_213))) | ~l1_struct_0(A_213) | v2_struct_0(A_213))), inference(negUnitSimplification, [status(thm)], [c_497, c_56, c_974])).
% 3.93/1.62  tff(c_982, plain, (v7_waybel_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3')) | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_90, c_976])).
% 3.93/1.62  tff(c_985, plain, (v7_waybel_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_498, c_620, c_982])).
% 3.93/1.62  tff(c_986, plain, (v7_waybel_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_62, c_985])).
% 3.93/1.62  tff(c_780, plain, (![A_176, B_177, C_178]: (l1_waybel_0(k3_yellow19(A_176, B_177, C_178), A_176) | ~m1_subset_1(C_178, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_177)))) | ~v13_waybel_0(C_178, k3_yellow_1(B_177)) | ~v2_waybel_0(C_178, k3_yellow_1(B_177)) | v1_xboole_0(C_178) | ~m1_subset_1(B_177, k1_zfmisc_1(u1_struct_0(A_176))) | v1_xboole_0(B_177) | ~l1_struct_0(A_176) | v2_struct_0(A_176))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.93/1.62  tff(c_785, plain, (![A_176]: (l1_waybel_0(k3_yellow19(A_176, k2_struct_0('#skF_2'), '#skF_3'), A_176) | ~v13_waybel_0('#skF_3', k3_yellow_1(k2_struct_0('#skF_2'))) | ~v2_waybel_0('#skF_3', k3_yellow_1(k2_struct_0('#skF_2'))) | v1_xboole_0('#skF_3') | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(u1_struct_0(A_176))) | v1_xboole_0(k2_struct_0('#skF_2')) | ~l1_struct_0(A_176) | v2_struct_0(A_176))), inference(resolution, [status(thm)], [c_48, c_780])).
% 3.93/1.62  tff(c_789, plain, (![A_176]: (l1_waybel_0(k3_yellow19(A_176, k2_struct_0('#skF_2'), '#skF_3'), A_176) | v1_xboole_0('#skF_3') | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(u1_struct_0(A_176))) | v1_xboole_0(k2_struct_0('#skF_2')) | ~l1_struct_0(A_176) | v2_struct_0(A_176))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_785])).
% 3.93/1.62  tff(c_791, plain, (![A_179]: (l1_waybel_0(k3_yellow19(A_179, k2_struct_0('#skF_2'), '#skF_3'), A_179) | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(u1_struct_0(A_179))) | ~l1_struct_0(A_179) | v2_struct_0(A_179))), inference(negUnitSimplification, [status(thm)], [c_497, c_56, c_789])).
% 3.93/1.62  tff(c_796, plain, (l1_waybel_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'), '#skF_2') | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_90, c_791])).
% 3.93/1.62  tff(c_799, plain, (l1_waybel_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'), '#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_498, c_620, c_796])).
% 3.93/1.62  tff(c_800, plain, (l1_waybel_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_62, c_799])).
% 3.93/1.62  tff(c_1020, plain, (![A_226, B_227]: (k2_yellow19(A_226, k3_yellow19(A_226, k2_struct_0(A_226), B_227))=B_227 | ~m1_subset_1(B_227, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_226))))) | ~v13_waybel_0(B_227, k3_yellow_1(k2_struct_0(A_226))) | ~v2_waybel_0(B_227, k3_yellow_1(k2_struct_0(A_226))) | ~v1_subset_1(B_227, u1_struct_0(k3_yellow_1(k2_struct_0(A_226)))) | v1_xboole_0(B_227) | ~l1_struct_0(A_226) | v2_struct_0(A_226))), inference(cnfTransformation, [status(thm)], [f_179])).
% 3.93/1.62  tff(c_1025, plain, (k2_yellow19('#skF_2', k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'))='#skF_3' | ~v13_waybel_0('#skF_3', k3_yellow_1(k2_struct_0('#skF_2'))) | ~v2_waybel_0('#skF_3', k3_yellow_1(k2_struct_0('#skF_2'))) | ~v1_subset_1('#skF_3', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2')))) | v1_xboole_0('#skF_3') | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_48, c_1020])).
% 3.93/1.62  tff(c_1029, plain, (k2_yellow19('#skF_2', k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'))='#skF_3' | v1_xboole_0('#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_498, c_54, c_52, c_50, c_1025])).
% 3.93/1.62  tff(c_1030, plain, (k2_yellow19('#skF_2', k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'))='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_62, c_56, c_1029])).
% 3.93/1.62  tff(c_1034, plain, (![C_27]: (r2_waybel_7('#skF_2', '#skF_3', C_27) | ~r2_hidden(C_27, k10_yellow_6('#skF_2', k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'))) | ~m1_subset_1(C_27, u1_struct_0('#skF_2')) | ~l1_waybel_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'), '#skF_2') | ~v7_waybel_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3')) | ~v4_orders_2(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3')) | v2_struct_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1030, c_42])).
% 3.93/1.62  tff(c_1041, plain, (![C_27]: (r2_waybel_7('#skF_2', '#skF_3', C_27) | ~r2_hidden(C_27, k10_yellow_6('#skF_2', k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'))) | ~m1_subset_1(C_27, k2_struct_0('#skF_2')) | v2_struct_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_659, c_986, c_800, c_90, c_1034])).
% 3.93/1.62  tff(c_1042, plain, (![C_27]: (r2_waybel_7('#skF_2', '#skF_3', C_27) | ~r2_hidden(C_27, k10_yellow_6('#skF_2', k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'))) | ~m1_subset_1(C_27, k2_struct_0('#skF_2')) | v2_struct_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_62, c_1041])).
% 3.93/1.62  tff(c_1047, plain, (v2_struct_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'))), inference(splitLeft, [status(thm)], [c_1042])).
% 3.93/1.62  tff(c_1049, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2'))))) | ~v13_waybel_0('#skF_3', k3_yellow_1(k2_struct_0('#skF_2'))) | ~v2_waybel_0('#skF_3', k3_yellow_1(k2_struct_0('#skF_2'))) | v1_xboole_0('#skF_3') | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | v1_xboole_0(k2_struct_0('#skF_2')) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_1047, c_32])).
% 3.93/1.62  tff(c_1052, plain, (v1_xboole_0('#skF_3') | v1_xboole_0(k2_struct_0('#skF_2')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_498, c_620, c_90, c_52, c_50, c_48, c_1049])).
% 3.93/1.62  tff(c_1054, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_497, c_56, c_1052])).
% 3.93/1.62  tff(c_1077, plain, (![C_232]: (r2_waybel_7('#skF_2', '#skF_3', C_232) | ~r2_hidden(C_232, k10_yellow_6('#skF_2', k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'))) | ~m1_subset_1(C_232, k2_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_1042])).
% 3.93/1.62  tff(c_1091, plain, (r2_waybel_7('#skF_2', '#skF_3', '#skF_4') | ~m1_subset_1('#skF_4', k2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_504, c_1077])).
% 3.93/1.62  tff(c_1097, plain, (r2_waybel_7('#skF_2', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_91, c_1091])).
% 3.93/1.62  tff(c_1099, plain, $false, inference(negUnitSimplification, [status(thm)], [c_487, c_1097])).
% 3.93/1.62  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.93/1.62  
% 3.93/1.62  Inference rules
% 3.93/1.62  ----------------------
% 3.93/1.62  #Ref     : 0
% 3.93/1.62  #Sup     : 184
% 3.93/1.62  #Fact    : 0
% 3.93/1.62  #Define  : 0
% 3.93/1.62  #Split   : 16
% 3.93/1.62  #Chain   : 0
% 3.93/1.62  #Close   : 0
% 3.93/1.62  
% 3.93/1.62  Ordering : KBO
% 3.93/1.62  
% 3.93/1.62  Simplification rules
% 3.93/1.62  ----------------------
% 3.93/1.62  #Subsume      : 34
% 3.93/1.62  #Demod        : 183
% 3.93/1.62  #Tautology    : 39
% 3.93/1.62  #SimpNegUnit  : 80
% 3.93/1.62  #BackRed      : 1
% 3.93/1.62  
% 3.93/1.62  #Partial instantiations: 0
% 3.93/1.62  #Strategies tried      : 1
% 3.93/1.62  
% 3.93/1.62  Timing (in seconds)
% 3.93/1.62  ----------------------
% 3.93/1.62  Preprocessing        : 0.35
% 3.93/1.62  Parsing              : 0.18
% 3.93/1.62  CNF conversion       : 0.02
% 3.93/1.62  Main loop            : 0.49
% 3.93/1.62  Inferencing          : 0.18
% 3.93/1.62  Reduction            : 0.15
% 3.93/1.62  Demodulation         : 0.11
% 3.93/1.62  BG Simplification    : 0.02
% 3.93/1.62  Subsumption          : 0.10
% 3.93/1.62  Abstraction          : 0.02
% 3.93/1.62  MUC search           : 0.00
% 3.93/1.62  Cooper               : 0.00
% 3.93/1.62  Total                : 0.89
% 3.93/1.62  Index Insertion      : 0.00
% 3.93/1.62  Index Deletion       : 0.00
% 3.93/1.62  Index Matching       : 0.00
% 3.93/1.62  BG Taut test         : 0.00
%------------------------------------------------------------------------------
