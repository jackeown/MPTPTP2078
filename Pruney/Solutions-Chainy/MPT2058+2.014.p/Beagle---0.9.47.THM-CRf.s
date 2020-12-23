%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:34 EST 2020

% Result     : Theorem 3.88s
% Output     : CNFRefutation 4.21s
% Verified   : 
% Statistics : Number of formulae       :  193 (2394 expanded)
%              Number of leaves         :   44 ( 836 expanded)
%              Depth                    :   18
%              Number of atoms          :  584 (12004 expanded)
%              Number of equality atoms :   13 ( 327 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_waybel_9 > r1_waybel_7 > v6_waybel_0 > v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_hidden > r1_tarski > m1_subset_1 > l1_waybel_0 > v7_waybel_0 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k3_yellow19 > k2_yellow19 > #nlpp > u1_struct_0 > k3_yellow_1 > k3_lattice3 > k2_struct_0 > k1_zfmisc_1 > k1_lattice3 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(v7_waybel_0,type,(
    v7_waybel_0: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r3_waybel_9,type,(
    r3_waybel_9: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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
               => ( r3_waybel_9(A,k3_yellow19(A,k2_struct_0(A),B),C)
                <=> r1_waybel_7(A,B,C) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_yellow19)).

tff(f_44,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_40,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_yellow19)).

tff(f_52,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(k2_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_struct_0)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_36,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_yellow19)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_yellow19)).

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
             => ( r3_waybel_9(A,B,C)
              <=> r1_waybel_7(A,k2_yellow19(A,B),C) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_yellow19)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_yellow19)).

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
    ( ~ r1_waybel_7('#skF_2','#skF_3','#skF_4')
    | ~ r3_waybel_9('#skF_2',k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_107,plain,(
    ~ r3_waybel_9('#skF_2',k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_70,plain,
    ( r3_waybel_9('#skF_2',k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'),'#skF_4')
    | r1_waybel_7('#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_120,plain,(
    r1_waybel_7('#skF_2','#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_107,c_70])).

tff(c_62,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_56,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_52,plain,(
    v2_waybel_0('#skF_3',k3_yellow_1(k2_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_50,plain,(
    v13_waybel_0('#skF_3',k3_yellow_1(k2_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_48,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2'))))) ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_176,plain,(
    ! [A_74,B_75,C_76] :
      ( v3_orders_2(k3_yellow19(A_74,B_75,C_76))
      | ~ m1_subset_1(C_76,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_75))))
      | ~ v13_waybel_0(C_76,k3_yellow_1(B_75))
      | ~ v2_waybel_0(C_76,k3_yellow_1(B_75))
      | v1_xboole_0(C_76)
      | ~ m1_subset_1(B_75,k1_zfmisc_1(u1_struct_0(A_74)))
      | v1_xboole_0(B_75)
      | ~ l1_struct_0(A_74)
      | v2_struct_0(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_181,plain,(
    ! [A_74] :
      ( v3_orders_2(k3_yellow19(A_74,k2_struct_0('#skF_2'),'#skF_3'))
      | ~ v13_waybel_0('#skF_3',k3_yellow_1(k2_struct_0('#skF_2')))
      | ~ v2_waybel_0('#skF_3',k3_yellow_1(k2_struct_0('#skF_2')))
      | v1_xboole_0('#skF_3')
      | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0(A_74)))
      | v1_xboole_0(k2_struct_0('#skF_2'))
      | ~ l1_struct_0(A_74)
      | v2_struct_0(A_74) ) ),
    inference(resolution,[status(thm)],[c_48,c_176])).

tff(c_185,plain,(
    ! [A_74] :
      ( v3_orders_2(k3_yellow19(A_74,k2_struct_0('#skF_2'),'#skF_3'))
      | v1_xboole_0('#skF_3')
      | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0(A_74)))
      | v1_xboole_0(k2_struct_0('#skF_2'))
      | ~ l1_struct_0(A_74)
      | v2_struct_0(A_74) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_181])).

tff(c_186,plain,(
    ! [A_74] :
      ( v3_orders_2(k3_yellow19(A_74,k2_struct_0('#skF_2'),'#skF_3'))
      | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0(A_74)))
      | v1_xboole_0(k2_struct_0('#skF_2'))
      | ~ l1_struct_0(A_74)
      | v2_struct_0(A_74) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_185])).

tff(c_187,plain,(
    v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_186])).

tff(c_16,plain,(
    ! [A_10] :
      ( ~ v1_xboole_0(k2_struct_0(A_10))
      | ~ l1_struct_0(A_10)
      | v2_struct_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_190,plain,
    ( ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_187,c_16])).

tff(c_193,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_190])).

tff(c_196,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_14,c_193])).

tff(c_200,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_196])).

tff(c_202,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_186])).

tff(c_203,plain,(
    ! [A_77] :
      ( v3_orders_2(k3_yellow19(A_77,k2_struct_0('#skF_2'),'#skF_3'))
      | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0(A_77)))
      | ~ l1_struct_0(A_77)
      | v2_struct_0(A_77) ) ),
    inference(splitRight,[status(thm)],[c_186])).

tff(c_209,plain,
    ( v3_orders_2(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'))
    | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_2')))
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_203])).

tff(c_211,plain,
    ( v3_orders_2(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'))
    | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_2')))
    | ~ l1_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_209])).

tff(c_212,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_211])).

tff(c_215,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_14,c_212])).

tff(c_219,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_215])).

tff(c_221,plain,(
    l1_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_211])).

tff(c_109,plain,(
    ! [A_46,B_47] :
      ( r2_hidden('#skF_1'(A_46,B_47),A_46)
      | r1_tarski(A_46,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_114,plain,(
    ! [A_46] : r1_tarski(A_46,A_46) ),
    inference(resolution,[status(thm)],[c_109,c_4])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(A_6,k1_zfmisc_1(B_7))
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_220,plain,
    ( ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_2')))
    | v3_orders_2(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3')) ),
    inference(splitRight,[status(thm)],[c_211])).

tff(c_238,plain,(
    ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_220])).

tff(c_241,plain,(
    ~ r1_tarski(k2_struct_0('#skF_2'),k2_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_10,c_238])).

tff(c_245,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_241])).

tff(c_247,plain,(
    m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_220])).

tff(c_60,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_227,plain,(
    ! [A_78,B_79,C_80] :
      ( v4_orders_2(k3_yellow19(A_78,B_79,C_80))
      | ~ m1_subset_1(C_80,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_79))))
      | ~ v13_waybel_0(C_80,k3_yellow_1(B_79))
      | ~ v2_waybel_0(C_80,k3_yellow_1(B_79))
      | v1_xboole_0(C_80)
      | ~ m1_subset_1(B_79,k1_zfmisc_1(u1_struct_0(A_78)))
      | v1_xboole_0(B_79)
      | ~ l1_struct_0(A_78)
      | v2_struct_0(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_232,plain,(
    ! [A_78] :
      ( v4_orders_2(k3_yellow19(A_78,k2_struct_0('#skF_2'),'#skF_3'))
      | ~ v13_waybel_0('#skF_3',k3_yellow_1(k2_struct_0('#skF_2')))
      | ~ v2_waybel_0('#skF_3',k3_yellow_1(k2_struct_0('#skF_2')))
      | v1_xboole_0('#skF_3')
      | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0(A_78)))
      | v1_xboole_0(k2_struct_0('#skF_2'))
      | ~ l1_struct_0(A_78)
      | v2_struct_0(A_78) ) ),
    inference(resolution,[status(thm)],[c_48,c_227])).

tff(c_236,plain,(
    ! [A_78] :
      ( v4_orders_2(k3_yellow19(A_78,k2_struct_0('#skF_2'),'#skF_3'))
      | v1_xboole_0('#skF_3')
      | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0(A_78)))
      | v1_xboole_0(k2_struct_0('#skF_2'))
      | ~ l1_struct_0(A_78)
      | v2_struct_0(A_78) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_232])).

tff(c_248,plain,(
    ! [A_81] :
      ( v4_orders_2(k3_yellow19(A_81,k2_struct_0('#skF_2'),'#skF_3'))
      | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0(A_81)))
      | ~ l1_struct_0(A_81)
      | v2_struct_0(A_81) ) ),
    inference(negUnitSimplification,[status(thm)],[c_202,c_56,c_236])).

tff(c_254,plain,
    ( v4_orders_2(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'))
    | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_2')))
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_248])).

tff(c_257,plain,
    ( v4_orders_2(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'))
    | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_2')))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_221,c_254])).

tff(c_258,plain,
    ( v4_orders_2(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'))
    | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_257])).

tff(c_265,plain,(
    v4_orders_2(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_247,c_258])).

tff(c_444,plain,(
    ! [A_113,B_114,C_115] :
      ( l1_waybel_0(k3_yellow19(A_113,B_114,C_115),A_113)
      | ~ m1_subset_1(C_115,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_114))))
      | ~ v13_waybel_0(C_115,k3_yellow_1(B_114))
      | ~ v2_waybel_0(C_115,k3_yellow_1(B_114))
      | v1_xboole_0(C_115)
      | ~ m1_subset_1(B_114,k1_zfmisc_1(u1_struct_0(A_113)))
      | v1_xboole_0(B_114)
      | ~ l1_struct_0(A_113)
      | v2_struct_0(A_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_449,plain,(
    ! [A_113] :
      ( l1_waybel_0(k3_yellow19(A_113,k2_struct_0('#skF_2'),'#skF_3'),A_113)
      | ~ v13_waybel_0('#skF_3',k3_yellow_1(k2_struct_0('#skF_2')))
      | ~ v2_waybel_0('#skF_3',k3_yellow_1(k2_struct_0('#skF_2')))
      | v1_xboole_0('#skF_3')
      | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0(A_113)))
      | v1_xboole_0(k2_struct_0('#skF_2'))
      | ~ l1_struct_0(A_113)
      | v2_struct_0(A_113) ) ),
    inference(resolution,[status(thm)],[c_48,c_444])).

tff(c_453,plain,(
    ! [A_113] :
      ( l1_waybel_0(k3_yellow19(A_113,k2_struct_0('#skF_2'),'#skF_3'),A_113)
      | v1_xboole_0('#skF_3')
      | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0(A_113)))
      | v1_xboole_0(k2_struct_0('#skF_2'))
      | ~ l1_struct_0(A_113)
      | v2_struct_0(A_113) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_449])).

tff(c_455,plain,(
    ! [A_116] :
      ( l1_waybel_0(k3_yellow19(A_116,k2_struct_0('#skF_2'),'#skF_3'),A_116)
      | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0(A_116)))
      | ~ l1_struct_0(A_116)
      | v2_struct_0(A_116) ) ),
    inference(negUnitSimplification,[status(thm)],[c_202,c_56,c_453])).

tff(c_460,plain,
    ( l1_waybel_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'),'#skF_2')
    | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_2')))
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_455])).

tff(c_463,plain,
    ( l1_waybel_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'),'#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_221,c_247,c_460])).

tff(c_464,plain,(
    l1_waybel_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_463])).

tff(c_54,plain,(
    v1_subset_1('#skF_3',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_541,plain,(
    ! [A_130,B_131] :
      ( k2_yellow19(A_130,k3_yellow19(A_130,k2_struct_0(A_130),B_131)) = B_131
      | ~ m1_subset_1(B_131,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_130)))))
      | ~ v13_waybel_0(B_131,k3_yellow_1(k2_struct_0(A_130)))
      | ~ v2_waybel_0(B_131,k3_yellow_1(k2_struct_0(A_130)))
      | ~ v1_subset_1(B_131,u1_struct_0(k3_yellow_1(k2_struct_0(A_130))))
      | v1_xboole_0(B_131)
      | ~ l1_struct_0(A_130)
      | v2_struct_0(A_130) ) ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_546,plain,
    ( k2_yellow19('#skF_2',k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3')) = '#skF_3'
    | ~ v13_waybel_0('#skF_3',k3_yellow_1(k2_struct_0('#skF_2')))
    | ~ v2_waybel_0('#skF_3',k3_yellow_1(k2_struct_0('#skF_2')))
    | ~ v1_subset_1('#skF_3',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2'))))
    | v1_xboole_0('#skF_3')
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_541])).

tff(c_550,plain,
    ( k2_yellow19('#skF_2',k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3')) = '#skF_3'
    | v1_xboole_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_221,c_54,c_52,c_50,c_546])).

tff(c_551,plain,(
    k2_yellow19('#skF_2',k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3')) = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_56,c_550])).

tff(c_42,plain,(
    ! [A_21,B_25,C_27] :
      ( r1_waybel_7(A_21,k2_yellow19(A_21,B_25),C_27)
      | ~ r3_waybel_9(A_21,B_25,C_27)
      | ~ m1_subset_1(C_27,u1_struct_0(A_21))
      | ~ l1_waybel_0(B_25,A_21)
      | ~ v7_waybel_0(B_25)
      | ~ v4_orders_2(B_25)
      | v2_struct_0(B_25)
      | ~ l1_pre_topc(A_21)
      | ~ v2_pre_topc(A_21)
      | v2_struct_0(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_555,plain,(
    ! [C_27] :
      ( r1_waybel_7('#skF_2','#skF_3',C_27)
      | ~ r3_waybel_9('#skF_2',k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'),C_27)
      | ~ m1_subset_1(C_27,u1_struct_0('#skF_2'))
      | ~ l1_waybel_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'),'#skF_2')
      | ~ v7_waybel_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'))
      | ~ v4_orders_2(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'))
      | v2_struct_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_551,c_42])).

tff(c_562,plain,(
    ! [C_27] :
      ( r1_waybel_7('#skF_2','#skF_3',C_27)
      | ~ r3_waybel_9('#skF_2',k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'),C_27)
      | ~ m1_subset_1(C_27,k2_struct_0('#skF_2'))
      | ~ v7_waybel_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'))
      | v2_struct_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_265,c_464,c_90,c_555])).

tff(c_563,plain,(
    ! [C_27] :
      ( r1_waybel_7('#skF_2','#skF_3',C_27)
      | ~ r3_waybel_9('#skF_2',k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'),C_27)
      | ~ m1_subset_1(C_27,k2_struct_0('#skF_2'))
      | ~ v7_waybel_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'))
      | v2_struct_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_562])).

tff(c_568,plain,(
    ~ v7_waybel_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_563])).

tff(c_612,plain,(
    ! [A_141,B_142,C_143] :
      ( v7_waybel_0(k3_yellow19(A_141,B_142,C_143))
      | ~ m1_subset_1(C_143,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_142))))
      | ~ v13_waybel_0(C_143,k3_yellow_1(B_142))
      | ~ v2_waybel_0(C_143,k3_yellow_1(B_142))
      | ~ v1_subset_1(C_143,u1_struct_0(k3_yellow_1(B_142)))
      | v1_xboole_0(C_143)
      | ~ m1_subset_1(B_142,k1_zfmisc_1(u1_struct_0(A_141)))
      | v1_xboole_0(B_142)
      | ~ l1_struct_0(A_141)
      | v2_struct_0(A_141) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_617,plain,(
    ! [A_141] :
      ( v7_waybel_0(k3_yellow19(A_141,k2_struct_0('#skF_2'),'#skF_3'))
      | ~ v13_waybel_0('#skF_3',k3_yellow_1(k2_struct_0('#skF_2')))
      | ~ v2_waybel_0('#skF_3',k3_yellow_1(k2_struct_0('#skF_2')))
      | ~ v1_subset_1('#skF_3',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2'))))
      | v1_xboole_0('#skF_3')
      | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0(A_141)))
      | v1_xboole_0(k2_struct_0('#skF_2'))
      | ~ l1_struct_0(A_141)
      | v2_struct_0(A_141) ) ),
    inference(resolution,[status(thm)],[c_48,c_612])).

tff(c_621,plain,(
    ! [A_141] :
      ( v7_waybel_0(k3_yellow19(A_141,k2_struct_0('#skF_2'),'#skF_3'))
      | v1_xboole_0('#skF_3')
      | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0(A_141)))
      | v1_xboole_0(k2_struct_0('#skF_2'))
      | ~ l1_struct_0(A_141)
      | v2_struct_0(A_141) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_617])).

tff(c_623,plain,(
    ! [A_144] :
      ( v7_waybel_0(k3_yellow19(A_144,k2_struct_0('#skF_2'),'#skF_3'))
      | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0(A_144)))
      | ~ l1_struct_0(A_144)
      | v2_struct_0(A_144) ) ),
    inference(negUnitSimplification,[status(thm)],[c_202,c_56,c_621])).

tff(c_629,plain,
    ( v7_waybel_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'))
    | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_2')))
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_623])).

tff(c_632,plain,
    ( v7_waybel_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_221,c_247,c_629])).

tff(c_634,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_568,c_632])).

tff(c_635,plain,(
    ! [C_27] :
      ( v2_struct_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'))
      | r1_waybel_7('#skF_2','#skF_3',C_27)
      | ~ r3_waybel_9('#skF_2',k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'),C_27)
      | ~ m1_subset_1(C_27,k2_struct_0('#skF_2')) ) ),
    inference(splitRight,[status(thm)],[c_563])).

tff(c_637,plain,(
    v2_struct_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_635])).

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

tff(c_642,plain,
    ( ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2')))))
    | ~ v13_waybel_0('#skF_3',k3_yellow_1(k2_struct_0('#skF_2')))
    | ~ v2_waybel_0('#skF_3',k3_yellow_1(k2_struct_0('#skF_2')))
    | v1_xboole_0('#skF_3')
    | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v1_xboole_0(k2_struct_0('#skF_2'))
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_637,c_32])).

tff(c_645,plain,
    ( v1_xboole_0('#skF_3')
    | v1_xboole_0(k2_struct_0('#skF_2'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_221,c_247,c_90,c_52,c_50,c_48,c_642])).

tff(c_647,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_202,c_56,c_645])).

tff(c_649,plain,(
    ~ v2_struct_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3')) ),
    inference(splitRight,[status(thm)],[c_635])).

tff(c_636,plain,(
    v7_waybel_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3')) ),
    inference(splitRight,[status(thm)],[c_563])).

tff(c_40,plain,(
    ! [A_21,B_25,C_27] :
      ( r3_waybel_9(A_21,B_25,C_27)
      | ~ r1_waybel_7(A_21,k2_yellow19(A_21,B_25),C_27)
      | ~ m1_subset_1(C_27,u1_struct_0(A_21))
      | ~ l1_waybel_0(B_25,A_21)
      | ~ v7_waybel_0(B_25)
      | ~ v4_orders_2(B_25)
      | v2_struct_0(B_25)
      | ~ l1_pre_topc(A_21)
      | ~ v2_pre_topc(A_21)
      | v2_struct_0(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_558,plain,(
    ! [C_27] :
      ( r3_waybel_9('#skF_2',k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'),C_27)
      | ~ r1_waybel_7('#skF_2','#skF_3',C_27)
      | ~ m1_subset_1(C_27,u1_struct_0('#skF_2'))
      | ~ l1_waybel_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'),'#skF_2')
      | ~ v7_waybel_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'))
      | ~ v4_orders_2(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'))
      | v2_struct_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_551,c_40])).

tff(c_565,plain,(
    ! [C_27] :
      ( r3_waybel_9('#skF_2',k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'),C_27)
      | ~ r1_waybel_7('#skF_2','#skF_3',C_27)
      | ~ m1_subset_1(C_27,k2_struct_0('#skF_2'))
      | ~ v7_waybel_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'))
      | v2_struct_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_265,c_464,c_90,c_558])).

tff(c_566,plain,(
    ! [C_27] :
      ( r3_waybel_9('#skF_2',k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'),C_27)
      | ~ r1_waybel_7('#skF_2','#skF_3',C_27)
      | ~ m1_subset_1(C_27,k2_struct_0('#skF_2'))
      | ~ v7_waybel_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'))
      | v2_struct_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_565])).

tff(c_652,plain,(
    ! [C_27] :
      ( r3_waybel_9('#skF_2',k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'),C_27)
      | ~ r1_waybel_7('#skF_2','#skF_3',C_27)
      | ~ m1_subset_1(C_27,k2_struct_0('#skF_2'))
      | v2_struct_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_636,c_566])).

tff(c_654,plain,(
    ! [C_146] :
      ( r3_waybel_9('#skF_2',k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'),C_146)
      | ~ r1_waybel_7('#skF_2','#skF_3',C_146)
      | ~ m1_subset_1(C_146,k2_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_649,c_652])).

tff(c_660,plain,
    ( ~ r1_waybel_7('#skF_2','#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_4',k2_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_654,c_107])).

tff(c_665,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_120,c_660])).

tff(c_666,plain,(
    ~ r1_waybel_7('#skF_2','#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_667,plain,(
    r3_waybel_9('#skF_2',k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_737,plain,(
    ! [A_177,B_178,C_179] :
      ( v4_orders_2(k3_yellow19(A_177,B_178,C_179))
      | ~ m1_subset_1(C_179,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_178))))
      | ~ v13_waybel_0(C_179,k3_yellow_1(B_178))
      | ~ v2_waybel_0(C_179,k3_yellow_1(B_178))
      | v1_xboole_0(C_179)
      | ~ m1_subset_1(B_178,k1_zfmisc_1(u1_struct_0(A_177)))
      | v1_xboole_0(B_178)
      | ~ l1_struct_0(A_177)
      | v2_struct_0(A_177) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_742,plain,(
    ! [A_177] :
      ( v4_orders_2(k3_yellow19(A_177,k2_struct_0('#skF_2'),'#skF_3'))
      | ~ v13_waybel_0('#skF_3',k3_yellow_1(k2_struct_0('#skF_2')))
      | ~ v2_waybel_0('#skF_3',k3_yellow_1(k2_struct_0('#skF_2')))
      | v1_xboole_0('#skF_3')
      | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0(A_177)))
      | v1_xboole_0(k2_struct_0('#skF_2'))
      | ~ l1_struct_0(A_177)
      | v2_struct_0(A_177) ) ),
    inference(resolution,[status(thm)],[c_48,c_737])).

tff(c_746,plain,(
    ! [A_177] :
      ( v4_orders_2(k3_yellow19(A_177,k2_struct_0('#skF_2'),'#skF_3'))
      | v1_xboole_0('#skF_3')
      | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0(A_177)))
      | v1_xboole_0(k2_struct_0('#skF_2'))
      | ~ l1_struct_0(A_177)
      | v2_struct_0(A_177) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_742])).

tff(c_747,plain,(
    ! [A_177] :
      ( v4_orders_2(k3_yellow19(A_177,k2_struct_0('#skF_2'),'#skF_3'))
      | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0(A_177)))
      | v1_xboole_0(k2_struct_0('#skF_2'))
      | ~ l1_struct_0(A_177)
      | v2_struct_0(A_177) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_746])).

tff(c_748,plain,(
    v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_747])).

tff(c_751,plain,
    ( ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_748,c_16])).

tff(c_754,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_751])).

tff(c_757,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_14,c_754])).

tff(c_761,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_757])).

tff(c_763,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_747])).

tff(c_765,plain,(
    ! [A_183] :
      ( v4_orders_2(k3_yellow19(A_183,k2_struct_0('#skF_2'),'#skF_3'))
      | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0(A_183)))
      | ~ l1_struct_0(A_183)
      | v2_struct_0(A_183) ) ),
    inference(splitRight,[status(thm)],[c_747])).

tff(c_771,plain,
    ( v4_orders_2(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'))
    | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_2')))
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_765])).

tff(c_773,plain,
    ( v4_orders_2(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'))
    | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_2')))
    | ~ l1_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_771])).

tff(c_774,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_773])).

tff(c_777,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_14,c_774])).

tff(c_781,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_777])).

tff(c_783,plain,(
    l1_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_773])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_669,plain,(
    ! [A_149,B_150] :
      ( ~ r2_hidden('#skF_1'(A_149,B_150),B_150)
      | r1_tarski(A_149,B_150) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_674,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_669])).

tff(c_782,plain,
    ( ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_2')))
    | v4_orders_2(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3')) ),
    inference(splitRight,[status(thm)],[c_773])).

tff(c_789,plain,(
    ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_782])).

tff(c_792,plain,(
    ~ r1_tarski(k2_struct_0('#skF_2'),k2_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_10,c_789])).

tff(c_796,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_674,c_792])).

tff(c_798,plain,(
    m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_782])).

tff(c_797,plain,(
    v4_orders_2(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3')) ),
    inference(splitRight,[status(thm)],[c_782])).

tff(c_1035,plain,(
    ! [A_222,B_223,C_224] :
      ( v7_waybel_0(k3_yellow19(A_222,B_223,C_224))
      | ~ m1_subset_1(C_224,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_223))))
      | ~ v13_waybel_0(C_224,k3_yellow_1(B_223))
      | ~ v2_waybel_0(C_224,k3_yellow_1(B_223))
      | ~ v1_subset_1(C_224,u1_struct_0(k3_yellow_1(B_223)))
      | v1_xboole_0(C_224)
      | ~ m1_subset_1(B_223,k1_zfmisc_1(u1_struct_0(A_222)))
      | v1_xboole_0(B_223)
      | ~ l1_struct_0(A_222)
      | v2_struct_0(A_222) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_1040,plain,(
    ! [A_222] :
      ( v7_waybel_0(k3_yellow19(A_222,k2_struct_0('#skF_2'),'#skF_3'))
      | ~ v13_waybel_0('#skF_3',k3_yellow_1(k2_struct_0('#skF_2')))
      | ~ v2_waybel_0('#skF_3',k3_yellow_1(k2_struct_0('#skF_2')))
      | ~ v1_subset_1('#skF_3',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2'))))
      | v1_xboole_0('#skF_3')
      | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0(A_222)))
      | v1_xboole_0(k2_struct_0('#skF_2'))
      | ~ l1_struct_0(A_222)
      | v2_struct_0(A_222) ) ),
    inference(resolution,[status(thm)],[c_48,c_1035])).

tff(c_1044,plain,(
    ! [A_222] :
      ( v7_waybel_0(k3_yellow19(A_222,k2_struct_0('#skF_2'),'#skF_3'))
      | v1_xboole_0('#skF_3')
      | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0(A_222)))
      | v1_xboole_0(k2_struct_0('#skF_2'))
      | ~ l1_struct_0(A_222)
      | v2_struct_0(A_222) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_1040])).

tff(c_1046,plain,(
    ! [A_225] :
      ( v7_waybel_0(k3_yellow19(A_225,k2_struct_0('#skF_2'),'#skF_3'))
      | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0(A_225)))
      | ~ l1_struct_0(A_225)
      | v2_struct_0(A_225) ) ),
    inference(negUnitSimplification,[status(thm)],[c_763,c_56,c_1044])).

tff(c_1052,plain,
    ( v7_waybel_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'))
    | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_2')))
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_1046])).

tff(c_1055,plain,
    ( v7_waybel_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_783,c_798,c_1052])).

tff(c_1056,plain,(
    v7_waybel_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_1055])).

tff(c_886,plain,(
    ! [A_195,B_196,C_197] :
      ( l1_waybel_0(k3_yellow19(A_195,B_196,C_197),A_195)
      | ~ m1_subset_1(C_197,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_196))))
      | ~ v13_waybel_0(C_197,k3_yellow_1(B_196))
      | ~ v2_waybel_0(C_197,k3_yellow_1(B_196))
      | v1_xboole_0(C_197)
      | ~ m1_subset_1(B_196,k1_zfmisc_1(u1_struct_0(A_195)))
      | v1_xboole_0(B_196)
      | ~ l1_struct_0(A_195)
      | v2_struct_0(A_195) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_891,plain,(
    ! [A_195] :
      ( l1_waybel_0(k3_yellow19(A_195,k2_struct_0('#skF_2'),'#skF_3'),A_195)
      | ~ v13_waybel_0('#skF_3',k3_yellow_1(k2_struct_0('#skF_2')))
      | ~ v2_waybel_0('#skF_3',k3_yellow_1(k2_struct_0('#skF_2')))
      | v1_xboole_0('#skF_3')
      | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0(A_195)))
      | v1_xboole_0(k2_struct_0('#skF_2'))
      | ~ l1_struct_0(A_195)
      | v2_struct_0(A_195) ) ),
    inference(resolution,[status(thm)],[c_48,c_886])).

tff(c_895,plain,(
    ! [A_195] :
      ( l1_waybel_0(k3_yellow19(A_195,k2_struct_0('#skF_2'),'#skF_3'),A_195)
      | v1_xboole_0('#skF_3')
      | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0(A_195)))
      | v1_xboole_0(k2_struct_0('#skF_2'))
      | ~ l1_struct_0(A_195)
      | v2_struct_0(A_195) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_891])).

tff(c_897,plain,(
    ! [A_198] :
      ( l1_waybel_0(k3_yellow19(A_198,k2_struct_0('#skF_2'),'#skF_3'),A_198)
      | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0(A_198)))
      | ~ l1_struct_0(A_198)
      | v2_struct_0(A_198) ) ),
    inference(negUnitSimplification,[status(thm)],[c_763,c_56,c_895])).

tff(c_902,plain,
    ( l1_waybel_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'),'#skF_2')
    | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_2')))
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_897])).

tff(c_905,plain,
    ( l1_waybel_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'),'#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_783,c_798,c_902])).

tff(c_906,plain,(
    l1_waybel_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_905])).

tff(c_1135,plain,(
    ! [A_239,B_240] :
      ( k2_yellow19(A_239,k3_yellow19(A_239,k2_struct_0(A_239),B_240)) = B_240
      | ~ m1_subset_1(B_240,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_239)))))
      | ~ v13_waybel_0(B_240,k3_yellow_1(k2_struct_0(A_239)))
      | ~ v2_waybel_0(B_240,k3_yellow_1(k2_struct_0(A_239)))
      | ~ v1_subset_1(B_240,u1_struct_0(k3_yellow_1(k2_struct_0(A_239))))
      | v1_xboole_0(B_240)
      | ~ l1_struct_0(A_239)
      | v2_struct_0(A_239) ) ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_1140,plain,
    ( k2_yellow19('#skF_2',k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3')) = '#skF_3'
    | ~ v13_waybel_0('#skF_3',k3_yellow_1(k2_struct_0('#skF_2')))
    | ~ v2_waybel_0('#skF_3',k3_yellow_1(k2_struct_0('#skF_2')))
    | ~ v1_subset_1('#skF_3',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2'))))
    | v1_xboole_0('#skF_3')
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_1135])).

tff(c_1144,plain,
    ( k2_yellow19('#skF_2',k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3')) = '#skF_3'
    | v1_xboole_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_783,c_54,c_52,c_50,c_1140])).

tff(c_1145,plain,(
    k2_yellow19('#skF_2',k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3')) = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_56,c_1144])).

tff(c_1149,plain,(
    ! [C_27] :
      ( r1_waybel_7('#skF_2','#skF_3',C_27)
      | ~ r3_waybel_9('#skF_2',k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'),C_27)
      | ~ m1_subset_1(C_27,u1_struct_0('#skF_2'))
      | ~ l1_waybel_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'),'#skF_2')
      | ~ v7_waybel_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'))
      | ~ v4_orders_2(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'))
      | v2_struct_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1145,c_42])).

tff(c_1156,plain,(
    ! [C_27] :
      ( r1_waybel_7('#skF_2','#skF_3',C_27)
      | ~ r3_waybel_9('#skF_2',k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'),C_27)
      | ~ m1_subset_1(C_27,k2_struct_0('#skF_2'))
      | v2_struct_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_797,c_1056,c_906,c_90,c_1149])).

tff(c_1157,plain,(
    ! [C_27] :
      ( r1_waybel_7('#skF_2','#skF_3',C_27)
      | ~ r3_waybel_9('#skF_2',k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'),C_27)
      | ~ m1_subset_1(C_27,k2_struct_0('#skF_2'))
      | v2_struct_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_1156])).

tff(c_1162,plain,(
    v2_struct_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1157])).

tff(c_1164,plain,
    ( ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2')))))
    | ~ v13_waybel_0('#skF_3',k3_yellow_1(k2_struct_0('#skF_2')))
    | ~ v2_waybel_0('#skF_3',k3_yellow_1(k2_struct_0('#skF_2')))
    | v1_xboole_0('#skF_3')
    | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v1_xboole_0(k2_struct_0('#skF_2'))
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_1162,c_32])).

tff(c_1167,plain,
    ( v1_xboole_0('#skF_3')
    | v1_xboole_0(k2_struct_0('#skF_2'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_783,c_798,c_90,c_52,c_50,c_48,c_1164])).

tff(c_1169,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_763,c_56,c_1167])).

tff(c_1191,plain,(
    ! [C_245] :
      ( r1_waybel_7('#skF_2','#skF_3',C_245)
      | ~ r3_waybel_9('#skF_2',k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'),C_245)
      | ~ m1_subset_1(C_245,k2_struct_0('#skF_2')) ) ),
    inference(splitRight,[status(thm)],[c_1157])).

tff(c_1197,plain,
    ( r1_waybel_7('#skF_2','#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_4',k2_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_667,c_1191])).

tff(c_1201,plain,(
    r1_waybel_7('#skF_2','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_1197])).

tff(c_1203,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_666,c_1201])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:20:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.88/1.62  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.88/1.65  
% 3.88/1.65  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.88/1.65  %$ r3_waybel_9 > r1_waybel_7 > v6_waybel_0 > v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_hidden > r1_tarski > m1_subset_1 > l1_waybel_0 > v7_waybel_0 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k3_yellow19 > k2_yellow19 > #nlpp > u1_struct_0 > k3_yellow_1 > k3_lattice3 > k2_struct_0 > k1_zfmisc_1 > k1_lattice3 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 3.88/1.65  
% 3.88/1.65  %Foreground sorts:
% 3.88/1.65  
% 3.88/1.65  
% 3.88/1.65  %Background operators:
% 3.88/1.65  
% 3.88/1.65  
% 3.88/1.65  %Foreground operators:
% 3.88/1.65  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.88/1.65  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 3.88/1.65  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.88/1.65  tff(k3_lattice3, type, k3_lattice3: $i > $i).
% 3.88/1.65  tff(v6_waybel_0, type, v6_waybel_0: ($i * $i) > $o).
% 3.88/1.65  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.88/1.65  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 3.88/1.65  tff(k3_yellow_1, type, k3_yellow_1: $i > $i).
% 3.88/1.65  tff(v2_waybel_0, type, v2_waybel_0: ($i * $i) > $o).
% 3.88/1.65  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.88/1.65  tff(v7_waybel_0, type, v7_waybel_0: $i > $o).
% 3.88/1.65  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.88/1.65  tff(r3_waybel_9, type, r3_waybel_9: ($i * $i * $i) > $o).
% 3.88/1.65  tff('#skF_2', type, '#skF_2': $i).
% 3.88/1.65  tff('#skF_3', type, '#skF_3': $i).
% 3.88/1.65  tff(k1_lattice3, type, k1_lattice3: $i > $i).
% 3.88/1.65  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 3.88/1.65  tff(r1_waybel_7, type, r1_waybel_7: ($i * $i * $i) > $o).
% 3.88/1.65  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.88/1.65  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.88/1.65  tff(k2_yellow19, type, k2_yellow19: ($i * $i) > $i).
% 3.88/1.65  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.88/1.65  tff(l1_waybel_0, type, l1_waybel_0: ($i * $i) > $o).
% 3.88/1.65  tff('#skF_4', type, '#skF_4': $i).
% 3.88/1.65  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.88/1.65  tff(k3_yellow19, type, k3_yellow19: ($i * $i * $i) > $i).
% 3.88/1.65  tff(v13_waybel_0, type, v13_waybel_0: ($i * $i) > $o).
% 3.88/1.65  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.88/1.65  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.88/1.65  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.88/1.65  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 3.88/1.65  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.88/1.65  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.88/1.65  
% 4.21/1.69  tff(f_206, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((((~v1_xboole_0(B) & v1_subset_1(B, u1_struct_0(k3_yellow_1(k2_struct_0(A))))) & v2_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & v13_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A)))))) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r3_waybel_9(A, k3_yellow19(A, k2_struct_0(A), B), C) <=> r1_waybel_7(A, B, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_yellow19)).
% 4.21/1.69  tff(f_44, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 4.21/1.69  tff(f_40, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 4.21/1.69  tff(f_108, axiom, (![A, B, C]: ((((((((~v2_struct_0(A) & l1_struct_0(A)) & ~v1_xboole_0(B)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) & ~v1_xboole_0(C)) & v2_waybel_0(C, k3_yellow_1(B))) & v13_waybel_0(C, k3_yellow_1(B))) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B))))) => (((~v2_struct_0(k3_yellow19(A, B, C)) & v3_orders_2(k3_yellow19(A, B, C))) & v4_orders_2(k3_yellow19(A, B, C))) & v6_waybel_0(k3_yellow19(A, B, C), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_yellow19)).
% 4.21/1.69  tff(f_52, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(k2_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc5_struct_0)).
% 4.21/1.69  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 4.21/1.69  tff(f_36, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 4.21/1.69  tff(f_80, axiom, (![A, B, C]: ((((((((~v2_struct_0(A) & l1_struct_0(A)) & ~v1_xboole_0(B)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) & ~v1_xboole_0(C)) & v2_waybel_0(C, k3_yellow_1(B))) & v13_waybel_0(C, k3_yellow_1(B))) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B))))) => ((~v2_struct_0(k3_yellow19(A, B, C)) & v6_waybel_0(k3_yellow19(A, B, C), A)) & l1_waybel_0(k3_yellow19(A, B, C), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_yellow19)).
% 4.21/1.69  tff(f_179, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: (((((~v1_xboole_0(B) & v1_subset_1(B, u1_struct_0(k3_yellow_1(k2_struct_0(A))))) & v2_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & v13_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A)))))) => (B = k2_yellow19(A, k3_yellow19(A, k2_struct_0(A), B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t15_yellow19)).
% 4.21/1.69  tff(f_160, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r3_waybel_9(A, B, C) <=> r1_waybel_7(A, k2_yellow19(A, B), C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_yellow19)).
% 4.21/1.69  tff(f_136, axiom, (![A, B, C]: (((((((((~v2_struct_0(A) & l1_struct_0(A)) & ~v1_xboole_0(B)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) & ~v1_xboole_0(C)) & v1_subset_1(C, u1_struct_0(k3_yellow_1(B)))) & v2_waybel_0(C, k3_yellow_1(B))) & v13_waybel_0(C, k3_yellow_1(B))) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B))))) => ((~v2_struct_0(k3_yellow19(A, B, C)) & v6_waybel_0(k3_yellow19(A, B, C), A)) & v7_waybel_0(k3_yellow19(A, B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc5_yellow19)).
% 4.21/1.69  tff(c_58, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_206])).
% 4.21/1.69  tff(c_14, plain, (![A_9]: (l1_struct_0(A_9) | ~l1_pre_topc(A_9))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.21/1.69  tff(c_81, plain, (![A_37]: (u1_struct_0(A_37)=k2_struct_0(A_37) | ~l1_struct_0(A_37))), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.21/1.69  tff(c_86, plain, (![A_38]: (u1_struct_0(A_38)=k2_struct_0(A_38) | ~l1_pre_topc(A_38))), inference(resolution, [status(thm)], [c_14, c_81])).
% 4.21/1.69  tff(c_90, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_58, c_86])).
% 4.21/1.69  tff(c_46, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_206])).
% 4.21/1.69  tff(c_91, plain, (m1_subset_1('#skF_4', k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_46])).
% 4.21/1.69  tff(c_64, plain, (~r1_waybel_7('#skF_2', '#skF_3', '#skF_4') | ~r3_waybel_9('#skF_2', k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_206])).
% 4.21/1.69  tff(c_107, plain, (~r3_waybel_9('#skF_2', k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'), '#skF_4')), inference(splitLeft, [status(thm)], [c_64])).
% 4.21/1.69  tff(c_70, plain, (r3_waybel_9('#skF_2', k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'), '#skF_4') | r1_waybel_7('#skF_2', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_206])).
% 4.21/1.69  tff(c_120, plain, (r1_waybel_7('#skF_2', '#skF_3', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_107, c_70])).
% 4.21/1.69  tff(c_62, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_206])).
% 4.21/1.69  tff(c_56, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_206])).
% 4.21/1.69  tff(c_52, plain, (v2_waybel_0('#skF_3', k3_yellow_1(k2_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_206])).
% 4.21/1.69  tff(c_50, plain, (v13_waybel_0('#skF_3', k3_yellow_1(k2_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_206])).
% 4.21/1.69  tff(c_48, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2')))))), inference(cnfTransformation, [status(thm)], [f_206])).
% 4.21/1.69  tff(c_176, plain, (![A_74, B_75, C_76]: (v3_orders_2(k3_yellow19(A_74, B_75, C_76)) | ~m1_subset_1(C_76, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_75)))) | ~v13_waybel_0(C_76, k3_yellow_1(B_75)) | ~v2_waybel_0(C_76, k3_yellow_1(B_75)) | v1_xboole_0(C_76) | ~m1_subset_1(B_75, k1_zfmisc_1(u1_struct_0(A_74))) | v1_xboole_0(B_75) | ~l1_struct_0(A_74) | v2_struct_0(A_74))), inference(cnfTransformation, [status(thm)], [f_108])).
% 4.21/1.69  tff(c_181, plain, (![A_74]: (v3_orders_2(k3_yellow19(A_74, k2_struct_0('#skF_2'), '#skF_3')) | ~v13_waybel_0('#skF_3', k3_yellow_1(k2_struct_0('#skF_2'))) | ~v2_waybel_0('#skF_3', k3_yellow_1(k2_struct_0('#skF_2'))) | v1_xboole_0('#skF_3') | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(u1_struct_0(A_74))) | v1_xboole_0(k2_struct_0('#skF_2')) | ~l1_struct_0(A_74) | v2_struct_0(A_74))), inference(resolution, [status(thm)], [c_48, c_176])).
% 4.21/1.69  tff(c_185, plain, (![A_74]: (v3_orders_2(k3_yellow19(A_74, k2_struct_0('#skF_2'), '#skF_3')) | v1_xboole_0('#skF_3') | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(u1_struct_0(A_74))) | v1_xboole_0(k2_struct_0('#skF_2')) | ~l1_struct_0(A_74) | v2_struct_0(A_74))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_181])).
% 4.21/1.69  tff(c_186, plain, (![A_74]: (v3_orders_2(k3_yellow19(A_74, k2_struct_0('#skF_2'), '#skF_3')) | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(u1_struct_0(A_74))) | v1_xboole_0(k2_struct_0('#skF_2')) | ~l1_struct_0(A_74) | v2_struct_0(A_74))), inference(negUnitSimplification, [status(thm)], [c_56, c_185])).
% 4.21/1.69  tff(c_187, plain, (v1_xboole_0(k2_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_186])).
% 4.21/1.69  tff(c_16, plain, (![A_10]: (~v1_xboole_0(k2_struct_0(A_10)) | ~l1_struct_0(A_10) | v2_struct_0(A_10))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.21/1.69  tff(c_190, plain, (~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_187, c_16])).
% 4.21/1.69  tff(c_193, plain, (~l1_struct_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_62, c_190])).
% 4.21/1.69  tff(c_196, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_14, c_193])).
% 4.21/1.69  tff(c_200, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_196])).
% 4.21/1.69  tff(c_202, plain, (~v1_xboole_0(k2_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_186])).
% 4.21/1.69  tff(c_203, plain, (![A_77]: (v3_orders_2(k3_yellow19(A_77, k2_struct_0('#skF_2'), '#skF_3')) | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(u1_struct_0(A_77))) | ~l1_struct_0(A_77) | v2_struct_0(A_77))), inference(splitRight, [status(thm)], [c_186])).
% 4.21/1.69  tff(c_209, plain, (v3_orders_2(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3')) | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_90, c_203])).
% 4.21/1.69  tff(c_211, plain, (v3_orders_2(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3')) | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_struct_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_62, c_209])).
% 4.21/1.69  tff(c_212, plain, (~l1_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_211])).
% 4.21/1.69  tff(c_215, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_14, c_212])).
% 4.21/1.69  tff(c_219, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_215])).
% 4.21/1.69  tff(c_221, plain, (l1_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_211])).
% 4.21/1.69  tff(c_109, plain, (![A_46, B_47]: (r2_hidden('#skF_1'(A_46, B_47), A_46) | r1_tarski(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.21/1.69  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.21/1.69  tff(c_114, plain, (![A_46]: (r1_tarski(A_46, A_46))), inference(resolution, [status(thm)], [c_109, c_4])).
% 4.21/1.69  tff(c_10, plain, (![A_6, B_7]: (m1_subset_1(A_6, k1_zfmisc_1(B_7)) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.21/1.69  tff(c_220, plain, (~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_2'))) | v3_orders_2(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'))), inference(splitRight, [status(thm)], [c_211])).
% 4.21/1.69  tff(c_238, plain, (~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_2')))), inference(splitLeft, [status(thm)], [c_220])).
% 4.21/1.69  tff(c_241, plain, (~r1_tarski(k2_struct_0('#skF_2'), k2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_10, c_238])).
% 4.21/1.69  tff(c_245, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_114, c_241])).
% 4.21/1.69  tff(c_247, plain, (m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_220])).
% 4.21/1.69  tff(c_60, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_206])).
% 4.21/1.69  tff(c_227, plain, (![A_78, B_79, C_80]: (v4_orders_2(k3_yellow19(A_78, B_79, C_80)) | ~m1_subset_1(C_80, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_79)))) | ~v13_waybel_0(C_80, k3_yellow_1(B_79)) | ~v2_waybel_0(C_80, k3_yellow_1(B_79)) | v1_xboole_0(C_80) | ~m1_subset_1(B_79, k1_zfmisc_1(u1_struct_0(A_78))) | v1_xboole_0(B_79) | ~l1_struct_0(A_78) | v2_struct_0(A_78))), inference(cnfTransformation, [status(thm)], [f_108])).
% 4.21/1.69  tff(c_232, plain, (![A_78]: (v4_orders_2(k3_yellow19(A_78, k2_struct_0('#skF_2'), '#skF_3')) | ~v13_waybel_0('#skF_3', k3_yellow_1(k2_struct_0('#skF_2'))) | ~v2_waybel_0('#skF_3', k3_yellow_1(k2_struct_0('#skF_2'))) | v1_xboole_0('#skF_3') | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(u1_struct_0(A_78))) | v1_xboole_0(k2_struct_0('#skF_2')) | ~l1_struct_0(A_78) | v2_struct_0(A_78))), inference(resolution, [status(thm)], [c_48, c_227])).
% 4.21/1.69  tff(c_236, plain, (![A_78]: (v4_orders_2(k3_yellow19(A_78, k2_struct_0('#skF_2'), '#skF_3')) | v1_xboole_0('#skF_3') | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(u1_struct_0(A_78))) | v1_xboole_0(k2_struct_0('#skF_2')) | ~l1_struct_0(A_78) | v2_struct_0(A_78))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_232])).
% 4.21/1.69  tff(c_248, plain, (![A_81]: (v4_orders_2(k3_yellow19(A_81, k2_struct_0('#skF_2'), '#skF_3')) | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(u1_struct_0(A_81))) | ~l1_struct_0(A_81) | v2_struct_0(A_81))), inference(negUnitSimplification, [status(thm)], [c_202, c_56, c_236])).
% 4.21/1.69  tff(c_254, plain, (v4_orders_2(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3')) | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_90, c_248])).
% 4.21/1.69  tff(c_257, plain, (v4_orders_2(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3')) | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_2'))) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_221, c_254])).
% 4.21/1.69  tff(c_258, plain, (v4_orders_2(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3')) | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_62, c_257])).
% 4.21/1.69  tff(c_265, plain, (v4_orders_2(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_247, c_258])).
% 4.21/1.69  tff(c_444, plain, (![A_113, B_114, C_115]: (l1_waybel_0(k3_yellow19(A_113, B_114, C_115), A_113) | ~m1_subset_1(C_115, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_114)))) | ~v13_waybel_0(C_115, k3_yellow_1(B_114)) | ~v2_waybel_0(C_115, k3_yellow_1(B_114)) | v1_xboole_0(C_115) | ~m1_subset_1(B_114, k1_zfmisc_1(u1_struct_0(A_113))) | v1_xboole_0(B_114) | ~l1_struct_0(A_113) | v2_struct_0(A_113))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.21/1.69  tff(c_449, plain, (![A_113]: (l1_waybel_0(k3_yellow19(A_113, k2_struct_0('#skF_2'), '#skF_3'), A_113) | ~v13_waybel_0('#skF_3', k3_yellow_1(k2_struct_0('#skF_2'))) | ~v2_waybel_0('#skF_3', k3_yellow_1(k2_struct_0('#skF_2'))) | v1_xboole_0('#skF_3') | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(u1_struct_0(A_113))) | v1_xboole_0(k2_struct_0('#skF_2')) | ~l1_struct_0(A_113) | v2_struct_0(A_113))), inference(resolution, [status(thm)], [c_48, c_444])).
% 4.21/1.69  tff(c_453, plain, (![A_113]: (l1_waybel_0(k3_yellow19(A_113, k2_struct_0('#skF_2'), '#skF_3'), A_113) | v1_xboole_0('#skF_3') | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(u1_struct_0(A_113))) | v1_xboole_0(k2_struct_0('#skF_2')) | ~l1_struct_0(A_113) | v2_struct_0(A_113))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_449])).
% 4.21/1.69  tff(c_455, plain, (![A_116]: (l1_waybel_0(k3_yellow19(A_116, k2_struct_0('#skF_2'), '#skF_3'), A_116) | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(u1_struct_0(A_116))) | ~l1_struct_0(A_116) | v2_struct_0(A_116))), inference(negUnitSimplification, [status(thm)], [c_202, c_56, c_453])).
% 4.21/1.69  tff(c_460, plain, (l1_waybel_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'), '#skF_2') | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_90, c_455])).
% 4.21/1.69  tff(c_463, plain, (l1_waybel_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'), '#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_221, c_247, c_460])).
% 4.21/1.69  tff(c_464, plain, (l1_waybel_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_62, c_463])).
% 4.21/1.69  tff(c_54, plain, (v1_subset_1('#skF_3', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_206])).
% 4.21/1.69  tff(c_541, plain, (![A_130, B_131]: (k2_yellow19(A_130, k3_yellow19(A_130, k2_struct_0(A_130), B_131))=B_131 | ~m1_subset_1(B_131, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_130))))) | ~v13_waybel_0(B_131, k3_yellow_1(k2_struct_0(A_130))) | ~v2_waybel_0(B_131, k3_yellow_1(k2_struct_0(A_130))) | ~v1_subset_1(B_131, u1_struct_0(k3_yellow_1(k2_struct_0(A_130)))) | v1_xboole_0(B_131) | ~l1_struct_0(A_130) | v2_struct_0(A_130))), inference(cnfTransformation, [status(thm)], [f_179])).
% 4.21/1.69  tff(c_546, plain, (k2_yellow19('#skF_2', k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'))='#skF_3' | ~v13_waybel_0('#skF_3', k3_yellow_1(k2_struct_0('#skF_2'))) | ~v2_waybel_0('#skF_3', k3_yellow_1(k2_struct_0('#skF_2'))) | ~v1_subset_1('#skF_3', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2')))) | v1_xboole_0('#skF_3') | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_48, c_541])).
% 4.21/1.69  tff(c_550, plain, (k2_yellow19('#skF_2', k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'))='#skF_3' | v1_xboole_0('#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_221, c_54, c_52, c_50, c_546])).
% 4.21/1.69  tff(c_551, plain, (k2_yellow19('#skF_2', k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'))='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_62, c_56, c_550])).
% 4.21/1.69  tff(c_42, plain, (![A_21, B_25, C_27]: (r1_waybel_7(A_21, k2_yellow19(A_21, B_25), C_27) | ~r3_waybel_9(A_21, B_25, C_27) | ~m1_subset_1(C_27, u1_struct_0(A_21)) | ~l1_waybel_0(B_25, A_21) | ~v7_waybel_0(B_25) | ~v4_orders_2(B_25) | v2_struct_0(B_25) | ~l1_pre_topc(A_21) | ~v2_pre_topc(A_21) | v2_struct_0(A_21))), inference(cnfTransformation, [status(thm)], [f_160])).
% 4.21/1.69  tff(c_555, plain, (![C_27]: (r1_waybel_7('#skF_2', '#skF_3', C_27) | ~r3_waybel_9('#skF_2', k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'), C_27) | ~m1_subset_1(C_27, u1_struct_0('#skF_2')) | ~l1_waybel_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'), '#skF_2') | ~v7_waybel_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3')) | ~v4_orders_2(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3')) | v2_struct_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_551, c_42])).
% 4.21/1.69  tff(c_562, plain, (![C_27]: (r1_waybel_7('#skF_2', '#skF_3', C_27) | ~r3_waybel_9('#skF_2', k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'), C_27) | ~m1_subset_1(C_27, k2_struct_0('#skF_2')) | ~v7_waybel_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3')) | v2_struct_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_265, c_464, c_90, c_555])).
% 4.21/1.69  tff(c_563, plain, (![C_27]: (r1_waybel_7('#skF_2', '#skF_3', C_27) | ~r3_waybel_9('#skF_2', k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'), C_27) | ~m1_subset_1(C_27, k2_struct_0('#skF_2')) | ~v7_waybel_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3')) | v2_struct_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_62, c_562])).
% 4.21/1.69  tff(c_568, plain, (~v7_waybel_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'))), inference(splitLeft, [status(thm)], [c_563])).
% 4.21/1.69  tff(c_612, plain, (![A_141, B_142, C_143]: (v7_waybel_0(k3_yellow19(A_141, B_142, C_143)) | ~m1_subset_1(C_143, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_142)))) | ~v13_waybel_0(C_143, k3_yellow_1(B_142)) | ~v2_waybel_0(C_143, k3_yellow_1(B_142)) | ~v1_subset_1(C_143, u1_struct_0(k3_yellow_1(B_142))) | v1_xboole_0(C_143) | ~m1_subset_1(B_142, k1_zfmisc_1(u1_struct_0(A_141))) | v1_xboole_0(B_142) | ~l1_struct_0(A_141) | v2_struct_0(A_141))), inference(cnfTransformation, [status(thm)], [f_136])).
% 4.21/1.69  tff(c_617, plain, (![A_141]: (v7_waybel_0(k3_yellow19(A_141, k2_struct_0('#skF_2'), '#skF_3')) | ~v13_waybel_0('#skF_3', k3_yellow_1(k2_struct_0('#skF_2'))) | ~v2_waybel_0('#skF_3', k3_yellow_1(k2_struct_0('#skF_2'))) | ~v1_subset_1('#skF_3', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2')))) | v1_xboole_0('#skF_3') | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(u1_struct_0(A_141))) | v1_xboole_0(k2_struct_0('#skF_2')) | ~l1_struct_0(A_141) | v2_struct_0(A_141))), inference(resolution, [status(thm)], [c_48, c_612])).
% 4.21/1.69  tff(c_621, plain, (![A_141]: (v7_waybel_0(k3_yellow19(A_141, k2_struct_0('#skF_2'), '#skF_3')) | v1_xboole_0('#skF_3') | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(u1_struct_0(A_141))) | v1_xboole_0(k2_struct_0('#skF_2')) | ~l1_struct_0(A_141) | v2_struct_0(A_141))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_617])).
% 4.21/1.69  tff(c_623, plain, (![A_144]: (v7_waybel_0(k3_yellow19(A_144, k2_struct_0('#skF_2'), '#skF_3')) | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(u1_struct_0(A_144))) | ~l1_struct_0(A_144) | v2_struct_0(A_144))), inference(negUnitSimplification, [status(thm)], [c_202, c_56, c_621])).
% 4.21/1.69  tff(c_629, plain, (v7_waybel_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3')) | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_90, c_623])).
% 4.21/1.69  tff(c_632, plain, (v7_waybel_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_221, c_247, c_629])).
% 4.21/1.69  tff(c_634, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_568, c_632])).
% 4.21/1.69  tff(c_635, plain, (![C_27]: (v2_struct_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3')) | r1_waybel_7('#skF_2', '#skF_3', C_27) | ~r3_waybel_9('#skF_2', k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'), C_27) | ~m1_subset_1(C_27, k2_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_563])).
% 4.21/1.69  tff(c_637, plain, (v2_struct_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'))), inference(splitLeft, [status(thm)], [c_635])).
% 4.21/1.69  tff(c_32, plain, (![A_15, B_16, C_17]: (~v2_struct_0(k3_yellow19(A_15, B_16, C_17)) | ~m1_subset_1(C_17, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_16)))) | ~v13_waybel_0(C_17, k3_yellow_1(B_16)) | ~v2_waybel_0(C_17, k3_yellow_1(B_16)) | v1_xboole_0(C_17) | ~m1_subset_1(B_16, k1_zfmisc_1(u1_struct_0(A_15))) | v1_xboole_0(B_16) | ~l1_struct_0(A_15) | v2_struct_0(A_15))), inference(cnfTransformation, [status(thm)], [f_108])).
% 4.21/1.69  tff(c_642, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2'))))) | ~v13_waybel_0('#skF_3', k3_yellow_1(k2_struct_0('#skF_2'))) | ~v2_waybel_0('#skF_3', k3_yellow_1(k2_struct_0('#skF_2'))) | v1_xboole_0('#skF_3') | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | v1_xboole_0(k2_struct_0('#skF_2')) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_637, c_32])).
% 4.21/1.69  tff(c_645, plain, (v1_xboole_0('#skF_3') | v1_xboole_0(k2_struct_0('#skF_2')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_221, c_247, c_90, c_52, c_50, c_48, c_642])).
% 4.21/1.69  tff(c_647, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_202, c_56, c_645])).
% 4.21/1.69  tff(c_649, plain, (~v2_struct_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'))), inference(splitRight, [status(thm)], [c_635])).
% 4.21/1.69  tff(c_636, plain, (v7_waybel_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'))), inference(splitRight, [status(thm)], [c_563])).
% 4.21/1.69  tff(c_40, plain, (![A_21, B_25, C_27]: (r3_waybel_9(A_21, B_25, C_27) | ~r1_waybel_7(A_21, k2_yellow19(A_21, B_25), C_27) | ~m1_subset_1(C_27, u1_struct_0(A_21)) | ~l1_waybel_0(B_25, A_21) | ~v7_waybel_0(B_25) | ~v4_orders_2(B_25) | v2_struct_0(B_25) | ~l1_pre_topc(A_21) | ~v2_pre_topc(A_21) | v2_struct_0(A_21))), inference(cnfTransformation, [status(thm)], [f_160])).
% 4.21/1.69  tff(c_558, plain, (![C_27]: (r3_waybel_9('#skF_2', k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'), C_27) | ~r1_waybel_7('#skF_2', '#skF_3', C_27) | ~m1_subset_1(C_27, u1_struct_0('#skF_2')) | ~l1_waybel_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'), '#skF_2') | ~v7_waybel_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3')) | ~v4_orders_2(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3')) | v2_struct_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_551, c_40])).
% 4.21/1.69  tff(c_565, plain, (![C_27]: (r3_waybel_9('#skF_2', k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'), C_27) | ~r1_waybel_7('#skF_2', '#skF_3', C_27) | ~m1_subset_1(C_27, k2_struct_0('#skF_2')) | ~v7_waybel_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3')) | v2_struct_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_265, c_464, c_90, c_558])).
% 4.21/1.69  tff(c_566, plain, (![C_27]: (r3_waybel_9('#skF_2', k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'), C_27) | ~r1_waybel_7('#skF_2', '#skF_3', C_27) | ~m1_subset_1(C_27, k2_struct_0('#skF_2')) | ~v7_waybel_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3')) | v2_struct_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_62, c_565])).
% 4.21/1.69  tff(c_652, plain, (![C_27]: (r3_waybel_9('#skF_2', k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'), C_27) | ~r1_waybel_7('#skF_2', '#skF_3', C_27) | ~m1_subset_1(C_27, k2_struct_0('#skF_2')) | v2_struct_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_636, c_566])).
% 4.21/1.69  tff(c_654, plain, (![C_146]: (r3_waybel_9('#skF_2', k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'), C_146) | ~r1_waybel_7('#skF_2', '#skF_3', C_146) | ~m1_subset_1(C_146, k2_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_649, c_652])).
% 4.21/1.69  tff(c_660, plain, (~r1_waybel_7('#skF_2', '#skF_3', '#skF_4') | ~m1_subset_1('#skF_4', k2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_654, c_107])).
% 4.21/1.69  tff(c_665, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_91, c_120, c_660])).
% 4.21/1.69  tff(c_666, plain, (~r1_waybel_7('#skF_2', '#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_64])).
% 4.21/1.69  tff(c_667, plain, (r3_waybel_9('#skF_2', k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'), '#skF_4')), inference(splitRight, [status(thm)], [c_64])).
% 4.21/1.69  tff(c_737, plain, (![A_177, B_178, C_179]: (v4_orders_2(k3_yellow19(A_177, B_178, C_179)) | ~m1_subset_1(C_179, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_178)))) | ~v13_waybel_0(C_179, k3_yellow_1(B_178)) | ~v2_waybel_0(C_179, k3_yellow_1(B_178)) | v1_xboole_0(C_179) | ~m1_subset_1(B_178, k1_zfmisc_1(u1_struct_0(A_177))) | v1_xboole_0(B_178) | ~l1_struct_0(A_177) | v2_struct_0(A_177))), inference(cnfTransformation, [status(thm)], [f_108])).
% 4.21/1.69  tff(c_742, plain, (![A_177]: (v4_orders_2(k3_yellow19(A_177, k2_struct_0('#skF_2'), '#skF_3')) | ~v13_waybel_0('#skF_3', k3_yellow_1(k2_struct_0('#skF_2'))) | ~v2_waybel_0('#skF_3', k3_yellow_1(k2_struct_0('#skF_2'))) | v1_xboole_0('#skF_3') | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(u1_struct_0(A_177))) | v1_xboole_0(k2_struct_0('#skF_2')) | ~l1_struct_0(A_177) | v2_struct_0(A_177))), inference(resolution, [status(thm)], [c_48, c_737])).
% 4.21/1.69  tff(c_746, plain, (![A_177]: (v4_orders_2(k3_yellow19(A_177, k2_struct_0('#skF_2'), '#skF_3')) | v1_xboole_0('#skF_3') | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(u1_struct_0(A_177))) | v1_xboole_0(k2_struct_0('#skF_2')) | ~l1_struct_0(A_177) | v2_struct_0(A_177))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_742])).
% 4.21/1.69  tff(c_747, plain, (![A_177]: (v4_orders_2(k3_yellow19(A_177, k2_struct_0('#skF_2'), '#skF_3')) | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(u1_struct_0(A_177))) | v1_xboole_0(k2_struct_0('#skF_2')) | ~l1_struct_0(A_177) | v2_struct_0(A_177))), inference(negUnitSimplification, [status(thm)], [c_56, c_746])).
% 4.21/1.69  tff(c_748, plain, (v1_xboole_0(k2_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_747])).
% 4.21/1.69  tff(c_751, plain, (~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_748, c_16])).
% 4.21/1.69  tff(c_754, plain, (~l1_struct_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_62, c_751])).
% 4.21/1.69  tff(c_757, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_14, c_754])).
% 4.21/1.69  tff(c_761, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_757])).
% 4.21/1.69  tff(c_763, plain, (~v1_xboole_0(k2_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_747])).
% 4.21/1.69  tff(c_765, plain, (![A_183]: (v4_orders_2(k3_yellow19(A_183, k2_struct_0('#skF_2'), '#skF_3')) | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(u1_struct_0(A_183))) | ~l1_struct_0(A_183) | v2_struct_0(A_183))), inference(splitRight, [status(thm)], [c_747])).
% 4.21/1.69  tff(c_771, plain, (v4_orders_2(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3')) | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_90, c_765])).
% 4.21/1.69  tff(c_773, plain, (v4_orders_2(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3')) | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_struct_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_62, c_771])).
% 4.21/1.69  tff(c_774, plain, (~l1_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_773])).
% 4.21/1.69  tff(c_777, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_14, c_774])).
% 4.21/1.69  tff(c_781, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_777])).
% 4.21/1.69  tff(c_783, plain, (l1_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_773])).
% 4.21/1.69  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.21/1.69  tff(c_669, plain, (![A_149, B_150]: (~r2_hidden('#skF_1'(A_149, B_150), B_150) | r1_tarski(A_149, B_150))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.21/1.69  tff(c_674, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_669])).
% 4.21/1.69  tff(c_782, plain, (~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_2'))) | v4_orders_2(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'))), inference(splitRight, [status(thm)], [c_773])).
% 4.21/1.69  tff(c_789, plain, (~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_2')))), inference(splitLeft, [status(thm)], [c_782])).
% 4.21/1.69  tff(c_792, plain, (~r1_tarski(k2_struct_0('#skF_2'), k2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_10, c_789])).
% 4.21/1.69  tff(c_796, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_674, c_792])).
% 4.21/1.69  tff(c_798, plain, (m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_782])).
% 4.21/1.69  tff(c_797, plain, (v4_orders_2(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'))), inference(splitRight, [status(thm)], [c_782])).
% 4.21/1.69  tff(c_1035, plain, (![A_222, B_223, C_224]: (v7_waybel_0(k3_yellow19(A_222, B_223, C_224)) | ~m1_subset_1(C_224, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_223)))) | ~v13_waybel_0(C_224, k3_yellow_1(B_223)) | ~v2_waybel_0(C_224, k3_yellow_1(B_223)) | ~v1_subset_1(C_224, u1_struct_0(k3_yellow_1(B_223))) | v1_xboole_0(C_224) | ~m1_subset_1(B_223, k1_zfmisc_1(u1_struct_0(A_222))) | v1_xboole_0(B_223) | ~l1_struct_0(A_222) | v2_struct_0(A_222))), inference(cnfTransformation, [status(thm)], [f_136])).
% 4.21/1.69  tff(c_1040, plain, (![A_222]: (v7_waybel_0(k3_yellow19(A_222, k2_struct_0('#skF_2'), '#skF_3')) | ~v13_waybel_0('#skF_3', k3_yellow_1(k2_struct_0('#skF_2'))) | ~v2_waybel_0('#skF_3', k3_yellow_1(k2_struct_0('#skF_2'))) | ~v1_subset_1('#skF_3', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2')))) | v1_xboole_0('#skF_3') | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(u1_struct_0(A_222))) | v1_xboole_0(k2_struct_0('#skF_2')) | ~l1_struct_0(A_222) | v2_struct_0(A_222))), inference(resolution, [status(thm)], [c_48, c_1035])).
% 4.21/1.69  tff(c_1044, plain, (![A_222]: (v7_waybel_0(k3_yellow19(A_222, k2_struct_0('#skF_2'), '#skF_3')) | v1_xboole_0('#skF_3') | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(u1_struct_0(A_222))) | v1_xboole_0(k2_struct_0('#skF_2')) | ~l1_struct_0(A_222) | v2_struct_0(A_222))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_1040])).
% 4.21/1.69  tff(c_1046, plain, (![A_225]: (v7_waybel_0(k3_yellow19(A_225, k2_struct_0('#skF_2'), '#skF_3')) | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(u1_struct_0(A_225))) | ~l1_struct_0(A_225) | v2_struct_0(A_225))), inference(negUnitSimplification, [status(thm)], [c_763, c_56, c_1044])).
% 4.21/1.69  tff(c_1052, plain, (v7_waybel_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3')) | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_90, c_1046])).
% 4.21/1.69  tff(c_1055, plain, (v7_waybel_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_783, c_798, c_1052])).
% 4.21/1.69  tff(c_1056, plain, (v7_waybel_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_62, c_1055])).
% 4.21/1.69  tff(c_886, plain, (![A_195, B_196, C_197]: (l1_waybel_0(k3_yellow19(A_195, B_196, C_197), A_195) | ~m1_subset_1(C_197, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_196)))) | ~v13_waybel_0(C_197, k3_yellow_1(B_196)) | ~v2_waybel_0(C_197, k3_yellow_1(B_196)) | v1_xboole_0(C_197) | ~m1_subset_1(B_196, k1_zfmisc_1(u1_struct_0(A_195))) | v1_xboole_0(B_196) | ~l1_struct_0(A_195) | v2_struct_0(A_195))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.21/1.69  tff(c_891, plain, (![A_195]: (l1_waybel_0(k3_yellow19(A_195, k2_struct_0('#skF_2'), '#skF_3'), A_195) | ~v13_waybel_0('#skF_3', k3_yellow_1(k2_struct_0('#skF_2'))) | ~v2_waybel_0('#skF_3', k3_yellow_1(k2_struct_0('#skF_2'))) | v1_xboole_0('#skF_3') | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(u1_struct_0(A_195))) | v1_xboole_0(k2_struct_0('#skF_2')) | ~l1_struct_0(A_195) | v2_struct_0(A_195))), inference(resolution, [status(thm)], [c_48, c_886])).
% 4.21/1.69  tff(c_895, plain, (![A_195]: (l1_waybel_0(k3_yellow19(A_195, k2_struct_0('#skF_2'), '#skF_3'), A_195) | v1_xboole_0('#skF_3') | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(u1_struct_0(A_195))) | v1_xboole_0(k2_struct_0('#skF_2')) | ~l1_struct_0(A_195) | v2_struct_0(A_195))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_891])).
% 4.21/1.69  tff(c_897, plain, (![A_198]: (l1_waybel_0(k3_yellow19(A_198, k2_struct_0('#skF_2'), '#skF_3'), A_198) | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(u1_struct_0(A_198))) | ~l1_struct_0(A_198) | v2_struct_0(A_198))), inference(negUnitSimplification, [status(thm)], [c_763, c_56, c_895])).
% 4.21/1.69  tff(c_902, plain, (l1_waybel_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'), '#skF_2') | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_90, c_897])).
% 4.21/1.69  tff(c_905, plain, (l1_waybel_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'), '#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_783, c_798, c_902])).
% 4.21/1.69  tff(c_906, plain, (l1_waybel_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_62, c_905])).
% 4.21/1.69  tff(c_1135, plain, (![A_239, B_240]: (k2_yellow19(A_239, k3_yellow19(A_239, k2_struct_0(A_239), B_240))=B_240 | ~m1_subset_1(B_240, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_239))))) | ~v13_waybel_0(B_240, k3_yellow_1(k2_struct_0(A_239))) | ~v2_waybel_0(B_240, k3_yellow_1(k2_struct_0(A_239))) | ~v1_subset_1(B_240, u1_struct_0(k3_yellow_1(k2_struct_0(A_239)))) | v1_xboole_0(B_240) | ~l1_struct_0(A_239) | v2_struct_0(A_239))), inference(cnfTransformation, [status(thm)], [f_179])).
% 4.21/1.69  tff(c_1140, plain, (k2_yellow19('#skF_2', k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'))='#skF_3' | ~v13_waybel_0('#skF_3', k3_yellow_1(k2_struct_0('#skF_2'))) | ~v2_waybel_0('#skF_3', k3_yellow_1(k2_struct_0('#skF_2'))) | ~v1_subset_1('#skF_3', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2')))) | v1_xboole_0('#skF_3') | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_48, c_1135])).
% 4.21/1.69  tff(c_1144, plain, (k2_yellow19('#skF_2', k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'))='#skF_3' | v1_xboole_0('#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_783, c_54, c_52, c_50, c_1140])).
% 4.21/1.69  tff(c_1145, plain, (k2_yellow19('#skF_2', k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'))='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_62, c_56, c_1144])).
% 4.21/1.69  tff(c_1149, plain, (![C_27]: (r1_waybel_7('#skF_2', '#skF_3', C_27) | ~r3_waybel_9('#skF_2', k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'), C_27) | ~m1_subset_1(C_27, u1_struct_0('#skF_2')) | ~l1_waybel_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'), '#skF_2') | ~v7_waybel_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3')) | ~v4_orders_2(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3')) | v2_struct_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1145, c_42])).
% 4.21/1.69  tff(c_1156, plain, (![C_27]: (r1_waybel_7('#skF_2', '#skF_3', C_27) | ~r3_waybel_9('#skF_2', k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'), C_27) | ~m1_subset_1(C_27, k2_struct_0('#skF_2')) | v2_struct_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_797, c_1056, c_906, c_90, c_1149])).
% 4.21/1.69  tff(c_1157, plain, (![C_27]: (r1_waybel_7('#skF_2', '#skF_3', C_27) | ~r3_waybel_9('#skF_2', k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'), C_27) | ~m1_subset_1(C_27, k2_struct_0('#skF_2')) | v2_struct_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_62, c_1156])).
% 4.21/1.69  tff(c_1162, plain, (v2_struct_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'))), inference(splitLeft, [status(thm)], [c_1157])).
% 4.21/1.69  tff(c_1164, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2'))))) | ~v13_waybel_0('#skF_3', k3_yellow_1(k2_struct_0('#skF_2'))) | ~v2_waybel_0('#skF_3', k3_yellow_1(k2_struct_0('#skF_2'))) | v1_xboole_0('#skF_3') | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | v1_xboole_0(k2_struct_0('#skF_2')) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_1162, c_32])).
% 4.21/1.69  tff(c_1167, plain, (v1_xboole_0('#skF_3') | v1_xboole_0(k2_struct_0('#skF_2')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_783, c_798, c_90, c_52, c_50, c_48, c_1164])).
% 4.21/1.69  tff(c_1169, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_763, c_56, c_1167])).
% 4.21/1.69  tff(c_1191, plain, (![C_245]: (r1_waybel_7('#skF_2', '#skF_3', C_245) | ~r3_waybel_9('#skF_2', k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'), C_245) | ~m1_subset_1(C_245, k2_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_1157])).
% 4.21/1.69  tff(c_1197, plain, (r1_waybel_7('#skF_2', '#skF_3', '#skF_4') | ~m1_subset_1('#skF_4', k2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_667, c_1191])).
% 4.21/1.69  tff(c_1201, plain, (r1_waybel_7('#skF_2', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_91, c_1197])).
% 4.21/1.69  tff(c_1203, plain, $false, inference(negUnitSimplification, [status(thm)], [c_666, c_1201])).
% 4.21/1.69  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.21/1.69  
% 4.21/1.69  Inference rules
% 4.21/1.69  ----------------------
% 4.21/1.69  #Ref     : 0
% 4.21/1.69  #Sup     : 198
% 4.21/1.69  #Fact    : 0
% 4.21/1.69  #Define  : 0
% 4.21/1.69  #Split   : 18
% 4.21/1.69  #Chain   : 0
% 4.21/1.69  #Close   : 0
% 4.21/1.69  
% 4.21/1.69  Ordering : KBO
% 4.21/1.69  
% 4.21/1.69  Simplification rules
% 4.21/1.69  ----------------------
% 4.21/1.69  #Subsume      : 38
% 4.21/1.69  #Demod        : 201
% 4.21/1.69  #Tautology    : 42
% 4.21/1.69  #SimpNegUnit  : 95
% 4.21/1.69  #BackRed      : 1
% 4.21/1.69  
% 4.21/1.69  #Partial instantiations: 0
% 4.21/1.69  #Strategies tried      : 1
% 4.21/1.69  
% 4.21/1.69  Timing (in seconds)
% 4.21/1.69  ----------------------
% 4.21/1.70  Preprocessing        : 0.36
% 4.21/1.70  Parsing              : 0.18
% 4.21/1.70  CNF conversion       : 0.02
% 4.21/1.70  Main loop            : 0.52
% 4.21/1.70  Inferencing          : 0.19
% 4.21/1.70  Reduction            : 0.17
% 4.21/1.70  Demodulation         : 0.11
% 4.21/1.70  BG Simplification    : 0.03
% 4.21/1.70  Subsumption          : 0.10
% 4.21/1.70  Abstraction          : 0.03
% 4.21/1.70  MUC search           : 0.00
% 4.21/1.70  Cooper               : 0.00
% 4.21/1.70  Total                : 0.96
% 4.21/1.70  Index Insertion      : 0.00
% 4.21/1.70  Index Deletion       : 0.00
% 4.21/1.70  Index Matching       : 0.00
% 4.21/1.70  BG Taut test         : 0.00
%------------------------------------------------------------------------------
