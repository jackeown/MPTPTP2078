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
% DateTime   : Thu Dec  3 10:31:34 EST 2020

% Result     : Theorem 3.81s
% Output     : CNFRefutation 4.08s
% Verified   : 
% Statistics : Number of formulae       :  176 (2094 expanded)
%              Number of leaves         :   44 ( 734 expanded)
%              Depth                    :   20
%              Number of atoms          :  537 (8308 expanded)
%              Number of equality atoms :   13 ( 441 expanded)
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

tff(f_52,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

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

tff(c_111,plain,(
    ~ r3_waybel_9('#skF_2',k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_70,plain,
    ( r3_waybel_9('#skF_2',k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'),'#skF_4')
    | r1_waybel_7('#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_139,plain,(
    r1_waybel_7('#skF_2','#skF_3','#skF_4') ),
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

tff(c_195,plain,(
    ! [A_74,B_75,C_76] :
      ( v4_orders_2(k3_yellow19(A_74,B_75,C_76))
      | ~ m1_subset_1(C_76,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_75))))
      | ~ v13_waybel_0(C_76,k3_yellow_1(B_75))
      | ~ v2_waybel_0(C_76,k3_yellow_1(B_75))
      | v1_xboole_0(C_76)
      | ~ m1_subset_1(B_75,k1_zfmisc_1(u1_struct_0(A_74)))
      | v1_xboole_0(B_75)
      | ~ l1_struct_0(A_74)
      | v2_struct_0(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_200,plain,(
    ! [A_74] :
      ( v4_orders_2(k3_yellow19(A_74,k2_struct_0('#skF_2'),'#skF_3'))
      | ~ v13_waybel_0('#skF_3',k3_yellow_1(k2_struct_0('#skF_2')))
      | ~ v2_waybel_0('#skF_3',k3_yellow_1(k2_struct_0('#skF_2')))
      | v1_xboole_0('#skF_3')
      | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0(A_74)))
      | v1_xboole_0(k2_struct_0('#skF_2'))
      | ~ l1_struct_0(A_74)
      | v2_struct_0(A_74) ) ),
    inference(resolution,[status(thm)],[c_48,c_195])).

tff(c_204,plain,(
    ! [A_74] :
      ( v4_orders_2(k3_yellow19(A_74,k2_struct_0('#skF_2'),'#skF_3'))
      | v1_xboole_0('#skF_3')
      | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0(A_74)))
      | v1_xboole_0(k2_struct_0('#skF_2'))
      | ~ l1_struct_0(A_74)
      | v2_struct_0(A_74) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_200])).

tff(c_206,plain,(
    ! [A_77] :
      ( v4_orders_2(k3_yellow19(A_77,k2_struct_0('#skF_2'),'#skF_3'))
      | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0(A_77)))
      | ~ l1_struct_0(A_77)
      | v2_struct_0(A_77) ) ),
    inference(negUnitSimplification,[status(thm)],[c_120,c_56,c_204])).

tff(c_212,plain,
    ( v4_orders_2(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'))
    | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_2')))
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_206])).

tff(c_215,plain,
    ( v4_orders_2(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'))
    | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_2')))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_212])).

tff(c_216,plain,
    ( v4_orders_2(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'))
    | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_215])).

tff(c_217,plain,(
    ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_216])).

tff(c_220,plain,(
    ~ r1_tarski(k2_struct_0('#skF_2'),k2_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_10,c_217])).

tff(c_224,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_220])).

tff(c_226,plain,(
    m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_216])).

tff(c_60,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_225,plain,(
    v4_orders_2(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3')) ),
    inference(splitRight,[status(thm)],[c_216])).

tff(c_54,plain,(
    v1_subset_1('#skF_3',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_558,plain,(
    ! [A_138,B_139,C_140] :
      ( v7_waybel_0(k3_yellow19(A_138,B_139,C_140))
      | ~ m1_subset_1(C_140,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_139))))
      | ~ v13_waybel_0(C_140,k3_yellow_1(B_139))
      | ~ v2_waybel_0(C_140,k3_yellow_1(B_139))
      | ~ v1_subset_1(C_140,u1_struct_0(k3_yellow_1(B_139)))
      | v1_xboole_0(C_140)
      | ~ m1_subset_1(B_139,k1_zfmisc_1(u1_struct_0(A_138)))
      | v1_xboole_0(B_139)
      | ~ l1_struct_0(A_138)
      | v2_struct_0(A_138) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_563,plain,(
    ! [A_138] :
      ( v7_waybel_0(k3_yellow19(A_138,k2_struct_0('#skF_2'),'#skF_3'))
      | ~ v13_waybel_0('#skF_3',k3_yellow_1(k2_struct_0('#skF_2')))
      | ~ v2_waybel_0('#skF_3',k3_yellow_1(k2_struct_0('#skF_2')))
      | ~ v1_subset_1('#skF_3',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2'))))
      | v1_xboole_0('#skF_3')
      | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0(A_138)))
      | v1_xboole_0(k2_struct_0('#skF_2'))
      | ~ l1_struct_0(A_138)
      | v2_struct_0(A_138) ) ),
    inference(resolution,[status(thm)],[c_48,c_558])).

tff(c_567,plain,(
    ! [A_138] :
      ( v7_waybel_0(k3_yellow19(A_138,k2_struct_0('#skF_2'),'#skF_3'))
      | v1_xboole_0('#skF_3')
      | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0(A_138)))
      | v1_xboole_0(k2_struct_0('#skF_2'))
      | ~ l1_struct_0(A_138)
      | v2_struct_0(A_138) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_563])).

tff(c_569,plain,(
    ! [A_141] :
      ( v7_waybel_0(k3_yellow19(A_141,k2_struct_0('#skF_2'),'#skF_3'))
      | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0(A_141)))
      | ~ l1_struct_0(A_141)
      | v2_struct_0(A_141) ) ),
    inference(negUnitSimplification,[status(thm)],[c_120,c_56,c_567])).

tff(c_575,plain,
    ( v7_waybel_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'))
    | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_2')))
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_569])).

tff(c_578,plain,
    ( v7_waybel_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_226,c_575])).

tff(c_579,plain,(
    v7_waybel_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_578])).

tff(c_474,plain,(
    ! [A_121,B_122,C_123] :
      ( l1_waybel_0(k3_yellow19(A_121,B_122,C_123),A_121)
      | ~ m1_subset_1(C_123,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_122))))
      | ~ v13_waybel_0(C_123,k3_yellow_1(B_122))
      | ~ v2_waybel_0(C_123,k3_yellow_1(B_122))
      | v1_xboole_0(C_123)
      | ~ m1_subset_1(B_122,k1_zfmisc_1(u1_struct_0(A_121)))
      | v1_xboole_0(B_122)
      | ~ l1_struct_0(A_121)
      | v2_struct_0(A_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_479,plain,(
    ! [A_121] :
      ( l1_waybel_0(k3_yellow19(A_121,k2_struct_0('#skF_2'),'#skF_3'),A_121)
      | ~ v13_waybel_0('#skF_3',k3_yellow_1(k2_struct_0('#skF_2')))
      | ~ v2_waybel_0('#skF_3',k3_yellow_1(k2_struct_0('#skF_2')))
      | v1_xboole_0('#skF_3')
      | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0(A_121)))
      | v1_xboole_0(k2_struct_0('#skF_2'))
      | ~ l1_struct_0(A_121)
      | v2_struct_0(A_121) ) ),
    inference(resolution,[status(thm)],[c_48,c_474])).

tff(c_483,plain,(
    ! [A_121] :
      ( l1_waybel_0(k3_yellow19(A_121,k2_struct_0('#skF_2'),'#skF_3'),A_121)
      | v1_xboole_0('#skF_3')
      | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0(A_121)))
      | v1_xboole_0(k2_struct_0('#skF_2'))
      | ~ l1_struct_0(A_121)
      | v2_struct_0(A_121) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_479])).

tff(c_485,plain,(
    ! [A_124] :
      ( l1_waybel_0(k3_yellow19(A_124,k2_struct_0('#skF_2'),'#skF_3'),A_124)
      | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0(A_124)))
      | ~ l1_struct_0(A_124)
      | v2_struct_0(A_124) ) ),
    inference(negUnitSimplification,[status(thm)],[c_120,c_56,c_483])).

tff(c_490,plain,
    ( l1_waybel_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'),'#skF_2')
    | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_2')))
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_485])).

tff(c_493,plain,
    ( l1_waybel_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'),'#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_226,c_490])).

tff(c_494,plain,(
    l1_waybel_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_493])).

tff(c_626,plain,(
    ! [A_154,B_155] :
      ( k2_yellow19(A_154,k3_yellow19(A_154,k2_struct_0(A_154),B_155)) = B_155
      | ~ m1_subset_1(B_155,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_154)))))
      | ~ v13_waybel_0(B_155,k3_yellow_1(k2_struct_0(A_154)))
      | ~ v2_waybel_0(B_155,k3_yellow_1(k2_struct_0(A_154)))
      | ~ v1_subset_1(B_155,u1_struct_0(k3_yellow_1(k2_struct_0(A_154))))
      | v1_xboole_0(B_155)
      | ~ l1_struct_0(A_154)
      | v2_struct_0(A_154) ) ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_631,plain,
    ( k2_yellow19('#skF_2',k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3')) = '#skF_3'
    | ~ v13_waybel_0('#skF_3',k3_yellow_1(k2_struct_0('#skF_2')))
    | ~ v2_waybel_0('#skF_3',k3_yellow_1(k2_struct_0('#skF_2')))
    | ~ v1_subset_1('#skF_3',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2'))))
    | v1_xboole_0('#skF_3')
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_626])).

tff(c_635,plain,
    ( k2_yellow19('#skF_2',k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3')) = '#skF_3'
    | v1_xboole_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_54,c_52,c_50,c_631])).

tff(c_636,plain,(
    k2_yellow19('#skF_2',k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3')) = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_56,c_635])).

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

tff(c_640,plain,(
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
    inference(superposition,[status(thm),theory(equality)],[c_636,c_40])).

tff(c_647,plain,(
    ! [C_27] :
      ( r3_waybel_9('#skF_2',k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'),C_27)
      | ~ r1_waybel_7('#skF_2','#skF_3',C_27)
      | ~ m1_subset_1(C_27,k2_struct_0('#skF_2'))
      | v2_struct_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_225,c_579,c_494,c_90,c_640])).

tff(c_648,plain,(
    ! [C_27] :
      ( r3_waybel_9('#skF_2',k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'),C_27)
      | ~ r1_waybel_7('#skF_2','#skF_3',C_27)
      | ~ m1_subset_1(C_27,k2_struct_0('#skF_2'))
      | v2_struct_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_647])).

tff(c_653,plain,(
    v2_struct_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_648])).

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

tff(c_655,plain,
    ( ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2')))))
    | ~ v13_waybel_0('#skF_3',k3_yellow_1(k2_struct_0('#skF_2')))
    | ~ v2_waybel_0('#skF_3',k3_yellow_1(k2_struct_0('#skF_2')))
    | v1_xboole_0('#skF_3')
    | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v1_xboole_0(k2_struct_0('#skF_2'))
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_653,c_32])).

tff(c_658,plain,
    ( v1_xboole_0('#skF_3')
    | v1_xboole_0(k2_struct_0('#skF_2'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_226,c_90,c_52,c_50,c_48,c_655])).

tff(c_660,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_120,c_56,c_658])).

tff(c_675,plain,(
    ! [C_160] :
      ( r3_waybel_9('#skF_2',k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'),C_160)
      | ~ r1_waybel_7('#skF_2','#skF_3',C_160)
      | ~ m1_subset_1(C_160,k2_struct_0('#skF_2')) ) ),
    inference(splitRight,[status(thm)],[c_648])).

tff(c_681,plain,
    ( ~ r1_waybel_7('#skF_2','#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_4',k2_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_675,c_111])).

tff(c_686,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_139,c_681])).

tff(c_687,plain,(
    ~ r1_waybel_7('#skF_2','#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_688,plain,(
    r3_waybel_9('#skF_2',k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_689,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_110])).

tff(c_693,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_14,c_689])).

tff(c_697,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_693])).

tff(c_698,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_110])).

tff(c_699,plain,(
    l1_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_110])).

tff(c_706,plain,(
    ! [A_163,B_164] :
      ( r2_hidden('#skF_1'(A_163,B_164),A_163)
      | r1_tarski(A_163,B_164) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_711,plain,(
    ! [A_163] : r1_tarski(A_163,A_163) ),
    inference(resolution,[status(thm)],[c_706,c_4])).

tff(c_774,plain,(
    ! [A_191,B_192,C_193] :
      ( v3_orders_2(k3_yellow19(A_191,B_192,C_193))
      | ~ m1_subset_1(C_193,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_192))))
      | ~ v13_waybel_0(C_193,k3_yellow_1(B_192))
      | ~ v2_waybel_0(C_193,k3_yellow_1(B_192))
      | v1_xboole_0(C_193)
      | ~ m1_subset_1(B_192,k1_zfmisc_1(u1_struct_0(A_191)))
      | v1_xboole_0(B_192)
      | ~ l1_struct_0(A_191)
      | v2_struct_0(A_191) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_779,plain,(
    ! [A_191] :
      ( v3_orders_2(k3_yellow19(A_191,k2_struct_0('#skF_2'),'#skF_3'))
      | ~ v13_waybel_0('#skF_3',k3_yellow_1(k2_struct_0('#skF_2')))
      | ~ v2_waybel_0('#skF_3',k3_yellow_1(k2_struct_0('#skF_2')))
      | v1_xboole_0('#skF_3')
      | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0(A_191)))
      | v1_xboole_0(k2_struct_0('#skF_2'))
      | ~ l1_struct_0(A_191)
      | v2_struct_0(A_191) ) ),
    inference(resolution,[status(thm)],[c_48,c_774])).

tff(c_783,plain,(
    ! [A_191] :
      ( v3_orders_2(k3_yellow19(A_191,k2_struct_0('#skF_2'),'#skF_3'))
      | v1_xboole_0('#skF_3')
      | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0(A_191)))
      | v1_xboole_0(k2_struct_0('#skF_2'))
      | ~ l1_struct_0(A_191)
      | v2_struct_0(A_191) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_779])).

tff(c_785,plain,(
    ! [A_194] :
      ( v3_orders_2(k3_yellow19(A_194,k2_struct_0('#skF_2'),'#skF_3'))
      | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0(A_194)))
      | ~ l1_struct_0(A_194)
      | v2_struct_0(A_194) ) ),
    inference(negUnitSimplification,[status(thm)],[c_698,c_56,c_783])).

tff(c_791,plain,
    ( v3_orders_2(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'))
    | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_2')))
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_785])).

tff(c_794,plain,
    ( v3_orders_2(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'))
    | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_2')))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_699,c_791])).

tff(c_795,plain,
    ( v3_orders_2(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'))
    | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_794])).

tff(c_796,plain,(
    ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_795])).

tff(c_799,plain,(
    ~ r1_tarski(k2_struct_0('#skF_2'),k2_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_10,c_796])).

tff(c_803,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_711,c_799])).

tff(c_805,plain,(
    m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_795])).

tff(c_825,plain,(
    ! [A_199,B_200,C_201] :
      ( v4_orders_2(k3_yellow19(A_199,B_200,C_201))
      | ~ m1_subset_1(C_201,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_200))))
      | ~ v13_waybel_0(C_201,k3_yellow_1(B_200))
      | ~ v2_waybel_0(C_201,k3_yellow_1(B_200))
      | v1_xboole_0(C_201)
      | ~ m1_subset_1(B_200,k1_zfmisc_1(u1_struct_0(A_199)))
      | v1_xboole_0(B_200)
      | ~ l1_struct_0(A_199)
      | v2_struct_0(A_199) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_830,plain,(
    ! [A_199] :
      ( v4_orders_2(k3_yellow19(A_199,k2_struct_0('#skF_2'),'#skF_3'))
      | ~ v13_waybel_0('#skF_3',k3_yellow_1(k2_struct_0('#skF_2')))
      | ~ v2_waybel_0('#skF_3',k3_yellow_1(k2_struct_0('#skF_2')))
      | v1_xboole_0('#skF_3')
      | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0(A_199)))
      | v1_xboole_0(k2_struct_0('#skF_2'))
      | ~ l1_struct_0(A_199)
      | v2_struct_0(A_199) ) ),
    inference(resolution,[status(thm)],[c_48,c_825])).

tff(c_834,plain,(
    ! [A_199] :
      ( v4_orders_2(k3_yellow19(A_199,k2_struct_0('#skF_2'),'#skF_3'))
      | v1_xboole_0('#skF_3')
      | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0(A_199)))
      | v1_xboole_0(k2_struct_0('#skF_2'))
      | ~ l1_struct_0(A_199)
      | v2_struct_0(A_199) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_830])).

tff(c_836,plain,(
    ! [A_202] :
      ( v4_orders_2(k3_yellow19(A_202,k2_struct_0('#skF_2'),'#skF_3'))
      | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0(A_202)))
      | ~ l1_struct_0(A_202)
      | v2_struct_0(A_202) ) ),
    inference(negUnitSimplification,[status(thm)],[c_698,c_56,c_834])).

tff(c_842,plain,
    ( v4_orders_2(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'))
    | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_2')))
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_836])).

tff(c_845,plain,
    ( v4_orders_2(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_699,c_805,c_842])).

tff(c_846,plain,(
    v4_orders_2(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_845])).

tff(c_894,plain,(
    ! [A_209,B_210,C_211] :
      ( l1_waybel_0(k3_yellow19(A_209,B_210,C_211),A_209)
      | ~ m1_subset_1(C_211,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_210))))
      | ~ v13_waybel_0(C_211,k3_yellow_1(B_210))
      | ~ v2_waybel_0(C_211,k3_yellow_1(B_210))
      | v1_xboole_0(C_211)
      | ~ m1_subset_1(B_210,k1_zfmisc_1(u1_struct_0(A_209)))
      | v1_xboole_0(B_210)
      | ~ l1_struct_0(A_209)
      | v2_struct_0(A_209) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_899,plain,(
    ! [A_209] :
      ( l1_waybel_0(k3_yellow19(A_209,k2_struct_0('#skF_2'),'#skF_3'),A_209)
      | ~ v13_waybel_0('#skF_3',k3_yellow_1(k2_struct_0('#skF_2')))
      | ~ v2_waybel_0('#skF_3',k3_yellow_1(k2_struct_0('#skF_2')))
      | v1_xboole_0('#skF_3')
      | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0(A_209)))
      | v1_xboole_0(k2_struct_0('#skF_2'))
      | ~ l1_struct_0(A_209)
      | v2_struct_0(A_209) ) ),
    inference(resolution,[status(thm)],[c_48,c_894])).

tff(c_903,plain,(
    ! [A_209] :
      ( l1_waybel_0(k3_yellow19(A_209,k2_struct_0('#skF_2'),'#skF_3'),A_209)
      | v1_xboole_0('#skF_3')
      | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0(A_209)))
      | v1_xboole_0(k2_struct_0('#skF_2'))
      | ~ l1_struct_0(A_209)
      | v2_struct_0(A_209) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_899])).

tff(c_905,plain,(
    ! [A_212] :
      ( l1_waybel_0(k3_yellow19(A_212,k2_struct_0('#skF_2'),'#skF_3'),A_212)
      | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0(A_212)))
      | ~ l1_struct_0(A_212)
      | v2_struct_0(A_212) ) ),
    inference(negUnitSimplification,[status(thm)],[c_698,c_56,c_903])).

tff(c_910,plain,
    ( l1_waybel_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'),'#skF_2')
    | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_2')))
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_905])).

tff(c_913,plain,
    ( l1_waybel_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'),'#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_699,c_805,c_910])).

tff(c_914,plain,(
    l1_waybel_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_913])).

tff(c_1043,plain,(
    ! [A_236,B_237] :
      ( k2_yellow19(A_236,k3_yellow19(A_236,k2_struct_0(A_236),B_237)) = B_237
      | ~ m1_subset_1(B_237,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_236)))))
      | ~ v13_waybel_0(B_237,k3_yellow_1(k2_struct_0(A_236)))
      | ~ v2_waybel_0(B_237,k3_yellow_1(k2_struct_0(A_236)))
      | ~ v1_subset_1(B_237,u1_struct_0(k3_yellow_1(k2_struct_0(A_236))))
      | v1_xboole_0(B_237)
      | ~ l1_struct_0(A_236)
      | v2_struct_0(A_236) ) ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_1048,plain,
    ( k2_yellow19('#skF_2',k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3')) = '#skF_3'
    | ~ v13_waybel_0('#skF_3',k3_yellow_1(k2_struct_0('#skF_2')))
    | ~ v2_waybel_0('#skF_3',k3_yellow_1(k2_struct_0('#skF_2')))
    | ~ v1_subset_1('#skF_3',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2'))))
    | v1_xboole_0('#skF_3')
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_1043])).

tff(c_1052,plain,
    ( k2_yellow19('#skF_2',k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3')) = '#skF_3'
    | v1_xboole_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_699,c_54,c_52,c_50,c_1048])).

tff(c_1053,plain,(
    k2_yellow19('#skF_2',k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3')) = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_56,c_1052])).

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

tff(c_1057,plain,(
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
    inference(superposition,[status(thm),theory(equality)],[c_1053,c_42])).

tff(c_1064,plain,(
    ! [C_27] :
      ( r1_waybel_7('#skF_2','#skF_3',C_27)
      | ~ r3_waybel_9('#skF_2',k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'),C_27)
      | ~ m1_subset_1(C_27,k2_struct_0('#skF_2'))
      | ~ v7_waybel_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'))
      | v2_struct_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_846,c_914,c_90,c_1057])).

tff(c_1065,plain,(
    ! [C_27] :
      ( r1_waybel_7('#skF_2','#skF_3',C_27)
      | ~ r3_waybel_9('#skF_2',k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'),C_27)
      | ~ m1_subset_1(C_27,k2_struct_0('#skF_2'))
      | ~ v7_waybel_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'))
      | v2_struct_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_1064])).

tff(c_1070,plain,(
    ~ v7_waybel_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1065])).

tff(c_1129,plain,(
    ! [A_249,B_250,C_251] :
      ( v7_waybel_0(k3_yellow19(A_249,B_250,C_251))
      | ~ m1_subset_1(C_251,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_250))))
      | ~ v13_waybel_0(C_251,k3_yellow_1(B_250))
      | ~ v2_waybel_0(C_251,k3_yellow_1(B_250))
      | ~ v1_subset_1(C_251,u1_struct_0(k3_yellow_1(B_250)))
      | v1_xboole_0(C_251)
      | ~ m1_subset_1(B_250,k1_zfmisc_1(u1_struct_0(A_249)))
      | v1_xboole_0(B_250)
      | ~ l1_struct_0(A_249)
      | v2_struct_0(A_249) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_1134,plain,(
    ! [A_249] :
      ( v7_waybel_0(k3_yellow19(A_249,k2_struct_0('#skF_2'),'#skF_3'))
      | ~ v13_waybel_0('#skF_3',k3_yellow_1(k2_struct_0('#skF_2')))
      | ~ v2_waybel_0('#skF_3',k3_yellow_1(k2_struct_0('#skF_2')))
      | ~ v1_subset_1('#skF_3',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2'))))
      | v1_xboole_0('#skF_3')
      | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0(A_249)))
      | v1_xboole_0(k2_struct_0('#skF_2'))
      | ~ l1_struct_0(A_249)
      | v2_struct_0(A_249) ) ),
    inference(resolution,[status(thm)],[c_48,c_1129])).

tff(c_1138,plain,(
    ! [A_249] :
      ( v7_waybel_0(k3_yellow19(A_249,k2_struct_0('#skF_2'),'#skF_3'))
      | v1_xboole_0('#skF_3')
      | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0(A_249)))
      | v1_xboole_0(k2_struct_0('#skF_2'))
      | ~ l1_struct_0(A_249)
      | v2_struct_0(A_249) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_1134])).

tff(c_1140,plain,(
    ! [A_252] :
      ( v7_waybel_0(k3_yellow19(A_252,k2_struct_0('#skF_2'),'#skF_3'))
      | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0(A_252)))
      | ~ l1_struct_0(A_252)
      | v2_struct_0(A_252) ) ),
    inference(negUnitSimplification,[status(thm)],[c_698,c_56,c_1138])).

tff(c_1146,plain,
    ( v7_waybel_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'))
    | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_2')))
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_1140])).

tff(c_1149,plain,
    ( v7_waybel_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_699,c_805,c_1146])).

tff(c_1151,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_1070,c_1149])).

tff(c_1152,plain,(
    ! [C_27] :
      ( v2_struct_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'))
      | r1_waybel_7('#skF_2','#skF_3',C_27)
      | ~ r3_waybel_9('#skF_2',k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'),C_27)
      | ~ m1_subset_1(C_27,k2_struct_0('#skF_2')) ) ),
    inference(splitRight,[status(thm)],[c_1065])).

tff(c_1154,plain,(
    v2_struct_0(k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1152])).

tff(c_1159,plain,
    ( ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2')))))
    | ~ v13_waybel_0('#skF_3',k3_yellow_1(k2_struct_0('#skF_2')))
    | ~ v2_waybel_0('#skF_3',k3_yellow_1(k2_struct_0('#skF_2')))
    | v1_xboole_0('#skF_3')
    | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v1_xboole_0(k2_struct_0('#skF_2'))
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_1154,c_32])).

tff(c_1162,plain,
    ( v1_xboole_0('#skF_3')
    | v1_xboole_0(k2_struct_0('#skF_2'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_699,c_805,c_90,c_52,c_50,c_48,c_1159])).

tff(c_1164,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_698,c_56,c_1162])).

tff(c_1167,plain,(
    ! [C_253] :
      ( r1_waybel_7('#skF_2','#skF_3',C_253)
      | ~ r3_waybel_9('#skF_2',k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'),C_253)
      | ~ m1_subset_1(C_253,k2_struct_0('#skF_2')) ) ),
    inference(splitRight,[status(thm)],[c_1152])).

tff(c_1170,plain,
    ( r1_waybel_7('#skF_2','#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_4',k2_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_688,c_1167])).

tff(c_1173,plain,(
    r1_waybel_7('#skF_2','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_1170])).

tff(c_1175,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_687,c_1173])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n015.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:30:23 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.81/1.64  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.81/1.66  
% 3.81/1.66  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.81/1.66  %$ r3_waybel_9 > r1_waybel_7 > v6_waybel_0 > v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_hidden > r1_tarski > m1_subset_1 > l1_waybel_0 > v7_waybel_0 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k3_yellow19 > k2_yellow19 > #nlpp > u1_struct_0 > k3_yellow_1 > k3_lattice3 > k2_struct_0 > k1_zfmisc_1 > k1_lattice3 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 3.81/1.66  
% 3.81/1.66  %Foreground sorts:
% 3.81/1.66  
% 3.81/1.66  
% 3.81/1.66  %Background operators:
% 3.81/1.66  
% 3.81/1.66  
% 3.81/1.66  %Foreground operators:
% 3.81/1.66  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.81/1.66  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 3.81/1.66  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.81/1.66  tff(k3_lattice3, type, k3_lattice3: $i > $i).
% 3.81/1.66  tff(v6_waybel_0, type, v6_waybel_0: ($i * $i) > $o).
% 3.81/1.66  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.81/1.66  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 3.81/1.66  tff(k3_yellow_1, type, k3_yellow_1: $i > $i).
% 3.81/1.66  tff(v2_waybel_0, type, v2_waybel_0: ($i * $i) > $o).
% 3.81/1.66  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.81/1.66  tff(v7_waybel_0, type, v7_waybel_0: $i > $o).
% 3.81/1.66  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.81/1.66  tff(r3_waybel_9, type, r3_waybel_9: ($i * $i * $i) > $o).
% 3.81/1.66  tff('#skF_2', type, '#skF_2': $i).
% 3.81/1.66  tff('#skF_3', type, '#skF_3': $i).
% 3.81/1.66  tff(k1_lattice3, type, k1_lattice3: $i > $i).
% 3.81/1.66  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 3.81/1.66  tff(r1_waybel_7, type, r1_waybel_7: ($i * $i * $i) > $o).
% 3.81/1.66  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.81/1.66  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.81/1.66  tff(k2_yellow19, type, k2_yellow19: ($i * $i) > $i).
% 3.81/1.66  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.81/1.66  tff(l1_waybel_0, type, l1_waybel_0: ($i * $i) > $o).
% 3.81/1.66  tff('#skF_4', type, '#skF_4': $i).
% 3.81/1.66  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.81/1.66  tff(k3_yellow19, type, k3_yellow19: ($i * $i * $i) > $i).
% 3.81/1.66  tff(v13_waybel_0, type, v13_waybel_0: ($i * $i) > $o).
% 3.81/1.66  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.81/1.66  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.81/1.66  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.81/1.66  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 3.81/1.66  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.81/1.66  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.81/1.66  
% 4.08/1.70  tff(f_206, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((((~v1_xboole_0(B) & v1_subset_1(B, u1_struct_0(k3_yellow_1(k2_struct_0(A))))) & v2_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & v13_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A)))))) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r3_waybel_9(A, k3_yellow19(A, k2_struct_0(A), B), C) <=> r1_waybel_7(A, B, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_yellow19)).
% 4.08/1.70  tff(f_44, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 4.08/1.70  tff(f_40, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 4.08/1.70  tff(f_52, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 4.08/1.70  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 4.08/1.70  tff(f_36, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 4.08/1.70  tff(f_108, axiom, (![A, B, C]: ((((((((~v2_struct_0(A) & l1_struct_0(A)) & ~v1_xboole_0(B)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) & ~v1_xboole_0(C)) & v2_waybel_0(C, k3_yellow_1(B))) & v13_waybel_0(C, k3_yellow_1(B))) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B))))) => (((~v2_struct_0(k3_yellow19(A, B, C)) & v3_orders_2(k3_yellow19(A, B, C))) & v4_orders_2(k3_yellow19(A, B, C))) & v6_waybel_0(k3_yellow19(A, B, C), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_yellow19)).
% 4.08/1.70  tff(f_136, axiom, (![A, B, C]: (((((((((~v2_struct_0(A) & l1_struct_0(A)) & ~v1_xboole_0(B)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) & ~v1_xboole_0(C)) & v1_subset_1(C, u1_struct_0(k3_yellow_1(B)))) & v2_waybel_0(C, k3_yellow_1(B))) & v13_waybel_0(C, k3_yellow_1(B))) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B))))) => ((~v2_struct_0(k3_yellow19(A, B, C)) & v6_waybel_0(k3_yellow19(A, B, C), A)) & v7_waybel_0(k3_yellow19(A, B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc5_yellow19)).
% 4.08/1.70  tff(f_80, axiom, (![A, B, C]: ((((((((~v2_struct_0(A) & l1_struct_0(A)) & ~v1_xboole_0(B)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) & ~v1_xboole_0(C)) & v2_waybel_0(C, k3_yellow_1(B))) & v13_waybel_0(C, k3_yellow_1(B))) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B))))) => ((~v2_struct_0(k3_yellow19(A, B, C)) & v6_waybel_0(k3_yellow19(A, B, C), A)) & l1_waybel_0(k3_yellow19(A, B, C), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_yellow19)).
% 4.08/1.70  tff(f_179, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: (((((~v1_xboole_0(B) & v1_subset_1(B, u1_struct_0(k3_yellow_1(k2_struct_0(A))))) & v2_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & v13_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A)))))) => (B = k2_yellow19(A, k3_yellow19(A, k2_struct_0(A), B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t15_yellow19)).
% 4.08/1.70  tff(f_160, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r3_waybel_9(A, B, C) <=> r1_waybel_7(A, k2_yellow19(A, B), C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_yellow19)).
% 4.08/1.70  tff(c_58, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_206])).
% 4.08/1.70  tff(c_14, plain, (![A_9]: (l1_struct_0(A_9) | ~l1_pre_topc(A_9))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.08/1.70  tff(c_81, plain, (![A_37]: (u1_struct_0(A_37)=k2_struct_0(A_37) | ~l1_struct_0(A_37))), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.08/1.70  tff(c_86, plain, (![A_38]: (u1_struct_0(A_38)=k2_struct_0(A_38) | ~l1_pre_topc(A_38))), inference(resolution, [status(thm)], [c_14, c_81])).
% 4.08/1.70  tff(c_90, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_58, c_86])).
% 4.08/1.70  tff(c_46, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_206])).
% 4.08/1.70  tff(c_91, plain, (m1_subset_1('#skF_4', k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_46])).
% 4.08/1.70  tff(c_64, plain, (~r1_waybel_7('#skF_2', '#skF_3', '#skF_4') | ~r3_waybel_9('#skF_2', k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_206])).
% 4.08/1.70  tff(c_111, plain, (~r3_waybel_9('#skF_2', k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'), '#skF_4')), inference(splitLeft, [status(thm)], [c_64])).
% 4.08/1.70  tff(c_70, plain, (r3_waybel_9('#skF_2', k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'), '#skF_4') | r1_waybel_7('#skF_2', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_206])).
% 4.08/1.70  tff(c_139, plain, (r1_waybel_7('#skF_2', '#skF_3', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_111, c_70])).
% 4.08/1.70  tff(c_62, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_206])).
% 4.08/1.70  tff(c_106, plain, (![A_43]: (~v1_xboole_0(u1_struct_0(A_43)) | ~l1_struct_0(A_43) | v2_struct_0(A_43))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.08/1.70  tff(c_109, plain, (~v1_xboole_0(k2_struct_0('#skF_2')) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_90, c_106])).
% 4.08/1.70  tff(c_110, plain, (~v1_xboole_0(k2_struct_0('#skF_2')) | ~l1_struct_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_62, c_109])).
% 4.08/1.70  tff(c_112, plain, (~l1_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_110])).
% 4.08/1.70  tff(c_115, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_14, c_112])).
% 4.08/1.70  tff(c_119, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_115])).
% 4.08/1.70  tff(c_120, plain, (~v1_xboole_0(k2_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_110])).
% 4.08/1.70  tff(c_56, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_206])).
% 4.08/1.70  tff(c_121, plain, (l1_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_110])).
% 4.08/1.70  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.08/1.70  tff(c_128, plain, (![A_46, B_47]: (~r2_hidden('#skF_1'(A_46, B_47), B_47) | r1_tarski(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.08/1.70  tff(c_133, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_128])).
% 4.08/1.70  tff(c_10, plain, (![A_6, B_7]: (m1_subset_1(A_6, k1_zfmisc_1(B_7)) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.08/1.70  tff(c_52, plain, (v2_waybel_0('#skF_3', k3_yellow_1(k2_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_206])).
% 4.08/1.70  tff(c_50, plain, (v13_waybel_0('#skF_3', k3_yellow_1(k2_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_206])).
% 4.08/1.70  tff(c_48, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2')))))), inference(cnfTransformation, [status(thm)], [f_206])).
% 4.08/1.70  tff(c_195, plain, (![A_74, B_75, C_76]: (v4_orders_2(k3_yellow19(A_74, B_75, C_76)) | ~m1_subset_1(C_76, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_75)))) | ~v13_waybel_0(C_76, k3_yellow_1(B_75)) | ~v2_waybel_0(C_76, k3_yellow_1(B_75)) | v1_xboole_0(C_76) | ~m1_subset_1(B_75, k1_zfmisc_1(u1_struct_0(A_74))) | v1_xboole_0(B_75) | ~l1_struct_0(A_74) | v2_struct_0(A_74))), inference(cnfTransformation, [status(thm)], [f_108])).
% 4.08/1.70  tff(c_200, plain, (![A_74]: (v4_orders_2(k3_yellow19(A_74, k2_struct_0('#skF_2'), '#skF_3')) | ~v13_waybel_0('#skF_3', k3_yellow_1(k2_struct_0('#skF_2'))) | ~v2_waybel_0('#skF_3', k3_yellow_1(k2_struct_0('#skF_2'))) | v1_xboole_0('#skF_3') | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(u1_struct_0(A_74))) | v1_xboole_0(k2_struct_0('#skF_2')) | ~l1_struct_0(A_74) | v2_struct_0(A_74))), inference(resolution, [status(thm)], [c_48, c_195])).
% 4.08/1.70  tff(c_204, plain, (![A_74]: (v4_orders_2(k3_yellow19(A_74, k2_struct_0('#skF_2'), '#skF_3')) | v1_xboole_0('#skF_3') | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(u1_struct_0(A_74))) | v1_xboole_0(k2_struct_0('#skF_2')) | ~l1_struct_0(A_74) | v2_struct_0(A_74))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_200])).
% 4.08/1.70  tff(c_206, plain, (![A_77]: (v4_orders_2(k3_yellow19(A_77, k2_struct_0('#skF_2'), '#skF_3')) | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(u1_struct_0(A_77))) | ~l1_struct_0(A_77) | v2_struct_0(A_77))), inference(negUnitSimplification, [status(thm)], [c_120, c_56, c_204])).
% 4.08/1.70  tff(c_212, plain, (v4_orders_2(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3')) | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_90, c_206])).
% 4.08/1.70  tff(c_215, plain, (v4_orders_2(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3')) | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_2'))) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_121, c_212])).
% 4.08/1.70  tff(c_216, plain, (v4_orders_2(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3')) | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_62, c_215])).
% 4.08/1.70  tff(c_217, plain, (~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_2')))), inference(splitLeft, [status(thm)], [c_216])).
% 4.08/1.70  tff(c_220, plain, (~r1_tarski(k2_struct_0('#skF_2'), k2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_10, c_217])).
% 4.08/1.70  tff(c_224, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_133, c_220])).
% 4.08/1.70  tff(c_226, plain, (m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_216])).
% 4.08/1.70  tff(c_60, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_206])).
% 4.08/1.70  tff(c_225, plain, (v4_orders_2(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'))), inference(splitRight, [status(thm)], [c_216])).
% 4.08/1.70  tff(c_54, plain, (v1_subset_1('#skF_3', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_206])).
% 4.08/1.70  tff(c_558, plain, (![A_138, B_139, C_140]: (v7_waybel_0(k3_yellow19(A_138, B_139, C_140)) | ~m1_subset_1(C_140, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_139)))) | ~v13_waybel_0(C_140, k3_yellow_1(B_139)) | ~v2_waybel_0(C_140, k3_yellow_1(B_139)) | ~v1_subset_1(C_140, u1_struct_0(k3_yellow_1(B_139))) | v1_xboole_0(C_140) | ~m1_subset_1(B_139, k1_zfmisc_1(u1_struct_0(A_138))) | v1_xboole_0(B_139) | ~l1_struct_0(A_138) | v2_struct_0(A_138))), inference(cnfTransformation, [status(thm)], [f_136])).
% 4.08/1.70  tff(c_563, plain, (![A_138]: (v7_waybel_0(k3_yellow19(A_138, k2_struct_0('#skF_2'), '#skF_3')) | ~v13_waybel_0('#skF_3', k3_yellow_1(k2_struct_0('#skF_2'))) | ~v2_waybel_0('#skF_3', k3_yellow_1(k2_struct_0('#skF_2'))) | ~v1_subset_1('#skF_3', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2')))) | v1_xboole_0('#skF_3') | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(u1_struct_0(A_138))) | v1_xboole_0(k2_struct_0('#skF_2')) | ~l1_struct_0(A_138) | v2_struct_0(A_138))), inference(resolution, [status(thm)], [c_48, c_558])).
% 4.08/1.70  tff(c_567, plain, (![A_138]: (v7_waybel_0(k3_yellow19(A_138, k2_struct_0('#skF_2'), '#skF_3')) | v1_xboole_0('#skF_3') | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(u1_struct_0(A_138))) | v1_xboole_0(k2_struct_0('#skF_2')) | ~l1_struct_0(A_138) | v2_struct_0(A_138))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_563])).
% 4.08/1.70  tff(c_569, plain, (![A_141]: (v7_waybel_0(k3_yellow19(A_141, k2_struct_0('#skF_2'), '#skF_3')) | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(u1_struct_0(A_141))) | ~l1_struct_0(A_141) | v2_struct_0(A_141))), inference(negUnitSimplification, [status(thm)], [c_120, c_56, c_567])).
% 4.08/1.70  tff(c_575, plain, (v7_waybel_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3')) | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_90, c_569])).
% 4.08/1.70  tff(c_578, plain, (v7_waybel_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_121, c_226, c_575])).
% 4.08/1.70  tff(c_579, plain, (v7_waybel_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_62, c_578])).
% 4.08/1.70  tff(c_474, plain, (![A_121, B_122, C_123]: (l1_waybel_0(k3_yellow19(A_121, B_122, C_123), A_121) | ~m1_subset_1(C_123, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_122)))) | ~v13_waybel_0(C_123, k3_yellow_1(B_122)) | ~v2_waybel_0(C_123, k3_yellow_1(B_122)) | v1_xboole_0(C_123) | ~m1_subset_1(B_122, k1_zfmisc_1(u1_struct_0(A_121))) | v1_xboole_0(B_122) | ~l1_struct_0(A_121) | v2_struct_0(A_121))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.08/1.70  tff(c_479, plain, (![A_121]: (l1_waybel_0(k3_yellow19(A_121, k2_struct_0('#skF_2'), '#skF_3'), A_121) | ~v13_waybel_0('#skF_3', k3_yellow_1(k2_struct_0('#skF_2'))) | ~v2_waybel_0('#skF_3', k3_yellow_1(k2_struct_0('#skF_2'))) | v1_xboole_0('#skF_3') | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(u1_struct_0(A_121))) | v1_xboole_0(k2_struct_0('#skF_2')) | ~l1_struct_0(A_121) | v2_struct_0(A_121))), inference(resolution, [status(thm)], [c_48, c_474])).
% 4.08/1.70  tff(c_483, plain, (![A_121]: (l1_waybel_0(k3_yellow19(A_121, k2_struct_0('#skF_2'), '#skF_3'), A_121) | v1_xboole_0('#skF_3') | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(u1_struct_0(A_121))) | v1_xboole_0(k2_struct_0('#skF_2')) | ~l1_struct_0(A_121) | v2_struct_0(A_121))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_479])).
% 4.08/1.70  tff(c_485, plain, (![A_124]: (l1_waybel_0(k3_yellow19(A_124, k2_struct_0('#skF_2'), '#skF_3'), A_124) | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(u1_struct_0(A_124))) | ~l1_struct_0(A_124) | v2_struct_0(A_124))), inference(negUnitSimplification, [status(thm)], [c_120, c_56, c_483])).
% 4.08/1.70  tff(c_490, plain, (l1_waybel_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'), '#skF_2') | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_90, c_485])).
% 4.08/1.70  tff(c_493, plain, (l1_waybel_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'), '#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_121, c_226, c_490])).
% 4.08/1.70  tff(c_494, plain, (l1_waybel_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_62, c_493])).
% 4.08/1.70  tff(c_626, plain, (![A_154, B_155]: (k2_yellow19(A_154, k3_yellow19(A_154, k2_struct_0(A_154), B_155))=B_155 | ~m1_subset_1(B_155, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_154))))) | ~v13_waybel_0(B_155, k3_yellow_1(k2_struct_0(A_154))) | ~v2_waybel_0(B_155, k3_yellow_1(k2_struct_0(A_154))) | ~v1_subset_1(B_155, u1_struct_0(k3_yellow_1(k2_struct_0(A_154)))) | v1_xboole_0(B_155) | ~l1_struct_0(A_154) | v2_struct_0(A_154))), inference(cnfTransformation, [status(thm)], [f_179])).
% 4.08/1.70  tff(c_631, plain, (k2_yellow19('#skF_2', k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'))='#skF_3' | ~v13_waybel_0('#skF_3', k3_yellow_1(k2_struct_0('#skF_2'))) | ~v2_waybel_0('#skF_3', k3_yellow_1(k2_struct_0('#skF_2'))) | ~v1_subset_1('#skF_3', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2')))) | v1_xboole_0('#skF_3') | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_48, c_626])).
% 4.08/1.70  tff(c_635, plain, (k2_yellow19('#skF_2', k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'))='#skF_3' | v1_xboole_0('#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_121, c_54, c_52, c_50, c_631])).
% 4.08/1.70  tff(c_636, plain, (k2_yellow19('#skF_2', k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'))='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_62, c_56, c_635])).
% 4.08/1.70  tff(c_40, plain, (![A_21, B_25, C_27]: (r3_waybel_9(A_21, B_25, C_27) | ~r1_waybel_7(A_21, k2_yellow19(A_21, B_25), C_27) | ~m1_subset_1(C_27, u1_struct_0(A_21)) | ~l1_waybel_0(B_25, A_21) | ~v7_waybel_0(B_25) | ~v4_orders_2(B_25) | v2_struct_0(B_25) | ~l1_pre_topc(A_21) | ~v2_pre_topc(A_21) | v2_struct_0(A_21))), inference(cnfTransformation, [status(thm)], [f_160])).
% 4.08/1.70  tff(c_640, plain, (![C_27]: (r3_waybel_9('#skF_2', k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'), C_27) | ~r1_waybel_7('#skF_2', '#skF_3', C_27) | ~m1_subset_1(C_27, u1_struct_0('#skF_2')) | ~l1_waybel_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'), '#skF_2') | ~v7_waybel_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3')) | ~v4_orders_2(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3')) | v2_struct_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_636, c_40])).
% 4.08/1.70  tff(c_647, plain, (![C_27]: (r3_waybel_9('#skF_2', k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'), C_27) | ~r1_waybel_7('#skF_2', '#skF_3', C_27) | ~m1_subset_1(C_27, k2_struct_0('#skF_2')) | v2_struct_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_225, c_579, c_494, c_90, c_640])).
% 4.08/1.70  tff(c_648, plain, (![C_27]: (r3_waybel_9('#skF_2', k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'), C_27) | ~r1_waybel_7('#skF_2', '#skF_3', C_27) | ~m1_subset_1(C_27, k2_struct_0('#skF_2')) | v2_struct_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_62, c_647])).
% 4.08/1.70  tff(c_653, plain, (v2_struct_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'))), inference(splitLeft, [status(thm)], [c_648])).
% 4.08/1.70  tff(c_32, plain, (![A_15, B_16, C_17]: (~v2_struct_0(k3_yellow19(A_15, B_16, C_17)) | ~m1_subset_1(C_17, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_16)))) | ~v13_waybel_0(C_17, k3_yellow_1(B_16)) | ~v2_waybel_0(C_17, k3_yellow_1(B_16)) | v1_xboole_0(C_17) | ~m1_subset_1(B_16, k1_zfmisc_1(u1_struct_0(A_15))) | v1_xboole_0(B_16) | ~l1_struct_0(A_15) | v2_struct_0(A_15))), inference(cnfTransformation, [status(thm)], [f_108])).
% 4.08/1.70  tff(c_655, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2'))))) | ~v13_waybel_0('#skF_3', k3_yellow_1(k2_struct_0('#skF_2'))) | ~v2_waybel_0('#skF_3', k3_yellow_1(k2_struct_0('#skF_2'))) | v1_xboole_0('#skF_3') | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | v1_xboole_0(k2_struct_0('#skF_2')) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_653, c_32])).
% 4.08/1.70  tff(c_658, plain, (v1_xboole_0('#skF_3') | v1_xboole_0(k2_struct_0('#skF_2')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_121, c_226, c_90, c_52, c_50, c_48, c_655])).
% 4.08/1.70  tff(c_660, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_120, c_56, c_658])).
% 4.08/1.70  tff(c_675, plain, (![C_160]: (r3_waybel_9('#skF_2', k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'), C_160) | ~r1_waybel_7('#skF_2', '#skF_3', C_160) | ~m1_subset_1(C_160, k2_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_648])).
% 4.08/1.70  tff(c_681, plain, (~r1_waybel_7('#skF_2', '#skF_3', '#skF_4') | ~m1_subset_1('#skF_4', k2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_675, c_111])).
% 4.08/1.70  tff(c_686, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_91, c_139, c_681])).
% 4.08/1.70  tff(c_687, plain, (~r1_waybel_7('#skF_2', '#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_64])).
% 4.08/1.70  tff(c_688, plain, (r3_waybel_9('#skF_2', k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'), '#skF_4')), inference(splitRight, [status(thm)], [c_64])).
% 4.08/1.70  tff(c_689, plain, (~l1_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_110])).
% 4.08/1.70  tff(c_693, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_14, c_689])).
% 4.08/1.70  tff(c_697, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_693])).
% 4.08/1.70  tff(c_698, plain, (~v1_xboole_0(k2_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_110])).
% 4.08/1.70  tff(c_699, plain, (l1_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_110])).
% 4.08/1.70  tff(c_706, plain, (![A_163, B_164]: (r2_hidden('#skF_1'(A_163, B_164), A_163) | r1_tarski(A_163, B_164))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.08/1.70  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.08/1.70  tff(c_711, plain, (![A_163]: (r1_tarski(A_163, A_163))), inference(resolution, [status(thm)], [c_706, c_4])).
% 4.08/1.70  tff(c_774, plain, (![A_191, B_192, C_193]: (v3_orders_2(k3_yellow19(A_191, B_192, C_193)) | ~m1_subset_1(C_193, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_192)))) | ~v13_waybel_0(C_193, k3_yellow_1(B_192)) | ~v2_waybel_0(C_193, k3_yellow_1(B_192)) | v1_xboole_0(C_193) | ~m1_subset_1(B_192, k1_zfmisc_1(u1_struct_0(A_191))) | v1_xboole_0(B_192) | ~l1_struct_0(A_191) | v2_struct_0(A_191))), inference(cnfTransformation, [status(thm)], [f_108])).
% 4.08/1.70  tff(c_779, plain, (![A_191]: (v3_orders_2(k3_yellow19(A_191, k2_struct_0('#skF_2'), '#skF_3')) | ~v13_waybel_0('#skF_3', k3_yellow_1(k2_struct_0('#skF_2'))) | ~v2_waybel_0('#skF_3', k3_yellow_1(k2_struct_0('#skF_2'))) | v1_xboole_0('#skF_3') | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(u1_struct_0(A_191))) | v1_xboole_0(k2_struct_0('#skF_2')) | ~l1_struct_0(A_191) | v2_struct_0(A_191))), inference(resolution, [status(thm)], [c_48, c_774])).
% 4.08/1.70  tff(c_783, plain, (![A_191]: (v3_orders_2(k3_yellow19(A_191, k2_struct_0('#skF_2'), '#skF_3')) | v1_xboole_0('#skF_3') | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(u1_struct_0(A_191))) | v1_xboole_0(k2_struct_0('#skF_2')) | ~l1_struct_0(A_191) | v2_struct_0(A_191))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_779])).
% 4.08/1.70  tff(c_785, plain, (![A_194]: (v3_orders_2(k3_yellow19(A_194, k2_struct_0('#skF_2'), '#skF_3')) | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(u1_struct_0(A_194))) | ~l1_struct_0(A_194) | v2_struct_0(A_194))), inference(negUnitSimplification, [status(thm)], [c_698, c_56, c_783])).
% 4.08/1.70  tff(c_791, plain, (v3_orders_2(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3')) | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_90, c_785])).
% 4.08/1.70  tff(c_794, plain, (v3_orders_2(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3')) | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_2'))) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_699, c_791])).
% 4.08/1.70  tff(c_795, plain, (v3_orders_2(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3')) | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_62, c_794])).
% 4.08/1.70  tff(c_796, plain, (~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_2')))), inference(splitLeft, [status(thm)], [c_795])).
% 4.08/1.70  tff(c_799, plain, (~r1_tarski(k2_struct_0('#skF_2'), k2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_10, c_796])).
% 4.08/1.70  tff(c_803, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_711, c_799])).
% 4.08/1.70  tff(c_805, plain, (m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_795])).
% 4.08/1.70  tff(c_825, plain, (![A_199, B_200, C_201]: (v4_orders_2(k3_yellow19(A_199, B_200, C_201)) | ~m1_subset_1(C_201, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_200)))) | ~v13_waybel_0(C_201, k3_yellow_1(B_200)) | ~v2_waybel_0(C_201, k3_yellow_1(B_200)) | v1_xboole_0(C_201) | ~m1_subset_1(B_200, k1_zfmisc_1(u1_struct_0(A_199))) | v1_xboole_0(B_200) | ~l1_struct_0(A_199) | v2_struct_0(A_199))), inference(cnfTransformation, [status(thm)], [f_108])).
% 4.08/1.70  tff(c_830, plain, (![A_199]: (v4_orders_2(k3_yellow19(A_199, k2_struct_0('#skF_2'), '#skF_3')) | ~v13_waybel_0('#skF_3', k3_yellow_1(k2_struct_0('#skF_2'))) | ~v2_waybel_0('#skF_3', k3_yellow_1(k2_struct_0('#skF_2'))) | v1_xboole_0('#skF_3') | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(u1_struct_0(A_199))) | v1_xboole_0(k2_struct_0('#skF_2')) | ~l1_struct_0(A_199) | v2_struct_0(A_199))), inference(resolution, [status(thm)], [c_48, c_825])).
% 4.08/1.70  tff(c_834, plain, (![A_199]: (v4_orders_2(k3_yellow19(A_199, k2_struct_0('#skF_2'), '#skF_3')) | v1_xboole_0('#skF_3') | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(u1_struct_0(A_199))) | v1_xboole_0(k2_struct_0('#skF_2')) | ~l1_struct_0(A_199) | v2_struct_0(A_199))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_830])).
% 4.08/1.70  tff(c_836, plain, (![A_202]: (v4_orders_2(k3_yellow19(A_202, k2_struct_0('#skF_2'), '#skF_3')) | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(u1_struct_0(A_202))) | ~l1_struct_0(A_202) | v2_struct_0(A_202))), inference(negUnitSimplification, [status(thm)], [c_698, c_56, c_834])).
% 4.08/1.70  tff(c_842, plain, (v4_orders_2(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3')) | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_90, c_836])).
% 4.08/1.70  tff(c_845, plain, (v4_orders_2(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_699, c_805, c_842])).
% 4.08/1.70  tff(c_846, plain, (v4_orders_2(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_62, c_845])).
% 4.08/1.70  tff(c_894, plain, (![A_209, B_210, C_211]: (l1_waybel_0(k3_yellow19(A_209, B_210, C_211), A_209) | ~m1_subset_1(C_211, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_210)))) | ~v13_waybel_0(C_211, k3_yellow_1(B_210)) | ~v2_waybel_0(C_211, k3_yellow_1(B_210)) | v1_xboole_0(C_211) | ~m1_subset_1(B_210, k1_zfmisc_1(u1_struct_0(A_209))) | v1_xboole_0(B_210) | ~l1_struct_0(A_209) | v2_struct_0(A_209))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.08/1.70  tff(c_899, plain, (![A_209]: (l1_waybel_0(k3_yellow19(A_209, k2_struct_0('#skF_2'), '#skF_3'), A_209) | ~v13_waybel_0('#skF_3', k3_yellow_1(k2_struct_0('#skF_2'))) | ~v2_waybel_0('#skF_3', k3_yellow_1(k2_struct_0('#skF_2'))) | v1_xboole_0('#skF_3') | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(u1_struct_0(A_209))) | v1_xboole_0(k2_struct_0('#skF_2')) | ~l1_struct_0(A_209) | v2_struct_0(A_209))), inference(resolution, [status(thm)], [c_48, c_894])).
% 4.08/1.70  tff(c_903, plain, (![A_209]: (l1_waybel_0(k3_yellow19(A_209, k2_struct_0('#skF_2'), '#skF_3'), A_209) | v1_xboole_0('#skF_3') | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(u1_struct_0(A_209))) | v1_xboole_0(k2_struct_0('#skF_2')) | ~l1_struct_0(A_209) | v2_struct_0(A_209))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_899])).
% 4.08/1.70  tff(c_905, plain, (![A_212]: (l1_waybel_0(k3_yellow19(A_212, k2_struct_0('#skF_2'), '#skF_3'), A_212) | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(u1_struct_0(A_212))) | ~l1_struct_0(A_212) | v2_struct_0(A_212))), inference(negUnitSimplification, [status(thm)], [c_698, c_56, c_903])).
% 4.08/1.70  tff(c_910, plain, (l1_waybel_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'), '#skF_2') | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_90, c_905])).
% 4.08/1.70  tff(c_913, plain, (l1_waybel_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'), '#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_699, c_805, c_910])).
% 4.08/1.70  tff(c_914, plain, (l1_waybel_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_62, c_913])).
% 4.08/1.70  tff(c_1043, plain, (![A_236, B_237]: (k2_yellow19(A_236, k3_yellow19(A_236, k2_struct_0(A_236), B_237))=B_237 | ~m1_subset_1(B_237, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_236))))) | ~v13_waybel_0(B_237, k3_yellow_1(k2_struct_0(A_236))) | ~v2_waybel_0(B_237, k3_yellow_1(k2_struct_0(A_236))) | ~v1_subset_1(B_237, u1_struct_0(k3_yellow_1(k2_struct_0(A_236)))) | v1_xboole_0(B_237) | ~l1_struct_0(A_236) | v2_struct_0(A_236))), inference(cnfTransformation, [status(thm)], [f_179])).
% 4.08/1.70  tff(c_1048, plain, (k2_yellow19('#skF_2', k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'))='#skF_3' | ~v13_waybel_0('#skF_3', k3_yellow_1(k2_struct_0('#skF_2'))) | ~v2_waybel_0('#skF_3', k3_yellow_1(k2_struct_0('#skF_2'))) | ~v1_subset_1('#skF_3', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2')))) | v1_xboole_0('#skF_3') | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_48, c_1043])).
% 4.08/1.70  tff(c_1052, plain, (k2_yellow19('#skF_2', k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'))='#skF_3' | v1_xboole_0('#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_699, c_54, c_52, c_50, c_1048])).
% 4.08/1.70  tff(c_1053, plain, (k2_yellow19('#skF_2', k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'))='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_62, c_56, c_1052])).
% 4.08/1.70  tff(c_42, plain, (![A_21, B_25, C_27]: (r1_waybel_7(A_21, k2_yellow19(A_21, B_25), C_27) | ~r3_waybel_9(A_21, B_25, C_27) | ~m1_subset_1(C_27, u1_struct_0(A_21)) | ~l1_waybel_0(B_25, A_21) | ~v7_waybel_0(B_25) | ~v4_orders_2(B_25) | v2_struct_0(B_25) | ~l1_pre_topc(A_21) | ~v2_pre_topc(A_21) | v2_struct_0(A_21))), inference(cnfTransformation, [status(thm)], [f_160])).
% 4.08/1.70  tff(c_1057, plain, (![C_27]: (r1_waybel_7('#skF_2', '#skF_3', C_27) | ~r3_waybel_9('#skF_2', k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'), C_27) | ~m1_subset_1(C_27, u1_struct_0('#skF_2')) | ~l1_waybel_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'), '#skF_2') | ~v7_waybel_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3')) | ~v4_orders_2(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3')) | v2_struct_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1053, c_42])).
% 4.08/1.70  tff(c_1064, plain, (![C_27]: (r1_waybel_7('#skF_2', '#skF_3', C_27) | ~r3_waybel_9('#skF_2', k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'), C_27) | ~m1_subset_1(C_27, k2_struct_0('#skF_2')) | ~v7_waybel_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3')) | v2_struct_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_846, c_914, c_90, c_1057])).
% 4.08/1.70  tff(c_1065, plain, (![C_27]: (r1_waybel_7('#skF_2', '#skF_3', C_27) | ~r3_waybel_9('#skF_2', k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'), C_27) | ~m1_subset_1(C_27, k2_struct_0('#skF_2')) | ~v7_waybel_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3')) | v2_struct_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_62, c_1064])).
% 4.08/1.70  tff(c_1070, plain, (~v7_waybel_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'))), inference(splitLeft, [status(thm)], [c_1065])).
% 4.08/1.70  tff(c_1129, plain, (![A_249, B_250, C_251]: (v7_waybel_0(k3_yellow19(A_249, B_250, C_251)) | ~m1_subset_1(C_251, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_250)))) | ~v13_waybel_0(C_251, k3_yellow_1(B_250)) | ~v2_waybel_0(C_251, k3_yellow_1(B_250)) | ~v1_subset_1(C_251, u1_struct_0(k3_yellow_1(B_250))) | v1_xboole_0(C_251) | ~m1_subset_1(B_250, k1_zfmisc_1(u1_struct_0(A_249))) | v1_xboole_0(B_250) | ~l1_struct_0(A_249) | v2_struct_0(A_249))), inference(cnfTransformation, [status(thm)], [f_136])).
% 4.08/1.70  tff(c_1134, plain, (![A_249]: (v7_waybel_0(k3_yellow19(A_249, k2_struct_0('#skF_2'), '#skF_3')) | ~v13_waybel_0('#skF_3', k3_yellow_1(k2_struct_0('#skF_2'))) | ~v2_waybel_0('#skF_3', k3_yellow_1(k2_struct_0('#skF_2'))) | ~v1_subset_1('#skF_3', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2')))) | v1_xboole_0('#skF_3') | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(u1_struct_0(A_249))) | v1_xboole_0(k2_struct_0('#skF_2')) | ~l1_struct_0(A_249) | v2_struct_0(A_249))), inference(resolution, [status(thm)], [c_48, c_1129])).
% 4.08/1.70  tff(c_1138, plain, (![A_249]: (v7_waybel_0(k3_yellow19(A_249, k2_struct_0('#skF_2'), '#skF_3')) | v1_xboole_0('#skF_3') | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(u1_struct_0(A_249))) | v1_xboole_0(k2_struct_0('#skF_2')) | ~l1_struct_0(A_249) | v2_struct_0(A_249))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_1134])).
% 4.08/1.70  tff(c_1140, plain, (![A_252]: (v7_waybel_0(k3_yellow19(A_252, k2_struct_0('#skF_2'), '#skF_3')) | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(u1_struct_0(A_252))) | ~l1_struct_0(A_252) | v2_struct_0(A_252))), inference(negUnitSimplification, [status(thm)], [c_698, c_56, c_1138])).
% 4.08/1.70  tff(c_1146, plain, (v7_waybel_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3')) | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_90, c_1140])).
% 4.08/1.70  tff(c_1149, plain, (v7_waybel_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_699, c_805, c_1146])).
% 4.08/1.70  tff(c_1151, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_1070, c_1149])).
% 4.08/1.70  tff(c_1152, plain, (![C_27]: (v2_struct_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3')) | r1_waybel_7('#skF_2', '#skF_3', C_27) | ~r3_waybel_9('#skF_2', k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'), C_27) | ~m1_subset_1(C_27, k2_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_1065])).
% 4.08/1.70  tff(c_1154, plain, (v2_struct_0(k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'))), inference(splitLeft, [status(thm)], [c_1152])).
% 4.08/1.70  tff(c_1159, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2'))))) | ~v13_waybel_0('#skF_3', k3_yellow_1(k2_struct_0('#skF_2'))) | ~v2_waybel_0('#skF_3', k3_yellow_1(k2_struct_0('#skF_2'))) | v1_xboole_0('#skF_3') | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | v1_xboole_0(k2_struct_0('#skF_2')) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_1154, c_32])).
% 4.08/1.70  tff(c_1162, plain, (v1_xboole_0('#skF_3') | v1_xboole_0(k2_struct_0('#skF_2')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_699, c_805, c_90, c_52, c_50, c_48, c_1159])).
% 4.08/1.70  tff(c_1164, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_698, c_56, c_1162])).
% 4.08/1.70  tff(c_1167, plain, (![C_253]: (r1_waybel_7('#skF_2', '#skF_3', C_253) | ~r3_waybel_9('#skF_2', k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'), C_253) | ~m1_subset_1(C_253, k2_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_1152])).
% 4.08/1.70  tff(c_1170, plain, (r1_waybel_7('#skF_2', '#skF_3', '#skF_4') | ~m1_subset_1('#skF_4', k2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_688, c_1167])).
% 4.08/1.70  tff(c_1173, plain, (r1_waybel_7('#skF_2', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_91, c_1170])).
% 4.08/1.70  tff(c_1175, plain, $false, inference(negUnitSimplification, [status(thm)], [c_687, c_1173])).
% 4.08/1.70  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.08/1.70  
% 4.08/1.70  Inference rules
% 4.08/1.70  ----------------------
% 4.08/1.70  #Ref     : 0
% 4.08/1.70  #Sup     : 194
% 4.08/1.70  #Fact    : 0
% 4.08/1.71  #Define  : 0
% 4.08/1.71  #Split   : 16
% 4.08/1.71  #Chain   : 0
% 4.08/1.71  #Close   : 0
% 4.08/1.71  
% 4.08/1.71  Ordering : KBO
% 4.08/1.71  
% 4.08/1.71  Simplification rules
% 4.08/1.71  ----------------------
% 4.08/1.71  #Subsume      : 39
% 4.08/1.71  #Demod        : 201
% 4.08/1.71  #Tautology    : 40
% 4.08/1.71  #SimpNegUnit  : 94
% 4.08/1.71  #BackRed      : 1
% 4.08/1.71  
% 4.08/1.71  #Partial instantiations: 0
% 4.08/1.71  #Strategies tried      : 1
% 4.08/1.71  
% 4.08/1.71  Timing (in seconds)
% 4.08/1.71  ----------------------
% 4.08/1.71  Preprocessing        : 0.35
% 4.08/1.71  Parsing              : 0.19
% 4.08/1.71  CNF conversion       : 0.02
% 4.08/1.71  Main loop            : 0.51
% 4.08/1.71  Inferencing          : 0.18
% 4.08/1.71  Reduction            : 0.16
% 4.08/1.71  Demodulation         : 0.11
% 4.08/1.71  BG Simplification    : 0.03
% 4.08/1.71  Subsumption          : 0.10
% 4.08/1.71  Abstraction          : 0.02
% 4.08/1.71  MUC search           : 0.00
% 4.08/1.71  Cooper               : 0.00
% 4.08/1.71  Total                : 0.93
% 4.08/1.71  Index Insertion      : 0.00
% 4.08/1.71  Index Deletion       : 0.00
% 4.08/1.71  Index Matching       : 0.00
% 4.08/1.71  BG Taut test         : 0.00
%------------------------------------------------------------------------------
