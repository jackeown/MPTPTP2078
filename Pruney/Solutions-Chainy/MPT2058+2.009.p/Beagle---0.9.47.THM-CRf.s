%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:33 EST 2020

% Result     : Theorem 4.44s
% Output     : CNFRefutation 4.76s
% Verified   : 
% Statistics : Number of formulae       :  215 (4053 expanded)
%              Number of leaves         :   53 (1437 expanded)
%              Depth                    :   25
%              Number of atoms          :  654 (15884 expanded)
%              Number of equality atoms :   15 ( 656 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_waybel_9 > r1_waybel_7 > v6_waybel_0 > v4_pre_topc > v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > l1_waybel_0 > v7_waybel_0 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k3_yellow19 > k2_yellow19 > #nlpp > u1_struct_0 > k3_yellow_1 > k3_lattice3 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_lattice3 > #skF_1 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_2

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

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

tff(k3_yellow19,type,(
    k3_yellow19: ( $i * $i * $i ) > $i )).

tff(v13_waybel_0,type,(
    v13_waybel_0: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_242,negated_conjecture,(
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

tff(f_73,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_69,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_88,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ? [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
          & ~ v1_xboole_0(B)
          & v4_pre_topc(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc7_pre_topc)).

tff(f_65,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_49,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_57,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ ( r1_tarski(B,A)
          & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).

tff(f_59,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_61,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_144,axiom,(
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

tff(f_116,axiom,(
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

tff(f_215,axiom,(
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

tff(f_196,axiom,(
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

tff(f_172,axiom,(
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

tff(c_76,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_242])).

tff(c_74,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_242])).

tff(c_72,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_242])).

tff(c_24,plain,(
    ! [A_17] :
      ( l1_struct_0(A_17)
      | ~ l1_pre_topc(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_112,plain,(
    ! [A_51] :
      ( u1_struct_0(A_51) = k2_struct_0(A_51)
      | ~ l1_struct_0(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_117,plain,(
    ! [A_52] :
      ( u1_struct_0(A_52) = k2_struct_0(A_52)
      | ~ l1_pre_topc(A_52) ) ),
    inference(resolution,[status(thm)],[c_24,c_112])).

tff(c_121,plain,(
    u1_struct_0('#skF_4') = k2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_72,c_117])).

tff(c_60,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_242])).

tff(c_122,plain,(
    m1_subset_1('#skF_6',k2_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_60])).

tff(c_84,plain,
    ( r3_waybel_9('#skF_4',k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'),'#skF_6')
    | r1_waybel_7('#skF_4','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_242])).

tff(c_127,plain,(
    r1_waybel_7('#skF_4','#skF_5','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_84])).

tff(c_186,plain,(
    ! [A_75] :
      ( m1_subset_1('#skF_3'(A_75),k1_zfmisc_1(u1_struct_0(A_75)))
      | ~ l1_pre_topc(A_75)
      | ~ v2_pre_topc(A_75)
      | v2_struct_0(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_192,plain,
    ( m1_subset_1('#skF_3'('#skF_4'),k1_zfmisc_1(k2_struct_0('#skF_4')))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_121,c_186])).

tff(c_195,plain,
    ( m1_subset_1('#skF_3'('#skF_4'),k1_zfmisc_1(k2_struct_0('#skF_4')))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_192])).

tff(c_196,plain,(
    m1_subset_1('#skF_3'('#skF_4'),k1_zfmisc_1(k2_struct_0('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_195])).

tff(c_18,plain,(
    ! [A_14,B_15] :
      ( r1_tarski(A_14,B_15)
      | ~ m1_subset_1(A_14,k1_zfmisc_1(B_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_200,plain,(
    r1_tarski('#skF_3'('#skF_4'),k2_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_196,c_18])).

tff(c_154,plain,(
    ! [A_64,B_65] :
      ( r2_hidden('#skF_2'(A_64,B_65),B_65)
      | r1_xboole_0(A_64,B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_161,plain,(
    ! [B_66,A_67] :
      ( ~ v1_xboole_0(B_66)
      | r1_xboole_0(A_67,B_66) ) ),
    inference(resolution,[status(thm)],[c_154,c_2])).

tff(c_12,plain,(
    ! [B_11,A_10] :
      ( ~ r1_xboole_0(B_11,A_10)
      | ~ r1_tarski(B_11,A_10)
      | v1_xboole_0(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_165,plain,(
    ! [A_67,B_66] :
      ( ~ r1_tarski(A_67,B_66)
      | v1_xboole_0(A_67)
      | ~ v1_xboole_0(B_66) ) ),
    inference(resolution,[status(thm)],[c_161,c_12])).

tff(c_204,plain,
    ( v1_xboole_0('#skF_3'('#skF_4'))
    | ~ v1_xboole_0(k2_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_200,c_165])).

tff(c_205,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_204])).

tff(c_70,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_242])).

tff(c_14,plain,(
    ! [A_12] : k2_subset_1(A_12) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_16,plain,(
    ! [A_13] : m1_subset_1(k2_subset_1(A_13),k1_zfmisc_1(A_13)) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_85,plain,(
    ! [A_13] : m1_subset_1(A_13,k1_zfmisc_1(A_13)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_16])).

tff(c_66,plain,(
    v2_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_242])).

tff(c_64,plain,(
    v13_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_242])).

tff(c_62,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4'))))) ),
    inference(cnfTransformation,[status(thm)],[f_242])).

tff(c_231,plain,(
    ! [A_87,B_88,C_89] :
      ( v3_orders_2(k3_yellow19(A_87,B_88,C_89))
      | ~ m1_subset_1(C_89,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_88))))
      | ~ v13_waybel_0(C_89,k3_yellow_1(B_88))
      | ~ v2_waybel_0(C_89,k3_yellow_1(B_88))
      | v1_xboole_0(C_89)
      | ~ m1_subset_1(B_88,k1_zfmisc_1(u1_struct_0(A_87)))
      | v1_xboole_0(B_88)
      | ~ l1_struct_0(A_87)
      | v2_struct_0(A_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_239,plain,(
    ! [A_87] :
      ( v3_orders_2(k3_yellow19(A_87,k2_struct_0('#skF_4'),'#skF_5'))
      | ~ v13_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_4')))
      | ~ v2_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_4')))
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0(A_87)))
      | v1_xboole_0(k2_struct_0('#skF_4'))
      | ~ l1_struct_0(A_87)
      | v2_struct_0(A_87) ) ),
    inference(resolution,[status(thm)],[c_62,c_231])).

tff(c_247,plain,(
    ! [A_87] :
      ( v3_orders_2(k3_yellow19(A_87,k2_struct_0('#skF_4'),'#skF_5'))
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0(A_87)))
      | v1_xboole_0(k2_struct_0('#skF_4'))
      | ~ l1_struct_0(A_87)
      | v2_struct_0(A_87) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_239])).

tff(c_250,plain,(
    ! [A_90] :
      ( v3_orders_2(k3_yellow19(A_90,k2_struct_0('#skF_4'),'#skF_5'))
      | ~ m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0(A_90)))
      | ~ l1_struct_0(A_90)
      | v2_struct_0(A_90) ) ),
    inference(negUnitSimplification,[status(thm)],[c_205,c_70,c_247])).

tff(c_256,plain,
    ( v3_orders_2(k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'))
    | ~ m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(k2_struct_0('#skF_4')))
    | ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_121,c_250])).

tff(c_259,plain,
    ( v3_orders_2(k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'))
    | ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_256])).

tff(c_260,plain,
    ( v3_orders_2(k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'))
    | ~ l1_struct_0('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_259])).

tff(c_261,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_260])).

tff(c_264,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_24,c_261])).

tff(c_268,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_264])).

tff(c_270,plain,(
    l1_struct_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_260])).

tff(c_323,plain,(
    ! [A_97,B_98,C_99] :
      ( v4_orders_2(k3_yellow19(A_97,B_98,C_99))
      | ~ m1_subset_1(C_99,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_98))))
      | ~ v13_waybel_0(C_99,k3_yellow_1(B_98))
      | ~ v2_waybel_0(C_99,k3_yellow_1(B_98))
      | v1_xboole_0(C_99)
      | ~ m1_subset_1(B_98,k1_zfmisc_1(u1_struct_0(A_97)))
      | v1_xboole_0(B_98)
      | ~ l1_struct_0(A_97)
      | v2_struct_0(A_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_331,plain,(
    ! [A_97] :
      ( v4_orders_2(k3_yellow19(A_97,k2_struct_0('#skF_4'),'#skF_5'))
      | ~ v13_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_4')))
      | ~ v2_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_4')))
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0(A_97)))
      | v1_xboole_0(k2_struct_0('#skF_4'))
      | ~ l1_struct_0(A_97)
      | v2_struct_0(A_97) ) ),
    inference(resolution,[status(thm)],[c_62,c_323])).

tff(c_339,plain,(
    ! [A_97] :
      ( v4_orders_2(k3_yellow19(A_97,k2_struct_0('#skF_4'),'#skF_5'))
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0(A_97)))
      | v1_xboole_0(k2_struct_0('#skF_4'))
      | ~ l1_struct_0(A_97)
      | v2_struct_0(A_97) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_331])).

tff(c_342,plain,(
    ! [A_100] :
      ( v4_orders_2(k3_yellow19(A_100,k2_struct_0('#skF_4'),'#skF_5'))
      | ~ m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0(A_100)))
      | ~ l1_struct_0(A_100)
      | v2_struct_0(A_100) ) ),
    inference(negUnitSimplification,[status(thm)],[c_205,c_70,c_339])).

tff(c_348,plain,
    ( v4_orders_2(k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'))
    | ~ m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(k2_struct_0('#skF_4')))
    | ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_121,c_342])).

tff(c_351,plain,
    ( v4_orders_2(k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_270,c_85,c_348])).

tff(c_352,plain,(
    v4_orders_2(k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_351])).

tff(c_402,plain,(
    ! [A_109,B_110,C_111] :
      ( l1_waybel_0(k3_yellow19(A_109,B_110,C_111),A_109)
      | ~ m1_subset_1(C_111,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_110))))
      | ~ v13_waybel_0(C_111,k3_yellow_1(B_110))
      | ~ v2_waybel_0(C_111,k3_yellow_1(B_110))
      | v1_xboole_0(C_111)
      | ~ m1_subset_1(B_110,k1_zfmisc_1(u1_struct_0(A_109)))
      | v1_xboole_0(B_110)
      | ~ l1_struct_0(A_109)
      | v2_struct_0(A_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_410,plain,(
    ! [A_109] :
      ( l1_waybel_0(k3_yellow19(A_109,k2_struct_0('#skF_4'),'#skF_5'),A_109)
      | ~ v13_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_4')))
      | ~ v2_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_4')))
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0(A_109)))
      | v1_xboole_0(k2_struct_0('#skF_4'))
      | ~ l1_struct_0(A_109)
      | v2_struct_0(A_109) ) ),
    inference(resolution,[status(thm)],[c_62,c_402])).

tff(c_418,plain,(
    ! [A_109] :
      ( l1_waybel_0(k3_yellow19(A_109,k2_struct_0('#skF_4'),'#skF_5'),A_109)
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0(A_109)))
      | v1_xboole_0(k2_struct_0('#skF_4'))
      | ~ l1_struct_0(A_109)
      | v2_struct_0(A_109) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_410])).

tff(c_421,plain,(
    ! [A_112] :
      ( l1_waybel_0(k3_yellow19(A_112,k2_struct_0('#skF_4'),'#skF_5'),A_112)
      | ~ m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0(A_112)))
      | ~ l1_struct_0(A_112)
      | v2_struct_0(A_112) ) ),
    inference(negUnitSimplification,[status(thm)],[c_205,c_70,c_418])).

tff(c_426,plain,
    ( l1_waybel_0(k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'),'#skF_4')
    | ~ m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(k2_struct_0('#skF_4')))
    | ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_121,c_421])).

tff(c_429,plain,
    ( l1_waybel_0(k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'),'#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_270,c_85,c_426])).

tff(c_430,plain,(
    l1_waybel_0(k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_429])).

tff(c_68,plain,(
    v1_subset_1('#skF_5',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4')))) ),
    inference(cnfTransformation,[status(thm)],[f_242])).

tff(c_623,plain,(
    ! [A_139,B_140] :
      ( k2_yellow19(A_139,k3_yellow19(A_139,k2_struct_0(A_139),B_140)) = B_140
      | ~ m1_subset_1(B_140,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_139)))))
      | ~ v13_waybel_0(B_140,k3_yellow_1(k2_struct_0(A_139)))
      | ~ v2_waybel_0(B_140,k3_yellow_1(k2_struct_0(A_139)))
      | ~ v1_subset_1(B_140,u1_struct_0(k3_yellow_1(k2_struct_0(A_139))))
      | v1_xboole_0(B_140)
      | ~ l1_struct_0(A_139)
      | v2_struct_0(A_139) ) ),
    inference(cnfTransformation,[status(thm)],[f_215])).

tff(c_631,plain,
    ( k2_yellow19('#skF_4',k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5')) = '#skF_5'
    | ~ v13_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_4')))
    | ~ v2_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_4')))
    | ~ v1_subset_1('#skF_5',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4'))))
    | v1_xboole_0('#skF_5')
    | ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_623])).

tff(c_639,plain,
    ( k2_yellow19('#skF_4',k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5')) = '#skF_5'
    | v1_xboole_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_270,c_68,c_66,c_64,c_631])).

tff(c_640,plain,(
    k2_yellow19('#skF_4',k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5')) = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_70,c_639])).

tff(c_56,plain,(
    ! [A_30,B_34,C_36] :
      ( r1_waybel_7(A_30,k2_yellow19(A_30,B_34),C_36)
      | ~ r3_waybel_9(A_30,B_34,C_36)
      | ~ m1_subset_1(C_36,u1_struct_0(A_30))
      | ~ l1_waybel_0(B_34,A_30)
      | ~ v7_waybel_0(B_34)
      | ~ v4_orders_2(B_34)
      | v2_struct_0(B_34)
      | ~ l1_pre_topc(A_30)
      | ~ v2_pre_topc(A_30)
      | v2_struct_0(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_645,plain,(
    ! [C_36] :
      ( r1_waybel_7('#skF_4','#skF_5',C_36)
      | ~ r3_waybel_9('#skF_4',k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'),C_36)
      | ~ m1_subset_1(C_36,u1_struct_0('#skF_4'))
      | ~ l1_waybel_0(k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'),'#skF_4')
      | ~ v7_waybel_0(k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'))
      | ~ v4_orders_2(k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'))
      | v2_struct_0(k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'))
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_640,c_56])).

tff(c_652,plain,(
    ! [C_36] :
      ( r1_waybel_7('#skF_4','#skF_5',C_36)
      | ~ r3_waybel_9('#skF_4',k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'),C_36)
      | ~ m1_subset_1(C_36,k2_struct_0('#skF_4'))
      | ~ v7_waybel_0(k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'))
      | v2_struct_0(k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_352,c_430,c_121,c_645])).

tff(c_653,plain,(
    ! [C_36] :
      ( r1_waybel_7('#skF_4','#skF_5',C_36)
      | ~ r3_waybel_9('#skF_4',k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'),C_36)
      | ~ m1_subset_1(C_36,k2_struct_0('#skF_4'))
      | ~ v7_waybel_0(k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'))
      | v2_struct_0(k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_652])).

tff(c_658,plain,(
    ~ v7_waybel_0(k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_653])).

tff(c_715,plain,(
    ! [A_151,B_152,C_153] :
      ( v7_waybel_0(k3_yellow19(A_151,B_152,C_153))
      | ~ m1_subset_1(C_153,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_152))))
      | ~ v13_waybel_0(C_153,k3_yellow_1(B_152))
      | ~ v2_waybel_0(C_153,k3_yellow_1(B_152))
      | ~ v1_subset_1(C_153,u1_struct_0(k3_yellow_1(B_152)))
      | v1_xboole_0(C_153)
      | ~ m1_subset_1(B_152,k1_zfmisc_1(u1_struct_0(A_151)))
      | v1_xboole_0(B_152)
      | ~ l1_struct_0(A_151)
      | v2_struct_0(A_151) ) ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_723,plain,(
    ! [A_151] :
      ( v7_waybel_0(k3_yellow19(A_151,k2_struct_0('#skF_4'),'#skF_5'))
      | ~ v13_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_4')))
      | ~ v2_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_4')))
      | ~ v1_subset_1('#skF_5',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4'))))
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0(A_151)))
      | v1_xboole_0(k2_struct_0('#skF_4'))
      | ~ l1_struct_0(A_151)
      | v2_struct_0(A_151) ) ),
    inference(resolution,[status(thm)],[c_62,c_715])).

tff(c_731,plain,(
    ! [A_151] :
      ( v7_waybel_0(k3_yellow19(A_151,k2_struct_0('#skF_4'),'#skF_5'))
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0(A_151)))
      | v1_xboole_0(k2_struct_0('#skF_4'))
      | ~ l1_struct_0(A_151)
      | v2_struct_0(A_151) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_64,c_723])).

tff(c_734,plain,(
    ! [A_154] :
      ( v7_waybel_0(k3_yellow19(A_154,k2_struct_0('#skF_4'),'#skF_5'))
      | ~ m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0(A_154)))
      | ~ l1_struct_0(A_154)
      | v2_struct_0(A_154) ) ),
    inference(negUnitSimplification,[status(thm)],[c_205,c_70,c_731])).

tff(c_740,plain,
    ( v7_waybel_0(k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'))
    | ~ m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(k2_struct_0('#skF_4')))
    | ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_121,c_734])).

tff(c_743,plain,
    ( v7_waybel_0(k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_270,c_85,c_740])).

tff(c_745,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_658,c_743])).

tff(c_746,plain,(
    ! [C_36] :
      ( v2_struct_0(k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'))
      | r1_waybel_7('#skF_4','#skF_5',C_36)
      | ~ r3_waybel_9('#skF_4',k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'),C_36)
      | ~ m1_subset_1(C_36,k2_struct_0('#skF_4')) ) ),
    inference(splitRight,[status(thm)],[c_653])).

tff(c_748,plain,(
    v2_struct_0(k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_746])).

tff(c_46,plain,(
    ! [A_24,B_25,C_26] :
      ( ~ v2_struct_0(k3_yellow19(A_24,B_25,C_26))
      | ~ m1_subset_1(C_26,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_25))))
      | ~ v13_waybel_0(C_26,k3_yellow_1(B_25))
      | ~ v2_waybel_0(C_26,k3_yellow_1(B_25))
      | v1_xboole_0(C_26)
      | ~ m1_subset_1(B_25,k1_zfmisc_1(u1_struct_0(A_24)))
      | v1_xboole_0(B_25)
      | ~ l1_struct_0(A_24)
      | v2_struct_0(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_753,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4')))))
    | ~ v13_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_4')))
    | ~ v2_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_4')))
    | v1_xboole_0('#skF_5')
    | ~ m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | v1_xboole_0(k2_struct_0('#skF_4'))
    | ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_748,c_46])).

tff(c_756,plain,
    ( v1_xboole_0('#skF_5')
    | v1_xboole_0(k2_struct_0('#skF_4'))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_270,c_85,c_121,c_66,c_64,c_62,c_753])).

tff(c_758,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_205,c_70,c_756])).

tff(c_760,plain,(
    ~ v2_struct_0(k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5')) ),
    inference(splitRight,[status(thm)],[c_746])).

tff(c_747,plain,(
    v7_waybel_0(k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5')) ),
    inference(splitRight,[status(thm)],[c_653])).

tff(c_54,plain,(
    ! [A_30,B_34,C_36] :
      ( r3_waybel_9(A_30,B_34,C_36)
      | ~ r1_waybel_7(A_30,k2_yellow19(A_30,B_34),C_36)
      | ~ m1_subset_1(C_36,u1_struct_0(A_30))
      | ~ l1_waybel_0(B_34,A_30)
      | ~ v7_waybel_0(B_34)
      | ~ v4_orders_2(B_34)
      | v2_struct_0(B_34)
      | ~ l1_pre_topc(A_30)
      | ~ v2_pre_topc(A_30)
      | v2_struct_0(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_648,plain,(
    ! [C_36] :
      ( r3_waybel_9('#skF_4',k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'),C_36)
      | ~ r1_waybel_7('#skF_4','#skF_5',C_36)
      | ~ m1_subset_1(C_36,u1_struct_0('#skF_4'))
      | ~ l1_waybel_0(k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'),'#skF_4')
      | ~ v7_waybel_0(k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'))
      | ~ v4_orders_2(k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'))
      | v2_struct_0(k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'))
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_640,c_54])).

tff(c_655,plain,(
    ! [C_36] :
      ( r3_waybel_9('#skF_4',k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'),C_36)
      | ~ r1_waybel_7('#skF_4','#skF_5',C_36)
      | ~ m1_subset_1(C_36,k2_struct_0('#skF_4'))
      | ~ v7_waybel_0(k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'))
      | v2_struct_0(k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_352,c_430,c_121,c_648])).

tff(c_656,plain,(
    ! [C_36] :
      ( r3_waybel_9('#skF_4',k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'),C_36)
      | ~ r1_waybel_7('#skF_4','#skF_5',C_36)
      | ~ m1_subset_1(C_36,k2_struct_0('#skF_4'))
      | ~ v7_waybel_0(k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'))
      | v2_struct_0(k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_655])).

tff(c_763,plain,(
    ! [C_36] :
      ( r3_waybel_9('#skF_4',k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'),C_36)
      | ~ r1_waybel_7('#skF_4','#skF_5',C_36)
      | ~ m1_subset_1(C_36,k2_struct_0('#skF_4'))
      | v2_struct_0(k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_747,c_656])).

tff(c_765,plain,(
    ! [C_156] :
      ( r3_waybel_9('#skF_4',k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'),C_156)
      | ~ r1_waybel_7('#skF_4','#skF_5',C_156)
      | ~ m1_subset_1(C_156,k2_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_760,c_763])).

tff(c_78,plain,
    ( ~ r1_waybel_7('#skF_4','#skF_5','#skF_6')
    | ~ r3_waybel_9('#skF_4',k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_242])).

tff(c_160,plain,(
    ~ r3_waybel_9('#skF_4',k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_78])).

tff(c_771,plain,
    ( ~ r1_waybel_7('#skF_4','#skF_5','#skF_6')
    | ~ m1_subset_1('#skF_6',k2_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_765,c_160])).

tff(c_776,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_127,c_771])).

tff(c_777,plain,(
    v1_xboole_0('#skF_3'('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_204])).

tff(c_28,plain,(
    ! [A_18] :
      ( ~ v1_xboole_0('#skF_3'(A_18))
      | ~ l1_pre_topc(A_18)
      | ~ v2_pre_topc(A_18)
      | v2_struct_0(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_781,plain,
    ( ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_777,c_28])).

tff(c_784,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_781])).

tff(c_786,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_784])).

tff(c_788,plain,(
    ~ r1_waybel_7('#skF_4','#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_787,plain,(
    r3_waybel_9('#skF_4',k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_845,plain,(
    ! [A_179] :
      ( m1_subset_1('#skF_3'(A_179),k1_zfmisc_1(u1_struct_0(A_179)))
      | ~ l1_pre_topc(A_179)
      | ~ v2_pre_topc(A_179)
      | v2_struct_0(A_179) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_851,plain,
    ( m1_subset_1('#skF_3'('#skF_4'),k1_zfmisc_1(k2_struct_0('#skF_4')))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_121,c_845])).

tff(c_854,plain,
    ( m1_subset_1('#skF_3'('#skF_4'),k1_zfmisc_1(k2_struct_0('#skF_4')))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_851])).

tff(c_855,plain,(
    m1_subset_1('#skF_3'('#skF_4'),k1_zfmisc_1(k2_struct_0('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_854])).

tff(c_859,plain,(
    r1_tarski('#skF_3'('#skF_4'),k2_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_855,c_18])).

tff(c_804,plain,(
    ! [A_162,B_163] :
      ( r2_hidden('#skF_2'(A_162,B_163),B_163)
      | r1_xboole_0(A_162,B_163) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_808,plain,(
    ! [B_163,A_162] :
      ( ~ v1_xboole_0(B_163)
      | r1_xboole_0(A_162,B_163) ) ),
    inference(resolution,[status(thm)],[c_804,c_2])).

tff(c_810,plain,(
    ! [B_166,A_167] :
      ( ~ r1_xboole_0(B_166,A_167)
      | ~ r1_tarski(B_166,A_167)
      | v1_xboole_0(B_166) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_814,plain,(
    ! [A_162,B_163] :
      ( ~ r1_tarski(A_162,B_163)
      | v1_xboole_0(A_162)
      | ~ v1_xboole_0(B_163) ) ),
    inference(resolution,[status(thm)],[c_808,c_810])).

tff(c_863,plain,
    ( v1_xboole_0('#skF_3'('#skF_4'))
    | ~ v1_xboole_0(k2_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_859,c_814])).

tff(c_865,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_863])).

tff(c_889,plain,(
    ! [A_188,B_189,C_190] :
      ( v4_orders_2(k3_yellow19(A_188,B_189,C_190))
      | ~ m1_subset_1(C_190,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_189))))
      | ~ v13_waybel_0(C_190,k3_yellow_1(B_189))
      | ~ v2_waybel_0(C_190,k3_yellow_1(B_189))
      | v1_xboole_0(C_190)
      | ~ m1_subset_1(B_189,k1_zfmisc_1(u1_struct_0(A_188)))
      | v1_xboole_0(B_189)
      | ~ l1_struct_0(A_188)
      | v2_struct_0(A_188) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_897,plain,(
    ! [A_188] :
      ( v4_orders_2(k3_yellow19(A_188,k2_struct_0('#skF_4'),'#skF_5'))
      | ~ v13_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_4')))
      | ~ v2_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_4')))
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0(A_188)))
      | v1_xboole_0(k2_struct_0('#skF_4'))
      | ~ l1_struct_0(A_188)
      | v2_struct_0(A_188) ) ),
    inference(resolution,[status(thm)],[c_62,c_889])).

tff(c_905,plain,(
    ! [A_188] :
      ( v4_orders_2(k3_yellow19(A_188,k2_struct_0('#skF_4'),'#skF_5'))
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0(A_188)))
      | v1_xboole_0(k2_struct_0('#skF_4'))
      | ~ l1_struct_0(A_188)
      | v2_struct_0(A_188) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_897])).

tff(c_908,plain,(
    ! [A_191] :
      ( v4_orders_2(k3_yellow19(A_191,k2_struct_0('#skF_4'),'#skF_5'))
      | ~ m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0(A_191)))
      | ~ l1_struct_0(A_191)
      | v2_struct_0(A_191) ) ),
    inference(negUnitSimplification,[status(thm)],[c_865,c_70,c_905])).

tff(c_914,plain,
    ( v4_orders_2(k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'))
    | ~ m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(k2_struct_0('#skF_4')))
    | ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_121,c_908])).

tff(c_917,plain,
    ( v4_orders_2(k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'))
    | ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_914])).

tff(c_918,plain,
    ( v4_orders_2(k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'))
    | ~ l1_struct_0('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_917])).

tff(c_919,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_918])).

tff(c_922,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_24,c_919])).

tff(c_926,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_922])).

tff(c_928,plain,(
    l1_struct_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_918])).

tff(c_927,plain,(
    v4_orders_2(k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5')) ),
    inference(splitRight,[status(thm)],[c_918])).

tff(c_1214,plain,(
    ! [A_233,B_234,C_235] :
      ( l1_waybel_0(k3_yellow19(A_233,B_234,C_235),A_233)
      | ~ m1_subset_1(C_235,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_234))))
      | ~ v13_waybel_0(C_235,k3_yellow_1(B_234))
      | ~ v2_waybel_0(C_235,k3_yellow_1(B_234))
      | v1_xboole_0(C_235)
      | ~ m1_subset_1(B_234,k1_zfmisc_1(u1_struct_0(A_233)))
      | v1_xboole_0(B_234)
      | ~ l1_struct_0(A_233)
      | v2_struct_0(A_233) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_1222,plain,(
    ! [A_233] :
      ( l1_waybel_0(k3_yellow19(A_233,k2_struct_0('#skF_4'),'#skF_5'),A_233)
      | ~ v13_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_4')))
      | ~ v2_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_4')))
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0(A_233)))
      | v1_xboole_0(k2_struct_0('#skF_4'))
      | ~ l1_struct_0(A_233)
      | v2_struct_0(A_233) ) ),
    inference(resolution,[status(thm)],[c_62,c_1214])).

tff(c_1230,plain,(
    ! [A_233] :
      ( l1_waybel_0(k3_yellow19(A_233,k2_struct_0('#skF_4'),'#skF_5'),A_233)
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0(A_233)))
      | v1_xboole_0(k2_struct_0('#skF_4'))
      | ~ l1_struct_0(A_233)
      | v2_struct_0(A_233) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_1222])).

tff(c_1233,plain,(
    ! [A_236] :
      ( l1_waybel_0(k3_yellow19(A_236,k2_struct_0('#skF_4'),'#skF_5'),A_236)
      | ~ m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0(A_236)))
      | ~ l1_struct_0(A_236)
      | v2_struct_0(A_236) ) ),
    inference(negUnitSimplification,[status(thm)],[c_865,c_70,c_1230])).

tff(c_1238,plain,
    ( l1_waybel_0(k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'),'#skF_4')
    | ~ m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(k2_struct_0('#skF_4')))
    | ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_121,c_1233])).

tff(c_1241,plain,
    ( l1_waybel_0(k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'),'#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_928,c_85,c_1238])).

tff(c_1242,plain,(
    l1_waybel_0(k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_1241])).

tff(c_1337,plain,(
    ! [A_252,B_253] :
      ( k2_yellow19(A_252,k3_yellow19(A_252,k2_struct_0(A_252),B_253)) = B_253
      | ~ m1_subset_1(B_253,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_252)))))
      | ~ v13_waybel_0(B_253,k3_yellow_1(k2_struct_0(A_252)))
      | ~ v2_waybel_0(B_253,k3_yellow_1(k2_struct_0(A_252)))
      | ~ v1_subset_1(B_253,u1_struct_0(k3_yellow_1(k2_struct_0(A_252))))
      | v1_xboole_0(B_253)
      | ~ l1_struct_0(A_252)
      | v2_struct_0(A_252) ) ),
    inference(cnfTransformation,[status(thm)],[f_215])).

tff(c_1345,plain,
    ( k2_yellow19('#skF_4',k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5')) = '#skF_5'
    | ~ v13_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_4')))
    | ~ v2_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_4')))
    | ~ v1_subset_1('#skF_5',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4'))))
    | v1_xboole_0('#skF_5')
    | ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_1337])).

tff(c_1353,plain,
    ( k2_yellow19('#skF_4',k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5')) = '#skF_5'
    | v1_xboole_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_928,c_68,c_66,c_64,c_1345])).

tff(c_1354,plain,(
    k2_yellow19('#skF_4',k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5')) = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_70,c_1353])).

tff(c_1359,plain,(
    ! [C_36] :
      ( r3_waybel_9('#skF_4',k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'),C_36)
      | ~ r1_waybel_7('#skF_4','#skF_5',C_36)
      | ~ m1_subset_1(C_36,u1_struct_0('#skF_4'))
      | ~ l1_waybel_0(k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'),'#skF_4')
      | ~ v7_waybel_0(k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'))
      | ~ v4_orders_2(k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'))
      | v2_struct_0(k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'))
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1354,c_54])).

tff(c_1366,plain,(
    ! [C_36] :
      ( r3_waybel_9('#skF_4',k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'),C_36)
      | ~ r1_waybel_7('#skF_4','#skF_5',C_36)
      | ~ m1_subset_1(C_36,k2_struct_0('#skF_4'))
      | ~ v7_waybel_0(k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'))
      | v2_struct_0(k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_927,c_1242,c_121,c_1359])).

tff(c_1367,plain,(
    ! [C_36] :
      ( r3_waybel_9('#skF_4',k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'),C_36)
      | ~ r1_waybel_7('#skF_4','#skF_5',C_36)
      | ~ m1_subset_1(C_36,k2_struct_0('#skF_4'))
      | ~ v7_waybel_0(k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'))
      | v2_struct_0(k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_1366])).

tff(c_1372,plain,(
    ~ v7_waybel_0(k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_1367])).

tff(c_1440,plain,(
    ! [A_261,B_262,C_263] :
      ( v7_waybel_0(k3_yellow19(A_261,B_262,C_263))
      | ~ m1_subset_1(C_263,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_262))))
      | ~ v13_waybel_0(C_263,k3_yellow_1(B_262))
      | ~ v2_waybel_0(C_263,k3_yellow_1(B_262))
      | ~ v1_subset_1(C_263,u1_struct_0(k3_yellow_1(B_262)))
      | v1_xboole_0(C_263)
      | ~ m1_subset_1(B_262,k1_zfmisc_1(u1_struct_0(A_261)))
      | v1_xboole_0(B_262)
      | ~ l1_struct_0(A_261)
      | v2_struct_0(A_261) ) ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_1448,plain,(
    ! [A_261] :
      ( v7_waybel_0(k3_yellow19(A_261,k2_struct_0('#skF_4'),'#skF_5'))
      | ~ v13_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_4')))
      | ~ v2_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_4')))
      | ~ v1_subset_1('#skF_5',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4'))))
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0(A_261)))
      | v1_xboole_0(k2_struct_0('#skF_4'))
      | ~ l1_struct_0(A_261)
      | v2_struct_0(A_261) ) ),
    inference(resolution,[status(thm)],[c_62,c_1440])).

tff(c_1456,plain,(
    ! [A_261] :
      ( v7_waybel_0(k3_yellow19(A_261,k2_struct_0('#skF_4'),'#skF_5'))
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0(A_261)))
      | v1_xboole_0(k2_struct_0('#skF_4'))
      | ~ l1_struct_0(A_261)
      | v2_struct_0(A_261) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_64,c_1448])).

tff(c_1459,plain,(
    ! [A_264] :
      ( v7_waybel_0(k3_yellow19(A_264,k2_struct_0('#skF_4'),'#skF_5'))
      | ~ m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0(A_264)))
      | ~ l1_struct_0(A_264)
      | v2_struct_0(A_264) ) ),
    inference(negUnitSimplification,[status(thm)],[c_865,c_70,c_1456])).

tff(c_1465,plain,
    ( v7_waybel_0(k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'))
    | ~ m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(k2_struct_0('#skF_4')))
    | ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_121,c_1459])).

tff(c_1468,plain,
    ( v7_waybel_0(k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_928,c_85,c_1465])).

tff(c_1470,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_1372,c_1468])).

tff(c_1471,plain,(
    ! [C_36] :
      ( v2_struct_0(k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'))
      | r3_waybel_9('#skF_4',k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'),C_36)
      | ~ r1_waybel_7('#skF_4','#skF_5',C_36)
      | ~ m1_subset_1(C_36,k2_struct_0('#skF_4')) ) ),
    inference(splitRight,[status(thm)],[c_1367])).

tff(c_1473,plain,(
    v2_struct_0(k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_1471])).

tff(c_1478,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4')))))
    | ~ v13_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_4')))
    | ~ v2_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_4')))
    | v1_xboole_0('#skF_5')
    | ~ m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | v1_xboole_0(k2_struct_0('#skF_4'))
    | ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_1473,c_46])).

tff(c_1481,plain,
    ( v1_xboole_0('#skF_5')
    | v1_xboole_0(k2_struct_0('#skF_4'))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_928,c_85,c_121,c_66,c_64,c_62,c_1478])).

tff(c_1483,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_865,c_70,c_1481])).

tff(c_1485,plain,(
    ~ v2_struct_0(k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5')) ),
    inference(splitRight,[status(thm)],[c_1471])).

tff(c_1472,plain,(
    v7_waybel_0(k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5')) ),
    inference(splitRight,[status(thm)],[c_1367])).

tff(c_1362,plain,(
    ! [C_36] :
      ( r1_waybel_7('#skF_4','#skF_5',C_36)
      | ~ r3_waybel_9('#skF_4',k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'),C_36)
      | ~ m1_subset_1(C_36,u1_struct_0('#skF_4'))
      | ~ l1_waybel_0(k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'),'#skF_4')
      | ~ v7_waybel_0(k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'))
      | ~ v4_orders_2(k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'))
      | v2_struct_0(k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'))
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1354,c_56])).

tff(c_1369,plain,(
    ! [C_36] :
      ( r1_waybel_7('#skF_4','#skF_5',C_36)
      | ~ r3_waybel_9('#skF_4',k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'),C_36)
      | ~ m1_subset_1(C_36,k2_struct_0('#skF_4'))
      | ~ v7_waybel_0(k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'))
      | v2_struct_0(k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_927,c_1242,c_121,c_1362])).

tff(c_1370,plain,(
    ! [C_36] :
      ( r1_waybel_7('#skF_4','#skF_5',C_36)
      | ~ r3_waybel_9('#skF_4',k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'),C_36)
      | ~ m1_subset_1(C_36,k2_struct_0('#skF_4'))
      | ~ v7_waybel_0(k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'))
      | v2_struct_0(k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_1369])).

tff(c_1488,plain,(
    ! [C_36] :
      ( r1_waybel_7('#skF_4','#skF_5',C_36)
      | ~ r3_waybel_9('#skF_4',k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'),C_36)
      | ~ m1_subset_1(C_36,k2_struct_0('#skF_4'))
      | v2_struct_0(k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1472,c_1370])).

tff(c_1490,plain,(
    ! [C_266] :
      ( r1_waybel_7('#skF_4','#skF_5',C_266)
      | ~ r3_waybel_9('#skF_4',k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'),C_266)
      | ~ m1_subset_1(C_266,k2_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1485,c_1488])).

tff(c_1496,plain,
    ( r1_waybel_7('#skF_4','#skF_5','#skF_6')
    | ~ m1_subset_1('#skF_6',k2_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_787,c_1490])).

tff(c_1500,plain,(
    r1_waybel_7('#skF_4','#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_1496])).

tff(c_1502,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_788,c_1500])).

tff(c_1503,plain,(
    v1_xboole_0('#skF_3'('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_863])).

tff(c_1507,plain,
    ( ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_1503,c_28])).

tff(c_1510,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_1507])).

tff(c_1512,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_1510])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:24:17 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.44/1.78  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.52/1.80  
% 4.52/1.80  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.52/1.81  %$ r3_waybel_9 > r1_waybel_7 > v6_waybel_0 > v4_pre_topc > v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > l1_waybel_0 > v7_waybel_0 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k3_yellow19 > k2_yellow19 > #nlpp > u1_struct_0 > k3_yellow_1 > k3_lattice3 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_lattice3 > #skF_1 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_2
% 4.52/1.81  
% 4.52/1.81  %Foreground sorts:
% 4.52/1.81  
% 4.52/1.81  
% 4.52/1.81  %Background operators:
% 4.52/1.81  
% 4.52/1.81  
% 4.52/1.81  %Foreground operators:
% 4.52/1.81  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.52/1.81  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 4.52/1.81  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.52/1.81  tff(k3_lattice3, type, k3_lattice3: $i > $i).
% 4.52/1.81  tff(v6_waybel_0, type, v6_waybel_0: ($i * $i) > $o).
% 4.52/1.81  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.52/1.81  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 4.52/1.81  tff(k3_yellow_1, type, k3_yellow_1: $i > $i).
% 4.52/1.81  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.52/1.81  tff(v2_waybel_0, type, v2_waybel_0: ($i * $i) > $o).
% 4.52/1.81  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.52/1.81  tff(v7_waybel_0, type, v7_waybel_0: $i > $o).
% 4.52/1.81  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.52/1.81  tff('#skF_5', type, '#skF_5': $i).
% 4.52/1.81  tff(r3_waybel_9, type, r3_waybel_9: ($i * $i * $i) > $o).
% 4.52/1.81  tff('#skF_6', type, '#skF_6': $i).
% 4.52/1.81  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.52/1.81  tff(k1_lattice3, type, k1_lattice3: $i > $i).
% 4.52/1.81  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 4.52/1.81  tff(r1_waybel_7, type, r1_waybel_7: ($i * $i * $i) > $o).
% 4.52/1.81  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.52/1.81  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 4.52/1.81  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 4.52/1.81  tff(k2_yellow19, type, k2_yellow19: ($i * $i) > $i).
% 4.52/1.81  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.52/1.81  tff(l1_waybel_0, type, l1_waybel_0: ($i * $i) > $o).
% 4.52/1.81  tff('#skF_4', type, '#skF_4': $i).
% 4.52/1.81  tff('#skF_3', type, '#skF_3': $i > $i).
% 4.52/1.81  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.52/1.81  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.52/1.81  tff(k3_yellow19, type, k3_yellow19: ($i * $i * $i) > $i).
% 4.52/1.81  tff(v13_waybel_0, type, v13_waybel_0: ($i * $i) > $o).
% 4.52/1.81  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.52/1.81  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.52/1.81  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 4.52/1.81  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 4.52/1.81  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.52/1.81  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.52/1.81  
% 4.76/1.84  tff(f_242, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((((~v1_xboole_0(B) & v1_subset_1(B, u1_struct_0(k3_yellow_1(k2_struct_0(A))))) & v2_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & v13_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A)))))) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r3_waybel_9(A, k3_yellow19(A, k2_struct_0(A), B), C) <=> r1_waybel_7(A, B, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_yellow19)).
% 4.76/1.84  tff(f_73, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 4.76/1.84  tff(f_69, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 4.76/1.84  tff(f_88, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (?[B]: ((m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) & ~v1_xboole_0(B)) & v4_pre_topc(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc7_pre_topc)).
% 4.76/1.84  tff(f_65, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 4.76/1.84  tff(f_49, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 4.76/1.84  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 4.76/1.84  tff(f_57, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_xboole_1)).
% 4.76/1.84  tff(f_59, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 4.76/1.84  tff(f_61, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 4.76/1.84  tff(f_144, axiom, (![A, B, C]: ((((((((~v2_struct_0(A) & l1_struct_0(A)) & ~v1_xboole_0(B)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) & ~v1_xboole_0(C)) & v2_waybel_0(C, k3_yellow_1(B))) & v13_waybel_0(C, k3_yellow_1(B))) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B))))) => (((~v2_struct_0(k3_yellow19(A, B, C)) & v3_orders_2(k3_yellow19(A, B, C))) & v4_orders_2(k3_yellow19(A, B, C))) & v6_waybel_0(k3_yellow19(A, B, C), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_yellow19)).
% 4.76/1.84  tff(f_116, axiom, (![A, B, C]: ((((((((~v2_struct_0(A) & l1_struct_0(A)) & ~v1_xboole_0(B)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) & ~v1_xboole_0(C)) & v2_waybel_0(C, k3_yellow_1(B))) & v13_waybel_0(C, k3_yellow_1(B))) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B))))) => ((~v2_struct_0(k3_yellow19(A, B, C)) & v6_waybel_0(k3_yellow19(A, B, C), A)) & l1_waybel_0(k3_yellow19(A, B, C), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_yellow19)).
% 4.76/1.84  tff(f_215, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: (((((~v1_xboole_0(B) & v1_subset_1(B, u1_struct_0(k3_yellow_1(k2_struct_0(A))))) & v2_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & v13_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A)))))) => (B = k2_yellow19(A, k3_yellow19(A, k2_struct_0(A), B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_yellow19)).
% 4.76/1.84  tff(f_196, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r3_waybel_9(A, B, C) <=> r1_waybel_7(A, k2_yellow19(A, B), C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_yellow19)).
% 4.76/1.84  tff(f_172, axiom, (![A, B, C]: (((((((((~v2_struct_0(A) & l1_struct_0(A)) & ~v1_xboole_0(B)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) & ~v1_xboole_0(C)) & v1_subset_1(C, u1_struct_0(k3_yellow_1(B)))) & v2_waybel_0(C, k3_yellow_1(B))) & v13_waybel_0(C, k3_yellow_1(B))) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B))))) => ((~v2_struct_0(k3_yellow19(A, B, C)) & v6_waybel_0(k3_yellow19(A, B, C), A)) & v7_waybel_0(k3_yellow19(A, B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc5_yellow19)).
% 4.76/1.84  tff(c_76, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_242])).
% 4.76/1.84  tff(c_74, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_242])).
% 4.76/1.84  tff(c_72, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_242])).
% 4.76/1.84  tff(c_24, plain, (![A_17]: (l1_struct_0(A_17) | ~l1_pre_topc(A_17))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.76/1.84  tff(c_112, plain, (![A_51]: (u1_struct_0(A_51)=k2_struct_0(A_51) | ~l1_struct_0(A_51))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.76/1.84  tff(c_117, plain, (![A_52]: (u1_struct_0(A_52)=k2_struct_0(A_52) | ~l1_pre_topc(A_52))), inference(resolution, [status(thm)], [c_24, c_112])).
% 4.76/1.84  tff(c_121, plain, (u1_struct_0('#skF_4')=k2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_72, c_117])).
% 4.76/1.84  tff(c_60, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_242])).
% 4.76/1.84  tff(c_122, plain, (m1_subset_1('#skF_6', k2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_121, c_60])).
% 4.76/1.84  tff(c_84, plain, (r3_waybel_9('#skF_4', k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5'), '#skF_6') | r1_waybel_7('#skF_4', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_242])).
% 4.76/1.84  tff(c_127, plain, (r1_waybel_7('#skF_4', '#skF_5', '#skF_6')), inference(splitLeft, [status(thm)], [c_84])).
% 4.76/1.84  tff(c_186, plain, (![A_75]: (m1_subset_1('#skF_3'(A_75), k1_zfmisc_1(u1_struct_0(A_75))) | ~l1_pre_topc(A_75) | ~v2_pre_topc(A_75) | v2_struct_0(A_75))), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.76/1.84  tff(c_192, plain, (m1_subset_1('#skF_3'('#skF_4'), k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_121, c_186])).
% 4.76/1.84  tff(c_195, plain, (m1_subset_1('#skF_3'('#skF_4'), k1_zfmisc_1(k2_struct_0('#skF_4'))) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_192])).
% 4.76/1.84  tff(c_196, plain, (m1_subset_1('#skF_3'('#skF_4'), k1_zfmisc_1(k2_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_76, c_195])).
% 4.76/1.84  tff(c_18, plain, (![A_14, B_15]: (r1_tarski(A_14, B_15) | ~m1_subset_1(A_14, k1_zfmisc_1(B_15)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.76/1.84  tff(c_200, plain, (r1_tarski('#skF_3'('#skF_4'), k2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_196, c_18])).
% 4.76/1.84  tff(c_154, plain, (![A_64, B_65]: (r2_hidden('#skF_2'(A_64, B_65), B_65) | r1_xboole_0(A_64, B_65))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.76/1.84  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.76/1.84  tff(c_161, plain, (![B_66, A_67]: (~v1_xboole_0(B_66) | r1_xboole_0(A_67, B_66))), inference(resolution, [status(thm)], [c_154, c_2])).
% 4.76/1.84  tff(c_12, plain, (![B_11, A_10]: (~r1_xboole_0(B_11, A_10) | ~r1_tarski(B_11, A_10) | v1_xboole_0(B_11))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.76/1.84  tff(c_165, plain, (![A_67, B_66]: (~r1_tarski(A_67, B_66) | v1_xboole_0(A_67) | ~v1_xboole_0(B_66))), inference(resolution, [status(thm)], [c_161, c_12])).
% 4.76/1.84  tff(c_204, plain, (v1_xboole_0('#skF_3'('#skF_4')) | ~v1_xboole_0(k2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_200, c_165])).
% 4.76/1.84  tff(c_205, plain, (~v1_xboole_0(k2_struct_0('#skF_4'))), inference(splitLeft, [status(thm)], [c_204])).
% 4.76/1.84  tff(c_70, plain, (~v1_xboole_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_242])).
% 4.76/1.84  tff(c_14, plain, (![A_12]: (k2_subset_1(A_12)=A_12)), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.76/1.84  tff(c_16, plain, (![A_13]: (m1_subset_1(k2_subset_1(A_13), k1_zfmisc_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.76/1.84  tff(c_85, plain, (![A_13]: (m1_subset_1(A_13, k1_zfmisc_1(A_13)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_16])).
% 4.76/1.84  tff(c_66, plain, (v2_waybel_0('#skF_5', k3_yellow_1(k2_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_242])).
% 4.76/1.84  tff(c_64, plain, (v13_waybel_0('#skF_5', k3_yellow_1(k2_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_242])).
% 4.76/1.84  tff(c_62, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4')))))), inference(cnfTransformation, [status(thm)], [f_242])).
% 4.76/1.84  tff(c_231, plain, (![A_87, B_88, C_89]: (v3_orders_2(k3_yellow19(A_87, B_88, C_89)) | ~m1_subset_1(C_89, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_88)))) | ~v13_waybel_0(C_89, k3_yellow_1(B_88)) | ~v2_waybel_0(C_89, k3_yellow_1(B_88)) | v1_xboole_0(C_89) | ~m1_subset_1(B_88, k1_zfmisc_1(u1_struct_0(A_87))) | v1_xboole_0(B_88) | ~l1_struct_0(A_87) | v2_struct_0(A_87))), inference(cnfTransformation, [status(thm)], [f_144])).
% 4.76/1.84  tff(c_239, plain, (![A_87]: (v3_orders_2(k3_yellow19(A_87, k2_struct_0('#skF_4'), '#skF_5')) | ~v13_waybel_0('#skF_5', k3_yellow_1(k2_struct_0('#skF_4'))) | ~v2_waybel_0('#skF_5', k3_yellow_1(k2_struct_0('#skF_4'))) | v1_xboole_0('#skF_5') | ~m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(u1_struct_0(A_87))) | v1_xboole_0(k2_struct_0('#skF_4')) | ~l1_struct_0(A_87) | v2_struct_0(A_87))), inference(resolution, [status(thm)], [c_62, c_231])).
% 4.76/1.84  tff(c_247, plain, (![A_87]: (v3_orders_2(k3_yellow19(A_87, k2_struct_0('#skF_4'), '#skF_5')) | v1_xboole_0('#skF_5') | ~m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(u1_struct_0(A_87))) | v1_xboole_0(k2_struct_0('#skF_4')) | ~l1_struct_0(A_87) | v2_struct_0(A_87))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_239])).
% 4.76/1.84  tff(c_250, plain, (![A_90]: (v3_orders_2(k3_yellow19(A_90, k2_struct_0('#skF_4'), '#skF_5')) | ~m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(u1_struct_0(A_90))) | ~l1_struct_0(A_90) | v2_struct_0(A_90))), inference(negUnitSimplification, [status(thm)], [c_205, c_70, c_247])).
% 4.76/1.84  tff(c_256, plain, (v3_orders_2(k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5')) | ~m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_121, c_250])).
% 4.76/1.84  tff(c_259, plain, (v3_orders_2(k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5')) | ~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_85, c_256])).
% 4.76/1.84  tff(c_260, plain, (v3_orders_2(k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5')) | ~l1_struct_0('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_76, c_259])).
% 4.76/1.84  tff(c_261, plain, (~l1_struct_0('#skF_4')), inference(splitLeft, [status(thm)], [c_260])).
% 4.76/1.84  tff(c_264, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_24, c_261])).
% 4.76/1.84  tff(c_268, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_72, c_264])).
% 4.76/1.84  tff(c_270, plain, (l1_struct_0('#skF_4')), inference(splitRight, [status(thm)], [c_260])).
% 4.76/1.84  tff(c_323, plain, (![A_97, B_98, C_99]: (v4_orders_2(k3_yellow19(A_97, B_98, C_99)) | ~m1_subset_1(C_99, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_98)))) | ~v13_waybel_0(C_99, k3_yellow_1(B_98)) | ~v2_waybel_0(C_99, k3_yellow_1(B_98)) | v1_xboole_0(C_99) | ~m1_subset_1(B_98, k1_zfmisc_1(u1_struct_0(A_97))) | v1_xboole_0(B_98) | ~l1_struct_0(A_97) | v2_struct_0(A_97))), inference(cnfTransformation, [status(thm)], [f_144])).
% 4.76/1.84  tff(c_331, plain, (![A_97]: (v4_orders_2(k3_yellow19(A_97, k2_struct_0('#skF_4'), '#skF_5')) | ~v13_waybel_0('#skF_5', k3_yellow_1(k2_struct_0('#skF_4'))) | ~v2_waybel_0('#skF_5', k3_yellow_1(k2_struct_0('#skF_4'))) | v1_xboole_0('#skF_5') | ~m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(u1_struct_0(A_97))) | v1_xboole_0(k2_struct_0('#skF_4')) | ~l1_struct_0(A_97) | v2_struct_0(A_97))), inference(resolution, [status(thm)], [c_62, c_323])).
% 4.76/1.84  tff(c_339, plain, (![A_97]: (v4_orders_2(k3_yellow19(A_97, k2_struct_0('#skF_4'), '#skF_5')) | v1_xboole_0('#skF_5') | ~m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(u1_struct_0(A_97))) | v1_xboole_0(k2_struct_0('#skF_4')) | ~l1_struct_0(A_97) | v2_struct_0(A_97))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_331])).
% 4.76/1.84  tff(c_342, plain, (![A_100]: (v4_orders_2(k3_yellow19(A_100, k2_struct_0('#skF_4'), '#skF_5')) | ~m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(u1_struct_0(A_100))) | ~l1_struct_0(A_100) | v2_struct_0(A_100))), inference(negUnitSimplification, [status(thm)], [c_205, c_70, c_339])).
% 4.76/1.84  tff(c_348, plain, (v4_orders_2(k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5')) | ~m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_121, c_342])).
% 4.76/1.84  tff(c_351, plain, (v4_orders_2(k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5')) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_270, c_85, c_348])).
% 4.76/1.84  tff(c_352, plain, (v4_orders_2(k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_76, c_351])).
% 4.76/1.84  tff(c_402, plain, (![A_109, B_110, C_111]: (l1_waybel_0(k3_yellow19(A_109, B_110, C_111), A_109) | ~m1_subset_1(C_111, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_110)))) | ~v13_waybel_0(C_111, k3_yellow_1(B_110)) | ~v2_waybel_0(C_111, k3_yellow_1(B_110)) | v1_xboole_0(C_111) | ~m1_subset_1(B_110, k1_zfmisc_1(u1_struct_0(A_109))) | v1_xboole_0(B_110) | ~l1_struct_0(A_109) | v2_struct_0(A_109))), inference(cnfTransformation, [status(thm)], [f_116])).
% 4.76/1.84  tff(c_410, plain, (![A_109]: (l1_waybel_0(k3_yellow19(A_109, k2_struct_0('#skF_4'), '#skF_5'), A_109) | ~v13_waybel_0('#skF_5', k3_yellow_1(k2_struct_0('#skF_4'))) | ~v2_waybel_0('#skF_5', k3_yellow_1(k2_struct_0('#skF_4'))) | v1_xboole_0('#skF_5') | ~m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(u1_struct_0(A_109))) | v1_xboole_0(k2_struct_0('#skF_4')) | ~l1_struct_0(A_109) | v2_struct_0(A_109))), inference(resolution, [status(thm)], [c_62, c_402])).
% 4.76/1.84  tff(c_418, plain, (![A_109]: (l1_waybel_0(k3_yellow19(A_109, k2_struct_0('#skF_4'), '#skF_5'), A_109) | v1_xboole_0('#skF_5') | ~m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(u1_struct_0(A_109))) | v1_xboole_0(k2_struct_0('#skF_4')) | ~l1_struct_0(A_109) | v2_struct_0(A_109))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_410])).
% 4.76/1.84  tff(c_421, plain, (![A_112]: (l1_waybel_0(k3_yellow19(A_112, k2_struct_0('#skF_4'), '#skF_5'), A_112) | ~m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(u1_struct_0(A_112))) | ~l1_struct_0(A_112) | v2_struct_0(A_112))), inference(negUnitSimplification, [status(thm)], [c_205, c_70, c_418])).
% 4.76/1.84  tff(c_426, plain, (l1_waybel_0(k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5'), '#skF_4') | ~m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_121, c_421])).
% 4.76/1.84  tff(c_429, plain, (l1_waybel_0(k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5'), '#skF_4') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_270, c_85, c_426])).
% 4.76/1.84  tff(c_430, plain, (l1_waybel_0(k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_76, c_429])).
% 4.76/1.84  tff(c_68, plain, (v1_subset_1('#skF_5', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_242])).
% 4.76/1.84  tff(c_623, plain, (![A_139, B_140]: (k2_yellow19(A_139, k3_yellow19(A_139, k2_struct_0(A_139), B_140))=B_140 | ~m1_subset_1(B_140, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_139))))) | ~v13_waybel_0(B_140, k3_yellow_1(k2_struct_0(A_139))) | ~v2_waybel_0(B_140, k3_yellow_1(k2_struct_0(A_139))) | ~v1_subset_1(B_140, u1_struct_0(k3_yellow_1(k2_struct_0(A_139)))) | v1_xboole_0(B_140) | ~l1_struct_0(A_139) | v2_struct_0(A_139))), inference(cnfTransformation, [status(thm)], [f_215])).
% 4.76/1.84  tff(c_631, plain, (k2_yellow19('#skF_4', k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5'))='#skF_5' | ~v13_waybel_0('#skF_5', k3_yellow_1(k2_struct_0('#skF_4'))) | ~v2_waybel_0('#skF_5', k3_yellow_1(k2_struct_0('#skF_4'))) | ~v1_subset_1('#skF_5', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4')))) | v1_xboole_0('#skF_5') | ~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_62, c_623])).
% 4.76/1.84  tff(c_639, plain, (k2_yellow19('#skF_4', k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5'))='#skF_5' | v1_xboole_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_270, c_68, c_66, c_64, c_631])).
% 4.76/1.84  tff(c_640, plain, (k2_yellow19('#skF_4', k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5'))='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_76, c_70, c_639])).
% 4.76/1.84  tff(c_56, plain, (![A_30, B_34, C_36]: (r1_waybel_7(A_30, k2_yellow19(A_30, B_34), C_36) | ~r3_waybel_9(A_30, B_34, C_36) | ~m1_subset_1(C_36, u1_struct_0(A_30)) | ~l1_waybel_0(B_34, A_30) | ~v7_waybel_0(B_34) | ~v4_orders_2(B_34) | v2_struct_0(B_34) | ~l1_pre_topc(A_30) | ~v2_pre_topc(A_30) | v2_struct_0(A_30))), inference(cnfTransformation, [status(thm)], [f_196])).
% 4.76/1.84  tff(c_645, plain, (![C_36]: (r1_waybel_7('#skF_4', '#skF_5', C_36) | ~r3_waybel_9('#skF_4', k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5'), C_36) | ~m1_subset_1(C_36, u1_struct_0('#skF_4')) | ~l1_waybel_0(k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5'), '#skF_4') | ~v7_waybel_0(k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5')) | ~v4_orders_2(k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5')) | v2_struct_0(k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_640, c_56])).
% 4.76/1.84  tff(c_652, plain, (![C_36]: (r1_waybel_7('#skF_4', '#skF_5', C_36) | ~r3_waybel_9('#skF_4', k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5'), C_36) | ~m1_subset_1(C_36, k2_struct_0('#skF_4')) | ~v7_waybel_0(k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5')) | v2_struct_0(k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5')) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_352, c_430, c_121, c_645])).
% 4.76/1.84  tff(c_653, plain, (![C_36]: (r1_waybel_7('#skF_4', '#skF_5', C_36) | ~r3_waybel_9('#skF_4', k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5'), C_36) | ~m1_subset_1(C_36, k2_struct_0('#skF_4')) | ~v7_waybel_0(k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5')) | v2_struct_0(k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_76, c_652])).
% 4.76/1.84  tff(c_658, plain, (~v7_waybel_0(k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5'))), inference(splitLeft, [status(thm)], [c_653])).
% 4.76/1.84  tff(c_715, plain, (![A_151, B_152, C_153]: (v7_waybel_0(k3_yellow19(A_151, B_152, C_153)) | ~m1_subset_1(C_153, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_152)))) | ~v13_waybel_0(C_153, k3_yellow_1(B_152)) | ~v2_waybel_0(C_153, k3_yellow_1(B_152)) | ~v1_subset_1(C_153, u1_struct_0(k3_yellow_1(B_152))) | v1_xboole_0(C_153) | ~m1_subset_1(B_152, k1_zfmisc_1(u1_struct_0(A_151))) | v1_xboole_0(B_152) | ~l1_struct_0(A_151) | v2_struct_0(A_151))), inference(cnfTransformation, [status(thm)], [f_172])).
% 4.76/1.84  tff(c_723, plain, (![A_151]: (v7_waybel_0(k3_yellow19(A_151, k2_struct_0('#skF_4'), '#skF_5')) | ~v13_waybel_0('#skF_5', k3_yellow_1(k2_struct_0('#skF_4'))) | ~v2_waybel_0('#skF_5', k3_yellow_1(k2_struct_0('#skF_4'))) | ~v1_subset_1('#skF_5', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4')))) | v1_xboole_0('#skF_5') | ~m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(u1_struct_0(A_151))) | v1_xboole_0(k2_struct_0('#skF_4')) | ~l1_struct_0(A_151) | v2_struct_0(A_151))), inference(resolution, [status(thm)], [c_62, c_715])).
% 4.76/1.84  tff(c_731, plain, (![A_151]: (v7_waybel_0(k3_yellow19(A_151, k2_struct_0('#skF_4'), '#skF_5')) | v1_xboole_0('#skF_5') | ~m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(u1_struct_0(A_151))) | v1_xboole_0(k2_struct_0('#skF_4')) | ~l1_struct_0(A_151) | v2_struct_0(A_151))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_64, c_723])).
% 4.76/1.84  tff(c_734, plain, (![A_154]: (v7_waybel_0(k3_yellow19(A_154, k2_struct_0('#skF_4'), '#skF_5')) | ~m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(u1_struct_0(A_154))) | ~l1_struct_0(A_154) | v2_struct_0(A_154))), inference(negUnitSimplification, [status(thm)], [c_205, c_70, c_731])).
% 4.76/1.84  tff(c_740, plain, (v7_waybel_0(k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5')) | ~m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_121, c_734])).
% 4.76/1.84  tff(c_743, plain, (v7_waybel_0(k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5')) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_270, c_85, c_740])).
% 4.76/1.84  tff(c_745, plain, $false, inference(negUnitSimplification, [status(thm)], [c_76, c_658, c_743])).
% 4.76/1.84  tff(c_746, plain, (![C_36]: (v2_struct_0(k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5')) | r1_waybel_7('#skF_4', '#skF_5', C_36) | ~r3_waybel_9('#skF_4', k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5'), C_36) | ~m1_subset_1(C_36, k2_struct_0('#skF_4')))), inference(splitRight, [status(thm)], [c_653])).
% 4.76/1.84  tff(c_748, plain, (v2_struct_0(k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5'))), inference(splitLeft, [status(thm)], [c_746])).
% 4.76/1.84  tff(c_46, plain, (![A_24, B_25, C_26]: (~v2_struct_0(k3_yellow19(A_24, B_25, C_26)) | ~m1_subset_1(C_26, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_25)))) | ~v13_waybel_0(C_26, k3_yellow_1(B_25)) | ~v2_waybel_0(C_26, k3_yellow_1(B_25)) | v1_xboole_0(C_26) | ~m1_subset_1(B_25, k1_zfmisc_1(u1_struct_0(A_24))) | v1_xboole_0(B_25) | ~l1_struct_0(A_24) | v2_struct_0(A_24))), inference(cnfTransformation, [status(thm)], [f_144])).
% 4.76/1.84  tff(c_753, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4'))))) | ~v13_waybel_0('#skF_5', k3_yellow_1(k2_struct_0('#skF_4'))) | ~v2_waybel_0('#skF_5', k3_yellow_1(k2_struct_0('#skF_4'))) | v1_xboole_0('#skF_5') | ~m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | v1_xboole_0(k2_struct_0('#skF_4')) | ~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_748, c_46])).
% 4.76/1.84  tff(c_756, plain, (v1_xboole_0('#skF_5') | v1_xboole_0(k2_struct_0('#skF_4')) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_270, c_85, c_121, c_66, c_64, c_62, c_753])).
% 4.76/1.84  tff(c_758, plain, $false, inference(negUnitSimplification, [status(thm)], [c_76, c_205, c_70, c_756])).
% 4.76/1.84  tff(c_760, plain, (~v2_struct_0(k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5'))), inference(splitRight, [status(thm)], [c_746])).
% 4.76/1.84  tff(c_747, plain, (v7_waybel_0(k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5'))), inference(splitRight, [status(thm)], [c_653])).
% 4.76/1.84  tff(c_54, plain, (![A_30, B_34, C_36]: (r3_waybel_9(A_30, B_34, C_36) | ~r1_waybel_7(A_30, k2_yellow19(A_30, B_34), C_36) | ~m1_subset_1(C_36, u1_struct_0(A_30)) | ~l1_waybel_0(B_34, A_30) | ~v7_waybel_0(B_34) | ~v4_orders_2(B_34) | v2_struct_0(B_34) | ~l1_pre_topc(A_30) | ~v2_pre_topc(A_30) | v2_struct_0(A_30))), inference(cnfTransformation, [status(thm)], [f_196])).
% 4.76/1.84  tff(c_648, plain, (![C_36]: (r3_waybel_9('#skF_4', k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5'), C_36) | ~r1_waybel_7('#skF_4', '#skF_5', C_36) | ~m1_subset_1(C_36, u1_struct_0('#skF_4')) | ~l1_waybel_0(k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5'), '#skF_4') | ~v7_waybel_0(k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5')) | ~v4_orders_2(k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5')) | v2_struct_0(k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_640, c_54])).
% 4.76/1.84  tff(c_655, plain, (![C_36]: (r3_waybel_9('#skF_4', k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5'), C_36) | ~r1_waybel_7('#skF_4', '#skF_5', C_36) | ~m1_subset_1(C_36, k2_struct_0('#skF_4')) | ~v7_waybel_0(k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5')) | v2_struct_0(k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5')) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_352, c_430, c_121, c_648])).
% 4.76/1.84  tff(c_656, plain, (![C_36]: (r3_waybel_9('#skF_4', k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5'), C_36) | ~r1_waybel_7('#skF_4', '#skF_5', C_36) | ~m1_subset_1(C_36, k2_struct_0('#skF_4')) | ~v7_waybel_0(k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5')) | v2_struct_0(k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_76, c_655])).
% 4.76/1.84  tff(c_763, plain, (![C_36]: (r3_waybel_9('#skF_4', k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5'), C_36) | ~r1_waybel_7('#skF_4', '#skF_5', C_36) | ~m1_subset_1(C_36, k2_struct_0('#skF_4')) | v2_struct_0(k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_747, c_656])).
% 4.76/1.84  tff(c_765, plain, (![C_156]: (r3_waybel_9('#skF_4', k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5'), C_156) | ~r1_waybel_7('#skF_4', '#skF_5', C_156) | ~m1_subset_1(C_156, k2_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_760, c_763])).
% 4.76/1.84  tff(c_78, plain, (~r1_waybel_7('#skF_4', '#skF_5', '#skF_6') | ~r3_waybel_9('#skF_4', k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_242])).
% 4.76/1.84  tff(c_160, plain, (~r3_waybel_9('#skF_4', k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_127, c_78])).
% 4.76/1.84  tff(c_771, plain, (~r1_waybel_7('#skF_4', '#skF_5', '#skF_6') | ~m1_subset_1('#skF_6', k2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_765, c_160])).
% 4.76/1.84  tff(c_776, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_122, c_127, c_771])).
% 4.76/1.84  tff(c_777, plain, (v1_xboole_0('#skF_3'('#skF_4'))), inference(splitRight, [status(thm)], [c_204])).
% 4.76/1.84  tff(c_28, plain, (![A_18]: (~v1_xboole_0('#skF_3'(A_18)) | ~l1_pre_topc(A_18) | ~v2_pre_topc(A_18) | v2_struct_0(A_18))), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.76/1.84  tff(c_781, plain, (~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_777, c_28])).
% 4.76/1.84  tff(c_784, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_781])).
% 4.76/1.84  tff(c_786, plain, $false, inference(negUnitSimplification, [status(thm)], [c_76, c_784])).
% 4.76/1.84  tff(c_788, plain, (~r1_waybel_7('#skF_4', '#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_84])).
% 4.76/1.84  tff(c_787, plain, (r3_waybel_9('#skF_4', k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5'), '#skF_6')), inference(splitRight, [status(thm)], [c_84])).
% 4.76/1.84  tff(c_845, plain, (![A_179]: (m1_subset_1('#skF_3'(A_179), k1_zfmisc_1(u1_struct_0(A_179))) | ~l1_pre_topc(A_179) | ~v2_pre_topc(A_179) | v2_struct_0(A_179))), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.76/1.84  tff(c_851, plain, (m1_subset_1('#skF_3'('#skF_4'), k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_121, c_845])).
% 4.76/1.84  tff(c_854, plain, (m1_subset_1('#skF_3'('#skF_4'), k1_zfmisc_1(k2_struct_0('#skF_4'))) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_851])).
% 4.76/1.84  tff(c_855, plain, (m1_subset_1('#skF_3'('#skF_4'), k1_zfmisc_1(k2_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_76, c_854])).
% 4.76/1.84  tff(c_859, plain, (r1_tarski('#skF_3'('#skF_4'), k2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_855, c_18])).
% 4.76/1.84  tff(c_804, plain, (![A_162, B_163]: (r2_hidden('#skF_2'(A_162, B_163), B_163) | r1_xboole_0(A_162, B_163))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.76/1.84  tff(c_808, plain, (![B_163, A_162]: (~v1_xboole_0(B_163) | r1_xboole_0(A_162, B_163))), inference(resolution, [status(thm)], [c_804, c_2])).
% 4.76/1.84  tff(c_810, plain, (![B_166, A_167]: (~r1_xboole_0(B_166, A_167) | ~r1_tarski(B_166, A_167) | v1_xboole_0(B_166))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.76/1.84  tff(c_814, plain, (![A_162, B_163]: (~r1_tarski(A_162, B_163) | v1_xboole_0(A_162) | ~v1_xboole_0(B_163))), inference(resolution, [status(thm)], [c_808, c_810])).
% 4.76/1.84  tff(c_863, plain, (v1_xboole_0('#skF_3'('#skF_4')) | ~v1_xboole_0(k2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_859, c_814])).
% 4.76/1.84  tff(c_865, plain, (~v1_xboole_0(k2_struct_0('#skF_4'))), inference(splitLeft, [status(thm)], [c_863])).
% 4.76/1.84  tff(c_889, plain, (![A_188, B_189, C_190]: (v4_orders_2(k3_yellow19(A_188, B_189, C_190)) | ~m1_subset_1(C_190, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_189)))) | ~v13_waybel_0(C_190, k3_yellow_1(B_189)) | ~v2_waybel_0(C_190, k3_yellow_1(B_189)) | v1_xboole_0(C_190) | ~m1_subset_1(B_189, k1_zfmisc_1(u1_struct_0(A_188))) | v1_xboole_0(B_189) | ~l1_struct_0(A_188) | v2_struct_0(A_188))), inference(cnfTransformation, [status(thm)], [f_144])).
% 4.76/1.84  tff(c_897, plain, (![A_188]: (v4_orders_2(k3_yellow19(A_188, k2_struct_0('#skF_4'), '#skF_5')) | ~v13_waybel_0('#skF_5', k3_yellow_1(k2_struct_0('#skF_4'))) | ~v2_waybel_0('#skF_5', k3_yellow_1(k2_struct_0('#skF_4'))) | v1_xboole_0('#skF_5') | ~m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(u1_struct_0(A_188))) | v1_xboole_0(k2_struct_0('#skF_4')) | ~l1_struct_0(A_188) | v2_struct_0(A_188))), inference(resolution, [status(thm)], [c_62, c_889])).
% 4.76/1.84  tff(c_905, plain, (![A_188]: (v4_orders_2(k3_yellow19(A_188, k2_struct_0('#skF_4'), '#skF_5')) | v1_xboole_0('#skF_5') | ~m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(u1_struct_0(A_188))) | v1_xboole_0(k2_struct_0('#skF_4')) | ~l1_struct_0(A_188) | v2_struct_0(A_188))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_897])).
% 4.76/1.84  tff(c_908, plain, (![A_191]: (v4_orders_2(k3_yellow19(A_191, k2_struct_0('#skF_4'), '#skF_5')) | ~m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(u1_struct_0(A_191))) | ~l1_struct_0(A_191) | v2_struct_0(A_191))), inference(negUnitSimplification, [status(thm)], [c_865, c_70, c_905])).
% 4.76/1.84  tff(c_914, plain, (v4_orders_2(k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5')) | ~m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_121, c_908])).
% 4.76/1.84  tff(c_917, plain, (v4_orders_2(k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5')) | ~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_85, c_914])).
% 4.76/1.84  tff(c_918, plain, (v4_orders_2(k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5')) | ~l1_struct_0('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_76, c_917])).
% 4.76/1.84  tff(c_919, plain, (~l1_struct_0('#skF_4')), inference(splitLeft, [status(thm)], [c_918])).
% 4.76/1.84  tff(c_922, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_24, c_919])).
% 4.76/1.84  tff(c_926, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_72, c_922])).
% 4.76/1.84  tff(c_928, plain, (l1_struct_0('#skF_4')), inference(splitRight, [status(thm)], [c_918])).
% 4.76/1.84  tff(c_927, plain, (v4_orders_2(k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5'))), inference(splitRight, [status(thm)], [c_918])).
% 4.76/1.84  tff(c_1214, plain, (![A_233, B_234, C_235]: (l1_waybel_0(k3_yellow19(A_233, B_234, C_235), A_233) | ~m1_subset_1(C_235, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_234)))) | ~v13_waybel_0(C_235, k3_yellow_1(B_234)) | ~v2_waybel_0(C_235, k3_yellow_1(B_234)) | v1_xboole_0(C_235) | ~m1_subset_1(B_234, k1_zfmisc_1(u1_struct_0(A_233))) | v1_xboole_0(B_234) | ~l1_struct_0(A_233) | v2_struct_0(A_233))), inference(cnfTransformation, [status(thm)], [f_116])).
% 4.76/1.84  tff(c_1222, plain, (![A_233]: (l1_waybel_0(k3_yellow19(A_233, k2_struct_0('#skF_4'), '#skF_5'), A_233) | ~v13_waybel_0('#skF_5', k3_yellow_1(k2_struct_0('#skF_4'))) | ~v2_waybel_0('#skF_5', k3_yellow_1(k2_struct_0('#skF_4'))) | v1_xboole_0('#skF_5') | ~m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(u1_struct_0(A_233))) | v1_xboole_0(k2_struct_0('#skF_4')) | ~l1_struct_0(A_233) | v2_struct_0(A_233))), inference(resolution, [status(thm)], [c_62, c_1214])).
% 4.76/1.84  tff(c_1230, plain, (![A_233]: (l1_waybel_0(k3_yellow19(A_233, k2_struct_0('#skF_4'), '#skF_5'), A_233) | v1_xboole_0('#skF_5') | ~m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(u1_struct_0(A_233))) | v1_xboole_0(k2_struct_0('#skF_4')) | ~l1_struct_0(A_233) | v2_struct_0(A_233))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_1222])).
% 4.76/1.84  tff(c_1233, plain, (![A_236]: (l1_waybel_0(k3_yellow19(A_236, k2_struct_0('#skF_4'), '#skF_5'), A_236) | ~m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(u1_struct_0(A_236))) | ~l1_struct_0(A_236) | v2_struct_0(A_236))), inference(negUnitSimplification, [status(thm)], [c_865, c_70, c_1230])).
% 4.76/1.84  tff(c_1238, plain, (l1_waybel_0(k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5'), '#skF_4') | ~m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_121, c_1233])).
% 4.76/1.84  tff(c_1241, plain, (l1_waybel_0(k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5'), '#skF_4') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_928, c_85, c_1238])).
% 4.76/1.84  tff(c_1242, plain, (l1_waybel_0(k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_76, c_1241])).
% 4.76/1.84  tff(c_1337, plain, (![A_252, B_253]: (k2_yellow19(A_252, k3_yellow19(A_252, k2_struct_0(A_252), B_253))=B_253 | ~m1_subset_1(B_253, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_252))))) | ~v13_waybel_0(B_253, k3_yellow_1(k2_struct_0(A_252))) | ~v2_waybel_0(B_253, k3_yellow_1(k2_struct_0(A_252))) | ~v1_subset_1(B_253, u1_struct_0(k3_yellow_1(k2_struct_0(A_252)))) | v1_xboole_0(B_253) | ~l1_struct_0(A_252) | v2_struct_0(A_252))), inference(cnfTransformation, [status(thm)], [f_215])).
% 4.76/1.84  tff(c_1345, plain, (k2_yellow19('#skF_4', k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5'))='#skF_5' | ~v13_waybel_0('#skF_5', k3_yellow_1(k2_struct_0('#skF_4'))) | ~v2_waybel_0('#skF_5', k3_yellow_1(k2_struct_0('#skF_4'))) | ~v1_subset_1('#skF_5', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4')))) | v1_xboole_0('#skF_5') | ~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_62, c_1337])).
% 4.76/1.84  tff(c_1353, plain, (k2_yellow19('#skF_4', k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5'))='#skF_5' | v1_xboole_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_928, c_68, c_66, c_64, c_1345])).
% 4.76/1.84  tff(c_1354, plain, (k2_yellow19('#skF_4', k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5'))='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_76, c_70, c_1353])).
% 4.76/1.84  tff(c_1359, plain, (![C_36]: (r3_waybel_9('#skF_4', k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5'), C_36) | ~r1_waybel_7('#skF_4', '#skF_5', C_36) | ~m1_subset_1(C_36, u1_struct_0('#skF_4')) | ~l1_waybel_0(k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5'), '#skF_4') | ~v7_waybel_0(k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5')) | ~v4_orders_2(k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5')) | v2_struct_0(k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1354, c_54])).
% 4.76/1.84  tff(c_1366, plain, (![C_36]: (r3_waybel_9('#skF_4', k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5'), C_36) | ~r1_waybel_7('#skF_4', '#skF_5', C_36) | ~m1_subset_1(C_36, k2_struct_0('#skF_4')) | ~v7_waybel_0(k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5')) | v2_struct_0(k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5')) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_927, c_1242, c_121, c_1359])).
% 4.76/1.84  tff(c_1367, plain, (![C_36]: (r3_waybel_9('#skF_4', k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5'), C_36) | ~r1_waybel_7('#skF_4', '#skF_5', C_36) | ~m1_subset_1(C_36, k2_struct_0('#skF_4')) | ~v7_waybel_0(k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5')) | v2_struct_0(k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_76, c_1366])).
% 4.76/1.84  tff(c_1372, plain, (~v7_waybel_0(k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5'))), inference(splitLeft, [status(thm)], [c_1367])).
% 4.76/1.84  tff(c_1440, plain, (![A_261, B_262, C_263]: (v7_waybel_0(k3_yellow19(A_261, B_262, C_263)) | ~m1_subset_1(C_263, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_262)))) | ~v13_waybel_0(C_263, k3_yellow_1(B_262)) | ~v2_waybel_0(C_263, k3_yellow_1(B_262)) | ~v1_subset_1(C_263, u1_struct_0(k3_yellow_1(B_262))) | v1_xboole_0(C_263) | ~m1_subset_1(B_262, k1_zfmisc_1(u1_struct_0(A_261))) | v1_xboole_0(B_262) | ~l1_struct_0(A_261) | v2_struct_0(A_261))), inference(cnfTransformation, [status(thm)], [f_172])).
% 4.76/1.84  tff(c_1448, plain, (![A_261]: (v7_waybel_0(k3_yellow19(A_261, k2_struct_0('#skF_4'), '#skF_5')) | ~v13_waybel_0('#skF_5', k3_yellow_1(k2_struct_0('#skF_4'))) | ~v2_waybel_0('#skF_5', k3_yellow_1(k2_struct_0('#skF_4'))) | ~v1_subset_1('#skF_5', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4')))) | v1_xboole_0('#skF_5') | ~m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(u1_struct_0(A_261))) | v1_xboole_0(k2_struct_0('#skF_4')) | ~l1_struct_0(A_261) | v2_struct_0(A_261))), inference(resolution, [status(thm)], [c_62, c_1440])).
% 4.76/1.84  tff(c_1456, plain, (![A_261]: (v7_waybel_0(k3_yellow19(A_261, k2_struct_0('#skF_4'), '#skF_5')) | v1_xboole_0('#skF_5') | ~m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(u1_struct_0(A_261))) | v1_xboole_0(k2_struct_0('#skF_4')) | ~l1_struct_0(A_261) | v2_struct_0(A_261))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_64, c_1448])).
% 4.76/1.84  tff(c_1459, plain, (![A_264]: (v7_waybel_0(k3_yellow19(A_264, k2_struct_0('#skF_4'), '#skF_5')) | ~m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(u1_struct_0(A_264))) | ~l1_struct_0(A_264) | v2_struct_0(A_264))), inference(negUnitSimplification, [status(thm)], [c_865, c_70, c_1456])).
% 4.76/1.84  tff(c_1465, plain, (v7_waybel_0(k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5')) | ~m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_121, c_1459])).
% 4.76/1.84  tff(c_1468, plain, (v7_waybel_0(k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5')) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_928, c_85, c_1465])).
% 4.76/1.84  tff(c_1470, plain, $false, inference(negUnitSimplification, [status(thm)], [c_76, c_1372, c_1468])).
% 4.76/1.84  tff(c_1471, plain, (![C_36]: (v2_struct_0(k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5')) | r3_waybel_9('#skF_4', k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5'), C_36) | ~r1_waybel_7('#skF_4', '#skF_5', C_36) | ~m1_subset_1(C_36, k2_struct_0('#skF_4')))), inference(splitRight, [status(thm)], [c_1367])).
% 4.76/1.84  tff(c_1473, plain, (v2_struct_0(k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5'))), inference(splitLeft, [status(thm)], [c_1471])).
% 4.76/1.84  tff(c_1478, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4'))))) | ~v13_waybel_0('#skF_5', k3_yellow_1(k2_struct_0('#skF_4'))) | ~v2_waybel_0('#skF_5', k3_yellow_1(k2_struct_0('#skF_4'))) | v1_xboole_0('#skF_5') | ~m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | v1_xboole_0(k2_struct_0('#skF_4')) | ~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_1473, c_46])).
% 4.76/1.84  tff(c_1481, plain, (v1_xboole_0('#skF_5') | v1_xboole_0(k2_struct_0('#skF_4')) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_928, c_85, c_121, c_66, c_64, c_62, c_1478])).
% 4.76/1.84  tff(c_1483, plain, $false, inference(negUnitSimplification, [status(thm)], [c_76, c_865, c_70, c_1481])).
% 4.76/1.84  tff(c_1485, plain, (~v2_struct_0(k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5'))), inference(splitRight, [status(thm)], [c_1471])).
% 4.76/1.84  tff(c_1472, plain, (v7_waybel_0(k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5'))), inference(splitRight, [status(thm)], [c_1367])).
% 4.76/1.84  tff(c_1362, plain, (![C_36]: (r1_waybel_7('#skF_4', '#skF_5', C_36) | ~r3_waybel_9('#skF_4', k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5'), C_36) | ~m1_subset_1(C_36, u1_struct_0('#skF_4')) | ~l1_waybel_0(k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5'), '#skF_4') | ~v7_waybel_0(k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5')) | ~v4_orders_2(k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5')) | v2_struct_0(k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1354, c_56])).
% 4.76/1.84  tff(c_1369, plain, (![C_36]: (r1_waybel_7('#skF_4', '#skF_5', C_36) | ~r3_waybel_9('#skF_4', k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5'), C_36) | ~m1_subset_1(C_36, k2_struct_0('#skF_4')) | ~v7_waybel_0(k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5')) | v2_struct_0(k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5')) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_927, c_1242, c_121, c_1362])).
% 4.76/1.84  tff(c_1370, plain, (![C_36]: (r1_waybel_7('#skF_4', '#skF_5', C_36) | ~r3_waybel_9('#skF_4', k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5'), C_36) | ~m1_subset_1(C_36, k2_struct_0('#skF_4')) | ~v7_waybel_0(k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5')) | v2_struct_0(k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_76, c_1369])).
% 4.76/1.84  tff(c_1488, plain, (![C_36]: (r1_waybel_7('#skF_4', '#skF_5', C_36) | ~r3_waybel_9('#skF_4', k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5'), C_36) | ~m1_subset_1(C_36, k2_struct_0('#skF_4')) | v2_struct_0(k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_1472, c_1370])).
% 4.76/1.84  tff(c_1490, plain, (![C_266]: (r1_waybel_7('#skF_4', '#skF_5', C_266) | ~r3_waybel_9('#skF_4', k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5'), C_266) | ~m1_subset_1(C_266, k2_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_1485, c_1488])).
% 4.76/1.84  tff(c_1496, plain, (r1_waybel_7('#skF_4', '#skF_5', '#skF_6') | ~m1_subset_1('#skF_6', k2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_787, c_1490])).
% 4.76/1.84  tff(c_1500, plain, (r1_waybel_7('#skF_4', '#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_122, c_1496])).
% 4.76/1.84  tff(c_1502, plain, $false, inference(negUnitSimplification, [status(thm)], [c_788, c_1500])).
% 4.76/1.84  tff(c_1503, plain, (v1_xboole_0('#skF_3'('#skF_4'))), inference(splitRight, [status(thm)], [c_863])).
% 4.76/1.84  tff(c_1507, plain, (~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_1503, c_28])).
% 4.76/1.84  tff(c_1510, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_1507])).
% 4.76/1.84  tff(c_1512, plain, $false, inference(negUnitSimplification, [status(thm)], [c_76, c_1510])).
% 4.76/1.84  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.76/1.84  
% 4.76/1.84  Inference rules
% 4.76/1.84  ----------------------
% 4.76/1.84  #Ref     : 0
% 4.76/1.84  #Sup     : 267
% 4.76/1.84  #Fact    : 0
% 4.76/1.84  #Define  : 0
% 4.76/1.84  #Split   : 15
% 4.76/1.84  #Chain   : 0
% 4.76/1.84  #Close   : 0
% 4.76/1.84  
% 4.76/1.84  Ordering : KBO
% 4.76/1.84  
% 4.76/1.84  Simplification rules
% 4.76/1.84  ----------------------
% 4.76/1.84  #Subsume      : 37
% 4.76/1.84  #Demod        : 234
% 4.76/1.84  #Tautology    : 47
% 4.76/1.84  #SimpNegUnit  : 97
% 4.76/1.84  #BackRed      : 1
% 4.76/1.84  
% 4.76/1.84  #Partial instantiations: 0
% 4.76/1.84  #Strategies tried      : 1
% 4.76/1.84  
% 4.76/1.84  Timing (in seconds)
% 4.76/1.84  ----------------------
% 4.76/1.85  Preprocessing        : 0.39
% 4.76/1.85  Parsing              : 0.22
% 4.76/1.85  CNF conversion       : 0.03
% 4.76/1.85  Main loop            : 0.62
% 4.76/1.85  Inferencing          : 0.23
% 4.76/1.85  Reduction            : 0.20
% 4.76/1.85  Demodulation         : 0.14
% 4.76/1.85  BG Simplification    : 0.03
% 4.76/1.85  Subsumption          : 0.12
% 4.76/1.85  Abstraction          : 0.03
% 4.76/1.85  MUC search           : 0.00
% 4.76/1.85  Cooper               : 0.00
% 4.76/1.85  Total                : 1.09
% 4.76/1.85  Index Insertion      : 0.00
% 4.76/1.85  Index Deletion       : 0.00
% 4.76/1.85  Index Matching       : 0.00
% 4.76/1.85  BG Taut test         : 0.00
%------------------------------------------------------------------------------
