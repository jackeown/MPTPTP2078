%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:34 EST 2020

% Result     : Theorem 3.57s
% Output     : CNFRefutation 3.57s
% Verified   : 
% Statistics : Number of formulae       :  184 (2798 expanded)
%              Number of leaves         :   47 ( 980 expanded)
%              Depth                    :   21
%              Number of atoms          :  574 (9950 expanded)
%              Number of equality atoms :   35 (1286 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_waybel_9 > r1_waybel_7 > v6_waybel_0 > v2_waybel_0 > v1_tops_1 > v1_subset_1 > v13_waybel_0 > m1_subset_1 > l1_waybel_0 > v7_waybel_0 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k3_yellow19 > k2_yellow19 > k2_pre_topc > #nlpp > u1_struct_0 > k3_yellow_1 > k3_lattice3 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_lattice3 > #skF_2 > #skF_3 > #skF_1

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

tff(v1_tops_1,type,(
    v1_tops_1: ( $i * $i ) > $o )).

tff(r3_waybel_9,type,(
    r3_waybel_9: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_221,negated_conjecture,(
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

tff(f_37,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_58,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => k2_pre_topc(A,k2_struct_0(A)) = k2_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_tops_1)).

tff(f_33,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => m1_subset_1(k2_struct_0(A),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_struct_0)).

tff(f_54,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_tops_1(B,A)
          <=> k2_pre_topc(A,B) = k2_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tops_1)).

tff(f_69,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_tops_1(B,A)
          <=> k2_pre_topc(A,B) = u1_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tops_3)).

tff(f_45,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_27,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_29,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_151,axiom,(
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

tff(f_123,axiom,(
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

tff(f_95,axiom,(
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

tff(f_194,axiom,(
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

tff(f_175,axiom,(
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

tff(c_62,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_8,plain,(
    ! [A_4] :
      ( l1_struct_0(A_4)
      | ~ l1_pre_topc(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_16,plain,(
    ! [A_9] :
      ( k2_pre_topc(A_9,k2_struct_0(A_9)) = k2_struct_0(A_9)
      | ~ l1_pre_topc(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_6,plain,(
    ! [A_3] :
      ( m1_subset_1(k2_struct_0(A_3),k1_zfmisc_1(u1_struct_0(A_3)))
      | ~ l1_struct_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_155,plain,(
    ! [B_53,A_54] :
      ( v1_tops_1(B_53,A_54)
      | k2_pre_topc(A_54,B_53) != k2_struct_0(A_54)
      | ~ m1_subset_1(B_53,k1_zfmisc_1(u1_struct_0(A_54)))
      | ~ l1_pre_topc(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_193,plain,(
    ! [A_58] :
      ( v1_tops_1(k2_struct_0(A_58),A_58)
      | k2_pre_topc(A_58,k2_struct_0(A_58)) != k2_struct_0(A_58)
      | ~ l1_pre_topc(A_58)
      | ~ l1_struct_0(A_58) ) ),
    inference(resolution,[status(thm)],[c_6,c_155])).

tff(c_110,plain,(
    ! [A_44,B_45] :
      ( k2_pre_topc(A_44,B_45) = u1_struct_0(A_44)
      | ~ v1_tops_1(B_45,A_44)
      | ~ m1_subset_1(B_45,k1_zfmisc_1(u1_struct_0(A_44)))
      | ~ l1_pre_topc(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_121,plain,(
    ! [A_3] :
      ( k2_pre_topc(A_3,k2_struct_0(A_3)) = u1_struct_0(A_3)
      | ~ v1_tops_1(k2_struct_0(A_3),A_3)
      | ~ l1_pre_topc(A_3)
      | ~ l1_struct_0(A_3) ) ),
    inference(resolution,[status(thm)],[c_6,c_110])).

tff(c_200,plain,(
    ! [A_61] :
      ( k2_pre_topc(A_61,k2_struct_0(A_61)) = u1_struct_0(A_61)
      | k2_pre_topc(A_61,k2_struct_0(A_61)) != k2_struct_0(A_61)
      | ~ l1_pre_topc(A_61)
      | ~ l1_struct_0(A_61) ) ),
    inference(resolution,[status(thm)],[c_193,c_121])).

tff(c_206,plain,(
    ! [A_65] :
      ( k2_pre_topc(A_65,k2_struct_0(A_65)) = u1_struct_0(A_65)
      | ~ l1_struct_0(A_65)
      | ~ l1_pre_topc(A_65) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_200])).

tff(c_221,plain,(
    ! [A_66] :
      ( u1_struct_0(A_66) = k2_struct_0(A_66)
      | ~ l1_pre_topc(A_66)
      | ~ l1_struct_0(A_66)
      | ~ l1_pre_topc(A_66) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_206,c_16])).

tff(c_226,plain,(
    ! [A_67] :
      ( u1_struct_0(A_67) = k2_struct_0(A_67)
      | ~ l1_pre_topc(A_67) ) ),
    inference(resolution,[status(thm)],[c_8,c_221])).

tff(c_230,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_62,c_226])).

tff(c_50,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_231,plain,(
    m1_subset_1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_230,c_50])).

tff(c_74,plain,
    ( r3_waybel_9('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),'#skF_3')
    | r1_waybel_7('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_107,plain,(
    r1_waybel_7('#skF_1','#skF_2','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_74])).

tff(c_66,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_10,plain,(
    ! [A_5] :
      ( ~ v1_xboole_0(u1_struct_0(A_5))
      | ~ l1_struct_0(A_5)
      | v2_struct_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_268,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_1'))
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_230,c_10])).

tff(c_292,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_1'))
    | ~ l1_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_268])).

tff(c_294,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_292])).

tff(c_297,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_8,c_294])).

tff(c_301,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_297])).

tff(c_302,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_292])).

tff(c_60,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_303,plain,(
    l1_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_292])).

tff(c_2,plain,(
    ! [A_1] : k2_subset_1(A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_2] : m1_subset_1(k2_subset_1(A_2),k1_zfmisc_1(A_2)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_75,plain,(
    ! [A_2] : m1_subset_1(A_2,k1_zfmisc_1(A_2)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_4])).

tff(c_56,plain,(
    v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_54,plain,(
    v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_52,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1'))))) ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_58,plain,(
    v1_subset_1('#skF_2',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_506,plain,(
    ! [A_100,B_101,C_102] :
      ( v7_waybel_0(k3_yellow19(A_100,B_101,C_102))
      | ~ m1_subset_1(C_102,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_101))))
      | ~ v13_waybel_0(C_102,k3_yellow_1(B_101))
      | ~ v2_waybel_0(C_102,k3_yellow_1(B_101))
      | ~ v1_subset_1(C_102,u1_struct_0(k3_yellow_1(B_101)))
      | v1_xboole_0(C_102)
      | ~ m1_subset_1(B_101,k1_zfmisc_1(u1_struct_0(A_100)))
      | v1_xboole_0(B_101)
      | ~ l1_struct_0(A_100)
      | v2_struct_0(A_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_511,plain,(
    ! [A_100] :
      ( v7_waybel_0(k3_yellow19(A_100,k2_struct_0('#skF_1'),'#skF_2'))
      | ~ v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
      | ~ v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
      | ~ v1_subset_1('#skF_2',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1'))))
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_100)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_100)
      | v2_struct_0(A_100) ) ),
    inference(resolution,[status(thm)],[c_52,c_506])).

tff(c_518,plain,(
    ! [A_100] :
      ( v7_waybel_0(k3_yellow19(A_100,k2_struct_0('#skF_1'),'#skF_2'))
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_100)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_100)
      | v2_struct_0(A_100) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_511])).

tff(c_552,plain,(
    ! [A_105] :
      ( v7_waybel_0(k3_yellow19(A_105,k2_struct_0('#skF_1'),'#skF_2'))
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_105)))
      | ~ l1_struct_0(A_105)
      | v2_struct_0(A_105) ) ),
    inference(negUnitSimplification,[status(thm)],[c_302,c_60,c_518])).

tff(c_555,plain,
    ( v7_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
    | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1')))
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_230,c_552])).

tff(c_561,plain,
    ( v7_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_303,c_75,c_555])).

tff(c_562,plain,(
    v7_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_561])).

tff(c_64,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_412,plain,(
    ! [A_77,B_78,C_79] :
      ( v4_orders_2(k3_yellow19(A_77,B_78,C_79))
      | ~ m1_subset_1(C_79,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_78))))
      | ~ v13_waybel_0(C_79,k3_yellow_1(B_78))
      | ~ v2_waybel_0(C_79,k3_yellow_1(B_78))
      | v1_xboole_0(C_79)
      | ~ m1_subset_1(B_78,k1_zfmisc_1(u1_struct_0(A_77)))
      | v1_xboole_0(B_78)
      | ~ l1_struct_0(A_77)
      | v2_struct_0(A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_417,plain,(
    ! [A_77] :
      ( v4_orders_2(k3_yellow19(A_77,k2_struct_0('#skF_1'),'#skF_2'))
      | ~ v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
      | ~ v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_77)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_77)
      | v2_struct_0(A_77) ) ),
    inference(resolution,[status(thm)],[c_52,c_412])).

tff(c_424,plain,(
    ! [A_77] :
      ( v4_orders_2(k3_yellow19(A_77,k2_struct_0('#skF_1'),'#skF_2'))
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_77)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_77)
      | v2_struct_0(A_77) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_417])).

tff(c_427,plain,(
    ! [A_80] :
      ( v4_orders_2(k3_yellow19(A_80,k2_struct_0('#skF_1'),'#skF_2'))
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_80)))
      | ~ l1_struct_0(A_80)
      | v2_struct_0(A_80) ) ),
    inference(negUnitSimplification,[status(thm)],[c_302,c_60,c_424])).

tff(c_430,plain,
    ( v4_orders_2(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
    | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1')))
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_230,c_427])).

tff(c_436,plain,
    ( v4_orders_2(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_303,c_75,c_430])).

tff(c_437,plain,(
    v4_orders_2(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_436])).

tff(c_472,plain,(
    ! [A_88,B_89,C_90] :
      ( l1_waybel_0(k3_yellow19(A_88,B_89,C_90),A_88)
      | ~ m1_subset_1(C_90,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_89))))
      | ~ v13_waybel_0(C_90,k3_yellow_1(B_89))
      | ~ v2_waybel_0(C_90,k3_yellow_1(B_89))
      | v1_xboole_0(C_90)
      | ~ m1_subset_1(B_89,k1_zfmisc_1(u1_struct_0(A_88)))
      | v1_xboole_0(B_89)
      | ~ l1_struct_0(A_88)
      | v2_struct_0(A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_477,plain,(
    ! [A_88] :
      ( l1_waybel_0(k3_yellow19(A_88,k2_struct_0('#skF_1'),'#skF_2'),A_88)
      | ~ v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
      | ~ v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_88)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_88)
      | v2_struct_0(A_88) ) ),
    inference(resolution,[status(thm)],[c_52,c_472])).

tff(c_484,plain,(
    ! [A_88] :
      ( l1_waybel_0(k3_yellow19(A_88,k2_struct_0('#skF_1'),'#skF_2'),A_88)
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_88)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_88)
      | v2_struct_0(A_88) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_477])).

tff(c_488,plain,(
    ! [A_91] :
      ( l1_waybel_0(k3_yellow19(A_91,k2_struct_0('#skF_1'),'#skF_2'),A_91)
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_91)))
      | ~ l1_struct_0(A_91)
      | v2_struct_0(A_91) ) ),
    inference(negUnitSimplification,[status(thm)],[c_302,c_60,c_484])).

tff(c_490,plain,
    ( l1_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1')))
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_230,c_488])).

tff(c_495,plain,
    ( l1_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_303,c_75,c_490])).

tff(c_496,plain,(
    l1_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_495])).

tff(c_521,plain,(
    ! [A_103,B_104] :
      ( k2_yellow19(A_103,k3_yellow19(A_103,k2_struct_0(A_103),B_104)) = B_104
      | ~ m1_subset_1(B_104,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_103)))))
      | ~ v13_waybel_0(B_104,k3_yellow_1(k2_struct_0(A_103)))
      | ~ v2_waybel_0(B_104,k3_yellow_1(k2_struct_0(A_103)))
      | ~ v1_subset_1(B_104,u1_struct_0(k3_yellow_1(k2_struct_0(A_103))))
      | v1_xboole_0(B_104)
      | ~ l1_struct_0(A_103)
      | v2_struct_0(A_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_526,plain,
    ( k2_yellow19('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) = '#skF_2'
    | ~ v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
    | ~ v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
    | ~ v1_subset_1('#skF_2',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1'))))
    | v1_xboole_0('#skF_2')
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_52,c_521])).

tff(c_533,plain,
    ( k2_yellow19('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) = '#skF_2'
    | v1_xboole_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_303,c_58,c_56,c_54,c_526])).

tff(c_534,plain,(
    k2_yellow19('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_60,c_533])).

tff(c_44,plain,(
    ! [A_23,B_27,C_29] :
      ( r3_waybel_9(A_23,B_27,C_29)
      | ~ r1_waybel_7(A_23,k2_yellow19(A_23,B_27),C_29)
      | ~ m1_subset_1(C_29,u1_struct_0(A_23))
      | ~ l1_waybel_0(B_27,A_23)
      | ~ v7_waybel_0(B_27)
      | ~ v4_orders_2(B_27)
      | v2_struct_0(B_27)
      | ~ l1_pre_topc(A_23)
      | ~ v2_pre_topc(A_23)
      | v2_struct_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_542,plain,(
    ! [C_29] :
      ( r3_waybel_9('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),C_29)
      | ~ r1_waybel_7('#skF_1','#skF_2',C_29)
      | ~ m1_subset_1(C_29,u1_struct_0('#skF_1'))
      | ~ l1_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
      | ~ v7_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | ~ v4_orders_2(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_534,c_44])).

tff(c_549,plain,(
    ! [C_29] :
      ( r3_waybel_9('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),C_29)
      | ~ r1_waybel_7('#skF_1','#skF_2',C_29)
      | ~ m1_subset_1(C_29,k2_struct_0('#skF_1'))
      | ~ v7_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_437,c_496,c_230,c_542])).

tff(c_550,plain,(
    ! [C_29] :
      ( r3_waybel_9('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),C_29)
      | ~ r1_waybel_7('#skF_1','#skF_2',C_29)
      | ~ m1_subset_1(C_29,k2_struct_0('#skF_1'))
      | ~ v7_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_549])).

tff(c_569,plain,(
    ! [C_29] :
      ( r3_waybel_9('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),C_29)
      | ~ r1_waybel_7('#skF_1','#skF_2',C_29)
      | ~ m1_subset_1(C_29,k2_struct_0('#skF_1'))
      | v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_562,c_550])).

tff(c_570,plain,(
    v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_569])).

tff(c_36,plain,(
    ! [A_17,B_18,C_19] :
      ( ~ v2_struct_0(k3_yellow19(A_17,B_18,C_19))
      | ~ m1_subset_1(C_19,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_18))))
      | ~ v13_waybel_0(C_19,k3_yellow_1(B_18))
      | ~ v2_waybel_0(C_19,k3_yellow_1(B_18))
      | v1_xboole_0(C_19)
      | ~ m1_subset_1(B_18,k1_zfmisc_1(u1_struct_0(A_17)))
      | v1_xboole_0(B_18)
      | ~ l1_struct_0(A_17)
      | v2_struct_0(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_572,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1')))))
    | ~ v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
    | ~ v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
    | v1_xboole_0('#skF_2')
    | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | v1_xboole_0(k2_struct_0('#skF_1'))
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_570,c_36])).

tff(c_575,plain,
    ( v1_xboole_0('#skF_2')
    | v1_xboole_0(k2_struct_0('#skF_1'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_303,c_75,c_230,c_56,c_54,c_52,c_572])).

tff(c_577,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_302,c_60,c_575])).

tff(c_580,plain,(
    ! [C_106] :
      ( r3_waybel_9('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),C_106)
      | ~ r1_waybel_7('#skF_1','#skF_2',C_106)
      | ~ m1_subset_1(C_106,k2_struct_0('#skF_1')) ) ),
    inference(splitRight,[status(thm)],[c_569])).

tff(c_68,plain,
    ( ~ r1_waybel_7('#skF_1','#skF_2','#skF_3')
    | ~ r3_waybel_9('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_109,plain,(
    ~ r3_waybel_9('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_68])).

tff(c_583,plain,
    ( ~ r1_waybel_7('#skF_1','#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_580,c_109])).

tff(c_587,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_231,c_107,c_583])).

tff(c_589,plain,(
    ~ r1_waybel_7('#skF_1','#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_624,plain,(
    ! [B_114,A_115] :
      ( v1_tops_1(B_114,A_115)
      | k2_pre_topc(A_115,B_114) != k2_struct_0(A_115)
      | ~ m1_subset_1(B_114,k1_zfmisc_1(u1_struct_0(A_115)))
      | ~ l1_pre_topc(A_115) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_670,plain,(
    ! [A_120] :
      ( v1_tops_1(k2_struct_0(A_120),A_120)
      | k2_pre_topc(A_120,k2_struct_0(A_120)) != k2_struct_0(A_120)
      | ~ l1_pre_topc(A_120)
      | ~ l1_struct_0(A_120) ) ),
    inference(resolution,[status(thm)],[c_6,c_624])).

tff(c_608,plain,(
    ! [A_110,B_111] :
      ( k2_pre_topc(A_110,B_111) = u1_struct_0(A_110)
      | ~ v1_tops_1(B_111,A_110)
      | ~ m1_subset_1(B_111,k1_zfmisc_1(u1_struct_0(A_110)))
      | ~ l1_pre_topc(A_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_619,plain,(
    ! [A_3] :
      ( k2_pre_topc(A_3,k2_struct_0(A_3)) = u1_struct_0(A_3)
      | ~ v1_tops_1(k2_struct_0(A_3),A_3)
      | ~ l1_pre_topc(A_3)
      | ~ l1_struct_0(A_3) ) ),
    inference(resolution,[status(thm)],[c_6,c_608])).

tff(c_683,plain,(
    ! [A_127] :
      ( k2_pre_topc(A_127,k2_struct_0(A_127)) = u1_struct_0(A_127)
      | k2_pre_topc(A_127,k2_struct_0(A_127)) != k2_struct_0(A_127)
      | ~ l1_pre_topc(A_127)
      | ~ l1_struct_0(A_127) ) ),
    inference(resolution,[status(thm)],[c_670,c_619])).

tff(c_688,plain,(
    ! [A_128] :
      ( k2_pre_topc(A_128,k2_struct_0(A_128)) = u1_struct_0(A_128)
      | ~ l1_struct_0(A_128)
      | ~ l1_pre_topc(A_128) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_683])).

tff(c_708,plain,(
    ! [A_132] :
      ( u1_struct_0(A_132) = k2_struct_0(A_132)
      | ~ l1_pre_topc(A_132)
      | ~ l1_struct_0(A_132)
      | ~ l1_pre_topc(A_132) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_688,c_16])).

tff(c_713,plain,(
    ! [A_133] :
      ( u1_struct_0(A_133) = k2_struct_0(A_133)
      | ~ l1_pre_topc(A_133) ) ),
    inference(resolution,[status(thm)],[c_8,c_708])).

tff(c_717,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_62,c_713])).

tff(c_718,plain,(
    m1_subset_1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_717,c_50])).

tff(c_588,plain,(
    r3_waybel_9('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_755,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_1'))
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_717,c_10])).

tff(c_779,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_1'))
    | ~ l1_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_755])).

tff(c_781,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_779])).

tff(c_784,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_8,c_781])).

tff(c_788,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_784])).

tff(c_789,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_779])).

tff(c_790,plain,(
    l1_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_779])).

tff(c_848,plain,(
    ! [A_137,B_138,C_139] :
      ( v4_orders_2(k3_yellow19(A_137,B_138,C_139))
      | ~ m1_subset_1(C_139,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_138))))
      | ~ v13_waybel_0(C_139,k3_yellow_1(B_138))
      | ~ v2_waybel_0(C_139,k3_yellow_1(B_138))
      | v1_xboole_0(C_139)
      | ~ m1_subset_1(B_138,k1_zfmisc_1(u1_struct_0(A_137)))
      | v1_xboole_0(B_138)
      | ~ l1_struct_0(A_137)
      | v2_struct_0(A_137) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_853,plain,(
    ! [A_137] :
      ( v4_orders_2(k3_yellow19(A_137,k2_struct_0('#skF_1'),'#skF_2'))
      | ~ v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
      | ~ v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_137)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_137)
      | v2_struct_0(A_137) ) ),
    inference(resolution,[status(thm)],[c_52,c_848])).

tff(c_860,plain,(
    ! [A_137] :
      ( v4_orders_2(k3_yellow19(A_137,k2_struct_0('#skF_1'),'#skF_2'))
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_137)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_137)
      | v2_struct_0(A_137) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_853])).

tff(c_868,plain,(
    ! [A_140] :
      ( v4_orders_2(k3_yellow19(A_140,k2_struct_0('#skF_1'),'#skF_2'))
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_140)))
      | ~ l1_struct_0(A_140)
      | v2_struct_0(A_140) ) ),
    inference(negUnitSimplification,[status(thm)],[c_789,c_60,c_860])).

tff(c_871,plain,
    ( v4_orders_2(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
    | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1')))
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_717,c_868])).

tff(c_877,plain,
    ( v4_orders_2(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_790,c_75,c_871])).

tff(c_878,plain,(
    v4_orders_2(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_877])).

tff(c_975,plain,(
    ! [A_154,B_155,C_156] :
      ( v7_waybel_0(k3_yellow19(A_154,B_155,C_156))
      | ~ m1_subset_1(C_156,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_155))))
      | ~ v13_waybel_0(C_156,k3_yellow_1(B_155))
      | ~ v2_waybel_0(C_156,k3_yellow_1(B_155))
      | ~ v1_subset_1(C_156,u1_struct_0(k3_yellow_1(B_155)))
      | v1_xboole_0(C_156)
      | ~ m1_subset_1(B_155,k1_zfmisc_1(u1_struct_0(A_154)))
      | v1_xboole_0(B_155)
      | ~ l1_struct_0(A_154)
      | v2_struct_0(A_154) ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_980,plain,(
    ! [A_154] :
      ( v7_waybel_0(k3_yellow19(A_154,k2_struct_0('#skF_1'),'#skF_2'))
      | ~ v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
      | ~ v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
      | ~ v1_subset_1('#skF_2',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1'))))
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_154)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_154)
      | v2_struct_0(A_154) ) ),
    inference(resolution,[status(thm)],[c_52,c_975])).

tff(c_987,plain,(
    ! [A_154] :
      ( v7_waybel_0(k3_yellow19(A_154,k2_struct_0('#skF_1'),'#skF_2'))
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_154)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_154)
      | v2_struct_0(A_154) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_980])).

tff(c_990,plain,(
    ! [A_157] :
      ( v7_waybel_0(k3_yellow19(A_157,k2_struct_0('#skF_1'),'#skF_2'))
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_157)))
      | ~ l1_struct_0(A_157)
      | v2_struct_0(A_157) ) ),
    inference(negUnitSimplification,[status(thm)],[c_789,c_60,c_987])).

tff(c_993,plain,
    ( v7_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
    | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1')))
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_717,c_990])).

tff(c_999,plain,
    ( v7_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_790,c_75,c_993])).

tff(c_1000,plain,(
    v7_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_999])).

tff(c_960,plain,(
    ! [A_151,B_152,C_153] :
      ( l1_waybel_0(k3_yellow19(A_151,B_152,C_153),A_151)
      | ~ m1_subset_1(C_153,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_152))))
      | ~ v13_waybel_0(C_153,k3_yellow_1(B_152))
      | ~ v2_waybel_0(C_153,k3_yellow_1(B_152))
      | v1_xboole_0(C_153)
      | ~ m1_subset_1(B_152,k1_zfmisc_1(u1_struct_0(A_151)))
      | v1_xboole_0(B_152)
      | ~ l1_struct_0(A_151)
      | v2_struct_0(A_151) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_965,plain,(
    ! [A_151] :
      ( l1_waybel_0(k3_yellow19(A_151,k2_struct_0('#skF_1'),'#skF_2'),A_151)
      | ~ v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
      | ~ v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_151)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_151)
      | v2_struct_0(A_151) ) ),
    inference(resolution,[status(thm)],[c_52,c_960])).

tff(c_972,plain,(
    ! [A_151] :
      ( l1_waybel_0(k3_yellow19(A_151,k2_struct_0('#skF_1'),'#skF_2'),A_151)
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_151)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_151)
      | v2_struct_0(A_151) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_965])).

tff(c_1006,plain,(
    ! [A_158] :
      ( l1_waybel_0(k3_yellow19(A_158,k2_struct_0('#skF_1'),'#skF_2'),A_158)
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_158)))
      | ~ l1_struct_0(A_158)
      | v2_struct_0(A_158) ) ),
    inference(negUnitSimplification,[status(thm)],[c_789,c_60,c_972])).

tff(c_1008,plain,
    ( l1_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1')))
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_717,c_1006])).

tff(c_1013,plain,
    ( l1_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_790,c_75,c_1008])).

tff(c_1014,plain,(
    l1_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_1013])).

tff(c_1023,plain,(
    ! [A_165,B_166] :
      ( k2_yellow19(A_165,k3_yellow19(A_165,k2_struct_0(A_165),B_166)) = B_166
      | ~ m1_subset_1(B_166,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_165)))))
      | ~ v13_waybel_0(B_166,k3_yellow_1(k2_struct_0(A_165)))
      | ~ v2_waybel_0(B_166,k3_yellow_1(k2_struct_0(A_165)))
      | ~ v1_subset_1(B_166,u1_struct_0(k3_yellow_1(k2_struct_0(A_165))))
      | v1_xboole_0(B_166)
      | ~ l1_struct_0(A_165)
      | v2_struct_0(A_165) ) ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_1028,plain,
    ( k2_yellow19('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) = '#skF_2'
    | ~ v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
    | ~ v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
    | ~ v1_subset_1('#skF_2',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1'))))
    | v1_xboole_0('#skF_2')
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_52,c_1023])).

tff(c_1035,plain,
    ( k2_yellow19('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) = '#skF_2'
    | v1_xboole_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_790,c_58,c_56,c_54,c_1028])).

tff(c_1036,plain,(
    k2_yellow19('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_60,c_1035])).

tff(c_1041,plain,(
    ! [C_29] :
      ( r3_waybel_9('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),C_29)
      | ~ r1_waybel_7('#skF_1','#skF_2',C_29)
      | ~ m1_subset_1(C_29,u1_struct_0('#skF_1'))
      | ~ l1_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
      | ~ v7_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | ~ v4_orders_2(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1036,c_44])).

tff(c_1048,plain,(
    ! [C_29] :
      ( r3_waybel_9('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),C_29)
      | ~ r1_waybel_7('#skF_1','#skF_2',C_29)
      | ~ m1_subset_1(C_29,k2_struct_0('#skF_1'))
      | v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_878,c_1000,c_1014,c_717,c_1041])).

tff(c_1049,plain,(
    ! [C_29] :
      ( r3_waybel_9('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),C_29)
      | ~ r1_waybel_7('#skF_1','#skF_2',C_29)
      | ~ m1_subset_1(C_29,k2_struct_0('#skF_1'))
      | v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_1048])).

tff(c_1054,plain,(
    v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_1049])).

tff(c_1056,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1')))))
    | ~ v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
    | ~ v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
    | v1_xboole_0('#skF_2')
    | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | v1_xboole_0(k2_struct_0('#skF_1'))
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_1054,c_36])).

tff(c_1059,plain,
    ( v1_xboole_0('#skF_2')
    | v1_xboole_0(k2_struct_0('#skF_1'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_790,c_75,c_717,c_56,c_54,c_52,c_1056])).

tff(c_1061,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_789,c_60,c_1059])).

tff(c_1063,plain,(
    ~ v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) ),
    inference(splitRight,[status(thm)],[c_1049])).

tff(c_46,plain,(
    ! [A_23,B_27,C_29] :
      ( r1_waybel_7(A_23,k2_yellow19(A_23,B_27),C_29)
      | ~ r3_waybel_9(A_23,B_27,C_29)
      | ~ m1_subset_1(C_29,u1_struct_0(A_23))
      | ~ l1_waybel_0(B_27,A_23)
      | ~ v7_waybel_0(B_27)
      | ~ v4_orders_2(B_27)
      | v2_struct_0(B_27)
      | ~ l1_pre_topc(A_23)
      | ~ v2_pre_topc(A_23)
      | v2_struct_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_1044,plain,(
    ! [C_29] :
      ( r1_waybel_7('#skF_1','#skF_2',C_29)
      | ~ r3_waybel_9('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),C_29)
      | ~ m1_subset_1(C_29,u1_struct_0('#skF_1'))
      | ~ l1_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
      | ~ v7_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | ~ v4_orders_2(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1036,c_46])).

tff(c_1051,plain,(
    ! [C_29] :
      ( r1_waybel_7('#skF_1','#skF_2',C_29)
      | ~ r3_waybel_9('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),C_29)
      | ~ m1_subset_1(C_29,k2_struct_0('#skF_1'))
      | v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_878,c_1000,c_1014,c_717,c_1044])).

tff(c_1052,plain,(
    ! [C_29] :
      ( r1_waybel_7('#skF_1','#skF_2',C_29)
      | ~ r3_waybel_9('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),C_29)
      | ~ m1_subset_1(C_29,k2_struct_0('#skF_1'))
      | v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_1051])).

tff(c_1064,plain,(
    v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_1052])).

tff(c_1065,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1063,c_1064])).

tff(c_1070,plain,(
    ! [C_170] :
      ( r1_waybel_7('#skF_1','#skF_2',C_170)
      | ~ r3_waybel_9('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),C_170)
      | ~ m1_subset_1(C_170,k2_struct_0('#skF_1')) ) ),
    inference(splitRight,[status(thm)],[c_1052])).

tff(c_1076,plain,
    ( r1_waybel_7('#skF_1','#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_588,c_1070])).

tff(c_1080,plain,(
    r1_waybel_7('#skF_1','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_718,c_1076])).

tff(c_1082,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_589,c_1080])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:03:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.57/1.56  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.57/1.58  
% 3.57/1.58  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.57/1.59  %$ r3_waybel_9 > r1_waybel_7 > v6_waybel_0 > v2_waybel_0 > v1_tops_1 > v1_subset_1 > v13_waybel_0 > m1_subset_1 > l1_waybel_0 > v7_waybel_0 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k3_yellow19 > k2_yellow19 > k2_pre_topc > #nlpp > u1_struct_0 > k3_yellow_1 > k3_lattice3 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_lattice3 > #skF_2 > #skF_3 > #skF_1
% 3.57/1.59  
% 3.57/1.59  %Foreground sorts:
% 3.57/1.59  
% 3.57/1.59  
% 3.57/1.59  %Background operators:
% 3.57/1.59  
% 3.57/1.59  
% 3.57/1.59  %Foreground operators:
% 3.57/1.59  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.57/1.59  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 3.57/1.59  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.57/1.59  tff(k3_lattice3, type, k3_lattice3: $i > $i).
% 3.57/1.59  tff(v6_waybel_0, type, v6_waybel_0: ($i * $i) > $o).
% 3.57/1.59  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 3.57/1.59  tff(k3_yellow_1, type, k3_yellow_1: $i > $i).
% 3.57/1.59  tff(v2_waybel_0, type, v2_waybel_0: ($i * $i) > $o).
% 3.57/1.59  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.57/1.59  tff(v7_waybel_0, type, v7_waybel_0: $i > $o).
% 3.57/1.59  tff(v1_tops_1, type, v1_tops_1: ($i * $i) > $o).
% 3.57/1.59  tff(r3_waybel_9, type, r3_waybel_9: ($i * $i * $i) > $o).
% 3.57/1.59  tff('#skF_2', type, '#skF_2': $i).
% 3.57/1.59  tff('#skF_3', type, '#skF_3': $i).
% 3.57/1.59  tff('#skF_1', type, '#skF_1': $i).
% 3.57/1.59  tff(k1_lattice3, type, k1_lattice3: $i > $i).
% 3.57/1.59  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 3.57/1.59  tff(r1_waybel_7, type, r1_waybel_7: ($i * $i * $i) > $o).
% 3.57/1.59  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.57/1.59  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.57/1.59  tff(k2_yellow19, type, k2_yellow19: ($i * $i) > $i).
% 3.57/1.59  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.57/1.59  tff(l1_waybel_0, type, l1_waybel_0: ($i * $i) > $o).
% 3.57/1.59  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.57/1.59  tff(k3_yellow19, type, k3_yellow19: ($i * $i * $i) > $i).
% 3.57/1.59  tff(v13_waybel_0, type, v13_waybel_0: ($i * $i) > $o).
% 3.57/1.59  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.57/1.59  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.57/1.59  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 3.57/1.59  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 3.57/1.59  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.57/1.59  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 3.57/1.59  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.57/1.59  
% 3.57/1.61  tff(f_221, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((((~v1_xboole_0(B) & v1_subset_1(B, u1_struct_0(k3_yellow_1(k2_struct_0(A))))) & v2_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & v13_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A)))))) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r3_waybel_9(A, k3_yellow19(A, k2_struct_0(A), B), C) <=> r1_waybel_7(A, B, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_yellow19)).
% 3.57/1.61  tff(f_37, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.57/1.61  tff(f_58, axiom, (![A]: (l1_pre_topc(A) => (k2_pre_topc(A, k2_struct_0(A)) = k2_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t27_tops_1)).
% 3.57/1.61  tff(f_33, axiom, (![A]: (l1_struct_0(A) => m1_subset_1(k2_struct_0(A), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_struct_0)).
% 3.57/1.61  tff(f_54, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) <=> (k2_pre_topc(A, B) = k2_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tops_1)).
% 3.57/1.61  tff(f_69, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) <=> (k2_pre_topc(A, B) = u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tops_3)).
% 3.57/1.61  tff(f_45, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 3.57/1.61  tff(f_27, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 3.57/1.61  tff(f_29, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 3.57/1.61  tff(f_151, axiom, (![A, B, C]: (((((((((~v2_struct_0(A) & l1_struct_0(A)) & ~v1_xboole_0(B)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) & ~v1_xboole_0(C)) & v1_subset_1(C, u1_struct_0(k3_yellow_1(B)))) & v2_waybel_0(C, k3_yellow_1(B))) & v13_waybel_0(C, k3_yellow_1(B))) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B))))) => ((~v2_struct_0(k3_yellow19(A, B, C)) & v6_waybel_0(k3_yellow19(A, B, C), A)) & v7_waybel_0(k3_yellow19(A, B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc5_yellow19)).
% 3.57/1.61  tff(f_123, axiom, (![A, B, C]: ((((((((~v2_struct_0(A) & l1_struct_0(A)) & ~v1_xboole_0(B)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) & ~v1_xboole_0(C)) & v2_waybel_0(C, k3_yellow_1(B))) & v13_waybel_0(C, k3_yellow_1(B))) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B))))) => (((~v2_struct_0(k3_yellow19(A, B, C)) & v3_orders_2(k3_yellow19(A, B, C))) & v4_orders_2(k3_yellow19(A, B, C))) & v6_waybel_0(k3_yellow19(A, B, C), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_yellow19)).
% 3.57/1.61  tff(f_95, axiom, (![A, B, C]: ((((((((~v2_struct_0(A) & l1_struct_0(A)) & ~v1_xboole_0(B)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) & ~v1_xboole_0(C)) & v2_waybel_0(C, k3_yellow_1(B))) & v13_waybel_0(C, k3_yellow_1(B))) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B))))) => ((~v2_struct_0(k3_yellow19(A, B, C)) & v6_waybel_0(k3_yellow19(A, B, C), A)) & l1_waybel_0(k3_yellow19(A, B, C), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_yellow19)).
% 3.57/1.61  tff(f_194, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: (((((~v1_xboole_0(B) & v1_subset_1(B, u1_struct_0(k3_yellow_1(k2_struct_0(A))))) & v2_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & v13_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A)))))) => (B = k2_yellow19(A, k3_yellow19(A, k2_struct_0(A), B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t15_yellow19)).
% 3.57/1.61  tff(f_175, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r3_waybel_9(A, B, C) <=> r1_waybel_7(A, k2_yellow19(A, B), C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_yellow19)).
% 3.57/1.61  tff(c_62, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_221])).
% 3.57/1.61  tff(c_8, plain, (![A_4]: (l1_struct_0(A_4) | ~l1_pre_topc(A_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.57/1.61  tff(c_16, plain, (![A_9]: (k2_pre_topc(A_9, k2_struct_0(A_9))=k2_struct_0(A_9) | ~l1_pre_topc(A_9))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.57/1.61  tff(c_6, plain, (![A_3]: (m1_subset_1(k2_struct_0(A_3), k1_zfmisc_1(u1_struct_0(A_3))) | ~l1_struct_0(A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.57/1.61  tff(c_155, plain, (![B_53, A_54]: (v1_tops_1(B_53, A_54) | k2_pre_topc(A_54, B_53)!=k2_struct_0(A_54) | ~m1_subset_1(B_53, k1_zfmisc_1(u1_struct_0(A_54))) | ~l1_pre_topc(A_54))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.57/1.61  tff(c_193, plain, (![A_58]: (v1_tops_1(k2_struct_0(A_58), A_58) | k2_pre_topc(A_58, k2_struct_0(A_58))!=k2_struct_0(A_58) | ~l1_pre_topc(A_58) | ~l1_struct_0(A_58))), inference(resolution, [status(thm)], [c_6, c_155])).
% 3.57/1.61  tff(c_110, plain, (![A_44, B_45]: (k2_pre_topc(A_44, B_45)=u1_struct_0(A_44) | ~v1_tops_1(B_45, A_44) | ~m1_subset_1(B_45, k1_zfmisc_1(u1_struct_0(A_44))) | ~l1_pre_topc(A_44))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.57/1.61  tff(c_121, plain, (![A_3]: (k2_pre_topc(A_3, k2_struct_0(A_3))=u1_struct_0(A_3) | ~v1_tops_1(k2_struct_0(A_3), A_3) | ~l1_pre_topc(A_3) | ~l1_struct_0(A_3))), inference(resolution, [status(thm)], [c_6, c_110])).
% 3.57/1.61  tff(c_200, plain, (![A_61]: (k2_pre_topc(A_61, k2_struct_0(A_61))=u1_struct_0(A_61) | k2_pre_topc(A_61, k2_struct_0(A_61))!=k2_struct_0(A_61) | ~l1_pre_topc(A_61) | ~l1_struct_0(A_61))), inference(resolution, [status(thm)], [c_193, c_121])).
% 3.57/1.61  tff(c_206, plain, (![A_65]: (k2_pre_topc(A_65, k2_struct_0(A_65))=u1_struct_0(A_65) | ~l1_struct_0(A_65) | ~l1_pre_topc(A_65))), inference(superposition, [status(thm), theory('equality')], [c_16, c_200])).
% 3.57/1.61  tff(c_221, plain, (![A_66]: (u1_struct_0(A_66)=k2_struct_0(A_66) | ~l1_pre_topc(A_66) | ~l1_struct_0(A_66) | ~l1_pre_topc(A_66))), inference(superposition, [status(thm), theory('equality')], [c_206, c_16])).
% 3.57/1.61  tff(c_226, plain, (![A_67]: (u1_struct_0(A_67)=k2_struct_0(A_67) | ~l1_pre_topc(A_67))), inference(resolution, [status(thm)], [c_8, c_221])).
% 3.57/1.61  tff(c_230, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_62, c_226])).
% 3.57/1.61  tff(c_50, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_221])).
% 3.57/1.61  tff(c_231, plain, (m1_subset_1('#skF_3', k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_230, c_50])).
% 3.57/1.61  tff(c_74, plain, (r3_waybel_9('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), '#skF_3') | r1_waybel_7('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_221])).
% 3.57/1.61  tff(c_107, plain, (r1_waybel_7('#skF_1', '#skF_2', '#skF_3')), inference(splitLeft, [status(thm)], [c_74])).
% 3.57/1.61  tff(c_66, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_221])).
% 3.57/1.61  tff(c_10, plain, (![A_5]: (~v1_xboole_0(u1_struct_0(A_5)) | ~l1_struct_0(A_5) | v2_struct_0(A_5))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.57/1.61  tff(c_268, plain, (~v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_230, c_10])).
% 3.57/1.61  tff(c_292, plain, (~v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_66, c_268])).
% 3.57/1.61  tff(c_294, plain, (~l1_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_292])).
% 3.57/1.61  tff(c_297, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_8, c_294])).
% 3.57/1.61  tff(c_301, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_62, c_297])).
% 3.57/1.61  tff(c_302, plain, (~v1_xboole_0(k2_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_292])).
% 3.57/1.61  tff(c_60, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_221])).
% 3.57/1.61  tff(c_303, plain, (l1_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_292])).
% 3.57/1.61  tff(c_2, plain, (![A_1]: (k2_subset_1(A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.57/1.61  tff(c_4, plain, (![A_2]: (m1_subset_1(k2_subset_1(A_2), k1_zfmisc_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.57/1.61  tff(c_75, plain, (![A_2]: (m1_subset_1(A_2, k1_zfmisc_1(A_2)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_4])).
% 3.57/1.61  tff(c_56, plain, (v2_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_221])).
% 3.57/1.61  tff(c_54, plain, (v13_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_221])).
% 3.57/1.61  tff(c_52, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1')))))), inference(cnfTransformation, [status(thm)], [f_221])).
% 3.57/1.61  tff(c_58, plain, (v1_subset_1('#skF_2', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_221])).
% 3.57/1.61  tff(c_506, plain, (![A_100, B_101, C_102]: (v7_waybel_0(k3_yellow19(A_100, B_101, C_102)) | ~m1_subset_1(C_102, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_101)))) | ~v13_waybel_0(C_102, k3_yellow_1(B_101)) | ~v2_waybel_0(C_102, k3_yellow_1(B_101)) | ~v1_subset_1(C_102, u1_struct_0(k3_yellow_1(B_101))) | v1_xboole_0(C_102) | ~m1_subset_1(B_101, k1_zfmisc_1(u1_struct_0(A_100))) | v1_xboole_0(B_101) | ~l1_struct_0(A_100) | v2_struct_0(A_100))), inference(cnfTransformation, [status(thm)], [f_151])).
% 3.57/1.61  tff(c_511, plain, (![A_100]: (v7_waybel_0(k3_yellow19(A_100, k2_struct_0('#skF_1'), '#skF_2')) | ~v13_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v2_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v1_subset_1('#skF_2', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1')))) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_100))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0(A_100) | v2_struct_0(A_100))), inference(resolution, [status(thm)], [c_52, c_506])).
% 3.57/1.61  tff(c_518, plain, (![A_100]: (v7_waybel_0(k3_yellow19(A_100, k2_struct_0('#skF_1'), '#skF_2')) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_100))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0(A_100) | v2_struct_0(A_100))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_511])).
% 3.57/1.61  tff(c_552, plain, (![A_105]: (v7_waybel_0(k3_yellow19(A_105, k2_struct_0('#skF_1'), '#skF_2')) | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_105))) | ~l1_struct_0(A_105) | v2_struct_0(A_105))), inference(negUnitSimplification, [status(thm)], [c_302, c_60, c_518])).
% 3.57/1.61  tff(c_555, plain, (v7_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_230, c_552])).
% 3.57/1.61  tff(c_561, plain, (v7_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_303, c_75, c_555])).
% 3.57/1.61  tff(c_562, plain, (v7_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_66, c_561])).
% 3.57/1.61  tff(c_64, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_221])).
% 3.57/1.61  tff(c_412, plain, (![A_77, B_78, C_79]: (v4_orders_2(k3_yellow19(A_77, B_78, C_79)) | ~m1_subset_1(C_79, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_78)))) | ~v13_waybel_0(C_79, k3_yellow_1(B_78)) | ~v2_waybel_0(C_79, k3_yellow_1(B_78)) | v1_xboole_0(C_79) | ~m1_subset_1(B_78, k1_zfmisc_1(u1_struct_0(A_77))) | v1_xboole_0(B_78) | ~l1_struct_0(A_77) | v2_struct_0(A_77))), inference(cnfTransformation, [status(thm)], [f_123])).
% 3.57/1.61  tff(c_417, plain, (![A_77]: (v4_orders_2(k3_yellow19(A_77, k2_struct_0('#skF_1'), '#skF_2')) | ~v13_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v2_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_77))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0(A_77) | v2_struct_0(A_77))), inference(resolution, [status(thm)], [c_52, c_412])).
% 3.57/1.61  tff(c_424, plain, (![A_77]: (v4_orders_2(k3_yellow19(A_77, k2_struct_0('#skF_1'), '#skF_2')) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_77))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0(A_77) | v2_struct_0(A_77))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_417])).
% 3.57/1.61  tff(c_427, plain, (![A_80]: (v4_orders_2(k3_yellow19(A_80, k2_struct_0('#skF_1'), '#skF_2')) | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_80))) | ~l1_struct_0(A_80) | v2_struct_0(A_80))), inference(negUnitSimplification, [status(thm)], [c_302, c_60, c_424])).
% 3.57/1.61  tff(c_430, plain, (v4_orders_2(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_230, c_427])).
% 3.57/1.61  tff(c_436, plain, (v4_orders_2(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_303, c_75, c_430])).
% 3.57/1.61  tff(c_437, plain, (v4_orders_2(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_66, c_436])).
% 3.57/1.61  tff(c_472, plain, (![A_88, B_89, C_90]: (l1_waybel_0(k3_yellow19(A_88, B_89, C_90), A_88) | ~m1_subset_1(C_90, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_89)))) | ~v13_waybel_0(C_90, k3_yellow_1(B_89)) | ~v2_waybel_0(C_90, k3_yellow_1(B_89)) | v1_xboole_0(C_90) | ~m1_subset_1(B_89, k1_zfmisc_1(u1_struct_0(A_88))) | v1_xboole_0(B_89) | ~l1_struct_0(A_88) | v2_struct_0(A_88))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.57/1.61  tff(c_477, plain, (![A_88]: (l1_waybel_0(k3_yellow19(A_88, k2_struct_0('#skF_1'), '#skF_2'), A_88) | ~v13_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v2_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_88))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0(A_88) | v2_struct_0(A_88))), inference(resolution, [status(thm)], [c_52, c_472])).
% 3.57/1.61  tff(c_484, plain, (![A_88]: (l1_waybel_0(k3_yellow19(A_88, k2_struct_0('#skF_1'), '#skF_2'), A_88) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_88))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0(A_88) | v2_struct_0(A_88))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_477])).
% 3.57/1.61  tff(c_488, plain, (![A_91]: (l1_waybel_0(k3_yellow19(A_91, k2_struct_0('#skF_1'), '#skF_2'), A_91) | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_91))) | ~l1_struct_0(A_91) | v2_struct_0(A_91))), inference(negUnitSimplification, [status(thm)], [c_302, c_60, c_484])).
% 3.57/1.61  tff(c_490, plain, (l1_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_230, c_488])).
% 3.57/1.61  tff(c_495, plain, (l1_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_303, c_75, c_490])).
% 3.57/1.61  tff(c_496, plain, (l1_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_66, c_495])).
% 3.57/1.61  tff(c_521, plain, (![A_103, B_104]: (k2_yellow19(A_103, k3_yellow19(A_103, k2_struct_0(A_103), B_104))=B_104 | ~m1_subset_1(B_104, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_103))))) | ~v13_waybel_0(B_104, k3_yellow_1(k2_struct_0(A_103))) | ~v2_waybel_0(B_104, k3_yellow_1(k2_struct_0(A_103))) | ~v1_subset_1(B_104, u1_struct_0(k3_yellow_1(k2_struct_0(A_103)))) | v1_xboole_0(B_104) | ~l1_struct_0(A_103) | v2_struct_0(A_103))), inference(cnfTransformation, [status(thm)], [f_194])).
% 3.57/1.61  tff(c_526, plain, (k2_yellow19('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))='#skF_2' | ~v13_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v2_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v1_subset_1('#skF_2', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1')))) | v1_xboole_0('#skF_2') | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_52, c_521])).
% 3.57/1.61  tff(c_533, plain, (k2_yellow19('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))='#skF_2' | v1_xboole_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_303, c_58, c_56, c_54, c_526])).
% 3.57/1.61  tff(c_534, plain, (k2_yellow19('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_66, c_60, c_533])).
% 3.57/1.61  tff(c_44, plain, (![A_23, B_27, C_29]: (r3_waybel_9(A_23, B_27, C_29) | ~r1_waybel_7(A_23, k2_yellow19(A_23, B_27), C_29) | ~m1_subset_1(C_29, u1_struct_0(A_23)) | ~l1_waybel_0(B_27, A_23) | ~v7_waybel_0(B_27) | ~v4_orders_2(B_27) | v2_struct_0(B_27) | ~l1_pre_topc(A_23) | ~v2_pre_topc(A_23) | v2_struct_0(A_23))), inference(cnfTransformation, [status(thm)], [f_175])).
% 3.57/1.61  tff(c_542, plain, (![C_29]: (r3_waybel_9('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), C_29) | ~r1_waybel_7('#skF_1', '#skF_2', C_29) | ~m1_subset_1(C_29, u1_struct_0('#skF_1')) | ~l1_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~v7_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | ~v4_orders_2(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_534, c_44])).
% 3.57/1.61  tff(c_549, plain, (![C_29]: (r3_waybel_9('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), C_29) | ~r1_waybel_7('#skF_1', '#skF_2', C_29) | ~m1_subset_1(C_29, k2_struct_0('#skF_1')) | ~v7_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_437, c_496, c_230, c_542])).
% 3.57/1.61  tff(c_550, plain, (![C_29]: (r3_waybel_9('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), C_29) | ~r1_waybel_7('#skF_1', '#skF_2', C_29) | ~m1_subset_1(C_29, k2_struct_0('#skF_1')) | ~v7_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_66, c_549])).
% 3.57/1.61  tff(c_569, plain, (![C_29]: (r3_waybel_9('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), C_29) | ~r1_waybel_7('#skF_1', '#skF_2', C_29) | ~m1_subset_1(C_29, k2_struct_0('#skF_1')) | v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_562, c_550])).
% 3.57/1.61  tff(c_570, plain, (v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))), inference(splitLeft, [status(thm)], [c_569])).
% 3.57/1.61  tff(c_36, plain, (![A_17, B_18, C_19]: (~v2_struct_0(k3_yellow19(A_17, B_18, C_19)) | ~m1_subset_1(C_19, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_18)))) | ~v13_waybel_0(C_19, k3_yellow_1(B_18)) | ~v2_waybel_0(C_19, k3_yellow_1(B_18)) | v1_xboole_0(C_19) | ~m1_subset_1(B_18, k1_zfmisc_1(u1_struct_0(A_17))) | v1_xboole_0(B_18) | ~l1_struct_0(A_17) | v2_struct_0(A_17))), inference(cnfTransformation, [status(thm)], [f_123])).
% 3.57/1.61  tff(c_572, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1'))))) | ~v13_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v2_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_570, c_36])).
% 3.57/1.61  tff(c_575, plain, (v1_xboole_0('#skF_2') | v1_xboole_0(k2_struct_0('#skF_1')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_303, c_75, c_230, c_56, c_54, c_52, c_572])).
% 3.57/1.61  tff(c_577, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_302, c_60, c_575])).
% 3.57/1.61  tff(c_580, plain, (![C_106]: (r3_waybel_9('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), C_106) | ~r1_waybel_7('#skF_1', '#skF_2', C_106) | ~m1_subset_1(C_106, k2_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_569])).
% 3.57/1.61  tff(c_68, plain, (~r1_waybel_7('#skF_1', '#skF_2', '#skF_3') | ~r3_waybel_9('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_221])).
% 3.57/1.61  tff(c_109, plain, (~r3_waybel_9('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_107, c_68])).
% 3.57/1.61  tff(c_583, plain, (~r1_waybel_7('#skF_1', '#skF_2', '#skF_3') | ~m1_subset_1('#skF_3', k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_580, c_109])).
% 3.57/1.61  tff(c_587, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_231, c_107, c_583])).
% 3.57/1.61  tff(c_589, plain, (~r1_waybel_7('#skF_1', '#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_74])).
% 3.57/1.61  tff(c_624, plain, (![B_114, A_115]: (v1_tops_1(B_114, A_115) | k2_pre_topc(A_115, B_114)!=k2_struct_0(A_115) | ~m1_subset_1(B_114, k1_zfmisc_1(u1_struct_0(A_115))) | ~l1_pre_topc(A_115))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.57/1.61  tff(c_670, plain, (![A_120]: (v1_tops_1(k2_struct_0(A_120), A_120) | k2_pre_topc(A_120, k2_struct_0(A_120))!=k2_struct_0(A_120) | ~l1_pre_topc(A_120) | ~l1_struct_0(A_120))), inference(resolution, [status(thm)], [c_6, c_624])).
% 3.57/1.61  tff(c_608, plain, (![A_110, B_111]: (k2_pre_topc(A_110, B_111)=u1_struct_0(A_110) | ~v1_tops_1(B_111, A_110) | ~m1_subset_1(B_111, k1_zfmisc_1(u1_struct_0(A_110))) | ~l1_pre_topc(A_110))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.57/1.61  tff(c_619, plain, (![A_3]: (k2_pre_topc(A_3, k2_struct_0(A_3))=u1_struct_0(A_3) | ~v1_tops_1(k2_struct_0(A_3), A_3) | ~l1_pre_topc(A_3) | ~l1_struct_0(A_3))), inference(resolution, [status(thm)], [c_6, c_608])).
% 3.57/1.61  tff(c_683, plain, (![A_127]: (k2_pre_topc(A_127, k2_struct_0(A_127))=u1_struct_0(A_127) | k2_pre_topc(A_127, k2_struct_0(A_127))!=k2_struct_0(A_127) | ~l1_pre_topc(A_127) | ~l1_struct_0(A_127))), inference(resolution, [status(thm)], [c_670, c_619])).
% 3.57/1.61  tff(c_688, plain, (![A_128]: (k2_pre_topc(A_128, k2_struct_0(A_128))=u1_struct_0(A_128) | ~l1_struct_0(A_128) | ~l1_pre_topc(A_128))), inference(superposition, [status(thm), theory('equality')], [c_16, c_683])).
% 3.57/1.61  tff(c_708, plain, (![A_132]: (u1_struct_0(A_132)=k2_struct_0(A_132) | ~l1_pre_topc(A_132) | ~l1_struct_0(A_132) | ~l1_pre_topc(A_132))), inference(superposition, [status(thm), theory('equality')], [c_688, c_16])).
% 3.57/1.61  tff(c_713, plain, (![A_133]: (u1_struct_0(A_133)=k2_struct_0(A_133) | ~l1_pre_topc(A_133))), inference(resolution, [status(thm)], [c_8, c_708])).
% 3.57/1.61  tff(c_717, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_62, c_713])).
% 3.57/1.61  tff(c_718, plain, (m1_subset_1('#skF_3', k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_717, c_50])).
% 3.57/1.61  tff(c_588, plain, (r3_waybel_9('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), '#skF_3')), inference(splitRight, [status(thm)], [c_74])).
% 3.57/1.61  tff(c_755, plain, (~v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_717, c_10])).
% 3.57/1.61  tff(c_779, plain, (~v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_66, c_755])).
% 3.57/1.61  tff(c_781, plain, (~l1_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_779])).
% 3.57/1.61  tff(c_784, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_8, c_781])).
% 3.57/1.61  tff(c_788, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_62, c_784])).
% 3.57/1.61  tff(c_789, plain, (~v1_xboole_0(k2_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_779])).
% 3.57/1.61  tff(c_790, plain, (l1_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_779])).
% 3.57/1.61  tff(c_848, plain, (![A_137, B_138, C_139]: (v4_orders_2(k3_yellow19(A_137, B_138, C_139)) | ~m1_subset_1(C_139, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_138)))) | ~v13_waybel_0(C_139, k3_yellow_1(B_138)) | ~v2_waybel_0(C_139, k3_yellow_1(B_138)) | v1_xboole_0(C_139) | ~m1_subset_1(B_138, k1_zfmisc_1(u1_struct_0(A_137))) | v1_xboole_0(B_138) | ~l1_struct_0(A_137) | v2_struct_0(A_137))), inference(cnfTransformation, [status(thm)], [f_123])).
% 3.57/1.61  tff(c_853, plain, (![A_137]: (v4_orders_2(k3_yellow19(A_137, k2_struct_0('#skF_1'), '#skF_2')) | ~v13_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v2_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_137))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0(A_137) | v2_struct_0(A_137))), inference(resolution, [status(thm)], [c_52, c_848])).
% 3.57/1.61  tff(c_860, plain, (![A_137]: (v4_orders_2(k3_yellow19(A_137, k2_struct_0('#skF_1'), '#skF_2')) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_137))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0(A_137) | v2_struct_0(A_137))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_853])).
% 3.57/1.61  tff(c_868, plain, (![A_140]: (v4_orders_2(k3_yellow19(A_140, k2_struct_0('#skF_1'), '#skF_2')) | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_140))) | ~l1_struct_0(A_140) | v2_struct_0(A_140))), inference(negUnitSimplification, [status(thm)], [c_789, c_60, c_860])).
% 3.57/1.61  tff(c_871, plain, (v4_orders_2(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_717, c_868])).
% 3.57/1.61  tff(c_877, plain, (v4_orders_2(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_790, c_75, c_871])).
% 3.57/1.61  tff(c_878, plain, (v4_orders_2(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_66, c_877])).
% 3.57/1.61  tff(c_975, plain, (![A_154, B_155, C_156]: (v7_waybel_0(k3_yellow19(A_154, B_155, C_156)) | ~m1_subset_1(C_156, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_155)))) | ~v13_waybel_0(C_156, k3_yellow_1(B_155)) | ~v2_waybel_0(C_156, k3_yellow_1(B_155)) | ~v1_subset_1(C_156, u1_struct_0(k3_yellow_1(B_155))) | v1_xboole_0(C_156) | ~m1_subset_1(B_155, k1_zfmisc_1(u1_struct_0(A_154))) | v1_xboole_0(B_155) | ~l1_struct_0(A_154) | v2_struct_0(A_154))), inference(cnfTransformation, [status(thm)], [f_151])).
% 3.57/1.61  tff(c_980, plain, (![A_154]: (v7_waybel_0(k3_yellow19(A_154, k2_struct_0('#skF_1'), '#skF_2')) | ~v13_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v2_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v1_subset_1('#skF_2', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1')))) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_154))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0(A_154) | v2_struct_0(A_154))), inference(resolution, [status(thm)], [c_52, c_975])).
% 3.57/1.61  tff(c_987, plain, (![A_154]: (v7_waybel_0(k3_yellow19(A_154, k2_struct_0('#skF_1'), '#skF_2')) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_154))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0(A_154) | v2_struct_0(A_154))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_980])).
% 3.57/1.61  tff(c_990, plain, (![A_157]: (v7_waybel_0(k3_yellow19(A_157, k2_struct_0('#skF_1'), '#skF_2')) | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_157))) | ~l1_struct_0(A_157) | v2_struct_0(A_157))), inference(negUnitSimplification, [status(thm)], [c_789, c_60, c_987])).
% 3.57/1.61  tff(c_993, plain, (v7_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_717, c_990])).
% 3.57/1.61  tff(c_999, plain, (v7_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_790, c_75, c_993])).
% 3.57/1.61  tff(c_1000, plain, (v7_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_66, c_999])).
% 3.57/1.61  tff(c_960, plain, (![A_151, B_152, C_153]: (l1_waybel_0(k3_yellow19(A_151, B_152, C_153), A_151) | ~m1_subset_1(C_153, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_152)))) | ~v13_waybel_0(C_153, k3_yellow_1(B_152)) | ~v2_waybel_0(C_153, k3_yellow_1(B_152)) | v1_xboole_0(C_153) | ~m1_subset_1(B_152, k1_zfmisc_1(u1_struct_0(A_151))) | v1_xboole_0(B_152) | ~l1_struct_0(A_151) | v2_struct_0(A_151))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.57/1.61  tff(c_965, plain, (![A_151]: (l1_waybel_0(k3_yellow19(A_151, k2_struct_0('#skF_1'), '#skF_2'), A_151) | ~v13_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v2_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_151))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0(A_151) | v2_struct_0(A_151))), inference(resolution, [status(thm)], [c_52, c_960])).
% 3.57/1.61  tff(c_972, plain, (![A_151]: (l1_waybel_0(k3_yellow19(A_151, k2_struct_0('#skF_1'), '#skF_2'), A_151) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_151))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0(A_151) | v2_struct_0(A_151))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_965])).
% 3.57/1.61  tff(c_1006, plain, (![A_158]: (l1_waybel_0(k3_yellow19(A_158, k2_struct_0('#skF_1'), '#skF_2'), A_158) | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_158))) | ~l1_struct_0(A_158) | v2_struct_0(A_158))), inference(negUnitSimplification, [status(thm)], [c_789, c_60, c_972])).
% 3.57/1.61  tff(c_1008, plain, (l1_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_717, c_1006])).
% 3.57/1.61  tff(c_1013, plain, (l1_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_790, c_75, c_1008])).
% 3.57/1.61  tff(c_1014, plain, (l1_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_66, c_1013])).
% 3.57/1.61  tff(c_1023, plain, (![A_165, B_166]: (k2_yellow19(A_165, k3_yellow19(A_165, k2_struct_0(A_165), B_166))=B_166 | ~m1_subset_1(B_166, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_165))))) | ~v13_waybel_0(B_166, k3_yellow_1(k2_struct_0(A_165))) | ~v2_waybel_0(B_166, k3_yellow_1(k2_struct_0(A_165))) | ~v1_subset_1(B_166, u1_struct_0(k3_yellow_1(k2_struct_0(A_165)))) | v1_xboole_0(B_166) | ~l1_struct_0(A_165) | v2_struct_0(A_165))), inference(cnfTransformation, [status(thm)], [f_194])).
% 3.57/1.61  tff(c_1028, plain, (k2_yellow19('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))='#skF_2' | ~v13_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v2_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v1_subset_1('#skF_2', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1')))) | v1_xboole_0('#skF_2') | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_52, c_1023])).
% 3.57/1.61  tff(c_1035, plain, (k2_yellow19('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))='#skF_2' | v1_xboole_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_790, c_58, c_56, c_54, c_1028])).
% 3.57/1.61  tff(c_1036, plain, (k2_yellow19('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_66, c_60, c_1035])).
% 3.57/1.61  tff(c_1041, plain, (![C_29]: (r3_waybel_9('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), C_29) | ~r1_waybel_7('#skF_1', '#skF_2', C_29) | ~m1_subset_1(C_29, u1_struct_0('#skF_1')) | ~l1_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~v7_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | ~v4_orders_2(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_1036, c_44])).
% 3.57/1.61  tff(c_1048, plain, (![C_29]: (r3_waybel_9('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), C_29) | ~r1_waybel_7('#skF_1', '#skF_2', C_29) | ~m1_subset_1(C_29, k2_struct_0('#skF_1')) | v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_878, c_1000, c_1014, c_717, c_1041])).
% 3.57/1.61  tff(c_1049, plain, (![C_29]: (r3_waybel_9('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), C_29) | ~r1_waybel_7('#skF_1', '#skF_2', C_29) | ~m1_subset_1(C_29, k2_struct_0('#skF_1')) | v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_66, c_1048])).
% 3.57/1.61  tff(c_1054, plain, (v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))), inference(splitLeft, [status(thm)], [c_1049])).
% 3.57/1.61  tff(c_1056, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1'))))) | ~v13_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v2_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_1054, c_36])).
% 3.57/1.61  tff(c_1059, plain, (v1_xboole_0('#skF_2') | v1_xboole_0(k2_struct_0('#skF_1')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_790, c_75, c_717, c_56, c_54, c_52, c_1056])).
% 3.57/1.61  tff(c_1061, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_789, c_60, c_1059])).
% 3.57/1.61  tff(c_1063, plain, (~v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))), inference(splitRight, [status(thm)], [c_1049])).
% 3.57/1.61  tff(c_46, plain, (![A_23, B_27, C_29]: (r1_waybel_7(A_23, k2_yellow19(A_23, B_27), C_29) | ~r3_waybel_9(A_23, B_27, C_29) | ~m1_subset_1(C_29, u1_struct_0(A_23)) | ~l1_waybel_0(B_27, A_23) | ~v7_waybel_0(B_27) | ~v4_orders_2(B_27) | v2_struct_0(B_27) | ~l1_pre_topc(A_23) | ~v2_pre_topc(A_23) | v2_struct_0(A_23))), inference(cnfTransformation, [status(thm)], [f_175])).
% 3.57/1.61  tff(c_1044, plain, (![C_29]: (r1_waybel_7('#skF_1', '#skF_2', C_29) | ~r3_waybel_9('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), C_29) | ~m1_subset_1(C_29, u1_struct_0('#skF_1')) | ~l1_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~v7_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | ~v4_orders_2(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_1036, c_46])).
% 3.57/1.61  tff(c_1051, plain, (![C_29]: (r1_waybel_7('#skF_1', '#skF_2', C_29) | ~r3_waybel_9('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), C_29) | ~m1_subset_1(C_29, k2_struct_0('#skF_1')) | v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_878, c_1000, c_1014, c_717, c_1044])).
% 3.57/1.61  tff(c_1052, plain, (![C_29]: (r1_waybel_7('#skF_1', '#skF_2', C_29) | ~r3_waybel_9('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), C_29) | ~m1_subset_1(C_29, k2_struct_0('#skF_1')) | v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_66, c_1051])).
% 3.57/1.61  tff(c_1064, plain, (v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))), inference(splitLeft, [status(thm)], [c_1052])).
% 3.57/1.61  tff(c_1065, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1063, c_1064])).
% 3.57/1.61  tff(c_1070, plain, (![C_170]: (r1_waybel_7('#skF_1', '#skF_2', C_170) | ~r3_waybel_9('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), C_170) | ~m1_subset_1(C_170, k2_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_1052])).
% 3.57/1.61  tff(c_1076, plain, (r1_waybel_7('#skF_1', '#skF_2', '#skF_3') | ~m1_subset_1('#skF_3', k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_588, c_1070])).
% 3.57/1.61  tff(c_1080, plain, (r1_waybel_7('#skF_1', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_718, c_1076])).
% 3.57/1.61  tff(c_1082, plain, $false, inference(negUnitSimplification, [status(thm)], [c_589, c_1080])).
% 3.57/1.61  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.57/1.61  
% 3.57/1.61  Inference rules
% 3.57/1.61  ----------------------
% 3.57/1.61  #Ref     : 0
% 3.57/1.61  #Sup     : 181
% 3.57/1.61  #Fact    : 0
% 3.57/1.61  #Define  : 0
% 3.57/1.61  #Split   : 11
% 3.57/1.61  #Chain   : 0
% 3.57/1.61  #Close   : 0
% 3.57/1.61  
% 3.57/1.61  Ordering : KBO
% 3.57/1.61  
% 3.57/1.61  Simplification rules
% 3.57/1.61  ----------------------
% 3.57/1.61  #Subsume      : 27
% 3.57/1.61  #Demod        : 214
% 3.57/1.61  #Tautology    : 68
% 3.57/1.61  #SimpNegUnit  : 42
% 3.57/1.62  #BackRed      : 2
% 3.57/1.62  
% 3.57/1.62  #Partial instantiations: 0
% 3.57/1.62  #Strategies tried      : 1
% 3.57/1.62  
% 3.57/1.62  Timing (in seconds)
% 3.57/1.62  ----------------------
% 3.57/1.62  Preprocessing        : 0.38
% 3.57/1.62  Parsing              : 0.21
% 3.57/1.62  CNF conversion       : 0.03
% 3.57/1.62  Main loop            : 0.42
% 3.57/1.62  Inferencing          : 0.15
% 3.57/1.62  Reduction            : 0.13
% 3.57/1.62  Demodulation         : 0.09
% 3.57/1.62  BG Simplification    : 0.03
% 3.57/1.62  Subsumption          : 0.08
% 3.57/1.62  Abstraction          : 0.02
% 3.57/1.62  MUC search           : 0.00
% 3.57/1.62  Cooper               : 0.00
% 3.57/1.62  Total                : 0.86
% 3.57/1.62  Index Insertion      : 0.00
% 3.57/1.62  Index Deletion       : 0.00
% 3.57/1.62  Index Matching       : 0.00
% 3.57/1.62  BG Taut test         : 0.00
%------------------------------------------------------------------------------
