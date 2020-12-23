%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:36 EST 2020

% Result     : Theorem 2.83s
% Output     : CNFRefutation 2.83s
% Verified   : 
% Statistics : Number of formulae       :  165 (1181 expanded)
%              Number of leaves         :   39 ( 429 expanded)
%              Depth                    :   20
%              Number of atoms          :  518 (6417 expanded)
%              Number of equality atoms :    9 (  25 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_waybel_9 > r1_waybel_7 > v6_waybel_0 > v2_waybel_0 > v1_subset_1 > v13_waybel_0 > m1_subset_1 > l1_waybel_0 > v7_waybel_0 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k3_yellow19 > k2_yellow19 > #nlpp > u1_struct_0 > k3_yellow_1 > k3_lattice3 > k2_struct_0 > k1_zfmisc_1 > k1_lattice3 > #skF_2 > #skF_3 > #skF_1

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

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_195,negated_conjecture,(
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

tff(f_33,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_29,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => m1_subset_1(k2_struct_0(A),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_struct_0)).

tff(f_97,axiom,(
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

tff(f_41,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(k2_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_struct_0)).

tff(f_69,axiom,(
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

tff(f_168,axiom,(
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

tff(f_149,axiom,(
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

tff(f_125,axiom,(
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

tff(c_36,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_54,plain,
    ( ~ r1_waybel_7('#skF_1','#skF_2','#skF_3')
    | ~ r3_waybel_9('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_73,plain,(
    ~ r3_waybel_9('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_60,plain,
    ( r3_waybel_9('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),'#skF_3')
    | r1_waybel_7('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_74,plain,(
    r1_waybel_7('#skF_1','#skF_2','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_73,c_60])).

tff(c_48,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_4,plain,(
    ! [A_2] :
      ( l1_struct_0(A_2)
      | ~ l1_pre_topc(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_52,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_2,plain,(
    ! [A_1] :
      ( m1_subset_1(k2_struct_0(A_1),k1_zfmisc_1(u1_struct_0(A_1)))
      | ~ l1_struct_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_46,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_42,plain,(
    v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_40,plain,(
    v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_38,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1'))))) ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_82,plain,(
    ! [A_41,B_42,C_43] :
      ( v4_orders_2(k3_yellow19(A_41,B_42,C_43))
      | ~ m1_subset_1(C_43,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_42))))
      | ~ v13_waybel_0(C_43,k3_yellow_1(B_42))
      | ~ v2_waybel_0(C_43,k3_yellow_1(B_42))
      | v1_xboole_0(C_43)
      | ~ m1_subset_1(B_42,k1_zfmisc_1(u1_struct_0(A_41)))
      | v1_xboole_0(B_42)
      | ~ l1_struct_0(A_41)
      | v2_struct_0(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_87,plain,(
    ! [A_41] :
      ( v4_orders_2(k3_yellow19(A_41,k2_struct_0('#skF_1'),'#skF_2'))
      | ~ v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
      | ~ v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_41)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_41)
      | v2_struct_0(A_41) ) ),
    inference(resolution,[status(thm)],[c_38,c_82])).

tff(c_91,plain,(
    ! [A_41] :
      ( v4_orders_2(k3_yellow19(A_41,k2_struct_0('#skF_1'),'#skF_2'))
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_41)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_41)
      | v2_struct_0(A_41) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_87])).

tff(c_92,plain,(
    ! [A_41] :
      ( v4_orders_2(k3_yellow19(A_41,k2_struct_0('#skF_1'),'#skF_2'))
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_41)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_41)
      | v2_struct_0(A_41) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_91])).

tff(c_93,plain,(
    v1_xboole_0(k2_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_92])).

tff(c_6,plain,(
    ! [A_3] :
      ( ~ v1_xboole_0(k2_struct_0(A_3))
      | ~ l1_struct_0(A_3)
      | v2_struct_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_96,plain,
    ( ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_93,c_6])).

tff(c_99,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_96])).

tff(c_102,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_4,c_99])).

tff(c_106,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_102])).

tff(c_109,plain,(
    ! [A_44] :
      ( v4_orders_2(k3_yellow19(A_44,k2_struct_0('#skF_1'),'#skF_2'))
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_44)))
      | ~ l1_struct_0(A_44)
      | v2_struct_0(A_44) ) ),
    inference(splitRight,[status(thm)],[c_92])).

tff(c_113,plain,
    ( v4_orders_2(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
    | v2_struct_0('#skF_1')
    | ~ l1_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_2,c_109])).

tff(c_116,plain,
    ( v4_orders_2(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
    | ~ l1_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_113])).

tff(c_128,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_116])).

tff(c_131,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_4,c_128])).

tff(c_135,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_131])).

tff(c_137,plain,(
    l1_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_116])).

tff(c_108,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_92])).

tff(c_50,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_136,plain,(
    v4_orders_2(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) ),
    inference(splitRight,[status(thm)],[c_116])).

tff(c_166,plain,(
    ! [A_53,B_54,C_55] :
      ( l1_waybel_0(k3_yellow19(A_53,B_54,C_55),A_53)
      | ~ m1_subset_1(C_55,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_54))))
      | ~ v13_waybel_0(C_55,k3_yellow_1(B_54))
      | ~ v2_waybel_0(C_55,k3_yellow_1(B_54))
      | v1_xboole_0(C_55)
      | ~ m1_subset_1(B_54,k1_zfmisc_1(u1_struct_0(A_53)))
      | v1_xboole_0(B_54)
      | ~ l1_struct_0(A_53)
      | v2_struct_0(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_171,plain,(
    ! [A_53] :
      ( l1_waybel_0(k3_yellow19(A_53,k2_struct_0('#skF_1'),'#skF_2'),A_53)
      | ~ v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
      | ~ v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_53)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_53)
      | v2_struct_0(A_53) ) ),
    inference(resolution,[status(thm)],[c_38,c_166])).

tff(c_175,plain,(
    ! [A_53] :
      ( l1_waybel_0(k3_yellow19(A_53,k2_struct_0('#skF_1'),'#skF_2'),A_53)
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_53)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_53)
      | v2_struct_0(A_53) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_171])).

tff(c_177,plain,(
    ! [A_56] :
      ( l1_waybel_0(k3_yellow19(A_56,k2_struct_0('#skF_1'),'#skF_2'),A_56)
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_56)))
      | ~ l1_struct_0(A_56)
      | v2_struct_0(A_56) ) ),
    inference(negUnitSimplification,[status(thm)],[c_108,c_46,c_175])).

tff(c_180,plain,
    ( l1_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | v2_struct_0('#skF_1')
    | ~ l1_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_2,c_177])).

tff(c_183,plain,
    ( l1_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_180])).

tff(c_184,plain,(
    l1_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_183])).

tff(c_44,plain,(
    v1_subset_1('#skF_2',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_185,plain,(
    ! [A_57,B_58] :
      ( k2_yellow19(A_57,k3_yellow19(A_57,k2_struct_0(A_57),B_58)) = B_58
      | ~ m1_subset_1(B_58,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_57)))))
      | ~ v13_waybel_0(B_58,k3_yellow_1(k2_struct_0(A_57)))
      | ~ v2_waybel_0(B_58,k3_yellow_1(k2_struct_0(A_57)))
      | ~ v1_subset_1(B_58,u1_struct_0(k3_yellow_1(k2_struct_0(A_57))))
      | v1_xboole_0(B_58)
      | ~ l1_struct_0(A_57)
      | v2_struct_0(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_190,plain,
    ( k2_yellow19('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) = '#skF_2'
    | ~ v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
    | ~ v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
    | ~ v1_subset_1('#skF_2',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1'))))
    | v1_xboole_0('#skF_2')
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_185])).

tff(c_194,plain,
    ( k2_yellow19('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) = '#skF_2'
    | v1_xboole_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_44,c_42,c_40,c_190])).

tff(c_195,plain,(
    k2_yellow19('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_46,c_194])).

tff(c_30,plain,(
    ! [A_14,B_18,C_20] :
      ( r3_waybel_9(A_14,B_18,C_20)
      | ~ r1_waybel_7(A_14,k2_yellow19(A_14,B_18),C_20)
      | ~ m1_subset_1(C_20,u1_struct_0(A_14))
      | ~ l1_waybel_0(B_18,A_14)
      | ~ v7_waybel_0(B_18)
      | ~ v4_orders_2(B_18)
      | v2_struct_0(B_18)
      | ~ l1_pre_topc(A_14)
      | ~ v2_pre_topc(A_14)
      | v2_struct_0(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_199,plain,(
    ! [C_20] :
      ( r3_waybel_9('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),C_20)
      | ~ r1_waybel_7('#skF_1','#skF_2',C_20)
      | ~ m1_subset_1(C_20,u1_struct_0('#skF_1'))
      | ~ l1_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
      | ~ v7_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | ~ v4_orders_2(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_195,c_30])).

tff(c_206,plain,(
    ! [C_20] :
      ( r3_waybel_9('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),C_20)
      | ~ r1_waybel_7('#skF_1','#skF_2',C_20)
      | ~ m1_subset_1(C_20,u1_struct_0('#skF_1'))
      | ~ v7_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_136,c_184,c_199])).

tff(c_207,plain,(
    ! [C_20] :
      ( r3_waybel_9('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),C_20)
      | ~ r1_waybel_7('#skF_1','#skF_2',C_20)
      | ~ m1_subset_1(C_20,u1_struct_0('#skF_1'))
      | ~ v7_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_206])).

tff(c_212,plain,(
    ~ v7_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_207])).

tff(c_213,plain,(
    ! [A_59,B_60,C_61] :
      ( v7_waybel_0(k3_yellow19(A_59,B_60,C_61))
      | ~ m1_subset_1(C_61,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_60))))
      | ~ v13_waybel_0(C_61,k3_yellow_1(B_60))
      | ~ v2_waybel_0(C_61,k3_yellow_1(B_60))
      | ~ v1_subset_1(C_61,u1_struct_0(k3_yellow_1(B_60)))
      | v1_xboole_0(C_61)
      | ~ m1_subset_1(B_60,k1_zfmisc_1(u1_struct_0(A_59)))
      | v1_xboole_0(B_60)
      | ~ l1_struct_0(A_59)
      | v2_struct_0(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_218,plain,(
    ! [A_59] :
      ( v7_waybel_0(k3_yellow19(A_59,k2_struct_0('#skF_1'),'#skF_2'))
      | ~ v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
      | ~ v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
      | ~ v1_subset_1('#skF_2',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1'))))
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_59)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_59)
      | v2_struct_0(A_59) ) ),
    inference(resolution,[status(thm)],[c_38,c_213])).

tff(c_222,plain,(
    ! [A_59] :
      ( v7_waybel_0(k3_yellow19(A_59,k2_struct_0('#skF_1'),'#skF_2'))
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_59)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_59)
      | v2_struct_0(A_59) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_218])).

tff(c_224,plain,(
    ! [A_62] :
      ( v7_waybel_0(k3_yellow19(A_62,k2_struct_0('#skF_1'),'#skF_2'))
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_62)))
      | ~ l1_struct_0(A_62)
      | v2_struct_0(A_62) ) ),
    inference(negUnitSimplification,[status(thm)],[c_108,c_46,c_222])).

tff(c_228,plain,
    ( v7_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
    | v2_struct_0('#skF_1')
    | ~ l1_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_2,c_224])).

tff(c_231,plain,
    ( v7_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_228])).

tff(c_233,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_212,c_231])).

tff(c_234,plain,(
    ! [C_20] :
      ( v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | r3_waybel_9('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),C_20)
      | ~ r1_waybel_7('#skF_1','#skF_2',C_20)
      | ~ m1_subset_1(C_20,u1_struct_0('#skF_1')) ) ),
    inference(splitRight,[status(thm)],[c_207])).

tff(c_256,plain,(
    v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_234])).

tff(c_22,plain,(
    ! [A_8,B_9,C_10] :
      ( ~ v2_struct_0(k3_yellow19(A_8,B_9,C_10))
      | ~ m1_subset_1(C_10,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_9))))
      | ~ v13_waybel_0(C_10,k3_yellow_1(B_9))
      | ~ v2_waybel_0(C_10,k3_yellow_1(B_9))
      | v1_xboole_0(C_10)
      | ~ m1_subset_1(B_9,k1_zfmisc_1(u1_struct_0(A_8)))
      | v1_xboole_0(B_9)
      | ~ l1_struct_0(A_8)
      | v2_struct_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_261,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1')))))
    | ~ v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
    | ~ v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
    | v1_xboole_0('#skF_2')
    | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | v1_xboole_0(k2_struct_0('#skF_1'))
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_256,c_22])).

tff(c_264,plain,
    ( v1_xboole_0('#skF_2')
    | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | v1_xboole_0(k2_struct_0('#skF_1'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_42,c_40,c_38,c_261])).

tff(c_265,plain,(
    ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_108,c_46,c_264])).

tff(c_269,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_2,c_265])).

tff(c_273,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_269])).

tff(c_276,plain,(
    ! [C_67] :
      ( r3_waybel_9('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),C_67)
      | ~ r1_waybel_7('#skF_1','#skF_2',C_67)
      | ~ m1_subset_1(C_67,u1_struct_0('#skF_1')) ) ),
    inference(splitRight,[status(thm)],[c_234])).

tff(c_279,plain,
    ( ~ r1_waybel_7('#skF_1','#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_276,c_73])).

tff(c_283,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_74,c_279])).

tff(c_284,plain,(
    ~ r1_waybel_7('#skF_1','#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_285,plain,(
    r3_waybel_9('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_294,plain,(
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
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_299,plain,(
    ! [A_74] :
      ( v3_orders_2(k3_yellow19(A_74,k2_struct_0('#skF_1'),'#skF_2'))
      | ~ v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
      | ~ v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_74)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_74)
      | v2_struct_0(A_74) ) ),
    inference(resolution,[status(thm)],[c_38,c_294])).

tff(c_303,plain,(
    ! [A_74] :
      ( v3_orders_2(k3_yellow19(A_74,k2_struct_0('#skF_1'),'#skF_2'))
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_74)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_74)
      | v2_struct_0(A_74) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_299])).

tff(c_304,plain,(
    ! [A_74] :
      ( v3_orders_2(k3_yellow19(A_74,k2_struct_0('#skF_1'),'#skF_2'))
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_74)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_74)
      | v2_struct_0(A_74) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_303])).

tff(c_305,plain,(
    v1_xboole_0(k2_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_304])).

tff(c_308,plain,
    ( ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_305,c_6])).

tff(c_311,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_308])).

tff(c_314,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_4,c_311])).

tff(c_318,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_314])).

tff(c_322,plain,(
    ! [A_80] :
      ( v3_orders_2(k3_yellow19(A_80,k2_struct_0('#skF_1'),'#skF_2'))
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_80)))
      | ~ l1_struct_0(A_80)
      | v2_struct_0(A_80) ) ),
    inference(splitRight,[status(thm)],[c_304])).

tff(c_326,plain,
    ( v3_orders_2(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
    | v2_struct_0('#skF_1')
    | ~ l1_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_2,c_322])).

tff(c_329,plain,
    ( v3_orders_2(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
    | ~ l1_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_326])).

tff(c_330,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_329])).

tff(c_333,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_4,c_330])).

tff(c_337,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_333])).

tff(c_339,plain,(
    l1_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_329])).

tff(c_320,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_304])).

tff(c_340,plain,(
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
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_345,plain,(
    ! [A_81] :
      ( v4_orders_2(k3_yellow19(A_81,k2_struct_0('#skF_1'),'#skF_2'))
      | ~ v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
      | ~ v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_81)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_81)
      | v2_struct_0(A_81) ) ),
    inference(resolution,[status(thm)],[c_38,c_340])).

tff(c_349,plain,(
    ! [A_81] :
      ( v4_orders_2(k3_yellow19(A_81,k2_struct_0('#skF_1'),'#skF_2'))
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_81)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_81)
      | v2_struct_0(A_81) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_345])).

tff(c_351,plain,(
    ! [A_84] :
      ( v4_orders_2(k3_yellow19(A_84,k2_struct_0('#skF_1'),'#skF_2'))
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_84)))
      | ~ l1_struct_0(A_84)
      | v2_struct_0(A_84) ) ),
    inference(negUnitSimplification,[status(thm)],[c_320,c_46,c_349])).

tff(c_355,plain,
    ( v4_orders_2(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
    | v2_struct_0('#skF_1')
    | ~ l1_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_2,c_351])).

tff(c_358,plain,
    ( v4_orders_2(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_339,c_355])).

tff(c_359,plain,(
    v4_orders_2(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_358])).

tff(c_398,plain,(
    ! [A_93,B_94,C_95] :
      ( v7_waybel_0(k3_yellow19(A_93,B_94,C_95))
      | ~ m1_subset_1(C_95,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_94))))
      | ~ v13_waybel_0(C_95,k3_yellow_1(B_94))
      | ~ v2_waybel_0(C_95,k3_yellow_1(B_94))
      | ~ v1_subset_1(C_95,u1_struct_0(k3_yellow_1(B_94)))
      | v1_xboole_0(C_95)
      | ~ m1_subset_1(B_94,k1_zfmisc_1(u1_struct_0(A_93)))
      | v1_xboole_0(B_94)
      | ~ l1_struct_0(A_93)
      | v2_struct_0(A_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_403,plain,(
    ! [A_93] :
      ( v7_waybel_0(k3_yellow19(A_93,k2_struct_0('#skF_1'),'#skF_2'))
      | ~ v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
      | ~ v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
      | ~ v1_subset_1('#skF_2',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1'))))
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_93)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_93)
      | v2_struct_0(A_93) ) ),
    inference(resolution,[status(thm)],[c_38,c_398])).

tff(c_407,plain,(
    ! [A_93] :
      ( v7_waybel_0(k3_yellow19(A_93,k2_struct_0('#skF_1'),'#skF_2'))
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_93)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_93)
      | v2_struct_0(A_93) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_403])).

tff(c_409,plain,(
    ! [A_96] :
      ( v7_waybel_0(k3_yellow19(A_96,k2_struct_0('#skF_1'),'#skF_2'))
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_96)))
      | ~ l1_struct_0(A_96)
      | v2_struct_0(A_96) ) ),
    inference(negUnitSimplification,[status(thm)],[c_320,c_46,c_407])).

tff(c_413,plain,
    ( v7_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
    | v2_struct_0('#skF_1')
    | ~ l1_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_2,c_409])).

tff(c_416,plain,
    ( v7_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_339,c_413])).

tff(c_417,plain,(
    v7_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_416])).

tff(c_371,plain,(
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
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_376,plain,(
    ! [A_88] :
      ( l1_waybel_0(k3_yellow19(A_88,k2_struct_0('#skF_1'),'#skF_2'),A_88)
      | ~ v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
      | ~ v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_88)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_88)
      | v2_struct_0(A_88) ) ),
    inference(resolution,[status(thm)],[c_38,c_371])).

tff(c_380,plain,(
    ! [A_88] :
      ( l1_waybel_0(k3_yellow19(A_88,k2_struct_0('#skF_1'),'#skF_2'),A_88)
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_88)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_88)
      | v2_struct_0(A_88) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_376])).

tff(c_390,plain,(
    ! [A_92] :
      ( l1_waybel_0(k3_yellow19(A_92,k2_struct_0('#skF_1'),'#skF_2'),A_92)
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_92)))
      | ~ l1_struct_0(A_92)
      | v2_struct_0(A_92) ) ),
    inference(negUnitSimplification,[status(thm)],[c_320,c_46,c_380])).

tff(c_393,plain,
    ( l1_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | v2_struct_0('#skF_1')
    | ~ l1_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_2,c_390])).

tff(c_396,plain,
    ( l1_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_339,c_393])).

tff(c_397,plain,(
    l1_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_396])).

tff(c_418,plain,(
    ! [A_97,B_98] :
      ( k2_yellow19(A_97,k3_yellow19(A_97,k2_struct_0(A_97),B_98)) = B_98
      | ~ m1_subset_1(B_98,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_97)))))
      | ~ v13_waybel_0(B_98,k3_yellow_1(k2_struct_0(A_97)))
      | ~ v2_waybel_0(B_98,k3_yellow_1(k2_struct_0(A_97)))
      | ~ v1_subset_1(B_98,u1_struct_0(k3_yellow_1(k2_struct_0(A_97))))
      | v1_xboole_0(B_98)
      | ~ l1_struct_0(A_97)
      | v2_struct_0(A_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_423,plain,
    ( k2_yellow19('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) = '#skF_2'
    | ~ v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
    | ~ v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
    | ~ v1_subset_1('#skF_2',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1'))))
    | v1_xboole_0('#skF_2')
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_418])).

tff(c_427,plain,
    ( k2_yellow19('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) = '#skF_2'
    | v1_xboole_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_339,c_44,c_42,c_40,c_423])).

tff(c_428,plain,(
    k2_yellow19('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_46,c_427])).

tff(c_32,plain,(
    ! [A_14,B_18,C_20] :
      ( r1_waybel_7(A_14,k2_yellow19(A_14,B_18),C_20)
      | ~ r3_waybel_9(A_14,B_18,C_20)
      | ~ m1_subset_1(C_20,u1_struct_0(A_14))
      | ~ l1_waybel_0(B_18,A_14)
      | ~ v7_waybel_0(B_18)
      | ~ v4_orders_2(B_18)
      | v2_struct_0(B_18)
      | ~ l1_pre_topc(A_14)
      | ~ v2_pre_topc(A_14)
      | v2_struct_0(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_432,plain,(
    ! [C_20] :
      ( r1_waybel_7('#skF_1','#skF_2',C_20)
      | ~ r3_waybel_9('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),C_20)
      | ~ m1_subset_1(C_20,u1_struct_0('#skF_1'))
      | ~ l1_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
      | ~ v7_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | ~ v4_orders_2(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_428,c_32])).

tff(c_439,plain,(
    ! [C_20] :
      ( r1_waybel_7('#skF_1','#skF_2',C_20)
      | ~ r3_waybel_9('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),C_20)
      | ~ m1_subset_1(C_20,u1_struct_0('#skF_1'))
      | v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_359,c_417,c_397,c_432])).

tff(c_440,plain,(
    ! [C_20] :
      ( r1_waybel_7('#skF_1','#skF_2',C_20)
      | ~ r3_waybel_9('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),C_20)
      | ~ m1_subset_1(C_20,u1_struct_0('#skF_1'))
      | v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_439])).

tff(c_446,plain,(
    v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_440])).

tff(c_448,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1')))))
    | ~ v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
    | ~ v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
    | v1_xboole_0('#skF_2')
    | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | v1_xboole_0(k2_struct_0('#skF_1'))
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_446,c_22])).

tff(c_451,plain,
    ( v1_xboole_0('#skF_2')
    | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | v1_xboole_0(k2_struct_0('#skF_1'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_339,c_42,c_40,c_38,c_448])).

tff(c_452,plain,(
    ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_320,c_46,c_451])).

tff(c_455,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_2,c_452])).

tff(c_459,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_339,c_455])).

tff(c_468,plain,(
    ! [C_104] :
      ( r1_waybel_7('#skF_1','#skF_2',C_104)
      | ~ r3_waybel_9('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),C_104)
      | ~ m1_subset_1(C_104,u1_struct_0('#skF_1')) ) ),
    inference(splitRight,[status(thm)],[c_440])).

tff(c_474,plain,
    ( r1_waybel_7('#skF_1','#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_285,c_468])).

tff(c_478,plain,(
    r1_waybel_7('#skF_1','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_474])).

tff(c_480,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_284,c_478])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.33  % Computer   : n006.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % DateTime   : Tue Dec  1 17:22:07 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.83/1.39  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.83/1.41  
% 2.83/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.83/1.41  %$ r3_waybel_9 > r1_waybel_7 > v6_waybel_0 > v2_waybel_0 > v1_subset_1 > v13_waybel_0 > m1_subset_1 > l1_waybel_0 > v7_waybel_0 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k3_yellow19 > k2_yellow19 > #nlpp > u1_struct_0 > k3_yellow_1 > k3_lattice3 > k2_struct_0 > k1_zfmisc_1 > k1_lattice3 > #skF_2 > #skF_3 > #skF_1
% 2.83/1.41  
% 2.83/1.41  %Foreground sorts:
% 2.83/1.41  
% 2.83/1.41  
% 2.83/1.41  %Background operators:
% 2.83/1.41  
% 2.83/1.41  
% 2.83/1.41  %Foreground operators:
% 2.83/1.41  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.83/1.41  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 2.83/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.83/1.41  tff(k3_lattice3, type, k3_lattice3: $i > $i).
% 2.83/1.41  tff(v6_waybel_0, type, v6_waybel_0: ($i * $i) > $o).
% 2.83/1.41  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 2.83/1.41  tff(k3_yellow_1, type, k3_yellow_1: $i > $i).
% 2.83/1.41  tff(v2_waybel_0, type, v2_waybel_0: ($i * $i) > $o).
% 2.83/1.41  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.83/1.41  tff(v7_waybel_0, type, v7_waybel_0: $i > $o).
% 2.83/1.41  tff(r3_waybel_9, type, r3_waybel_9: ($i * $i * $i) > $o).
% 2.83/1.41  tff('#skF_2', type, '#skF_2': $i).
% 2.83/1.41  tff('#skF_3', type, '#skF_3': $i).
% 2.83/1.41  tff('#skF_1', type, '#skF_1': $i).
% 2.83/1.41  tff(k1_lattice3, type, k1_lattice3: $i > $i).
% 2.83/1.41  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.83/1.41  tff(r1_waybel_7, type, r1_waybel_7: ($i * $i * $i) > $o).
% 2.83/1.41  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.83/1.41  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.83/1.41  tff(k2_yellow19, type, k2_yellow19: ($i * $i) > $i).
% 2.83/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.83/1.41  tff(l1_waybel_0, type, l1_waybel_0: ($i * $i) > $o).
% 2.83/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.83/1.41  tff(k3_yellow19, type, k3_yellow19: ($i * $i * $i) > $i).
% 2.83/1.41  tff(v13_waybel_0, type, v13_waybel_0: ($i * $i) > $o).
% 2.83/1.41  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.83/1.41  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.83/1.41  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.83/1.41  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.83/1.41  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.83/1.41  
% 2.83/1.44  tff(f_195, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((((~v1_xboole_0(B) & v1_subset_1(B, u1_struct_0(k3_yellow_1(k2_struct_0(A))))) & v2_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & v13_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A)))))) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r3_waybel_9(A, k3_yellow19(A, k2_struct_0(A), B), C) <=> r1_waybel_7(A, B, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_yellow19)).
% 2.83/1.44  tff(f_33, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.83/1.44  tff(f_29, axiom, (![A]: (l1_struct_0(A) => m1_subset_1(k2_struct_0(A), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_struct_0)).
% 2.83/1.44  tff(f_97, axiom, (![A, B, C]: ((((((((~v2_struct_0(A) & l1_struct_0(A)) & ~v1_xboole_0(B)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) & ~v1_xboole_0(C)) & v2_waybel_0(C, k3_yellow_1(B))) & v13_waybel_0(C, k3_yellow_1(B))) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B))))) => (((~v2_struct_0(k3_yellow19(A, B, C)) & v3_orders_2(k3_yellow19(A, B, C))) & v4_orders_2(k3_yellow19(A, B, C))) & v6_waybel_0(k3_yellow19(A, B, C), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_yellow19)).
% 2.83/1.44  tff(f_41, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(k2_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc5_struct_0)).
% 2.83/1.44  tff(f_69, axiom, (![A, B, C]: ((((((((~v2_struct_0(A) & l1_struct_0(A)) & ~v1_xboole_0(B)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) & ~v1_xboole_0(C)) & v2_waybel_0(C, k3_yellow_1(B))) & v13_waybel_0(C, k3_yellow_1(B))) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B))))) => ((~v2_struct_0(k3_yellow19(A, B, C)) & v6_waybel_0(k3_yellow19(A, B, C), A)) & l1_waybel_0(k3_yellow19(A, B, C), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_yellow19)).
% 2.83/1.44  tff(f_168, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: (((((~v1_xboole_0(B) & v1_subset_1(B, u1_struct_0(k3_yellow_1(k2_struct_0(A))))) & v2_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & v13_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A)))))) => (B = k2_yellow19(A, k3_yellow19(A, k2_struct_0(A), B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t15_yellow19)).
% 2.83/1.44  tff(f_149, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r3_waybel_9(A, B, C) <=> r1_waybel_7(A, k2_yellow19(A, B), C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_yellow19)).
% 2.83/1.44  tff(f_125, axiom, (![A, B, C]: (((((((((~v2_struct_0(A) & l1_struct_0(A)) & ~v1_xboole_0(B)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) & ~v1_xboole_0(C)) & v1_subset_1(C, u1_struct_0(k3_yellow_1(B)))) & v2_waybel_0(C, k3_yellow_1(B))) & v13_waybel_0(C, k3_yellow_1(B))) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B))))) => ((~v2_struct_0(k3_yellow19(A, B, C)) & v6_waybel_0(k3_yellow19(A, B, C), A)) & v7_waybel_0(k3_yellow19(A, B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc5_yellow19)).
% 2.83/1.44  tff(c_36, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_195])).
% 2.83/1.44  tff(c_54, plain, (~r1_waybel_7('#skF_1', '#skF_2', '#skF_3') | ~r3_waybel_9('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_195])).
% 2.83/1.44  tff(c_73, plain, (~r3_waybel_9('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), '#skF_3')), inference(splitLeft, [status(thm)], [c_54])).
% 2.83/1.44  tff(c_60, plain, (r3_waybel_9('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), '#skF_3') | r1_waybel_7('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_195])).
% 2.83/1.44  tff(c_74, plain, (r1_waybel_7('#skF_1', '#skF_2', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_73, c_60])).
% 2.83/1.44  tff(c_48, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_195])).
% 2.83/1.44  tff(c_4, plain, (![A_2]: (l1_struct_0(A_2) | ~l1_pre_topc(A_2))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.83/1.44  tff(c_52, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_195])).
% 2.83/1.44  tff(c_2, plain, (![A_1]: (m1_subset_1(k2_struct_0(A_1), k1_zfmisc_1(u1_struct_0(A_1))) | ~l1_struct_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.83/1.44  tff(c_46, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_195])).
% 2.83/1.44  tff(c_42, plain, (v2_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_195])).
% 2.83/1.44  tff(c_40, plain, (v13_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_195])).
% 2.83/1.44  tff(c_38, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1')))))), inference(cnfTransformation, [status(thm)], [f_195])).
% 2.83/1.44  tff(c_82, plain, (![A_41, B_42, C_43]: (v4_orders_2(k3_yellow19(A_41, B_42, C_43)) | ~m1_subset_1(C_43, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_42)))) | ~v13_waybel_0(C_43, k3_yellow_1(B_42)) | ~v2_waybel_0(C_43, k3_yellow_1(B_42)) | v1_xboole_0(C_43) | ~m1_subset_1(B_42, k1_zfmisc_1(u1_struct_0(A_41))) | v1_xboole_0(B_42) | ~l1_struct_0(A_41) | v2_struct_0(A_41))), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.83/1.44  tff(c_87, plain, (![A_41]: (v4_orders_2(k3_yellow19(A_41, k2_struct_0('#skF_1'), '#skF_2')) | ~v13_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v2_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_41))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0(A_41) | v2_struct_0(A_41))), inference(resolution, [status(thm)], [c_38, c_82])).
% 2.83/1.44  tff(c_91, plain, (![A_41]: (v4_orders_2(k3_yellow19(A_41, k2_struct_0('#skF_1'), '#skF_2')) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_41))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0(A_41) | v2_struct_0(A_41))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_87])).
% 2.83/1.44  tff(c_92, plain, (![A_41]: (v4_orders_2(k3_yellow19(A_41, k2_struct_0('#skF_1'), '#skF_2')) | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_41))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0(A_41) | v2_struct_0(A_41))), inference(negUnitSimplification, [status(thm)], [c_46, c_91])).
% 2.83/1.44  tff(c_93, plain, (v1_xboole_0(k2_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_92])).
% 2.83/1.44  tff(c_6, plain, (![A_3]: (~v1_xboole_0(k2_struct_0(A_3)) | ~l1_struct_0(A_3) | v2_struct_0(A_3))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.83/1.44  tff(c_96, plain, (~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_93, c_6])).
% 2.83/1.44  tff(c_99, plain, (~l1_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_52, c_96])).
% 2.83/1.44  tff(c_102, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_4, c_99])).
% 2.83/1.44  tff(c_106, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_102])).
% 2.83/1.44  tff(c_109, plain, (![A_44]: (v4_orders_2(k3_yellow19(A_44, k2_struct_0('#skF_1'), '#skF_2')) | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_44))) | ~l1_struct_0(A_44) | v2_struct_0(A_44))), inference(splitRight, [status(thm)], [c_92])).
% 2.83/1.44  tff(c_113, plain, (v4_orders_2(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0('#skF_1') | ~l1_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_2, c_109])).
% 2.83/1.44  tff(c_116, plain, (v4_orders_2(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | ~l1_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_52, c_113])).
% 2.83/1.44  tff(c_128, plain, (~l1_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_116])).
% 2.83/1.44  tff(c_131, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_4, c_128])).
% 2.83/1.44  tff(c_135, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_131])).
% 2.83/1.44  tff(c_137, plain, (l1_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_116])).
% 2.83/1.44  tff(c_108, plain, (~v1_xboole_0(k2_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_92])).
% 2.83/1.44  tff(c_50, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_195])).
% 2.83/1.44  tff(c_136, plain, (v4_orders_2(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))), inference(splitRight, [status(thm)], [c_116])).
% 2.83/1.44  tff(c_166, plain, (![A_53, B_54, C_55]: (l1_waybel_0(k3_yellow19(A_53, B_54, C_55), A_53) | ~m1_subset_1(C_55, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_54)))) | ~v13_waybel_0(C_55, k3_yellow_1(B_54)) | ~v2_waybel_0(C_55, k3_yellow_1(B_54)) | v1_xboole_0(C_55) | ~m1_subset_1(B_54, k1_zfmisc_1(u1_struct_0(A_53))) | v1_xboole_0(B_54) | ~l1_struct_0(A_53) | v2_struct_0(A_53))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.83/1.44  tff(c_171, plain, (![A_53]: (l1_waybel_0(k3_yellow19(A_53, k2_struct_0('#skF_1'), '#skF_2'), A_53) | ~v13_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v2_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_53))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0(A_53) | v2_struct_0(A_53))), inference(resolution, [status(thm)], [c_38, c_166])).
% 2.83/1.44  tff(c_175, plain, (![A_53]: (l1_waybel_0(k3_yellow19(A_53, k2_struct_0('#skF_1'), '#skF_2'), A_53) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_53))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0(A_53) | v2_struct_0(A_53))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_171])).
% 2.83/1.44  tff(c_177, plain, (![A_56]: (l1_waybel_0(k3_yellow19(A_56, k2_struct_0('#skF_1'), '#skF_2'), A_56) | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_56))) | ~l1_struct_0(A_56) | v2_struct_0(A_56))), inference(negUnitSimplification, [status(thm)], [c_108, c_46, c_175])).
% 2.83/1.44  tff(c_180, plain, (l1_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | v2_struct_0('#skF_1') | ~l1_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_2, c_177])).
% 2.83/1.44  tff(c_183, plain, (l1_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_137, c_180])).
% 2.83/1.44  tff(c_184, plain, (l1_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_52, c_183])).
% 2.83/1.44  tff(c_44, plain, (v1_subset_1('#skF_2', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_195])).
% 2.83/1.44  tff(c_185, plain, (![A_57, B_58]: (k2_yellow19(A_57, k3_yellow19(A_57, k2_struct_0(A_57), B_58))=B_58 | ~m1_subset_1(B_58, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_57))))) | ~v13_waybel_0(B_58, k3_yellow_1(k2_struct_0(A_57))) | ~v2_waybel_0(B_58, k3_yellow_1(k2_struct_0(A_57))) | ~v1_subset_1(B_58, u1_struct_0(k3_yellow_1(k2_struct_0(A_57)))) | v1_xboole_0(B_58) | ~l1_struct_0(A_57) | v2_struct_0(A_57))), inference(cnfTransformation, [status(thm)], [f_168])).
% 2.83/1.44  tff(c_190, plain, (k2_yellow19('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))='#skF_2' | ~v13_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v2_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v1_subset_1('#skF_2', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1')))) | v1_xboole_0('#skF_2') | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_38, c_185])).
% 2.83/1.44  tff(c_194, plain, (k2_yellow19('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))='#skF_2' | v1_xboole_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_137, c_44, c_42, c_40, c_190])).
% 2.83/1.44  tff(c_195, plain, (k2_yellow19('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_52, c_46, c_194])).
% 2.83/1.44  tff(c_30, plain, (![A_14, B_18, C_20]: (r3_waybel_9(A_14, B_18, C_20) | ~r1_waybel_7(A_14, k2_yellow19(A_14, B_18), C_20) | ~m1_subset_1(C_20, u1_struct_0(A_14)) | ~l1_waybel_0(B_18, A_14) | ~v7_waybel_0(B_18) | ~v4_orders_2(B_18) | v2_struct_0(B_18) | ~l1_pre_topc(A_14) | ~v2_pre_topc(A_14) | v2_struct_0(A_14))), inference(cnfTransformation, [status(thm)], [f_149])).
% 2.83/1.44  tff(c_199, plain, (![C_20]: (r3_waybel_9('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), C_20) | ~r1_waybel_7('#skF_1', '#skF_2', C_20) | ~m1_subset_1(C_20, u1_struct_0('#skF_1')) | ~l1_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~v7_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | ~v4_orders_2(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_195, c_30])).
% 2.83/1.44  tff(c_206, plain, (![C_20]: (r3_waybel_9('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), C_20) | ~r1_waybel_7('#skF_1', '#skF_2', C_20) | ~m1_subset_1(C_20, u1_struct_0('#skF_1')) | ~v7_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_136, c_184, c_199])).
% 2.83/1.44  tff(c_207, plain, (![C_20]: (r3_waybel_9('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), C_20) | ~r1_waybel_7('#skF_1', '#skF_2', C_20) | ~m1_subset_1(C_20, u1_struct_0('#skF_1')) | ~v7_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_52, c_206])).
% 2.83/1.44  tff(c_212, plain, (~v7_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))), inference(splitLeft, [status(thm)], [c_207])).
% 2.83/1.44  tff(c_213, plain, (![A_59, B_60, C_61]: (v7_waybel_0(k3_yellow19(A_59, B_60, C_61)) | ~m1_subset_1(C_61, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_60)))) | ~v13_waybel_0(C_61, k3_yellow_1(B_60)) | ~v2_waybel_0(C_61, k3_yellow_1(B_60)) | ~v1_subset_1(C_61, u1_struct_0(k3_yellow_1(B_60))) | v1_xboole_0(C_61) | ~m1_subset_1(B_60, k1_zfmisc_1(u1_struct_0(A_59))) | v1_xboole_0(B_60) | ~l1_struct_0(A_59) | v2_struct_0(A_59))), inference(cnfTransformation, [status(thm)], [f_125])).
% 2.83/1.44  tff(c_218, plain, (![A_59]: (v7_waybel_0(k3_yellow19(A_59, k2_struct_0('#skF_1'), '#skF_2')) | ~v13_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v2_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v1_subset_1('#skF_2', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1')))) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_59))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0(A_59) | v2_struct_0(A_59))), inference(resolution, [status(thm)], [c_38, c_213])).
% 2.83/1.44  tff(c_222, plain, (![A_59]: (v7_waybel_0(k3_yellow19(A_59, k2_struct_0('#skF_1'), '#skF_2')) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_59))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0(A_59) | v2_struct_0(A_59))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_40, c_218])).
% 2.83/1.44  tff(c_224, plain, (![A_62]: (v7_waybel_0(k3_yellow19(A_62, k2_struct_0('#skF_1'), '#skF_2')) | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_62))) | ~l1_struct_0(A_62) | v2_struct_0(A_62))), inference(negUnitSimplification, [status(thm)], [c_108, c_46, c_222])).
% 2.83/1.44  tff(c_228, plain, (v7_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0('#skF_1') | ~l1_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_2, c_224])).
% 2.83/1.44  tff(c_231, plain, (v7_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_137, c_228])).
% 2.83/1.44  tff(c_233, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_212, c_231])).
% 2.83/1.44  tff(c_234, plain, (![C_20]: (v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | r3_waybel_9('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), C_20) | ~r1_waybel_7('#skF_1', '#skF_2', C_20) | ~m1_subset_1(C_20, u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_207])).
% 2.83/1.44  tff(c_256, plain, (v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))), inference(splitLeft, [status(thm)], [c_234])).
% 2.83/1.44  tff(c_22, plain, (![A_8, B_9, C_10]: (~v2_struct_0(k3_yellow19(A_8, B_9, C_10)) | ~m1_subset_1(C_10, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_9)))) | ~v13_waybel_0(C_10, k3_yellow_1(B_9)) | ~v2_waybel_0(C_10, k3_yellow_1(B_9)) | v1_xboole_0(C_10) | ~m1_subset_1(B_9, k1_zfmisc_1(u1_struct_0(A_8))) | v1_xboole_0(B_9) | ~l1_struct_0(A_8) | v2_struct_0(A_8))), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.83/1.44  tff(c_261, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1'))))) | ~v13_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v2_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_256, c_22])).
% 2.83/1.44  tff(c_264, plain, (v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | v1_xboole_0(k2_struct_0('#skF_1')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_137, c_42, c_40, c_38, c_261])).
% 2.83/1.44  tff(c_265, plain, (~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_52, c_108, c_46, c_264])).
% 2.83/1.44  tff(c_269, plain, (~l1_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_2, c_265])).
% 2.83/1.44  tff(c_273, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_137, c_269])).
% 2.83/1.44  tff(c_276, plain, (![C_67]: (r3_waybel_9('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), C_67) | ~r1_waybel_7('#skF_1', '#skF_2', C_67) | ~m1_subset_1(C_67, u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_234])).
% 2.83/1.44  tff(c_279, plain, (~r1_waybel_7('#skF_1', '#skF_2', '#skF_3') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_276, c_73])).
% 2.83/1.44  tff(c_283, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_74, c_279])).
% 2.83/1.44  tff(c_284, plain, (~r1_waybel_7('#skF_1', '#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_54])).
% 2.83/1.44  tff(c_285, plain, (r3_waybel_9('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), '#skF_3')), inference(splitRight, [status(thm)], [c_54])).
% 2.83/1.44  tff(c_294, plain, (![A_74, B_75, C_76]: (v3_orders_2(k3_yellow19(A_74, B_75, C_76)) | ~m1_subset_1(C_76, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_75)))) | ~v13_waybel_0(C_76, k3_yellow_1(B_75)) | ~v2_waybel_0(C_76, k3_yellow_1(B_75)) | v1_xboole_0(C_76) | ~m1_subset_1(B_75, k1_zfmisc_1(u1_struct_0(A_74))) | v1_xboole_0(B_75) | ~l1_struct_0(A_74) | v2_struct_0(A_74))), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.83/1.44  tff(c_299, plain, (![A_74]: (v3_orders_2(k3_yellow19(A_74, k2_struct_0('#skF_1'), '#skF_2')) | ~v13_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v2_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_74))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0(A_74) | v2_struct_0(A_74))), inference(resolution, [status(thm)], [c_38, c_294])).
% 2.83/1.44  tff(c_303, plain, (![A_74]: (v3_orders_2(k3_yellow19(A_74, k2_struct_0('#skF_1'), '#skF_2')) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_74))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0(A_74) | v2_struct_0(A_74))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_299])).
% 2.83/1.44  tff(c_304, plain, (![A_74]: (v3_orders_2(k3_yellow19(A_74, k2_struct_0('#skF_1'), '#skF_2')) | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_74))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0(A_74) | v2_struct_0(A_74))), inference(negUnitSimplification, [status(thm)], [c_46, c_303])).
% 2.83/1.44  tff(c_305, plain, (v1_xboole_0(k2_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_304])).
% 2.83/1.44  tff(c_308, plain, (~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_305, c_6])).
% 2.83/1.44  tff(c_311, plain, (~l1_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_52, c_308])).
% 2.83/1.44  tff(c_314, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_4, c_311])).
% 2.83/1.44  tff(c_318, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_314])).
% 2.83/1.44  tff(c_322, plain, (![A_80]: (v3_orders_2(k3_yellow19(A_80, k2_struct_0('#skF_1'), '#skF_2')) | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_80))) | ~l1_struct_0(A_80) | v2_struct_0(A_80))), inference(splitRight, [status(thm)], [c_304])).
% 2.83/1.44  tff(c_326, plain, (v3_orders_2(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0('#skF_1') | ~l1_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_2, c_322])).
% 2.83/1.44  tff(c_329, plain, (v3_orders_2(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | ~l1_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_52, c_326])).
% 2.83/1.44  tff(c_330, plain, (~l1_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_329])).
% 2.83/1.44  tff(c_333, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_4, c_330])).
% 2.83/1.44  tff(c_337, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_333])).
% 2.83/1.44  tff(c_339, plain, (l1_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_329])).
% 2.83/1.44  tff(c_320, plain, (~v1_xboole_0(k2_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_304])).
% 2.83/1.44  tff(c_340, plain, (![A_81, B_82, C_83]: (v4_orders_2(k3_yellow19(A_81, B_82, C_83)) | ~m1_subset_1(C_83, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_82)))) | ~v13_waybel_0(C_83, k3_yellow_1(B_82)) | ~v2_waybel_0(C_83, k3_yellow_1(B_82)) | v1_xboole_0(C_83) | ~m1_subset_1(B_82, k1_zfmisc_1(u1_struct_0(A_81))) | v1_xboole_0(B_82) | ~l1_struct_0(A_81) | v2_struct_0(A_81))), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.83/1.44  tff(c_345, plain, (![A_81]: (v4_orders_2(k3_yellow19(A_81, k2_struct_0('#skF_1'), '#skF_2')) | ~v13_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v2_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_81))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0(A_81) | v2_struct_0(A_81))), inference(resolution, [status(thm)], [c_38, c_340])).
% 2.83/1.44  tff(c_349, plain, (![A_81]: (v4_orders_2(k3_yellow19(A_81, k2_struct_0('#skF_1'), '#skF_2')) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_81))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0(A_81) | v2_struct_0(A_81))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_345])).
% 2.83/1.44  tff(c_351, plain, (![A_84]: (v4_orders_2(k3_yellow19(A_84, k2_struct_0('#skF_1'), '#skF_2')) | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_84))) | ~l1_struct_0(A_84) | v2_struct_0(A_84))), inference(negUnitSimplification, [status(thm)], [c_320, c_46, c_349])).
% 2.83/1.44  tff(c_355, plain, (v4_orders_2(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0('#skF_1') | ~l1_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_2, c_351])).
% 2.83/1.44  tff(c_358, plain, (v4_orders_2(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_339, c_355])).
% 2.83/1.44  tff(c_359, plain, (v4_orders_2(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_52, c_358])).
% 2.83/1.44  tff(c_398, plain, (![A_93, B_94, C_95]: (v7_waybel_0(k3_yellow19(A_93, B_94, C_95)) | ~m1_subset_1(C_95, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_94)))) | ~v13_waybel_0(C_95, k3_yellow_1(B_94)) | ~v2_waybel_0(C_95, k3_yellow_1(B_94)) | ~v1_subset_1(C_95, u1_struct_0(k3_yellow_1(B_94))) | v1_xboole_0(C_95) | ~m1_subset_1(B_94, k1_zfmisc_1(u1_struct_0(A_93))) | v1_xboole_0(B_94) | ~l1_struct_0(A_93) | v2_struct_0(A_93))), inference(cnfTransformation, [status(thm)], [f_125])).
% 2.83/1.44  tff(c_403, plain, (![A_93]: (v7_waybel_0(k3_yellow19(A_93, k2_struct_0('#skF_1'), '#skF_2')) | ~v13_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v2_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v1_subset_1('#skF_2', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1')))) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_93))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0(A_93) | v2_struct_0(A_93))), inference(resolution, [status(thm)], [c_38, c_398])).
% 2.83/1.44  tff(c_407, plain, (![A_93]: (v7_waybel_0(k3_yellow19(A_93, k2_struct_0('#skF_1'), '#skF_2')) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_93))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0(A_93) | v2_struct_0(A_93))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_40, c_403])).
% 2.83/1.44  tff(c_409, plain, (![A_96]: (v7_waybel_0(k3_yellow19(A_96, k2_struct_0('#skF_1'), '#skF_2')) | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_96))) | ~l1_struct_0(A_96) | v2_struct_0(A_96))), inference(negUnitSimplification, [status(thm)], [c_320, c_46, c_407])).
% 2.83/1.44  tff(c_413, plain, (v7_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0('#skF_1') | ~l1_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_2, c_409])).
% 2.83/1.44  tff(c_416, plain, (v7_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_339, c_413])).
% 2.83/1.44  tff(c_417, plain, (v7_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_52, c_416])).
% 2.83/1.44  tff(c_371, plain, (![A_88, B_89, C_90]: (l1_waybel_0(k3_yellow19(A_88, B_89, C_90), A_88) | ~m1_subset_1(C_90, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_89)))) | ~v13_waybel_0(C_90, k3_yellow_1(B_89)) | ~v2_waybel_0(C_90, k3_yellow_1(B_89)) | v1_xboole_0(C_90) | ~m1_subset_1(B_89, k1_zfmisc_1(u1_struct_0(A_88))) | v1_xboole_0(B_89) | ~l1_struct_0(A_88) | v2_struct_0(A_88))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.83/1.44  tff(c_376, plain, (![A_88]: (l1_waybel_0(k3_yellow19(A_88, k2_struct_0('#skF_1'), '#skF_2'), A_88) | ~v13_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v2_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_88))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0(A_88) | v2_struct_0(A_88))), inference(resolution, [status(thm)], [c_38, c_371])).
% 2.83/1.44  tff(c_380, plain, (![A_88]: (l1_waybel_0(k3_yellow19(A_88, k2_struct_0('#skF_1'), '#skF_2'), A_88) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_88))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0(A_88) | v2_struct_0(A_88))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_376])).
% 2.83/1.44  tff(c_390, plain, (![A_92]: (l1_waybel_0(k3_yellow19(A_92, k2_struct_0('#skF_1'), '#skF_2'), A_92) | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_92))) | ~l1_struct_0(A_92) | v2_struct_0(A_92))), inference(negUnitSimplification, [status(thm)], [c_320, c_46, c_380])).
% 2.83/1.44  tff(c_393, plain, (l1_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | v2_struct_0('#skF_1') | ~l1_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_2, c_390])).
% 2.83/1.44  tff(c_396, plain, (l1_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_339, c_393])).
% 2.83/1.44  tff(c_397, plain, (l1_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_52, c_396])).
% 2.83/1.44  tff(c_418, plain, (![A_97, B_98]: (k2_yellow19(A_97, k3_yellow19(A_97, k2_struct_0(A_97), B_98))=B_98 | ~m1_subset_1(B_98, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_97))))) | ~v13_waybel_0(B_98, k3_yellow_1(k2_struct_0(A_97))) | ~v2_waybel_0(B_98, k3_yellow_1(k2_struct_0(A_97))) | ~v1_subset_1(B_98, u1_struct_0(k3_yellow_1(k2_struct_0(A_97)))) | v1_xboole_0(B_98) | ~l1_struct_0(A_97) | v2_struct_0(A_97))), inference(cnfTransformation, [status(thm)], [f_168])).
% 2.83/1.44  tff(c_423, plain, (k2_yellow19('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))='#skF_2' | ~v13_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v2_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v1_subset_1('#skF_2', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1')))) | v1_xboole_0('#skF_2') | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_38, c_418])).
% 2.83/1.44  tff(c_427, plain, (k2_yellow19('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))='#skF_2' | v1_xboole_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_339, c_44, c_42, c_40, c_423])).
% 2.83/1.44  tff(c_428, plain, (k2_yellow19('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_52, c_46, c_427])).
% 2.83/1.44  tff(c_32, plain, (![A_14, B_18, C_20]: (r1_waybel_7(A_14, k2_yellow19(A_14, B_18), C_20) | ~r3_waybel_9(A_14, B_18, C_20) | ~m1_subset_1(C_20, u1_struct_0(A_14)) | ~l1_waybel_0(B_18, A_14) | ~v7_waybel_0(B_18) | ~v4_orders_2(B_18) | v2_struct_0(B_18) | ~l1_pre_topc(A_14) | ~v2_pre_topc(A_14) | v2_struct_0(A_14))), inference(cnfTransformation, [status(thm)], [f_149])).
% 2.83/1.44  tff(c_432, plain, (![C_20]: (r1_waybel_7('#skF_1', '#skF_2', C_20) | ~r3_waybel_9('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), C_20) | ~m1_subset_1(C_20, u1_struct_0('#skF_1')) | ~l1_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~v7_waybel_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | ~v4_orders_2(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_428, c_32])).
% 2.83/1.44  tff(c_439, plain, (![C_20]: (r1_waybel_7('#skF_1', '#skF_2', C_20) | ~r3_waybel_9('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), C_20) | ~m1_subset_1(C_20, u1_struct_0('#skF_1')) | v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_359, c_417, c_397, c_432])).
% 2.83/1.44  tff(c_440, plain, (![C_20]: (r1_waybel_7('#skF_1', '#skF_2', C_20) | ~r3_waybel_9('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), C_20) | ~m1_subset_1(C_20, u1_struct_0('#skF_1')) | v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_52, c_439])).
% 2.83/1.44  tff(c_446, plain, (v2_struct_0(k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))), inference(splitLeft, [status(thm)], [c_440])).
% 2.83/1.44  tff(c_448, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1'))))) | ~v13_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v2_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_446, c_22])).
% 2.83/1.44  tff(c_451, plain, (v1_xboole_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | v1_xboole_0(k2_struct_0('#skF_1')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_339, c_42, c_40, c_38, c_448])).
% 2.83/1.44  tff(c_452, plain, (~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_52, c_320, c_46, c_451])).
% 2.83/1.44  tff(c_455, plain, (~l1_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_2, c_452])).
% 2.83/1.44  tff(c_459, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_339, c_455])).
% 2.83/1.44  tff(c_468, plain, (![C_104]: (r1_waybel_7('#skF_1', '#skF_2', C_104) | ~r3_waybel_9('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'), C_104) | ~m1_subset_1(C_104, u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_440])).
% 2.83/1.44  tff(c_474, plain, (r1_waybel_7('#skF_1', '#skF_2', '#skF_3') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_285, c_468])).
% 2.83/1.44  tff(c_478, plain, (r1_waybel_7('#skF_1', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_474])).
% 2.83/1.44  tff(c_480, plain, $false, inference(negUnitSimplification, [status(thm)], [c_284, c_478])).
% 2.83/1.44  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.83/1.44  
% 2.83/1.44  Inference rules
% 2.83/1.44  ----------------------
% 2.83/1.44  #Ref     : 0
% 2.83/1.44  #Sup     : 62
% 2.83/1.44  #Fact    : 0
% 2.83/1.44  #Define  : 0
% 2.83/1.44  #Split   : 10
% 2.83/1.44  #Chain   : 0
% 2.83/1.44  #Close   : 0
% 2.83/1.44  
% 2.83/1.44  Ordering : KBO
% 2.83/1.44  
% 2.83/1.44  Simplification rules
% 2.83/1.44  ----------------------
% 2.83/1.44  #Subsume      : 6
% 2.83/1.44  #Demod        : 81
% 2.83/1.44  #Tautology    : 14
% 2.83/1.44  #SimpNegUnit  : 36
% 2.83/1.44  #BackRed      : 0
% 2.83/1.44  
% 2.83/1.44  #Partial instantiations: 0
% 2.83/1.44  #Strategies tried      : 1
% 2.83/1.44  
% 2.83/1.44  Timing (in seconds)
% 2.83/1.44  ----------------------
% 2.83/1.44  Preprocessing        : 0.34
% 2.83/1.44  Parsing              : 0.19
% 2.83/1.44  CNF conversion       : 0.02
% 2.83/1.44  Main loop            : 0.32
% 2.83/1.44  Inferencing          : 0.12
% 2.83/1.44  Reduction            : 0.10
% 2.83/1.44  Demodulation         : 0.06
% 2.83/1.44  BG Simplification    : 0.02
% 2.83/1.44  Subsumption          : 0.06
% 2.83/1.44  Abstraction          : 0.01
% 2.83/1.44  MUC search           : 0.00
% 2.83/1.44  Cooper               : 0.00
% 2.83/1.45  Total                : 0.71
% 2.83/1.45  Index Insertion      : 0.00
% 2.83/1.45  Index Deletion       : 0.00
% 2.83/1.45  Index Matching       : 0.00
% 2.83/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
