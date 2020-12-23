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
% DateTime   : Thu Dec  3 10:31:05 EST 2020

% Result     : Theorem 2.34s
% Output     : CNFRefutation 2.34s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 221 expanded)
%              Number of leaves         :   38 ( 111 expanded)
%              Depth                    :   12
%              Number of atoms          :  262 (1323 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   18 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_waybel_7 > r1_waybel_7 > r1_waybel_3 > v3_waybel_7 > v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_orders_2 > l1_pre_topc > l1_orders_2 > #nlpp > u1_struct_0 > u1_pre_topc > k3_yellow_1 > k2_yellow_1 > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_2 > #skF_6 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_orders_2,type,(
    v1_orders_2: $i > $o )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff(k2_yellow_1,type,(
    k2_yellow_1: $i > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(r1_waybel_7,type,(
    r1_waybel_7: ( $i * $i * $i ) > $o )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(r2_waybel_7,type,(
    r2_waybel_7: ( $i * $i * $i ) > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v13_waybel_0,type,(
    v13_waybel_0: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(v3_waybel_7,type,(
    v3_waybel_7: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(r1_waybel_3,type,(
    r1_waybel_3: ( $i * $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_179,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(k2_yellow_1(u1_pre_topc(A))))
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(k2_yellow_1(u1_pre_topc(A))))
               => ( r1_waybel_3(k2_yellow_1(u1_pre_topc(A)),B,C)
                 => ! [D] :
                      ( ( ~ v1_xboole_0(D)
                        & v2_waybel_0(D,k3_yellow_1(u1_struct_0(A)))
                        & v13_waybel_0(D,k3_yellow_1(u1_struct_0(A)))
                        & v3_waybel_7(D,k3_yellow_1(u1_struct_0(A)))
                        & m1_subset_1(D,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(A))))) )
                     => ~ ( r2_hidden(B,D)
                          & ! [E] :
                              ( m1_subset_1(E,u1_struct_0(A))
                             => ~ ( r2_hidden(E,C)
                                  & r2_waybel_7(A,D,E) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_waybel_7)).

tff(f_46,axiom,(
    ! [A] :
      ( ~ v2_struct_0(k3_yellow_1(A))
      & v1_orders_2(k3_yellow_1(A))
      & v3_orders_2(k3_yellow_1(A))
      & v4_orders_2(k3_yellow_1(A))
      & v5_orders_2(k3_yellow_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_yellow_1)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_orders_2(k3_yellow_1(A))
      & l1_orders_2(k3_yellow_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_yellow_1)).

tff(f_78,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( ~ v1_xboole_0(B)
              & v2_waybel_0(B,A)
              & v13_waybel_0(B,A)
              & v3_waybel_7(B,A) )
           => ( ~ v1_xboole_0(B)
              & v1_subset_1(B,u1_struct_0(A))
              & v2_waybel_0(B,A)
              & v13_waybel_0(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_waybel_7)).

tff(f_140,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(k2_yellow_1(u1_pre_topc(A))))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(k2_yellow_1(u1_pre_topc(A))))
             => ( r1_waybel_3(k2_yellow_1(u1_pre_topc(A)),B,C)
               => ! [D] :
                    ( ( ~ v1_xboole_0(D)
                      & v1_subset_1(D,u1_struct_0(k3_yellow_1(u1_struct_0(A))))
                      & v2_waybel_0(D,k3_yellow_1(u1_struct_0(A)))
                      & v13_waybel_0(D,k3_yellow_1(u1_struct_0(A)))
                      & m1_subset_1(D,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(A))))) )
                   => ~ ( r2_hidden(B,D)
                        & ! [E] :
                            ( m1_subset_1(E,u1_struct_0(A))
                           => ~ ( r2_hidden(E,C)
                                & r1_waybel_7(A,D,E) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_waybel_7)).

tff(f_102,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v2_waybel_0(B,k3_yellow_1(u1_struct_0(A)))
            & v13_waybel_0(B,k3_yellow_1(u1_struct_0(A)))
            & v3_waybel_7(B,k3_yellow_1(u1_struct_0(A)))
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(A))))) )
         => ! [C] :
              ( r1_waybel_7(A,B,C)
            <=> r2_waybel_7(A,B,C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_waybel_7)).

tff(c_56,plain,(
    m1_subset_1('#skF_4',u1_struct_0(k2_yellow_1(u1_pre_topc('#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_54,plain,(
    m1_subset_1('#skF_5',u1_struct_0(k2_yellow_1(u1_pre_topc('#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_40,plain,(
    r2_hidden('#skF_4','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_52,plain,(
    r1_waybel_3(k2_yellow_1(u1_pre_topc('#skF_3')),'#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_62,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_50,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_60,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_58,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_10,plain,(
    ! [A_6] : ~ v2_struct_0(k3_yellow_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_14,plain,(
    ! [A_6] : v3_orders_2(k3_yellow_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_16,plain,(
    ! [A_6] : v4_orders_2(k3_yellow_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_18,plain,(
    ! [A_6] : v5_orders_2(k3_yellow_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_8,plain,(
    ! [A_5] : l1_orders_2(k3_yellow_1(A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_48,plain,(
    v2_waybel_0('#skF_6',k3_yellow_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_46,plain,(
    v13_waybel_0('#skF_6',k3_yellow_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_44,plain,(
    v3_waybel_7('#skF_6',k3_yellow_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_42,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0('#skF_3'))))) ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_81,plain,(
    ! [B_84,A_85] :
      ( v1_subset_1(B_84,u1_struct_0(A_85))
      | ~ v3_waybel_7(B_84,A_85)
      | ~ v13_waybel_0(B_84,A_85)
      | ~ v2_waybel_0(B_84,A_85)
      | v1_xboole_0(B_84)
      | ~ m1_subset_1(B_84,k1_zfmisc_1(u1_struct_0(A_85)))
      | ~ l1_orders_2(A_85)
      | ~ v5_orders_2(A_85)
      | ~ v4_orders_2(A_85)
      | ~ v3_orders_2(A_85)
      | v2_struct_0(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_84,plain,
    ( v1_subset_1('#skF_6',u1_struct_0(k3_yellow_1(u1_struct_0('#skF_3'))))
    | ~ v3_waybel_7('#skF_6',k3_yellow_1(u1_struct_0('#skF_3')))
    | ~ v13_waybel_0('#skF_6',k3_yellow_1(u1_struct_0('#skF_3')))
    | ~ v2_waybel_0('#skF_6',k3_yellow_1(u1_struct_0('#skF_3')))
    | v1_xboole_0('#skF_6')
    | ~ l1_orders_2(k3_yellow_1(u1_struct_0('#skF_3')))
    | ~ v5_orders_2(k3_yellow_1(u1_struct_0('#skF_3')))
    | ~ v4_orders_2(k3_yellow_1(u1_struct_0('#skF_3')))
    | ~ v3_orders_2(k3_yellow_1(u1_struct_0('#skF_3')))
    | v2_struct_0(k3_yellow_1(u1_struct_0('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_42,c_81])).

tff(c_87,plain,
    ( v1_subset_1('#skF_6',u1_struct_0(k3_yellow_1(u1_struct_0('#skF_3'))))
    | v1_xboole_0('#skF_6')
    | v2_struct_0(k3_yellow_1(u1_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_16,c_18,c_8,c_48,c_46,c_44,c_84])).

tff(c_88,plain,(
    v1_subset_1('#skF_6',u1_struct_0(k3_yellow_1(u1_struct_0('#skF_3')))) ),
    inference(negUnitSimplification,[status(thm)],[c_10,c_50,c_87])).

tff(c_121,plain,(
    ! [A_99,D_100,B_101,C_102] :
      ( r1_waybel_7(A_99,D_100,'#skF_2'(A_99,B_101,C_102,D_100))
      | ~ r2_hidden(B_101,D_100)
      | ~ m1_subset_1(D_100,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(A_99)))))
      | ~ v13_waybel_0(D_100,k3_yellow_1(u1_struct_0(A_99)))
      | ~ v2_waybel_0(D_100,k3_yellow_1(u1_struct_0(A_99)))
      | ~ v1_subset_1(D_100,u1_struct_0(k3_yellow_1(u1_struct_0(A_99))))
      | v1_xboole_0(D_100)
      | ~ r1_waybel_3(k2_yellow_1(u1_pre_topc(A_99)),B_101,C_102)
      | ~ m1_subset_1(C_102,u1_struct_0(k2_yellow_1(u1_pre_topc(A_99))))
      | ~ m1_subset_1(B_101,u1_struct_0(k2_yellow_1(u1_pre_topc(A_99))))
      | ~ l1_pre_topc(A_99)
      | ~ v2_pre_topc(A_99)
      | v2_struct_0(A_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_123,plain,(
    ! [B_101,C_102] :
      ( r1_waybel_7('#skF_3','#skF_6','#skF_2'('#skF_3',B_101,C_102,'#skF_6'))
      | ~ r2_hidden(B_101,'#skF_6')
      | ~ v13_waybel_0('#skF_6',k3_yellow_1(u1_struct_0('#skF_3')))
      | ~ v2_waybel_0('#skF_6',k3_yellow_1(u1_struct_0('#skF_3')))
      | ~ v1_subset_1('#skF_6',u1_struct_0(k3_yellow_1(u1_struct_0('#skF_3'))))
      | v1_xboole_0('#skF_6')
      | ~ r1_waybel_3(k2_yellow_1(u1_pre_topc('#skF_3')),B_101,C_102)
      | ~ m1_subset_1(C_102,u1_struct_0(k2_yellow_1(u1_pre_topc('#skF_3'))))
      | ~ m1_subset_1(B_101,u1_struct_0(k2_yellow_1(u1_pre_topc('#skF_3'))))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_42,c_121])).

tff(c_126,plain,(
    ! [B_101,C_102] :
      ( r1_waybel_7('#skF_3','#skF_6','#skF_2'('#skF_3',B_101,C_102,'#skF_6'))
      | ~ r2_hidden(B_101,'#skF_6')
      | v1_xboole_0('#skF_6')
      | ~ r1_waybel_3(k2_yellow_1(u1_pre_topc('#skF_3')),B_101,C_102)
      | ~ m1_subset_1(C_102,u1_struct_0(k2_yellow_1(u1_pre_topc('#skF_3'))))
      | ~ m1_subset_1(B_101,u1_struct_0(k2_yellow_1(u1_pre_topc('#skF_3'))))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_88,c_48,c_46,c_123])).

tff(c_128,plain,(
    ! [B_103,C_104] :
      ( r1_waybel_7('#skF_3','#skF_6','#skF_2'('#skF_3',B_103,C_104,'#skF_6'))
      | ~ r2_hidden(B_103,'#skF_6')
      | ~ r1_waybel_3(k2_yellow_1(u1_pre_topc('#skF_3')),B_103,C_104)
      | ~ m1_subset_1(C_104,u1_struct_0(k2_yellow_1(u1_pre_topc('#skF_3'))))
      | ~ m1_subset_1(B_103,u1_struct_0(k2_yellow_1(u1_pre_topc('#skF_3')))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_50,c_126])).

tff(c_130,plain,
    ( r1_waybel_7('#skF_3','#skF_6','#skF_2'('#skF_3','#skF_4','#skF_5','#skF_6'))
    | ~ r2_hidden('#skF_4','#skF_6')
    | ~ m1_subset_1('#skF_5',u1_struct_0(k2_yellow_1(u1_pre_topc('#skF_3'))))
    | ~ m1_subset_1('#skF_4',u1_struct_0(k2_yellow_1(u1_pre_topc('#skF_3')))) ),
    inference(resolution,[status(thm)],[c_52,c_128])).

tff(c_133,plain,(
    r1_waybel_7('#skF_3','#skF_6','#skF_2'('#skF_3','#skF_4','#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_40,c_130])).

tff(c_89,plain,(
    ! [A_86,B_87,C_88] :
      ( r2_waybel_7(A_86,B_87,C_88)
      | ~ r1_waybel_7(A_86,B_87,C_88)
      | ~ m1_subset_1(B_87,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(A_86)))))
      | ~ v3_waybel_7(B_87,k3_yellow_1(u1_struct_0(A_86)))
      | ~ v13_waybel_0(B_87,k3_yellow_1(u1_struct_0(A_86)))
      | ~ v2_waybel_0(B_87,k3_yellow_1(u1_struct_0(A_86)))
      | v1_xboole_0(B_87)
      | ~ l1_pre_topc(A_86)
      | ~ v2_pre_topc(A_86)
      | v2_struct_0(A_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_91,plain,(
    ! [C_88] :
      ( r2_waybel_7('#skF_3','#skF_6',C_88)
      | ~ r1_waybel_7('#skF_3','#skF_6',C_88)
      | ~ v3_waybel_7('#skF_6',k3_yellow_1(u1_struct_0('#skF_3')))
      | ~ v13_waybel_0('#skF_6',k3_yellow_1(u1_struct_0('#skF_3')))
      | ~ v2_waybel_0('#skF_6',k3_yellow_1(u1_struct_0('#skF_3')))
      | v1_xboole_0('#skF_6')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_42,c_89])).

tff(c_94,plain,(
    ! [C_88] :
      ( r2_waybel_7('#skF_3','#skF_6',C_88)
      | ~ r1_waybel_7('#skF_3','#skF_6',C_88)
      | v1_xboole_0('#skF_6')
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_48,c_46,c_44,c_91])).

tff(c_95,plain,(
    ! [C_88] :
      ( r2_waybel_7('#skF_3','#skF_6',C_88)
      | ~ r1_waybel_7('#skF_3','#skF_6',C_88) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_50,c_94])).

tff(c_104,plain,(
    ! [A_93,B_94,C_95,D_96] :
      ( r2_hidden('#skF_2'(A_93,B_94,C_95,D_96),C_95)
      | ~ r2_hidden(B_94,D_96)
      | ~ m1_subset_1(D_96,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(A_93)))))
      | ~ v13_waybel_0(D_96,k3_yellow_1(u1_struct_0(A_93)))
      | ~ v2_waybel_0(D_96,k3_yellow_1(u1_struct_0(A_93)))
      | ~ v1_subset_1(D_96,u1_struct_0(k3_yellow_1(u1_struct_0(A_93))))
      | v1_xboole_0(D_96)
      | ~ r1_waybel_3(k2_yellow_1(u1_pre_topc(A_93)),B_94,C_95)
      | ~ m1_subset_1(C_95,u1_struct_0(k2_yellow_1(u1_pre_topc(A_93))))
      | ~ m1_subset_1(B_94,u1_struct_0(k2_yellow_1(u1_pre_topc(A_93))))
      | ~ l1_pre_topc(A_93)
      | ~ v2_pre_topc(A_93)
      | v2_struct_0(A_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_106,plain,(
    ! [B_94,C_95] :
      ( r2_hidden('#skF_2'('#skF_3',B_94,C_95,'#skF_6'),C_95)
      | ~ r2_hidden(B_94,'#skF_6')
      | ~ v13_waybel_0('#skF_6',k3_yellow_1(u1_struct_0('#skF_3')))
      | ~ v2_waybel_0('#skF_6',k3_yellow_1(u1_struct_0('#skF_3')))
      | ~ v1_subset_1('#skF_6',u1_struct_0(k3_yellow_1(u1_struct_0('#skF_3'))))
      | v1_xboole_0('#skF_6')
      | ~ r1_waybel_3(k2_yellow_1(u1_pre_topc('#skF_3')),B_94,C_95)
      | ~ m1_subset_1(C_95,u1_struct_0(k2_yellow_1(u1_pre_topc('#skF_3'))))
      | ~ m1_subset_1(B_94,u1_struct_0(k2_yellow_1(u1_pre_topc('#skF_3'))))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_42,c_104])).

tff(c_109,plain,(
    ! [B_94,C_95] :
      ( r2_hidden('#skF_2'('#skF_3',B_94,C_95,'#skF_6'),C_95)
      | ~ r2_hidden(B_94,'#skF_6')
      | v1_xboole_0('#skF_6')
      | ~ r1_waybel_3(k2_yellow_1(u1_pre_topc('#skF_3')),B_94,C_95)
      | ~ m1_subset_1(C_95,u1_struct_0(k2_yellow_1(u1_pre_topc('#skF_3'))))
      | ~ m1_subset_1(B_94,u1_struct_0(k2_yellow_1(u1_pre_topc('#skF_3'))))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_88,c_48,c_46,c_106])).

tff(c_111,plain,(
    ! [B_97,C_98] :
      ( r2_hidden('#skF_2'('#skF_3',B_97,C_98,'#skF_6'),C_98)
      | ~ r2_hidden(B_97,'#skF_6')
      | ~ r1_waybel_3(k2_yellow_1(u1_pre_topc('#skF_3')),B_97,C_98)
      | ~ m1_subset_1(C_98,u1_struct_0(k2_yellow_1(u1_pre_topc('#skF_3'))))
      | ~ m1_subset_1(B_97,u1_struct_0(k2_yellow_1(u1_pre_topc('#skF_3')))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_50,c_109])).

tff(c_113,plain,
    ( r2_hidden('#skF_2'('#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_5')
    | ~ r2_hidden('#skF_4','#skF_6')
    | ~ m1_subset_1('#skF_5',u1_struct_0(k2_yellow_1(u1_pre_topc('#skF_3'))))
    | ~ m1_subset_1('#skF_4',u1_struct_0(k2_yellow_1(u1_pre_topc('#skF_3')))) ),
    inference(resolution,[status(thm)],[c_52,c_111])).

tff(c_116,plain,(
    r2_hidden('#skF_2'('#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_40,c_113])).

tff(c_134,plain,(
    ! [A_105,B_106,C_107,D_108] :
      ( m1_subset_1('#skF_2'(A_105,B_106,C_107,D_108),u1_struct_0(A_105))
      | ~ r2_hidden(B_106,D_108)
      | ~ m1_subset_1(D_108,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(A_105)))))
      | ~ v13_waybel_0(D_108,k3_yellow_1(u1_struct_0(A_105)))
      | ~ v2_waybel_0(D_108,k3_yellow_1(u1_struct_0(A_105)))
      | ~ v1_subset_1(D_108,u1_struct_0(k3_yellow_1(u1_struct_0(A_105))))
      | v1_xboole_0(D_108)
      | ~ r1_waybel_3(k2_yellow_1(u1_pre_topc(A_105)),B_106,C_107)
      | ~ m1_subset_1(C_107,u1_struct_0(k2_yellow_1(u1_pre_topc(A_105))))
      | ~ m1_subset_1(B_106,u1_struct_0(k2_yellow_1(u1_pre_topc(A_105))))
      | ~ l1_pre_topc(A_105)
      | ~ v2_pre_topc(A_105)
      | v2_struct_0(A_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_136,plain,(
    ! [B_106,C_107] :
      ( m1_subset_1('#skF_2'('#skF_3',B_106,C_107,'#skF_6'),u1_struct_0('#skF_3'))
      | ~ r2_hidden(B_106,'#skF_6')
      | ~ v13_waybel_0('#skF_6',k3_yellow_1(u1_struct_0('#skF_3')))
      | ~ v2_waybel_0('#skF_6',k3_yellow_1(u1_struct_0('#skF_3')))
      | ~ v1_subset_1('#skF_6',u1_struct_0(k3_yellow_1(u1_struct_0('#skF_3'))))
      | v1_xboole_0('#skF_6')
      | ~ r1_waybel_3(k2_yellow_1(u1_pre_topc('#skF_3')),B_106,C_107)
      | ~ m1_subset_1(C_107,u1_struct_0(k2_yellow_1(u1_pre_topc('#skF_3'))))
      | ~ m1_subset_1(B_106,u1_struct_0(k2_yellow_1(u1_pre_topc('#skF_3'))))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_42,c_134])).

tff(c_139,plain,(
    ! [B_106,C_107] :
      ( m1_subset_1('#skF_2'('#skF_3',B_106,C_107,'#skF_6'),u1_struct_0('#skF_3'))
      | ~ r2_hidden(B_106,'#skF_6')
      | v1_xboole_0('#skF_6')
      | ~ r1_waybel_3(k2_yellow_1(u1_pre_topc('#skF_3')),B_106,C_107)
      | ~ m1_subset_1(C_107,u1_struct_0(k2_yellow_1(u1_pre_topc('#skF_3'))))
      | ~ m1_subset_1(B_106,u1_struct_0(k2_yellow_1(u1_pre_topc('#skF_3'))))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_88,c_48,c_46,c_136])).

tff(c_141,plain,(
    ! [B_109,C_110] :
      ( m1_subset_1('#skF_2'('#skF_3',B_109,C_110,'#skF_6'),u1_struct_0('#skF_3'))
      | ~ r2_hidden(B_109,'#skF_6')
      | ~ r1_waybel_3(k2_yellow_1(u1_pre_topc('#skF_3')),B_109,C_110)
      | ~ m1_subset_1(C_110,u1_struct_0(k2_yellow_1(u1_pre_topc('#skF_3'))))
      | ~ m1_subset_1(B_109,u1_struct_0(k2_yellow_1(u1_pre_topc('#skF_3')))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_50,c_139])).

tff(c_143,plain,
    ( m1_subset_1('#skF_2'('#skF_3','#skF_4','#skF_5','#skF_6'),u1_struct_0('#skF_3'))
    | ~ r2_hidden('#skF_4','#skF_6')
    | ~ m1_subset_1('#skF_5',u1_struct_0(k2_yellow_1(u1_pre_topc('#skF_3'))))
    | ~ m1_subset_1('#skF_4',u1_struct_0(k2_yellow_1(u1_pre_topc('#skF_3')))) ),
    inference(resolution,[status(thm)],[c_52,c_141])).

tff(c_146,plain,(
    m1_subset_1('#skF_2'('#skF_3','#skF_4','#skF_5','#skF_6'),u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_40,c_143])).

tff(c_38,plain,(
    ! [E_73] :
      ( ~ r2_waybel_7('#skF_3','#skF_6',E_73)
      | ~ r2_hidden(E_73,'#skF_5')
      | ~ m1_subset_1(E_73,u1_struct_0('#skF_3')) ) ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_149,plain,
    ( ~ r2_waybel_7('#skF_3','#skF_6','#skF_2'('#skF_3','#skF_4','#skF_5','#skF_6'))
    | ~ r2_hidden('#skF_2'('#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_146,c_38])).

tff(c_152,plain,(
    ~ r2_waybel_7('#skF_3','#skF_6','#skF_2'('#skF_3','#skF_4','#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_149])).

tff(c_155,plain,(
    ~ r1_waybel_7('#skF_3','#skF_6','#skF_2'('#skF_3','#skF_4','#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_95,c_152])).

tff(c_159,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_155])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:34:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.34/1.27  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.34/1.28  
% 2.34/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.34/1.28  %$ r2_waybel_7 > r1_waybel_7 > r1_waybel_3 > v3_waybel_7 > v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_orders_2 > l1_pre_topc > l1_orders_2 > #nlpp > u1_struct_0 > u1_pre_topc > k3_yellow_1 > k2_yellow_1 > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_2 > #skF_6 > #skF_3 > #skF_4
% 2.34/1.28  
% 2.34/1.28  %Foreground sorts:
% 2.34/1.28  
% 2.34/1.28  
% 2.34/1.28  %Background operators:
% 2.34/1.28  
% 2.34/1.28  
% 2.34/1.28  %Foreground operators:
% 2.34/1.28  tff(v1_orders_2, type, v1_orders_2: $i > $o).
% 2.34/1.28  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.34/1.28  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 2.34/1.28  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 2.34/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.34/1.28  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.34/1.28  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 2.34/1.28  tff(k3_yellow_1, type, k3_yellow_1: $i > $i).
% 2.34/1.28  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.34/1.28  tff(v2_waybel_0, type, v2_waybel_0: ($i * $i) > $o).
% 2.34/1.28  tff(k2_yellow_1, type, k2_yellow_1: $i > $i).
% 2.34/1.28  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.34/1.28  tff('#skF_5', type, '#skF_5': $i).
% 2.34/1.28  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.34/1.28  tff('#skF_6', type, '#skF_6': $i).
% 2.34/1.28  tff('#skF_3', type, '#skF_3': $i).
% 2.34/1.28  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.34/1.28  tff(r1_waybel_7, type, r1_waybel_7: ($i * $i * $i) > $o).
% 2.34/1.28  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 2.34/1.28  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.34/1.28  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.34/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.34/1.28  tff('#skF_4', type, '#skF_4': $i).
% 2.34/1.28  tff(r2_waybel_7, type, r2_waybel_7: ($i * $i * $i) > $o).
% 2.34/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.34/1.28  tff(v13_waybel_0, type, v13_waybel_0: ($i * $i) > $o).
% 2.34/1.28  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.34/1.28  tff(v3_waybel_7, type, v3_waybel_7: ($i * $i) > $o).
% 2.34/1.28  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.34/1.28  tff(r1_waybel_3, type, r1_waybel_3: ($i * $i * $i) > $o).
% 2.34/1.28  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.34/1.28  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.34/1.28  
% 2.34/1.30  tff(f_179, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(k2_yellow_1(u1_pre_topc(A)))) => (![C]: (m1_subset_1(C, u1_struct_0(k2_yellow_1(u1_pre_topc(A)))) => (r1_waybel_3(k2_yellow_1(u1_pre_topc(A)), B, C) => (![D]: (((((~v1_xboole_0(D) & v2_waybel_0(D, k3_yellow_1(u1_struct_0(A)))) & v13_waybel_0(D, k3_yellow_1(u1_struct_0(A)))) & v3_waybel_7(D, k3_yellow_1(u1_struct_0(A)))) & m1_subset_1(D, k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(A)))))) => ~(r2_hidden(B, D) & (![E]: (m1_subset_1(E, u1_struct_0(A)) => ~(r2_hidden(E, C) & r2_waybel_7(A, D, E)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t33_waybel_7)).
% 2.34/1.30  tff(f_46, axiom, (![A]: ((((~v2_struct_0(k3_yellow_1(A)) & v1_orders_2(k3_yellow_1(A))) & v3_orders_2(k3_yellow_1(A))) & v4_orders_2(k3_yellow_1(A))) & v5_orders_2(k3_yellow_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc7_yellow_1)).
% 2.34/1.30  tff(f_35, axiom, (![A]: (v1_orders_2(k3_yellow_1(A)) & l1_orders_2(k3_yellow_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_yellow_1)).
% 2.34/1.30  tff(f_78, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((((~v1_xboole_0(B) & v2_waybel_0(B, A)) & v13_waybel_0(B, A)) & v3_waybel_7(B, A)) => (((~v1_xboole_0(B) & v1_subset_1(B, u1_struct_0(A))) & v2_waybel_0(B, A)) & v13_waybel_0(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_waybel_7)).
% 2.34/1.30  tff(f_140, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(k2_yellow_1(u1_pre_topc(A)))) => (![C]: (m1_subset_1(C, u1_struct_0(k2_yellow_1(u1_pre_topc(A)))) => (r1_waybel_3(k2_yellow_1(u1_pre_topc(A)), B, C) => (![D]: (((((~v1_xboole_0(D) & v1_subset_1(D, u1_struct_0(k3_yellow_1(u1_struct_0(A))))) & v2_waybel_0(D, k3_yellow_1(u1_struct_0(A)))) & v13_waybel_0(D, k3_yellow_1(u1_struct_0(A)))) & m1_subset_1(D, k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(A)))))) => ~(r2_hidden(B, D) & (![E]: (m1_subset_1(E, u1_struct_0(A)) => ~(r2_hidden(E, C) & r1_waybel_7(A, D, E)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_waybel_7)).
% 2.34/1.30  tff(f_102, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((((~v1_xboole_0(B) & v2_waybel_0(B, k3_yellow_1(u1_struct_0(A)))) & v13_waybel_0(B, k3_yellow_1(u1_struct_0(A)))) & v3_waybel_7(B, k3_yellow_1(u1_struct_0(A)))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(A)))))) => (![C]: (r1_waybel_7(A, B, C) <=> r2_waybel_7(A, B, C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_waybel_7)).
% 2.34/1.30  tff(c_56, plain, (m1_subset_1('#skF_4', u1_struct_0(k2_yellow_1(u1_pre_topc('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_179])).
% 2.34/1.30  tff(c_54, plain, (m1_subset_1('#skF_5', u1_struct_0(k2_yellow_1(u1_pre_topc('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_179])).
% 2.34/1.30  tff(c_40, plain, (r2_hidden('#skF_4', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_179])).
% 2.34/1.30  tff(c_52, plain, (r1_waybel_3(k2_yellow_1(u1_pre_topc('#skF_3')), '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_179])).
% 2.34/1.30  tff(c_62, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_179])).
% 2.34/1.30  tff(c_50, plain, (~v1_xboole_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_179])).
% 2.34/1.30  tff(c_60, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_179])).
% 2.34/1.30  tff(c_58, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_179])).
% 2.34/1.30  tff(c_10, plain, (![A_6]: (~v2_struct_0(k3_yellow_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.34/1.30  tff(c_14, plain, (![A_6]: (v3_orders_2(k3_yellow_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.34/1.30  tff(c_16, plain, (![A_6]: (v4_orders_2(k3_yellow_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.34/1.30  tff(c_18, plain, (![A_6]: (v5_orders_2(k3_yellow_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.34/1.30  tff(c_8, plain, (![A_5]: (l1_orders_2(k3_yellow_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.34/1.30  tff(c_48, plain, (v2_waybel_0('#skF_6', k3_yellow_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_179])).
% 2.34/1.30  tff(c_46, plain, (v13_waybel_0('#skF_6', k3_yellow_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_179])).
% 2.34/1.30  tff(c_44, plain, (v3_waybel_7('#skF_6', k3_yellow_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_179])).
% 2.34/1.30  tff(c_42, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0('#skF_3')))))), inference(cnfTransformation, [status(thm)], [f_179])).
% 2.34/1.30  tff(c_81, plain, (![B_84, A_85]: (v1_subset_1(B_84, u1_struct_0(A_85)) | ~v3_waybel_7(B_84, A_85) | ~v13_waybel_0(B_84, A_85) | ~v2_waybel_0(B_84, A_85) | v1_xboole_0(B_84) | ~m1_subset_1(B_84, k1_zfmisc_1(u1_struct_0(A_85))) | ~l1_orders_2(A_85) | ~v5_orders_2(A_85) | ~v4_orders_2(A_85) | ~v3_orders_2(A_85) | v2_struct_0(A_85))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.34/1.30  tff(c_84, plain, (v1_subset_1('#skF_6', u1_struct_0(k3_yellow_1(u1_struct_0('#skF_3')))) | ~v3_waybel_7('#skF_6', k3_yellow_1(u1_struct_0('#skF_3'))) | ~v13_waybel_0('#skF_6', k3_yellow_1(u1_struct_0('#skF_3'))) | ~v2_waybel_0('#skF_6', k3_yellow_1(u1_struct_0('#skF_3'))) | v1_xboole_0('#skF_6') | ~l1_orders_2(k3_yellow_1(u1_struct_0('#skF_3'))) | ~v5_orders_2(k3_yellow_1(u1_struct_0('#skF_3'))) | ~v4_orders_2(k3_yellow_1(u1_struct_0('#skF_3'))) | ~v3_orders_2(k3_yellow_1(u1_struct_0('#skF_3'))) | v2_struct_0(k3_yellow_1(u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_42, c_81])).
% 2.34/1.30  tff(c_87, plain, (v1_subset_1('#skF_6', u1_struct_0(k3_yellow_1(u1_struct_0('#skF_3')))) | v1_xboole_0('#skF_6') | v2_struct_0(k3_yellow_1(u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_16, c_18, c_8, c_48, c_46, c_44, c_84])).
% 2.34/1.30  tff(c_88, plain, (v1_subset_1('#skF_6', u1_struct_0(k3_yellow_1(u1_struct_0('#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_10, c_50, c_87])).
% 2.34/1.30  tff(c_121, plain, (![A_99, D_100, B_101, C_102]: (r1_waybel_7(A_99, D_100, '#skF_2'(A_99, B_101, C_102, D_100)) | ~r2_hidden(B_101, D_100) | ~m1_subset_1(D_100, k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(A_99))))) | ~v13_waybel_0(D_100, k3_yellow_1(u1_struct_0(A_99))) | ~v2_waybel_0(D_100, k3_yellow_1(u1_struct_0(A_99))) | ~v1_subset_1(D_100, u1_struct_0(k3_yellow_1(u1_struct_0(A_99)))) | v1_xboole_0(D_100) | ~r1_waybel_3(k2_yellow_1(u1_pre_topc(A_99)), B_101, C_102) | ~m1_subset_1(C_102, u1_struct_0(k2_yellow_1(u1_pre_topc(A_99)))) | ~m1_subset_1(B_101, u1_struct_0(k2_yellow_1(u1_pre_topc(A_99)))) | ~l1_pre_topc(A_99) | ~v2_pre_topc(A_99) | v2_struct_0(A_99))), inference(cnfTransformation, [status(thm)], [f_140])).
% 2.34/1.30  tff(c_123, plain, (![B_101, C_102]: (r1_waybel_7('#skF_3', '#skF_6', '#skF_2'('#skF_3', B_101, C_102, '#skF_6')) | ~r2_hidden(B_101, '#skF_6') | ~v13_waybel_0('#skF_6', k3_yellow_1(u1_struct_0('#skF_3'))) | ~v2_waybel_0('#skF_6', k3_yellow_1(u1_struct_0('#skF_3'))) | ~v1_subset_1('#skF_6', u1_struct_0(k3_yellow_1(u1_struct_0('#skF_3')))) | v1_xboole_0('#skF_6') | ~r1_waybel_3(k2_yellow_1(u1_pre_topc('#skF_3')), B_101, C_102) | ~m1_subset_1(C_102, u1_struct_0(k2_yellow_1(u1_pre_topc('#skF_3')))) | ~m1_subset_1(B_101, u1_struct_0(k2_yellow_1(u1_pre_topc('#skF_3')))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_42, c_121])).
% 2.34/1.30  tff(c_126, plain, (![B_101, C_102]: (r1_waybel_7('#skF_3', '#skF_6', '#skF_2'('#skF_3', B_101, C_102, '#skF_6')) | ~r2_hidden(B_101, '#skF_6') | v1_xboole_0('#skF_6') | ~r1_waybel_3(k2_yellow_1(u1_pre_topc('#skF_3')), B_101, C_102) | ~m1_subset_1(C_102, u1_struct_0(k2_yellow_1(u1_pre_topc('#skF_3')))) | ~m1_subset_1(B_101, u1_struct_0(k2_yellow_1(u1_pre_topc('#skF_3')))) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_88, c_48, c_46, c_123])).
% 2.34/1.30  tff(c_128, plain, (![B_103, C_104]: (r1_waybel_7('#skF_3', '#skF_6', '#skF_2'('#skF_3', B_103, C_104, '#skF_6')) | ~r2_hidden(B_103, '#skF_6') | ~r1_waybel_3(k2_yellow_1(u1_pre_topc('#skF_3')), B_103, C_104) | ~m1_subset_1(C_104, u1_struct_0(k2_yellow_1(u1_pre_topc('#skF_3')))) | ~m1_subset_1(B_103, u1_struct_0(k2_yellow_1(u1_pre_topc('#skF_3')))))), inference(negUnitSimplification, [status(thm)], [c_62, c_50, c_126])).
% 2.34/1.30  tff(c_130, plain, (r1_waybel_7('#skF_3', '#skF_6', '#skF_2'('#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~r2_hidden('#skF_4', '#skF_6') | ~m1_subset_1('#skF_5', u1_struct_0(k2_yellow_1(u1_pre_topc('#skF_3')))) | ~m1_subset_1('#skF_4', u1_struct_0(k2_yellow_1(u1_pre_topc('#skF_3'))))), inference(resolution, [status(thm)], [c_52, c_128])).
% 2.34/1.30  tff(c_133, plain, (r1_waybel_7('#skF_3', '#skF_6', '#skF_2'('#skF_3', '#skF_4', '#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_40, c_130])).
% 2.34/1.30  tff(c_89, plain, (![A_86, B_87, C_88]: (r2_waybel_7(A_86, B_87, C_88) | ~r1_waybel_7(A_86, B_87, C_88) | ~m1_subset_1(B_87, k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(A_86))))) | ~v3_waybel_7(B_87, k3_yellow_1(u1_struct_0(A_86))) | ~v13_waybel_0(B_87, k3_yellow_1(u1_struct_0(A_86))) | ~v2_waybel_0(B_87, k3_yellow_1(u1_struct_0(A_86))) | v1_xboole_0(B_87) | ~l1_pre_topc(A_86) | ~v2_pre_topc(A_86) | v2_struct_0(A_86))), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.34/1.30  tff(c_91, plain, (![C_88]: (r2_waybel_7('#skF_3', '#skF_6', C_88) | ~r1_waybel_7('#skF_3', '#skF_6', C_88) | ~v3_waybel_7('#skF_6', k3_yellow_1(u1_struct_0('#skF_3'))) | ~v13_waybel_0('#skF_6', k3_yellow_1(u1_struct_0('#skF_3'))) | ~v2_waybel_0('#skF_6', k3_yellow_1(u1_struct_0('#skF_3'))) | v1_xboole_0('#skF_6') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_42, c_89])).
% 2.34/1.30  tff(c_94, plain, (![C_88]: (r2_waybel_7('#skF_3', '#skF_6', C_88) | ~r1_waybel_7('#skF_3', '#skF_6', C_88) | v1_xboole_0('#skF_6') | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_48, c_46, c_44, c_91])).
% 2.34/1.30  tff(c_95, plain, (![C_88]: (r2_waybel_7('#skF_3', '#skF_6', C_88) | ~r1_waybel_7('#skF_3', '#skF_6', C_88))), inference(negUnitSimplification, [status(thm)], [c_62, c_50, c_94])).
% 2.34/1.30  tff(c_104, plain, (![A_93, B_94, C_95, D_96]: (r2_hidden('#skF_2'(A_93, B_94, C_95, D_96), C_95) | ~r2_hidden(B_94, D_96) | ~m1_subset_1(D_96, k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(A_93))))) | ~v13_waybel_0(D_96, k3_yellow_1(u1_struct_0(A_93))) | ~v2_waybel_0(D_96, k3_yellow_1(u1_struct_0(A_93))) | ~v1_subset_1(D_96, u1_struct_0(k3_yellow_1(u1_struct_0(A_93)))) | v1_xboole_0(D_96) | ~r1_waybel_3(k2_yellow_1(u1_pre_topc(A_93)), B_94, C_95) | ~m1_subset_1(C_95, u1_struct_0(k2_yellow_1(u1_pre_topc(A_93)))) | ~m1_subset_1(B_94, u1_struct_0(k2_yellow_1(u1_pre_topc(A_93)))) | ~l1_pre_topc(A_93) | ~v2_pre_topc(A_93) | v2_struct_0(A_93))), inference(cnfTransformation, [status(thm)], [f_140])).
% 2.34/1.30  tff(c_106, plain, (![B_94, C_95]: (r2_hidden('#skF_2'('#skF_3', B_94, C_95, '#skF_6'), C_95) | ~r2_hidden(B_94, '#skF_6') | ~v13_waybel_0('#skF_6', k3_yellow_1(u1_struct_0('#skF_3'))) | ~v2_waybel_0('#skF_6', k3_yellow_1(u1_struct_0('#skF_3'))) | ~v1_subset_1('#skF_6', u1_struct_0(k3_yellow_1(u1_struct_0('#skF_3')))) | v1_xboole_0('#skF_6') | ~r1_waybel_3(k2_yellow_1(u1_pre_topc('#skF_3')), B_94, C_95) | ~m1_subset_1(C_95, u1_struct_0(k2_yellow_1(u1_pre_topc('#skF_3')))) | ~m1_subset_1(B_94, u1_struct_0(k2_yellow_1(u1_pre_topc('#skF_3')))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_42, c_104])).
% 2.34/1.30  tff(c_109, plain, (![B_94, C_95]: (r2_hidden('#skF_2'('#skF_3', B_94, C_95, '#skF_6'), C_95) | ~r2_hidden(B_94, '#skF_6') | v1_xboole_0('#skF_6') | ~r1_waybel_3(k2_yellow_1(u1_pre_topc('#skF_3')), B_94, C_95) | ~m1_subset_1(C_95, u1_struct_0(k2_yellow_1(u1_pre_topc('#skF_3')))) | ~m1_subset_1(B_94, u1_struct_0(k2_yellow_1(u1_pre_topc('#skF_3')))) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_88, c_48, c_46, c_106])).
% 2.34/1.30  tff(c_111, plain, (![B_97, C_98]: (r2_hidden('#skF_2'('#skF_3', B_97, C_98, '#skF_6'), C_98) | ~r2_hidden(B_97, '#skF_6') | ~r1_waybel_3(k2_yellow_1(u1_pre_topc('#skF_3')), B_97, C_98) | ~m1_subset_1(C_98, u1_struct_0(k2_yellow_1(u1_pre_topc('#skF_3')))) | ~m1_subset_1(B_97, u1_struct_0(k2_yellow_1(u1_pre_topc('#skF_3')))))), inference(negUnitSimplification, [status(thm)], [c_62, c_50, c_109])).
% 2.34/1.30  tff(c_113, plain, (r2_hidden('#skF_2'('#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_5') | ~r2_hidden('#skF_4', '#skF_6') | ~m1_subset_1('#skF_5', u1_struct_0(k2_yellow_1(u1_pre_topc('#skF_3')))) | ~m1_subset_1('#skF_4', u1_struct_0(k2_yellow_1(u1_pre_topc('#skF_3'))))), inference(resolution, [status(thm)], [c_52, c_111])).
% 2.34/1.30  tff(c_116, plain, (r2_hidden('#skF_2'('#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_40, c_113])).
% 2.34/1.30  tff(c_134, plain, (![A_105, B_106, C_107, D_108]: (m1_subset_1('#skF_2'(A_105, B_106, C_107, D_108), u1_struct_0(A_105)) | ~r2_hidden(B_106, D_108) | ~m1_subset_1(D_108, k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(A_105))))) | ~v13_waybel_0(D_108, k3_yellow_1(u1_struct_0(A_105))) | ~v2_waybel_0(D_108, k3_yellow_1(u1_struct_0(A_105))) | ~v1_subset_1(D_108, u1_struct_0(k3_yellow_1(u1_struct_0(A_105)))) | v1_xboole_0(D_108) | ~r1_waybel_3(k2_yellow_1(u1_pre_topc(A_105)), B_106, C_107) | ~m1_subset_1(C_107, u1_struct_0(k2_yellow_1(u1_pre_topc(A_105)))) | ~m1_subset_1(B_106, u1_struct_0(k2_yellow_1(u1_pre_topc(A_105)))) | ~l1_pre_topc(A_105) | ~v2_pre_topc(A_105) | v2_struct_0(A_105))), inference(cnfTransformation, [status(thm)], [f_140])).
% 2.34/1.30  tff(c_136, plain, (![B_106, C_107]: (m1_subset_1('#skF_2'('#skF_3', B_106, C_107, '#skF_6'), u1_struct_0('#skF_3')) | ~r2_hidden(B_106, '#skF_6') | ~v13_waybel_0('#skF_6', k3_yellow_1(u1_struct_0('#skF_3'))) | ~v2_waybel_0('#skF_6', k3_yellow_1(u1_struct_0('#skF_3'))) | ~v1_subset_1('#skF_6', u1_struct_0(k3_yellow_1(u1_struct_0('#skF_3')))) | v1_xboole_0('#skF_6') | ~r1_waybel_3(k2_yellow_1(u1_pre_topc('#skF_3')), B_106, C_107) | ~m1_subset_1(C_107, u1_struct_0(k2_yellow_1(u1_pre_topc('#skF_3')))) | ~m1_subset_1(B_106, u1_struct_0(k2_yellow_1(u1_pre_topc('#skF_3')))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_42, c_134])).
% 2.34/1.30  tff(c_139, plain, (![B_106, C_107]: (m1_subset_1('#skF_2'('#skF_3', B_106, C_107, '#skF_6'), u1_struct_0('#skF_3')) | ~r2_hidden(B_106, '#skF_6') | v1_xboole_0('#skF_6') | ~r1_waybel_3(k2_yellow_1(u1_pre_topc('#skF_3')), B_106, C_107) | ~m1_subset_1(C_107, u1_struct_0(k2_yellow_1(u1_pre_topc('#skF_3')))) | ~m1_subset_1(B_106, u1_struct_0(k2_yellow_1(u1_pre_topc('#skF_3')))) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_88, c_48, c_46, c_136])).
% 2.34/1.30  tff(c_141, plain, (![B_109, C_110]: (m1_subset_1('#skF_2'('#skF_3', B_109, C_110, '#skF_6'), u1_struct_0('#skF_3')) | ~r2_hidden(B_109, '#skF_6') | ~r1_waybel_3(k2_yellow_1(u1_pre_topc('#skF_3')), B_109, C_110) | ~m1_subset_1(C_110, u1_struct_0(k2_yellow_1(u1_pre_topc('#skF_3')))) | ~m1_subset_1(B_109, u1_struct_0(k2_yellow_1(u1_pre_topc('#skF_3')))))), inference(negUnitSimplification, [status(thm)], [c_62, c_50, c_139])).
% 2.34/1.30  tff(c_143, plain, (m1_subset_1('#skF_2'('#skF_3', '#skF_4', '#skF_5', '#skF_6'), u1_struct_0('#skF_3')) | ~r2_hidden('#skF_4', '#skF_6') | ~m1_subset_1('#skF_5', u1_struct_0(k2_yellow_1(u1_pre_topc('#skF_3')))) | ~m1_subset_1('#skF_4', u1_struct_0(k2_yellow_1(u1_pre_topc('#skF_3'))))), inference(resolution, [status(thm)], [c_52, c_141])).
% 2.34/1.30  tff(c_146, plain, (m1_subset_1('#skF_2'('#skF_3', '#skF_4', '#skF_5', '#skF_6'), u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_40, c_143])).
% 2.34/1.30  tff(c_38, plain, (![E_73]: (~r2_waybel_7('#skF_3', '#skF_6', E_73) | ~r2_hidden(E_73, '#skF_5') | ~m1_subset_1(E_73, u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_179])).
% 2.34/1.30  tff(c_149, plain, (~r2_waybel_7('#skF_3', '#skF_6', '#skF_2'('#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~r2_hidden('#skF_2'('#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_5')), inference(resolution, [status(thm)], [c_146, c_38])).
% 2.34/1.30  tff(c_152, plain, (~r2_waybel_7('#skF_3', '#skF_6', '#skF_2'('#skF_3', '#skF_4', '#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_116, c_149])).
% 2.34/1.30  tff(c_155, plain, (~r1_waybel_7('#skF_3', '#skF_6', '#skF_2'('#skF_3', '#skF_4', '#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_95, c_152])).
% 2.34/1.30  tff(c_159, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_133, c_155])).
% 2.34/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.34/1.30  
% 2.34/1.30  Inference rules
% 2.34/1.30  ----------------------
% 2.34/1.30  #Ref     : 0
% 2.34/1.30  #Sup     : 14
% 2.34/1.30  #Fact    : 0
% 2.34/1.30  #Define  : 0
% 2.34/1.30  #Split   : 0
% 2.34/1.30  #Chain   : 0
% 2.34/1.30  #Close   : 0
% 2.34/1.30  
% 2.34/1.30  Ordering : KBO
% 2.34/1.30  
% 2.34/1.30  Simplification rules
% 2.34/1.30  ----------------------
% 2.34/1.30  #Subsume      : 1
% 2.34/1.30  #Demod        : 45
% 2.34/1.30  #Tautology    : 6
% 2.34/1.30  #SimpNegUnit  : 6
% 2.34/1.30  #BackRed      : 0
% 2.34/1.30  
% 2.34/1.30  #Partial instantiations: 0
% 2.34/1.30  #Strategies tried      : 1
% 2.34/1.30  
% 2.34/1.30  Timing (in seconds)
% 2.34/1.30  ----------------------
% 2.34/1.30  Preprocessing        : 0.33
% 2.34/1.30  Parsing              : 0.18
% 2.34/1.30  CNF conversion       : 0.03
% 2.34/1.30  Main loop            : 0.20
% 2.34/1.30  Inferencing          : 0.08
% 2.34/1.30  Reduction            : 0.07
% 2.34/1.30  Demodulation         : 0.05
% 2.34/1.30  BG Simplification    : 0.02
% 2.34/1.30  Subsumption          : 0.03
% 2.34/1.30  Abstraction          : 0.01
% 2.34/1.30  MUC search           : 0.00
% 2.34/1.30  Cooper               : 0.00
% 2.34/1.30  Total                : 0.57
% 2.34/1.30  Index Insertion      : 0.00
% 2.34/1.30  Index Deletion       : 0.00
% 2.34/1.30  Index Matching       : 0.00
% 2.34/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
