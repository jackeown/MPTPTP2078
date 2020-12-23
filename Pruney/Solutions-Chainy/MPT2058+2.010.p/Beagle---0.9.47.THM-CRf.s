%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:34 EST 2020

% Result     : Theorem 26.48s
% Output     : CNFRefutation 26.55s
% Verified   : 
% Statistics : Number of formulae       :  221 (1524 expanded)
%              Number of leaves         :   52 ( 558 expanded)
%              Depth                    :   19
%              Number of atoms          :  654 (8163 expanded)
%              Number of equality atoms :   45 ( 101 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_waybel_9 > r1_waybel_7 > v6_waybel_0 > v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_hidden > m1_subset_1 > l1_waybel_0 > v7_waybel_0 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k7_subset_1 > k3_yellow19 > k4_xboole_0 > k2_yellow19 > #nlpp > u1_struct_0 > k3_yellow_1 > k3_lattice3 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_lattice3 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3

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

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(v2_waybel_0,type,(
    v2_waybel_0: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(v7_waybel_0,type,(
    v7_waybel_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r3_waybel_9,type,(
    r3_waybel_9: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

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
    '#skF_3': ( $i * $i * $i ) > $i )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_226,negated_conjecture,(
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

tff(f_57,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_53,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => m1_subset_1(k2_struct_0(A),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_struct_0)).

tff(f_199,axiom,(
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

tff(f_128,axiom,(
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

tff(f_43,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_45,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_72,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k7_subset_1(u1_struct_0(A),k2_struct_0(A),k7_subset_1(u1_struct_0(A),k2_struct_0(A),B)) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_pre_topc)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_65,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_156,axiom,(
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

tff(f_100,axiom,(
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

tff(f_180,axiom,(
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

tff(c_66,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_226])).

tff(c_84,plain,
    ( ~ r1_waybel_7('#skF_4','#skF_5','#skF_6')
    | ~ r3_waybel_9('#skF_4',k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_226])).

tff(c_132,plain,(
    ~ r3_waybel_9('#skF_4',k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_84])).

tff(c_90,plain,
    ( r3_waybel_9('#skF_4',k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'),'#skF_6')
    | r1_waybel_7('#skF_4','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_226])).

tff(c_200,plain,(
    r1_waybel_7('#skF_4','#skF_5','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_132,c_90])).

tff(c_78,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_226])).

tff(c_32,plain,(
    ! [A_17] :
      ( l1_struct_0(A_17)
      | ~ l1_pre_topc(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_82,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_226])).

tff(c_30,plain,(
    ! [A_16] :
      ( m1_subset_1(k2_struct_0(A_16),k1_zfmisc_1(u1_struct_0(A_16)))
      | ~ l1_struct_0(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_76,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_226])).

tff(c_74,plain,(
    v1_subset_1('#skF_5',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4')))) ),
    inference(cnfTransformation,[status(thm)],[f_226])).

tff(c_72,plain,(
    v2_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_226])).

tff(c_70,plain,(
    v13_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_226])).

tff(c_68,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4'))))) ),
    inference(cnfTransformation,[status(thm)],[f_226])).

tff(c_3652,plain,(
    ! [A_229,B_230] :
      ( k2_yellow19(A_229,k3_yellow19(A_229,k2_struct_0(A_229),B_230)) = B_230
      | ~ m1_subset_1(B_230,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_229)))))
      | ~ v13_waybel_0(B_230,k3_yellow_1(k2_struct_0(A_229)))
      | ~ v2_waybel_0(B_230,k3_yellow_1(k2_struct_0(A_229)))
      | ~ v1_subset_1(B_230,u1_struct_0(k3_yellow_1(k2_struct_0(A_229))))
      | v1_xboole_0(B_230)
      | ~ l1_struct_0(A_229)
      | v2_struct_0(A_229) ) ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_3657,plain,
    ( k2_yellow19('#skF_4',k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5')) = '#skF_5'
    | ~ v13_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_4')))
    | ~ v2_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_4')))
    | ~ v1_subset_1('#skF_5',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4'))))
    | v1_xboole_0('#skF_5')
    | ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_3652])).

tff(c_3664,plain,
    ( k2_yellow19('#skF_4',k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5')) = '#skF_5'
    | v1_xboole_0('#skF_5')
    | ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_3657])).

tff(c_3665,plain,
    ( k2_yellow19('#skF_4',k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5')) = '#skF_5'
    | ~ l1_struct_0('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_76,c_3664])).

tff(c_3667,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_3665])).

tff(c_3670,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_3667])).

tff(c_3674,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_3670])).

tff(c_3676,plain,(
    l1_struct_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_3665])).

tff(c_2691,plain,(
    ! [A_185,B_186,C_187] :
      ( v3_orders_2(k3_yellow19(A_185,B_186,C_187))
      | ~ m1_subset_1(C_187,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_186))))
      | ~ v13_waybel_0(C_187,k3_yellow_1(B_186))
      | ~ v2_waybel_0(C_187,k3_yellow_1(B_186))
      | v1_xboole_0(C_187)
      | ~ m1_subset_1(B_186,k1_zfmisc_1(u1_struct_0(A_185)))
      | v1_xboole_0(B_186)
      | ~ l1_struct_0(A_185)
      | v2_struct_0(A_185) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_2696,plain,(
    ! [A_185] :
      ( v3_orders_2(k3_yellow19(A_185,k2_struct_0('#skF_4'),'#skF_5'))
      | ~ v13_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_4')))
      | ~ v2_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_4')))
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0(A_185)))
      | v1_xboole_0(k2_struct_0('#skF_4'))
      | ~ l1_struct_0(A_185)
      | v2_struct_0(A_185) ) ),
    inference(resolution,[status(thm)],[c_68,c_2691])).

tff(c_2703,plain,(
    ! [A_185] :
      ( v3_orders_2(k3_yellow19(A_185,k2_struct_0('#skF_4'),'#skF_5'))
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0(A_185)))
      | v1_xboole_0(k2_struct_0('#skF_4'))
      | ~ l1_struct_0(A_185)
      | v2_struct_0(A_185) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_2696])).

tff(c_2704,plain,(
    ! [A_185] :
      ( v3_orders_2(k3_yellow19(A_185,k2_struct_0('#skF_4'),'#skF_5'))
      | ~ m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0(A_185)))
      | v1_xboole_0(k2_struct_0('#skF_4'))
      | ~ l1_struct_0(A_185)
      | v2_struct_0(A_185) ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_2703])).

tff(c_2976,plain,(
    v1_xboole_0(k2_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_2704])).

tff(c_24,plain,(
    ! [A_11] : k2_subset_1(A_11) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_26,plain,(
    ! [A_12] : m1_subset_1(k2_subset_1(A_12),k1_zfmisc_1(A_12)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_91,plain,(
    ! [A_12] : m1_subset_1(A_12,k1_zfmisc_1(A_12)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_26])).

tff(c_181,plain,(
    ! [A_74,B_75,C_76] :
      ( k7_subset_1(A_74,B_75,C_76) = k4_xboole_0(B_75,C_76)
      | ~ m1_subset_1(B_75,k1_zfmisc_1(A_74)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_188,plain,(
    ! [A_16,C_76] :
      ( k7_subset_1(u1_struct_0(A_16),k2_struct_0(A_16),C_76) = k4_xboole_0(k2_struct_0(A_16),C_76)
      | ~ l1_struct_0(A_16) ) ),
    inference(resolution,[status(thm)],[c_30,c_181])).

tff(c_554,plain,(
    ! [A_117,B_118] :
      ( k7_subset_1(u1_struct_0(A_117),k2_struct_0(A_117),k7_subset_1(u1_struct_0(A_117),k2_struct_0(A_117),B_118)) = B_118
      | ~ m1_subset_1(B_118,k1_zfmisc_1(u1_struct_0(A_117)))
      | ~ l1_struct_0(A_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_37012,plain,(
    ! [A_5945,B_5946] :
      ( k4_xboole_0(k2_struct_0(A_5945),k7_subset_1(u1_struct_0(A_5945),k2_struct_0(A_5945),B_5946)) = B_5946
      | ~ m1_subset_1(B_5946,k1_zfmisc_1(u1_struct_0(A_5945)))
      | ~ l1_struct_0(A_5945)
      | ~ l1_struct_0(A_5945) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_188,c_554])).

tff(c_308,plain,(
    ! [A_108,B_109,C_110] :
      ( r2_hidden('#skF_2'(A_108,B_109,C_110),A_108)
      | r2_hidden('#skF_3'(A_108,B_109,C_110),C_110)
      | k4_xboole_0(A_108,B_109) = C_110 ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_18,plain,(
    ! [A_5,B_6,C_7] :
      ( ~ r2_hidden('#skF_2'(A_5,B_6,C_7),C_7)
      | r2_hidden('#skF_3'(A_5,B_6,C_7),C_7)
      | k4_xboole_0(A_5,B_6) = C_7 ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1250,plain,(
    ! [A_148,B_149] :
      ( r2_hidden('#skF_3'(A_148,B_149,A_148),A_148)
      | k4_xboole_0(A_148,B_149) = A_148 ) ),
    inference(resolution,[status(thm)],[c_308,c_18])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1275,plain,(
    ! [A_148,B_149] :
      ( ~ v1_xboole_0(A_148)
      | k4_xboole_0(A_148,B_149) = A_148 ) ),
    inference(resolution,[status(thm)],[c_1250,c_2])).

tff(c_2989,plain,(
    ! [B_149] : k4_xboole_0(k2_struct_0('#skF_4'),B_149) = k2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_2976,c_1275])).

tff(c_37249,plain,(
    ! [B_5946] :
      ( k2_struct_0('#skF_4') = B_5946
      | ~ m1_subset_1(B_5946,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_struct_0('#skF_4')
      | ~ l1_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_37012,c_2989])).

tff(c_37356,plain,(
    ! [B_5971] :
      ( k2_struct_0('#skF_4') = B_5971
      | ~ m1_subset_1(B_5971,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3676,c_3676,c_37249])).

tff(c_37369,plain,(
    u1_struct_0('#skF_4') = k2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_91,c_37356])).

tff(c_34,plain,(
    ! [A_18] :
      ( ~ v1_xboole_0(u1_struct_0(A_18))
      | ~ l1_struct_0(A_18)
      | v2_struct_0(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_37393,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_4'))
    | ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_37369,c_34])).

tff(c_37409,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3676,c_2976,c_37393])).

tff(c_37411,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_37409])).

tff(c_37414,plain,(
    ! [A_6020] :
      ( v3_orders_2(k3_yellow19(A_6020,k2_struct_0('#skF_4'),'#skF_5'))
      | ~ m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0(A_6020)))
      | ~ l1_struct_0(A_6020)
      | v2_struct_0(A_6020) ) ),
    inference(splitRight,[status(thm)],[c_2704])).

tff(c_37418,plain,
    ( v3_orders_2(k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'))
    | v2_struct_0('#skF_4')
    | ~ l1_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_37414])).

tff(c_37421,plain,
    ( v3_orders_2(k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'))
    | ~ l1_struct_0('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_37418])).

tff(c_37422,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_37421])).

tff(c_37425,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_37422])).

tff(c_37429,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_37425])).

tff(c_37431,plain,(
    l1_struct_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_37421])).

tff(c_37413,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_2704])).

tff(c_80,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_226])).

tff(c_37500,plain,(
    ! [A_6027,B_6028,C_6029] :
      ( v4_orders_2(k3_yellow19(A_6027,B_6028,C_6029))
      | ~ m1_subset_1(C_6029,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_6028))))
      | ~ v13_waybel_0(C_6029,k3_yellow_1(B_6028))
      | ~ v2_waybel_0(C_6029,k3_yellow_1(B_6028))
      | v1_xboole_0(C_6029)
      | ~ m1_subset_1(B_6028,k1_zfmisc_1(u1_struct_0(A_6027)))
      | v1_xboole_0(B_6028)
      | ~ l1_struct_0(A_6027)
      | v2_struct_0(A_6027) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_37505,plain,(
    ! [A_6027] :
      ( v4_orders_2(k3_yellow19(A_6027,k2_struct_0('#skF_4'),'#skF_5'))
      | ~ v13_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_4')))
      | ~ v2_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_4')))
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0(A_6027)))
      | v1_xboole_0(k2_struct_0('#skF_4'))
      | ~ l1_struct_0(A_6027)
      | v2_struct_0(A_6027) ) ),
    inference(resolution,[status(thm)],[c_68,c_37500])).

tff(c_37512,plain,(
    ! [A_6027] :
      ( v4_orders_2(k3_yellow19(A_6027,k2_struct_0('#skF_4'),'#skF_5'))
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0(A_6027)))
      | v1_xboole_0(k2_struct_0('#skF_4'))
      | ~ l1_struct_0(A_6027)
      | v2_struct_0(A_6027) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_37505])).

tff(c_38912,plain,(
    ! [A_6053] :
      ( v4_orders_2(k3_yellow19(A_6053,k2_struct_0('#skF_4'),'#skF_5'))
      | ~ m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0(A_6053)))
      | ~ l1_struct_0(A_6053)
      | v2_struct_0(A_6053) ) ),
    inference(negUnitSimplification,[status(thm)],[c_37413,c_76,c_37512])).

tff(c_38916,plain,
    ( v4_orders_2(k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'))
    | v2_struct_0('#skF_4')
    | ~ l1_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_38912])).

tff(c_38919,plain,
    ( v4_orders_2(k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_37431,c_38916])).

tff(c_38920,plain,(
    v4_orders_2(k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_38919])).

tff(c_39810,plain,(
    ! [A_6070,B_6071,C_6072] :
      ( v7_waybel_0(k3_yellow19(A_6070,B_6071,C_6072))
      | ~ m1_subset_1(C_6072,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_6071))))
      | ~ v13_waybel_0(C_6072,k3_yellow_1(B_6071))
      | ~ v2_waybel_0(C_6072,k3_yellow_1(B_6071))
      | ~ v1_subset_1(C_6072,u1_struct_0(k3_yellow_1(B_6071)))
      | v1_xboole_0(C_6072)
      | ~ m1_subset_1(B_6071,k1_zfmisc_1(u1_struct_0(A_6070)))
      | v1_xboole_0(B_6071)
      | ~ l1_struct_0(A_6070)
      | v2_struct_0(A_6070) ) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_39815,plain,(
    ! [A_6070] :
      ( v7_waybel_0(k3_yellow19(A_6070,k2_struct_0('#skF_4'),'#skF_5'))
      | ~ v13_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_4')))
      | ~ v2_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_4')))
      | ~ v1_subset_1('#skF_5',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4'))))
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0(A_6070)))
      | v1_xboole_0(k2_struct_0('#skF_4'))
      | ~ l1_struct_0(A_6070)
      | v2_struct_0(A_6070) ) ),
    inference(resolution,[status(thm)],[c_68,c_39810])).

tff(c_39822,plain,(
    ! [A_6070] :
      ( v7_waybel_0(k3_yellow19(A_6070,k2_struct_0('#skF_4'),'#skF_5'))
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0(A_6070)))
      | v1_xboole_0(k2_struct_0('#skF_4'))
      | ~ l1_struct_0(A_6070)
      | v2_struct_0(A_6070) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_39815])).

tff(c_39825,plain,(
    ! [A_6073] :
      ( v7_waybel_0(k3_yellow19(A_6073,k2_struct_0('#skF_4'),'#skF_5'))
      | ~ m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0(A_6073)))
      | ~ l1_struct_0(A_6073)
      | v2_struct_0(A_6073) ) ),
    inference(negUnitSimplification,[status(thm)],[c_37413,c_76,c_39822])).

tff(c_39829,plain,
    ( v7_waybel_0(k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'))
    | v2_struct_0('#skF_4')
    | ~ l1_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_39825])).

tff(c_39832,plain,
    ( v7_waybel_0(k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_37431,c_39829])).

tff(c_39833,plain,(
    v7_waybel_0(k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_39832])).

tff(c_38167,plain,(
    ! [A_6042,B_6043,C_6044] :
      ( l1_waybel_0(k3_yellow19(A_6042,B_6043,C_6044),A_6042)
      | ~ m1_subset_1(C_6044,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_6043))))
      | ~ v13_waybel_0(C_6044,k3_yellow_1(B_6043))
      | ~ v2_waybel_0(C_6044,k3_yellow_1(B_6043))
      | v1_xboole_0(C_6044)
      | ~ m1_subset_1(B_6043,k1_zfmisc_1(u1_struct_0(A_6042)))
      | v1_xboole_0(B_6043)
      | ~ l1_struct_0(A_6042)
      | v2_struct_0(A_6042) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_38172,plain,(
    ! [A_6042] :
      ( l1_waybel_0(k3_yellow19(A_6042,k2_struct_0('#skF_4'),'#skF_5'),A_6042)
      | ~ v13_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_4')))
      | ~ v2_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_4')))
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0(A_6042)))
      | v1_xboole_0(k2_struct_0('#skF_4'))
      | ~ l1_struct_0(A_6042)
      | v2_struct_0(A_6042) ) ),
    inference(resolution,[status(thm)],[c_68,c_38167])).

tff(c_38179,plain,(
    ! [A_6042] :
      ( l1_waybel_0(k3_yellow19(A_6042,k2_struct_0('#skF_4'),'#skF_5'),A_6042)
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0(A_6042)))
      | v1_xboole_0(k2_struct_0('#skF_4'))
      | ~ l1_struct_0(A_6042)
      | v2_struct_0(A_6042) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_38172])).

tff(c_39770,plain,(
    ! [A_6065] :
      ( l1_waybel_0(k3_yellow19(A_6065,k2_struct_0('#skF_4'),'#skF_5'),A_6065)
      | ~ m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0(A_6065)))
      | ~ l1_struct_0(A_6065)
      | v2_struct_0(A_6065) ) ),
    inference(negUnitSimplification,[status(thm)],[c_37413,c_76,c_38179])).

tff(c_39773,plain,
    ( l1_waybel_0(k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'),'#skF_4')
    | v2_struct_0('#skF_4')
    | ~ l1_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_39770])).

tff(c_39776,plain,
    ( l1_waybel_0(k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'),'#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_37431,c_39773])).

tff(c_39777,plain,(
    l1_waybel_0(k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_39776])).

tff(c_39835,plain,(
    ! [A_6074,B_6075] :
      ( k2_yellow19(A_6074,k3_yellow19(A_6074,k2_struct_0(A_6074),B_6075)) = B_6075
      | ~ m1_subset_1(B_6075,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_6074)))))
      | ~ v13_waybel_0(B_6075,k3_yellow_1(k2_struct_0(A_6074)))
      | ~ v2_waybel_0(B_6075,k3_yellow_1(k2_struct_0(A_6074)))
      | ~ v1_subset_1(B_6075,u1_struct_0(k3_yellow_1(k2_struct_0(A_6074))))
      | v1_xboole_0(B_6075)
      | ~ l1_struct_0(A_6074)
      | v2_struct_0(A_6074) ) ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_39840,plain,
    ( k2_yellow19('#skF_4',k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5')) = '#skF_5'
    | ~ v13_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_4')))
    | ~ v2_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_4')))
    | ~ v1_subset_1('#skF_5',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4'))))
    | v1_xboole_0('#skF_5')
    | ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_39835])).

tff(c_39847,plain,
    ( k2_yellow19('#skF_4',k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5')) = '#skF_5'
    | v1_xboole_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_37431,c_74,c_72,c_70,c_39840])).

tff(c_39848,plain,(
    k2_yellow19('#skF_4',k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5')) = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_76,c_39847])).

tff(c_60,plain,(
    ! [A_32,B_36,C_38] :
      ( r3_waybel_9(A_32,B_36,C_38)
      | ~ r1_waybel_7(A_32,k2_yellow19(A_32,B_36),C_38)
      | ~ m1_subset_1(C_38,u1_struct_0(A_32))
      | ~ l1_waybel_0(B_36,A_32)
      | ~ v7_waybel_0(B_36)
      | ~ v4_orders_2(B_36)
      | v2_struct_0(B_36)
      | ~ l1_pre_topc(A_32)
      | ~ v2_pre_topc(A_32)
      | v2_struct_0(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_39853,plain,(
    ! [C_38] :
      ( r3_waybel_9('#skF_4',k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'),C_38)
      | ~ r1_waybel_7('#skF_4','#skF_5',C_38)
      | ~ m1_subset_1(C_38,u1_struct_0('#skF_4'))
      | ~ l1_waybel_0(k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'),'#skF_4')
      | ~ v7_waybel_0(k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'))
      | ~ v4_orders_2(k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'))
      | v2_struct_0(k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'))
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_39848,c_60])).

tff(c_39860,plain,(
    ! [C_38] :
      ( r3_waybel_9('#skF_4',k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'),C_38)
      | ~ r1_waybel_7('#skF_4','#skF_5',C_38)
      | ~ m1_subset_1(C_38,u1_struct_0('#skF_4'))
      | v2_struct_0(k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_38920,c_39833,c_39777,c_39853])).

tff(c_39861,plain,(
    ! [C_38] :
      ( r3_waybel_9('#skF_4',k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'),C_38)
      | ~ r1_waybel_7('#skF_4','#skF_5',C_38)
      | ~ m1_subset_1(C_38,u1_struct_0('#skF_4'))
      | v2_struct_0(k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_39860])).

tff(c_40264,plain,(
    v2_struct_0(k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_39861])).

tff(c_52,plain,(
    ! [A_26,B_27,C_28] :
      ( ~ v2_struct_0(k3_yellow19(A_26,B_27,C_28))
      | ~ m1_subset_1(C_28,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_27))))
      | ~ v13_waybel_0(C_28,k3_yellow_1(B_27))
      | ~ v2_waybel_0(C_28,k3_yellow_1(B_27))
      | v1_xboole_0(C_28)
      | ~ m1_subset_1(B_27,k1_zfmisc_1(u1_struct_0(A_26)))
      | v1_xboole_0(B_27)
      | ~ l1_struct_0(A_26)
      | v2_struct_0(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_40266,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4')))))
    | ~ v13_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_4')))
    | ~ v2_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_4')))
    | v1_xboole_0('#skF_5')
    | ~ m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | v1_xboole_0(k2_struct_0('#skF_4'))
    | ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_40264,c_52])).

tff(c_40269,plain,
    ( v1_xboole_0('#skF_5')
    | ~ m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | v1_xboole_0(k2_struct_0('#skF_4'))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_37431,c_72,c_70,c_68,c_40266])).

tff(c_40270,plain,(
    ~ m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_37413,c_76,c_40269])).

tff(c_40273,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_40270])).

tff(c_40277,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_37431,c_40273])).

tff(c_40998,plain,(
    ! [C_6123] :
      ( r3_waybel_9('#skF_4',k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'),C_6123)
      | ~ r1_waybel_7('#skF_4','#skF_5',C_6123)
      | ~ m1_subset_1(C_6123,u1_struct_0('#skF_4')) ) ),
    inference(splitRight,[status(thm)],[c_39861])).

tff(c_41004,plain,
    ( ~ r1_waybel_7('#skF_4','#skF_5','#skF_6')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_40998,c_132])).

tff(c_41009,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_200,c_41004])).

tff(c_41010,plain,(
    ~ r1_waybel_7('#skF_4','#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_41011,plain,(
    r3_waybel_9('#skF_4',k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_44387,plain,(
    ! [A_6291,B_6292] :
      ( k2_yellow19(A_6291,k3_yellow19(A_6291,k2_struct_0(A_6291),B_6292)) = B_6292
      | ~ m1_subset_1(B_6292,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_6291)))))
      | ~ v13_waybel_0(B_6292,k3_yellow_1(k2_struct_0(A_6291)))
      | ~ v2_waybel_0(B_6292,k3_yellow_1(k2_struct_0(A_6291)))
      | ~ v1_subset_1(B_6292,u1_struct_0(k3_yellow_1(k2_struct_0(A_6291))))
      | v1_xboole_0(B_6292)
      | ~ l1_struct_0(A_6291)
      | v2_struct_0(A_6291) ) ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_44392,plain,
    ( k2_yellow19('#skF_4',k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5')) = '#skF_5'
    | ~ v13_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_4')))
    | ~ v2_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_4')))
    | ~ v1_subset_1('#skF_5',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4'))))
    | v1_xboole_0('#skF_5')
    | ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_44387])).

tff(c_44399,plain,
    ( k2_yellow19('#skF_4',k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5')) = '#skF_5'
    | v1_xboole_0('#skF_5')
    | ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_44392])).

tff(c_44400,plain,
    ( k2_yellow19('#skF_4',k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5')) = '#skF_5'
    | ~ l1_struct_0('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_76,c_44399])).

tff(c_44547,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_44400])).

tff(c_44550,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_44547])).

tff(c_44554,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_44550])).

tff(c_44556,plain,(
    l1_struct_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_44400])).

tff(c_43209,plain,(
    ! [A_6240,B_6241,C_6242] :
      ( v4_orders_2(k3_yellow19(A_6240,B_6241,C_6242))
      | ~ m1_subset_1(C_6242,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_6241))))
      | ~ v13_waybel_0(C_6242,k3_yellow_1(B_6241))
      | ~ v2_waybel_0(C_6242,k3_yellow_1(B_6241))
      | v1_xboole_0(C_6242)
      | ~ m1_subset_1(B_6241,k1_zfmisc_1(u1_struct_0(A_6240)))
      | v1_xboole_0(B_6241)
      | ~ l1_struct_0(A_6240)
      | v2_struct_0(A_6240) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_43214,plain,(
    ! [A_6240] :
      ( v4_orders_2(k3_yellow19(A_6240,k2_struct_0('#skF_4'),'#skF_5'))
      | ~ v13_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_4')))
      | ~ v2_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_4')))
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0(A_6240)))
      | v1_xboole_0(k2_struct_0('#skF_4'))
      | ~ l1_struct_0(A_6240)
      | v2_struct_0(A_6240) ) ),
    inference(resolution,[status(thm)],[c_68,c_43209])).

tff(c_43221,plain,(
    ! [A_6240] :
      ( v4_orders_2(k3_yellow19(A_6240,k2_struct_0('#skF_4'),'#skF_5'))
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0(A_6240)))
      | v1_xboole_0(k2_struct_0('#skF_4'))
      | ~ l1_struct_0(A_6240)
      | v2_struct_0(A_6240) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_43214])).

tff(c_43222,plain,(
    ! [A_6240] :
      ( v4_orders_2(k3_yellow19(A_6240,k2_struct_0('#skF_4'),'#skF_5'))
      | ~ m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0(A_6240)))
      | v1_xboole_0(k2_struct_0('#skF_4'))
      | ~ l1_struct_0(A_6240)
      | v2_struct_0(A_6240) ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_43221])).

tff(c_43896,plain,(
    v1_xboole_0(k2_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_43222])).

tff(c_41060,plain,(
    ! [A_6137,B_6138,C_6139] :
      ( k7_subset_1(A_6137,B_6138,C_6139) = k4_xboole_0(B_6138,C_6139)
      | ~ m1_subset_1(B_6138,k1_zfmisc_1(A_6137)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_41067,plain,(
    ! [A_16,C_6139] :
      ( k7_subset_1(u1_struct_0(A_16),k2_struct_0(A_16),C_6139) = k4_xboole_0(k2_struct_0(A_16),C_6139)
      | ~ l1_struct_0(A_16) ) ),
    inference(resolution,[status(thm)],[c_30,c_41060])).

tff(c_41424,plain,(
    ! [A_6185,B_6186] :
      ( k7_subset_1(u1_struct_0(A_6185),k2_struct_0(A_6185),k7_subset_1(u1_struct_0(A_6185),k2_struct_0(A_6185),B_6186)) = B_6186
      | ~ m1_subset_1(B_6186,k1_zfmisc_1(u1_struct_0(A_6185)))
      | ~ l1_struct_0(A_6185) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_81012,plain,(
    ! [A_11926,B_11927] :
      ( k4_xboole_0(k2_struct_0(A_11926),k7_subset_1(u1_struct_0(A_11926),k2_struct_0(A_11926),B_11927)) = B_11927
      | ~ m1_subset_1(B_11927,k1_zfmisc_1(u1_struct_0(A_11926)))
      | ~ l1_struct_0(A_11926)
      | ~ l1_struct_0(A_11926) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_41067,c_41424])).

tff(c_41148,plain,(
    ! [A_6161,B_6162,C_6163] :
      ( r2_hidden('#skF_2'(A_6161,B_6162,C_6163),A_6161)
      | r2_hidden('#skF_3'(A_6161,B_6162,C_6163),C_6163)
      | k4_xboole_0(A_6161,B_6162) = C_6163 ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_41209,plain,(
    ! [A_6167,B_6168] :
      ( r2_hidden('#skF_3'(A_6167,B_6168,A_6167),A_6167)
      | k4_xboole_0(A_6167,B_6168) = A_6167 ) ),
    inference(resolution,[status(thm)],[c_41148,c_18])).

tff(c_41227,plain,(
    ! [A_6167,B_6168] :
      ( ~ v1_xboole_0(A_6167)
      | k4_xboole_0(A_6167,B_6168) = A_6167 ) ),
    inference(resolution,[status(thm)],[c_41209,c_2])).

tff(c_43911,plain,(
    ! [B_6168] : k4_xboole_0(k2_struct_0('#skF_4'),B_6168) = k2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_43896,c_41227])).

tff(c_81249,plain,(
    ! [B_11927] :
      ( k2_struct_0('#skF_4') = B_11927
      | ~ m1_subset_1(B_11927,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_struct_0('#skF_4')
      | ~ l1_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_81012,c_43911])).

tff(c_81348,plain,(
    ! [B_11952] :
      ( k2_struct_0('#skF_4') = B_11952
      | ~ m1_subset_1(B_11952,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44556,c_44556,c_81249])).

tff(c_81361,plain,(
    u1_struct_0('#skF_4') = k2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_91,c_81348])).

tff(c_81382,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_4'))
    | ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_81361,c_34])).

tff(c_81396,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44556,c_43896,c_81382])).

tff(c_81398,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_81396])).

tff(c_81401,plain,(
    ! [A_12001] :
      ( v4_orders_2(k3_yellow19(A_12001,k2_struct_0('#skF_4'),'#skF_5'))
      | ~ m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0(A_12001)))
      | ~ l1_struct_0(A_12001)
      | v2_struct_0(A_12001) ) ),
    inference(splitRight,[status(thm)],[c_43222])).

tff(c_81405,plain,
    ( v4_orders_2(k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'))
    | v2_struct_0('#skF_4')
    | ~ l1_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_81401])).

tff(c_81408,plain,
    ( v4_orders_2(k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'))
    | ~ l1_struct_0('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_81405])).

tff(c_81409,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_81408])).

tff(c_81412,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_81409])).

tff(c_81416,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_81412])).

tff(c_81418,plain,(
    l1_struct_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_81408])).

tff(c_81400,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_43222])).

tff(c_81417,plain,(
    v4_orders_2(k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5')) ),
    inference(splitRight,[status(thm)],[c_81408])).

tff(c_83012,plain,(
    ! [A_12038,B_12039,C_12040] :
      ( v7_waybel_0(k3_yellow19(A_12038,B_12039,C_12040))
      | ~ m1_subset_1(C_12040,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_12039))))
      | ~ v13_waybel_0(C_12040,k3_yellow_1(B_12039))
      | ~ v2_waybel_0(C_12040,k3_yellow_1(B_12039))
      | ~ v1_subset_1(C_12040,u1_struct_0(k3_yellow_1(B_12039)))
      | v1_xboole_0(C_12040)
      | ~ m1_subset_1(B_12039,k1_zfmisc_1(u1_struct_0(A_12038)))
      | v1_xboole_0(B_12039)
      | ~ l1_struct_0(A_12038)
      | v2_struct_0(A_12038) ) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_83017,plain,(
    ! [A_12038] :
      ( v7_waybel_0(k3_yellow19(A_12038,k2_struct_0('#skF_4'),'#skF_5'))
      | ~ v13_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_4')))
      | ~ v2_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_4')))
      | ~ v1_subset_1('#skF_5',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4'))))
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0(A_12038)))
      | v1_xboole_0(k2_struct_0('#skF_4'))
      | ~ l1_struct_0(A_12038)
      | v2_struct_0(A_12038) ) ),
    inference(resolution,[status(thm)],[c_68,c_83012])).

tff(c_83024,plain,(
    ! [A_12038] :
      ( v7_waybel_0(k3_yellow19(A_12038,k2_struct_0('#skF_4'),'#skF_5'))
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0(A_12038)))
      | v1_xboole_0(k2_struct_0('#skF_4'))
      | ~ l1_struct_0(A_12038)
      | v2_struct_0(A_12038) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_83017])).

tff(c_83609,plain,(
    ! [A_12045] :
      ( v7_waybel_0(k3_yellow19(A_12045,k2_struct_0('#skF_4'),'#skF_5'))
      | ~ m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0(A_12045)))
      | ~ l1_struct_0(A_12045)
      | v2_struct_0(A_12045) ) ),
    inference(negUnitSimplification,[status(thm)],[c_81400,c_76,c_83024])).

tff(c_83613,plain,
    ( v7_waybel_0(k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'))
    | v2_struct_0('#skF_4')
    | ~ l1_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_83609])).

tff(c_83616,plain,
    ( v7_waybel_0(k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_81418,c_83613])).

tff(c_83617,plain,(
    v7_waybel_0(k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_83616])).

tff(c_82275,plain,(
    ! [A_12022,B_12023,C_12024] :
      ( l1_waybel_0(k3_yellow19(A_12022,B_12023,C_12024),A_12022)
      | ~ m1_subset_1(C_12024,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_12023))))
      | ~ v13_waybel_0(C_12024,k3_yellow_1(B_12023))
      | ~ v2_waybel_0(C_12024,k3_yellow_1(B_12023))
      | v1_xboole_0(C_12024)
      | ~ m1_subset_1(B_12023,k1_zfmisc_1(u1_struct_0(A_12022)))
      | v1_xboole_0(B_12023)
      | ~ l1_struct_0(A_12022)
      | v2_struct_0(A_12022) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_82280,plain,(
    ! [A_12022] :
      ( l1_waybel_0(k3_yellow19(A_12022,k2_struct_0('#skF_4'),'#skF_5'),A_12022)
      | ~ v13_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_4')))
      | ~ v2_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_4')))
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0(A_12022)))
      | v1_xboole_0(k2_struct_0('#skF_4'))
      | ~ l1_struct_0(A_12022)
      | v2_struct_0(A_12022) ) ),
    inference(resolution,[status(thm)],[c_68,c_82275])).

tff(c_82287,plain,(
    ! [A_12022] :
      ( l1_waybel_0(k3_yellow19(A_12022,k2_struct_0('#skF_4'),'#skF_5'),A_12022)
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0(A_12022)))
      | v1_xboole_0(k2_struct_0('#skF_4'))
      | ~ l1_struct_0(A_12022)
      | v2_struct_0(A_12022) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_82280])).

tff(c_82487,plain,(
    ! [A_12029] :
      ( l1_waybel_0(k3_yellow19(A_12029,k2_struct_0('#skF_4'),'#skF_5'),A_12029)
      | ~ m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0(A_12029)))
      | ~ l1_struct_0(A_12029)
      | v2_struct_0(A_12029) ) ),
    inference(negUnitSimplification,[status(thm)],[c_81400,c_76,c_82287])).

tff(c_82490,plain,
    ( l1_waybel_0(k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'),'#skF_4')
    | v2_struct_0('#skF_4')
    | ~ l1_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_82487])).

tff(c_82493,plain,
    ( l1_waybel_0(k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'),'#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_81418,c_82490])).

tff(c_82494,plain,(
    l1_waybel_0(k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_82493])).

tff(c_83736,plain,(
    ! [A_12049,B_12050] :
      ( k2_yellow19(A_12049,k3_yellow19(A_12049,k2_struct_0(A_12049),B_12050)) = B_12050
      | ~ m1_subset_1(B_12050,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_12049)))))
      | ~ v13_waybel_0(B_12050,k3_yellow_1(k2_struct_0(A_12049)))
      | ~ v2_waybel_0(B_12050,k3_yellow_1(k2_struct_0(A_12049)))
      | ~ v1_subset_1(B_12050,u1_struct_0(k3_yellow_1(k2_struct_0(A_12049))))
      | v1_xboole_0(B_12050)
      | ~ l1_struct_0(A_12049)
      | v2_struct_0(A_12049) ) ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_83741,plain,
    ( k2_yellow19('#skF_4',k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5')) = '#skF_5'
    | ~ v13_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_4')))
    | ~ v2_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_4')))
    | ~ v1_subset_1('#skF_5',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4'))))
    | v1_xboole_0('#skF_5')
    | ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_83736])).

tff(c_83748,plain,
    ( k2_yellow19('#skF_4',k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5')) = '#skF_5'
    | v1_xboole_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_81418,c_74,c_72,c_70,c_83741])).

tff(c_83749,plain,(
    k2_yellow19('#skF_4',k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5')) = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_76,c_83748])).

tff(c_83757,plain,(
    ! [C_38] :
      ( r3_waybel_9('#skF_4',k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'),C_38)
      | ~ r1_waybel_7('#skF_4','#skF_5',C_38)
      | ~ m1_subset_1(C_38,u1_struct_0('#skF_4'))
      | ~ l1_waybel_0(k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'),'#skF_4')
      | ~ v7_waybel_0(k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'))
      | ~ v4_orders_2(k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'))
      | v2_struct_0(k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'))
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_83749,c_60])).

tff(c_83764,plain,(
    ! [C_38] :
      ( r3_waybel_9('#skF_4',k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'),C_38)
      | ~ r1_waybel_7('#skF_4','#skF_5',C_38)
      | ~ m1_subset_1(C_38,u1_struct_0('#skF_4'))
      | v2_struct_0(k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_81417,c_83617,c_82494,c_83757])).

tff(c_83765,plain,(
    ! [C_38] :
      ( r3_waybel_9('#skF_4',k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'),C_38)
      | ~ r1_waybel_7('#skF_4','#skF_5',C_38)
      | ~ m1_subset_1(C_38,u1_struct_0('#skF_4'))
      | v2_struct_0(k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_83764])).

tff(c_84054,plain,(
    v2_struct_0(k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_83765])).

tff(c_84056,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4')))))
    | ~ v13_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_4')))
    | ~ v2_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_4')))
    | v1_xboole_0('#skF_5')
    | ~ m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | v1_xboole_0(k2_struct_0('#skF_4'))
    | ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_84054,c_52])).

tff(c_84059,plain,
    ( v1_xboole_0('#skF_5')
    | ~ m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | v1_xboole_0(k2_struct_0('#skF_4'))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_81418,c_72,c_70,c_68,c_84056])).

tff(c_84060,plain,(
    ~ m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_81400,c_76,c_84059])).

tff(c_84063,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_84060])).

tff(c_84067,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_81418,c_84063])).

tff(c_84069,plain,(
    ~ v2_struct_0(k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5')) ),
    inference(splitRight,[status(thm)],[c_83765])).

tff(c_62,plain,(
    ! [A_32,B_36,C_38] :
      ( r1_waybel_7(A_32,k2_yellow19(A_32,B_36),C_38)
      | ~ r3_waybel_9(A_32,B_36,C_38)
      | ~ m1_subset_1(C_38,u1_struct_0(A_32))
      | ~ l1_waybel_0(B_36,A_32)
      | ~ v7_waybel_0(B_36)
      | ~ v4_orders_2(B_36)
      | v2_struct_0(B_36)
      | ~ l1_pre_topc(A_32)
      | ~ v2_pre_topc(A_32)
      | v2_struct_0(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_83754,plain,(
    ! [C_38] :
      ( r1_waybel_7('#skF_4','#skF_5',C_38)
      | ~ r3_waybel_9('#skF_4',k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'),C_38)
      | ~ m1_subset_1(C_38,u1_struct_0('#skF_4'))
      | ~ l1_waybel_0(k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'),'#skF_4')
      | ~ v7_waybel_0(k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'))
      | ~ v4_orders_2(k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'))
      | v2_struct_0(k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'))
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_83749,c_62])).

tff(c_83761,plain,(
    ! [C_38] :
      ( r1_waybel_7('#skF_4','#skF_5',C_38)
      | ~ r3_waybel_9('#skF_4',k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'),C_38)
      | ~ m1_subset_1(C_38,u1_struct_0('#skF_4'))
      | v2_struct_0(k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_81417,c_83617,c_82494,c_83754])).

tff(c_83762,plain,(
    ! [C_38] :
      ( r1_waybel_7('#skF_4','#skF_5',C_38)
      | ~ r3_waybel_9('#skF_4',k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'),C_38)
      | ~ m1_subset_1(C_38,u1_struct_0('#skF_4'))
      | v2_struct_0(k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_83761])).

tff(c_84225,plain,(
    ! [C_12068] :
      ( r1_waybel_7('#skF_4','#skF_5',C_12068)
      | ~ r3_waybel_9('#skF_4',k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'),C_12068)
      | ~ m1_subset_1(C_12068,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_84069,c_83762])).

tff(c_84228,plain,
    ( r1_waybel_7('#skF_4','#skF_5','#skF_6')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_41011,c_84225])).

tff(c_84231,plain,(
    r1_waybel_7('#skF_4','#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_84228])).

tff(c_84233,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_41010,c_84231])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 09:38:11 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 26.48/13.02  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 26.55/13.05  
% 26.55/13.05  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 26.55/13.05  %$ r3_waybel_9 > r1_waybel_7 > v6_waybel_0 > v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_hidden > m1_subset_1 > l1_waybel_0 > v7_waybel_0 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k7_subset_1 > k3_yellow19 > k4_xboole_0 > k2_yellow19 > #nlpp > u1_struct_0 > k3_yellow_1 > k3_lattice3 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_lattice3 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3
% 26.55/13.05  
% 26.55/13.05  %Foreground sorts:
% 26.55/13.05  
% 26.55/13.05  
% 26.55/13.05  %Background operators:
% 26.55/13.05  
% 26.55/13.05  
% 26.55/13.05  %Foreground operators:
% 26.55/13.05  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 26.55/13.05  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 26.55/13.05  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 26.55/13.05  tff(k3_lattice3, type, k3_lattice3: $i > $i).
% 26.55/13.05  tff(v6_waybel_0, type, v6_waybel_0: ($i * $i) > $o).
% 26.55/13.05  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 26.55/13.05  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 26.55/13.05  tff(k3_yellow_1, type, k3_yellow_1: $i > $i).
% 26.55/13.05  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 26.55/13.05  tff('#skF_1', type, '#skF_1': $i > $i).
% 26.55/13.05  tff(v2_waybel_0, type, v2_waybel_0: ($i * $i) > $o).
% 26.55/13.05  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 26.55/13.05  tff(v7_waybel_0, type, v7_waybel_0: $i > $o).
% 26.55/13.05  tff('#skF_5', type, '#skF_5': $i).
% 26.55/13.05  tff(r3_waybel_9, type, r3_waybel_9: ($i * $i * $i) > $o).
% 26.55/13.05  tff('#skF_6', type, '#skF_6': $i).
% 26.55/13.05  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 26.55/13.05  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 26.55/13.05  tff(k1_lattice3, type, k1_lattice3: $i > $i).
% 26.55/13.05  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 26.55/13.05  tff(r1_waybel_7, type, r1_waybel_7: ($i * $i * $i) > $o).
% 26.55/13.05  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 26.55/13.05  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 26.55/13.05  tff(k2_yellow19, type, k2_yellow19: ($i * $i) > $i).
% 26.55/13.05  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 26.55/13.05  tff(l1_waybel_0, type, l1_waybel_0: ($i * $i) > $o).
% 26.55/13.05  tff('#skF_4', type, '#skF_4': $i).
% 26.55/13.05  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 26.55/13.05  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 26.55/13.05  tff(k3_yellow19, type, k3_yellow19: ($i * $i * $i) > $i).
% 26.55/13.05  tff(v13_waybel_0, type, v13_waybel_0: ($i * $i) > $o).
% 26.55/13.05  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 26.55/13.05  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 26.55/13.05  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 26.55/13.05  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 26.55/13.05  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 26.55/13.05  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 26.55/13.05  
% 26.55/13.08  tff(f_226, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((((~v1_xboole_0(B) & v1_subset_1(B, u1_struct_0(k3_yellow_1(k2_struct_0(A))))) & v2_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & v13_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A)))))) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r3_waybel_9(A, k3_yellow19(A, k2_struct_0(A), B), C) <=> r1_waybel_7(A, B, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_yellow19)).
% 26.55/13.08  tff(f_57, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 26.55/13.08  tff(f_53, axiom, (![A]: (l1_struct_0(A) => m1_subset_1(k2_struct_0(A), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_struct_0)).
% 26.55/13.08  tff(f_199, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: (((((~v1_xboole_0(B) & v1_subset_1(B, u1_struct_0(k3_yellow_1(k2_struct_0(A))))) & v2_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & v13_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A)))))) => (B = k2_yellow19(A, k3_yellow19(A, k2_struct_0(A), B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t15_yellow19)).
% 26.55/13.08  tff(f_128, axiom, (![A, B, C]: ((((((((~v2_struct_0(A) & l1_struct_0(A)) & ~v1_xboole_0(B)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) & ~v1_xboole_0(C)) & v2_waybel_0(C, k3_yellow_1(B))) & v13_waybel_0(C, k3_yellow_1(B))) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B))))) => (((~v2_struct_0(k3_yellow19(A, B, C)) & v3_orders_2(k3_yellow19(A, B, C))) & v4_orders_2(k3_yellow19(A, B, C))) & v6_waybel_0(k3_yellow19(A, B, C), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_yellow19)).
% 26.55/13.08  tff(f_43, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 26.55/13.08  tff(f_45, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 26.55/13.08  tff(f_49, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 26.55/13.08  tff(f_72, axiom, (![A]: (l1_struct_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k7_subset_1(u1_struct_0(A), k2_struct_0(A), k7_subset_1(u1_struct_0(A), k2_struct_0(A), B)) = B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_pre_topc)).
% 26.55/13.08  tff(f_41, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 26.55/13.08  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 26.55/13.08  tff(f_65, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 26.55/13.08  tff(f_156, axiom, (![A, B, C]: (((((((((~v2_struct_0(A) & l1_struct_0(A)) & ~v1_xboole_0(B)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) & ~v1_xboole_0(C)) & v1_subset_1(C, u1_struct_0(k3_yellow_1(B)))) & v2_waybel_0(C, k3_yellow_1(B))) & v13_waybel_0(C, k3_yellow_1(B))) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B))))) => ((~v2_struct_0(k3_yellow19(A, B, C)) & v6_waybel_0(k3_yellow19(A, B, C), A)) & v7_waybel_0(k3_yellow19(A, B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc5_yellow19)).
% 26.55/13.08  tff(f_100, axiom, (![A, B, C]: ((((((((~v2_struct_0(A) & l1_struct_0(A)) & ~v1_xboole_0(B)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) & ~v1_xboole_0(C)) & v2_waybel_0(C, k3_yellow_1(B))) & v13_waybel_0(C, k3_yellow_1(B))) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B))))) => ((~v2_struct_0(k3_yellow19(A, B, C)) & v6_waybel_0(k3_yellow19(A, B, C), A)) & l1_waybel_0(k3_yellow19(A, B, C), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_yellow19)).
% 26.55/13.08  tff(f_180, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r3_waybel_9(A, B, C) <=> r1_waybel_7(A, k2_yellow19(A, B), C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_yellow19)).
% 26.55/13.08  tff(c_66, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_226])).
% 26.55/13.08  tff(c_84, plain, (~r1_waybel_7('#skF_4', '#skF_5', '#skF_6') | ~r3_waybel_9('#skF_4', k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_226])).
% 26.55/13.08  tff(c_132, plain, (~r3_waybel_9('#skF_4', k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5'), '#skF_6')), inference(splitLeft, [status(thm)], [c_84])).
% 26.55/13.08  tff(c_90, plain, (r3_waybel_9('#skF_4', k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5'), '#skF_6') | r1_waybel_7('#skF_4', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_226])).
% 26.55/13.08  tff(c_200, plain, (r1_waybel_7('#skF_4', '#skF_5', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_132, c_90])).
% 26.55/13.08  tff(c_78, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_226])).
% 26.55/13.08  tff(c_32, plain, (![A_17]: (l1_struct_0(A_17) | ~l1_pre_topc(A_17))), inference(cnfTransformation, [status(thm)], [f_57])).
% 26.55/13.08  tff(c_82, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_226])).
% 26.55/13.08  tff(c_30, plain, (![A_16]: (m1_subset_1(k2_struct_0(A_16), k1_zfmisc_1(u1_struct_0(A_16))) | ~l1_struct_0(A_16))), inference(cnfTransformation, [status(thm)], [f_53])).
% 26.55/13.08  tff(c_76, plain, (~v1_xboole_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_226])).
% 26.55/13.08  tff(c_74, plain, (v1_subset_1('#skF_5', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_226])).
% 26.55/13.08  tff(c_72, plain, (v2_waybel_0('#skF_5', k3_yellow_1(k2_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_226])).
% 26.55/13.08  tff(c_70, plain, (v13_waybel_0('#skF_5', k3_yellow_1(k2_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_226])).
% 26.55/13.08  tff(c_68, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4')))))), inference(cnfTransformation, [status(thm)], [f_226])).
% 26.55/13.08  tff(c_3652, plain, (![A_229, B_230]: (k2_yellow19(A_229, k3_yellow19(A_229, k2_struct_0(A_229), B_230))=B_230 | ~m1_subset_1(B_230, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_229))))) | ~v13_waybel_0(B_230, k3_yellow_1(k2_struct_0(A_229))) | ~v2_waybel_0(B_230, k3_yellow_1(k2_struct_0(A_229))) | ~v1_subset_1(B_230, u1_struct_0(k3_yellow_1(k2_struct_0(A_229)))) | v1_xboole_0(B_230) | ~l1_struct_0(A_229) | v2_struct_0(A_229))), inference(cnfTransformation, [status(thm)], [f_199])).
% 26.55/13.08  tff(c_3657, plain, (k2_yellow19('#skF_4', k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5'))='#skF_5' | ~v13_waybel_0('#skF_5', k3_yellow_1(k2_struct_0('#skF_4'))) | ~v2_waybel_0('#skF_5', k3_yellow_1(k2_struct_0('#skF_4'))) | ~v1_subset_1('#skF_5', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4')))) | v1_xboole_0('#skF_5') | ~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_68, c_3652])).
% 26.55/13.08  tff(c_3664, plain, (k2_yellow19('#skF_4', k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5'))='#skF_5' | v1_xboole_0('#skF_5') | ~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_70, c_3657])).
% 26.55/13.08  tff(c_3665, plain, (k2_yellow19('#skF_4', k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5'))='#skF_5' | ~l1_struct_0('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_82, c_76, c_3664])).
% 26.55/13.08  tff(c_3667, plain, (~l1_struct_0('#skF_4')), inference(splitLeft, [status(thm)], [c_3665])).
% 26.55/13.08  tff(c_3670, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_32, c_3667])).
% 26.55/13.08  tff(c_3674, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_78, c_3670])).
% 26.55/13.08  tff(c_3676, plain, (l1_struct_0('#skF_4')), inference(splitRight, [status(thm)], [c_3665])).
% 26.55/13.08  tff(c_2691, plain, (![A_185, B_186, C_187]: (v3_orders_2(k3_yellow19(A_185, B_186, C_187)) | ~m1_subset_1(C_187, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_186)))) | ~v13_waybel_0(C_187, k3_yellow_1(B_186)) | ~v2_waybel_0(C_187, k3_yellow_1(B_186)) | v1_xboole_0(C_187) | ~m1_subset_1(B_186, k1_zfmisc_1(u1_struct_0(A_185))) | v1_xboole_0(B_186) | ~l1_struct_0(A_185) | v2_struct_0(A_185))), inference(cnfTransformation, [status(thm)], [f_128])).
% 26.55/13.08  tff(c_2696, plain, (![A_185]: (v3_orders_2(k3_yellow19(A_185, k2_struct_0('#skF_4'), '#skF_5')) | ~v13_waybel_0('#skF_5', k3_yellow_1(k2_struct_0('#skF_4'))) | ~v2_waybel_0('#skF_5', k3_yellow_1(k2_struct_0('#skF_4'))) | v1_xboole_0('#skF_5') | ~m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(u1_struct_0(A_185))) | v1_xboole_0(k2_struct_0('#skF_4')) | ~l1_struct_0(A_185) | v2_struct_0(A_185))), inference(resolution, [status(thm)], [c_68, c_2691])).
% 26.55/13.08  tff(c_2703, plain, (![A_185]: (v3_orders_2(k3_yellow19(A_185, k2_struct_0('#skF_4'), '#skF_5')) | v1_xboole_0('#skF_5') | ~m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(u1_struct_0(A_185))) | v1_xboole_0(k2_struct_0('#skF_4')) | ~l1_struct_0(A_185) | v2_struct_0(A_185))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_2696])).
% 26.55/13.08  tff(c_2704, plain, (![A_185]: (v3_orders_2(k3_yellow19(A_185, k2_struct_0('#skF_4'), '#skF_5')) | ~m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(u1_struct_0(A_185))) | v1_xboole_0(k2_struct_0('#skF_4')) | ~l1_struct_0(A_185) | v2_struct_0(A_185))), inference(negUnitSimplification, [status(thm)], [c_76, c_2703])).
% 26.55/13.08  tff(c_2976, plain, (v1_xboole_0(k2_struct_0('#skF_4'))), inference(splitLeft, [status(thm)], [c_2704])).
% 26.55/13.08  tff(c_24, plain, (![A_11]: (k2_subset_1(A_11)=A_11)), inference(cnfTransformation, [status(thm)], [f_43])).
% 26.55/13.08  tff(c_26, plain, (![A_12]: (m1_subset_1(k2_subset_1(A_12), k1_zfmisc_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 26.55/13.08  tff(c_91, plain, (![A_12]: (m1_subset_1(A_12, k1_zfmisc_1(A_12)))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_26])).
% 26.55/13.08  tff(c_181, plain, (![A_74, B_75, C_76]: (k7_subset_1(A_74, B_75, C_76)=k4_xboole_0(B_75, C_76) | ~m1_subset_1(B_75, k1_zfmisc_1(A_74)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 26.55/13.08  tff(c_188, plain, (![A_16, C_76]: (k7_subset_1(u1_struct_0(A_16), k2_struct_0(A_16), C_76)=k4_xboole_0(k2_struct_0(A_16), C_76) | ~l1_struct_0(A_16))), inference(resolution, [status(thm)], [c_30, c_181])).
% 26.55/13.08  tff(c_554, plain, (![A_117, B_118]: (k7_subset_1(u1_struct_0(A_117), k2_struct_0(A_117), k7_subset_1(u1_struct_0(A_117), k2_struct_0(A_117), B_118))=B_118 | ~m1_subset_1(B_118, k1_zfmisc_1(u1_struct_0(A_117))) | ~l1_struct_0(A_117))), inference(cnfTransformation, [status(thm)], [f_72])).
% 26.55/13.08  tff(c_37012, plain, (![A_5945, B_5946]: (k4_xboole_0(k2_struct_0(A_5945), k7_subset_1(u1_struct_0(A_5945), k2_struct_0(A_5945), B_5946))=B_5946 | ~m1_subset_1(B_5946, k1_zfmisc_1(u1_struct_0(A_5945))) | ~l1_struct_0(A_5945) | ~l1_struct_0(A_5945))), inference(superposition, [status(thm), theory('equality')], [c_188, c_554])).
% 26.55/13.08  tff(c_308, plain, (![A_108, B_109, C_110]: (r2_hidden('#skF_2'(A_108, B_109, C_110), A_108) | r2_hidden('#skF_3'(A_108, B_109, C_110), C_110) | k4_xboole_0(A_108, B_109)=C_110)), inference(cnfTransformation, [status(thm)], [f_41])).
% 26.55/13.08  tff(c_18, plain, (![A_5, B_6, C_7]: (~r2_hidden('#skF_2'(A_5, B_6, C_7), C_7) | r2_hidden('#skF_3'(A_5, B_6, C_7), C_7) | k4_xboole_0(A_5, B_6)=C_7)), inference(cnfTransformation, [status(thm)], [f_41])).
% 26.55/13.08  tff(c_1250, plain, (![A_148, B_149]: (r2_hidden('#skF_3'(A_148, B_149, A_148), A_148) | k4_xboole_0(A_148, B_149)=A_148)), inference(resolution, [status(thm)], [c_308, c_18])).
% 26.55/13.08  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 26.55/13.08  tff(c_1275, plain, (![A_148, B_149]: (~v1_xboole_0(A_148) | k4_xboole_0(A_148, B_149)=A_148)), inference(resolution, [status(thm)], [c_1250, c_2])).
% 26.55/13.08  tff(c_2989, plain, (![B_149]: (k4_xboole_0(k2_struct_0('#skF_4'), B_149)=k2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_2976, c_1275])).
% 26.55/13.08  tff(c_37249, plain, (![B_5946]: (k2_struct_0('#skF_4')=B_5946 | ~m1_subset_1(B_5946, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_struct_0('#skF_4') | ~l1_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_37012, c_2989])).
% 26.55/13.08  tff(c_37356, plain, (![B_5971]: (k2_struct_0('#skF_4')=B_5971 | ~m1_subset_1(B_5971, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_3676, c_3676, c_37249])).
% 26.55/13.08  tff(c_37369, plain, (u1_struct_0('#skF_4')=k2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_91, c_37356])).
% 26.55/13.08  tff(c_34, plain, (![A_18]: (~v1_xboole_0(u1_struct_0(A_18)) | ~l1_struct_0(A_18) | v2_struct_0(A_18))), inference(cnfTransformation, [status(thm)], [f_65])).
% 26.55/13.08  tff(c_37393, plain, (~v1_xboole_0(k2_struct_0('#skF_4')) | ~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_37369, c_34])).
% 26.55/13.08  tff(c_37409, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3676, c_2976, c_37393])).
% 26.55/13.08  tff(c_37411, plain, $false, inference(negUnitSimplification, [status(thm)], [c_82, c_37409])).
% 26.55/13.08  tff(c_37414, plain, (![A_6020]: (v3_orders_2(k3_yellow19(A_6020, k2_struct_0('#skF_4'), '#skF_5')) | ~m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(u1_struct_0(A_6020))) | ~l1_struct_0(A_6020) | v2_struct_0(A_6020))), inference(splitRight, [status(thm)], [c_2704])).
% 26.55/13.08  tff(c_37418, plain, (v3_orders_2(k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5')) | v2_struct_0('#skF_4') | ~l1_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_30, c_37414])).
% 26.55/13.08  tff(c_37421, plain, (v3_orders_2(k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5')) | ~l1_struct_0('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_82, c_37418])).
% 26.55/13.08  tff(c_37422, plain, (~l1_struct_0('#skF_4')), inference(splitLeft, [status(thm)], [c_37421])).
% 26.55/13.08  tff(c_37425, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_32, c_37422])).
% 26.55/13.08  tff(c_37429, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_78, c_37425])).
% 26.55/13.08  tff(c_37431, plain, (l1_struct_0('#skF_4')), inference(splitRight, [status(thm)], [c_37421])).
% 26.55/13.08  tff(c_37413, plain, (~v1_xboole_0(k2_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_2704])).
% 26.55/13.08  tff(c_80, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_226])).
% 26.55/13.08  tff(c_37500, plain, (![A_6027, B_6028, C_6029]: (v4_orders_2(k3_yellow19(A_6027, B_6028, C_6029)) | ~m1_subset_1(C_6029, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_6028)))) | ~v13_waybel_0(C_6029, k3_yellow_1(B_6028)) | ~v2_waybel_0(C_6029, k3_yellow_1(B_6028)) | v1_xboole_0(C_6029) | ~m1_subset_1(B_6028, k1_zfmisc_1(u1_struct_0(A_6027))) | v1_xboole_0(B_6028) | ~l1_struct_0(A_6027) | v2_struct_0(A_6027))), inference(cnfTransformation, [status(thm)], [f_128])).
% 26.55/13.08  tff(c_37505, plain, (![A_6027]: (v4_orders_2(k3_yellow19(A_6027, k2_struct_0('#skF_4'), '#skF_5')) | ~v13_waybel_0('#skF_5', k3_yellow_1(k2_struct_0('#skF_4'))) | ~v2_waybel_0('#skF_5', k3_yellow_1(k2_struct_0('#skF_4'))) | v1_xboole_0('#skF_5') | ~m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(u1_struct_0(A_6027))) | v1_xboole_0(k2_struct_0('#skF_4')) | ~l1_struct_0(A_6027) | v2_struct_0(A_6027))), inference(resolution, [status(thm)], [c_68, c_37500])).
% 26.55/13.08  tff(c_37512, plain, (![A_6027]: (v4_orders_2(k3_yellow19(A_6027, k2_struct_0('#skF_4'), '#skF_5')) | v1_xboole_0('#skF_5') | ~m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(u1_struct_0(A_6027))) | v1_xboole_0(k2_struct_0('#skF_4')) | ~l1_struct_0(A_6027) | v2_struct_0(A_6027))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_37505])).
% 26.55/13.08  tff(c_38912, plain, (![A_6053]: (v4_orders_2(k3_yellow19(A_6053, k2_struct_0('#skF_4'), '#skF_5')) | ~m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(u1_struct_0(A_6053))) | ~l1_struct_0(A_6053) | v2_struct_0(A_6053))), inference(negUnitSimplification, [status(thm)], [c_37413, c_76, c_37512])).
% 26.55/13.08  tff(c_38916, plain, (v4_orders_2(k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5')) | v2_struct_0('#skF_4') | ~l1_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_30, c_38912])).
% 26.55/13.08  tff(c_38919, plain, (v4_orders_2(k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5')) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_37431, c_38916])).
% 26.55/13.08  tff(c_38920, plain, (v4_orders_2(k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_82, c_38919])).
% 26.55/13.08  tff(c_39810, plain, (![A_6070, B_6071, C_6072]: (v7_waybel_0(k3_yellow19(A_6070, B_6071, C_6072)) | ~m1_subset_1(C_6072, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_6071)))) | ~v13_waybel_0(C_6072, k3_yellow_1(B_6071)) | ~v2_waybel_0(C_6072, k3_yellow_1(B_6071)) | ~v1_subset_1(C_6072, u1_struct_0(k3_yellow_1(B_6071))) | v1_xboole_0(C_6072) | ~m1_subset_1(B_6071, k1_zfmisc_1(u1_struct_0(A_6070))) | v1_xboole_0(B_6071) | ~l1_struct_0(A_6070) | v2_struct_0(A_6070))), inference(cnfTransformation, [status(thm)], [f_156])).
% 26.55/13.08  tff(c_39815, plain, (![A_6070]: (v7_waybel_0(k3_yellow19(A_6070, k2_struct_0('#skF_4'), '#skF_5')) | ~v13_waybel_0('#skF_5', k3_yellow_1(k2_struct_0('#skF_4'))) | ~v2_waybel_0('#skF_5', k3_yellow_1(k2_struct_0('#skF_4'))) | ~v1_subset_1('#skF_5', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4')))) | v1_xboole_0('#skF_5') | ~m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(u1_struct_0(A_6070))) | v1_xboole_0(k2_struct_0('#skF_4')) | ~l1_struct_0(A_6070) | v2_struct_0(A_6070))), inference(resolution, [status(thm)], [c_68, c_39810])).
% 26.55/13.08  tff(c_39822, plain, (![A_6070]: (v7_waybel_0(k3_yellow19(A_6070, k2_struct_0('#skF_4'), '#skF_5')) | v1_xboole_0('#skF_5') | ~m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(u1_struct_0(A_6070))) | v1_xboole_0(k2_struct_0('#skF_4')) | ~l1_struct_0(A_6070) | v2_struct_0(A_6070))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_70, c_39815])).
% 26.55/13.08  tff(c_39825, plain, (![A_6073]: (v7_waybel_0(k3_yellow19(A_6073, k2_struct_0('#skF_4'), '#skF_5')) | ~m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(u1_struct_0(A_6073))) | ~l1_struct_0(A_6073) | v2_struct_0(A_6073))), inference(negUnitSimplification, [status(thm)], [c_37413, c_76, c_39822])).
% 26.55/13.08  tff(c_39829, plain, (v7_waybel_0(k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5')) | v2_struct_0('#skF_4') | ~l1_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_30, c_39825])).
% 26.55/13.08  tff(c_39832, plain, (v7_waybel_0(k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5')) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_37431, c_39829])).
% 26.55/13.08  tff(c_39833, plain, (v7_waybel_0(k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_82, c_39832])).
% 26.55/13.08  tff(c_38167, plain, (![A_6042, B_6043, C_6044]: (l1_waybel_0(k3_yellow19(A_6042, B_6043, C_6044), A_6042) | ~m1_subset_1(C_6044, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_6043)))) | ~v13_waybel_0(C_6044, k3_yellow_1(B_6043)) | ~v2_waybel_0(C_6044, k3_yellow_1(B_6043)) | v1_xboole_0(C_6044) | ~m1_subset_1(B_6043, k1_zfmisc_1(u1_struct_0(A_6042))) | v1_xboole_0(B_6043) | ~l1_struct_0(A_6042) | v2_struct_0(A_6042))), inference(cnfTransformation, [status(thm)], [f_100])).
% 26.55/13.08  tff(c_38172, plain, (![A_6042]: (l1_waybel_0(k3_yellow19(A_6042, k2_struct_0('#skF_4'), '#skF_5'), A_6042) | ~v13_waybel_0('#skF_5', k3_yellow_1(k2_struct_0('#skF_4'))) | ~v2_waybel_0('#skF_5', k3_yellow_1(k2_struct_0('#skF_4'))) | v1_xboole_0('#skF_5') | ~m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(u1_struct_0(A_6042))) | v1_xboole_0(k2_struct_0('#skF_4')) | ~l1_struct_0(A_6042) | v2_struct_0(A_6042))), inference(resolution, [status(thm)], [c_68, c_38167])).
% 26.55/13.08  tff(c_38179, plain, (![A_6042]: (l1_waybel_0(k3_yellow19(A_6042, k2_struct_0('#skF_4'), '#skF_5'), A_6042) | v1_xboole_0('#skF_5') | ~m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(u1_struct_0(A_6042))) | v1_xboole_0(k2_struct_0('#skF_4')) | ~l1_struct_0(A_6042) | v2_struct_0(A_6042))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_38172])).
% 26.55/13.08  tff(c_39770, plain, (![A_6065]: (l1_waybel_0(k3_yellow19(A_6065, k2_struct_0('#skF_4'), '#skF_5'), A_6065) | ~m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(u1_struct_0(A_6065))) | ~l1_struct_0(A_6065) | v2_struct_0(A_6065))), inference(negUnitSimplification, [status(thm)], [c_37413, c_76, c_38179])).
% 26.55/13.08  tff(c_39773, plain, (l1_waybel_0(k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5'), '#skF_4') | v2_struct_0('#skF_4') | ~l1_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_30, c_39770])).
% 26.55/13.08  tff(c_39776, plain, (l1_waybel_0(k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5'), '#skF_4') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_37431, c_39773])).
% 26.55/13.08  tff(c_39777, plain, (l1_waybel_0(k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_82, c_39776])).
% 26.55/13.08  tff(c_39835, plain, (![A_6074, B_6075]: (k2_yellow19(A_6074, k3_yellow19(A_6074, k2_struct_0(A_6074), B_6075))=B_6075 | ~m1_subset_1(B_6075, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_6074))))) | ~v13_waybel_0(B_6075, k3_yellow_1(k2_struct_0(A_6074))) | ~v2_waybel_0(B_6075, k3_yellow_1(k2_struct_0(A_6074))) | ~v1_subset_1(B_6075, u1_struct_0(k3_yellow_1(k2_struct_0(A_6074)))) | v1_xboole_0(B_6075) | ~l1_struct_0(A_6074) | v2_struct_0(A_6074))), inference(cnfTransformation, [status(thm)], [f_199])).
% 26.55/13.08  tff(c_39840, plain, (k2_yellow19('#skF_4', k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5'))='#skF_5' | ~v13_waybel_0('#skF_5', k3_yellow_1(k2_struct_0('#skF_4'))) | ~v2_waybel_0('#skF_5', k3_yellow_1(k2_struct_0('#skF_4'))) | ~v1_subset_1('#skF_5', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4')))) | v1_xboole_0('#skF_5') | ~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_68, c_39835])).
% 26.55/13.08  tff(c_39847, plain, (k2_yellow19('#skF_4', k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5'))='#skF_5' | v1_xboole_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_37431, c_74, c_72, c_70, c_39840])).
% 26.55/13.08  tff(c_39848, plain, (k2_yellow19('#skF_4', k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5'))='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_82, c_76, c_39847])).
% 26.55/13.08  tff(c_60, plain, (![A_32, B_36, C_38]: (r3_waybel_9(A_32, B_36, C_38) | ~r1_waybel_7(A_32, k2_yellow19(A_32, B_36), C_38) | ~m1_subset_1(C_38, u1_struct_0(A_32)) | ~l1_waybel_0(B_36, A_32) | ~v7_waybel_0(B_36) | ~v4_orders_2(B_36) | v2_struct_0(B_36) | ~l1_pre_topc(A_32) | ~v2_pre_topc(A_32) | v2_struct_0(A_32))), inference(cnfTransformation, [status(thm)], [f_180])).
% 26.55/13.08  tff(c_39853, plain, (![C_38]: (r3_waybel_9('#skF_4', k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5'), C_38) | ~r1_waybel_7('#skF_4', '#skF_5', C_38) | ~m1_subset_1(C_38, u1_struct_0('#skF_4')) | ~l1_waybel_0(k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5'), '#skF_4') | ~v7_waybel_0(k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5')) | ~v4_orders_2(k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5')) | v2_struct_0(k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_39848, c_60])).
% 26.55/13.08  tff(c_39860, plain, (![C_38]: (r3_waybel_9('#skF_4', k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5'), C_38) | ~r1_waybel_7('#skF_4', '#skF_5', C_38) | ~m1_subset_1(C_38, u1_struct_0('#skF_4')) | v2_struct_0(k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5')) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_38920, c_39833, c_39777, c_39853])).
% 26.55/13.08  tff(c_39861, plain, (![C_38]: (r3_waybel_9('#skF_4', k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5'), C_38) | ~r1_waybel_7('#skF_4', '#skF_5', C_38) | ~m1_subset_1(C_38, u1_struct_0('#skF_4')) | v2_struct_0(k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_82, c_39860])).
% 26.55/13.08  tff(c_40264, plain, (v2_struct_0(k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5'))), inference(splitLeft, [status(thm)], [c_39861])).
% 26.55/13.08  tff(c_52, plain, (![A_26, B_27, C_28]: (~v2_struct_0(k3_yellow19(A_26, B_27, C_28)) | ~m1_subset_1(C_28, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_27)))) | ~v13_waybel_0(C_28, k3_yellow_1(B_27)) | ~v2_waybel_0(C_28, k3_yellow_1(B_27)) | v1_xboole_0(C_28) | ~m1_subset_1(B_27, k1_zfmisc_1(u1_struct_0(A_26))) | v1_xboole_0(B_27) | ~l1_struct_0(A_26) | v2_struct_0(A_26))), inference(cnfTransformation, [status(thm)], [f_128])).
% 26.55/13.08  tff(c_40266, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4'))))) | ~v13_waybel_0('#skF_5', k3_yellow_1(k2_struct_0('#skF_4'))) | ~v2_waybel_0('#skF_5', k3_yellow_1(k2_struct_0('#skF_4'))) | v1_xboole_0('#skF_5') | ~m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | v1_xboole_0(k2_struct_0('#skF_4')) | ~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_40264, c_52])).
% 26.55/13.08  tff(c_40269, plain, (v1_xboole_0('#skF_5') | ~m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | v1_xboole_0(k2_struct_0('#skF_4')) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_37431, c_72, c_70, c_68, c_40266])).
% 26.55/13.08  tff(c_40270, plain, (~m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_82, c_37413, c_76, c_40269])).
% 26.55/13.08  tff(c_40273, plain, (~l1_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_30, c_40270])).
% 26.55/13.08  tff(c_40277, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_37431, c_40273])).
% 26.55/13.08  tff(c_40998, plain, (![C_6123]: (r3_waybel_9('#skF_4', k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5'), C_6123) | ~r1_waybel_7('#skF_4', '#skF_5', C_6123) | ~m1_subset_1(C_6123, u1_struct_0('#skF_4')))), inference(splitRight, [status(thm)], [c_39861])).
% 26.55/13.08  tff(c_41004, plain, (~r1_waybel_7('#skF_4', '#skF_5', '#skF_6') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_40998, c_132])).
% 26.55/13.08  tff(c_41009, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_66, c_200, c_41004])).
% 26.55/13.08  tff(c_41010, plain, (~r1_waybel_7('#skF_4', '#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_84])).
% 26.55/13.08  tff(c_41011, plain, (r3_waybel_9('#skF_4', k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5'), '#skF_6')), inference(splitRight, [status(thm)], [c_84])).
% 26.55/13.08  tff(c_44387, plain, (![A_6291, B_6292]: (k2_yellow19(A_6291, k3_yellow19(A_6291, k2_struct_0(A_6291), B_6292))=B_6292 | ~m1_subset_1(B_6292, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_6291))))) | ~v13_waybel_0(B_6292, k3_yellow_1(k2_struct_0(A_6291))) | ~v2_waybel_0(B_6292, k3_yellow_1(k2_struct_0(A_6291))) | ~v1_subset_1(B_6292, u1_struct_0(k3_yellow_1(k2_struct_0(A_6291)))) | v1_xboole_0(B_6292) | ~l1_struct_0(A_6291) | v2_struct_0(A_6291))), inference(cnfTransformation, [status(thm)], [f_199])).
% 26.55/13.08  tff(c_44392, plain, (k2_yellow19('#skF_4', k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5'))='#skF_5' | ~v13_waybel_0('#skF_5', k3_yellow_1(k2_struct_0('#skF_4'))) | ~v2_waybel_0('#skF_5', k3_yellow_1(k2_struct_0('#skF_4'))) | ~v1_subset_1('#skF_5', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4')))) | v1_xboole_0('#skF_5') | ~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_68, c_44387])).
% 26.55/13.08  tff(c_44399, plain, (k2_yellow19('#skF_4', k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5'))='#skF_5' | v1_xboole_0('#skF_5') | ~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_70, c_44392])).
% 26.55/13.08  tff(c_44400, plain, (k2_yellow19('#skF_4', k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5'))='#skF_5' | ~l1_struct_0('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_82, c_76, c_44399])).
% 26.55/13.08  tff(c_44547, plain, (~l1_struct_0('#skF_4')), inference(splitLeft, [status(thm)], [c_44400])).
% 26.55/13.08  tff(c_44550, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_32, c_44547])).
% 26.55/13.08  tff(c_44554, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_78, c_44550])).
% 26.55/13.08  tff(c_44556, plain, (l1_struct_0('#skF_4')), inference(splitRight, [status(thm)], [c_44400])).
% 26.55/13.08  tff(c_43209, plain, (![A_6240, B_6241, C_6242]: (v4_orders_2(k3_yellow19(A_6240, B_6241, C_6242)) | ~m1_subset_1(C_6242, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_6241)))) | ~v13_waybel_0(C_6242, k3_yellow_1(B_6241)) | ~v2_waybel_0(C_6242, k3_yellow_1(B_6241)) | v1_xboole_0(C_6242) | ~m1_subset_1(B_6241, k1_zfmisc_1(u1_struct_0(A_6240))) | v1_xboole_0(B_6241) | ~l1_struct_0(A_6240) | v2_struct_0(A_6240))), inference(cnfTransformation, [status(thm)], [f_128])).
% 26.55/13.08  tff(c_43214, plain, (![A_6240]: (v4_orders_2(k3_yellow19(A_6240, k2_struct_0('#skF_4'), '#skF_5')) | ~v13_waybel_0('#skF_5', k3_yellow_1(k2_struct_0('#skF_4'))) | ~v2_waybel_0('#skF_5', k3_yellow_1(k2_struct_0('#skF_4'))) | v1_xboole_0('#skF_5') | ~m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(u1_struct_0(A_6240))) | v1_xboole_0(k2_struct_0('#skF_4')) | ~l1_struct_0(A_6240) | v2_struct_0(A_6240))), inference(resolution, [status(thm)], [c_68, c_43209])).
% 26.55/13.08  tff(c_43221, plain, (![A_6240]: (v4_orders_2(k3_yellow19(A_6240, k2_struct_0('#skF_4'), '#skF_5')) | v1_xboole_0('#skF_5') | ~m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(u1_struct_0(A_6240))) | v1_xboole_0(k2_struct_0('#skF_4')) | ~l1_struct_0(A_6240) | v2_struct_0(A_6240))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_43214])).
% 26.55/13.08  tff(c_43222, plain, (![A_6240]: (v4_orders_2(k3_yellow19(A_6240, k2_struct_0('#skF_4'), '#skF_5')) | ~m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(u1_struct_0(A_6240))) | v1_xboole_0(k2_struct_0('#skF_4')) | ~l1_struct_0(A_6240) | v2_struct_0(A_6240))), inference(negUnitSimplification, [status(thm)], [c_76, c_43221])).
% 26.55/13.08  tff(c_43896, plain, (v1_xboole_0(k2_struct_0('#skF_4'))), inference(splitLeft, [status(thm)], [c_43222])).
% 26.55/13.08  tff(c_41060, plain, (![A_6137, B_6138, C_6139]: (k7_subset_1(A_6137, B_6138, C_6139)=k4_xboole_0(B_6138, C_6139) | ~m1_subset_1(B_6138, k1_zfmisc_1(A_6137)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 26.55/13.08  tff(c_41067, plain, (![A_16, C_6139]: (k7_subset_1(u1_struct_0(A_16), k2_struct_0(A_16), C_6139)=k4_xboole_0(k2_struct_0(A_16), C_6139) | ~l1_struct_0(A_16))), inference(resolution, [status(thm)], [c_30, c_41060])).
% 26.55/13.08  tff(c_41424, plain, (![A_6185, B_6186]: (k7_subset_1(u1_struct_0(A_6185), k2_struct_0(A_6185), k7_subset_1(u1_struct_0(A_6185), k2_struct_0(A_6185), B_6186))=B_6186 | ~m1_subset_1(B_6186, k1_zfmisc_1(u1_struct_0(A_6185))) | ~l1_struct_0(A_6185))), inference(cnfTransformation, [status(thm)], [f_72])).
% 26.55/13.08  tff(c_81012, plain, (![A_11926, B_11927]: (k4_xboole_0(k2_struct_0(A_11926), k7_subset_1(u1_struct_0(A_11926), k2_struct_0(A_11926), B_11927))=B_11927 | ~m1_subset_1(B_11927, k1_zfmisc_1(u1_struct_0(A_11926))) | ~l1_struct_0(A_11926) | ~l1_struct_0(A_11926))), inference(superposition, [status(thm), theory('equality')], [c_41067, c_41424])).
% 26.55/13.08  tff(c_41148, plain, (![A_6161, B_6162, C_6163]: (r2_hidden('#skF_2'(A_6161, B_6162, C_6163), A_6161) | r2_hidden('#skF_3'(A_6161, B_6162, C_6163), C_6163) | k4_xboole_0(A_6161, B_6162)=C_6163)), inference(cnfTransformation, [status(thm)], [f_41])).
% 26.55/13.08  tff(c_41209, plain, (![A_6167, B_6168]: (r2_hidden('#skF_3'(A_6167, B_6168, A_6167), A_6167) | k4_xboole_0(A_6167, B_6168)=A_6167)), inference(resolution, [status(thm)], [c_41148, c_18])).
% 26.55/13.08  tff(c_41227, plain, (![A_6167, B_6168]: (~v1_xboole_0(A_6167) | k4_xboole_0(A_6167, B_6168)=A_6167)), inference(resolution, [status(thm)], [c_41209, c_2])).
% 26.55/13.08  tff(c_43911, plain, (![B_6168]: (k4_xboole_0(k2_struct_0('#skF_4'), B_6168)=k2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_43896, c_41227])).
% 26.55/13.08  tff(c_81249, plain, (![B_11927]: (k2_struct_0('#skF_4')=B_11927 | ~m1_subset_1(B_11927, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_struct_0('#skF_4') | ~l1_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_81012, c_43911])).
% 26.55/13.08  tff(c_81348, plain, (![B_11952]: (k2_struct_0('#skF_4')=B_11952 | ~m1_subset_1(B_11952, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_44556, c_44556, c_81249])).
% 26.55/13.08  tff(c_81361, plain, (u1_struct_0('#skF_4')=k2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_91, c_81348])).
% 26.55/13.08  tff(c_81382, plain, (~v1_xboole_0(k2_struct_0('#skF_4')) | ~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_81361, c_34])).
% 26.55/13.08  tff(c_81396, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_44556, c_43896, c_81382])).
% 26.55/13.08  tff(c_81398, plain, $false, inference(negUnitSimplification, [status(thm)], [c_82, c_81396])).
% 26.55/13.08  tff(c_81401, plain, (![A_12001]: (v4_orders_2(k3_yellow19(A_12001, k2_struct_0('#skF_4'), '#skF_5')) | ~m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(u1_struct_0(A_12001))) | ~l1_struct_0(A_12001) | v2_struct_0(A_12001))), inference(splitRight, [status(thm)], [c_43222])).
% 26.55/13.08  tff(c_81405, plain, (v4_orders_2(k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5')) | v2_struct_0('#skF_4') | ~l1_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_30, c_81401])).
% 26.55/13.08  tff(c_81408, plain, (v4_orders_2(k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5')) | ~l1_struct_0('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_82, c_81405])).
% 26.55/13.08  tff(c_81409, plain, (~l1_struct_0('#skF_4')), inference(splitLeft, [status(thm)], [c_81408])).
% 26.55/13.08  tff(c_81412, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_32, c_81409])).
% 26.55/13.08  tff(c_81416, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_78, c_81412])).
% 26.55/13.08  tff(c_81418, plain, (l1_struct_0('#skF_4')), inference(splitRight, [status(thm)], [c_81408])).
% 26.55/13.08  tff(c_81400, plain, (~v1_xboole_0(k2_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_43222])).
% 26.55/13.08  tff(c_81417, plain, (v4_orders_2(k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5'))), inference(splitRight, [status(thm)], [c_81408])).
% 26.55/13.08  tff(c_83012, plain, (![A_12038, B_12039, C_12040]: (v7_waybel_0(k3_yellow19(A_12038, B_12039, C_12040)) | ~m1_subset_1(C_12040, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_12039)))) | ~v13_waybel_0(C_12040, k3_yellow_1(B_12039)) | ~v2_waybel_0(C_12040, k3_yellow_1(B_12039)) | ~v1_subset_1(C_12040, u1_struct_0(k3_yellow_1(B_12039))) | v1_xboole_0(C_12040) | ~m1_subset_1(B_12039, k1_zfmisc_1(u1_struct_0(A_12038))) | v1_xboole_0(B_12039) | ~l1_struct_0(A_12038) | v2_struct_0(A_12038))), inference(cnfTransformation, [status(thm)], [f_156])).
% 26.55/13.08  tff(c_83017, plain, (![A_12038]: (v7_waybel_0(k3_yellow19(A_12038, k2_struct_0('#skF_4'), '#skF_5')) | ~v13_waybel_0('#skF_5', k3_yellow_1(k2_struct_0('#skF_4'))) | ~v2_waybel_0('#skF_5', k3_yellow_1(k2_struct_0('#skF_4'))) | ~v1_subset_1('#skF_5', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4')))) | v1_xboole_0('#skF_5') | ~m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(u1_struct_0(A_12038))) | v1_xboole_0(k2_struct_0('#skF_4')) | ~l1_struct_0(A_12038) | v2_struct_0(A_12038))), inference(resolution, [status(thm)], [c_68, c_83012])).
% 26.55/13.08  tff(c_83024, plain, (![A_12038]: (v7_waybel_0(k3_yellow19(A_12038, k2_struct_0('#skF_4'), '#skF_5')) | v1_xboole_0('#skF_5') | ~m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(u1_struct_0(A_12038))) | v1_xboole_0(k2_struct_0('#skF_4')) | ~l1_struct_0(A_12038) | v2_struct_0(A_12038))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_70, c_83017])).
% 26.55/13.08  tff(c_83609, plain, (![A_12045]: (v7_waybel_0(k3_yellow19(A_12045, k2_struct_0('#skF_4'), '#skF_5')) | ~m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(u1_struct_0(A_12045))) | ~l1_struct_0(A_12045) | v2_struct_0(A_12045))), inference(negUnitSimplification, [status(thm)], [c_81400, c_76, c_83024])).
% 26.55/13.08  tff(c_83613, plain, (v7_waybel_0(k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5')) | v2_struct_0('#skF_4') | ~l1_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_30, c_83609])).
% 26.55/13.08  tff(c_83616, plain, (v7_waybel_0(k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5')) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_81418, c_83613])).
% 26.55/13.08  tff(c_83617, plain, (v7_waybel_0(k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_82, c_83616])).
% 26.55/13.08  tff(c_82275, plain, (![A_12022, B_12023, C_12024]: (l1_waybel_0(k3_yellow19(A_12022, B_12023, C_12024), A_12022) | ~m1_subset_1(C_12024, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_12023)))) | ~v13_waybel_0(C_12024, k3_yellow_1(B_12023)) | ~v2_waybel_0(C_12024, k3_yellow_1(B_12023)) | v1_xboole_0(C_12024) | ~m1_subset_1(B_12023, k1_zfmisc_1(u1_struct_0(A_12022))) | v1_xboole_0(B_12023) | ~l1_struct_0(A_12022) | v2_struct_0(A_12022))), inference(cnfTransformation, [status(thm)], [f_100])).
% 26.55/13.08  tff(c_82280, plain, (![A_12022]: (l1_waybel_0(k3_yellow19(A_12022, k2_struct_0('#skF_4'), '#skF_5'), A_12022) | ~v13_waybel_0('#skF_5', k3_yellow_1(k2_struct_0('#skF_4'))) | ~v2_waybel_0('#skF_5', k3_yellow_1(k2_struct_0('#skF_4'))) | v1_xboole_0('#skF_5') | ~m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(u1_struct_0(A_12022))) | v1_xboole_0(k2_struct_0('#skF_4')) | ~l1_struct_0(A_12022) | v2_struct_0(A_12022))), inference(resolution, [status(thm)], [c_68, c_82275])).
% 26.55/13.08  tff(c_82287, plain, (![A_12022]: (l1_waybel_0(k3_yellow19(A_12022, k2_struct_0('#skF_4'), '#skF_5'), A_12022) | v1_xboole_0('#skF_5') | ~m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(u1_struct_0(A_12022))) | v1_xboole_0(k2_struct_0('#skF_4')) | ~l1_struct_0(A_12022) | v2_struct_0(A_12022))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_82280])).
% 26.55/13.08  tff(c_82487, plain, (![A_12029]: (l1_waybel_0(k3_yellow19(A_12029, k2_struct_0('#skF_4'), '#skF_5'), A_12029) | ~m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(u1_struct_0(A_12029))) | ~l1_struct_0(A_12029) | v2_struct_0(A_12029))), inference(negUnitSimplification, [status(thm)], [c_81400, c_76, c_82287])).
% 26.55/13.08  tff(c_82490, plain, (l1_waybel_0(k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5'), '#skF_4') | v2_struct_0('#skF_4') | ~l1_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_30, c_82487])).
% 26.55/13.08  tff(c_82493, plain, (l1_waybel_0(k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5'), '#skF_4') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_81418, c_82490])).
% 26.55/13.08  tff(c_82494, plain, (l1_waybel_0(k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_82, c_82493])).
% 26.55/13.08  tff(c_83736, plain, (![A_12049, B_12050]: (k2_yellow19(A_12049, k3_yellow19(A_12049, k2_struct_0(A_12049), B_12050))=B_12050 | ~m1_subset_1(B_12050, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_12049))))) | ~v13_waybel_0(B_12050, k3_yellow_1(k2_struct_0(A_12049))) | ~v2_waybel_0(B_12050, k3_yellow_1(k2_struct_0(A_12049))) | ~v1_subset_1(B_12050, u1_struct_0(k3_yellow_1(k2_struct_0(A_12049)))) | v1_xboole_0(B_12050) | ~l1_struct_0(A_12049) | v2_struct_0(A_12049))), inference(cnfTransformation, [status(thm)], [f_199])).
% 26.55/13.08  tff(c_83741, plain, (k2_yellow19('#skF_4', k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5'))='#skF_5' | ~v13_waybel_0('#skF_5', k3_yellow_1(k2_struct_0('#skF_4'))) | ~v2_waybel_0('#skF_5', k3_yellow_1(k2_struct_0('#skF_4'))) | ~v1_subset_1('#skF_5', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4')))) | v1_xboole_0('#skF_5') | ~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_68, c_83736])).
% 26.55/13.08  tff(c_83748, plain, (k2_yellow19('#skF_4', k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5'))='#skF_5' | v1_xboole_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_81418, c_74, c_72, c_70, c_83741])).
% 26.55/13.08  tff(c_83749, plain, (k2_yellow19('#skF_4', k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5'))='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_82, c_76, c_83748])).
% 26.55/13.08  tff(c_83757, plain, (![C_38]: (r3_waybel_9('#skF_4', k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5'), C_38) | ~r1_waybel_7('#skF_4', '#skF_5', C_38) | ~m1_subset_1(C_38, u1_struct_0('#skF_4')) | ~l1_waybel_0(k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5'), '#skF_4') | ~v7_waybel_0(k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5')) | ~v4_orders_2(k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5')) | v2_struct_0(k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_83749, c_60])).
% 26.55/13.08  tff(c_83764, plain, (![C_38]: (r3_waybel_9('#skF_4', k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5'), C_38) | ~r1_waybel_7('#skF_4', '#skF_5', C_38) | ~m1_subset_1(C_38, u1_struct_0('#skF_4')) | v2_struct_0(k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5')) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_81417, c_83617, c_82494, c_83757])).
% 26.55/13.08  tff(c_83765, plain, (![C_38]: (r3_waybel_9('#skF_4', k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5'), C_38) | ~r1_waybel_7('#skF_4', '#skF_5', C_38) | ~m1_subset_1(C_38, u1_struct_0('#skF_4')) | v2_struct_0(k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_82, c_83764])).
% 26.55/13.08  tff(c_84054, plain, (v2_struct_0(k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5'))), inference(splitLeft, [status(thm)], [c_83765])).
% 26.55/13.08  tff(c_84056, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4'))))) | ~v13_waybel_0('#skF_5', k3_yellow_1(k2_struct_0('#skF_4'))) | ~v2_waybel_0('#skF_5', k3_yellow_1(k2_struct_0('#skF_4'))) | v1_xboole_0('#skF_5') | ~m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | v1_xboole_0(k2_struct_0('#skF_4')) | ~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_84054, c_52])).
% 26.55/13.08  tff(c_84059, plain, (v1_xboole_0('#skF_5') | ~m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | v1_xboole_0(k2_struct_0('#skF_4')) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_81418, c_72, c_70, c_68, c_84056])).
% 26.55/13.08  tff(c_84060, plain, (~m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_82, c_81400, c_76, c_84059])).
% 26.55/13.08  tff(c_84063, plain, (~l1_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_30, c_84060])).
% 26.55/13.08  tff(c_84067, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_81418, c_84063])).
% 26.55/13.08  tff(c_84069, plain, (~v2_struct_0(k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5'))), inference(splitRight, [status(thm)], [c_83765])).
% 26.55/13.08  tff(c_62, plain, (![A_32, B_36, C_38]: (r1_waybel_7(A_32, k2_yellow19(A_32, B_36), C_38) | ~r3_waybel_9(A_32, B_36, C_38) | ~m1_subset_1(C_38, u1_struct_0(A_32)) | ~l1_waybel_0(B_36, A_32) | ~v7_waybel_0(B_36) | ~v4_orders_2(B_36) | v2_struct_0(B_36) | ~l1_pre_topc(A_32) | ~v2_pre_topc(A_32) | v2_struct_0(A_32))), inference(cnfTransformation, [status(thm)], [f_180])).
% 26.55/13.08  tff(c_83754, plain, (![C_38]: (r1_waybel_7('#skF_4', '#skF_5', C_38) | ~r3_waybel_9('#skF_4', k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5'), C_38) | ~m1_subset_1(C_38, u1_struct_0('#skF_4')) | ~l1_waybel_0(k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5'), '#skF_4') | ~v7_waybel_0(k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5')) | ~v4_orders_2(k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5')) | v2_struct_0(k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_83749, c_62])).
% 26.55/13.08  tff(c_83761, plain, (![C_38]: (r1_waybel_7('#skF_4', '#skF_5', C_38) | ~r3_waybel_9('#skF_4', k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5'), C_38) | ~m1_subset_1(C_38, u1_struct_0('#skF_4')) | v2_struct_0(k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5')) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_81417, c_83617, c_82494, c_83754])).
% 26.55/13.08  tff(c_83762, plain, (![C_38]: (r1_waybel_7('#skF_4', '#skF_5', C_38) | ~r3_waybel_9('#skF_4', k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5'), C_38) | ~m1_subset_1(C_38, u1_struct_0('#skF_4')) | v2_struct_0(k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_82, c_83761])).
% 26.55/13.08  tff(c_84225, plain, (![C_12068]: (r1_waybel_7('#skF_4', '#skF_5', C_12068) | ~r3_waybel_9('#skF_4', k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5'), C_12068) | ~m1_subset_1(C_12068, u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_84069, c_83762])).
% 26.55/13.08  tff(c_84228, plain, (r1_waybel_7('#skF_4', '#skF_5', '#skF_6') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_41011, c_84225])).
% 26.55/13.08  tff(c_84231, plain, (r1_waybel_7('#skF_4', '#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_84228])).
% 26.55/13.08  tff(c_84233, plain, $false, inference(negUnitSimplification, [status(thm)], [c_41010, c_84231])).
% 26.55/13.08  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 26.55/13.08  
% 26.55/13.08  Inference rules
% 26.55/13.08  ----------------------
% 26.55/13.08  #Ref     : 0
% 26.55/13.08  #Sup     : 20828
% 26.55/13.08  #Fact    : 0
% 26.55/13.08  #Define  : 0
% 26.55/13.08  #Split   : 30
% 26.55/13.08  #Chain   : 0
% 26.55/13.08  #Close   : 0
% 26.55/13.08  
% 26.55/13.08  Ordering : KBO
% 26.55/13.08  
% 26.55/13.08  Simplification rules
% 26.55/13.08  ----------------------
% 26.55/13.08  #Subsume      : 10939
% 26.55/13.08  #Demod        : 8167
% 26.55/13.08  #Tautology    : 3680
% 26.55/13.08  #SimpNegUnit  : 82
% 26.55/13.08  #BackRed      : 47
% 26.55/13.08  
% 26.55/13.08  #Partial instantiations: 7480
% 26.55/13.08  #Strategies tried      : 1
% 26.55/13.08  
% 26.55/13.08  Timing (in seconds)
% 26.55/13.08  ----------------------
% 26.55/13.08  Preprocessing        : 0.59
% 26.55/13.08  Parsing              : 0.30
% 26.55/13.08  CNF conversion       : 0.05
% 26.55/13.08  Main loop            : 11.53
% 26.55/13.08  Inferencing          : 2.61
% 26.55/13.08  Reduction            : 3.05
% 26.55/13.08  Demodulation         : 2.29
% 26.55/13.08  BG Simplification    : 0.29
% 26.55/13.08  Subsumption          : 4.95
% 26.55/13.08  Abstraction          : 0.48
% 26.55/13.08  MUC search           : 0.00
% 26.55/13.08  Cooper               : 0.00
% 26.55/13.08  Total                : 12.19
% 26.55/13.08  Index Insertion      : 0.00
% 26.55/13.08  Index Deletion       : 0.00
% 26.55/13.08  Index Matching       : 0.00
% 26.55/13.08  BG Taut test         : 0.00
%------------------------------------------------------------------------------
