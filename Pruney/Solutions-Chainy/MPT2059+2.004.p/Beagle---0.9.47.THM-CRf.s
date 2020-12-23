%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:36 EST 2020

% Result     : Theorem 3.45s
% Output     : CNFRefutation 3.75s
% Verified   : 
% Statistics : Number of formulae       :  192 (2629 expanded)
%              Number of leaves         :   48 ( 945 expanded)
%              Depth                    :   23
%              Number of atoms          :  586 (10754 expanded)
%              Number of equality atoms :   15 ( 480 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_waybel_7 > v6_waybel_0 > v4_pre_topc > v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_hidden > m1_subset_1 > l1_waybel_0 > v7_waybel_0 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k3_yellow19 > k2_yellow19 > k10_yellow_6 > #nlpp > u1_struct_0 > k3_yellow_1 > k3_lattice3 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_lattice3 > #skF_2 > #skF_1 > #skF_5 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

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

tff(k10_yellow_6,type,(
    k10_yellow_6: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(v7_waybel_0,type,(
    v7_waybel_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

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

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_219,negated_conjecture,(
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

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_50,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_46,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_65,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ? [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
          & ~ v1_xboole_0(B)
          & v4_pre_topc(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc7_pre_topc)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_33,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_35,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_121,axiom,(
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

tff(f_93,axiom,(
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

tff(f_192,axiom,(
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

tff(f_173,axiom,(
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

tff(f_149,axiom,(
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

tff(c_66,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_64,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_62,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_14,plain,(
    ! [A_11] :
      ( l1_struct_0(A_11)
      | ~ l1_pre_topc(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_102,plain,(
    ! [A_45] :
      ( u1_struct_0(A_45) = k2_struct_0(A_45)
      | ~ l1_struct_0(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_107,plain,(
    ! [A_46] :
      ( u1_struct_0(A_46) = k2_struct_0(A_46)
      | ~ l1_pre_topc(A_46) ) ),
    inference(resolution,[status(thm)],[c_14,c_102])).

tff(c_111,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_107])).

tff(c_50,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_112,plain,(
    m1_subset_1('#skF_5',k2_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_50])).

tff(c_74,plain,
    ( r2_hidden('#skF_5',k10_yellow_6('#skF_3',k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4')))
    | r2_waybel_7('#skF_3','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_117,plain,(
    r2_waybel_7('#skF_3','#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_74])).

tff(c_128,plain,(
    ! [A_52] :
      ( m1_subset_1('#skF_2'(A_52),k1_zfmisc_1(u1_struct_0(A_52)))
      | ~ l1_pre_topc(A_52)
      | ~ v2_pre_topc(A_52)
      | v2_struct_0(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_133,plain,
    ( m1_subset_1('#skF_2'('#skF_3'),k1_zfmisc_1(k2_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_111,c_128])).

tff(c_136,plain,
    ( m1_subset_1('#skF_2'('#skF_3'),k1_zfmisc_1(k2_struct_0('#skF_3')))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_133])).

tff(c_137,plain,(
    m1_subset_1('#skF_2'('#skF_3'),k1_zfmisc_1(k2_struct_0('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_136])).

tff(c_10,plain,(
    ! [C_9,B_8,A_7] :
      ( ~ v1_xboole_0(C_9)
      | ~ m1_subset_1(B_8,k1_zfmisc_1(C_9))
      | ~ r2_hidden(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_140,plain,(
    ! [A_7] :
      ( ~ v1_xboole_0(k2_struct_0('#skF_3'))
      | ~ r2_hidden(A_7,'#skF_2'('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_137,c_10])).

tff(c_141,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_140])).

tff(c_60,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_6,plain,(
    ! [A_5] : k2_subset_1(A_5) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_8,plain,(
    ! [A_6] : m1_subset_1(k2_subset_1(A_6),k1_zfmisc_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_75,plain,(
    ! [A_6] : m1_subset_1(A_6,k1_zfmisc_1(A_6)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_8])).

tff(c_56,plain,(
    v2_waybel_0('#skF_4',k3_yellow_1(k2_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_54,plain,(
    v13_waybel_0('#skF_4',k3_yellow_1(k2_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_52,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3'))))) ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_163,plain,(
    ! [A_62,B_63,C_64] :
      ( v3_orders_2(k3_yellow19(A_62,B_63,C_64))
      | ~ m1_subset_1(C_64,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_63))))
      | ~ v13_waybel_0(C_64,k3_yellow_1(B_63))
      | ~ v2_waybel_0(C_64,k3_yellow_1(B_63))
      | v1_xboole_0(C_64)
      | ~ m1_subset_1(B_63,k1_zfmisc_1(u1_struct_0(A_62)))
      | v1_xboole_0(B_63)
      | ~ l1_struct_0(A_62)
      | v2_struct_0(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_168,plain,(
    ! [A_62] :
      ( v3_orders_2(k3_yellow19(A_62,k2_struct_0('#skF_3'),'#skF_4'))
      | ~ v13_waybel_0('#skF_4',k3_yellow_1(k2_struct_0('#skF_3')))
      | ~ v2_waybel_0('#skF_4',k3_yellow_1(k2_struct_0('#skF_3')))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(u1_struct_0(A_62)))
      | v1_xboole_0(k2_struct_0('#skF_3'))
      | ~ l1_struct_0(A_62)
      | v2_struct_0(A_62) ) ),
    inference(resolution,[status(thm)],[c_52,c_163])).

tff(c_175,plain,(
    ! [A_62] :
      ( v3_orders_2(k3_yellow19(A_62,k2_struct_0('#skF_3'),'#skF_4'))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(u1_struct_0(A_62)))
      | v1_xboole_0(k2_struct_0('#skF_3'))
      | ~ l1_struct_0(A_62)
      | v2_struct_0(A_62) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_168])).

tff(c_178,plain,(
    ! [A_65] :
      ( v3_orders_2(k3_yellow19(A_65,k2_struct_0('#skF_3'),'#skF_4'))
      | ~ m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(u1_struct_0(A_65)))
      | ~ l1_struct_0(A_65)
      | v2_struct_0(A_65) ) ),
    inference(negUnitSimplification,[status(thm)],[c_141,c_60,c_175])).

tff(c_181,plain,
    ( v3_orders_2(k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4'))
    | ~ m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(k2_struct_0('#skF_3')))
    | ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_111,c_178])).

tff(c_183,plain,
    ( v3_orders_2(k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4'))
    | ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_181])).

tff(c_184,plain,
    ( v3_orders_2(k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4'))
    | ~ l1_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_183])).

tff(c_185,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_184])).

tff(c_188,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_14,c_185])).

tff(c_192,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_188])).

tff(c_194,plain,(
    l1_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_184])).

tff(c_200,plain,(
    ! [A_66,B_67,C_68] :
      ( v4_orders_2(k3_yellow19(A_66,B_67,C_68))
      | ~ m1_subset_1(C_68,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_67))))
      | ~ v13_waybel_0(C_68,k3_yellow_1(B_67))
      | ~ v2_waybel_0(C_68,k3_yellow_1(B_67))
      | v1_xboole_0(C_68)
      | ~ m1_subset_1(B_67,k1_zfmisc_1(u1_struct_0(A_66)))
      | v1_xboole_0(B_67)
      | ~ l1_struct_0(A_66)
      | v2_struct_0(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_205,plain,(
    ! [A_66] :
      ( v4_orders_2(k3_yellow19(A_66,k2_struct_0('#skF_3'),'#skF_4'))
      | ~ v13_waybel_0('#skF_4',k3_yellow_1(k2_struct_0('#skF_3')))
      | ~ v2_waybel_0('#skF_4',k3_yellow_1(k2_struct_0('#skF_3')))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(u1_struct_0(A_66)))
      | v1_xboole_0(k2_struct_0('#skF_3'))
      | ~ l1_struct_0(A_66)
      | v2_struct_0(A_66) ) ),
    inference(resolution,[status(thm)],[c_52,c_200])).

tff(c_212,plain,(
    ! [A_66] :
      ( v4_orders_2(k3_yellow19(A_66,k2_struct_0('#skF_3'),'#skF_4'))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(u1_struct_0(A_66)))
      | v1_xboole_0(k2_struct_0('#skF_3'))
      | ~ l1_struct_0(A_66)
      | v2_struct_0(A_66) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_205])).

tff(c_215,plain,(
    ! [A_69] :
      ( v4_orders_2(k3_yellow19(A_69,k2_struct_0('#skF_3'),'#skF_4'))
      | ~ m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(u1_struct_0(A_69)))
      | ~ l1_struct_0(A_69)
      | v2_struct_0(A_69) ) ),
    inference(negUnitSimplification,[status(thm)],[c_141,c_60,c_212])).

tff(c_218,plain,
    ( v4_orders_2(k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4'))
    | ~ m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(k2_struct_0('#skF_3')))
    | ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_111,c_215])).

tff(c_220,plain,
    ( v4_orders_2(k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_194,c_75,c_218])).

tff(c_221,plain,(
    v4_orders_2(k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_220])).

tff(c_244,plain,(
    ! [A_77,B_78,C_79] :
      ( l1_waybel_0(k3_yellow19(A_77,B_78,C_79),A_77)
      | ~ m1_subset_1(C_79,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_78))))
      | ~ v13_waybel_0(C_79,k3_yellow_1(B_78))
      | ~ v2_waybel_0(C_79,k3_yellow_1(B_78))
      | v1_xboole_0(C_79)
      | ~ m1_subset_1(B_78,k1_zfmisc_1(u1_struct_0(A_77)))
      | v1_xboole_0(B_78)
      | ~ l1_struct_0(A_77)
      | v2_struct_0(A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_249,plain,(
    ! [A_77] :
      ( l1_waybel_0(k3_yellow19(A_77,k2_struct_0('#skF_3'),'#skF_4'),A_77)
      | ~ v13_waybel_0('#skF_4',k3_yellow_1(k2_struct_0('#skF_3')))
      | ~ v2_waybel_0('#skF_4',k3_yellow_1(k2_struct_0('#skF_3')))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(u1_struct_0(A_77)))
      | v1_xboole_0(k2_struct_0('#skF_3'))
      | ~ l1_struct_0(A_77)
      | v2_struct_0(A_77) ) ),
    inference(resolution,[status(thm)],[c_52,c_244])).

tff(c_256,plain,(
    ! [A_77] :
      ( l1_waybel_0(k3_yellow19(A_77,k2_struct_0('#skF_3'),'#skF_4'),A_77)
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(u1_struct_0(A_77)))
      | v1_xboole_0(k2_struct_0('#skF_3'))
      | ~ l1_struct_0(A_77)
      | v2_struct_0(A_77) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_249])).

tff(c_259,plain,(
    ! [A_80] :
      ( l1_waybel_0(k3_yellow19(A_80,k2_struct_0('#skF_3'),'#skF_4'),A_80)
      | ~ m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(u1_struct_0(A_80)))
      | ~ l1_struct_0(A_80)
      | v2_struct_0(A_80) ) ),
    inference(negUnitSimplification,[status(thm)],[c_141,c_60,c_256])).

tff(c_261,plain,
    ( l1_waybel_0(k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4'),'#skF_3')
    | ~ m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(k2_struct_0('#skF_3')))
    | ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_111,c_259])).

tff(c_263,plain,
    ( l1_waybel_0(k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4'),'#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_194,c_75,c_261])).

tff(c_264,plain,(
    l1_waybel_0(k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_263])).

tff(c_58,plain,(
    v1_subset_1('#skF_4',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_269,plain,(
    ! [A_89,B_90] :
      ( k2_yellow19(A_89,k3_yellow19(A_89,k2_struct_0(A_89),B_90)) = B_90
      | ~ m1_subset_1(B_90,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_89)))))
      | ~ v13_waybel_0(B_90,k3_yellow_1(k2_struct_0(A_89)))
      | ~ v2_waybel_0(B_90,k3_yellow_1(k2_struct_0(A_89)))
      | ~ v1_subset_1(B_90,u1_struct_0(k3_yellow_1(k2_struct_0(A_89))))
      | v1_xboole_0(B_90)
      | ~ l1_struct_0(A_89)
      | v2_struct_0(A_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_274,plain,
    ( k2_yellow19('#skF_3',k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4')) = '#skF_4'
    | ~ v13_waybel_0('#skF_4',k3_yellow_1(k2_struct_0('#skF_3')))
    | ~ v2_waybel_0('#skF_4',k3_yellow_1(k2_struct_0('#skF_3')))
    | ~ v1_subset_1('#skF_4',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3'))))
    | v1_xboole_0('#skF_4')
    | ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_269])).

tff(c_281,plain,
    ( k2_yellow19('#skF_3',k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4')) = '#skF_4'
    | v1_xboole_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_194,c_58,c_56,c_54,c_274])).

tff(c_282,plain,(
    k2_yellow19('#skF_3',k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4')) = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_60,c_281])).

tff(c_44,plain,(
    ! [C_30,A_24,B_28] :
      ( r2_hidden(C_30,k10_yellow_6(A_24,B_28))
      | ~ r2_waybel_7(A_24,k2_yellow19(A_24,B_28),C_30)
      | ~ m1_subset_1(C_30,u1_struct_0(A_24))
      | ~ l1_waybel_0(B_28,A_24)
      | ~ v7_waybel_0(B_28)
      | ~ v4_orders_2(B_28)
      | v2_struct_0(B_28)
      | ~ l1_pre_topc(A_24)
      | ~ v2_pre_topc(A_24)
      | v2_struct_0(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_287,plain,(
    ! [C_30] :
      ( r2_hidden(C_30,k10_yellow_6('#skF_3',k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4')))
      | ~ r2_waybel_7('#skF_3','#skF_4',C_30)
      | ~ m1_subset_1(C_30,u1_struct_0('#skF_3'))
      | ~ l1_waybel_0(k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4'),'#skF_3')
      | ~ v7_waybel_0(k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4'))
      | ~ v4_orders_2(k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4'))
      | v2_struct_0(k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_282,c_44])).

tff(c_294,plain,(
    ! [C_30] :
      ( r2_hidden(C_30,k10_yellow_6('#skF_3',k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4')))
      | ~ r2_waybel_7('#skF_3','#skF_4',C_30)
      | ~ m1_subset_1(C_30,k2_struct_0('#skF_3'))
      | ~ v7_waybel_0(k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4'))
      | v2_struct_0(k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_221,c_264,c_111,c_287])).

tff(c_295,plain,(
    ! [C_30] :
      ( r2_hidden(C_30,k10_yellow_6('#skF_3',k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4')))
      | ~ r2_waybel_7('#skF_3','#skF_4',C_30)
      | ~ m1_subset_1(C_30,k2_struct_0('#skF_3'))
      | ~ v7_waybel_0(k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4'))
      | v2_struct_0(k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_294])).

tff(c_300,plain,(
    ~ v7_waybel_0(k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_295])).

tff(c_301,plain,(
    ! [A_91,B_92,C_93] :
      ( v7_waybel_0(k3_yellow19(A_91,B_92,C_93))
      | ~ m1_subset_1(C_93,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_92))))
      | ~ v13_waybel_0(C_93,k3_yellow_1(B_92))
      | ~ v2_waybel_0(C_93,k3_yellow_1(B_92))
      | ~ v1_subset_1(C_93,u1_struct_0(k3_yellow_1(B_92)))
      | v1_xboole_0(C_93)
      | ~ m1_subset_1(B_92,k1_zfmisc_1(u1_struct_0(A_91)))
      | v1_xboole_0(B_92)
      | ~ l1_struct_0(A_91)
      | v2_struct_0(A_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_306,plain,(
    ! [A_91] :
      ( v7_waybel_0(k3_yellow19(A_91,k2_struct_0('#skF_3'),'#skF_4'))
      | ~ v13_waybel_0('#skF_4',k3_yellow_1(k2_struct_0('#skF_3')))
      | ~ v2_waybel_0('#skF_4',k3_yellow_1(k2_struct_0('#skF_3')))
      | ~ v1_subset_1('#skF_4',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3'))))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(u1_struct_0(A_91)))
      | v1_xboole_0(k2_struct_0('#skF_3'))
      | ~ l1_struct_0(A_91)
      | v2_struct_0(A_91) ) ),
    inference(resolution,[status(thm)],[c_52,c_301])).

tff(c_313,plain,(
    ! [A_91] :
      ( v7_waybel_0(k3_yellow19(A_91,k2_struct_0('#skF_3'),'#skF_4'))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(u1_struct_0(A_91)))
      | v1_xboole_0(k2_struct_0('#skF_3'))
      | ~ l1_struct_0(A_91)
      | v2_struct_0(A_91) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_306])).

tff(c_316,plain,(
    ! [A_94] :
      ( v7_waybel_0(k3_yellow19(A_94,k2_struct_0('#skF_3'),'#skF_4'))
      | ~ m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(u1_struct_0(A_94)))
      | ~ l1_struct_0(A_94)
      | v2_struct_0(A_94) ) ),
    inference(negUnitSimplification,[status(thm)],[c_141,c_60,c_313])).

tff(c_319,plain,
    ( v7_waybel_0(k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4'))
    | ~ m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(k2_struct_0('#skF_3')))
    | ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_111,c_316])).

tff(c_321,plain,
    ( v7_waybel_0(k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_194,c_75,c_319])).

tff(c_323,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_300,c_321])).

tff(c_324,plain,(
    ! [C_30] :
      ( v2_struct_0(k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4'))
      | r2_hidden(C_30,k10_yellow_6('#skF_3',k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4')))
      | ~ r2_waybel_7('#skF_3','#skF_4',C_30)
      | ~ m1_subset_1(C_30,k2_struct_0('#skF_3')) ) ),
    inference(splitRight,[status(thm)],[c_295])).

tff(c_326,plain,(
    v2_struct_0(k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_324])).

tff(c_36,plain,(
    ! [A_18,B_19,C_20] :
      ( ~ v2_struct_0(k3_yellow19(A_18,B_19,C_20))
      | ~ m1_subset_1(C_20,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_19))))
      | ~ v13_waybel_0(C_20,k3_yellow_1(B_19))
      | ~ v2_waybel_0(C_20,k3_yellow_1(B_19))
      | v1_xboole_0(C_20)
      | ~ m1_subset_1(B_19,k1_zfmisc_1(u1_struct_0(A_18)))
      | v1_xboole_0(B_19)
      | ~ l1_struct_0(A_18)
      | v2_struct_0(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_328,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3')))))
    | ~ v13_waybel_0('#skF_4',k3_yellow_1(k2_struct_0('#skF_3')))
    | ~ v2_waybel_0('#skF_4',k3_yellow_1(k2_struct_0('#skF_3')))
    | v1_xboole_0('#skF_4')
    | ~ m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | v1_xboole_0(k2_struct_0('#skF_3'))
    | ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_326,c_36])).

tff(c_331,plain,
    ( v1_xboole_0('#skF_4')
    | v1_xboole_0(k2_struct_0('#skF_3'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_194,c_75,c_111,c_56,c_54,c_52,c_328])).

tff(c_333,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_141,c_60,c_331])).

tff(c_358,plain,(
    ! [C_99] :
      ( r2_hidden(C_99,k10_yellow_6('#skF_3',k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4')))
      | ~ r2_waybel_7('#skF_3','#skF_4',C_99)
      | ~ m1_subset_1(C_99,k2_struct_0('#skF_3')) ) ),
    inference(splitRight,[status(thm)],[c_324])).

tff(c_68,plain,
    ( ~ r2_waybel_7('#skF_3','#skF_4','#skF_5')
    | ~ r2_hidden('#skF_5',k10_yellow_6('#skF_3',k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_143,plain,(
    ~ r2_hidden('#skF_5',k10_yellow_6('#skF_3',k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_68])).

tff(c_361,plain,
    ( ~ r2_waybel_7('#skF_3','#skF_4','#skF_5')
    | ~ m1_subset_1('#skF_5',k2_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_358,c_143])).

tff(c_368,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_117,c_361])).

tff(c_373,plain,(
    ! [A_100] : ~ r2_hidden(A_100,'#skF_2'('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_140])).

tff(c_378,plain,(
    v1_xboole_0('#skF_2'('#skF_3')) ),
    inference(resolution,[status(thm)],[c_4,c_373])).

tff(c_18,plain,(
    ! [A_12] :
      ( ~ v1_xboole_0('#skF_2'(A_12))
      | ~ l1_pre_topc(A_12)
      | ~ v2_pre_topc(A_12)
      | v2_struct_0(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_381,plain,
    ( ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_378,c_18])).

tff(c_384,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_381])).

tff(c_386,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_384])).

tff(c_388,plain,(
    ~ r2_waybel_7('#skF_3','#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_387,plain,(
    r2_hidden('#skF_5',k10_yellow_6('#skF_3',k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_405,plain,(
    ! [A_106] :
      ( m1_subset_1('#skF_2'(A_106),k1_zfmisc_1(u1_struct_0(A_106)))
      | ~ l1_pre_topc(A_106)
      | ~ v2_pre_topc(A_106)
      | v2_struct_0(A_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_410,plain,
    ( m1_subset_1('#skF_2'('#skF_3'),k1_zfmisc_1(k2_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_111,c_405])).

tff(c_413,plain,
    ( m1_subset_1('#skF_2'('#skF_3'),k1_zfmisc_1(k2_struct_0('#skF_3')))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_410])).

tff(c_414,plain,(
    m1_subset_1('#skF_2'('#skF_3'),k1_zfmisc_1(k2_struct_0('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_413])).

tff(c_417,plain,(
    ! [A_7] :
      ( ~ v1_xboole_0(k2_struct_0('#skF_3'))
      | ~ r2_hidden(A_7,'#skF_2'('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_414,c_10])).

tff(c_418,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_417])).

tff(c_438,plain,(
    ! [A_116,B_117,C_118] :
      ( v4_orders_2(k3_yellow19(A_116,B_117,C_118))
      | ~ m1_subset_1(C_118,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_117))))
      | ~ v13_waybel_0(C_118,k3_yellow_1(B_117))
      | ~ v2_waybel_0(C_118,k3_yellow_1(B_117))
      | v1_xboole_0(C_118)
      | ~ m1_subset_1(B_117,k1_zfmisc_1(u1_struct_0(A_116)))
      | v1_xboole_0(B_117)
      | ~ l1_struct_0(A_116)
      | v2_struct_0(A_116) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_443,plain,(
    ! [A_116] :
      ( v4_orders_2(k3_yellow19(A_116,k2_struct_0('#skF_3'),'#skF_4'))
      | ~ v13_waybel_0('#skF_4',k3_yellow_1(k2_struct_0('#skF_3')))
      | ~ v2_waybel_0('#skF_4',k3_yellow_1(k2_struct_0('#skF_3')))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(u1_struct_0(A_116)))
      | v1_xboole_0(k2_struct_0('#skF_3'))
      | ~ l1_struct_0(A_116)
      | v2_struct_0(A_116) ) ),
    inference(resolution,[status(thm)],[c_52,c_438])).

tff(c_450,plain,(
    ! [A_116] :
      ( v4_orders_2(k3_yellow19(A_116,k2_struct_0('#skF_3'),'#skF_4'))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(u1_struct_0(A_116)))
      | v1_xboole_0(k2_struct_0('#skF_3'))
      | ~ l1_struct_0(A_116)
      | v2_struct_0(A_116) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_443])).

tff(c_453,plain,(
    ! [A_119] :
      ( v4_orders_2(k3_yellow19(A_119,k2_struct_0('#skF_3'),'#skF_4'))
      | ~ m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(u1_struct_0(A_119)))
      | ~ l1_struct_0(A_119)
      | v2_struct_0(A_119) ) ),
    inference(negUnitSimplification,[status(thm)],[c_418,c_60,c_450])).

tff(c_456,plain,
    ( v4_orders_2(k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4'))
    | ~ m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(k2_struct_0('#skF_3')))
    | ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_111,c_453])).

tff(c_458,plain,
    ( v4_orders_2(k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4'))
    | ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_456])).

tff(c_459,plain,
    ( v4_orders_2(k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4'))
    | ~ l1_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_458])).

tff(c_460,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_459])).

tff(c_463,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_14,c_460])).

tff(c_467,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_463])).

tff(c_469,plain,(
    l1_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_459])).

tff(c_468,plain,(
    v4_orders_2(k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4')) ),
    inference(splitRight,[status(thm)],[c_459])).

tff(c_540,plain,(
    ! [A_135,B_136,C_137] :
      ( v7_waybel_0(k3_yellow19(A_135,B_136,C_137))
      | ~ m1_subset_1(C_137,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_136))))
      | ~ v13_waybel_0(C_137,k3_yellow_1(B_136))
      | ~ v2_waybel_0(C_137,k3_yellow_1(B_136))
      | ~ v1_subset_1(C_137,u1_struct_0(k3_yellow_1(B_136)))
      | v1_xboole_0(C_137)
      | ~ m1_subset_1(B_136,k1_zfmisc_1(u1_struct_0(A_135)))
      | v1_xboole_0(B_136)
      | ~ l1_struct_0(A_135)
      | v2_struct_0(A_135) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_545,plain,(
    ! [A_135] :
      ( v7_waybel_0(k3_yellow19(A_135,k2_struct_0('#skF_3'),'#skF_4'))
      | ~ v13_waybel_0('#skF_4',k3_yellow_1(k2_struct_0('#skF_3')))
      | ~ v2_waybel_0('#skF_4',k3_yellow_1(k2_struct_0('#skF_3')))
      | ~ v1_subset_1('#skF_4',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3'))))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(u1_struct_0(A_135)))
      | v1_xboole_0(k2_struct_0('#skF_3'))
      | ~ l1_struct_0(A_135)
      | v2_struct_0(A_135) ) ),
    inference(resolution,[status(thm)],[c_52,c_540])).

tff(c_552,plain,(
    ! [A_135] :
      ( v7_waybel_0(k3_yellow19(A_135,k2_struct_0('#skF_3'),'#skF_4'))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(u1_struct_0(A_135)))
      | v1_xboole_0(k2_struct_0('#skF_3'))
      | ~ l1_struct_0(A_135)
      | v2_struct_0(A_135) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_545])).

tff(c_555,plain,(
    ! [A_138] :
      ( v7_waybel_0(k3_yellow19(A_138,k2_struct_0('#skF_3'),'#skF_4'))
      | ~ m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(u1_struct_0(A_138)))
      | ~ l1_struct_0(A_138)
      | v2_struct_0(A_138) ) ),
    inference(negUnitSimplification,[status(thm)],[c_418,c_60,c_552])).

tff(c_558,plain,
    ( v7_waybel_0(k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4'))
    | ~ m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(k2_struct_0('#skF_3')))
    | ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_111,c_555])).

tff(c_560,plain,
    ( v7_waybel_0(k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_469,c_75,c_558])).

tff(c_561,plain,(
    v7_waybel_0(k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_560])).

tff(c_519,plain,(
    ! [A_131,B_132,C_133] :
      ( l1_waybel_0(k3_yellow19(A_131,B_132,C_133),A_131)
      | ~ m1_subset_1(C_133,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_132))))
      | ~ v13_waybel_0(C_133,k3_yellow_1(B_132))
      | ~ v2_waybel_0(C_133,k3_yellow_1(B_132))
      | v1_xboole_0(C_133)
      | ~ m1_subset_1(B_132,k1_zfmisc_1(u1_struct_0(A_131)))
      | v1_xboole_0(B_132)
      | ~ l1_struct_0(A_131)
      | v2_struct_0(A_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_524,plain,(
    ! [A_131] :
      ( l1_waybel_0(k3_yellow19(A_131,k2_struct_0('#skF_3'),'#skF_4'),A_131)
      | ~ v13_waybel_0('#skF_4',k3_yellow_1(k2_struct_0('#skF_3')))
      | ~ v2_waybel_0('#skF_4',k3_yellow_1(k2_struct_0('#skF_3')))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(u1_struct_0(A_131)))
      | v1_xboole_0(k2_struct_0('#skF_3'))
      | ~ l1_struct_0(A_131)
      | v2_struct_0(A_131) ) ),
    inference(resolution,[status(thm)],[c_52,c_519])).

tff(c_531,plain,(
    ! [A_131] :
      ( l1_waybel_0(k3_yellow19(A_131,k2_struct_0('#skF_3'),'#skF_4'),A_131)
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(u1_struct_0(A_131)))
      | v1_xboole_0(k2_struct_0('#skF_3'))
      | ~ l1_struct_0(A_131)
      | v2_struct_0(A_131) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_524])).

tff(c_534,plain,(
    ! [A_134] :
      ( l1_waybel_0(k3_yellow19(A_134,k2_struct_0('#skF_3'),'#skF_4'),A_134)
      | ~ m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(u1_struct_0(A_134)))
      | ~ l1_struct_0(A_134)
      | v2_struct_0(A_134) ) ),
    inference(negUnitSimplification,[status(thm)],[c_418,c_60,c_531])).

tff(c_536,plain,
    ( l1_waybel_0(k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4'),'#skF_3')
    | ~ m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(k2_struct_0('#skF_3')))
    | ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_111,c_534])).

tff(c_538,plain,
    ( l1_waybel_0(k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4'),'#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_469,c_75,c_536])).

tff(c_539,plain,(
    l1_waybel_0(k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_538])).

tff(c_562,plain,(
    ! [A_139,B_140] :
      ( k2_yellow19(A_139,k3_yellow19(A_139,k2_struct_0(A_139),B_140)) = B_140
      | ~ m1_subset_1(B_140,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_139)))))
      | ~ v13_waybel_0(B_140,k3_yellow_1(k2_struct_0(A_139)))
      | ~ v2_waybel_0(B_140,k3_yellow_1(k2_struct_0(A_139)))
      | ~ v1_subset_1(B_140,u1_struct_0(k3_yellow_1(k2_struct_0(A_139))))
      | v1_xboole_0(B_140)
      | ~ l1_struct_0(A_139)
      | v2_struct_0(A_139) ) ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_567,plain,
    ( k2_yellow19('#skF_3',k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4')) = '#skF_4'
    | ~ v13_waybel_0('#skF_4',k3_yellow_1(k2_struct_0('#skF_3')))
    | ~ v2_waybel_0('#skF_4',k3_yellow_1(k2_struct_0('#skF_3')))
    | ~ v1_subset_1('#skF_4',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3'))))
    | v1_xboole_0('#skF_4')
    | ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_562])).

tff(c_574,plain,
    ( k2_yellow19('#skF_3',k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4')) = '#skF_4'
    | v1_xboole_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_469,c_58,c_56,c_54,c_567])).

tff(c_575,plain,(
    k2_yellow19('#skF_3',k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4')) = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_60,c_574])).

tff(c_580,plain,(
    ! [C_30] :
      ( r2_hidden(C_30,k10_yellow_6('#skF_3',k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4')))
      | ~ r2_waybel_7('#skF_3','#skF_4',C_30)
      | ~ m1_subset_1(C_30,u1_struct_0('#skF_3'))
      | ~ l1_waybel_0(k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4'),'#skF_3')
      | ~ v7_waybel_0(k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4'))
      | ~ v4_orders_2(k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4'))
      | v2_struct_0(k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_575,c_44])).

tff(c_587,plain,(
    ! [C_30] :
      ( r2_hidden(C_30,k10_yellow_6('#skF_3',k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4')))
      | ~ r2_waybel_7('#skF_3','#skF_4',C_30)
      | ~ m1_subset_1(C_30,k2_struct_0('#skF_3'))
      | v2_struct_0(k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_468,c_561,c_539,c_111,c_580])).

tff(c_588,plain,(
    ! [C_30] :
      ( r2_hidden(C_30,k10_yellow_6('#skF_3',k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4')))
      | ~ r2_waybel_7('#skF_3','#skF_4',C_30)
      | ~ m1_subset_1(C_30,k2_struct_0('#skF_3'))
      | v2_struct_0(k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_587])).

tff(c_593,plain,(
    v2_struct_0(k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_588])).

tff(c_595,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3')))))
    | ~ v13_waybel_0('#skF_4',k3_yellow_1(k2_struct_0('#skF_3')))
    | ~ v2_waybel_0('#skF_4',k3_yellow_1(k2_struct_0('#skF_3')))
    | v1_xboole_0('#skF_4')
    | ~ m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | v1_xboole_0(k2_struct_0('#skF_3'))
    | ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_593,c_36])).

tff(c_598,plain,
    ( v1_xboole_0('#skF_4')
    | v1_xboole_0(k2_struct_0('#skF_3'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_469,c_75,c_111,c_56,c_54,c_52,c_595])).

tff(c_600,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_418,c_60,c_598])).

tff(c_602,plain,(
    ~ v2_struct_0(k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4')) ),
    inference(splitRight,[status(thm)],[c_588])).

tff(c_46,plain,(
    ! [A_24,B_28,C_30] :
      ( r2_waybel_7(A_24,k2_yellow19(A_24,B_28),C_30)
      | ~ r2_hidden(C_30,k10_yellow_6(A_24,B_28))
      | ~ m1_subset_1(C_30,u1_struct_0(A_24))
      | ~ l1_waybel_0(B_28,A_24)
      | ~ v7_waybel_0(B_28)
      | ~ v4_orders_2(B_28)
      | v2_struct_0(B_28)
      | ~ l1_pre_topc(A_24)
      | ~ v2_pre_topc(A_24)
      | v2_struct_0(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_583,plain,(
    ! [C_30] :
      ( r2_waybel_7('#skF_3','#skF_4',C_30)
      | ~ r2_hidden(C_30,k10_yellow_6('#skF_3',k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4')))
      | ~ m1_subset_1(C_30,u1_struct_0('#skF_3'))
      | ~ l1_waybel_0(k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4'),'#skF_3')
      | ~ v7_waybel_0(k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4'))
      | ~ v4_orders_2(k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4'))
      | v2_struct_0(k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_575,c_46])).

tff(c_590,plain,(
    ! [C_30] :
      ( r2_waybel_7('#skF_3','#skF_4',C_30)
      | ~ r2_hidden(C_30,k10_yellow_6('#skF_3',k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4')))
      | ~ m1_subset_1(C_30,k2_struct_0('#skF_3'))
      | v2_struct_0(k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_468,c_561,c_539,c_111,c_583])).

tff(c_591,plain,(
    ! [C_30] :
      ( r2_waybel_7('#skF_3','#skF_4',C_30)
      | ~ r2_hidden(C_30,k10_yellow_6('#skF_3',k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4')))
      | ~ m1_subset_1(C_30,k2_struct_0('#skF_3'))
      | v2_struct_0(k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_590])).

tff(c_610,plain,(
    ! [C_144] :
      ( r2_waybel_7('#skF_3','#skF_4',C_144)
      | ~ r2_hidden(C_144,k10_yellow_6('#skF_3',k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4')))
      | ~ m1_subset_1(C_144,k2_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_602,c_591])).

tff(c_616,plain,
    ( r2_waybel_7('#skF_3','#skF_4','#skF_5')
    | ~ m1_subset_1('#skF_5',k2_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_387,c_610])).

tff(c_624,plain,(
    r2_waybel_7('#skF_3','#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_616])).

tff(c_626,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_388,c_624])).

tff(c_629,plain,(
    ! [A_145] : ~ r2_hidden(A_145,'#skF_2'('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_417])).

tff(c_634,plain,(
    v1_xboole_0('#skF_2'('#skF_3')) ),
    inference(resolution,[status(thm)],[c_4,c_629])).

tff(c_637,plain,
    ( ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_634,c_18])).

tff(c_640,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_637])).

tff(c_642,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_640])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:40:56 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.45/1.67  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.45/1.69  
% 3.45/1.69  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.75/1.70  %$ r2_waybel_7 > v6_waybel_0 > v4_pre_topc > v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_hidden > m1_subset_1 > l1_waybel_0 > v7_waybel_0 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k3_yellow19 > k2_yellow19 > k10_yellow_6 > #nlpp > u1_struct_0 > k3_yellow_1 > k3_lattice3 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_lattice3 > #skF_2 > #skF_1 > #skF_5 > #skF_3 > #skF_4
% 3.75/1.70  
% 3.75/1.70  %Foreground sorts:
% 3.75/1.70  
% 3.75/1.70  
% 3.75/1.70  %Background operators:
% 3.75/1.70  
% 3.75/1.70  
% 3.75/1.70  %Foreground operators:
% 3.75/1.70  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.75/1.70  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 3.75/1.70  tff('#skF_2', type, '#skF_2': $i > $i).
% 3.75/1.70  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.75/1.70  tff(k3_lattice3, type, k3_lattice3: $i > $i).
% 3.75/1.70  tff(v6_waybel_0, type, v6_waybel_0: ($i * $i) > $o).
% 3.75/1.70  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.75/1.70  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 3.75/1.70  tff(k3_yellow_1, type, k3_yellow_1: $i > $i).
% 3.75/1.70  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.75/1.70  tff(v2_waybel_0, type, v2_waybel_0: ($i * $i) > $o).
% 3.75/1.70  tff(k10_yellow_6, type, k10_yellow_6: ($i * $i) > $i).
% 3.75/1.70  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.75/1.70  tff(v7_waybel_0, type, v7_waybel_0: $i > $o).
% 3.75/1.70  tff('#skF_5', type, '#skF_5': $i).
% 3.75/1.70  tff('#skF_3', type, '#skF_3': $i).
% 3.75/1.70  tff(k1_lattice3, type, k1_lattice3: $i > $i).
% 3.75/1.70  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 3.75/1.70  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.75/1.70  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.75/1.70  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 3.75/1.70  tff(k2_yellow19, type, k2_yellow19: ($i * $i) > $i).
% 3.75/1.70  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.75/1.70  tff(l1_waybel_0, type, l1_waybel_0: ($i * $i) > $o).
% 3.75/1.70  tff('#skF_4', type, '#skF_4': $i).
% 3.75/1.70  tff(r2_waybel_7, type, r2_waybel_7: ($i * $i * $i) > $o).
% 3.75/1.70  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.75/1.70  tff(k3_yellow19, type, k3_yellow19: ($i * $i * $i) > $i).
% 3.75/1.70  tff(v13_waybel_0, type, v13_waybel_0: ($i * $i) > $o).
% 3.75/1.70  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.75/1.70  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.75/1.70  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 3.75/1.70  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 3.75/1.70  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.75/1.70  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.75/1.70  
% 3.75/1.73  tff(f_219, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((((~v1_xboole_0(B) & v1_subset_1(B, u1_struct_0(k3_yellow_1(k2_struct_0(A))))) & v2_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & v13_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A)))))) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_hidden(C, k10_yellow_6(A, k3_yellow19(A, k2_struct_0(A), B))) <=> r2_waybel_7(A, B, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_yellow19)).
% 3.75/1.73  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.75/1.73  tff(f_50, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.75/1.73  tff(f_46, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 3.75/1.73  tff(f_65, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (?[B]: ((m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) & ~v1_xboole_0(B)) & v4_pre_topc(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc7_pre_topc)).
% 3.75/1.73  tff(f_42, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 3.75/1.73  tff(f_33, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 3.75/1.73  tff(f_35, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 3.75/1.73  tff(f_121, axiom, (![A, B, C]: ((((((((~v2_struct_0(A) & l1_struct_0(A)) & ~v1_xboole_0(B)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) & ~v1_xboole_0(C)) & v2_waybel_0(C, k3_yellow_1(B))) & v13_waybel_0(C, k3_yellow_1(B))) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B))))) => (((~v2_struct_0(k3_yellow19(A, B, C)) & v3_orders_2(k3_yellow19(A, B, C))) & v4_orders_2(k3_yellow19(A, B, C))) & v6_waybel_0(k3_yellow19(A, B, C), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_yellow19)).
% 3.75/1.73  tff(f_93, axiom, (![A, B, C]: ((((((((~v2_struct_0(A) & l1_struct_0(A)) & ~v1_xboole_0(B)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) & ~v1_xboole_0(C)) & v2_waybel_0(C, k3_yellow_1(B))) & v13_waybel_0(C, k3_yellow_1(B))) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B))))) => ((~v2_struct_0(k3_yellow19(A, B, C)) & v6_waybel_0(k3_yellow19(A, B, C), A)) & l1_waybel_0(k3_yellow19(A, B, C), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_yellow19)).
% 3.75/1.73  tff(f_192, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: (((((~v1_xboole_0(B) & v1_subset_1(B, u1_struct_0(k3_yellow_1(k2_struct_0(A))))) & v2_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & v13_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A)))))) => (B = k2_yellow19(A, k3_yellow19(A, k2_struct_0(A), B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_yellow19)).
% 3.75/1.73  tff(f_173, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_hidden(C, k10_yellow_6(A, B)) <=> r2_waybel_7(A, k2_yellow19(A, B), C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_yellow19)).
% 3.75/1.73  tff(f_149, axiom, (![A, B, C]: (((((((((~v2_struct_0(A) & l1_struct_0(A)) & ~v1_xboole_0(B)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) & ~v1_xboole_0(C)) & v1_subset_1(C, u1_struct_0(k3_yellow_1(B)))) & v2_waybel_0(C, k3_yellow_1(B))) & v13_waybel_0(C, k3_yellow_1(B))) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B))))) => ((~v2_struct_0(k3_yellow19(A, B, C)) & v6_waybel_0(k3_yellow19(A, B, C), A)) & v7_waybel_0(k3_yellow19(A, B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc5_yellow19)).
% 3.75/1.73  tff(c_66, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_219])).
% 3.75/1.73  tff(c_64, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_219])).
% 3.75/1.73  tff(c_62, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_219])).
% 3.75/1.73  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.75/1.73  tff(c_14, plain, (![A_11]: (l1_struct_0(A_11) | ~l1_pre_topc(A_11))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.75/1.73  tff(c_102, plain, (![A_45]: (u1_struct_0(A_45)=k2_struct_0(A_45) | ~l1_struct_0(A_45))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.75/1.73  tff(c_107, plain, (![A_46]: (u1_struct_0(A_46)=k2_struct_0(A_46) | ~l1_pre_topc(A_46))), inference(resolution, [status(thm)], [c_14, c_102])).
% 3.75/1.73  tff(c_111, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_62, c_107])).
% 3.75/1.73  tff(c_50, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_219])).
% 3.75/1.73  tff(c_112, plain, (m1_subset_1('#skF_5', k2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_111, c_50])).
% 3.75/1.73  tff(c_74, plain, (r2_hidden('#skF_5', k10_yellow_6('#skF_3', k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4'))) | r2_waybel_7('#skF_3', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_219])).
% 3.75/1.73  tff(c_117, plain, (r2_waybel_7('#skF_3', '#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_74])).
% 3.75/1.73  tff(c_128, plain, (![A_52]: (m1_subset_1('#skF_2'(A_52), k1_zfmisc_1(u1_struct_0(A_52))) | ~l1_pre_topc(A_52) | ~v2_pre_topc(A_52) | v2_struct_0(A_52))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.75/1.73  tff(c_133, plain, (m1_subset_1('#skF_2'('#skF_3'), k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_111, c_128])).
% 3.75/1.73  tff(c_136, plain, (m1_subset_1('#skF_2'('#skF_3'), k1_zfmisc_1(k2_struct_0('#skF_3'))) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_133])).
% 3.75/1.73  tff(c_137, plain, (m1_subset_1('#skF_2'('#skF_3'), k1_zfmisc_1(k2_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_66, c_136])).
% 3.75/1.73  tff(c_10, plain, (![C_9, B_8, A_7]: (~v1_xboole_0(C_9) | ~m1_subset_1(B_8, k1_zfmisc_1(C_9)) | ~r2_hidden(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.75/1.73  tff(c_140, plain, (![A_7]: (~v1_xboole_0(k2_struct_0('#skF_3')) | ~r2_hidden(A_7, '#skF_2'('#skF_3')))), inference(resolution, [status(thm)], [c_137, c_10])).
% 3.75/1.73  tff(c_141, plain, (~v1_xboole_0(k2_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_140])).
% 3.75/1.73  tff(c_60, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_219])).
% 3.75/1.73  tff(c_6, plain, (![A_5]: (k2_subset_1(A_5)=A_5)), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.75/1.73  tff(c_8, plain, (![A_6]: (m1_subset_1(k2_subset_1(A_6), k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.75/1.73  tff(c_75, plain, (![A_6]: (m1_subset_1(A_6, k1_zfmisc_1(A_6)))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_8])).
% 3.75/1.73  tff(c_56, plain, (v2_waybel_0('#skF_4', k3_yellow_1(k2_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_219])).
% 3.75/1.73  tff(c_54, plain, (v13_waybel_0('#skF_4', k3_yellow_1(k2_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_219])).
% 3.75/1.73  tff(c_52, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3')))))), inference(cnfTransformation, [status(thm)], [f_219])).
% 3.75/1.73  tff(c_163, plain, (![A_62, B_63, C_64]: (v3_orders_2(k3_yellow19(A_62, B_63, C_64)) | ~m1_subset_1(C_64, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_63)))) | ~v13_waybel_0(C_64, k3_yellow_1(B_63)) | ~v2_waybel_0(C_64, k3_yellow_1(B_63)) | v1_xboole_0(C_64) | ~m1_subset_1(B_63, k1_zfmisc_1(u1_struct_0(A_62))) | v1_xboole_0(B_63) | ~l1_struct_0(A_62) | v2_struct_0(A_62))), inference(cnfTransformation, [status(thm)], [f_121])).
% 3.75/1.73  tff(c_168, plain, (![A_62]: (v3_orders_2(k3_yellow19(A_62, k2_struct_0('#skF_3'), '#skF_4')) | ~v13_waybel_0('#skF_4', k3_yellow_1(k2_struct_0('#skF_3'))) | ~v2_waybel_0('#skF_4', k3_yellow_1(k2_struct_0('#skF_3'))) | v1_xboole_0('#skF_4') | ~m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(u1_struct_0(A_62))) | v1_xboole_0(k2_struct_0('#skF_3')) | ~l1_struct_0(A_62) | v2_struct_0(A_62))), inference(resolution, [status(thm)], [c_52, c_163])).
% 3.75/1.73  tff(c_175, plain, (![A_62]: (v3_orders_2(k3_yellow19(A_62, k2_struct_0('#skF_3'), '#skF_4')) | v1_xboole_0('#skF_4') | ~m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(u1_struct_0(A_62))) | v1_xboole_0(k2_struct_0('#skF_3')) | ~l1_struct_0(A_62) | v2_struct_0(A_62))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_168])).
% 3.75/1.73  tff(c_178, plain, (![A_65]: (v3_orders_2(k3_yellow19(A_65, k2_struct_0('#skF_3'), '#skF_4')) | ~m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(u1_struct_0(A_65))) | ~l1_struct_0(A_65) | v2_struct_0(A_65))), inference(negUnitSimplification, [status(thm)], [c_141, c_60, c_175])).
% 3.75/1.73  tff(c_181, plain, (v3_orders_2(k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4')) | ~m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_111, c_178])).
% 3.75/1.73  tff(c_183, plain, (v3_orders_2(k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4')) | ~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_75, c_181])).
% 3.75/1.73  tff(c_184, plain, (v3_orders_2(k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4')) | ~l1_struct_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_66, c_183])).
% 3.75/1.73  tff(c_185, plain, (~l1_struct_0('#skF_3')), inference(splitLeft, [status(thm)], [c_184])).
% 3.75/1.73  tff(c_188, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_14, c_185])).
% 3.75/1.73  tff(c_192, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_62, c_188])).
% 3.75/1.73  tff(c_194, plain, (l1_struct_0('#skF_3')), inference(splitRight, [status(thm)], [c_184])).
% 3.75/1.73  tff(c_200, plain, (![A_66, B_67, C_68]: (v4_orders_2(k3_yellow19(A_66, B_67, C_68)) | ~m1_subset_1(C_68, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_67)))) | ~v13_waybel_0(C_68, k3_yellow_1(B_67)) | ~v2_waybel_0(C_68, k3_yellow_1(B_67)) | v1_xboole_0(C_68) | ~m1_subset_1(B_67, k1_zfmisc_1(u1_struct_0(A_66))) | v1_xboole_0(B_67) | ~l1_struct_0(A_66) | v2_struct_0(A_66))), inference(cnfTransformation, [status(thm)], [f_121])).
% 3.75/1.73  tff(c_205, plain, (![A_66]: (v4_orders_2(k3_yellow19(A_66, k2_struct_0('#skF_3'), '#skF_4')) | ~v13_waybel_0('#skF_4', k3_yellow_1(k2_struct_0('#skF_3'))) | ~v2_waybel_0('#skF_4', k3_yellow_1(k2_struct_0('#skF_3'))) | v1_xboole_0('#skF_4') | ~m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(u1_struct_0(A_66))) | v1_xboole_0(k2_struct_0('#skF_3')) | ~l1_struct_0(A_66) | v2_struct_0(A_66))), inference(resolution, [status(thm)], [c_52, c_200])).
% 3.75/1.73  tff(c_212, plain, (![A_66]: (v4_orders_2(k3_yellow19(A_66, k2_struct_0('#skF_3'), '#skF_4')) | v1_xboole_0('#skF_4') | ~m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(u1_struct_0(A_66))) | v1_xboole_0(k2_struct_0('#skF_3')) | ~l1_struct_0(A_66) | v2_struct_0(A_66))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_205])).
% 3.75/1.73  tff(c_215, plain, (![A_69]: (v4_orders_2(k3_yellow19(A_69, k2_struct_0('#skF_3'), '#skF_4')) | ~m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(u1_struct_0(A_69))) | ~l1_struct_0(A_69) | v2_struct_0(A_69))), inference(negUnitSimplification, [status(thm)], [c_141, c_60, c_212])).
% 3.75/1.73  tff(c_218, plain, (v4_orders_2(k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4')) | ~m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_111, c_215])).
% 3.75/1.73  tff(c_220, plain, (v4_orders_2(k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4')) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_194, c_75, c_218])).
% 3.75/1.73  tff(c_221, plain, (v4_orders_2(k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_66, c_220])).
% 3.75/1.73  tff(c_244, plain, (![A_77, B_78, C_79]: (l1_waybel_0(k3_yellow19(A_77, B_78, C_79), A_77) | ~m1_subset_1(C_79, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_78)))) | ~v13_waybel_0(C_79, k3_yellow_1(B_78)) | ~v2_waybel_0(C_79, k3_yellow_1(B_78)) | v1_xboole_0(C_79) | ~m1_subset_1(B_78, k1_zfmisc_1(u1_struct_0(A_77))) | v1_xboole_0(B_78) | ~l1_struct_0(A_77) | v2_struct_0(A_77))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.75/1.73  tff(c_249, plain, (![A_77]: (l1_waybel_0(k3_yellow19(A_77, k2_struct_0('#skF_3'), '#skF_4'), A_77) | ~v13_waybel_0('#skF_4', k3_yellow_1(k2_struct_0('#skF_3'))) | ~v2_waybel_0('#skF_4', k3_yellow_1(k2_struct_0('#skF_3'))) | v1_xboole_0('#skF_4') | ~m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(u1_struct_0(A_77))) | v1_xboole_0(k2_struct_0('#skF_3')) | ~l1_struct_0(A_77) | v2_struct_0(A_77))), inference(resolution, [status(thm)], [c_52, c_244])).
% 3.75/1.73  tff(c_256, plain, (![A_77]: (l1_waybel_0(k3_yellow19(A_77, k2_struct_0('#skF_3'), '#skF_4'), A_77) | v1_xboole_0('#skF_4') | ~m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(u1_struct_0(A_77))) | v1_xboole_0(k2_struct_0('#skF_3')) | ~l1_struct_0(A_77) | v2_struct_0(A_77))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_249])).
% 3.75/1.73  tff(c_259, plain, (![A_80]: (l1_waybel_0(k3_yellow19(A_80, k2_struct_0('#skF_3'), '#skF_4'), A_80) | ~m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(u1_struct_0(A_80))) | ~l1_struct_0(A_80) | v2_struct_0(A_80))), inference(negUnitSimplification, [status(thm)], [c_141, c_60, c_256])).
% 3.75/1.73  tff(c_261, plain, (l1_waybel_0(k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4'), '#skF_3') | ~m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_111, c_259])).
% 3.75/1.73  tff(c_263, plain, (l1_waybel_0(k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4'), '#skF_3') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_194, c_75, c_261])).
% 3.75/1.73  tff(c_264, plain, (l1_waybel_0(k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_66, c_263])).
% 3.75/1.73  tff(c_58, plain, (v1_subset_1('#skF_4', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_219])).
% 3.75/1.73  tff(c_269, plain, (![A_89, B_90]: (k2_yellow19(A_89, k3_yellow19(A_89, k2_struct_0(A_89), B_90))=B_90 | ~m1_subset_1(B_90, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_89))))) | ~v13_waybel_0(B_90, k3_yellow_1(k2_struct_0(A_89))) | ~v2_waybel_0(B_90, k3_yellow_1(k2_struct_0(A_89))) | ~v1_subset_1(B_90, u1_struct_0(k3_yellow_1(k2_struct_0(A_89)))) | v1_xboole_0(B_90) | ~l1_struct_0(A_89) | v2_struct_0(A_89))), inference(cnfTransformation, [status(thm)], [f_192])).
% 3.75/1.73  tff(c_274, plain, (k2_yellow19('#skF_3', k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4'))='#skF_4' | ~v13_waybel_0('#skF_4', k3_yellow_1(k2_struct_0('#skF_3'))) | ~v2_waybel_0('#skF_4', k3_yellow_1(k2_struct_0('#skF_3'))) | ~v1_subset_1('#skF_4', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3')))) | v1_xboole_0('#skF_4') | ~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_52, c_269])).
% 3.75/1.73  tff(c_281, plain, (k2_yellow19('#skF_3', k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4'))='#skF_4' | v1_xboole_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_194, c_58, c_56, c_54, c_274])).
% 3.75/1.73  tff(c_282, plain, (k2_yellow19('#skF_3', k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4'))='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_66, c_60, c_281])).
% 3.75/1.73  tff(c_44, plain, (![C_30, A_24, B_28]: (r2_hidden(C_30, k10_yellow_6(A_24, B_28)) | ~r2_waybel_7(A_24, k2_yellow19(A_24, B_28), C_30) | ~m1_subset_1(C_30, u1_struct_0(A_24)) | ~l1_waybel_0(B_28, A_24) | ~v7_waybel_0(B_28) | ~v4_orders_2(B_28) | v2_struct_0(B_28) | ~l1_pre_topc(A_24) | ~v2_pre_topc(A_24) | v2_struct_0(A_24))), inference(cnfTransformation, [status(thm)], [f_173])).
% 3.75/1.73  tff(c_287, plain, (![C_30]: (r2_hidden(C_30, k10_yellow_6('#skF_3', k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4'))) | ~r2_waybel_7('#skF_3', '#skF_4', C_30) | ~m1_subset_1(C_30, u1_struct_0('#skF_3')) | ~l1_waybel_0(k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4'), '#skF_3') | ~v7_waybel_0(k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4')) | ~v4_orders_2(k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4')) | v2_struct_0(k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_282, c_44])).
% 3.75/1.73  tff(c_294, plain, (![C_30]: (r2_hidden(C_30, k10_yellow_6('#skF_3', k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4'))) | ~r2_waybel_7('#skF_3', '#skF_4', C_30) | ~m1_subset_1(C_30, k2_struct_0('#skF_3')) | ~v7_waybel_0(k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4')) | v2_struct_0(k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_221, c_264, c_111, c_287])).
% 3.75/1.73  tff(c_295, plain, (![C_30]: (r2_hidden(C_30, k10_yellow_6('#skF_3', k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4'))) | ~r2_waybel_7('#skF_3', '#skF_4', C_30) | ~m1_subset_1(C_30, k2_struct_0('#skF_3')) | ~v7_waybel_0(k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4')) | v2_struct_0(k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_66, c_294])).
% 3.75/1.73  tff(c_300, plain, (~v7_waybel_0(k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4'))), inference(splitLeft, [status(thm)], [c_295])).
% 3.75/1.73  tff(c_301, plain, (![A_91, B_92, C_93]: (v7_waybel_0(k3_yellow19(A_91, B_92, C_93)) | ~m1_subset_1(C_93, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_92)))) | ~v13_waybel_0(C_93, k3_yellow_1(B_92)) | ~v2_waybel_0(C_93, k3_yellow_1(B_92)) | ~v1_subset_1(C_93, u1_struct_0(k3_yellow_1(B_92))) | v1_xboole_0(C_93) | ~m1_subset_1(B_92, k1_zfmisc_1(u1_struct_0(A_91))) | v1_xboole_0(B_92) | ~l1_struct_0(A_91) | v2_struct_0(A_91))), inference(cnfTransformation, [status(thm)], [f_149])).
% 3.75/1.73  tff(c_306, plain, (![A_91]: (v7_waybel_0(k3_yellow19(A_91, k2_struct_0('#skF_3'), '#skF_4')) | ~v13_waybel_0('#skF_4', k3_yellow_1(k2_struct_0('#skF_3'))) | ~v2_waybel_0('#skF_4', k3_yellow_1(k2_struct_0('#skF_3'))) | ~v1_subset_1('#skF_4', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3')))) | v1_xboole_0('#skF_4') | ~m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(u1_struct_0(A_91))) | v1_xboole_0(k2_struct_0('#skF_3')) | ~l1_struct_0(A_91) | v2_struct_0(A_91))), inference(resolution, [status(thm)], [c_52, c_301])).
% 3.75/1.73  tff(c_313, plain, (![A_91]: (v7_waybel_0(k3_yellow19(A_91, k2_struct_0('#skF_3'), '#skF_4')) | v1_xboole_0('#skF_4') | ~m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(u1_struct_0(A_91))) | v1_xboole_0(k2_struct_0('#skF_3')) | ~l1_struct_0(A_91) | v2_struct_0(A_91))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_306])).
% 3.75/1.73  tff(c_316, plain, (![A_94]: (v7_waybel_0(k3_yellow19(A_94, k2_struct_0('#skF_3'), '#skF_4')) | ~m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(u1_struct_0(A_94))) | ~l1_struct_0(A_94) | v2_struct_0(A_94))), inference(negUnitSimplification, [status(thm)], [c_141, c_60, c_313])).
% 3.75/1.73  tff(c_319, plain, (v7_waybel_0(k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4')) | ~m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_111, c_316])).
% 3.75/1.73  tff(c_321, plain, (v7_waybel_0(k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4')) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_194, c_75, c_319])).
% 3.75/1.73  tff(c_323, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_300, c_321])).
% 3.75/1.73  tff(c_324, plain, (![C_30]: (v2_struct_0(k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4')) | r2_hidden(C_30, k10_yellow_6('#skF_3', k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4'))) | ~r2_waybel_7('#skF_3', '#skF_4', C_30) | ~m1_subset_1(C_30, k2_struct_0('#skF_3')))), inference(splitRight, [status(thm)], [c_295])).
% 3.75/1.73  tff(c_326, plain, (v2_struct_0(k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4'))), inference(splitLeft, [status(thm)], [c_324])).
% 3.75/1.73  tff(c_36, plain, (![A_18, B_19, C_20]: (~v2_struct_0(k3_yellow19(A_18, B_19, C_20)) | ~m1_subset_1(C_20, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_19)))) | ~v13_waybel_0(C_20, k3_yellow_1(B_19)) | ~v2_waybel_0(C_20, k3_yellow_1(B_19)) | v1_xboole_0(C_20) | ~m1_subset_1(B_19, k1_zfmisc_1(u1_struct_0(A_18))) | v1_xboole_0(B_19) | ~l1_struct_0(A_18) | v2_struct_0(A_18))), inference(cnfTransformation, [status(thm)], [f_121])).
% 3.75/1.73  tff(c_328, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3'))))) | ~v13_waybel_0('#skF_4', k3_yellow_1(k2_struct_0('#skF_3'))) | ~v2_waybel_0('#skF_4', k3_yellow_1(k2_struct_0('#skF_3'))) | v1_xboole_0('#skF_4') | ~m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | v1_xboole_0(k2_struct_0('#skF_3')) | ~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_326, c_36])).
% 3.75/1.73  tff(c_331, plain, (v1_xboole_0('#skF_4') | v1_xboole_0(k2_struct_0('#skF_3')) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_194, c_75, c_111, c_56, c_54, c_52, c_328])).
% 3.75/1.73  tff(c_333, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_141, c_60, c_331])).
% 3.75/1.73  tff(c_358, plain, (![C_99]: (r2_hidden(C_99, k10_yellow_6('#skF_3', k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4'))) | ~r2_waybel_7('#skF_3', '#skF_4', C_99) | ~m1_subset_1(C_99, k2_struct_0('#skF_3')))), inference(splitRight, [status(thm)], [c_324])).
% 3.75/1.73  tff(c_68, plain, (~r2_waybel_7('#skF_3', '#skF_4', '#skF_5') | ~r2_hidden('#skF_5', k10_yellow_6('#skF_3', k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_219])).
% 3.75/1.73  tff(c_143, plain, (~r2_hidden('#skF_5', k10_yellow_6('#skF_3', k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_117, c_68])).
% 3.75/1.73  tff(c_361, plain, (~r2_waybel_7('#skF_3', '#skF_4', '#skF_5') | ~m1_subset_1('#skF_5', k2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_358, c_143])).
% 3.75/1.73  tff(c_368, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_112, c_117, c_361])).
% 3.75/1.73  tff(c_373, plain, (![A_100]: (~r2_hidden(A_100, '#skF_2'('#skF_3')))), inference(splitRight, [status(thm)], [c_140])).
% 3.75/1.73  tff(c_378, plain, (v1_xboole_0('#skF_2'('#skF_3'))), inference(resolution, [status(thm)], [c_4, c_373])).
% 3.75/1.73  tff(c_18, plain, (![A_12]: (~v1_xboole_0('#skF_2'(A_12)) | ~l1_pre_topc(A_12) | ~v2_pre_topc(A_12) | v2_struct_0(A_12))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.75/1.73  tff(c_381, plain, (~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_378, c_18])).
% 3.75/1.73  tff(c_384, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_381])).
% 3.75/1.73  tff(c_386, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_384])).
% 3.75/1.73  tff(c_388, plain, (~r2_waybel_7('#skF_3', '#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_74])).
% 3.75/1.73  tff(c_387, plain, (r2_hidden('#skF_5', k10_yellow_6('#skF_3', k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4')))), inference(splitRight, [status(thm)], [c_74])).
% 3.75/1.73  tff(c_405, plain, (![A_106]: (m1_subset_1('#skF_2'(A_106), k1_zfmisc_1(u1_struct_0(A_106))) | ~l1_pre_topc(A_106) | ~v2_pre_topc(A_106) | v2_struct_0(A_106))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.75/1.73  tff(c_410, plain, (m1_subset_1('#skF_2'('#skF_3'), k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_111, c_405])).
% 3.75/1.73  tff(c_413, plain, (m1_subset_1('#skF_2'('#skF_3'), k1_zfmisc_1(k2_struct_0('#skF_3'))) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_410])).
% 3.75/1.73  tff(c_414, plain, (m1_subset_1('#skF_2'('#skF_3'), k1_zfmisc_1(k2_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_66, c_413])).
% 3.75/1.73  tff(c_417, plain, (![A_7]: (~v1_xboole_0(k2_struct_0('#skF_3')) | ~r2_hidden(A_7, '#skF_2'('#skF_3')))), inference(resolution, [status(thm)], [c_414, c_10])).
% 3.75/1.73  tff(c_418, plain, (~v1_xboole_0(k2_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_417])).
% 3.75/1.73  tff(c_438, plain, (![A_116, B_117, C_118]: (v4_orders_2(k3_yellow19(A_116, B_117, C_118)) | ~m1_subset_1(C_118, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_117)))) | ~v13_waybel_0(C_118, k3_yellow_1(B_117)) | ~v2_waybel_0(C_118, k3_yellow_1(B_117)) | v1_xboole_0(C_118) | ~m1_subset_1(B_117, k1_zfmisc_1(u1_struct_0(A_116))) | v1_xboole_0(B_117) | ~l1_struct_0(A_116) | v2_struct_0(A_116))), inference(cnfTransformation, [status(thm)], [f_121])).
% 3.75/1.73  tff(c_443, plain, (![A_116]: (v4_orders_2(k3_yellow19(A_116, k2_struct_0('#skF_3'), '#skF_4')) | ~v13_waybel_0('#skF_4', k3_yellow_1(k2_struct_0('#skF_3'))) | ~v2_waybel_0('#skF_4', k3_yellow_1(k2_struct_0('#skF_3'))) | v1_xboole_0('#skF_4') | ~m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(u1_struct_0(A_116))) | v1_xboole_0(k2_struct_0('#skF_3')) | ~l1_struct_0(A_116) | v2_struct_0(A_116))), inference(resolution, [status(thm)], [c_52, c_438])).
% 3.75/1.73  tff(c_450, plain, (![A_116]: (v4_orders_2(k3_yellow19(A_116, k2_struct_0('#skF_3'), '#skF_4')) | v1_xboole_0('#skF_4') | ~m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(u1_struct_0(A_116))) | v1_xboole_0(k2_struct_0('#skF_3')) | ~l1_struct_0(A_116) | v2_struct_0(A_116))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_443])).
% 3.75/1.73  tff(c_453, plain, (![A_119]: (v4_orders_2(k3_yellow19(A_119, k2_struct_0('#skF_3'), '#skF_4')) | ~m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(u1_struct_0(A_119))) | ~l1_struct_0(A_119) | v2_struct_0(A_119))), inference(negUnitSimplification, [status(thm)], [c_418, c_60, c_450])).
% 3.75/1.73  tff(c_456, plain, (v4_orders_2(k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4')) | ~m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_111, c_453])).
% 3.75/1.73  tff(c_458, plain, (v4_orders_2(k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4')) | ~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_75, c_456])).
% 3.75/1.73  tff(c_459, plain, (v4_orders_2(k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4')) | ~l1_struct_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_66, c_458])).
% 3.75/1.73  tff(c_460, plain, (~l1_struct_0('#skF_3')), inference(splitLeft, [status(thm)], [c_459])).
% 3.75/1.73  tff(c_463, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_14, c_460])).
% 3.75/1.73  tff(c_467, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_62, c_463])).
% 3.75/1.73  tff(c_469, plain, (l1_struct_0('#skF_3')), inference(splitRight, [status(thm)], [c_459])).
% 3.75/1.73  tff(c_468, plain, (v4_orders_2(k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4'))), inference(splitRight, [status(thm)], [c_459])).
% 3.75/1.73  tff(c_540, plain, (![A_135, B_136, C_137]: (v7_waybel_0(k3_yellow19(A_135, B_136, C_137)) | ~m1_subset_1(C_137, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_136)))) | ~v13_waybel_0(C_137, k3_yellow_1(B_136)) | ~v2_waybel_0(C_137, k3_yellow_1(B_136)) | ~v1_subset_1(C_137, u1_struct_0(k3_yellow_1(B_136))) | v1_xboole_0(C_137) | ~m1_subset_1(B_136, k1_zfmisc_1(u1_struct_0(A_135))) | v1_xboole_0(B_136) | ~l1_struct_0(A_135) | v2_struct_0(A_135))), inference(cnfTransformation, [status(thm)], [f_149])).
% 3.75/1.73  tff(c_545, plain, (![A_135]: (v7_waybel_0(k3_yellow19(A_135, k2_struct_0('#skF_3'), '#skF_4')) | ~v13_waybel_0('#skF_4', k3_yellow_1(k2_struct_0('#skF_3'))) | ~v2_waybel_0('#skF_4', k3_yellow_1(k2_struct_0('#skF_3'))) | ~v1_subset_1('#skF_4', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3')))) | v1_xboole_0('#skF_4') | ~m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(u1_struct_0(A_135))) | v1_xboole_0(k2_struct_0('#skF_3')) | ~l1_struct_0(A_135) | v2_struct_0(A_135))), inference(resolution, [status(thm)], [c_52, c_540])).
% 3.75/1.73  tff(c_552, plain, (![A_135]: (v7_waybel_0(k3_yellow19(A_135, k2_struct_0('#skF_3'), '#skF_4')) | v1_xboole_0('#skF_4') | ~m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(u1_struct_0(A_135))) | v1_xboole_0(k2_struct_0('#skF_3')) | ~l1_struct_0(A_135) | v2_struct_0(A_135))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_545])).
% 3.75/1.73  tff(c_555, plain, (![A_138]: (v7_waybel_0(k3_yellow19(A_138, k2_struct_0('#skF_3'), '#skF_4')) | ~m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(u1_struct_0(A_138))) | ~l1_struct_0(A_138) | v2_struct_0(A_138))), inference(negUnitSimplification, [status(thm)], [c_418, c_60, c_552])).
% 3.75/1.73  tff(c_558, plain, (v7_waybel_0(k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4')) | ~m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_111, c_555])).
% 3.75/1.73  tff(c_560, plain, (v7_waybel_0(k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4')) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_469, c_75, c_558])).
% 3.75/1.73  tff(c_561, plain, (v7_waybel_0(k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_66, c_560])).
% 3.75/1.73  tff(c_519, plain, (![A_131, B_132, C_133]: (l1_waybel_0(k3_yellow19(A_131, B_132, C_133), A_131) | ~m1_subset_1(C_133, k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_132)))) | ~v13_waybel_0(C_133, k3_yellow_1(B_132)) | ~v2_waybel_0(C_133, k3_yellow_1(B_132)) | v1_xboole_0(C_133) | ~m1_subset_1(B_132, k1_zfmisc_1(u1_struct_0(A_131))) | v1_xboole_0(B_132) | ~l1_struct_0(A_131) | v2_struct_0(A_131))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.75/1.73  tff(c_524, plain, (![A_131]: (l1_waybel_0(k3_yellow19(A_131, k2_struct_0('#skF_3'), '#skF_4'), A_131) | ~v13_waybel_0('#skF_4', k3_yellow_1(k2_struct_0('#skF_3'))) | ~v2_waybel_0('#skF_4', k3_yellow_1(k2_struct_0('#skF_3'))) | v1_xboole_0('#skF_4') | ~m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(u1_struct_0(A_131))) | v1_xboole_0(k2_struct_0('#skF_3')) | ~l1_struct_0(A_131) | v2_struct_0(A_131))), inference(resolution, [status(thm)], [c_52, c_519])).
% 3.75/1.73  tff(c_531, plain, (![A_131]: (l1_waybel_0(k3_yellow19(A_131, k2_struct_0('#skF_3'), '#skF_4'), A_131) | v1_xboole_0('#skF_4') | ~m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(u1_struct_0(A_131))) | v1_xboole_0(k2_struct_0('#skF_3')) | ~l1_struct_0(A_131) | v2_struct_0(A_131))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_524])).
% 3.75/1.73  tff(c_534, plain, (![A_134]: (l1_waybel_0(k3_yellow19(A_134, k2_struct_0('#skF_3'), '#skF_4'), A_134) | ~m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(u1_struct_0(A_134))) | ~l1_struct_0(A_134) | v2_struct_0(A_134))), inference(negUnitSimplification, [status(thm)], [c_418, c_60, c_531])).
% 3.75/1.73  tff(c_536, plain, (l1_waybel_0(k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4'), '#skF_3') | ~m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_111, c_534])).
% 3.75/1.73  tff(c_538, plain, (l1_waybel_0(k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4'), '#skF_3') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_469, c_75, c_536])).
% 3.75/1.73  tff(c_539, plain, (l1_waybel_0(k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_66, c_538])).
% 3.75/1.73  tff(c_562, plain, (![A_139, B_140]: (k2_yellow19(A_139, k3_yellow19(A_139, k2_struct_0(A_139), B_140))=B_140 | ~m1_subset_1(B_140, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_139))))) | ~v13_waybel_0(B_140, k3_yellow_1(k2_struct_0(A_139))) | ~v2_waybel_0(B_140, k3_yellow_1(k2_struct_0(A_139))) | ~v1_subset_1(B_140, u1_struct_0(k3_yellow_1(k2_struct_0(A_139)))) | v1_xboole_0(B_140) | ~l1_struct_0(A_139) | v2_struct_0(A_139))), inference(cnfTransformation, [status(thm)], [f_192])).
% 3.75/1.73  tff(c_567, plain, (k2_yellow19('#skF_3', k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4'))='#skF_4' | ~v13_waybel_0('#skF_4', k3_yellow_1(k2_struct_0('#skF_3'))) | ~v2_waybel_0('#skF_4', k3_yellow_1(k2_struct_0('#skF_3'))) | ~v1_subset_1('#skF_4', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3')))) | v1_xboole_0('#skF_4') | ~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_52, c_562])).
% 3.75/1.73  tff(c_574, plain, (k2_yellow19('#skF_3', k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4'))='#skF_4' | v1_xboole_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_469, c_58, c_56, c_54, c_567])).
% 3.75/1.73  tff(c_575, plain, (k2_yellow19('#skF_3', k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4'))='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_66, c_60, c_574])).
% 3.75/1.73  tff(c_580, plain, (![C_30]: (r2_hidden(C_30, k10_yellow_6('#skF_3', k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4'))) | ~r2_waybel_7('#skF_3', '#skF_4', C_30) | ~m1_subset_1(C_30, u1_struct_0('#skF_3')) | ~l1_waybel_0(k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4'), '#skF_3') | ~v7_waybel_0(k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4')) | ~v4_orders_2(k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4')) | v2_struct_0(k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_575, c_44])).
% 3.75/1.73  tff(c_587, plain, (![C_30]: (r2_hidden(C_30, k10_yellow_6('#skF_3', k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4'))) | ~r2_waybel_7('#skF_3', '#skF_4', C_30) | ~m1_subset_1(C_30, k2_struct_0('#skF_3')) | v2_struct_0(k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_468, c_561, c_539, c_111, c_580])).
% 3.75/1.73  tff(c_588, plain, (![C_30]: (r2_hidden(C_30, k10_yellow_6('#skF_3', k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4'))) | ~r2_waybel_7('#skF_3', '#skF_4', C_30) | ~m1_subset_1(C_30, k2_struct_0('#skF_3')) | v2_struct_0(k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_66, c_587])).
% 3.75/1.73  tff(c_593, plain, (v2_struct_0(k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4'))), inference(splitLeft, [status(thm)], [c_588])).
% 3.75/1.73  tff(c_595, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3'))))) | ~v13_waybel_0('#skF_4', k3_yellow_1(k2_struct_0('#skF_3'))) | ~v2_waybel_0('#skF_4', k3_yellow_1(k2_struct_0('#skF_3'))) | v1_xboole_0('#skF_4') | ~m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | v1_xboole_0(k2_struct_0('#skF_3')) | ~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_593, c_36])).
% 3.75/1.73  tff(c_598, plain, (v1_xboole_0('#skF_4') | v1_xboole_0(k2_struct_0('#skF_3')) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_469, c_75, c_111, c_56, c_54, c_52, c_595])).
% 3.75/1.73  tff(c_600, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_418, c_60, c_598])).
% 3.75/1.73  tff(c_602, plain, (~v2_struct_0(k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4'))), inference(splitRight, [status(thm)], [c_588])).
% 3.75/1.73  tff(c_46, plain, (![A_24, B_28, C_30]: (r2_waybel_7(A_24, k2_yellow19(A_24, B_28), C_30) | ~r2_hidden(C_30, k10_yellow_6(A_24, B_28)) | ~m1_subset_1(C_30, u1_struct_0(A_24)) | ~l1_waybel_0(B_28, A_24) | ~v7_waybel_0(B_28) | ~v4_orders_2(B_28) | v2_struct_0(B_28) | ~l1_pre_topc(A_24) | ~v2_pre_topc(A_24) | v2_struct_0(A_24))), inference(cnfTransformation, [status(thm)], [f_173])).
% 3.75/1.73  tff(c_583, plain, (![C_30]: (r2_waybel_7('#skF_3', '#skF_4', C_30) | ~r2_hidden(C_30, k10_yellow_6('#skF_3', k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4'))) | ~m1_subset_1(C_30, u1_struct_0('#skF_3')) | ~l1_waybel_0(k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4'), '#skF_3') | ~v7_waybel_0(k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4')) | ~v4_orders_2(k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4')) | v2_struct_0(k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_575, c_46])).
% 3.75/1.73  tff(c_590, plain, (![C_30]: (r2_waybel_7('#skF_3', '#skF_4', C_30) | ~r2_hidden(C_30, k10_yellow_6('#skF_3', k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4'))) | ~m1_subset_1(C_30, k2_struct_0('#skF_3')) | v2_struct_0(k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_468, c_561, c_539, c_111, c_583])).
% 3.75/1.73  tff(c_591, plain, (![C_30]: (r2_waybel_7('#skF_3', '#skF_4', C_30) | ~r2_hidden(C_30, k10_yellow_6('#skF_3', k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4'))) | ~m1_subset_1(C_30, k2_struct_0('#skF_3')) | v2_struct_0(k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_66, c_590])).
% 3.75/1.73  tff(c_610, plain, (![C_144]: (r2_waybel_7('#skF_3', '#skF_4', C_144) | ~r2_hidden(C_144, k10_yellow_6('#skF_3', k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4'))) | ~m1_subset_1(C_144, k2_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_602, c_591])).
% 3.75/1.73  tff(c_616, plain, (r2_waybel_7('#skF_3', '#skF_4', '#skF_5') | ~m1_subset_1('#skF_5', k2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_387, c_610])).
% 3.75/1.73  tff(c_624, plain, (r2_waybel_7('#skF_3', '#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_112, c_616])).
% 3.75/1.73  tff(c_626, plain, $false, inference(negUnitSimplification, [status(thm)], [c_388, c_624])).
% 3.75/1.73  tff(c_629, plain, (![A_145]: (~r2_hidden(A_145, '#skF_2'('#skF_3')))), inference(splitRight, [status(thm)], [c_417])).
% 3.75/1.73  tff(c_634, plain, (v1_xboole_0('#skF_2'('#skF_3'))), inference(resolution, [status(thm)], [c_4, c_629])).
% 3.75/1.73  tff(c_637, plain, (~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_634, c_18])).
% 3.75/1.73  tff(c_640, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_637])).
% 3.75/1.73  tff(c_642, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_640])).
% 3.75/1.73  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.75/1.73  
% 3.75/1.73  Inference rules
% 3.75/1.73  ----------------------
% 3.75/1.73  #Ref     : 0
% 3.75/1.73  #Sup     : 100
% 3.75/1.73  #Fact    : 0
% 3.75/1.73  #Define  : 0
% 3.75/1.73  #Split   : 10
% 3.75/1.73  #Chain   : 0
% 3.75/1.73  #Close   : 0
% 3.75/1.73  
% 3.75/1.73  Ordering : KBO
% 3.75/1.73  
% 3.75/1.73  Simplification rules
% 3.75/1.73  ----------------------
% 3.75/1.73  #Subsume      : 11
% 3.75/1.73  #Demod        : 112
% 3.75/1.73  #Tautology    : 19
% 3.75/1.73  #SimpNegUnit  : 38
% 3.75/1.73  #BackRed      : 1
% 3.75/1.73  
% 3.75/1.73  #Partial instantiations: 0
% 3.75/1.73  #Strategies tried      : 1
% 3.75/1.73  
% 3.75/1.73  Timing (in seconds)
% 3.75/1.73  ----------------------
% 3.75/1.73  Preprocessing        : 0.47
% 3.75/1.73  Parsing              : 0.28
% 3.75/1.73  CNF conversion       : 0.03
% 3.75/1.73  Main loop            : 0.40
% 3.75/1.73  Inferencing          : 0.15
% 3.75/1.73  Reduction            : 0.13
% 3.75/1.73  Demodulation         : 0.09
% 3.75/1.73  BG Simplification    : 0.03
% 3.75/1.73  Subsumption          : 0.07
% 3.75/1.73  Abstraction          : 0.02
% 3.75/1.73  MUC search           : 0.00
% 3.75/1.73  Cooper               : 0.00
% 3.75/1.73  Total                : 0.95
% 3.75/1.73  Index Insertion      : 0.00
% 3.75/1.73  Index Deletion       : 0.00
% 3.75/1.73  Index Matching       : 0.00
% 3.75/1.73  BG Taut test         : 0.00
%------------------------------------------------------------------------------
