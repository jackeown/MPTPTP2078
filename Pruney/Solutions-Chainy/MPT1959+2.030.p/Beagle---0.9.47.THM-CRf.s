%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:01 EST 2020

% Result     : Theorem 22.31s
% Output     : CNFRefutation 22.31s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 347 expanded)
%              Number of leaves         :   47 ( 141 expanded)
%              Depth                    :   17
%              Number of atoms          :  232 (1225 expanded)
%              Number of equality atoms :   22 (  92 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_lattice3 > r1_orders_2 > v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_yellow_0 > r2_hidden > r1_yellow_0 > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_yellow_0 > v1_xboole_0 > l1_orders_2 > k1_yellow_0 > #nlpp > u1_struct_0 > k3_yellow_0 > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_6 > #skF_4 > #skF_7 > #skF_8 > #skF_3 > #skF_2 > #skF_1 > #skF_5

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k1_yellow_0,type,(
    k1_yellow_0: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(v2_waybel_0,type,(
    v2_waybel_0: ( $i * $i ) > $o )).

tff(k3_yellow_0,type,(
    k3_yellow_0: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r2_lattice3,type,(
    r2_lattice3: ( $i * $i * $i ) > $o )).

tff(r2_yellow_0,type,(
    r2_yellow_0: ( $i * $i ) > $o )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(r1_yellow_0,type,(
    r1_yellow_0: ( $i * $i ) > $o )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v13_waybel_0,type,(
    v13_waybel_0: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(v1_yellow_0,type,(
    v1_yellow_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_180,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & v1_yellow_0(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( ( ~ v1_xboole_0(B)
              & v2_waybel_0(B,A)
              & v13_waybel_0(B,A)
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
           => ( v1_subset_1(B,u1_struct_0(A))
            <=> ~ r2_hidden(k3_yellow_0(A),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_waybel_7)).

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( ! [C] :
            ( m1_subset_1(C,A)
           => r2_hidden(C,B) )
       => A = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_subset_1)).

tff(f_86,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B,C] :
          ( m1_subset_1(C,u1_struct_0(A))
         => ( r2_lattice3(A,B,C)
          <=> ! [D] :
                ( m1_subset_1(D,u1_struct_0(A))
               => ( r2_hidden(D,B)
                 => r1_orders_2(A,D,C) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_lattice3)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_28,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ~ ( B != k1_xboole_0
          & ! [C] :
              ( m1_subset_1(C,A)
             => ~ r2_hidden(C,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_subset_1)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_59,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_151,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( v1_subset_1(B,A)
      <=> B != A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).

tff(f_90,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => k3_yellow_0(A) = k1_yellow_0(A,k1_xboole_0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_yellow_0)).

tff(f_112,axiom,(
    ! [A,B] :
      ( l1_orders_2(A)
     => m1_subset_1(k1_yellow_0(A,B),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_yellow_0)).

tff(f_125,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v5_orders_2(A)
        & v1_yellow_0(A)
        & l1_orders_2(A) )
     => ( r1_yellow_0(A,k1_xboole_0)
        & r2_yellow_0(A,u1_struct_0(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_yellow_0)).

tff(f_108,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B,C] :
          ( m1_subset_1(C,u1_struct_0(A))
         => ( r1_yellow_0(A,B)
           => ( C = k1_yellow_0(A,B)
            <=> ( r2_lattice3(A,B,C)
                & ! [D] :
                    ( m1_subset_1(D,u1_struct_0(A))
                   => ( r2_lattice3(A,B,D)
                     => r1_orders_2(A,C,D) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_yellow_0)).

tff(f_144,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v13_waybel_0(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => ! [D] :
                    ( m1_subset_1(D,u1_struct_0(A))
                   => ( ( r2_hidden(C,B)
                        & r1_orders_2(A,C,D) )
                     => r2_hidden(D,B) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d20_waybel_0)).

tff(c_64,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(u1_struct_0('#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_72,plain,(
    l1_orders_2('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_12,plain,(
    ! [A_5,B_6] :
      ( m1_subset_1('#skF_2'(A_5,B_6),A_5)
      | B_6 = A_5
      | ~ m1_subset_1(B_6,k1_zfmisc_1(A_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_705,plain,(
    ! [A_140,B_141,C_142] :
      ( r2_hidden('#skF_3'(A_140,B_141,C_142),B_141)
      | r2_lattice3(A_140,B_141,C_142)
      | ~ m1_subset_1(C_142,u1_struct_0(A_140))
      | ~ l1_orders_2(A_140) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_4,plain,(
    ! [A_1] : m1_subset_1(k2_subset_1(A_1),k1_zfmisc_1(A_1)) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_235,plain,(
    ! [A_110,B_111] :
      ( r2_hidden('#skF_1'(A_110,B_111),B_111)
      | k1_xboole_0 = B_111
      | ~ m1_subset_1(B_111,k1_zfmisc_1(A_110)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_181,plain,(
    ! [C_93,B_94,A_95] :
      ( ~ v1_xboole_0(C_93)
      | ~ m1_subset_1(B_94,k1_zfmisc_1(C_93))
      | ~ r2_hidden(A_95,B_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_186,plain,(
    ! [A_1,A_95] :
      ( ~ v1_xboole_0(A_1)
      | ~ r2_hidden(A_95,k2_subset_1(A_1)) ) ),
    inference(resolution,[status(thm)],[c_4,c_181])).

tff(c_250,plain,(
    ! [A_112,A_113] :
      ( ~ v1_xboole_0(A_112)
      | k2_subset_1(A_112) = k1_xboole_0
      | ~ m1_subset_1(k2_subset_1(A_112),k1_zfmisc_1(A_113)) ) ),
    inference(resolution,[status(thm)],[c_235,c_186])).

tff(c_255,plain,(
    ! [A_114] :
      ( ~ v1_xboole_0(A_114)
      | k2_subset_1(A_114) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_250])).

tff(c_259,plain,(
    k2_subset_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_255])).

tff(c_272,plain,(
    ! [A_95] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(A_95,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_259,c_186])).

tff(c_285,plain,(
    ! [A_95] : ~ r2_hidden(A_95,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_272])).

tff(c_753,plain,(
    ! [A_145,C_146] :
      ( r2_lattice3(A_145,k1_xboole_0,C_146)
      | ~ m1_subset_1(C_146,u1_struct_0(A_145))
      | ~ l1_orders_2(A_145) ) ),
    inference(resolution,[status(thm)],[c_705,c_285])).

tff(c_784,plain,(
    ! [A_145,B_6] :
      ( r2_lattice3(A_145,k1_xboole_0,'#skF_2'(u1_struct_0(A_145),B_6))
      | ~ l1_orders_2(A_145)
      | u1_struct_0(A_145) = B_6
      | ~ m1_subset_1(B_6,k1_zfmisc_1(u1_struct_0(A_145))) ) ),
    inference(resolution,[status(thm)],[c_12,c_753])).

tff(c_66,plain,(
    v13_waybel_0('#skF_8','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_90,plain,
    ( v1_subset_1('#skF_8',u1_struct_0('#skF_7'))
    | ~ r2_hidden(k3_yellow_0('#skF_7'),'#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_109,plain,(
    ~ r2_hidden(k3_yellow_0('#skF_7'),'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_90])).

tff(c_70,plain,(
    ~ v1_xboole_0('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_111,plain,(
    ! [A_81,B_82] :
      ( r2_hidden(A_81,B_82)
      | v1_xboole_0(B_82)
      | ~ m1_subset_1(A_81,B_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_114,plain,
    ( v1_xboole_0('#skF_8')
    | ~ m1_subset_1(k3_yellow_0('#skF_7'),'#skF_8') ),
    inference(resolution,[status(thm)],[c_111,c_109])).

tff(c_120,plain,(
    ~ m1_subset_1(k3_yellow_0('#skF_7'),'#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_114])).

tff(c_84,plain,
    ( r2_hidden(k3_yellow_0('#skF_7'),'#skF_8')
    | ~ v1_subset_1('#skF_8',u1_struct_0('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_110,plain,(
    ~ v1_subset_1('#skF_8',u1_struct_0('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_84])).

tff(c_129,plain,(
    ! [B_86,A_87] :
      ( v1_subset_1(B_86,A_87)
      | B_86 = A_87
      | ~ m1_subset_1(B_86,k1_zfmisc_1(A_87)) ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_135,plain,
    ( v1_subset_1('#skF_8',u1_struct_0('#skF_7'))
    | u1_struct_0('#skF_7') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_64,c_129])).

tff(c_139,plain,(
    u1_struct_0('#skF_7') = '#skF_8' ),
    inference(negUnitSimplification,[status(thm)],[c_110,c_135])).

tff(c_94,plain,(
    ! [A_78] :
      ( k1_yellow_0(A_78,k1_xboole_0) = k3_yellow_0(A_78)
      | ~ l1_orders_2(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_98,plain,(
    k1_yellow_0('#skF_7',k1_xboole_0) = k3_yellow_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_72,c_94])).

tff(c_42,plain,(
    ! [A_43,B_44] :
      ( m1_subset_1(k1_yellow_0(A_43,B_44),u1_struct_0(A_43))
      | ~ l1_orders_2(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_103,plain,
    ( m1_subset_1(k3_yellow_0('#skF_7'),u1_struct_0('#skF_7'))
    | ~ l1_orders_2('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_98,c_42])).

tff(c_107,plain,(
    m1_subset_1(k3_yellow_0('#skF_7'),u1_struct_0('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_103])).

tff(c_141,plain,(
    m1_subset_1(k3_yellow_0('#skF_7'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_107])).

tff(c_144,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_120,c_141])).

tff(c_145,plain,(
    r2_hidden(k3_yellow_0('#skF_7'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_147,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_109,c_145])).

tff(c_149,plain,(
    r2_hidden(k3_yellow_0('#skF_7'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_90])).

tff(c_82,plain,(
    ~ v2_struct_0('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_76,plain,(
    v5_orders_2('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_74,plain,(
    v1_yellow_0('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_46,plain,(
    ! [A_45] :
      ( r1_yellow_0(A_45,k1_xboole_0)
      | ~ l1_orders_2(A_45)
      | ~ v1_yellow_0(A_45)
      | ~ v5_orders_2(A_45)
      | v2_struct_0(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_2340,plain,(
    ! [A_247,B_248,D_249] :
      ( r1_orders_2(A_247,k1_yellow_0(A_247,B_248),D_249)
      | ~ r2_lattice3(A_247,B_248,D_249)
      | ~ m1_subset_1(D_249,u1_struct_0(A_247))
      | ~ r1_yellow_0(A_247,B_248)
      | ~ m1_subset_1(k1_yellow_0(A_247,B_248),u1_struct_0(A_247))
      | ~ l1_orders_2(A_247) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_2345,plain,(
    ! [D_249] :
      ( r1_orders_2('#skF_7',k1_yellow_0('#skF_7',k1_xboole_0),D_249)
      | ~ r2_lattice3('#skF_7',k1_xboole_0,D_249)
      | ~ m1_subset_1(D_249,u1_struct_0('#skF_7'))
      | ~ r1_yellow_0('#skF_7',k1_xboole_0)
      | ~ m1_subset_1(k3_yellow_0('#skF_7'),u1_struct_0('#skF_7'))
      | ~ l1_orders_2('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_98,c_2340])).

tff(c_2352,plain,(
    ! [D_249] :
      ( r1_orders_2('#skF_7',k3_yellow_0('#skF_7'),D_249)
      | ~ r2_lattice3('#skF_7',k1_xboole_0,D_249)
      | ~ m1_subset_1(D_249,u1_struct_0('#skF_7'))
      | ~ r1_yellow_0('#skF_7',k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_107,c_98,c_2345])).

tff(c_2354,plain,(
    ~ r1_yellow_0('#skF_7',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_2352])).

tff(c_2357,plain,
    ( ~ l1_orders_2('#skF_7')
    | ~ v1_yellow_0('#skF_7')
    | ~ v5_orders_2('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_46,c_2354])).

tff(c_2360,plain,(
    v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_72,c_2357])).

tff(c_2362,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_2360])).

tff(c_2364,plain,(
    r1_yellow_0('#skF_7',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_2352])).

tff(c_3340,plain,(
    ! [A_286,B_287,D_288] :
      ( r1_orders_2(A_286,k1_yellow_0(A_286,B_287),D_288)
      | ~ r2_lattice3(A_286,B_287,D_288)
      | ~ m1_subset_1(D_288,u1_struct_0(A_286))
      | ~ r1_yellow_0(A_286,B_287)
      | ~ l1_orders_2(A_286) ) ),
    inference(resolution,[status(thm)],[c_42,c_2340])).

tff(c_48,plain,(
    ! [D_69,B_60,A_46,C_67] :
      ( r2_hidden(D_69,B_60)
      | ~ r1_orders_2(A_46,C_67,D_69)
      | ~ r2_hidden(C_67,B_60)
      | ~ m1_subset_1(D_69,u1_struct_0(A_46))
      | ~ m1_subset_1(C_67,u1_struct_0(A_46))
      | ~ v13_waybel_0(B_60,A_46)
      | ~ m1_subset_1(B_60,k1_zfmisc_1(u1_struct_0(A_46)))
      | ~ l1_orders_2(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_49676,plain,(
    ! [D_775,B_776,A_777,B_778] :
      ( r2_hidden(D_775,B_776)
      | ~ r2_hidden(k1_yellow_0(A_777,B_778),B_776)
      | ~ m1_subset_1(k1_yellow_0(A_777,B_778),u1_struct_0(A_777))
      | ~ v13_waybel_0(B_776,A_777)
      | ~ m1_subset_1(B_776,k1_zfmisc_1(u1_struct_0(A_777)))
      | ~ r2_lattice3(A_777,B_778,D_775)
      | ~ m1_subset_1(D_775,u1_struct_0(A_777))
      | ~ r1_yellow_0(A_777,B_778)
      | ~ l1_orders_2(A_777) ) ),
    inference(resolution,[status(thm)],[c_3340,c_48])).

tff(c_49687,plain,(
    ! [D_775,B_776] :
      ( r2_hidden(D_775,B_776)
      | ~ r2_hidden(k3_yellow_0('#skF_7'),B_776)
      | ~ m1_subset_1(k1_yellow_0('#skF_7',k1_xboole_0),u1_struct_0('#skF_7'))
      | ~ v13_waybel_0(B_776,'#skF_7')
      | ~ m1_subset_1(B_776,k1_zfmisc_1(u1_struct_0('#skF_7')))
      | ~ r2_lattice3('#skF_7',k1_xboole_0,D_775)
      | ~ m1_subset_1(D_775,u1_struct_0('#skF_7'))
      | ~ r1_yellow_0('#skF_7',k1_xboole_0)
      | ~ l1_orders_2('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_98,c_49676])).

tff(c_49793,plain,(
    ! [D_785,B_786] :
      ( r2_hidden(D_785,B_786)
      | ~ r2_hidden(k3_yellow_0('#skF_7'),B_786)
      | ~ v13_waybel_0(B_786,'#skF_7')
      | ~ m1_subset_1(B_786,k1_zfmisc_1(u1_struct_0('#skF_7')))
      | ~ r2_lattice3('#skF_7',k1_xboole_0,D_785)
      | ~ m1_subset_1(D_785,u1_struct_0('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_2364,c_107,c_98,c_49687])).

tff(c_49851,plain,(
    ! [D_785] :
      ( r2_hidden(D_785,'#skF_8')
      | ~ r2_hidden(k3_yellow_0('#skF_7'),'#skF_8')
      | ~ v13_waybel_0('#skF_8','#skF_7')
      | ~ r2_lattice3('#skF_7',k1_xboole_0,D_785)
      | ~ m1_subset_1(D_785,u1_struct_0('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_64,c_49793])).

tff(c_49896,plain,(
    ! [D_787] :
      ( r2_hidden(D_787,'#skF_8')
      | ~ r2_lattice3('#skF_7',k1_xboole_0,D_787)
      | ~ m1_subset_1(D_787,u1_struct_0('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_149,c_49851])).

tff(c_50711,plain,(
    ! [B_807] :
      ( r2_hidden('#skF_2'(u1_struct_0('#skF_7'),B_807),'#skF_8')
      | ~ r2_lattice3('#skF_7',k1_xboole_0,'#skF_2'(u1_struct_0('#skF_7'),B_807))
      | u1_struct_0('#skF_7') = B_807
      | ~ m1_subset_1(B_807,k1_zfmisc_1(u1_struct_0('#skF_7'))) ) ),
    inference(resolution,[status(thm)],[c_12,c_49896])).

tff(c_50736,plain,(
    ! [B_6] :
      ( r2_hidden('#skF_2'(u1_struct_0('#skF_7'),B_6),'#skF_8')
      | ~ l1_orders_2('#skF_7')
      | u1_struct_0('#skF_7') = B_6
      | ~ m1_subset_1(B_6,k1_zfmisc_1(u1_struct_0('#skF_7'))) ) ),
    inference(resolution,[status(thm)],[c_784,c_50711])).

tff(c_50772,plain,(
    ! [B_808] :
      ( r2_hidden('#skF_2'(u1_struct_0('#skF_7'),B_808),'#skF_8')
      | u1_struct_0('#skF_7') = B_808
      | ~ m1_subset_1(B_808,k1_zfmisc_1(u1_struct_0('#skF_7'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_50736])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( ~ r2_hidden('#skF_2'(A_5,B_6),B_6)
      | B_6 = A_5
      | ~ m1_subset_1(B_6,k1_zfmisc_1(A_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_50786,plain,
    ( u1_struct_0('#skF_7') = '#skF_8'
    | ~ m1_subset_1('#skF_8',k1_zfmisc_1(u1_struct_0('#skF_7'))) ),
    inference(resolution,[status(thm)],[c_50772,c_10])).

tff(c_50797,plain,(
    u1_struct_0('#skF_7') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_50786])).

tff(c_148,plain,(
    v1_subset_1('#skF_8',u1_struct_0('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_90])).

tff(c_50850,plain,(
    v1_subset_1('#skF_8','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50797,c_148])).

tff(c_50852,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50797,c_64])).

tff(c_62,plain,(
    ! [B_72] :
      ( ~ v1_subset_1(B_72,B_72)
      | ~ m1_subset_1(B_72,k1_zfmisc_1(B_72)) ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_51989,plain,(
    ~ v1_subset_1('#skF_8','#skF_8') ),
    inference(resolution,[status(thm)],[c_50852,c_62])).

tff(c_51998,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50850,c_51989])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:11:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 22.31/12.43  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 22.31/12.44  
% 22.31/12.44  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 22.31/12.44  %$ r2_lattice3 > r1_orders_2 > v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_yellow_0 > r2_hidden > r1_yellow_0 > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_yellow_0 > v1_xboole_0 > l1_orders_2 > k1_yellow_0 > #nlpp > u1_struct_0 > k3_yellow_0 > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_6 > #skF_4 > #skF_7 > #skF_8 > #skF_3 > #skF_2 > #skF_1 > #skF_5
% 22.31/12.44  
% 22.31/12.44  %Foreground sorts:
% 22.31/12.44  
% 22.31/12.44  
% 22.31/12.44  %Background operators:
% 22.31/12.44  
% 22.31/12.44  
% 22.31/12.44  %Foreground operators:
% 22.31/12.44  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 22.31/12.44  tff(k1_yellow_0, type, k1_yellow_0: ($i * $i) > $i).
% 22.31/12.44  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 22.31/12.44  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 22.31/12.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 22.31/12.44  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 22.31/12.44  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 22.31/12.44  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 22.31/12.44  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 22.31/12.44  tff(v2_waybel_0, type, v2_waybel_0: ($i * $i) > $o).
% 22.31/12.44  tff(k3_yellow_0, type, k3_yellow_0: $i > $i).
% 22.31/12.44  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 22.31/12.44  tff('#skF_7', type, '#skF_7': $i).
% 22.31/12.44  tff(r2_lattice3, type, r2_lattice3: ($i * $i * $i) > $o).
% 22.31/12.44  tff(r2_yellow_0, type, r2_yellow_0: ($i * $i) > $o).
% 22.31/12.44  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 22.31/12.44  tff(r1_yellow_0, type, r1_yellow_0: ($i * $i) > $o).
% 22.31/12.44  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 22.31/12.44  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 22.31/12.44  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 22.31/12.44  tff('#skF_8', type, '#skF_8': $i).
% 22.31/12.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 22.31/12.44  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 22.31/12.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 22.31/12.44  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 22.31/12.44  tff(v13_waybel_0, type, v13_waybel_0: ($i * $i) > $o).
% 22.31/12.44  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 22.31/12.44  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 22.31/12.44  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 22.31/12.44  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 22.31/12.44  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 22.31/12.44  tff(v1_yellow_0, type, v1_yellow_0: $i > $o).
% 22.31/12.44  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 22.31/12.44  
% 22.31/12.46  tff(f_180, negated_conjecture, ~(![A]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & v1_yellow_0(A)) & l1_orders_2(A)) => (![B]: ((((~v1_xboole_0(B) & v2_waybel_0(B, A)) & v13_waybel_0(B, A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v1_subset_1(B, u1_struct_0(A)) <=> ~r2_hidden(k3_yellow_0(A), B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_waybel_7)).
% 22.31/12.46  tff(f_49, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => ((![C]: (m1_subset_1(C, A) => r2_hidden(C, B))) => (A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_subset_1)).
% 22.31/12.46  tff(f_86, axiom, (![A]: (l1_orders_2(A) => (![B, C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_lattice3(A, B, C) <=> (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_hidden(D, B) => r1_orders_2(A, D, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_lattice3)).
% 22.31/12.46  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 22.31/12.46  tff(f_28, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 22.31/12.46  tff(f_40, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => ~(~(B = k1_xboole_0) & (![C]: (m1_subset_1(C, A) => ~r2_hidden(C, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_subset_1)).
% 22.31/12.46  tff(f_72, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 22.31/12.46  tff(f_59, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 22.31/12.46  tff(f_151, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (v1_subset_1(B, A) <=> ~(B = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_subset_1)).
% 22.31/12.46  tff(f_90, axiom, (![A]: (l1_orders_2(A) => (k3_yellow_0(A) = k1_yellow_0(A, k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d11_yellow_0)).
% 22.31/12.46  tff(f_112, axiom, (![A, B]: (l1_orders_2(A) => m1_subset_1(k1_yellow_0(A, B), u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_yellow_0)).
% 22.31/12.46  tff(f_125, axiom, (![A]: ((((~v2_struct_0(A) & v5_orders_2(A)) & v1_yellow_0(A)) & l1_orders_2(A)) => (r1_yellow_0(A, k1_xboole_0) & r2_yellow_0(A, u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_yellow_0)).
% 22.31/12.46  tff(f_108, axiom, (![A]: (l1_orders_2(A) => (![B, C]: (m1_subset_1(C, u1_struct_0(A)) => (r1_yellow_0(A, B) => ((C = k1_yellow_0(A, B)) <=> (r2_lattice3(A, B, C) & (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_lattice3(A, B, D) => r1_orders_2(A, C, D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_yellow_0)).
% 22.31/12.46  tff(f_144, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v13_waybel_0(B, A) <=> (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => ((r2_hidden(C, B) & r1_orders_2(A, C, D)) => r2_hidden(D, B))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d20_waybel_0)).
% 22.31/12.46  tff(c_64, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(u1_struct_0('#skF_7')))), inference(cnfTransformation, [status(thm)], [f_180])).
% 22.31/12.46  tff(c_72, plain, (l1_orders_2('#skF_7')), inference(cnfTransformation, [status(thm)], [f_180])).
% 22.31/12.46  tff(c_12, plain, (![A_5, B_6]: (m1_subset_1('#skF_2'(A_5, B_6), A_5) | B_6=A_5 | ~m1_subset_1(B_6, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 22.31/12.46  tff(c_705, plain, (![A_140, B_141, C_142]: (r2_hidden('#skF_3'(A_140, B_141, C_142), B_141) | r2_lattice3(A_140, B_141, C_142) | ~m1_subset_1(C_142, u1_struct_0(A_140)) | ~l1_orders_2(A_140))), inference(cnfTransformation, [status(thm)], [f_86])).
% 22.31/12.46  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 22.31/12.46  tff(c_4, plain, (![A_1]: (m1_subset_1(k2_subset_1(A_1), k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_28])).
% 22.31/12.46  tff(c_235, plain, (![A_110, B_111]: (r2_hidden('#skF_1'(A_110, B_111), B_111) | k1_xboole_0=B_111 | ~m1_subset_1(B_111, k1_zfmisc_1(A_110)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 22.31/12.46  tff(c_181, plain, (![C_93, B_94, A_95]: (~v1_xboole_0(C_93) | ~m1_subset_1(B_94, k1_zfmisc_1(C_93)) | ~r2_hidden(A_95, B_94))), inference(cnfTransformation, [status(thm)], [f_72])).
% 22.31/12.46  tff(c_186, plain, (![A_1, A_95]: (~v1_xboole_0(A_1) | ~r2_hidden(A_95, k2_subset_1(A_1)))), inference(resolution, [status(thm)], [c_4, c_181])).
% 22.31/12.46  tff(c_250, plain, (![A_112, A_113]: (~v1_xboole_0(A_112) | k2_subset_1(A_112)=k1_xboole_0 | ~m1_subset_1(k2_subset_1(A_112), k1_zfmisc_1(A_113)))), inference(resolution, [status(thm)], [c_235, c_186])).
% 22.31/12.46  tff(c_255, plain, (![A_114]: (~v1_xboole_0(A_114) | k2_subset_1(A_114)=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_250])).
% 22.31/12.46  tff(c_259, plain, (k2_subset_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_2, c_255])).
% 22.31/12.46  tff(c_272, plain, (![A_95]: (~v1_xboole_0(k1_xboole_0) | ~r2_hidden(A_95, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_259, c_186])).
% 22.31/12.46  tff(c_285, plain, (![A_95]: (~r2_hidden(A_95, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_272])).
% 22.31/12.46  tff(c_753, plain, (![A_145, C_146]: (r2_lattice3(A_145, k1_xboole_0, C_146) | ~m1_subset_1(C_146, u1_struct_0(A_145)) | ~l1_orders_2(A_145))), inference(resolution, [status(thm)], [c_705, c_285])).
% 22.31/12.46  tff(c_784, plain, (![A_145, B_6]: (r2_lattice3(A_145, k1_xboole_0, '#skF_2'(u1_struct_0(A_145), B_6)) | ~l1_orders_2(A_145) | u1_struct_0(A_145)=B_6 | ~m1_subset_1(B_6, k1_zfmisc_1(u1_struct_0(A_145))))), inference(resolution, [status(thm)], [c_12, c_753])).
% 22.31/12.46  tff(c_66, plain, (v13_waybel_0('#skF_8', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_180])).
% 22.31/12.46  tff(c_90, plain, (v1_subset_1('#skF_8', u1_struct_0('#skF_7')) | ~r2_hidden(k3_yellow_0('#skF_7'), '#skF_8')), inference(cnfTransformation, [status(thm)], [f_180])).
% 22.31/12.46  tff(c_109, plain, (~r2_hidden(k3_yellow_0('#skF_7'), '#skF_8')), inference(splitLeft, [status(thm)], [c_90])).
% 22.31/12.46  tff(c_70, plain, (~v1_xboole_0('#skF_8')), inference(cnfTransformation, [status(thm)], [f_180])).
% 22.31/12.46  tff(c_111, plain, (![A_81, B_82]: (r2_hidden(A_81, B_82) | v1_xboole_0(B_82) | ~m1_subset_1(A_81, B_82))), inference(cnfTransformation, [status(thm)], [f_59])).
% 22.31/12.46  tff(c_114, plain, (v1_xboole_0('#skF_8') | ~m1_subset_1(k3_yellow_0('#skF_7'), '#skF_8')), inference(resolution, [status(thm)], [c_111, c_109])).
% 22.31/12.46  tff(c_120, plain, (~m1_subset_1(k3_yellow_0('#skF_7'), '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_70, c_114])).
% 22.31/12.46  tff(c_84, plain, (r2_hidden(k3_yellow_0('#skF_7'), '#skF_8') | ~v1_subset_1('#skF_8', u1_struct_0('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_180])).
% 22.31/12.46  tff(c_110, plain, (~v1_subset_1('#skF_8', u1_struct_0('#skF_7'))), inference(splitLeft, [status(thm)], [c_84])).
% 22.31/12.46  tff(c_129, plain, (![B_86, A_87]: (v1_subset_1(B_86, A_87) | B_86=A_87 | ~m1_subset_1(B_86, k1_zfmisc_1(A_87)))), inference(cnfTransformation, [status(thm)], [f_151])).
% 22.31/12.46  tff(c_135, plain, (v1_subset_1('#skF_8', u1_struct_0('#skF_7')) | u1_struct_0('#skF_7')='#skF_8'), inference(resolution, [status(thm)], [c_64, c_129])).
% 22.31/12.46  tff(c_139, plain, (u1_struct_0('#skF_7')='#skF_8'), inference(negUnitSimplification, [status(thm)], [c_110, c_135])).
% 22.31/12.46  tff(c_94, plain, (![A_78]: (k1_yellow_0(A_78, k1_xboole_0)=k3_yellow_0(A_78) | ~l1_orders_2(A_78))), inference(cnfTransformation, [status(thm)], [f_90])).
% 22.31/12.46  tff(c_98, plain, (k1_yellow_0('#skF_7', k1_xboole_0)=k3_yellow_0('#skF_7')), inference(resolution, [status(thm)], [c_72, c_94])).
% 22.31/12.46  tff(c_42, plain, (![A_43, B_44]: (m1_subset_1(k1_yellow_0(A_43, B_44), u1_struct_0(A_43)) | ~l1_orders_2(A_43))), inference(cnfTransformation, [status(thm)], [f_112])).
% 22.31/12.46  tff(c_103, plain, (m1_subset_1(k3_yellow_0('#skF_7'), u1_struct_0('#skF_7')) | ~l1_orders_2('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_98, c_42])).
% 22.31/12.46  tff(c_107, plain, (m1_subset_1(k3_yellow_0('#skF_7'), u1_struct_0('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_103])).
% 22.31/12.46  tff(c_141, plain, (m1_subset_1(k3_yellow_0('#skF_7'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_139, c_107])).
% 22.31/12.46  tff(c_144, plain, $false, inference(negUnitSimplification, [status(thm)], [c_120, c_141])).
% 22.31/12.46  tff(c_145, plain, (r2_hidden(k3_yellow_0('#skF_7'), '#skF_8')), inference(splitRight, [status(thm)], [c_84])).
% 22.31/12.46  tff(c_147, plain, $false, inference(negUnitSimplification, [status(thm)], [c_109, c_145])).
% 22.31/12.46  tff(c_149, plain, (r2_hidden(k3_yellow_0('#skF_7'), '#skF_8')), inference(splitRight, [status(thm)], [c_90])).
% 22.31/12.46  tff(c_82, plain, (~v2_struct_0('#skF_7')), inference(cnfTransformation, [status(thm)], [f_180])).
% 22.31/12.46  tff(c_76, plain, (v5_orders_2('#skF_7')), inference(cnfTransformation, [status(thm)], [f_180])).
% 22.31/12.46  tff(c_74, plain, (v1_yellow_0('#skF_7')), inference(cnfTransformation, [status(thm)], [f_180])).
% 22.31/12.46  tff(c_46, plain, (![A_45]: (r1_yellow_0(A_45, k1_xboole_0) | ~l1_orders_2(A_45) | ~v1_yellow_0(A_45) | ~v5_orders_2(A_45) | v2_struct_0(A_45))), inference(cnfTransformation, [status(thm)], [f_125])).
% 22.31/12.46  tff(c_2340, plain, (![A_247, B_248, D_249]: (r1_orders_2(A_247, k1_yellow_0(A_247, B_248), D_249) | ~r2_lattice3(A_247, B_248, D_249) | ~m1_subset_1(D_249, u1_struct_0(A_247)) | ~r1_yellow_0(A_247, B_248) | ~m1_subset_1(k1_yellow_0(A_247, B_248), u1_struct_0(A_247)) | ~l1_orders_2(A_247))), inference(cnfTransformation, [status(thm)], [f_108])).
% 22.31/12.46  tff(c_2345, plain, (![D_249]: (r1_orders_2('#skF_7', k1_yellow_0('#skF_7', k1_xboole_0), D_249) | ~r2_lattice3('#skF_7', k1_xboole_0, D_249) | ~m1_subset_1(D_249, u1_struct_0('#skF_7')) | ~r1_yellow_0('#skF_7', k1_xboole_0) | ~m1_subset_1(k3_yellow_0('#skF_7'), u1_struct_0('#skF_7')) | ~l1_orders_2('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_98, c_2340])).
% 22.31/12.46  tff(c_2352, plain, (![D_249]: (r1_orders_2('#skF_7', k3_yellow_0('#skF_7'), D_249) | ~r2_lattice3('#skF_7', k1_xboole_0, D_249) | ~m1_subset_1(D_249, u1_struct_0('#skF_7')) | ~r1_yellow_0('#skF_7', k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_107, c_98, c_2345])).
% 22.31/12.46  tff(c_2354, plain, (~r1_yellow_0('#skF_7', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_2352])).
% 22.31/12.46  tff(c_2357, plain, (~l1_orders_2('#skF_7') | ~v1_yellow_0('#skF_7') | ~v5_orders_2('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_46, c_2354])).
% 22.31/12.46  tff(c_2360, plain, (v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_72, c_2357])).
% 22.31/12.46  tff(c_2362, plain, $false, inference(negUnitSimplification, [status(thm)], [c_82, c_2360])).
% 22.31/12.46  tff(c_2364, plain, (r1_yellow_0('#skF_7', k1_xboole_0)), inference(splitRight, [status(thm)], [c_2352])).
% 22.31/12.46  tff(c_3340, plain, (![A_286, B_287, D_288]: (r1_orders_2(A_286, k1_yellow_0(A_286, B_287), D_288) | ~r2_lattice3(A_286, B_287, D_288) | ~m1_subset_1(D_288, u1_struct_0(A_286)) | ~r1_yellow_0(A_286, B_287) | ~l1_orders_2(A_286))), inference(resolution, [status(thm)], [c_42, c_2340])).
% 22.31/12.46  tff(c_48, plain, (![D_69, B_60, A_46, C_67]: (r2_hidden(D_69, B_60) | ~r1_orders_2(A_46, C_67, D_69) | ~r2_hidden(C_67, B_60) | ~m1_subset_1(D_69, u1_struct_0(A_46)) | ~m1_subset_1(C_67, u1_struct_0(A_46)) | ~v13_waybel_0(B_60, A_46) | ~m1_subset_1(B_60, k1_zfmisc_1(u1_struct_0(A_46))) | ~l1_orders_2(A_46))), inference(cnfTransformation, [status(thm)], [f_144])).
% 22.31/12.46  tff(c_49676, plain, (![D_775, B_776, A_777, B_778]: (r2_hidden(D_775, B_776) | ~r2_hidden(k1_yellow_0(A_777, B_778), B_776) | ~m1_subset_1(k1_yellow_0(A_777, B_778), u1_struct_0(A_777)) | ~v13_waybel_0(B_776, A_777) | ~m1_subset_1(B_776, k1_zfmisc_1(u1_struct_0(A_777))) | ~r2_lattice3(A_777, B_778, D_775) | ~m1_subset_1(D_775, u1_struct_0(A_777)) | ~r1_yellow_0(A_777, B_778) | ~l1_orders_2(A_777))), inference(resolution, [status(thm)], [c_3340, c_48])).
% 22.31/12.46  tff(c_49687, plain, (![D_775, B_776]: (r2_hidden(D_775, B_776) | ~r2_hidden(k3_yellow_0('#skF_7'), B_776) | ~m1_subset_1(k1_yellow_0('#skF_7', k1_xboole_0), u1_struct_0('#skF_7')) | ~v13_waybel_0(B_776, '#skF_7') | ~m1_subset_1(B_776, k1_zfmisc_1(u1_struct_0('#skF_7'))) | ~r2_lattice3('#skF_7', k1_xboole_0, D_775) | ~m1_subset_1(D_775, u1_struct_0('#skF_7')) | ~r1_yellow_0('#skF_7', k1_xboole_0) | ~l1_orders_2('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_98, c_49676])).
% 22.31/12.46  tff(c_49793, plain, (![D_785, B_786]: (r2_hidden(D_785, B_786) | ~r2_hidden(k3_yellow_0('#skF_7'), B_786) | ~v13_waybel_0(B_786, '#skF_7') | ~m1_subset_1(B_786, k1_zfmisc_1(u1_struct_0('#skF_7'))) | ~r2_lattice3('#skF_7', k1_xboole_0, D_785) | ~m1_subset_1(D_785, u1_struct_0('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_2364, c_107, c_98, c_49687])).
% 22.31/12.46  tff(c_49851, plain, (![D_785]: (r2_hidden(D_785, '#skF_8') | ~r2_hidden(k3_yellow_0('#skF_7'), '#skF_8') | ~v13_waybel_0('#skF_8', '#skF_7') | ~r2_lattice3('#skF_7', k1_xboole_0, D_785) | ~m1_subset_1(D_785, u1_struct_0('#skF_7')))), inference(resolution, [status(thm)], [c_64, c_49793])).
% 22.31/12.46  tff(c_49896, plain, (![D_787]: (r2_hidden(D_787, '#skF_8') | ~r2_lattice3('#skF_7', k1_xboole_0, D_787) | ~m1_subset_1(D_787, u1_struct_0('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_149, c_49851])).
% 22.31/12.46  tff(c_50711, plain, (![B_807]: (r2_hidden('#skF_2'(u1_struct_0('#skF_7'), B_807), '#skF_8') | ~r2_lattice3('#skF_7', k1_xboole_0, '#skF_2'(u1_struct_0('#skF_7'), B_807)) | u1_struct_0('#skF_7')=B_807 | ~m1_subset_1(B_807, k1_zfmisc_1(u1_struct_0('#skF_7'))))), inference(resolution, [status(thm)], [c_12, c_49896])).
% 22.31/12.46  tff(c_50736, plain, (![B_6]: (r2_hidden('#skF_2'(u1_struct_0('#skF_7'), B_6), '#skF_8') | ~l1_orders_2('#skF_7') | u1_struct_0('#skF_7')=B_6 | ~m1_subset_1(B_6, k1_zfmisc_1(u1_struct_0('#skF_7'))))), inference(resolution, [status(thm)], [c_784, c_50711])).
% 22.31/12.46  tff(c_50772, plain, (![B_808]: (r2_hidden('#skF_2'(u1_struct_0('#skF_7'), B_808), '#skF_8') | u1_struct_0('#skF_7')=B_808 | ~m1_subset_1(B_808, k1_zfmisc_1(u1_struct_0('#skF_7'))))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_50736])).
% 22.31/12.46  tff(c_10, plain, (![A_5, B_6]: (~r2_hidden('#skF_2'(A_5, B_6), B_6) | B_6=A_5 | ~m1_subset_1(B_6, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 22.31/12.46  tff(c_50786, plain, (u1_struct_0('#skF_7')='#skF_8' | ~m1_subset_1('#skF_8', k1_zfmisc_1(u1_struct_0('#skF_7')))), inference(resolution, [status(thm)], [c_50772, c_10])).
% 22.31/12.46  tff(c_50797, plain, (u1_struct_0('#skF_7')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_50786])).
% 22.31/12.46  tff(c_148, plain, (v1_subset_1('#skF_8', u1_struct_0('#skF_7'))), inference(splitRight, [status(thm)], [c_90])).
% 22.31/12.46  tff(c_50850, plain, (v1_subset_1('#skF_8', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_50797, c_148])).
% 22.31/12.46  tff(c_50852, plain, (m1_subset_1('#skF_8', k1_zfmisc_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_50797, c_64])).
% 22.31/12.46  tff(c_62, plain, (![B_72]: (~v1_subset_1(B_72, B_72) | ~m1_subset_1(B_72, k1_zfmisc_1(B_72)))), inference(cnfTransformation, [status(thm)], [f_151])).
% 22.31/12.46  tff(c_51989, plain, (~v1_subset_1('#skF_8', '#skF_8')), inference(resolution, [status(thm)], [c_50852, c_62])).
% 22.31/12.46  tff(c_51998, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50850, c_51989])).
% 22.31/12.46  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 22.31/12.46  
% 22.31/12.46  Inference rules
% 22.31/12.46  ----------------------
% 22.31/12.46  #Ref     : 0
% 22.31/12.46  #Sup     : 13988
% 22.31/12.46  #Fact    : 8
% 22.31/12.46  #Define  : 0
% 22.31/12.46  #Split   : 18
% 22.31/12.46  #Chain   : 0
% 22.31/12.46  #Close   : 0
% 22.31/12.46  
% 22.31/12.46  Ordering : KBO
% 22.31/12.46  
% 22.31/12.46  Simplification rules
% 22.31/12.46  ----------------------
% 22.31/12.46  #Subsume      : 6400
% 22.31/12.46  #Demod        : 11508
% 22.31/12.46  #Tautology    : 3130
% 22.31/12.46  #SimpNegUnit  : 665
% 22.31/12.46  #BackRed      : 99
% 22.31/12.46  
% 22.31/12.46  #Partial instantiations: 0
% 22.31/12.46  #Strategies tried      : 1
% 22.31/12.46  
% 22.31/12.46  Timing (in seconds)
% 22.31/12.46  ----------------------
% 22.31/12.46  Preprocessing        : 0.34
% 22.31/12.46  Parsing              : 0.17
% 22.31/12.46  CNF conversion       : 0.03
% 22.31/12.46  Main loop            : 11.31
% 22.31/12.46  Inferencing          : 1.74
% 22.31/12.46  Reduction            : 2.82
% 22.31/12.46  Demodulation         : 2.02
% 22.31/12.46  BG Simplification    : 0.20
% 22.31/12.46  Subsumption          : 6.15
% 22.31/12.46  Abstraction          : 0.33
% 22.31/12.46  MUC search           : 0.00
% 22.31/12.46  Cooper               : 0.00
% 22.31/12.46  Total                : 11.69
% 22.31/12.46  Index Insertion      : 0.00
% 22.31/12.46  Index Deletion       : 0.00
% 22.31/12.46  Index Matching       : 0.00
% 22.31/12.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
