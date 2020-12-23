%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:00 EST 2020

% Result     : Theorem 4.83s
% Output     : CNFRefutation 5.10s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 336 expanded)
%              Number of leaves         :   44 ( 140 expanded)
%              Depth                    :   19
%              Number of atoms          :  221 (1317 expanded)
%              Number of equality atoms :   18 (  93 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_lattice3 > r1_orders_2 > v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_yellow_0 > r2_hidden > r1_yellow_0 > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_yellow_0 > v1_xboole_0 > l1_orders_2 > k1_yellow_0 > #nlpp > u1_struct_0 > k3_yellow_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_6 > #skF_1 > #skF_4 > #skF_7 > #skF_8 > #skF_3 > #skF_2 > #skF_5

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

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(v1_yellow_0,type,(
    v1_yellow_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_177,negated_conjecture,(
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

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( ! [C] :
            ( m1_subset_1(C,A)
           => r2_hidden(C,B) )
       => A = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_subset_1)).

tff(f_67,axiom,(
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

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_148,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( v1_subset_1(B,A)
      <=> B != A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).

tff(f_71,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => k3_yellow_0(A) = k1_yellow_0(A,k1_xboole_0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_yellow_0)).

tff(f_75,axiom,(
    ! [A,B] :
      ( l1_orders_2(A)
     => m1_subset_1(k1_yellow_0(A,B),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_yellow_0)).

tff(f_122,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v5_orders_2(A)
        & v1_yellow_0(A)
        & l1_orders_2(A) )
     => ( r1_yellow_0(A,k1_xboole_0)
        & r2_yellow_0(A,u1_struct_0(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_yellow_0)).

tff(f_109,axiom,(
    ! [A] :
      ( ( v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( ( ( B = k1_yellow_0(A,C)
                  & r1_yellow_0(A,C) )
               => ( r2_lattice3(A,C,B)
                  & ! [D] :
                      ( m1_subset_1(D,u1_struct_0(A))
                     => ( r2_lattice3(A,C,D)
                       => r1_orders_2(A,B,D) ) ) ) )
              & ( ( r2_lattice3(A,C,B)
                  & ! [D] :
                      ( m1_subset_1(D,u1_struct_0(A))
                     => ( r2_lattice3(A,C,D)
                       => r1_orders_2(A,B,D) ) ) )
               => ( B = k1_yellow_0(A,C)
                  & r1_yellow_0(A,C) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_yellow_0)).

tff(f_141,axiom,(
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
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_72,plain,(
    l1_orders_2('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( m1_subset_1('#skF_2'(A_5,B_6),A_5)
      | B_6 = A_5
      | ~ m1_subset_1(B_6,k1_zfmisc_1(A_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1204,plain,(
    ! [A_259,B_260,C_261] :
      ( r2_hidden('#skF_3'(A_259,B_260,C_261),B_260)
      | r2_lattice3(A_259,B_260,C_261)
      | ~ m1_subset_1(C_261,u1_struct_0(A_259))
      | ~ l1_orders_2(A_259) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1209,plain,(
    ! [B_262,A_263,C_264] :
      ( ~ v1_xboole_0(B_262)
      | r2_lattice3(A_263,B_262,C_264)
      | ~ m1_subset_1(C_264,u1_struct_0(A_263))
      | ~ l1_orders_2(A_263) ) ),
    inference(resolution,[status(thm)],[c_1204,c_2])).

tff(c_1222,plain,(
    ! [B_262,A_263,B_6] :
      ( ~ v1_xboole_0(B_262)
      | r2_lattice3(A_263,B_262,'#skF_2'(u1_struct_0(A_263),B_6))
      | ~ l1_orders_2(A_263)
      | u1_struct_0(A_263) = B_6
      | ~ m1_subset_1(B_6,k1_zfmisc_1(u1_struct_0(A_263))) ) ),
    inference(resolution,[status(thm)],[c_10,c_1209])).

tff(c_66,plain,(
    v13_waybel_0('#skF_8','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_70,plain,(
    ~ v1_xboole_0('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_12,plain,(
    ! [A_8,B_9] :
      ( r2_hidden(A_8,B_9)
      | v1_xboole_0(B_9)
      | ~ m1_subset_1(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_84,plain,
    ( r2_hidden(k3_yellow_0('#skF_7'),'#skF_8')
    | ~ v1_subset_1('#skF_8',u1_struct_0('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_107,plain,(
    ~ v1_subset_1('#skF_8',u1_struct_0('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_84])).

tff(c_90,plain,
    ( v1_subset_1('#skF_8',u1_struct_0('#skF_7'))
    | ~ r2_hidden(k3_yellow_0('#skF_7'),'#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_113,plain,(
    ~ r2_hidden(k3_yellow_0('#skF_7'),'#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_107,c_90])).

tff(c_116,plain,
    ( v1_xboole_0('#skF_8')
    | ~ m1_subset_1(k3_yellow_0('#skF_7'),'#skF_8') ),
    inference(resolution,[status(thm)],[c_12,c_113])).

tff(c_119,plain,(
    ~ m1_subset_1(k3_yellow_0('#skF_7'),'#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_116])).

tff(c_126,plain,(
    ! [B_88,A_89] :
      ( v1_subset_1(B_88,A_89)
      | B_88 = A_89
      | ~ m1_subset_1(B_88,k1_zfmisc_1(A_89)) ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_129,plain,
    ( v1_subset_1('#skF_8',u1_struct_0('#skF_7'))
    | u1_struct_0('#skF_7') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_64,c_126])).

tff(c_132,plain,(
    u1_struct_0('#skF_7') = '#skF_8' ),
    inference(negUnitSimplification,[status(thm)],[c_107,c_129])).

tff(c_97,plain,(
    ! [A_82] :
      ( k1_yellow_0(A_82,k1_xboole_0) = k3_yellow_0(A_82)
      | ~ l1_orders_2(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_101,plain,(
    k1_yellow_0('#skF_7',k1_xboole_0) = k3_yellow_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_72,c_97])).

tff(c_120,plain,(
    ! [A_86,B_87] :
      ( m1_subset_1(k1_yellow_0(A_86,B_87),u1_struct_0(A_86))
      | ~ l1_orders_2(A_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_123,plain,
    ( m1_subset_1(k3_yellow_0('#skF_7'),u1_struct_0('#skF_7'))
    | ~ l1_orders_2('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_101,c_120])).

tff(c_125,plain,(
    m1_subset_1(k3_yellow_0('#skF_7'),u1_struct_0('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_123])).

tff(c_133,plain,(
    m1_subset_1(k3_yellow_0('#skF_7'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_125])).

tff(c_137,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_119,c_133])).

tff(c_138,plain,(
    r2_hidden(k3_yellow_0('#skF_7'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_146,plain,(
    ! [A_90,B_91] :
      ( m1_subset_1(k1_yellow_0(A_90,B_91),u1_struct_0(A_90))
      | ~ l1_orders_2(A_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_149,plain,
    ( m1_subset_1(k3_yellow_0('#skF_7'),u1_struct_0('#skF_7'))
    | ~ l1_orders_2('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_101,c_146])).

tff(c_151,plain,(
    m1_subset_1(k3_yellow_0('#skF_7'),u1_struct_0('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_149])).

tff(c_76,plain,(
    v5_orders_2('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_82,plain,(
    ~ v2_struct_0('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_74,plain,(
    v1_yellow_0('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_46,plain,(
    ! [A_50] :
      ( r1_yellow_0(A_50,k1_xboole_0)
      | ~ l1_orders_2(A_50)
      | ~ v1_yellow_0(A_50)
      | ~ v5_orders_2(A_50)
      | v2_struct_0(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_1295,plain,(
    ! [A_292,C_293] :
      ( r2_lattice3(A_292,C_293,k1_yellow_0(A_292,C_293))
      | ~ r1_yellow_0(A_292,C_293)
      | ~ m1_subset_1(k1_yellow_0(A_292,C_293),u1_struct_0(A_292))
      | ~ l1_orders_2(A_292)
      | ~ v5_orders_2(A_292) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_1302,plain,
    ( r2_lattice3('#skF_7',k1_xboole_0,k1_yellow_0('#skF_7',k1_xboole_0))
    | ~ r1_yellow_0('#skF_7',k1_xboole_0)
    | ~ m1_subset_1(k3_yellow_0('#skF_7'),u1_struct_0('#skF_7'))
    | ~ l1_orders_2('#skF_7')
    | ~ v5_orders_2('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_101,c_1295])).

tff(c_1308,plain,
    ( r2_lattice3('#skF_7',k1_xboole_0,k3_yellow_0('#skF_7'))
    | ~ r1_yellow_0('#skF_7',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_72,c_151,c_101,c_1302])).

tff(c_1309,plain,(
    ~ r1_yellow_0('#skF_7',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_1308])).

tff(c_1325,plain,
    ( ~ l1_orders_2('#skF_7')
    | ~ v1_yellow_0('#skF_7')
    | ~ v5_orders_2('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_46,c_1309])).

tff(c_1328,plain,(
    v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_72,c_1325])).

tff(c_1330,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_1328])).

tff(c_1332,plain,(
    r1_yellow_0('#skF_7',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_1308])).

tff(c_1681,plain,(
    ! [A_363,C_364,D_365] :
      ( r1_orders_2(A_363,k1_yellow_0(A_363,C_364),D_365)
      | ~ r2_lattice3(A_363,C_364,D_365)
      | ~ m1_subset_1(D_365,u1_struct_0(A_363))
      | ~ r1_yellow_0(A_363,C_364)
      | ~ m1_subset_1(k1_yellow_0(A_363,C_364),u1_struct_0(A_363))
      | ~ l1_orders_2(A_363)
      | ~ v5_orders_2(A_363) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_1688,plain,(
    ! [D_365] :
      ( r1_orders_2('#skF_7',k1_yellow_0('#skF_7',k1_xboole_0),D_365)
      | ~ r2_lattice3('#skF_7',k1_xboole_0,D_365)
      | ~ m1_subset_1(D_365,u1_struct_0('#skF_7'))
      | ~ r1_yellow_0('#skF_7',k1_xboole_0)
      | ~ m1_subset_1(k3_yellow_0('#skF_7'),u1_struct_0('#skF_7'))
      | ~ l1_orders_2('#skF_7')
      | ~ v5_orders_2('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_101,c_1681])).

tff(c_1694,plain,(
    ! [D_365] :
      ( r1_orders_2('#skF_7',k3_yellow_0('#skF_7'),D_365)
      | ~ r2_lattice3('#skF_7',k1_xboole_0,D_365)
      | ~ m1_subset_1(D_365,u1_struct_0('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_72,c_151,c_1332,c_101,c_1688])).

tff(c_1827,plain,(
    ! [D_380,B_381,A_382,C_383] :
      ( r2_hidden(D_380,B_381)
      | ~ r1_orders_2(A_382,C_383,D_380)
      | ~ r2_hidden(C_383,B_381)
      | ~ m1_subset_1(D_380,u1_struct_0(A_382))
      | ~ m1_subset_1(C_383,u1_struct_0(A_382))
      | ~ v13_waybel_0(B_381,A_382)
      | ~ m1_subset_1(B_381,k1_zfmisc_1(u1_struct_0(A_382)))
      | ~ l1_orders_2(A_382) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_1833,plain,(
    ! [D_365,B_381] :
      ( r2_hidden(D_365,B_381)
      | ~ r2_hidden(k3_yellow_0('#skF_7'),B_381)
      | ~ m1_subset_1(k3_yellow_0('#skF_7'),u1_struct_0('#skF_7'))
      | ~ v13_waybel_0(B_381,'#skF_7')
      | ~ m1_subset_1(B_381,k1_zfmisc_1(u1_struct_0('#skF_7')))
      | ~ l1_orders_2('#skF_7')
      | ~ r2_lattice3('#skF_7',k1_xboole_0,D_365)
      | ~ m1_subset_1(D_365,u1_struct_0('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_1694,c_1827])).

tff(c_1864,plain,(
    ! [D_384,B_385] :
      ( r2_hidden(D_384,B_385)
      | ~ r2_hidden(k3_yellow_0('#skF_7'),B_385)
      | ~ v13_waybel_0(B_385,'#skF_7')
      | ~ m1_subset_1(B_385,k1_zfmisc_1(u1_struct_0('#skF_7')))
      | ~ r2_lattice3('#skF_7',k1_xboole_0,D_384)
      | ~ m1_subset_1(D_384,u1_struct_0('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_151,c_1833])).

tff(c_1872,plain,(
    ! [D_384] :
      ( r2_hidden(D_384,'#skF_8')
      | ~ r2_hidden(k3_yellow_0('#skF_7'),'#skF_8')
      | ~ v13_waybel_0('#skF_8','#skF_7')
      | ~ r2_lattice3('#skF_7',k1_xboole_0,D_384)
      | ~ m1_subset_1(D_384,u1_struct_0('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_64,c_1864])).

tff(c_1878,plain,(
    ! [D_386] :
      ( r2_hidden(D_386,'#skF_8')
      | ~ r2_lattice3('#skF_7',k1_xboole_0,D_386)
      | ~ m1_subset_1(D_386,u1_struct_0('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_138,c_1872])).

tff(c_2076,plain,(
    ! [B_396] :
      ( r2_hidden('#skF_2'(u1_struct_0('#skF_7'),B_396),'#skF_8')
      | ~ r2_lattice3('#skF_7',k1_xboole_0,'#skF_2'(u1_struct_0('#skF_7'),B_396))
      | u1_struct_0('#skF_7') = B_396
      | ~ m1_subset_1(B_396,k1_zfmisc_1(u1_struct_0('#skF_7'))) ) ),
    inference(resolution,[status(thm)],[c_10,c_1878])).

tff(c_2080,plain,(
    ! [B_6] :
      ( r2_hidden('#skF_2'(u1_struct_0('#skF_7'),B_6),'#skF_8')
      | ~ v1_xboole_0(k1_xboole_0)
      | ~ l1_orders_2('#skF_7')
      | u1_struct_0('#skF_7') = B_6
      | ~ m1_subset_1(B_6,k1_zfmisc_1(u1_struct_0('#skF_7'))) ) ),
    inference(resolution,[status(thm)],[c_1222,c_2076])).

tff(c_2090,plain,(
    ! [B_397] :
      ( r2_hidden('#skF_2'(u1_struct_0('#skF_7'),B_397),'#skF_8')
      | u1_struct_0('#skF_7') = B_397
      | ~ m1_subset_1(B_397,k1_zfmisc_1(u1_struct_0('#skF_7'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_6,c_2080])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( ~ r2_hidden('#skF_2'(A_5,B_6),B_6)
      | B_6 = A_5
      | ~ m1_subset_1(B_6,k1_zfmisc_1(A_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2100,plain,
    ( u1_struct_0('#skF_7') = '#skF_8'
    | ~ m1_subset_1('#skF_8',k1_zfmisc_1(u1_struct_0('#skF_7'))) ),
    inference(resolution,[status(thm)],[c_2090,c_8])).

tff(c_2109,plain,(
    u1_struct_0('#skF_7') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_2100])).

tff(c_139,plain,(
    v1_subset_1('#skF_8',u1_struct_0('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_2129,plain,(
    v1_subset_1('#skF_8','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2109,c_139])).

tff(c_2130,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2109,c_64])).

tff(c_62,plain,(
    ! [B_77] :
      ( ~ v1_subset_1(B_77,B_77)
      | ~ m1_subset_1(B_77,k1_zfmisc_1(B_77)) ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_2233,plain,(
    ~ v1_subset_1('#skF_8','#skF_8') ),
    inference(resolution,[status(thm)],[c_2130,c_62])).

tff(c_2241,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2129,c_2233])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:35:16 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.83/1.98  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.10/1.99  
% 5.10/1.99  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.10/1.99  %$ r2_lattice3 > r1_orders_2 > v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_yellow_0 > r2_hidden > r1_yellow_0 > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_yellow_0 > v1_xboole_0 > l1_orders_2 > k1_yellow_0 > #nlpp > u1_struct_0 > k3_yellow_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_6 > #skF_1 > #skF_4 > #skF_7 > #skF_8 > #skF_3 > #skF_2 > #skF_5
% 5.10/1.99  
% 5.10/1.99  %Foreground sorts:
% 5.10/1.99  
% 5.10/1.99  
% 5.10/1.99  %Background operators:
% 5.10/1.99  
% 5.10/1.99  
% 5.10/1.99  %Foreground operators:
% 5.10/1.99  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 5.10/1.99  tff(k1_yellow_0, type, k1_yellow_0: ($i * $i) > $i).
% 5.10/1.99  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 5.10/1.99  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 5.10/1.99  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.10/1.99  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.10/1.99  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 5.10/1.99  tff('#skF_1', type, '#skF_1': $i > $i).
% 5.10/1.99  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 5.10/1.99  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.10/1.99  tff(v2_waybel_0, type, v2_waybel_0: ($i * $i) > $o).
% 5.10/1.99  tff(k3_yellow_0, type, k3_yellow_0: $i > $i).
% 5.10/1.99  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 5.10/1.99  tff('#skF_7', type, '#skF_7': $i).
% 5.10/1.99  tff(r2_lattice3, type, r2_lattice3: ($i * $i * $i) > $o).
% 5.10/1.99  tff(r2_yellow_0, type, r2_yellow_0: ($i * $i) > $o).
% 5.10/1.99  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 5.10/1.99  tff(r1_yellow_0, type, r1_yellow_0: ($i * $i) > $o).
% 5.10/1.99  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 5.10/1.99  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.10/1.99  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 5.10/1.99  tff('#skF_8', type, '#skF_8': $i).
% 5.10/1.99  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.10/1.99  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 5.10/1.99  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.10/1.99  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 5.10/1.99  tff(v13_waybel_0, type, v13_waybel_0: ($i * $i) > $o).
% 5.10/1.99  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.10/1.99  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.10/1.99  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 5.10/1.99  tff(v1_yellow_0, type, v1_yellow_0: $i > $o).
% 5.10/1.99  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.10/1.99  
% 5.10/2.01  tff(f_177, negated_conjecture, ~(![A]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & v1_yellow_0(A)) & l1_orders_2(A)) => (![B]: ((((~v1_xboole_0(B) & v2_waybel_0(B, A)) & v13_waybel_0(B, A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v1_subset_1(B, u1_struct_0(A)) <=> ~r2_hidden(k3_yellow_0(A), B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_waybel_7)).
% 5.10/2.01  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 5.10/2.01  tff(f_41, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => ((![C]: (m1_subset_1(C, A) => r2_hidden(C, B))) => (A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_subset_1)).
% 5.10/2.01  tff(f_67, axiom, (![A]: (l1_orders_2(A) => (![B, C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_lattice3(A, B, C) <=> (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_hidden(D, B) => r1_orders_2(A, D, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_lattice3)).
% 5.10/2.01  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 5.10/2.01  tff(f_47, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 5.10/2.01  tff(f_148, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (v1_subset_1(B, A) <=> ~(B = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_subset_1)).
% 5.10/2.01  tff(f_71, axiom, (![A]: (l1_orders_2(A) => (k3_yellow_0(A) = k1_yellow_0(A, k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d11_yellow_0)).
% 5.10/2.01  tff(f_75, axiom, (![A, B]: (l1_orders_2(A) => m1_subset_1(k1_yellow_0(A, B), u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_yellow_0)).
% 5.10/2.01  tff(f_122, axiom, (![A]: ((((~v2_struct_0(A) & v5_orders_2(A)) & v1_yellow_0(A)) & l1_orders_2(A)) => (r1_yellow_0(A, k1_xboole_0) & r2_yellow_0(A, u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_yellow_0)).
% 5.10/2.01  tff(f_109, axiom, (![A]: ((v5_orders_2(A) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: ((((B = k1_yellow_0(A, C)) & r1_yellow_0(A, C)) => (r2_lattice3(A, C, B) & (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_lattice3(A, C, D) => r1_orders_2(A, B, D)))))) & ((r2_lattice3(A, C, B) & (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_lattice3(A, C, D) => r1_orders_2(A, B, D))))) => ((B = k1_yellow_0(A, C)) & r1_yellow_0(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_yellow_0)).
% 5.10/2.01  tff(f_141, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v13_waybel_0(B, A) <=> (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => ((r2_hidden(C, B) & r1_orders_2(A, C, D)) => r2_hidden(D, B))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d20_waybel_0)).
% 5.10/2.01  tff(c_64, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(u1_struct_0('#skF_7')))), inference(cnfTransformation, [status(thm)], [f_177])).
% 5.10/2.01  tff(c_72, plain, (l1_orders_2('#skF_7')), inference(cnfTransformation, [status(thm)], [f_177])).
% 5.10/2.01  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.10/2.01  tff(c_10, plain, (![A_5, B_6]: (m1_subset_1('#skF_2'(A_5, B_6), A_5) | B_6=A_5 | ~m1_subset_1(B_6, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.10/2.01  tff(c_1204, plain, (![A_259, B_260, C_261]: (r2_hidden('#skF_3'(A_259, B_260, C_261), B_260) | r2_lattice3(A_259, B_260, C_261) | ~m1_subset_1(C_261, u1_struct_0(A_259)) | ~l1_orders_2(A_259))), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.10/2.01  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.10/2.01  tff(c_1209, plain, (![B_262, A_263, C_264]: (~v1_xboole_0(B_262) | r2_lattice3(A_263, B_262, C_264) | ~m1_subset_1(C_264, u1_struct_0(A_263)) | ~l1_orders_2(A_263))), inference(resolution, [status(thm)], [c_1204, c_2])).
% 5.10/2.01  tff(c_1222, plain, (![B_262, A_263, B_6]: (~v1_xboole_0(B_262) | r2_lattice3(A_263, B_262, '#skF_2'(u1_struct_0(A_263), B_6)) | ~l1_orders_2(A_263) | u1_struct_0(A_263)=B_6 | ~m1_subset_1(B_6, k1_zfmisc_1(u1_struct_0(A_263))))), inference(resolution, [status(thm)], [c_10, c_1209])).
% 5.10/2.01  tff(c_66, plain, (v13_waybel_0('#skF_8', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_177])).
% 5.10/2.01  tff(c_70, plain, (~v1_xboole_0('#skF_8')), inference(cnfTransformation, [status(thm)], [f_177])).
% 5.10/2.01  tff(c_12, plain, (![A_8, B_9]: (r2_hidden(A_8, B_9) | v1_xboole_0(B_9) | ~m1_subset_1(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.10/2.01  tff(c_84, plain, (r2_hidden(k3_yellow_0('#skF_7'), '#skF_8') | ~v1_subset_1('#skF_8', u1_struct_0('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_177])).
% 5.10/2.01  tff(c_107, plain, (~v1_subset_1('#skF_8', u1_struct_0('#skF_7'))), inference(splitLeft, [status(thm)], [c_84])).
% 5.10/2.01  tff(c_90, plain, (v1_subset_1('#skF_8', u1_struct_0('#skF_7')) | ~r2_hidden(k3_yellow_0('#skF_7'), '#skF_8')), inference(cnfTransformation, [status(thm)], [f_177])).
% 5.10/2.01  tff(c_113, plain, (~r2_hidden(k3_yellow_0('#skF_7'), '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_107, c_90])).
% 5.10/2.01  tff(c_116, plain, (v1_xboole_0('#skF_8') | ~m1_subset_1(k3_yellow_0('#skF_7'), '#skF_8')), inference(resolution, [status(thm)], [c_12, c_113])).
% 5.10/2.01  tff(c_119, plain, (~m1_subset_1(k3_yellow_0('#skF_7'), '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_70, c_116])).
% 5.10/2.01  tff(c_126, plain, (![B_88, A_89]: (v1_subset_1(B_88, A_89) | B_88=A_89 | ~m1_subset_1(B_88, k1_zfmisc_1(A_89)))), inference(cnfTransformation, [status(thm)], [f_148])).
% 5.10/2.01  tff(c_129, plain, (v1_subset_1('#skF_8', u1_struct_0('#skF_7')) | u1_struct_0('#skF_7')='#skF_8'), inference(resolution, [status(thm)], [c_64, c_126])).
% 5.10/2.01  tff(c_132, plain, (u1_struct_0('#skF_7')='#skF_8'), inference(negUnitSimplification, [status(thm)], [c_107, c_129])).
% 5.10/2.01  tff(c_97, plain, (![A_82]: (k1_yellow_0(A_82, k1_xboole_0)=k3_yellow_0(A_82) | ~l1_orders_2(A_82))), inference(cnfTransformation, [status(thm)], [f_71])).
% 5.10/2.01  tff(c_101, plain, (k1_yellow_0('#skF_7', k1_xboole_0)=k3_yellow_0('#skF_7')), inference(resolution, [status(thm)], [c_72, c_97])).
% 5.10/2.01  tff(c_120, plain, (![A_86, B_87]: (m1_subset_1(k1_yellow_0(A_86, B_87), u1_struct_0(A_86)) | ~l1_orders_2(A_86))), inference(cnfTransformation, [status(thm)], [f_75])).
% 5.10/2.01  tff(c_123, plain, (m1_subset_1(k3_yellow_0('#skF_7'), u1_struct_0('#skF_7')) | ~l1_orders_2('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_101, c_120])).
% 5.10/2.01  tff(c_125, plain, (m1_subset_1(k3_yellow_0('#skF_7'), u1_struct_0('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_123])).
% 5.10/2.01  tff(c_133, plain, (m1_subset_1(k3_yellow_0('#skF_7'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_132, c_125])).
% 5.10/2.01  tff(c_137, plain, $false, inference(negUnitSimplification, [status(thm)], [c_119, c_133])).
% 5.10/2.01  tff(c_138, plain, (r2_hidden(k3_yellow_0('#skF_7'), '#skF_8')), inference(splitRight, [status(thm)], [c_84])).
% 5.10/2.01  tff(c_146, plain, (![A_90, B_91]: (m1_subset_1(k1_yellow_0(A_90, B_91), u1_struct_0(A_90)) | ~l1_orders_2(A_90))), inference(cnfTransformation, [status(thm)], [f_75])).
% 5.10/2.01  tff(c_149, plain, (m1_subset_1(k3_yellow_0('#skF_7'), u1_struct_0('#skF_7')) | ~l1_orders_2('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_101, c_146])).
% 5.10/2.01  tff(c_151, plain, (m1_subset_1(k3_yellow_0('#skF_7'), u1_struct_0('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_149])).
% 5.10/2.01  tff(c_76, plain, (v5_orders_2('#skF_7')), inference(cnfTransformation, [status(thm)], [f_177])).
% 5.10/2.01  tff(c_82, plain, (~v2_struct_0('#skF_7')), inference(cnfTransformation, [status(thm)], [f_177])).
% 5.10/2.01  tff(c_74, plain, (v1_yellow_0('#skF_7')), inference(cnfTransformation, [status(thm)], [f_177])).
% 5.10/2.01  tff(c_46, plain, (![A_50]: (r1_yellow_0(A_50, k1_xboole_0) | ~l1_orders_2(A_50) | ~v1_yellow_0(A_50) | ~v5_orders_2(A_50) | v2_struct_0(A_50))), inference(cnfTransformation, [status(thm)], [f_122])).
% 5.10/2.01  tff(c_1295, plain, (![A_292, C_293]: (r2_lattice3(A_292, C_293, k1_yellow_0(A_292, C_293)) | ~r1_yellow_0(A_292, C_293) | ~m1_subset_1(k1_yellow_0(A_292, C_293), u1_struct_0(A_292)) | ~l1_orders_2(A_292) | ~v5_orders_2(A_292))), inference(cnfTransformation, [status(thm)], [f_109])).
% 5.10/2.01  tff(c_1302, plain, (r2_lattice3('#skF_7', k1_xboole_0, k1_yellow_0('#skF_7', k1_xboole_0)) | ~r1_yellow_0('#skF_7', k1_xboole_0) | ~m1_subset_1(k3_yellow_0('#skF_7'), u1_struct_0('#skF_7')) | ~l1_orders_2('#skF_7') | ~v5_orders_2('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_101, c_1295])).
% 5.10/2.01  tff(c_1308, plain, (r2_lattice3('#skF_7', k1_xboole_0, k3_yellow_0('#skF_7')) | ~r1_yellow_0('#skF_7', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_76, c_72, c_151, c_101, c_1302])).
% 5.10/2.01  tff(c_1309, plain, (~r1_yellow_0('#skF_7', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_1308])).
% 5.10/2.01  tff(c_1325, plain, (~l1_orders_2('#skF_7') | ~v1_yellow_0('#skF_7') | ~v5_orders_2('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_46, c_1309])).
% 5.10/2.01  tff(c_1328, plain, (v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_72, c_1325])).
% 5.10/2.01  tff(c_1330, plain, $false, inference(negUnitSimplification, [status(thm)], [c_82, c_1328])).
% 5.10/2.01  tff(c_1332, plain, (r1_yellow_0('#skF_7', k1_xboole_0)), inference(splitRight, [status(thm)], [c_1308])).
% 5.10/2.01  tff(c_1681, plain, (![A_363, C_364, D_365]: (r1_orders_2(A_363, k1_yellow_0(A_363, C_364), D_365) | ~r2_lattice3(A_363, C_364, D_365) | ~m1_subset_1(D_365, u1_struct_0(A_363)) | ~r1_yellow_0(A_363, C_364) | ~m1_subset_1(k1_yellow_0(A_363, C_364), u1_struct_0(A_363)) | ~l1_orders_2(A_363) | ~v5_orders_2(A_363))), inference(cnfTransformation, [status(thm)], [f_109])).
% 5.10/2.01  tff(c_1688, plain, (![D_365]: (r1_orders_2('#skF_7', k1_yellow_0('#skF_7', k1_xboole_0), D_365) | ~r2_lattice3('#skF_7', k1_xboole_0, D_365) | ~m1_subset_1(D_365, u1_struct_0('#skF_7')) | ~r1_yellow_0('#skF_7', k1_xboole_0) | ~m1_subset_1(k3_yellow_0('#skF_7'), u1_struct_0('#skF_7')) | ~l1_orders_2('#skF_7') | ~v5_orders_2('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_101, c_1681])).
% 5.10/2.01  tff(c_1694, plain, (![D_365]: (r1_orders_2('#skF_7', k3_yellow_0('#skF_7'), D_365) | ~r2_lattice3('#skF_7', k1_xboole_0, D_365) | ~m1_subset_1(D_365, u1_struct_0('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_72, c_151, c_1332, c_101, c_1688])).
% 5.10/2.01  tff(c_1827, plain, (![D_380, B_381, A_382, C_383]: (r2_hidden(D_380, B_381) | ~r1_orders_2(A_382, C_383, D_380) | ~r2_hidden(C_383, B_381) | ~m1_subset_1(D_380, u1_struct_0(A_382)) | ~m1_subset_1(C_383, u1_struct_0(A_382)) | ~v13_waybel_0(B_381, A_382) | ~m1_subset_1(B_381, k1_zfmisc_1(u1_struct_0(A_382))) | ~l1_orders_2(A_382))), inference(cnfTransformation, [status(thm)], [f_141])).
% 5.10/2.01  tff(c_1833, plain, (![D_365, B_381]: (r2_hidden(D_365, B_381) | ~r2_hidden(k3_yellow_0('#skF_7'), B_381) | ~m1_subset_1(k3_yellow_0('#skF_7'), u1_struct_0('#skF_7')) | ~v13_waybel_0(B_381, '#skF_7') | ~m1_subset_1(B_381, k1_zfmisc_1(u1_struct_0('#skF_7'))) | ~l1_orders_2('#skF_7') | ~r2_lattice3('#skF_7', k1_xboole_0, D_365) | ~m1_subset_1(D_365, u1_struct_0('#skF_7')))), inference(resolution, [status(thm)], [c_1694, c_1827])).
% 5.10/2.01  tff(c_1864, plain, (![D_384, B_385]: (r2_hidden(D_384, B_385) | ~r2_hidden(k3_yellow_0('#skF_7'), B_385) | ~v13_waybel_0(B_385, '#skF_7') | ~m1_subset_1(B_385, k1_zfmisc_1(u1_struct_0('#skF_7'))) | ~r2_lattice3('#skF_7', k1_xboole_0, D_384) | ~m1_subset_1(D_384, u1_struct_0('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_151, c_1833])).
% 5.10/2.01  tff(c_1872, plain, (![D_384]: (r2_hidden(D_384, '#skF_8') | ~r2_hidden(k3_yellow_0('#skF_7'), '#skF_8') | ~v13_waybel_0('#skF_8', '#skF_7') | ~r2_lattice3('#skF_7', k1_xboole_0, D_384) | ~m1_subset_1(D_384, u1_struct_0('#skF_7')))), inference(resolution, [status(thm)], [c_64, c_1864])).
% 5.10/2.01  tff(c_1878, plain, (![D_386]: (r2_hidden(D_386, '#skF_8') | ~r2_lattice3('#skF_7', k1_xboole_0, D_386) | ~m1_subset_1(D_386, u1_struct_0('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_138, c_1872])).
% 5.10/2.01  tff(c_2076, plain, (![B_396]: (r2_hidden('#skF_2'(u1_struct_0('#skF_7'), B_396), '#skF_8') | ~r2_lattice3('#skF_7', k1_xboole_0, '#skF_2'(u1_struct_0('#skF_7'), B_396)) | u1_struct_0('#skF_7')=B_396 | ~m1_subset_1(B_396, k1_zfmisc_1(u1_struct_0('#skF_7'))))), inference(resolution, [status(thm)], [c_10, c_1878])).
% 5.10/2.01  tff(c_2080, plain, (![B_6]: (r2_hidden('#skF_2'(u1_struct_0('#skF_7'), B_6), '#skF_8') | ~v1_xboole_0(k1_xboole_0) | ~l1_orders_2('#skF_7') | u1_struct_0('#skF_7')=B_6 | ~m1_subset_1(B_6, k1_zfmisc_1(u1_struct_0('#skF_7'))))), inference(resolution, [status(thm)], [c_1222, c_2076])).
% 5.10/2.01  tff(c_2090, plain, (![B_397]: (r2_hidden('#skF_2'(u1_struct_0('#skF_7'), B_397), '#skF_8') | u1_struct_0('#skF_7')=B_397 | ~m1_subset_1(B_397, k1_zfmisc_1(u1_struct_0('#skF_7'))))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_6, c_2080])).
% 5.10/2.01  tff(c_8, plain, (![A_5, B_6]: (~r2_hidden('#skF_2'(A_5, B_6), B_6) | B_6=A_5 | ~m1_subset_1(B_6, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.10/2.01  tff(c_2100, plain, (u1_struct_0('#skF_7')='#skF_8' | ~m1_subset_1('#skF_8', k1_zfmisc_1(u1_struct_0('#skF_7')))), inference(resolution, [status(thm)], [c_2090, c_8])).
% 5.10/2.01  tff(c_2109, plain, (u1_struct_0('#skF_7')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_2100])).
% 5.10/2.01  tff(c_139, plain, (v1_subset_1('#skF_8', u1_struct_0('#skF_7'))), inference(splitRight, [status(thm)], [c_84])).
% 5.10/2.01  tff(c_2129, plain, (v1_subset_1('#skF_8', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_2109, c_139])).
% 5.10/2.01  tff(c_2130, plain, (m1_subset_1('#skF_8', k1_zfmisc_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_2109, c_64])).
% 5.10/2.01  tff(c_62, plain, (![B_77]: (~v1_subset_1(B_77, B_77) | ~m1_subset_1(B_77, k1_zfmisc_1(B_77)))), inference(cnfTransformation, [status(thm)], [f_148])).
% 5.10/2.01  tff(c_2233, plain, (~v1_subset_1('#skF_8', '#skF_8')), inference(resolution, [status(thm)], [c_2130, c_62])).
% 5.10/2.01  tff(c_2241, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2129, c_2233])).
% 5.10/2.01  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.10/2.01  
% 5.10/2.01  Inference rules
% 5.10/2.01  ----------------------
% 5.10/2.01  #Ref     : 0
% 5.10/2.01  #Sup     : 400
% 5.10/2.01  #Fact    : 0
% 5.10/2.01  #Define  : 0
% 5.10/2.01  #Split   : 6
% 5.10/2.01  #Chain   : 0
% 5.10/2.01  #Close   : 0
% 5.10/2.01  
% 5.10/2.01  Ordering : KBO
% 5.10/2.01  
% 5.10/2.01  Simplification rules
% 5.10/2.01  ----------------------
% 5.10/2.01  #Subsume      : 52
% 5.10/2.01  #Demod        : 500
% 5.10/2.01  #Tautology    : 104
% 5.10/2.01  #SimpNegUnit  : 11
% 5.10/2.01  #BackRed      : 44
% 5.10/2.01  
% 5.10/2.01  #Partial instantiations: 0
% 5.10/2.01  #Strategies tried      : 1
% 5.10/2.01  
% 5.10/2.01  Timing (in seconds)
% 5.10/2.01  ----------------------
% 5.10/2.01  Preprocessing        : 0.44
% 5.10/2.01  Parsing              : 0.22
% 5.10/2.01  CNF conversion       : 0.03
% 5.10/2.01  Main loop            : 0.72
% 5.10/2.01  Inferencing          : 0.27
% 5.10/2.01  Reduction            : 0.22
% 5.10/2.01  Demodulation         : 0.14
% 5.10/2.01  BG Simplification    : 0.04
% 5.10/2.01  Subsumption          : 0.13
% 5.10/2.01  Abstraction          : 0.04
% 5.10/2.01  MUC search           : 0.00
% 5.10/2.01  Cooper               : 0.00
% 5.10/2.01  Total                : 1.20
% 5.10/2.01  Index Insertion      : 0.00
% 5.10/2.01  Index Deletion       : 0.00
% 5.10/2.01  Index Matching       : 0.00
% 5.10/2.01  BG Taut test         : 0.00
%------------------------------------------------------------------------------
