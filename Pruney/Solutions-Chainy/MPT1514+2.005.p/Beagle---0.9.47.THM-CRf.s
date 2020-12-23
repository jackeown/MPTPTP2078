%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:51 EST 2020

% Result     : Theorem 6.76s
% Output     : CNFRefutation 7.02s
% Verified   : 
% Statistics : Number of formulae       :  118 (1328 expanded)
%              Number of leaves         :   36 ( 498 expanded)
%              Depth                    :   31
%              Number of atoms          :  369 (7084 expanded)
%              Number of equality atoms :   20 ( 170 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r4_lattice3 > r3_lattices > r1_lattices > r2_hidden > m1_subset_1 > v4_lattice3 > v2_struct_0 > v10_lattices > l3_lattices > k16_lattice3 > k15_lattice3 > a_2_6_lattice3 > a_2_5_lattice3 > a_2_2_lattice3 > #nlpp > u1_struct_0 > #skF_9 > #skF_1 > #skF_4 > #skF_7 > #skF_6 > #skF_5 > #skF_2 > #skF_8 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(l3_lattices,type,(
    l3_lattices: $i > $o )).

tff('#skF_9',type,(
    '#skF_9': $i > $i )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(r3_lattices,type,(
    r3_lattices: ( $i * $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k16_lattice3,type,(
    k16_lattice3: ( $i * $i ) > $i )).

tff(k15_lattice3,type,(
    k15_lattice3: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_lattices,type,(
    r1_lattices: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(r4_lattice3,type,(
    r4_lattice3: ( $i * $i * $i ) > $o )).

tff(a_2_5_lattice3,type,(
    a_2_5_lattice3: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(v4_lattice3,type,(
    v4_lattice3: $i > $o )).

tff(v10_lattices,type,(
    v10_lattices: $i > $o )).

tff(a_2_2_lattice3,type,(
    a_2_2_lattice3: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(a_2_6_lattice3,type,(
    a_2_6_lattice3: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_191,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v10_lattices(A)
          & v4_lattice3(A)
          & l3_lattices(A) )
       => ! [B,C] :
            ( ! [D] :
                ( m1_subset_1(D,u1_struct_0(A))
               => ~ ( r2_hidden(D,B)
                    & ! [E] :
                        ( m1_subset_1(E,u1_struct_0(A))
                       => ~ ( r3_lattices(A,D,E)
                            & r2_hidden(E,C) ) ) ) )
           => r3_lattices(A,k15_lattice3(A,B),k15_lattice3(A,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_lattice3)).

tff(f_164,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v10_lattices(A)
        & v4_lattice3(A)
        & l3_lattices(A) )
     => ! [B] :
          ( k15_lattice3(A,B) = k15_lattice3(A,a_2_5_lattice3(A,B))
          & k16_lattice3(A,B) = k16_lattice3(A,a_2_6_lattice3(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_lattice3)).

tff(f_78,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l3_lattices(A) )
     => m1_subset_1(k15_lattice3(A,B),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k15_lattice3)).

tff(f_71,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l3_lattices(A) )
     => ( ( ~ v2_struct_0(A)
          & v10_lattices(A)
          & v4_lattice3(A)
          & l3_lattices(A) )
       => ! [B,C] :
            ( m1_subset_1(C,u1_struct_0(A))
           => ( C = k15_lattice3(A,B)
            <=> ( r4_lattice3(A,C,B)
                & ! [D] :
                    ( m1_subset_1(D,u1_struct_0(A))
                   => ( r4_lattice3(A,D,B)
                     => r1_lattices(A,C,D) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d21_lattice3)).

tff(f_131,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v10_lattices(A)
        & v4_lattice3(A)
        & l3_lattices(A) )
     => ! [B] : k15_lattice3(A,B) = k16_lattice3(A,a_2_2_lattice3(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_lattice3)).

tff(f_150,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v10_lattices(A)
        & v4_lattice3(A)
        & l3_lattices(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( r2_hidden(B,C)
             => ( r3_lattices(A,B,k15_lattice3(A,C))
                & r3_lattices(A,k16_lattice3(A,C),B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_lattice3)).

tff(f_96,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(B)
        & v10_lattices(B)
        & v4_lattice3(B)
        & l3_lattices(B) )
     => ( r2_hidden(A,a_2_2_lattice3(B,C))
      <=> ? [D] :
            ( m1_subset_1(D,u1_struct_0(B))
            & A = D
            & r4_lattice3(B,D,C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_2_lattice3)).

tff(f_43,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l3_lattices(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( r4_lattice3(A,B,C)
            <=> ! [D] :
                  ( m1_subset_1(D,u1_struct_0(A))
                 => ( r2_hidden(D,C)
                   => r1_lattices(A,D,B) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d17_lattice3)).

tff(f_119,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(B)
        & v10_lattices(B)
        & v4_lattice3(B)
        & l3_lattices(B) )
     => ( r2_hidden(A,a_2_5_lattice3(B,C))
      <=> ? [D] :
            ( m1_subset_1(D,u1_struct_0(B))
            & A = D
            & ? [E] :
                ( m1_subset_1(E,u1_struct_0(B))
                & r3_lattices(B,D,E)
                & r2_hidden(E,C) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_5_lattice3)).

tff(c_60,plain,(
    ~ v2_struct_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_58,plain,(
    v10_lattices('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_56,plain,(
    v4_lattice3('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_54,plain,(
    l3_lattices('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_48,plain,(
    ! [A_66,B_68] :
      ( k15_lattice3(A_66,a_2_5_lattice3(A_66,B_68)) = k15_lattice3(A_66,B_68)
      | ~ l3_lattices(A_66)
      | ~ v4_lattice3(A_66)
      | ~ v10_lattices(A_66)
      | v2_struct_0(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_20,plain,(
    ! [A_35,B_36] :
      ( m1_subset_1(k15_lattice3(A_35,B_36),u1_struct_0(A_35))
      | ~ l3_lattices(A_35)
      | v2_struct_0(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_131,plain,(
    ! [A_123,B_124] :
      ( r4_lattice3(A_123,k15_lattice3(A_123,B_124),B_124)
      | ~ m1_subset_1(k15_lattice3(A_123,B_124),u1_struct_0(A_123))
      | ~ v4_lattice3(A_123)
      | ~ v10_lattices(A_123)
      | ~ l3_lattices(A_123)
      | v2_struct_0(A_123) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_137,plain,(
    ! [A_125,B_126] :
      ( r4_lattice3(A_125,k15_lattice3(A_125,B_126),B_126)
      | ~ v4_lattice3(A_125)
      | ~ v10_lattices(A_125)
      | ~ l3_lattices(A_125)
      | v2_struct_0(A_125) ) ),
    inference(resolution,[status(thm)],[c_20,c_131])).

tff(c_140,plain,(
    ! [A_66,B_68] :
      ( r4_lattice3(A_66,k15_lattice3(A_66,B_68),a_2_5_lattice3(A_66,B_68))
      | ~ v4_lattice3(A_66)
      | ~ v10_lattices(A_66)
      | ~ l3_lattices(A_66)
      | v2_struct_0(A_66)
      | ~ l3_lattices(A_66)
      | ~ v4_lattice3(A_66)
      | ~ v10_lattices(A_66)
      | v2_struct_0(A_66) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_137])).

tff(c_42,plain,(
    ! [A_56,B_58] :
      ( k16_lattice3(A_56,a_2_2_lattice3(A_56,B_58)) = k15_lattice3(A_56,B_58)
      | ~ l3_lattices(A_56)
      | ~ v4_lattice3(A_56)
      | ~ v10_lattices(A_56)
      | v2_struct_0(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_141,plain,(
    ! [A_127,C_128,B_129] :
      ( r3_lattices(A_127,k16_lattice3(A_127,C_128),B_129)
      | ~ r2_hidden(B_129,C_128)
      | ~ m1_subset_1(B_129,u1_struct_0(A_127))
      | ~ l3_lattices(A_127)
      | ~ v4_lattice3(A_127)
      | ~ v10_lattices(A_127)
      | v2_struct_0(A_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_991,plain,(
    ! [A_201,B_202,B_203] :
      ( r3_lattices(A_201,k15_lattice3(A_201,B_202),B_203)
      | ~ r2_hidden(B_203,a_2_2_lattice3(A_201,B_202))
      | ~ m1_subset_1(B_203,u1_struct_0(A_201))
      | ~ l3_lattices(A_201)
      | ~ v4_lattice3(A_201)
      | ~ v10_lattices(A_201)
      | v2_struct_0(A_201)
      | ~ l3_lattices(A_201)
      | ~ v4_lattice3(A_201)
      | ~ v10_lattices(A_201)
      | v2_struct_0(A_201) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_141])).

tff(c_52,plain,(
    ~ r3_lattices('#skF_6',k15_lattice3('#skF_6','#skF_7'),k15_lattice3('#skF_6','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_994,plain,
    ( ~ r2_hidden(k15_lattice3('#skF_6','#skF_8'),a_2_2_lattice3('#skF_6','#skF_7'))
    | ~ m1_subset_1(k15_lattice3('#skF_6','#skF_8'),u1_struct_0('#skF_6'))
    | ~ l3_lattices('#skF_6')
    | ~ v4_lattice3('#skF_6')
    | ~ v10_lattices('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_991,c_52])).

tff(c_1009,plain,
    ( ~ r2_hidden(k15_lattice3('#skF_6','#skF_8'),a_2_2_lattice3('#skF_6','#skF_7'))
    | ~ m1_subset_1(k15_lattice3('#skF_6','#skF_8'),u1_struct_0('#skF_6'))
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_994])).

tff(c_1010,plain,
    ( ~ r2_hidden(k15_lattice3('#skF_6','#skF_8'),a_2_2_lattice3('#skF_6','#skF_7'))
    | ~ m1_subset_1(k15_lattice3('#skF_6','#skF_8'),u1_struct_0('#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_1009])).

tff(c_1020,plain,(
    ~ m1_subset_1(k15_lattice3('#skF_6','#skF_8'),u1_struct_0('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_1010])).

tff(c_1023,plain,
    ( ~ l3_lattices('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_20,c_1020])).

tff(c_1026,plain,(
    v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_1023])).

tff(c_1028,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_1026])).

tff(c_1030,plain,(
    m1_subset_1(k15_lattice3('#skF_6','#skF_8'),u1_struct_0('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_1010])).

tff(c_22,plain,(
    ! [D_42,B_38,C_39] :
      ( r2_hidden(D_42,a_2_2_lattice3(B_38,C_39))
      | ~ r4_lattice3(B_38,D_42,C_39)
      | ~ m1_subset_1(D_42,u1_struct_0(B_38))
      | ~ l3_lattices(B_38)
      | ~ v4_lattice3(B_38)
      | ~ v10_lattices(B_38)
      | v2_struct_0(B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_1029,plain,(
    ~ r2_hidden(k15_lattice3('#skF_6','#skF_8'),a_2_2_lattice3('#skF_6','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_1010])).

tff(c_1058,plain,
    ( ~ r4_lattice3('#skF_6',k15_lattice3('#skF_6','#skF_8'),'#skF_7')
    | ~ m1_subset_1(k15_lattice3('#skF_6','#skF_8'),u1_struct_0('#skF_6'))
    | ~ l3_lattices('#skF_6')
    | ~ v4_lattice3('#skF_6')
    | ~ v10_lattices('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_22,c_1029])).

tff(c_1061,plain,
    ( ~ r4_lattice3('#skF_6',k15_lattice3('#skF_6','#skF_8'),'#skF_7')
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_1030,c_1058])).

tff(c_1062,plain,(
    ~ r4_lattice3('#skF_6',k15_lattice3('#skF_6','#skF_8'),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_1061])).

tff(c_6,plain,(
    ! [A_1,B_13,C_19] :
      ( r2_hidden('#skF_1'(A_1,B_13,C_19),C_19)
      | r4_lattice3(A_1,B_13,C_19)
      | ~ m1_subset_1(B_13,u1_struct_0(A_1))
      | ~ l3_lattices(A_1)
      | v2_struct_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_8,plain,(
    ! [A_1,B_13,C_19] :
      ( m1_subset_1('#skF_1'(A_1,B_13,C_19),u1_struct_0(A_1))
      | r4_lattice3(A_1,B_13,C_19)
      | ~ m1_subset_1(B_13,u1_struct_0(A_1))
      | ~ l3_lattices(A_1)
      | v2_struct_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_66,plain,(
    ! [D_80] :
      ( m1_subset_1('#skF_9'(D_80),u1_struct_0('#skF_6'))
      | ~ r2_hidden(D_80,'#skF_7')
      | ~ m1_subset_1(D_80,u1_struct_0('#skF_6')) ) ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_64,plain,(
    ! [D_80] :
      ( r3_lattices('#skF_6',D_80,'#skF_9'(D_80))
      | ~ r2_hidden(D_80,'#skF_7')
      | ~ m1_subset_1(D_80,u1_struct_0('#skF_6')) ) ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_62,plain,(
    ! [D_80] :
      ( r2_hidden('#skF_9'(D_80),'#skF_8')
      | ~ r2_hidden(D_80,'#skF_7')
      | ~ m1_subset_1(D_80,u1_struct_0('#skF_6')) ) ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_455,plain,(
    ! [D_169,B_170,C_171,E_172] :
      ( r2_hidden(D_169,a_2_5_lattice3(B_170,C_171))
      | ~ r2_hidden(E_172,C_171)
      | ~ r3_lattices(B_170,D_169,E_172)
      | ~ m1_subset_1(E_172,u1_struct_0(B_170))
      | ~ m1_subset_1(D_169,u1_struct_0(B_170))
      | ~ l3_lattices(B_170)
      | ~ v4_lattice3(B_170)
      | ~ v10_lattices(B_170)
      | v2_struct_0(B_170) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_1368,plain,(
    ! [D_212,B_213,D_214] :
      ( r2_hidden(D_212,a_2_5_lattice3(B_213,'#skF_8'))
      | ~ r3_lattices(B_213,D_212,'#skF_9'(D_214))
      | ~ m1_subset_1('#skF_9'(D_214),u1_struct_0(B_213))
      | ~ m1_subset_1(D_212,u1_struct_0(B_213))
      | ~ l3_lattices(B_213)
      | ~ v4_lattice3(B_213)
      | ~ v10_lattices(B_213)
      | v2_struct_0(B_213)
      | ~ r2_hidden(D_214,'#skF_7')
      | ~ m1_subset_1(D_214,u1_struct_0('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_62,c_455])).

tff(c_1379,plain,(
    ! [D_80] :
      ( r2_hidden(D_80,a_2_5_lattice3('#skF_6','#skF_8'))
      | ~ m1_subset_1('#skF_9'(D_80),u1_struct_0('#skF_6'))
      | ~ l3_lattices('#skF_6')
      | ~ v4_lattice3('#skF_6')
      | ~ v10_lattices('#skF_6')
      | v2_struct_0('#skF_6')
      | ~ r2_hidden(D_80,'#skF_7')
      | ~ m1_subset_1(D_80,u1_struct_0('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_64,c_1368])).

tff(c_1385,plain,(
    ! [D_80] :
      ( r2_hidden(D_80,a_2_5_lattice3('#skF_6','#skF_8'))
      | ~ m1_subset_1('#skF_9'(D_80),u1_struct_0('#skF_6'))
      | v2_struct_0('#skF_6')
      | ~ r2_hidden(D_80,'#skF_7')
      | ~ m1_subset_1(D_80,u1_struct_0('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_1379])).

tff(c_1387,plain,(
    ! [D_215] :
      ( r2_hidden(D_215,a_2_5_lattice3('#skF_6','#skF_8'))
      | ~ m1_subset_1('#skF_9'(D_215),u1_struct_0('#skF_6'))
      | ~ r2_hidden(D_215,'#skF_7')
      | ~ m1_subset_1(D_215,u1_struct_0('#skF_6')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_1385])).

tff(c_1391,plain,(
    ! [D_80] :
      ( r2_hidden(D_80,a_2_5_lattice3('#skF_6','#skF_8'))
      | ~ r2_hidden(D_80,'#skF_7')
      | ~ m1_subset_1(D_80,u1_struct_0('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_66,c_1387])).

tff(c_1392,plain,(
    ! [D_216] :
      ( r2_hidden(D_216,a_2_5_lattice3('#skF_6','#skF_8'))
      | ~ r2_hidden(D_216,'#skF_7')
      | ~ m1_subset_1(D_216,u1_struct_0('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_66,c_1387])).

tff(c_38,plain,(
    ! [A_43,B_44,C_45] :
      ( '#skF_4'(A_43,B_44,C_45) = A_43
      | ~ r2_hidden(A_43,a_2_5_lattice3(B_44,C_45))
      | ~ l3_lattices(B_44)
      | ~ v4_lattice3(B_44)
      | ~ v10_lattices(B_44)
      | v2_struct_0(B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_1402,plain,(
    ! [D_216] :
      ( '#skF_4'(D_216,'#skF_6','#skF_8') = D_216
      | ~ l3_lattices('#skF_6')
      | ~ v4_lattice3('#skF_6')
      | ~ v10_lattices('#skF_6')
      | v2_struct_0('#skF_6')
      | ~ r2_hidden(D_216,'#skF_7')
      | ~ m1_subset_1(D_216,u1_struct_0('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_1392,c_38])).

tff(c_1410,plain,(
    ! [D_216] :
      ( '#skF_4'(D_216,'#skF_6','#skF_8') = D_216
      | v2_struct_0('#skF_6')
      | ~ r2_hidden(D_216,'#skF_7')
      | ~ m1_subset_1(D_216,u1_struct_0('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_1402])).

tff(c_1412,plain,(
    ! [D_217] :
      ( '#skF_4'(D_217,'#skF_6','#skF_8') = D_217
      | ~ r2_hidden(D_217,'#skF_7')
      | ~ m1_subset_1(D_217,u1_struct_0('#skF_6')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_1410])).

tff(c_1441,plain,(
    ! [B_13,C_19] :
      ( '#skF_4'('#skF_1'('#skF_6',B_13,C_19),'#skF_6','#skF_8') = '#skF_1'('#skF_6',B_13,C_19)
      | ~ r2_hidden('#skF_1'('#skF_6',B_13,C_19),'#skF_7')
      | r4_lattice3('#skF_6',B_13,C_19)
      | ~ m1_subset_1(B_13,u1_struct_0('#skF_6'))
      | ~ l3_lattices('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_8,c_1412])).

tff(c_1470,plain,(
    ! [B_13,C_19] :
      ( '#skF_4'('#skF_1'('#skF_6',B_13,C_19),'#skF_6','#skF_8') = '#skF_1'('#skF_6',B_13,C_19)
      | ~ r2_hidden('#skF_1'('#skF_6',B_13,C_19),'#skF_7')
      | r4_lattice3('#skF_6',B_13,C_19)
      | ~ m1_subset_1(B_13,u1_struct_0('#skF_6'))
      | v2_struct_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_1441])).

tff(c_3217,plain,(
    ! [B_281,C_282] :
      ( '#skF_4'('#skF_1'('#skF_6',B_281,C_282),'#skF_6','#skF_8') = '#skF_1'('#skF_6',B_281,C_282)
      | ~ r2_hidden('#skF_1'('#skF_6',B_281,C_282),'#skF_7')
      | r4_lattice3('#skF_6',B_281,C_282)
      | ~ m1_subset_1(B_281,u1_struct_0('#skF_6')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_1470])).

tff(c_3221,plain,(
    ! [B_13] :
      ( '#skF_4'('#skF_1'('#skF_6',B_13,'#skF_7'),'#skF_6','#skF_8') = '#skF_1'('#skF_6',B_13,'#skF_7')
      | r4_lattice3('#skF_6',B_13,'#skF_7')
      | ~ m1_subset_1(B_13,u1_struct_0('#skF_6'))
      | ~ l3_lattices('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_6,c_3217])).

tff(c_3224,plain,(
    ! [B_13] :
      ( '#skF_4'('#skF_1'('#skF_6',B_13,'#skF_7'),'#skF_6','#skF_8') = '#skF_1'('#skF_6',B_13,'#skF_7')
      | r4_lattice3('#skF_6',B_13,'#skF_7')
      | ~ m1_subset_1(B_13,u1_struct_0('#skF_6'))
      | v2_struct_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_3221])).

tff(c_3226,plain,(
    ! [B_283] :
      ( '#skF_4'('#skF_1'('#skF_6',B_283,'#skF_7'),'#skF_6','#skF_8') = '#skF_1'('#skF_6',B_283,'#skF_7')
      | r4_lattice3('#skF_6',B_283,'#skF_7')
      | ~ m1_subset_1(B_283,u1_struct_0('#skF_6')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_3224])).

tff(c_3250,plain,
    ( '#skF_4'('#skF_1'('#skF_6',k15_lattice3('#skF_6','#skF_8'),'#skF_7'),'#skF_6','#skF_8') = '#skF_1'('#skF_6',k15_lattice3('#skF_6','#skF_8'),'#skF_7')
    | r4_lattice3('#skF_6',k15_lattice3('#skF_6','#skF_8'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_1030,c_3226])).

tff(c_3293,plain,(
    '#skF_4'('#skF_1'('#skF_6',k15_lattice3('#skF_6','#skF_8'),'#skF_7'),'#skF_6','#skF_8') = '#skF_1'('#skF_6',k15_lattice3('#skF_6','#skF_8'),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_1062,c_3250])).

tff(c_40,plain,(
    ! [A_43,B_44,C_45] :
      ( m1_subset_1('#skF_4'(A_43,B_44,C_45),u1_struct_0(B_44))
      | ~ r2_hidden(A_43,a_2_5_lattice3(B_44,C_45))
      | ~ l3_lattices(B_44)
      | ~ v4_lattice3(B_44)
      | ~ v10_lattices(B_44)
      | v2_struct_0(B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_3331,plain,
    ( m1_subset_1('#skF_1'('#skF_6',k15_lattice3('#skF_6','#skF_8'),'#skF_7'),u1_struct_0('#skF_6'))
    | ~ r2_hidden('#skF_1'('#skF_6',k15_lattice3('#skF_6','#skF_8'),'#skF_7'),a_2_5_lattice3('#skF_6','#skF_8'))
    | ~ l3_lattices('#skF_6')
    | ~ v4_lattice3('#skF_6')
    | ~ v10_lattices('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_3293,c_40])).

tff(c_3339,plain,
    ( m1_subset_1('#skF_1'('#skF_6',k15_lattice3('#skF_6','#skF_8'),'#skF_7'),u1_struct_0('#skF_6'))
    | ~ r2_hidden('#skF_1'('#skF_6',k15_lattice3('#skF_6','#skF_8'),'#skF_7'),a_2_5_lattice3('#skF_6','#skF_8'))
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_3331])).

tff(c_3340,plain,
    ( m1_subset_1('#skF_1'('#skF_6',k15_lattice3('#skF_6','#skF_8'),'#skF_7'),u1_struct_0('#skF_6'))
    | ~ r2_hidden('#skF_1'('#skF_6',k15_lattice3('#skF_6','#skF_8'),'#skF_7'),a_2_5_lattice3('#skF_6','#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_3339])).

tff(c_3342,plain,(
    ~ r2_hidden('#skF_1'('#skF_6',k15_lattice3('#skF_6','#skF_8'),'#skF_7'),a_2_5_lattice3('#skF_6','#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_3340])).

tff(c_3355,plain,
    ( ~ r2_hidden('#skF_1'('#skF_6',k15_lattice3('#skF_6','#skF_8'),'#skF_7'),'#skF_7')
    | ~ m1_subset_1('#skF_1'('#skF_6',k15_lattice3('#skF_6','#skF_8'),'#skF_7'),u1_struct_0('#skF_6')) ),
    inference(resolution,[status(thm)],[c_1391,c_3342])).

tff(c_3356,plain,(
    ~ m1_subset_1('#skF_1'('#skF_6',k15_lattice3('#skF_6','#skF_8'),'#skF_7'),u1_struct_0('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_3355])).

tff(c_3359,plain,
    ( r4_lattice3('#skF_6',k15_lattice3('#skF_6','#skF_8'),'#skF_7')
    | ~ m1_subset_1(k15_lattice3('#skF_6','#skF_8'),u1_struct_0('#skF_6'))
    | ~ l3_lattices('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_8,c_3356])).

tff(c_3362,plain,
    ( r4_lattice3('#skF_6',k15_lattice3('#skF_6','#skF_8'),'#skF_7')
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_1030,c_3359])).

tff(c_3364,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_1062,c_3362])).

tff(c_3365,plain,(
    ~ r2_hidden('#skF_1'('#skF_6',k15_lattice3('#skF_6','#skF_8'),'#skF_7'),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_3355])).

tff(c_3429,plain,
    ( r4_lattice3('#skF_6',k15_lattice3('#skF_6','#skF_8'),'#skF_7')
    | ~ m1_subset_1(k15_lattice3('#skF_6','#skF_8'),u1_struct_0('#skF_6'))
    | ~ l3_lattices('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_6,c_3365])).

tff(c_3432,plain,
    ( r4_lattice3('#skF_6',k15_lattice3('#skF_6','#skF_8'),'#skF_7')
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_1030,c_3429])).

tff(c_3434,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_1062,c_3432])).

tff(c_3435,plain,(
    m1_subset_1('#skF_1'('#skF_6',k15_lattice3('#skF_6','#skF_8'),'#skF_7'),u1_struct_0('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_3340])).

tff(c_2,plain,(
    ! [A_1,D_22,B_13,C_19] :
      ( r1_lattices(A_1,D_22,B_13)
      | ~ r2_hidden(D_22,C_19)
      | ~ m1_subset_1(D_22,u1_struct_0(A_1))
      | ~ r4_lattice3(A_1,B_13,C_19)
      | ~ m1_subset_1(B_13,u1_struct_0(A_1))
      | ~ l3_lattices(A_1)
      | v2_struct_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_5472,plain,(
    ! [A_358,D_359,B_360] :
      ( r1_lattices(A_358,D_359,B_360)
      | ~ m1_subset_1(D_359,u1_struct_0(A_358))
      | ~ r4_lattice3(A_358,B_360,a_2_5_lattice3('#skF_6','#skF_8'))
      | ~ m1_subset_1(B_360,u1_struct_0(A_358))
      | ~ l3_lattices(A_358)
      | v2_struct_0(A_358)
      | ~ r2_hidden(D_359,'#skF_7')
      | ~ m1_subset_1(D_359,u1_struct_0('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_1392,c_2])).

tff(c_5484,plain,(
    ! [B_360] :
      ( r1_lattices('#skF_6','#skF_1'('#skF_6',k15_lattice3('#skF_6','#skF_8'),'#skF_7'),B_360)
      | ~ r4_lattice3('#skF_6',B_360,a_2_5_lattice3('#skF_6','#skF_8'))
      | ~ m1_subset_1(B_360,u1_struct_0('#skF_6'))
      | ~ l3_lattices('#skF_6')
      | v2_struct_0('#skF_6')
      | ~ r2_hidden('#skF_1'('#skF_6',k15_lattice3('#skF_6','#skF_8'),'#skF_7'),'#skF_7')
      | ~ m1_subset_1('#skF_1'('#skF_6',k15_lattice3('#skF_6','#skF_8'),'#skF_7'),u1_struct_0('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_3435,c_5472])).

tff(c_5541,plain,(
    ! [B_360] :
      ( r1_lattices('#skF_6','#skF_1'('#skF_6',k15_lattice3('#skF_6','#skF_8'),'#skF_7'),B_360)
      | ~ r4_lattice3('#skF_6',B_360,a_2_5_lattice3('#skF_6','#skF_8'))
      | ~ m1_subset_1(B_360,u1_struct_0('#skF_6'))
      | v2_struct_0('#skF_6')
      | ~ r2_hidden('#skF_1'('#skF_6',k15_lattice3('#skF_6','#skF_8'),'#skF_7'),'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3435,c_54,c_5484])).

tff(c_5542,plain,(
    ! [B_360] :
      ( r1_lattices('#skF_6','#skF_1'('#skF_6',k15_lattice3('#skF_6','#skF_8'),'#skF_7'),B_360)
      | ~ r4_lattice3('#skF_6',B_360,a_2_5_lattice3('#skF_6','#skF_8'))
      | ~ m1_subset_1(B_360,u1_struct_0('#skF_6'))
      | ~ r2_hidden('#skF_1'('#skF_6',k15_lattice3('#skF_6','#skF_8'),'#skF_7'),'#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_5541])).

tff(c_5616,plain,(
    ~ r2_hidden('#skF_1'('#skF_6',k15_lattice3('#skF_6','#skF_8'),'#skF_7'),'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_5542])).

tff(c_5648,plain,
    ( r4_lattice3('#skF_6',k15_lattice3('#skF_6','#skF_8'),'#skF_7')
    | ~ m1_subset_1(k15_lattice3('#skF_6','#skF_8'),u1_struct_0('#skF_6'))
    | ~ l3_lattices('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_6,c_5616])).

tff(c_5651,plain,
    ( r4_lattice3('#skF_6',k15_lattice3('#skF_6','#skF_8'),'#skF_7')
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_1030,c_5648])).

tff(c_5653,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_1062,c_5651])).

tff(c_5669,plain,(
    ! [B_368] :
      ( r1_lattices('#skF_6','#skF_1'('#skF_6',k15_lattice3('#skF_6','#skF_8'),'#skF_7'),B_368)
      | ~ r4_lattice3('#skF_6',B_368,a_2_5_lattice3('#skF_6','#skF_8'))
      | ~ m1_subset_1(B_368,u1_struct_0('#skF_6')) ) ),
    inference(splitRight,[status(thm)],[c_5542])).

tff(c_4,plain,(
    ! [A_1,B_13,C_19] :
      ( ~ r1_lattices(A_1,'#skF_1'(A_1,B_13,C_19),B_13)
      | r4_lattice3(A_1,B_13,C_19)
      | ~ m1_subset_1(B_13,u1_struct_0(A_1))
      | ~ l3_lattices(A_1)
      | v2_struct_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_5677,plain,
    ( r4_lattice3('#skF_6',k15_lattice3('#skF_6','#skF_8'),'#skF_7')
    | ~ l3_lattices('#skF_6')
    | v2_struct_0('#skF_6')
    | ~ r4_lattice3('#skF_6',k15_lattice3('#skF_6','#skF_8'),a_2_5_lattice3('#skF_6','#skF_8'))
    | ~ m1_subset_1(k15_lattice3('#skF_6','#skF_8'),u1_struct_0('#skF_6')) ),
    inference(resolution,[status(thm)],[c_5669,c_4])).

tff(c_5684,plain,
    ( r4_lattice3('#skF_6',k15_lattice3('#skF_6','#skF_8'),'#skF_7')
    | v2_struct_0('#skF_6')
    | ~ r4_lattice3('#skF_6',k15_lattice3('#skF_6','#skF_8'),a_2_5_lattice3('#skF_6','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1030,c_54,c_5677])).

tff(c_5685,plain,(
    ~ r4_lattice3('#skF_6',k15_lattice3('#skF_6','#skF_8'),a_2_5_lattice3('#skF_6','#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_1062,c_5684])).

tff(c_5688,plain,
    ( ~ l3_lattices('#skF_6')
    | ~ v4_lattice3('#skF_6')
    | ~ v10_lattices('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_140,c_5685])).

tff(c_5691,plain,(
    v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_5688])).

tff(c_5693,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_5691])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n001.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 11:19:14 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.76/2.34  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.76/2.35  
% 6.76/2.35  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.76/2.35  %$ r4_lattice3 > r3_lattices > r1_lattices > r2_hidden > m1_subset_1 > v4_lattice3 > v2_struct_0 > v10_lattices > l3_lattices > k16_lattice3 > k15_lattice3 > a_2_6_lattice3 > a_2_5_lattice3 > a_2_2_lattice3 > #nlpp > u1_struct_0 > #skF_9 > #skF_1 > #skF_4 > #skF_7 > #skF_6 > #skF_5 > #skF_2 > #skF_8 > #skF_3
% 6.76/2.35  
% 6.76/2.35  %Foreground sorts:
% 6.76/2.35  
% 6.76/2.35  
% 6.76/2.35  %Background operators:
% 6.76/2.35  
% 6.76/2.35  
% 6.76/2.35  %Foreground operators:
% 6.76/2.35  tff(l3_lattices, type, l3_lattices: $i > $o).
% 6.76/2.35  tff('#skF_9', type, '#skF_9': $i > $i).
% 6.76/2.35  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 6.76/2.35  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 6.76/2.35  tff(r3_lattices, type, r3_lattices: ($i * $i * $i) > $o).
% 6.76/2.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.76/2.35  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.76/2.35  tff(k16_lattice3, type, k16_lattice3: ($i * $i) > $i).
% 6.76/2.35  tff(k15_lattice3, type, k15_lattice3: ($i * $i) > $i).
% 6.76/2.35  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 6.76/2.35  tff('#skF_7', type, '#skF_7': $i).
% 6.76/2.35  tff(r1_lattices, type, r1_lattices: ($i * $i * $i) > $o).
% 6.76/2.35  tff('#skF_6', type, '#skF_6': $i).
% 6.76/2.35  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 6.76/2.35  tff(r4_lattice3, type, r4_lattice3: ($i * $i * $i) > $o).
% 6.76/2.35  tff(a_2_5_lattice3, type, a_2_5_lattice3: ($i * $i) > $i).
% 6.76/2.35  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 6.76/2.35  tff(v4_lattice3, type, v4_lattice3: $i > $o).
% 6.76/2.35  tff(v10_lattices, type, v10_lattices: $i > $o).
% 6.76/2.35  tff(a_2_2_lattice3, type, a_2_2_lattice3: ($i * $i) > $i).
% 6.76/2.35  tff('#skF_8', type, '#skF_8': $i).
% 6.76/2.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.76/2.35  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 6.76/2.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.76/2.35  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 6.76/2.35  tff(a_2_6_lattice3, type, a_2_6_lattice3: ($i * $i) > $i).
% 6.76/2.35  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.76/2.35  
% 7.02/2.37  tff(f_191, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v4_lattice3(A)) & l3_lattices(A)) => (![B, C]: ((![D]: (m1_subset_1(D, u1_struct_0(A)) => ~(r2_hidden(D, B) & (![E]: (m1_subset_1(E, u1_struct_0(A)) => ~(r3_lattices(A, D, E) & r2_hidden(E, C))))))) => r3_lattices(A, k15_lattice3(A, B), k15_lattice3(A, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_lattice3)).
% 7.02/2.37  tff(f_164, axiom, (![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v4_lattice3(A)) & l3_lattices(A)) => (![B]: ((k15_lattice3(A, B) = k15_lattice3(A, a_2_5_lattice3(A, B))) & (k16_lattice3(A, B) = k16_lattice3(A, a_2_6_lattice3(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_lattice3)).
% 7.02/2.37  tff(f_78, axiom, (![A, B]: ((~v2_struct_0(A) & l3_lattices(A)) => m1_subset_1(k15_lattice3(A, B), u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k15_lattice3)).
% 7.02/2.37  tff(f_71, axiom, (![A]: ((~v2_struct_0(A) & l3_lattices(A)) => ((((~v2_struct_0(A) & v10_lattices(A)) & v4_lattice3(A)) & l3_lattices(A)) => (![B, C]: (m1_subset_1(C, u1_struct_0(A)) => ((C = k15_lattice3(A, B)) <=> (r4_lattice3(A, C, B) & (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r4_lattice3(A, D, B) => r1_lattices(A, C, D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d21_lattice3)).
% 7.02/2.37  tff(f_131, axiom, (![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v4_lattice3(A)) & l3_lattices(A)) => (![B]: (k15_lattice3(A, B) = k16_lattice3(A, a_2_2_lattice3(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_lattice3)).
% 7.02/2.37  tff(f_150, axiom, (![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v4_lattice3(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (r2_hidden(B, C) => (r3_lattices(A, B, k15_lattice3(A, C)) & r3_lattices(A, k16_lattice3(A, C), B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_lattice3)).
% 7.02/2.37  tff(f_96, axiom, (![A, B, C]: ((((~v2_struct_0(B) & v10_lattices(B)) & v4_lattice3(B)) & l3_lattices(B)) => (r2_hidden(A, a_2_2_lattice3(B, C)) <=> (?[D]: ((m1_subset_1(D, u1_struct_0(B)) & (A = D)) & r4_lattice3(B, D, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fraenkel_a_2_2_lattice3)).
% 7.02/2.37  tff(f_43, axiom, (![A]: ((~v2_struct_0(A) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (r4_lattice3(A, B, C) <=> (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_hidden(D, C) => r1_lattices(A, D, B)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d17_lattice3)).
% 7.02/2.37  tff(f_119, axiom, (![A, B, C]: ((((~v2_struct_0(B) & v10_lattices(B)) & v4_lattice3(B)) & l3_lattices(B)) => (r2_hidden(A, a_2_5_lattice3(B, C)) <=> (?[D]: ((m1_subset_1(D, u1_struct_0(B)) & (A = D)) & (?[E]: ((m1_subset_1(E, u1_struct_0(B)) & r3_lattices(B, D, E)) & r2_hidden(E, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fraenkel_a_2_5_lattice3)).
% 7.02/2.37  tff(c_60, plain, (~v2_struct_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_191])).
% 7.02/2.37  tff(c_58, plain, (v10_lattices('#skF_6')), inference(cnfTransformation, [status(thm)], [f_191])).
% 7.02/2.37  tff(c_56, plain, (v4_lattice3('#skF_6')), inference(cnfTransformation, [status(thm)], [f_191])).
% 7.02/2.37  tff(c_54, plain, (l3_lattices('#skF_6')), inference(cnfTransformation, [status(thm)], [f_191])).
% 7.02/2.37  tff(c_48, plain, (![A_66, B_68]: (k15_lattice3(A_66, a_2_5_lattice3(A_66, B_68))=k15_lattice3(A_66, B_68) | ~l3_lattices(A_66) | ~v4_lattice3(A_66) | ~v10_lattices(A_66) | v2_struct_0(A_66))), inference(cnfTransformation, [status(thm)], [f_164])).
% 7.02/2.37  tff(c_20, plain, (![A_35, B_36]: (m1_subset_1(k15_lattice3(A_35, B_36), u1_struct_0(A_35)) | ~l3_lattices(A_35) | v2_struct_0(A_35))), inference(cnfTransformation, [status(thm)], [f_78])).
% 7.02/2.37  tff(c_131, plain, (![A_123, B_124]: (r4_lattice3(A_123, k15_lattice3(A_123, B_124), B_124) | ~m1_subset_1(k15_lattice3(A_123, B_124), u1_struct_0(A_123)) | ~v4_lattice3(A_123) | ~v10_lattices(A_123) | ~l3_lattices(A_123) | v2_struct_0(A_123))), inference(cnfTransformation, [status(thm)], [f_71])).
% 7.02/2.37  tff(c_137, plain, (![A_125, B_126]: (r4_lattice3(A_125, k15_lattice3(A_125, B_126), B_126) | ~v4_lattice3(A_125) | ~v10_lattices(A_125) | ~l3_lattices(A_125) | v2_struct_0(A_125))), inference(resolution, [status(thm)], [c_20, c_131])).
% 7.02/2.37  tff(c_140, plain, (![A_66, B_68]: (r4_lattice3(A_66, k15_lattice3(A_66, B_68), a_2_5_lattice3(A_66, B_68)) | ~v4_lattice3(A_66) | ~v10_lattices(A_66) | ~l3_lattices(A_66) | v2_struct_0(A_66) | ~l3_lattices(A_66) | ~v4_lattice3(A_66) | ~v10_lattices(A_66) | v2_struct_0(A_66))), inference(superposition, [status(thm), theory('equality')], [c_48, c_137])).
% 7.02/2.37  tff(c_42, plain, (![A_56, B_58]: (k16_lattice3(A_56, a_2_2_lattice3(A_56, B_58))=k15_lattice3(A_56, B_58) | ~l3_lattices(A_56) | ~v4_lattice3(A_56) | ~v10_lattices(A_56) | v2_struct_0(A_56))), inference(cnfTransformation, [status(thm)], [f_131])).
% 7.02/2.37  tff(c_141, plain, (![A_127, C_128, B_129]: (r3_lattices(A_127, k16_lattice3(A_127, C_128), B_129) | ~r2_hidden(B_129, C_128) | ~m1_subset_1(B_129, u1_struct_0(A_127)) | ~l3_lattices(A_127) | ~v4_lattice3(A_127) | ~v10_lattices(A_127) | v2_struct_0(A_127))), inference(cnfTransformation, [status(thm)], [f_150])).
% 7.02/2.37  tff(c_991, plain, (![A_201, B_202, B_203]: (r3_lattices(A_201, k15_lattice3(A_201, B_202), B_203) | ~r2_hidden(B_203, a_2_2_lattice3(A_201, B_202)) | ~m1_subset_1(B_203, u1_struct_0(A_201)) | ~l3_lattices(A_201) | ~v4_lattice3(A_201) | ~v10_lattices(A_201) | v2_struct_0(A_201) | ~l3_lattices(A_201) | ~v4_lattice3(A_201) | ~v10_lattices(A_201) | v2_struct_0(A_201))), inference(superposition, [status(thm), theory('equality')], [c_42, c_141])).
% 7.02/2.37  tff(c_52, plain, (~r3_lattices('#skF_6', k15_lattice3('#skF_6', '#skF_7'), k15_lattice3('#skF_6', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_191])).
% 7.02/2.37  tff(c_994, plain, (~r2_hidden(k15_lattice3('#skF_6', '#skF_8'), a_2_2_lattice3('#skF_6', '#skF_7')) | ~m1_subset_1(k15_lattice3('#skF_6', '#skF_8'), u1_struct_0('#skF_6')) | ~l3_lattices('#skF_6') | ~v4_lattice3('#skF_6') | ~v10_lattices('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_991, c_52])).
% 7.02/2.37  tff(c_1009, plain, (~r2_hidden(k15_lattice3('#skF_6', '#skF_8'), a_2_2_lattice3('#skF_6', '#skF_7')) | ~m1_subset_1(k15_lattice3('#skF_6', '#skF_8'), u1_struct_0('#skF_6')) | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_994])).
% 7.02/2.37  tff(c_1010, plain, (~r2_hidden(k15_lattice3('#skF_6', '#skF_8'), a_2_2_lattice3('#skF_6', '#skF_7')) | ~m1_subset_1(k15_lattice3('#skF_6', '#skF_8'), u1_struct_0('#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_60, c_1009])).
% 7.02/2.37  tff(c_1020, plain, (~m1_subset_1(k15_lattice3('#skF_6', '#skF_8'), u1_struct_0('#skF_6'))), inference(splitLeft, [status(thm)], [c_1010])).
% 7.02/2.37  tff(c_1023, plain, (~l3_lattices('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_20, c_1020])).
% 7.02/2.37  tff(c_1026, plain, (v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_1023])).
% 7.02/2.37  tff(c_1028, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_1026])).
% 7.02/2.37  tff(c_1030, plain, (m1_subset_1(k15_lattice3('#skF_6', '#skF_8'), u1_struct_0('#skF_6'))), inference(splitRight, [status(thm)], [c_1010])).
% 7.02/2.37  tff(c_22, plain, (![D_42, B_38, C_39]: (r2_hidden(D_42, a_2_2_lattice3(B_38, C_39)) | ~r4_lattice3(B_38, D_42, C_39) | ~m1_subset_1(D_42, u1_struct_0(B_38)) | ~l3_lattices(B_38) | ~v4_lattice3(B_38) | ~v10_lattices(B_38) | v2_struct_0(B_38))), inference(cnfTransformation, [status(thm)], [f_96])).
% 7.02/2.37  tff(c_1029, plain, (~r2_hidden(k15_lattice3('#skF_6', '#skF_8'), a_2_2_lattice3('#skF_6', '#skF_7'))), inference(splitRight, [status(thm)], [c_1010])).
% 7.02/2.37  tff(c_1058, plain, (~r4_lattice3('#skF_6', k15_lattice3('#skF_6', '#skF_8'), '#skF_7') | ~m1_subset_1(k15_lattice3('#skF_6', '#skF_8'), u1_struct_0('#skF_6')) | ~l3_lattices('#skF_6') | ~v4_lattice3('#skF_6') | ~v10_lattices('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_22, c_1029])).
% 7.02/2.37  tff(c_1061, plain, (~r4_lattice3('#skF_6', k15_lattice3('#skF_6', '#skF_8'), '#skF_7') | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_1030, c_1058])).
% 7.02/2.37  tff(c_1062, plain, (~r4_lattice3('#skF_6', k15_lattice3('#skF_6', '#skF_8'), '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_60, c_1061])).
% 7.02/2.37  tff(c_6, plain, (![A_1, B_13, C_19]: (r2_hidden('#skF_1'(A_1, B_13, C_19), C_19) | r4_lattice3(A_1, B_13, C_19) | ~m1_subset_1(B_13, u1_struct_0(A_1)) | ~l3_lattices(A_1) | v2_struct_0(A_1))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.02/2.37  tff(c_8, plain, (![A_1, B_13, C_19]: (m1_subset_1('#skF_1'(A_1, B_13, C_19), u1_struct_0(A_1)) | r4_lattice3(A_1, B_13, C_19) | ~m1_subset_1(B_13, u1_struct_0(A_1)) | ~l3_lattices(A_1) | v2_struct_0(A_1))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.02/2.37  tff(c_66, plain, (![D_80]: (m1_subset_1('#skF_9'(D_80), u1_struct_0('#skF_6')) | ~r2_hidden(D_80, '#skF_7') | ~m1_subset_1(D_80, u1_struct_0('#skF_6')))), inference(cnfTransformation, [status(thm)], [f_191])).
% 7.02/2.37  tff(c_64, plain, (![D_80]: (r3_lattices('#skF_6', D_80, '#skF_9'(D_80)) | ~r2_hidden(D_80, '#skF_7') | ~m1_subset_1(D_80, u1_struct_0('#skF_6')))), inference(cnfTransformation, [status(thm)], [f_191])).
% 7.02/2.37  tff(c_62, plain, (![D_80]: (r2_hidden('#skF_9'(D_80), '#skF_8') | ~r2_hidden(D_80, '#skF_7') | ~m1_subset_1(D_80, u1_struct_0('#skF_6')))), inference(cnfTransformation, [status(thm)], [f_191])).
% 7.02/2.37  tff(c_455, plain, (![D_169, B_170, C_171, E_172]: (r2_hidden(D_169, a_2_5_lattice3(B_170, C_171)) | ~r2_hidden(E_172, C_171) | ~r3_lattices(B_170, D_169, E_172) | ~m1_subset_1(E_172, u1_struct_0(B_170)) | ~m1_subset_1(D_169, u1_struct_0(B_170)) | ~l3_lattices(B_170) | ~v4_lattice3(B_170) | ~v10_lattices(B_170) | v2_struct_0(B_170))), inference(cnfTransformation, [status(thm)], [f_119])).
% 7.02/2.37  tff(c_1368, plain, (![D_212, B_213, D_214]: (r2_hidden(D_212, a_2_5_lattice3(B_213, '#skF_8')) | ~r3_lattices(B_213, D_212, '#skF_9'(D_214)) | ~m1_subset_1('#skF_9'(D_214), u1_struct_0(B_213)) | ~m1_subset_1(D_212, u1_struct_0(B_213)) | ~l3_lattices(B_213) | ~v4_lattice3(B_213) | ~v10_lattices(B_213) | v2_struct_0(B_213) | ~r2_hidden(D_214, '#skF_7') | ~m1_subset_1(D_214, u1_struct_0('#skF_6')))), inference(resolution, [status(thm)], [c_62, c_455])).
% 7.02/2.37  tff(c_1379, plain, (![D_80]: (r2_hidden(D_80, a_2_5_lattice3('#skF_6', '#skF_8')) | ~m1_subset_1('#skF_9'(D_80), u1_struct_0('#skF_6')) | ~l3_lattices('#skF_6') | ~v4_lattice3('#skF_6') | ~v10_lattices('#skF_6') | v2_struct_0('#skF_6') | ~r2_hidden(D_80, '#skF_7') | ~m1_subset_1(D_80, u1_struct_0('#skF_6')))), inference(resolution, [status(thm)], [c_64, c_1368])).
% 7.02/2.37  tff(c_1385, plain, (![D_80]: (r2_hidden(D_80, a_2_5_lattice3('#skF_6', '#skF_8')) | ~m1_subset_1('#skF_9'(D_80), u1_struct_0('#skF_6')) | v2_struct_0('#skF_6') | ~r2_hidden(D_80, '#skF_7') | ~m1_subset_1(D_80, u1_struct_0('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_1379])).
% 7.02/2.37  tff(c_1387, plain, (![D_215]: (r2_hidden(D_215, a_2_5_lattice3('#skF_6', '#skF_8')) | ~m1_subset_1('#skF_9'(D_215), u1_struct_0('#skF_6')) | ~r2_hidden(D_215, '#skF_7') | ~m1_subset_1(D_215, u1_struct_0('#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_60, c_1385])).
% 7.02/2.37  tff(c_1391, plain, (![D_80]: (r2_hidden(D_80, a_2_5_lattice3('#skF_6', '#skF_8')) | ~r2_hidden(D_80, '#skF_7') | ~m1_subset_1(D_80, u1_struct_0('#skF_6')))), inference(resolution, [status(thm)], [c_66, c_1387])).
% 7.02/2.37  tff(c_1392, plain, (![D_216]: (r2_hidden(D_216, a_2_5_lattice3('#skF_6', '#skF_8')) | ~r2_hidden(D_216, '#skF_7') | ~m1_subset_1(D_216, u1_struct_0('#skF_6')))), inference(resolution, [status(thm)], [c_66, c_1387])).
% 7.02/2.37  tff(c_38, plain, (![A_43, B_44, C_45]: ('#skF_4'(A_43, B_44, C_45)=A_43 | ~r2_hidden(A_43, a_2_5_lattice3(B_44, C_45)) | ~l3_lattices(B_44) | ~v4_lattice3(B_44) | ~v10_lattices(B_44) | v2_struct_0(B_44))), inference(cnfTransformation, [status(thm)], [f_119])).
% 7.02/2.37  tff(c_1402, plain, (![D_216]: ('#skF_4'(D_216, '#skF_6', '#skF_8')=D_216 | ~l3_lattices('#skF_6') | ~v4_lattice3('#skF_6') | ~v10_lattices('#skF_6') | v2_struct_0('#skF_6') | ~r2_hidden(D_216, '#skF_7') | ~m1_subset_1(D_216, u1_struct_0('#skF_6')))), inference(resolution, [status(thm)], [c_1392, c_38])).
% 7.02/2.37  tff(c_1410, plain, (![D_216]: ('#skF_4'(D_216, '#skF_6', '#skF_8')=D_216 | v2_struct_0('#skF_6') | ~r2_hidden(D_216, '#skF_7') | ~m1_subset_1(D_216, u1_struct_0('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_1402])).
% 7.02/2.37  tff(c_1412, plain, (![D_217]: ('#skF_4'(D_217, '#skF_6', '#skF_8')=D_217 | ~r2_hidden(D_217, '#skF_7') | ~m1_subset_1(D_217, u1_struct_0('#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_60, c_1410])).
% 7.02/2.37  tff(c_1441, plain, (![B_13, C_19]: ('#skF_4'('#skF_1'('#skF_6', B_13, C_19), '#skF_6', '#skF_8')='#skF_1'('#skF_6', B_13, C_19) | ~r2_hidden('#skF_1'('#skF_6', B_13, C_19), '#skF_7') | r4_lattice3('#skF_6', B_13, C_19) | ~m1_subset_1(B_13, u1_struct_0('#skF_6')) | ~l3_lattices('#skF_6') | v2_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_8, c_1412])).
% 7.02/2.37  tff(c_1470, plain, (![B_13, C_19]: ('#skF_4'('#skF_1'('#skF_6', B_13, C_19), '#skF_6', '#skF_8')='#skF_1'('#skF_6', B_13, C_19) | ~r2_hidden('#skF_1'('#skF_6', B_13, C_19), '#skF_7') | r4_lattice3('#skF_6', B_13, C_19) | ~m1_subset_1(B_13, u1_struct_0('#skF_6')) | v2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_1441])).
% 7.02/2.37  tff(c_3217, plain, (![B_281, C_282]: ('#skF_4'('#skF_1'('#skF_6', B_281, C_282), '#skF_6', '#skF_8')='#skF_1'('#skF_6', B_281, C_282) | ~r2_hidden('#skF_1'('#skF_6', B_281, C_282), '#skF_7') | r4_lattice3('#skF_6', B_281, C_282) | ~m1_subset_1(B_281, u1_struct_0('#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_60, c_1470])).
% 7.02/2.37  tff(c_3221, plain, (![B_13]: ('#skF_4'('#skF_1'('#skF_6', B_13, '#skF_7'), '#skF_6', '#skF_8')='#skF_1'('#skF_6', B_13, '#skF_7') | r4_lattice3('#skF_6', B_13, '#skF_7') | ~m1_subset_1(B_13, u1_struct_0('#skF_6')) | ~l3_lattices('#skF_6') | v2_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_6, c_3217])).
% 7.02/2.37  tff(c_3224, plain, (![B_13]: ('#skF_4'('#skF_1'('#skF_6', B_13, '#skF_7'), '#skF_6', '#skF_8')='#skF_1'('#skF_6', B_13, '#skF_7') | r4_lattice3('#skF_6', B_13, '#skF_7') | ~m1_subset_1(B_13, u1_struct_0('#skF_6')) | v2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_3221])).
% 7.02/2.37  tff(c_3226, plain, (![B_283]: ('#skF_4'('#skF_1'('#skF_6', B_283, '#skF_7'), '#skF_6', '#skF_8')='#skF_1'('#skF_6', B_283, '#skF_7') | r4_lattice3('#skF_6', B_283, '#skF_7') | ~m1_subset_1(B_283, u1_struct_0('#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_60, c_3224])).
% 7.02/2.37  tff(c_3250, plain, ('#skF_4'('#skF_1'('#skF_6', k15_lattice3('#skF_6', '#skF_8'), '#skF_7'), '#skF_6', '#skF_8')='#skF_1'('#skF_6', k15_lattice3('#skF_6', '#skF_8'), '#skF_7') | r4_lattice3('#skF_6', k15_lattice3('#skF_6', '#skF_8'), '#skF_7')), inference(resolution, [status(thm)], [c_1030, c_3226])).
% 7.02/2.37  tff(c_3293, plain, ('#skF_4'('#skF_1'('#skF_6', k15_lattice3('#skF_6', '#skF_8'), '#skF_7'), '#skF_6', '#skF_8')='#skF_1'('#skF_6', k15_lattice3('#skF_6', '#skF_8'), '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_1062, c_3250])).
% 7.02/2.37  tff(c_40, plain, (![A_43, B_44, C_45]: (m1_subset_1('#skF_4'(A_43, B_44, C_45), u1_struct_0(B_44)) | ~r2_hidden(A_43, a_2_5_lattice3(B_44, C_45)) | ~l3_lattices(B_44) | ~v4_lattice3(B_44) | ~v10_lattices(B_44) | v2_struct_0(B_44))), inference(cnfTransformation, [status(thm)], [f_119])).
% 7.02/2.37  tff(c_3331, plain, (m1_subset_1('#skF_1'('#skF_6', k15_lattice3('#skF_6', '#skF_8'), '#skF_7'), u1_struct_0('#skF_6')) | ~r2_hidden('#skF_1'('#skF_6', k15_lattice3('#skF_6', '#skF_8'), '#skF_7'), a_2_5_lattice3('#skF_6', '#skF_8')) | ~l3_lattices('#skF_6') | ~v4_lattice3('#skF_6') | ~v10_lattices('#skF_6') | v2_struct_0('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_3293, c_40])).
% 7.02/2.37  tff(c_3339, plain, (m1_subset_1('#skF_1'('#skF_6', k15_lattice3('#skF_6', '#skF_8'), '#skF_7'), u1_struct_0('#skF_6')) | ~r2_hidden('#skF_1'('#skF_6', k15_lattice3('#skF_6', '#skF_8'), '#skF_7'), a_2_5_lattice3('#skF_6', '#skF_8')) | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_3331])).
% 7.02/2.37  tff(c_3340, plain, (m1_subset_1('#skF_1'('#skF_6', k15_lattice3('#skF_6', '#skF_8'), '#skF_7'), u1_struct_0('#skF_6')) | ~r2_hidden('#skF_1'('#skF_6', k15_lattice3('#skF_6', '#skF_8'), '#skF_7'), a_2_5_lattice3('#skF_6', '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_60, c_3339])).
% 7.02/2.37  tff(c_3342, plain, (~r2_hidden('#skF_1'('#skF_6', k15_lattice3('#skF_6', '#skF_8'), '#skF_7'), a_2_5_lattice3('#skF_6', '#skF_8'))), inference(splitLeft, [status(thm)], [c_3340])).
% 7.02/2.37  tff(c_3355, plain, (~r2_hidden('#skF_1'('#skF_6', k15_lattice3('#skF_6', '#skF_8'), '#skF_7'), '#skF_7') | ~m1_subset_1('#skF_1'('#skF_6', k15_lattice3('#skF_6', '#skF_8'), '#skF_7'), u1_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_1391, c_3342])).
% 7.02/2.37  tff(c_3356, plain, (~m1_subset_1('#skF_1'('#skF_6', k15_lattice3('#skF_6', '#skF_8'), '#skF_7'), u1_struct_0('#skF_6'))), inference(splitLeft, [status(thm)], [c_3355])).
% 7.02/2.37  tff(c_3359, plain, (r4_lattice3('#skF_6', k15_lattice3('#skF_6', '#skF_8'), '#skF_7') | ~m1_subset_1(k15_lattice3('#skF_6', '#skF_8'), u1_struct_0('#skF_6')) | ~l3_lattices('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_8, c_3356])).
% 7.02/2.37  tff(c_3362, plain, (r4_lattice3('#skF_6', k15_lattice3('#skF_6', '#skF_8'), '#skF_7') | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_1030, c_3359])).
% 7.02/2.37  tff(c_3364, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_1062, c_3362])).
% 7.02/2.37  tff(c_3365, plain, (~r2_hidden('#skF_1'('#skF_6', k15_lattice3('#skF_6', '#skF_8'), '#skF_7'), '#skF_7')), inference(splitRight, [status(thm)], [c_3355])).
% 7.02/2.37  tff(c_3429, plain, (r4_lattice3('#skF_6', k15_lattice3('#skF_6', '#skF_8'), '#skF_7') | ~m1_subset_1(k15_lattice3('#skF_6', '#skF_8'), u1_struct_0('#skF_6')) | ~l3_lattices('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_6, c_3365])).
% 7.02/2.37  tff(c_3432, plain, (r4_lattice3('#skF_6', k15_lattice3('#skF_6', '#skF_8'), '#skF_7') | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_1030, c_3429])).
% 7.02/2.37  tff(c_3434, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_1062, c_3432])).
% 7.02/2.37  tff(c_3435, plain, (m1_subset_1('#skF_1'('#skF_6', k15_lattice3('#skF_6', '#skF_8'), '#skF_7'), u1_struct_0('#skF_6'))), inference(splitRight, [status(thm)], [c_3340])).
% 7.02/2.37  tff(c_2, plain, (![A_1, D_22, B_13, C_19]: (r1_lattices(A_1, D_22, B_13) | ~r2_hidden(D_22, C_19) | ~m1_subset_1(D_22, u1_struct_0(A_1)) | ~r4_lattice3(A_1, B_13, C_19) | ~m1_subset_1(B_13, u1_struct_0(A_1)) | ~l3_lattices(A_1) | v2_struct_0(A_1))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.02/2.37  tff(c_5472, plain, (![A_358, D_359, B_360]: (r1_lattices(A_358, D_359, B_360) | ~m1_subset_1(D_359, u1_struct_0(A_358)) | ~r4_lattice3(A_358, B_360, a_2_5_lattice3('#skF_6', '#skF_8')) | ~m1_subset_1(B_360, u1_struct_0(A_358)) | ~l3_lattices(A_358) | v2_struct_0(A_358) | ~r2_hidden(D_359, '#skF_7') | ~m1_subset_1(D_359, u1_struct_0('#skF_6')))), inference(resolution, [status(thm)], [c_1392, c_2])).
% 7.02/2.37  tff(c_5484, plain, (![B_360]: (r1_lattices('#skF_6', '#skF_1'('#skF_6', k15_lattice3('#skF_6', '#skF_8'), '#skF_7'), B_360) | ~r4_lattice3('#skF_6', B_360, a_2_5_lattice3('#skF_6', '#skF_8')) | ~m1_subset_1(B_360, u1_struct_0('#skF_6')) | ~l3_lattices('#skF_6') | v2_struct_0('#skF_6') | ~r2_hidden('#skF_1'('#skF_6', k15_lattice3('#skF_6', '#skF_8'), '#skF_7'), '#skF_7') | ~m1_subset_1('#skF_1'('#skF_6', k15_lattice3('#skF_6', '#skF_8'), '#skF_7'), u1_struct_0('#skF_6')))), inference(resolution, [status(thm)], [c_3435, c_5472])).
% 7.02/2.37  tff(c_5541, plain, (![B_360]: (r1_lattices('#skF_6', '#skF_1'('#skF_6', k15_lattice3('#skF_6', '#skF_8'), '#skF_7'), B_360) | ~r4_lattice3('#skF_6', B_360, a_2_5_lattice3('#skF_6', '#skF_8')) | ~m1_subset_1(B_360, u1_struct_0('#skF_6')) | v2_struct_0('#skF_6') | ~r2_hidden('#skF_1'('#skF_6', k15_lattice3('#skF_6', '#skF_8'), '#skF_7'), '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_3435, c_54, c_5484])).
% 7.02/2.37  tff(c_5542, plain, (![B_360]: (r1_lattices('#skF_6', '#skF_1'('#skF_6', k15_lattice3('#skF_6', '#skF_8'), '#skF_7'), B_360) | ~r4_lattice3('#skF_6', B_360, a_2_5_lattice3('#skF_6', '#skF_8')) | ~m1_subset_1(B_360, u1_struct_0('#skF_6')) | ~r2_hidden('#skF_1'('#skF_6', k15_lattice3('#skF_6', '#skF_8'), '#skF_7'), '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_60, c_5541])).
% 7.02/2.37  tff(c_5616, plain, (~r2_hidden('#skF_1'('#skF_6', k15_lattice3('#skF_6', '#skF_8'), '#skF_7'), '#skF_7')), inference(splitLeft, [status(thm)], [c_5542])).
% 7.02/2.37  tff(c_5648, plain, (r4_lattice3('#skF_6', k15_lattice3('#skF_6', '#skF_8'), '#skF_7') | ~m1_subset_1(k15_lattice3('#skF_6', '#skF_8'), u1_struct_0('#skF_6')) | ~l3_lattices('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_6, c_5616])).
% 7.02/2.37  tff(c_5651, plain, (r4_lattice3('#skF_6', k15_lattice3('#skF_6', '#skF_8'), '#skF_7') | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_1030, c_5648])).
% 7.02/2.37  tff(c_5653, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_1062, c_5651])).
% 7.02/2.37  tff(c_5669, plain, (![B_368]: (r1_lattices('#skF_6', '#skF_1'('#skF_6', k15_lattice3('#skF_6', '#skF_8'), '#skF_7'), B_368) | ~r4_lattice3('#skF_6', B_368, a_2_5_lattice3('#skF_6', '#skF_8')) | ~m1_subset_1(B_368, u1_struct_0('#skF_6')))), inference(splitRight, [status(thm)], [c_5542])).
% 7.02/2.37  tff(c_4, plain, (![A_1, B_13, C_19]: (~r1_lattices(A_1, '#skF_1'(A_1, B_13, C_19), B_13) | r4_lattice3(A_1, B_13, C_19) | ~m1_subset_1(B_13, u1_struct_0(A_1)) | ~l3_lattices(A_1) | v2_struct_0(A_1))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.02/2.37  tff(c_5677, plain, (r4_lattice3('#skF_6', k15_lattice3('#skF_6', '#skF_8'), '#skF_7') | ~l3_lattices('#skF_6') | v2_struct_0('#skF_6') | ~r4_lattice3('#skF_6', k15_lattice3('#skF_6', '#skF_8'), a_2_5_lattice3('#skF_6', '#skF_8')) | ~m1_subset_1(k15_lattice3('#skF_6', '#skF_8'), u1_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_5669, c_4])).
% 7.02/2.37  tff(c_5684, plain, (r4_lattice3('#skF_6', k15_lattice3('#skF_6', '#skF_8'), '#skF_7') | v2_struct_0('#skF_6') | ~r4_lattice3('#skF_6', k15_lattice3('#skF_6', '#skF_8'), a_2_5_lattice3('#skF_6', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_1030, c_54, c_5677])).
% 7.02/2.37  tff(c_5685, plain, (~r4_lattice3('#skF_6', k15_lattice3('#skF_6', '#skF_8'), a_2_5_lattice3('#skF_6', '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_60, c_1062, c_5684])).
% 7.02/2.37  tff(c_5688, plain, (~l3_lattices('#skF_6') | ~v4_lattice3('#skF_6') | ~v10_lattices('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_140, c_5685])).
% 7.02/2.37  tff(c_5691, plain, (v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_5688])).
% 7.02/2.37  tff(c_5693, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_5691])).
% 7.02/2.37  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.02/2.37  
% 7.02/2.37  Inference rules
% 7.02/2.37  ----------------------
% 7.02/2.37  #Ref     : 0
% 7.02/2.37  #Sup     : 1105
% 7.02/2.37  #Fact    : 0
% 7.02/2.37  #Define  : 0
% 7.02/2.37  #Split   : 11
% 7.02/2.37  #Chain   : 0
% 7.02/2.37  #Close   : 0
% 7.02/2.37  
% 7.02/2.37  Ordering : KBO
% 7.02/2.37  
% 7.02/2.37  Simplification rules
% 7.02/2.37  ----------------------
% 7.02/2.37  #Subsume      : 412
% 7.02/2.37  #Demod        : 2157
% 7.02/2.37  #Tautology    : 169
% 7.02/2.37  #SimpNegUnit  : 365
% 7.02/2.37  #BackRed      : 0
% 7.02/2.37  
% 7.02/2.37  #Partial instantiations: 0
% 7.02/2.37  #Strategies tried      : 1
% 7.02/2.37  
% 7.02/2.37  Timing (in seconds)
% 7.02/2.37  ----------------------
% 7.02/2.38  Preprocessing        : 0.34
% 7.02/2.38  Parsing              : 0.18
% 7.02/2.38  CNF conversion       : 0.03
% 7.02/2.38  Main loop            : 1.26
% 7.02/2.38  Inferencing          : 0.44
% 7.02/2.38  Reduction            : 0.46
% 7.02/2.38  Demodulation         : 0.33
% 7.02/2.38  BG Simplification    : 0.05
% 7.02/2.38  Subsumption          : 0.25
% 7.02/2.38  Abstraction          : 0.06
% 7.02/2.38  MUC search           : 0.00
% 7.02/2.38  Cooper               : 0.00
% 7.02/2.38  Total                : 1.64
% 7.02/2.38  Index Insertion      : 0.00
% 7.02/2.38  Index Deletion       : 0.00
% 7.02/2.38  Index Matching       : 0.00
% 7.02/2.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
