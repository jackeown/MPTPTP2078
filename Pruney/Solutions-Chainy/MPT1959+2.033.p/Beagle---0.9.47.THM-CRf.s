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
% DateTime   : Thu Dec  3 10:31:02 EST 2020

% Result     : Theorem 12.89s
% Output     : CNFRefutation 12.89s
% Verified   : 
% Statistics : Number of formulae       :  194 (2476 expanded)
%              Number of leaves         :   45 ( 852 expanded)
%              Depth                    :   26
%              Number of atoms          :  510 (8451 expanded)
%              Number of equality atoms :   71 ( 749 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_lattice3 > r1_orders_2 > r1_lattice3 > v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_yellow_0 > r2_hidden > r1_yellow_0 > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_yellow_0 > v1_xboole_0 > l1_orders_2 > k1_yellow_0 > #nlpp > u1_struct_0 > k3_yellow_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_7 > #skF_6 > #skF_3 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k1_yellow_0,type,(
    k1_yellow_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

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

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r2_lattice3,type,(
    r2_lattice3: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r2_yellow_0,type,(
    r2_yellow_0: ( $i * $i ) > $o )).

tff(r1_lattice3,type,(
    r1_lattice3: ( $i * $i * $i ) > $o )).

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v13_waybel_0,type,(
    v13_waybel_0: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(v1_yellow_0,type,(
    v1_yellow_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_52,axiom,(
    ! [A] :
    ? [B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
      & ~ v1_subset_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc3_subset_1)).

tff(f_138,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( v1_subset_1(B,A)
      <=> B != A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).

tff(f_167,negated_conjecture,(
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

tff(f_46,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( ! [D] :
                ( m1_subset_1(D,A)
               => ( r2_hidden(D,B)
                <=> r2_hidden(D,C) ) )
           => B = C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_subset_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_58,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_112,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ( r2_lattice3(A,k1_xboole_0,B)
            & r1_lattice3(A,k1_xboole_0,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_yellow_0)).

tff(f_68,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => k3_yellow_0(A) = k1_yellow_0(A,k1_xboole_0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_yellow_0)).

tff(f_90,axiom,(
    ! [A,B] :
      ( l1_orders_2(A)
     => m1_subset_1(k1_yellow_0(A,B),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_yellow_0)).

tff(f_103,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v5_orders_2(A)
        & v1_yellow_0(A)
        & l1_orders_2(A) )
     => ( r1_yellow_0(A,k1_xboole_0)
        & r2_yellow_0(A,u1_struct_0(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_yellow_0)).

tff(f_86,axiom,(
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

tff(f_131,axiom,(
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

tff(c_14,plain,(
    ! [A_12] : ~ v1_subset_1('#skF_2'(A_12),A_12) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_16,plain,(
    ! [A_12] : m1_subset_1('#skF_2'(A_12),k1_zfmisc_1(A_12)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_153,plain,(
    ! [B_83,A_84] :
      ( v1_subset_1(B_83,A_84)
      | B_83 = A_84
      | ~ m1_subset_1(B_83,k1_zfmisc_1(A_84)) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_156,plain,(
    ! [A_12] :
      ( v1_subset_1('#skF_2'(A_12),A_12)
      | '#skF_2'(A_12) = A_12 ) ),
    inference(resolution,[status(thm)],[c_16,c_153])).

tff(c_162,plain,(
    ! [A_12] : '#skF_2'(A_12) = A_12 ),
    inference(negUnitSimplification,[status(thm)],[c_14,c_156])).

tff(c_166,plain,(
    ! [A_12] : ~ v1_subset_1(A_12,A_12) ),
    inference(demodulation,[status(thm),theory(equality)],[c_162,c_14])).

tff(c_165,plain,(
    ! [A_12] : m1_subset_1(A_12,k1_zfmisc_1(A_12)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_162,c_16])).

tff(c_66,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_740,plain,(
    ! [A_174,B_175,C_176] :
      ( r2_hidden('#skF_1'(A_174,B_175,C_176),B_175)
      | r2_hidden('#skF_1'(A_174,B_175,C_176),C_176)
      | C_176 = B_175
      | ~ m1_subset_1(C_176,k1_zfmisc_1(A_174))
      | ~ m1_subset_1(B_175,k1_zfmisc_1(A_174)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_2,plain,(
    ! [C_4,A_1,B_2] :
      ( r2_hidden(C_4,A_1)
      | ~ r2_hidden(C_4,B_2)
      | ~ m1_subset_1(B_2,k1_zfmisc_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_2140,plain,(
    ! [A_318,B_319,C_320,A_321] :
      ( r2_hidden('#skF_1'(A_318,B_319,C_320),A_321)
      | ~ m1_subset_1(B_319,k1_zfmisc_1(A_321))
      | r2_hidden('#skF_1'(A_318,B_319,C_320),C_320)
      | C_320 = B_319
      | ~ m1_subset_1(C_320,k1_zfmisc_1(A_318))
      | ~ m1_subset_1(B_319,k1_zfmisc_1(A_318)) ) ),
    inference(resolution,[status(thm)],[c_740,c_2])).

tff(c_213,plain,(
    ! [A_96,C_97,B_98] :
      ( m1_subset_1(A_96,C_97)
      | ~ m1_subset_1(B_98,k1_zfmisc_1(C_97))
      | ~ r2_hidden(A_96,B_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_218,plain,(
    ! [A_96,A_12] :
      ( m1_subset_1(A_96,A_12)
      | ~ r2_hidden(A_96,A_12) ) ),
    inference(resolution,[status(thm)],[c_165,c_213])).

tff(c_15169,plain,(
    ! [A_827,B_828,C_829,A_830] :
      ( m1_subset_1('#skF_1'(A_827,B_828,C_829),C_829)
      | r2_hidden('#skF_1'(A_827,B_828,C_829),A_830)
      | ~ m1_subset_1(B_828,k1_zfmisc_1(A_830))
      | C_829 = B_828
      | ~ m1_subset_1(C_829,k1_zfmisc_1(A_827))
      | ~ m1_subset_1(B_828,k1_zfmisc_1(A_827)) ) ),
    inference(resolution,[status(thm)],[c_2140,c_218])).

tff(c_16293,plain,(
    ! [A_842,B_843,C_844,A_845] :
      ( m1_subset_1('#skF_1'(A_842,B_843,C_844),A_845)
      | m1_subset_1('#skF_1'(A_842,B_843,C_844),C_844)
      | ~ m1_subset_1(B_843,k1_zfmisc_1(A_845))
      | C_844 = B_843
      | ~ m1_subset_1(C_844,k1_zfmisc_1(A_842))
      | ~ m1_subset_1(B_843,k1_zfmisc_1(A_842)) ) ),
    inference(resolution,[status(thm)],[c_15169,c_218])).

tff(c_60,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_18,plain,(
    ! [A_14,B_15] :
      ( r2_hidden(A_14,B_15)
      | v1_xboole_0(B_15)
      | ~ m1_subset_1(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_202,plain,(
    ! [C_92,A_93,B_94] :
      ( r2_hidden(C_92,A_93)
      | ~ r2_hidden(C_92,B_94)
      | ~ m1_subset_1(B_94,k1_zfmisc_1(A_93)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_287,plain,(
    ! [A_111,A_112,B_113] :
      ( r2_hidden(A_111,A_112)
      | ~ m1_subset_1(B_113,k1_zfmisc_1(A_112))
      | v1_xboole_0(B_113)
      | ~ m1_subset_1(A_111,B_113) ) ),
    inference(resolution,[status(thm)],[c_18,c_202])).

tff(c_294,plain,(
    ! [A_111] :
      ( r2_hidden(A_111,u1_struct_0('#skF_6'))
      | v1_xboole_0('#skF_7')
      | ~ m1_subset_1(A_111,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_60,c_287])).

tff(c_299,plain,(
    ! [A_111] :
      ( r2_hidden(A_111,u1_struct_0('#skF_6'))
      | ~ m1_subset_1(A_111,'#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_294])).

tff(c_68,plain,(
    l1_orders_2('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_300,plain,(
    ! [A_114] :
      ( r2_hidden(A_114,u1_struct_0('#skF_6'))
      | ~ m1_subset_1(A_114,'#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_294])).

tff(c_308,plain,(
    ! [A_115] :
      ( m1_subset_1(A_115,u1_struct_0('#skF_6'))
      | ~ m1_subset_1(A_115,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_300,c_218])).

tff(c_42,plain,(
    ! [A_35,B_37] :
      ( r2_lattice3(A_35,k1_xboole_0,B_37)
      | ~ m1_subset_1(B_37,u1_struct_0(A_35))
      | ~ l1_orders_2(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_311,plain,(
    ! [A_115] :
      ( r2_lattice3('#skF_6',k1_xboole_0,A_115)
      | ~ l1_orders_2('#skF_6')
      | ~ m1_subset_1(A_115,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_308,c_42])).

tff(c_317,plain,(
    ! [A_115] :
      ( r2_lattice3('#skF_6',k1_xboole_0,A_115)
      | ~ m1_subset_1(A_115,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_311])).

tff(c_306,plain,(
    ! [A_114] :
      ( m1_subset_1(A_114,u1_struct_0('#skF_6'))
      | ~ m1_subset_1(A_114,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_300,c_218])).

tff(c_62,plain,(
    v13_waybel_0('#skF_7','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_107,plain,(
    ! [A_72,B_73] :
      ( r2_hidden(A_72,B_73)
      | v1_xboole_0(B_73)
      | ~ m1_subset_1(A_72,B_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_86,plain,
    ( v1_subset_1('#skF_7',u1_struct_0('#skF_6'))
    | ~ r2_hidden(k3_yellow_0('#skF_6'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_105,plain,(
    ~ r2_hidden(k3_yellow_0('#skF_6'),'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_86])).

tff(c_110,plain,
    ( v1_xboole_0('#skF_7')
    | ~ m1_subset_1(k3_yellow_0('#skF_6'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_107,c_105])).

tff(c_113,plain,(
    ~ m1_subset_1(k3_yellow_0('#skF_6'),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_110])).

tff(c_80,plain,
    ( r2_hidden(k3_yellow_0('#skF_6'),'#skF_7')
    | ~ v1_subset_1('#skF_7',u1_struct_0('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_106,plain,(
    ~ v1_subset_1('#skF_7',u1_struct_0('#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_105,c_80])).

tff(c_114,plain,(
    ! [B_74,A_75] :
      ( v1_subset_1(B_74,A_75)
      | B_74 = A_75
      | ~ m1_subset_1(B_74,k1_zfmisc_1(A_75)) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_120,plain,
    ( v1_subset_1('#skF_7',u1_struct_0('#skF_6'))
    | u1_struct_0('#skF_6') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_60,c_114])).

tff(c_126,plain,(
    u1_struct_0('#skF_6') = '#skF_7' ),
    inference(negUnitSimplification,[status(thm)],[c_106,c_120])).

tff(c_89,plain,(
    ! [A_68] :
      ( k1_yellow_0(A_68,k1_xboole_0) = k3_yellow_0(A_68)
      | ~ l1_orders_2(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_93,plain,(
    k1_yellow_0('#skF_6',k1_xboole_0) = k3_yellow_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_68,c_89])).

tff(c_99,plain,(
    ! [A_70,B_71] :
      ( m1_subset_1(k1_yellow_0(A_70,B_71),u1_struct_0(A_70))
      | ~ l1_orders_2(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_102,plain,
    ( m1_subset_1(k3_yellow_0('#skF_6'),u1_struct_0('#skF_6'))
    | ~ l1_orders_2('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_93,c_99])).

tff(c_104,plain,(
    m1_subset_1(k3_yellow_0('#skF_6'),u1_struct_0('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_102])).

tff(c_144,plain,(
    m1_subset_1(k3_yellow_0('#skF_6'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_104])).

tff(c_147,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_113,c_144])).

tff(c_149,plain,(
    r2_hidden(k3_yellow_0('#skF_6'),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_86])).

tff(c_78,plain,(
    ~ v2_struct_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_72,plain,(
    v5_orders_2('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_70,plain,(
    v1_yellow_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_38,plain,(
    ! [A_34] :
      ( r1_yellow_0(A_34,k1_xboole_0)
      | ~ l1_orders_2(A_34)
      | ~ v1_yellow_0(A_34)
      | ~ v5_orders_2(A_34)
      | v2_struct_0(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_1354,plain,(
    ! [A_259,B_260,D_261] :
      ( r1_orders_2(A_259,k1_yellow_0(A_259,B_260),D_261)
      | ~ r2_lattice3(A_259,B_260,D_261)
      | ~ m1_subset_1(D_261,u1_struct_0(A_259))
      | ~ r1_yellow_0(A_259,B_260)
      | ~ m1_subset_1(k1_yellow_0(A_259,B_260),u1_struct_0(A_259))
      | ~ l1_orders_2(A_259) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_1364,plain,(
    ! [D_261] :
      ( r1_orders_2('#skF_6',k1_yellow_0('#skF_6',k1_xboole_0),D_261)
      | ~ r2_lattice3('#skF_6',k1_xboole_0,D_261)
      | ~ m1_subset_1(D_261,u1_struct_0('#skF_6'))
      | ~ r1_yellow_0('#skF_6',k1_xboole_0)
      | ~ m1_subset_1(k3_yellow_0('#skF_6'),u1_struct_0('#skF_6'))
      | ~ l1_orders_2('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_93,c_1354])).

tff(c_1373,plain,(
    ! [D_261] :
      ( r1_orders_2('#skF_6',k3_yellow_0('#skF_6'),D_261)
      | ~ r2_lattice3('#skF_6',k1_xboole_0,D_261)
      | ~ m1_subset_1(D_261,u1_struct_0('#skF_6'))
      | ~ r1_yellow_0('#skF_6',k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_104,c_93,c_1364])).

tff(c_1374,plain,(
    ~ r1_yellow_0('#skF_6',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_1373])).

tff(c_1377,plain,
    ( ~ l1_orders_2('#skF_6')
    | ~ v1_yellow_0('#skF_6')
    | ~ v5_orders_2('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_38,c_1374])).

tff(c_1380,plain,(
    v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_68,c_1377])).

tff(c_1382,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_1380])).

tff(c_1383,plain,(
    ! [D_261] :
      ( r1_orders_2('#skF_6',k3_yellow_0('#skF_6'),D_261)
      | ~ r2_lattice3('#skF_6',k1_xboole_0,D_261)
      | ~ m1_subset_1(D_261,u1_struct_0('#skF_6')) ) ),
    inference(splitRight,[status(thm)],[c_1373])).

tff(c_1431,plain,(
    ! [D_273,B_274,A_275,C_276] :
      ( r2_hidden(D_273,B_274)
      | ~ r1_orders_2(A_275,C_276,D_273)
      | ~ r2_hidden(C_276,B_274)
      | ~ m1_subset_1(D_273,u1_struct_0(A_275))
      | ~ m1_subset_1(C_276,u1_struct_0(A_275))
      | ~ v13_waybel_0(B_274,A_275)
      | ~ m1_subset_1(B_274,k1_zfmisc_1(u1_struct_0(A_275)))
      | ~ l1_orders_2(A_275) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_1437,plain,(
    ! [D_261,B_274] :
      ( r2_hidden(D_261,B_274)
      | ~ r2_hidden(k3_yellow_0('#skF_6'),B_274)
      | ~ m1_subset_1(k3_yellow_0('#skF_6'),u1_struct_0('#skF_6'))
      | ~ v13_waybel_0(B_274,'#skF_6')
      | ~ m1_subset_1(B_274,k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ l1_orders_2('#skF_6')
      | ~ r2_lattice3('#skF_6',k1_xboole_0,D_261)
      | ~ m1_subset_1(D_261,u1_struct_0('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_1383,c_1431])).

tff(c_1453,plain,(
    ! [D_277,B_278] :
      ( r2_hidden(D_277,B_278)
      | ~ r2_hidden(k3_yellow_0('#skF_6'),B_278)
      | ~ v13_waybel_0(B_278,'#skF_6')
      | ~ m1_subset_1(B_278,k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ r2_lattice3('#skF_6',k1_xboole_0,D_277)
      | ~ m1_subset_1(D_277,u1_struct_0('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_104,c_1437])).

tff(c_1482,plain,(
    ! [D_277] :
      ( r2_hidden(D_277,'#skF_7')
      | ~ r2_hidden(k3_yellow_0('#skF_6'),'#skF_7')
      | ~ v13_waybel_0('#skF_7','#skF_6')
      | ~ r2_lattice3('#skF_6',k1_xboole_0,D_277)
      | ~ m1_subset_1(D_277,u1_struct_0('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_60,c_1453])).

tff(c_1497,plain,(
    ! [D_279] :
      ( r2_hidden(D_279,'#skF_7')
      | ~ r2_lattice3('#skF_6',k1_xboole_0,D_279)
      | ~ m1_subset_1(D_279,u1_struct_0('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_149,c_1482])).

tff(c_1595,plain,(
    ! [A_280] :
      ( r2_hidden(A_280,'#skF_7')
      | ~ r2_lattice3('#skF_6',k1_xboole_0,A_280)
      | ~ m1_subset_1(A_280,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_306,c_1497])).

tff(c_1696,plain,(
    ! [A_282] :
      ( r2_hidden(A_282,'#skF_7')
      | ~ m1_subset_1(A_282,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_317,c_1595])).

tff(c_6,plain,(
    ! [A_5,B_6,C_10] :
      ( ~ r2_hidden('#skF_1'(A_5,B_6,C_10),C_10)
      | ~ r2_hidden('#skF_1'(A_5,B_6,C_10),B_6)
      | C_10 = B_6
      | ~ m1_subset_1(C_10,k1_zfmisc_1(A_5))
      | ~ m1_subset_1(B_6,k1_zfmisc_1(A_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_4550,plain,(
    ! [A_432,B_433] :
      ( ~ r2_hidden('#skF_1'(A_432,B_433,'#skF_7'),B_433)
      | B_433 = '#skF_7'
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(A_432))
      | ~ m1_subset_1(B_433,k1_zfmisc_1(A_432))
      | ~ m1_subset_1('#skF_1'(A_432,B_433,'#skF_7'),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_1696,c_6])).

tff(c_4644,plain,(
    ! [A_432] :
      ( u1_struct_0('#skF_6') = '#skF_7'
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(A_432))
      | ~ m1_subset_1(u1_struct_0('#skF_6'),k1_zfmisc_1(A_432))
      | ~ m1_subset_1('#skF_1'(A_432,u1_struct_0('#skF_6'),'#skF_7'),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_299,c_4550])).

tff(c_4646,plain,(
    ! [A_432] :
      ( ~ m1_subset_1('#skF_7',k1_zfmisc_1(A_432))
      | ~ m1_subset_1(u1_struct_0('#skF_6'),k1_zfmisc_1(A_432))
      | ~ m1_subset_1('#skF_1'(A_432,u1_struct_0('#skF_6'),'#skF_7'),'#skF_7') ) ),
    inference(splitLeft,[status(thm)],[c_4644])).

tff(c_16743,plain,(
    ! [A_842,A_845] :
      ( m1_subset_1('#skF_1'(A_842,u1_struct_0('#skF_6'),'#skF_7'),A_845)
      | ~ m1_subset_1(u1_struct_0('#skF_6'),k1_zfmisc_1(A_845))
      | u1_struct_0('#skF_6') = '#skF_7'
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(A_842))
      | ~ m1_subset_1(u1_struct_0('#skF_6'),k1_zfmisc_1(A_842)) ) ),
    inference(resolution,[status(thm)],[c_16293,c_4646])).

tff(c_17050,plain,(
    u1_struct_0('#skF_6') = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_16743])).

tff(c_219,plain,(
    ! [A_96] :
      ( m1_subset_1(A_96,u1_struct_0('#skF_6'))
      | ~ r2_hidden(A_96,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_60,c_213])).

tff(c_4,plain,(
    ! [A_5,B_6,C_10] :
      ( m1_subset_1('#skF_1'(A_5,B_6,C_10),A_5)
      | C_10 = B_6
      | ~ m1_subset_1(C_10,k1_zfmisc_1(A_5))
      | ~ m1_subset_1(B_6,k1_zfmisc_1(A_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_817,plain,(
    ! [A_190,B_191,C_192] :
      ( ~ r2_hidden('#skF_1'(A_190,B_191,C_192),C_192)
      | ~ r2_hidden('#skF_1'(A_190,B_191,C_192),B_191)
      | C_192 = B_191
      | ~ m1_subset_1(C_192,k1_zfmisc_1(A_190))
      | ~ m1_subset_1(B_191,k1_zfmisc_1(A_190)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_1289,plain,(
    ! [A_244,B_245,B_246] :
      ( ~ r2_hidden('#skF_1'(A_244,B_245,B_246),B_245)
      | B_246 = B_245
      | ~ m1_subset_1(B_246,k1_zfmisc_1(A_244))
      | ~ m1_subset_1(B_245,k1_zfmisc_1(A_244))
      | v1_xboole_0(B_246)
      | ~ m1_subset_1('#skF_1'(A_244,B_245,B_246),B_246) ) ),
    inference(resolution,[status(thm)],[c_18,c_817])).

tff(c_2940,plain,(
    ! [B_368,B_367,A_369] :
      ( B_368 = B_367
      | ~ m1_subset_1(B_367,k1_zfmisc_1(A_369))
      | ~ m1_subset_1(B_368,k1_zfmisc_1(A_369))
      | v1_xboole_0(B_367)
      | ~ m1_subset_1('#skF_1'(A_369,B_368,B_367),B_367)
      | v1_xboole_0(B_368)
      | ~ m1_subset_1('#skF_1'(A_369,B_368,B_367),B_368) ) ),
    inference(resolution,[status(thm)],[c_18,c_1289])).

tff(c_2954,plain,(
    ! [A_5,B_6] :
      ( v1_xboole_0(A_5)
      | v1_xboole_0(B_6)
      | ~ m1_subset_1('#skF_1'(A_5,B_6,A_5),B_6)
      | B_6 = A_5
      | ~ m1_subset_1(A_5,k1_zfmisc_1(A_5))
      | ~ m1_subset_1(B_6,k1_zfmisc_1(A_5)) ) ),
    inference(resolution,[status(thm)],[c_4,c_2940])).

tff(c_2973,plain,(
    ! [A_370,B_371] :
      ( v1_xboole_0(A_370)
      | v1_xboole_0(B_371)
      | ~ m1_subset_1('#skF_1'(A_370,B_371,A_370),B_371)
      | B_371 = A_370
      | ~ m1_subset_1(B_371,k1_zfmisc_1(A_370)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_165,c_2954])).

tff(c_3024,plain,(
    ! [A_370] :
      ( v1_xboole_0(A_370)
      | v1_xboole_0(u1_struct_0('#skF_6'))
      | u1_struct_0('#skF_6') = A_370
      | ~ m1_subset_1(u1_struct_0('#skF_6'),k1_zfmisc_1(A_370))
      | ~ r2_hidden('#skF_1'(A_370,u1_struct_0('#skF_6'),A_370),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_219,c_2973])).

tff(c_3135,plain,(
    v1_xboole_0(u1_struct_0('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_3024])).

tff(c_17100,plain,(
    v1_xboole_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_17050,c_3135])).

tff(c_17138,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_17100])).

tff(c_17140,plain,(
    u1_struct_0('#skF_6') != '#skF_7' ),
    inference(splitRight,[status(thm)],[c_16743])).

tff(c_431,plain,(
    ! [A_136,B_137,C_138] :
      ( m1_subset_1('#skF_1'(A_136,B_137,C_138),A_136)
      | C_138 = B_137
      | ~ m1_subset_1(C_138,k1_zfmisc_1(A_136))
      | ~ m1_subset_1(B_137,k1_zfmisc_1(A_136)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_459,plain,(
    ! [A_35,B_137,C_138] :
      ( r2_lattice3(A_35,k1_xboole_0,'#skF_1'(u1_struct_0(A_35),B_137,C_138))
      | ~ l1_orders_2(A_35)
      | C_138 = B_137
      | ~ m1_subset_1(C_138,k1_zfmisc_1(u1_struct_0(A_35)))
      | ~ m1_subset_1(B_137,k1_zfmisc_1(u1_struct_0(A_35))) ) ),
    inference(resolution,[status(thm)],[c_431,c_42])).

tff(c_17141,plain,(
    ! [A_850,A_851] :
      ( m1_subset_1('#skF_1'(A_850,u1_struct_0('#skF_6'),'#skF_7'),A_851)
      | ~ m1_subset_1(u1_struct_0('#skF_6'),k1_zfmisc_1(A_851))
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(A_850))
      | ~ m1_subset_1(u1_struct_0('#skF_6'),k1_zfmisc_1(A_850)) ) ),
    inference(splitRight,[status(thm)],[c_16743])).

tff(c_1496,plain,(
    ! [D_277] :
      ( r2_hidden(D_277,'#skF_7')
      | ~ r2_lattice3('#skF_6',k1_xboole_0,D_277)
      | ~ m1_subset_1(D_277,u1_struct_0('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_149,c_1482])).

tff(c_17262,plain,(
    ! [A_850] :
      ( r2_hidden('#skF_1'(A_850,u1_struct_0('#skF_6'),'#skF_7'),'#skF_7')
      | ~ r2_lattice3('#skF_6',k1_xboole_0,'#skF_1'(A_850,u1_struct_0('#skF_6'),'#skF_7'))
      | ~ m1_subset_1(u1_struct_0('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(A_850))
      | ~ m1_subset_1(u1_struct_0('#skF_6'),k1_zfmisc_1(A_850)) ) ),
    inference(resolution,[status(thm)],[c_17141,c_1496])).

tff(c_17402,plain,(
    ! [A_852] :
      ( r2_hidden('#skF_1'(A_852,u1_struct_0('#skF_6'),'#skF_7'),'#skF_7')
      | ~ r2_lattice3('#skF_6',k1_xboole_0,'#skF_1'(A_852,u1_struct_0('#skF_6'),'#skF_7'))
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(A_852))
      | ~ m1_subset_1(u1_struct_0('#skF_6'),k1_zfmisc_1(A_852)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_165,c_17262])).

tff(c_17430,plain,
    ( r2_hidden('#skF_1'(u1_struct_0('#skF_6'),u1_struct_0('#skF_6'),'#skF_7'),'#skF_7')
    | ~ l1_orders_2('#skF_6')
    | u1_struct_0('#skF_6') = '#skF_7'
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_6')))
    | ~ m1_subset_1(u1_struct_0('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_6'))) ),
    inference(resolution,[status(thm)],[c_459,c_17402])).

tff(c_17463,plain,
    ( r2_hidden('#skF_1'(u1_struct_0('#skF_6'),u1_struct_0('#skF_6'),'#skF_7'),'#skF_7')
    | u1_struct_0('#skF_6') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_165,c_60,c_68,c_17430])).

tff(c_17464,plain,(
    r2_hidden('#skF_1'(u1_struct_0('#skF_6'),u1_struct_0('#skF_6'),'#skF_7'),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_17140,c_17463])).

tff(c_17494,plain,(
    m1_subset_1('#skF_1'(u1_struct_0('#skF_6'),u1_struct_0('#skF_6'),'#skF_7'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_17464,c_218])).

tff(c_1959,plain,(
    ! [A_299,B_300,C_301,A_302] :
      ( r2_hidden('#skF_1'(A_299,B_300,C_301),A_302)
      | ~ m1_subset_1(C_301,k1_zfmisc_1(A_302))
      | r2_hidden('#skF_1'(A_299,B_300,C_301),B_300)
      | C_301 = B_300
      | ~ m1_subset_1(C_301,k1_zfmisc_1(A_299))
      | ~ m1_subset_1(B_300,k1_zfmisc_1(A_299)) ) ),
    inference(resolution,[status(thm)],[c_740,c_2])).

tff(c_5543,plain,(
    ! [C_476,B_475,A_474,A_473,A_477] :
      ( r2_hidden('#skF_1'(A_473,B_475,C_476),A_477)
      | ~ m1_subset_1(A_474,k1_zfmisc_1(A_477))
      | ~ m1_subset_1(C_476,k1_zfmisc_1(A_474))
      | r2_hidden('#skF_1'(A_473,B_475,C_476),B_475)
      | C_476 = B_475
      | ~ m1_subset_1(C_476,k1_zfmisc_1(A_473))
      | ~ m1_subset_1(B_475,k1_zfmisc_1(A_473)) ) ),
    inference(resolution,[status(thm)],[c_1959,c_2])).

tff(c_5605,plain,(
    ! [A_473,B_475,C_476] :
      ( r2_hidden('#skF_1'(A_473,B_475,C_476),u1_struct_0('#skF_6'))
      | ~ m1_subset_1(C_476,k1_zfmisc_1('#skF_7'))
      | r2_hidden('#skF_1'(A_473,B_475,C_476),B_475)
      | C_476 = B_475
      | ~ m1_subset_1(C_476,k1_zfmisc_1(A_473))
      | ~ m1_subset_1(B_475,k1_zfmisc_1(A_473)) ) ),
    inference(resolution,[status(thm)],[c_60,c_5543])).

tff(c_6524,plain,(
    ! [C_509,A_510] :
      ( ~ m1_subset_1(C_509,k1_zfmisc_1('#skF_7'))
      | u1_struct_0('#skF_6') = C_509
      | ~ m1_subset_1(C_509,k1_zfmisc_1(A_510))
      | ~ m1_subset_1(u1_struct_0('#skF_6'),k1_zfmisc_1(A_510))
      | r2_hidden('#skF_1'(A_510,u1_struct_0('#skF_6'),C_509),u1_struct_0('#skF_6')) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_5605])).

tff(c_829,plain,(
    ! [A_190,B_191,B_15] :
      ( ~ r2_hidden('#skF_1'(A_190,B_191,B_15),B_191)
      | B_191 = B_15
      | ~ m1_subset_1(B_15,k1_zfmisc_1(A_190))
      | ~ m1_subset_1(B_191,k1_zfmisc_1(A_190))
      | v1_xboole_0(B_15)
      | ~ m1_subset_1('#skF_1'(A_190,B_191,B_15),B_15) ) ),
    inference(resolution,[status(thm)],[c_18,c_817])).

tff(c_6562,plain,(
    ! [C_509,A_510] :
      ( v1_xboole_0(C_509)
      | ~ m1_subset_1('#skF_1'(A_510,u1_struct_0('#skF_6'),C_509),C_509)
      | ~ m1_subset_1(C_509,k1_zfmisc_1('#skF_7'))
      | u1_struct_0('#skF_6') = C_509
      | ~ m1_subset_1(C_509,k1_zfmisc_1(A_510))
      | ~ m1_subset_1(u1_struct_0('#skF_6'),k1_zfmisc_1(A_510)) ) ),
    inference(resolution,[status(thm)],[c_6524,c_829])).

tff(c_17500,plain,
    ( v1_xboole_0('#skF_7')
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1('#skF_7'))
    | u1_struct_0('#skF_6') = '#skF_7'
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_6')))
    | ~ m1_subset_1(u1_struct_0('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_6'))) ),
    inference(resolution,[status(thm)],[c_17494,c_6562])).

tff(c_17525,plain,
    ( v1_xboole_0('#skF_7')
    | u1_struct_0('#skF_6') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_165,c_60,c_165,c_17500])).

tff(c_17527,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_17140,c_66,c_17525])).

tff(c_17528,plain,(
    u1_struct_0('#skF_6') = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_4644])).

tff(c_17531,plain,(
    v1_xboole_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_17528,c_3135])).

tff(c_17569,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_17531])).

tff(c_17571,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_3024])).

tff(c_900,plain,(
    ! [A_208,B_209,C_210] :
      ( m1_subset_1('#skF_1'(A_208,B_209,C_210),C_210)
      | r2_hidden('#skF_1'(A_208,B_209,C_210),B_209)
      | C_210 = B_209
      | ~ m1_subset_1(C_210,k1_zfmisc_1(A_208))
      | ~ m1_subset_1(B_209,k1_zfmisc_1(A_208)) ) ),
    inference(resolution,[status(thm)],[c_740,c_218])).

tff(c_978,plain,(
    ! [A_208,B_209,C_210] :
      ( m1_subset_1('#skF_1'(A_208,B_209,C_210),B_209)
      | m1_subset_1('#skF_1'(A_208,B_209,C_210),C_210)
      | C_210 = B_209
      | ~ m1_subset_1(C_210,k1_zfmisc_1(A_208))
      | ~ m1_subset_1(B_209,k1_zfmisc_1(A_208)) ) ),
    inference(resolution,[status(thm)],[c_900,c_218])).

tff(c_1670,plain,(
    ! [A_115] :
      ( r2_hidden(A_115,'#skF_7')
      | ~ m1_subset_1(A_115,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_317,c_1595])).

tff(c_758,plain,(
    ! [A_174,B_175,C_176] :
      ( m1_subset_1('#skF_1'(A_174,B_175,C_176),B_175)
      | r2_hidden('#skF_1'(A_174,B_175,C_176),C_176)
      | C_176 = B_175
      | ~ m1_subset_1(C_176,k1_zfmisc_1(A_174))
      | ~ m1_subset_1(B_175,k1_zfmisc_1(A_174)) ) ),
    inference(resolution,[status(thm)],[c_740,c_218])).

tff(c_2991,plain,(
    ! [C_176,B_175] :
      ( v1_xboole_0(C_176)
      | v1_xboole_0(B_175)
      | r2_hidden('#skF_1'(C_176,B_175,C_176),C_176)
      | C_176 = B_175
      | ~ m1_subset_1(C_176,k1_zfmisc_1(C_176))
      | ~ m1_subset_1(B_175,k1_zfmisc_1(C_176)) ) ),
    inference(resolution,[status(thm)],[c_758,c_2973])).

tff(c_3081,plain,(
    ! [C_374,B_375] :
      ( v1_xboole_0(C_374)
      | v1_xboole_0(B_375)
      | r2_hidden('#skF_1'(C_374,B_375,C_374),C_374)
      | C_374 = B_375
      | ~ m1_subset_1(B_375,k1_zfmisc_1(C_374)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_165,c_2991])).

tff(c_3104,plain,(
    ! [C_374,B_375] :
      ( ~ r2_hidden('#skF_1'(C_374,B_375,C_374),B_375)
      | ~ m1_subset_1(C_374,k1_zfmisc_1(C_374))
      | v1_xboole_0(C_374)
      | v1_xboole_0(B_375)
      | C_374 = B_375
      | ~ m1_subset_1(B_375,k1_zfmisc_1(C_374)) ) ),
    inference(resolution,[status(thm)],[c_3081,c_6])).

tff(c_17718,plain,(
    ! [C_858,B_859] :
      ( ~ r2_hidden('#skF_1'(C_858,B_859,C_858),B_859)
      | v1_xboole_0(C_858)
      | v1_xboole_0(B_859)
      | C_858 = B_859
      | ~ m1_subset_1(B_859,k1_zfmisc_1(C_858)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_165,c_3104])).

tff(c_17752,plain,(
    ! [C_858] :
      ( v1_xboole_0(C_858)
      | v1_xboole_0('#skF_7')
      | C_858 = '#skF_7'
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(C_858))
      | ~ m1_subset_1('#skF_1'(C_858,'#skF_7',C_858),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_1670,c_17718])).

tff(c_17815,plain,(
    ! [C_860] :
      ( v1_xboole_0(C_860)
      | C_860 = '#skF_7'
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(C_860))
      | ~ m1_subset_1('#skF_1'(C_860,'#skF_7',C_860),'#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_17752])).

tff(c_17831,plain,(
    ! [C_210] :
      ( v1_xboole_0(C_210)
      | m1_subset_1('#skF_1'(C_210,'#skF_7',C_210),C_210)
      | C_210 = '#skF_7'
      | ~ m1_subset_1(C_210,k1_zfmisc_1(C_210))
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(C_210)) ) ),
    inference(resolution,[status(thm)],[c_978,c_17815])).

tff(c_17974,plain,(
    ! [C_866] :
      ( v1_xboole_0(C_866)
      | m1_subset_1('#skF_1'(C_866,'#skF_7',C_866),C_866)
      | C_866 = '#skF_7'
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(C_866)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_165,c_17831])).

tff(c_18017,plain,
    ( r2_hidden('#skF_1'(u1_struct_0('#skF_6'),'#skF_7',u1_struct_0('#skF_6')),'#skF_7')
    | ~ r2_lattice3('#skF_6',k1_xboole_0,'#skF_1'(u1_struct_0('#skF_6'),'#skF_7',u1_struct_0('#skF_6')))
    | v1_xboole_0(u1_struct_0('#skF_6'))
    | u1_struct_0('#skF_6') = '#skF_7'
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_6'))) ),
    inference(resolution,[status(thm)],[c_17974,c_1496])).

tff(c_18088,plain,
    ( r2_hidden('#skF_1'(u1_struct_0('#skF_6'),'#skF_7',u1_struct_0('#skF_6')),'#skF_7')
    | ~ r2_lattice3('#skF_6',k1_xboole_0,'#skF_1'(u1_struct_0('#skF_6'),'#skF_7',u1_struct_0('#skF_6')))
    | v1_xboole_0(u1_struct_0('#skF_6'))
    | u1_struct_0('#skF_6') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_18017])).

tff(c_18089,plain,
    ( r2_hidden('#skF_1'(u1_struct_0('#skF_6'),'#skF_7',u1_struct_0('#skF_6')),'#skF_7')
    | ~ r2_lattice3('#skF_6',k1_xboole_0,'#skF_1'(u1_struct_0('#skF_6'),'#skF_7',u1_struct_0('#skF_6')))
    | u1_struct_0('#skF_6') = '#skF_7' ),
    inference(negUnitSimplification,[status(thm)],[c_17571,c_18088])).

tff(c_18639,plain,(
    ~ r2_lattice3('#skF_6',k1_xboole_0,'#skF_1'(u1_struct_0('#skF_6'),'#skF_7',u1_struct_0('#skF_6'))) ),
    inference(splitLeft,[status(thm)],[c_18089])).

tff(c_18642,plain,
    ( ~ l1_orders_2('#skF_6')
    | u1_struct_0('#skF_6') = '#skF_7'
    | ~ m1_subset_1(u1_struct_0('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_6')))
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_6'))) ),
    inference(resolution,[status(thm)],[c_459,c_18639])).

tff(c_18651,plain,(
    u1_struct_0('#skF_6') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_165,c_68,c_18642])).

tff(c_1311,plain,(
    ! [B_250,A_251] :
      ( u1_struct_0('#skF_6') = B_250
      | ~ m1_subset_1(B_250,k1_zfmisc_1(A_251))
      | ~ m1_subset_1(u1_struct_0('#skF_6'),k1_zfmisc_1(A_251))
      | v1_xboole_0(B_250)
      | ~ m1_subset_1('#skF_1'(A_251,u1_struct_0('#skF_6'),B_250),B_250)
      | ~ m1_subset_1('#skF_1'(A_251,u1_struct_0('#skF_6'),B_250),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_299,c_1289])).

tff(c_1322,plain,(
    ! [A_5] :
      ( v1_xboole_0(A_5)
      | ~ m1_subset_1('#skF_1'(A_5,u1_struct_0('#skF_6'),A_5),'#skF_7')
      | u1_struct_0('#skF_6') = A_5
      | ~ m1_subset_1(A_5,k1_zfmisc_1(A_5))
      | ~ m1_subset_1(u1_struct_0('#skF_6'),k1_zfmisc_1(A_5)) ) ),
    inference(resolution,[status(thm)],[c_4,c_1311])).

tff(c_1338,plain,(
    ! [A_252] :
      ( v1_xboole_0(A_252)
      | ~ m1_subset_1('#skF_1'(A_252,u1_struct_0('#skF_6'),A_252),'#skF_7')
      | u1_struct_0('#skF_6') = A_252
      | ~ m1_subset_1(u1_struct_0('#skF_6'),k1_zfmisc_1(A_252)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_165,c_1322])).

tff(c_1346,plain,
    ( v1_xboole_0('#skF_7')
    | u1_struct_0('#skF_6') = '#skF_7'
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1('#skF_7'))
    | ~ m1_subset_1(u1_struct_0('#skF_6'),k1_zfmisc_1('#skF_7')) ),
    inference(resolution,[status(thm)],[c_4,c_1338])).

tff(c_1349,plain,
    ( v1_xboole_0('#skF_7')
    | u1_struct_0('#skF_6') = '#skF_7'
    | ~ m1_subset_1(u1_struct_0('#skF_6'),k1_zfmisc_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_165,c_1346])).

tff(c_1350,plain,
    ( u1_struct_0('#skF_6') = '#skF_7'
    | ~ m1_subset_1(u1_struct_0('#skF_6'),k1_zfmisc_1('#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_1349])).

tff(c_1351,plain,(
    ~ m1_subset_1(u1_struct_0('#skF_6'),k1_zfmisc_1('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_1350])).

tff(c_18678,plain,(
    ~ m1_subset_1('#skF_7',k1_zfmisc_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18651,c_1351])).

tff(c_18703,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_165,c_18678])).

tff(c_18704,plain,
    ( u1_struct_0('#skF_6') = '#skF_7'
    | r2_hidden('#skF_1'(u1_struct_0('#skF_6'),'#skF_7',u1_struct_0('#skF_6')),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_18089])).

tff(c_18769,plain,(
    r2_hidden('#skF_1'(u1_struct_0('#skF_6'),'#skF_7',u1_struct_0('#skF_6')),'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_18704])).

tff(c_3130,plain,(
    ! [C_374,B_375] :
      ( ~ r2_hidden('#skF_1'(C_374,B_375,C_374),B_375)
      | v1_xboole_0(C_374)
      | v1_xboole_0(B_375)
      | C_374 = B_375
      | ~ m1_subset_1(B_375,k1_zfmisc_1(C_374)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_165,c_3104])).

tff(c_18772,plain,
    ( v1_xboole_0(u1_struct_0('#skF_6'))
    | v1_xboole_0('#skF_7')
    | u1_struct_0('#skF_6') = '#skF_7'
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_6'))) ),
    inference(resolution,[status(thm)],[c_18769,c_3130])).

tff(c_18788,plain,
    ( v1_xboole_0(u1_struct_0('#skF_6'))
    | v1_xboole_0('#skF_7')
    | u1_struct_0('#skF_6') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_18772])).

tff(c_18789,plain,(
    u1_struct_0('#skF_6') = '#skF_7' ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_17571,c_18788])).

tff(c_18827,plain,(
    ~ m1_subset_1('#skF_7',k1_zfmisc_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18789,c_1351])).

tff(c_18852,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_165,c_18827])).

tff(c_18853,plain,(
    u1_struct_0('#skF_6') = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_18704])).

tff(c_18879,plain,(
    ~ m1_subset_1('#skF_7',k1_zfmisc_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18853,c_1351])).

tff(c_18904,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_165,c_18879])).

tff(c_18905,plain,(
    u1_struct_0('#skF_6') = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_1350])).

tff(c_148,plain,(
    v1_subset_1('#skF_7',u1_struct_0('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_86])).

tff(c_18923,plain,(
    v1_subset_1('#skF_7','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18905,c_148])).

tff(c_18928,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_166,c_18923])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:16:01 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 12.89/5.56  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.89/5.58  
% 12.89/5.58  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.89/5.58  %$ r2_lattice3 > r1_orders_2 > r1_lattice3 > v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_yellow_0 > r2_hidden > r1_yellow_0 > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_yellow_0 > v1_xboole_0 > l1_orders_2 > k1_yellow_0 > #nlpp > u1_struct_0 > k3_yellow_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_7 > #skF_6 > #skF_3 > #skF_5 > #skF_4
% 12.89/5.58  
% 12.89/5.58  %Foreground sorts:
% 12.89/5.58  
% 12.89/5.58  
% 12.89/5.58  %Background operators:
% 12.89/5.58  
% 12.89/5.58  
% 12.89/5.58  %Foreground operators:
% 12.89/5.58  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 12.89/5.58  tff(k1_yellow_0, type, k1_yellow_0: ($i * $i) > $i).
% 12.89/5.58  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 12.89/5.58  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 12.89/5.58  tff('#skF_2', type, '#skF_2': $i > $i).
% 12.89/5.58  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 12.89/5.58  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 12.89/5.58  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 12.89/5.58  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 12.89/5.58  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 12.89/5.58  tff(v2_waybel_0, type, v2_waybel_0: ($i * $i) > $o).
% 12.89/5.58  tff(k3_yellow_0, type, k3_yellow_0: $i > $i).
% 12.89/5.58  tff('#skF_7', type, '#skF_7': $i).
% 12.89/5.58  tff(r2_lattice3, type, r2_lattice3: ($i * $i * $i) > $o).
% 12.89/5.58  tff('#skF_6', type, '#skF_6': $i).
% 12.89/5.58  tff(r2_yellow_0, type, r2_yellow_0: ($i * $i) > $o).
% 12.89/5.58  tff(r1_lattice3, type, r1_lattice3: ($i * $i * $i) > $o).
% 12.89/5.58  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 12.89/5.58  tff(r1_yellow_0, type, r1_yellow_0: ($i * $i) > $o).
% 12.89/5.58  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 12.89/5.58  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 12.89/5.58  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 12.89/5.58  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 12.89/5.58  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 12.89/5.58  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 12.89/5.58  tff(v13_waybel_0, type, v13_waybel_0: ($i * $i) > $o).
% 12.89/5.58  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 12.89/5.58  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 12.89/5.58  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 12.89/5.58  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 12.89/5.58  tff(v1_yellow_0, type, v1_yellow_0: $i > $o).
% 12.89/5.58  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 12.89/5.58  
% 12.89/5.61  tff(f_52, axiom, (![A]: (?[B]: (m1_subset_1(B, k1_zfmisc_1(A)) & ~v1_subset_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc3_subset_1)).
% 12.89/5.61  tff(f_138, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (v1_subset_1(B, A) <=> ~(B = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_subset_1)).
% 12.89/5.61  tff(f_167, negated_conjecture, ~(![A]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & v1_yellow_0(A)) & l1_orders_2(A)) => (![B]: ((((~v1_xboole_0(B) & v2_waybel_0(B, A)) & v13_waybel_0(B, A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v1_subset_1(B, u1_struct_0(A)) <=> ~r2_hidden(k3_yellow_0(A), B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_waybel_7)).
% 12.89/5.61  tff(f_46, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => ((![D]: (m1_subset_1(D, A) => (r2_hidden(D, B) <=> r2_hidden(D, C)))) => (B = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_subset_1)).
% 12.89/5.61  tff(f_32, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 12.89/5.61  tff(f_64, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 12.89/5.61  tff(f_58, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 12.89/5.61  tff(f_112, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (r2_lattice3(A, k1_xboole_0, B) & r1_lattice3(A, k1_xboole_0, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_yellow_0)).
% 12.89/5.61  tff(f_68, axiom, (![A]: (l1_orders_2(A) => (k3_yellow_0(A) = k1_yellow_0(A, k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d11_yellow_0)).
% 12.89/5.61  tff(f_90, axiom, (![A, B]: (l1_orders_2(A) => m1_subset_1(k1_yellow_0(A, B), u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_yellow_0)).
% 12.89/5.61  tff(f_103, axiom, (![A]: ((((~v2_struct_0(A) & v5_orders_2(A)) & v1_yellow_0(A)) & l1_orders_2(A)) => (r1_yellow_0(A, k1_xboole_0) & r2_yellow_0(A, u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_yellow_0)).
% 12.89/5.61  tff(f_86, axiom, (![A]: (l1_orders_2(A) => (![B, C]: (m1_subset_1(C, u1_struct_0(A)) => (r1_yellow_0(A, B) => ((C = k1_yellow_0(A, B)) <=> (r2_lattice3(A, B, C) & (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_lattice3(A, B, D) => r1_orders_2(A, C, D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_yellow_0)).
% 12.89/5.61  tff(f_131, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v13_waybel_0(B, A) <=> (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => ((r2_hidden(C, B) & r1_orders_2(A, C, D)) => r2_hidden(D, B))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d20_waybel_0)).
% 12.89/5.61  tff(c_14, plain, (![A_12]: (~v1_subset_1('#skF_2'(A_12), A_12))), inference(cnfTransformation, [status(thm)], [f_52])).
% 12.89/5.61  tff(c_16, plain, (![A_12]: (m1_subset_1('#skF_2'(A_12), k1_zfmisc_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 12.89/5.61  tff(c_153, plain, (![B_83, A_84]: (v1_subset_1(B_83, A_84) | B_83=A_84 | ~m1_subset_1(B_83, k1_zfmisc_1(A_84)))), inference(cnfTransformation, [status(thm)], [f_138])).
% 12.89/5.61  tff(c_156, plain, (![A_12]: (v1_subset_1('#skF_2'(A_12), A_12) | '#skF_2'(A_12)=A_12)), inference(resolution, [status(thm)], [c_16, c_153])).
% 12.89/5.61  tff(c_162, plain, (![A_12]: ('#skF_2'(A_12)=A_12)), inference(negUnitSimplification, [status(thm)], [c_14, c_156])).
% 12.89/5.61  tff(c_166, plain, (![A_12]: (~v1_subset_1(A_12, A_12))), inference(demodulation, [status(thm), theory('equality')], [c_162, c_14])).
% 12.89/5.61  tff(c_165, plain, (![A_12]: (m1_subset_1(A_12, k1_zfmisc_1(A_12)))), inference(demodulation, [status(thm), theory('equality')], [c_162, c_16])).
% 12.89/5.61  tff(c_66, plain, (~v1_xboole_0('#skF_7')), inference(cnfTransformation, [status(thm)], [f_167])).
% 12.89/5.61  tff(c_740, plain, (![A_174, B_175, C_176]: (r2_hidden('#skF_1'(A_174, B_175, C_176), B_175) | r2_hidden('#skF_1'(A_174, B_175, C_176), C_176) | C_176=B_175 | ~m1_subset_1(C_176, k1_zfmisc_1(A_174)) | ~m1_subset_1(B_175, k1_zfmisc_1(A_174)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 12.89/5.61  tff(c_2, plain, (![C_4, A_1, B_2]: (r2_hidden(C_4, A_1) | ~r2_hidden(C_4, B_2) | ~m1_subset_1(B_2, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 12.89/5.61  tff(c_2140, plain, (![A_318, B_319, C_320, A_321]: (r2_hidden('#skF_1'(A_318, B_319, C_320), A_321) | ~m1_subset_1(B_319, k1_zfmisc_1(A_321)) | r2_hidden('#skF_1'(A_318, B_319, C_320), C_320) | C_320=B_319 | ~m1_subset_1(C_320, k1_zfmisc_1(A_318)) | ~m1_subset_1(B_319, k1_zfmisc_1(A_318)))), inference(resolution, [status(thm)], [c_740, c_2])).
% 12.89/5.61  tff(c_213, plain, (![A_96, C_97, B_98]: (m1_subset_1(A_96, C_97) | ~m1_subset_1(B_98, k1_zfmisc_1(C_97)) | ~r2_hidden(A_96, B_98))), inference(cnfTransformation, [status(thm)], [f_64])).
% 12.89/5.61  tff(c_218, plain, (![A_96, A_12]: (m1_subset_1(A_96, A_12) | ~r2_hidden(A_96, A_12))), inference(resolution, [status(thm)], [c_165, c_213])).
% 12.89/5.61  tff(c_15169, plain, (![A_827, B_828, C_829, A_830]: (m1_subset_1('#skF_1'(A_827, B_828, C_829), C_829) | r2_hidden('#skF_1'(A_827, B_828, C_829), A_830) | ~m1_subset_1(B_828, k1_zfmisc_1(A_830)) | C_829=B_828 | ~m1_subset_1(C_829, k1_zfmisc_1(A_827)) | ~m1_subset_1(B_828, k1_zfmisc_1(A_827)))), inference(resolution, [status(thm)], [c_2140, c_218])).
% 12.89/5.61  tff(c_16293, plain, (![A_842, B_843, C_844, A_845]: (m1_subset_1('#skF_1'(A_842, B_843, C_844), A_845) | m1_subset_1('#skF_1'(A_842, B_843, C_844), C_844) | ~m1_subset_1(B_843, k1_zfmisc_1(A_845)) | C_844=B_843 | ~m1_subset_1(C_844, k1_zfmisc_1(A_842)) | ~m1_subset_1(B_843, k1_zfmisc_1(A_842)))), inference(resolution, [status(thm)], [c_15169, c_218])).
% 12.89/5.61  tff(c_60, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0('#skF_6')))), inference(cnfTransformation, [status(thm)], [f_167])).
% 12.89/5.61  tff(c_18, plain, (![A_14, B_15]: (r2_hidden(A_14, B_15) | v1_xboole_0(B_15) | ~m1_subset_1(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_58])).
% 12.89/5.61  tff(c_202, plain, (![C_92, A_93, B_94]: (r2_hidden(C_92, A_93) | ~r2_hidden(C_92, B_94) | ~m1_subset_1(B_94, k1_zfmisc_1(A_93)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 12.89/5.61  tff(c_287, plain, (![A_111, A_112, B_113]: (r2_hidden(A_111, A_112) | ~m1_subset_1(B_113, k1_zfmisc_1(A_112)) | v1_xboole_0(B_113) | ~m1_subset_1(A_111, B_113))), inference(resolution, [status(thm)], [c_18, c_202])).
% 12.89/5.61  tff(c_294, plain, (![A_111]: (r2_hidden(A_111, u1_struct_0('#skF_6')) | v1_xboole_0('#skF_7') | ~m1_subset_1(A_111, '#skF_7'))), inference(resolution, [status(thm)], [c_60, c_287])).
% 12.89/5.61  tff(c_299, plain, (![A_111]: (r2_hidden(A_111, u1_struct_0('#skF_6')) | ~m1_subset_1(A_111, '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_66, c_294])).
% 12.89/5.61  tff(c_68, plain, (l1_orders_2('#skF_6')), inference(cnfTransformation, [status(thm)], [f_167])).
% 12.89/5.61  tff(c_300, plain, (![A_114]: (r2_hidden(A_114, u1_struct_0('#skF_6')) | ~m1_subset_1(A_114, '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_66, c_294])).
% 12.89/5.61  tff(c_308, plain, (![A_115]: (m1_subset_1(A_115, u1_struct_0('#skF_6')) | ~m1_subset_1(A_115, '#skF_7'))), inference(resolution, [status(thm)], [c_300, c_218])).
% 12.89/5.61  tff(c_42, plain, (![A_35, B_37]: (r2_lattice3(A_35, k1_xboole_0, B_37) | ~m1_subset_1(B_37, u1_struct_0(A_35)) | ~l1_orders_2(A_35))), inference(cnfTransformation, [status(thm)], [f_112])).
% 12.89/5.61  tff(c_311, plain, (![A_115]: (r2_lattice3('#skF_6', k1_xboole_0, A_115) | ~l1_orders_2('#skF_6') | ~m1_subset_1(A_115, '#skF_7'))), inference(resolution, [status(thm)], [c_308, c_42])).
% 12.89/5.61  tff(c_317, plain, (![A_115]: (r2_lattice3('#skF_6', k1_xboole_0, A_115) | ~m1_subset_1(A_115, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_311])).
% 12.89/5.61  tff(c_306, plain, (![A_114]: (m1_subset_1(A_114, u1_struct_0('#skF_6')) | ~m1_subset_1(A_114, '#skF_7'))), inference(resolution, [status(thm)], [c_300, c_218])).
% 12.89/5.61  tff(c_62, plain, (v13_waybel_0('#skF_7', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_167])).
% 12.89/5.61  tff(c_107, plain, (![A_72, B_73]: (r2_hidden(A_72, B_73) | v1_xboole_0(B_73) | ~m1_subset_1(A_72, B_73))), inference(cnfTransformation, [status(thm)], [f_58])).
% 12.89/5.61  tff(c_86, plain, (v1_subset_1('#skF_7', u1_struct_0('#skF_6')) | ~r2_hidden(k3_yellow_0('#skF_6'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_167])).
% 12.89/5.61  tff(c_105, plain, (~r2_hidden(k3_yellow_0('#skF_6'), '#skF_7')), inference(splitLeft, [status(thm)], [c_86])).
% 12.89/5.61  tff(c_110, plain, (v1_xboole_0('#skF_7') | ~m1_subset_1(k3_yellow_0('#skF_6'), '#skF_7')), inference(resolution, [status(thm)], [c_107, c_105])).
% 12.89/5.61  tff(c_113, plain, (~m1_subset_1(k3_yellow_0('#skF_6'), '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_66, c_110])).
% 12.89/5.61  tff(c_80, plain, (r2_hidden(k3_yellow_0('#skF_6'), '#skF_7') | ~v1_subset_1('#skF_7', u1_struct_0('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_167])).
% 12.89/5.61  tff(c_106, plain, (~v1_subset_1('#skF_7', u1_struct_0('#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_105, c_80])).
% 12.89/5.61  tff(c_114, plain, (![B_74, A_75]: (v1_subset_1(B_74, A_75) | B_74=A_75 | ~m1_subset_1(B_74, k1_zfmisc_1(A_75)))), inference(cnfTransformation, [status(thm)], [f_138])).
% 12.89/5.61  tff(c_120, plain, (v1_subset_1('#skF_7', u1_struct_0('#skF_6')) | u1_struct_0('#skF_6')='#skF_7'), inference(resolution, [status(thm)], [c_60, c_114])).
% 12.89/5.61  tff(c_126, plain, (u1_struct_0('#skF_6')='#skF_7'), inference(negUnitSimplification, [status(thm)], [c_106, c_120])).
% 12.89/5.61  tff(c_89, plain, (![A_68]: (k1_yellow_0(A_68, k1_xboole_0)=k3_yellow_0(A_68) | ~l1_orders_2(A_68))), inference(cnfTransformation, [status(thm)], [f_68])).
% 12.89/5.61  tff(c_93, plain, (k1_yellow_0('#skF_6', k1_xboole_0)=k3_yellow_0('#skF_6')), inference(resolution, [status(thm)], [c_68, c_89])).
% 12.89/5.61  tff(c_99, plain, (![A_70, B_71]: (m1_subset_1(k1_yellow_0(A_70, B_71), u1_struct_0(A_70)) | ~l1_orders_2(A_70))), inference(cnfTransformation, [status(thm)], [f_90])).
% 12.89/5.61  tff(c_102, plain, (m1_subset_1(k3_yellow_0('#skF_6'), u1_struct_0('#skF_6')) | ~l1_orders_2('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_93, c_99])).
% 12.89/5.61  tff(c_104, plain, (m1_subset_1(k3_yellow_0('#skF_6'), u1_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_102])).
% 12.89/5.61  tff(c_144, plain, (m1_subset_1(k3_yellow_0('#skF_6'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_126, c_104])).
% 12.89/5.61  tff(c_147, plain, $false, inference(negUnitSimplification, [status(thm)], [c_113, c_144])).
% 12.89/5.61  tff(c_149, plain, (r2_hidden(k3_yellow_0('#skF_6'), '#skF_7')), inference(splitRight, [status(thm)], [c_86])).
% 12.89/5.61  tff(c_78, plain, (~v2_struct_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_167])).
% 12.89/5.61  tff(c_72, plain, (v5_orders_2('#skF_6')), inference(cnfTransformation, [status(thm)], [f_167])).
% 12.89/5.61  tff(c_70, plain, (v1_yellow_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_167])).
% 12.89/5.61  tff(c_38, plain, (![A_34]: (r1_yellow_0(A_34, k1_xboole_0) | ~l1_orders_2(A_34) | ~v1_yellow_0(A_34) | ~v5_orders_2(A_34) | v2_struct_0(A_34))), inference(cnfTransformation, [status(thm)], [f_103])).
% 12.89/5.61  tff(c_1354, plain, (![A_259, B_260, D_261]: (r1_orders_2(A_259, k1_yellow_0(A_259, B_260), D_261) | ~r2_lattice3(A_259, B_260, D_261) | ~m1_subset_1(D_261, u1_struct_0(A_259)) | ~r1_yellow_0(A_259, B_260) | ~m1_subset_1(k1_yellow_0(A_259, B_260), u1_struct_0(A_259)) | ~l1_orders_2(A_259))), inference(cnfTransformation, [status(thm)], [f_86])).
% 12.89/5.61  tff(c_1364, plain, (![D_261]: (r1_orders_2('#skF_6', k1_yellow_0('#skF_6', k1_xboole_0), D_261) | ~r2_lattice3('#skF_6', k1_xboole_0, D_261) | ~m1_subset_1(D_261, u1_struct_0('#skF_6')) | ~r1_yellow_0('#skF_6', k1_xboole_0) | ~m1_subset_1(k3_yellow_0('#skF_6'), u1_struct_0('#skF_6')) | ~l1_orders_2('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_93, c_1354])).
% 12.89/5.61  tff(c_1373, plain, (![D_261]: (r1_orders_2('#skF_6', k3_yellow_0('#skF_6'), D_261) | ~r2_lattice3('#skF_6', k1_xboole_0, D_261) | ~m1_subset_1(D_261, u1_struct_0('#skF_6')) | ~r1_yellow_0('#skF_6', k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_104, c_93, c_1364])).
% 12.89/5.61  tff(c_1374, plain, (~r1_yellow_0('#skF_6', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_1373])).
% 12.89/5.61  tff(c_1377, plain, (~l1_orders_2('#skF_6') | ~v1_yellow_0('#skF_6') | ~v5_orders_2('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_38, c_1374])).
% 12.89/5.61  tff(c_1380, plain, (v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_68, c_1377])).
% 12.89/5.61  tff(c_1382, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_1380])).
% 12.89/5.61  tff(c_1383, plain, (![D_261]: (r1_orders_2('#skF_6', k3_yellow_0('#skF_6'), D_261) | ~r2_lattice3('#skF_6', k1_xboole_0, D_261) | ~m1_subset_1(D_261, u1_struct_0('#skF_6')))), inference(splitRight, [status(thm)], [c_1373])).
% 12.89/5.61  tff(c_1431, plain, (![D_273, B_274, A_275, C_276]: (r2_hidden(D_273, B_274) | ~r1_orders_2(A_275, C_276, D_273) | ~r2_hidden(C_276, B_274) | ~m1_subset_1(D_273, u1_struct_0(A_275)) | ~m1_subset_1(C_276, u1_struct_0(A_275)) | ~v13_waybel_0(B_274, A_275) | ~m1_subset_1(B_274, k1_zfmisc_1(u1_struct_0(A_275))) | ~l1_orders_2(A_275))), inference(cnfTransformation, [status(thm)], [f_131])).
% 12.89/5.61  tff(c_1437, plain, (![D_261, B_274]: (r2_hidden(D_261, B_274) | ~r2_hidden(k3_yellow_0('#skF_6'), B_274) | ~m1_subset_1(k3_yellow_0('#skF_6'), u1_struct_0('#skF_6')) | ~v13_waybel_0(B_274, '#skF_6') | ~m1_subset_1(B_274, k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~l1_orders_2('#skF_6') | ~r2_lattice3('#skF_6', k1_xboole_0, D_261) | ~m1_subset_1(D_261, u1_struct_0('#skF_6')))), inference(resolution, [status(thm)], [c_1383, c_1431])).
% 12.89/5.61  tff(c_1453, plain, (![D_277, B_278]: (r2_hidden(D_277, B_278) | ~r2_hidden(k3_yellow_0('#skF_6'), B_278) | ~v13_waybel_0(B_278, '#skF_6') | ~m1_subset_1(B_278, k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~r2_lattice3('#skF_6', k1_xboole_0, D_277) | ~m1_subset_1(D_277, u1_struct_0('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_104, c_1437])).
% 12.89/5.61  tff(c_1482, plain, (![D_277]: (r2_hidden(D_277, '#skF_7') | ~r2_hidden(k3_yellow_0('#skF_6'), '#skF_7') | ~v13_waybel_0('#skF_7', '#skF_6') | ~r2_lattice3('#skF_6', k1_xboole_0, D_277) | ~m1_subset_1(D_277, u1_struct_0('#skF_6')))), inference(resolution, [status(thm)], [c_60, c_1453])).
% 12.89/5.61  tff(c_1497, plain, (![D_279]: (r2_hidden(D_279, '#skF_7') | ~r2_lattice3('#skF_6', k1_xboole_0, D_279) | ~m1_subset_1(D_279, u1_struct_0('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_149, c_1482])).
% 12.89/5.61  tff(c_1595, plain, (![A_280]: (r2_hidden(A_280, '#skF_7') | ~r2_lattice3('#skF_6', k1_xboole_0, A_280) | ~m1_subset_1(A_280, '#skF_7'))), inference(resolution, [status(thm)], [c_306, c_1497])).
% 12.89/5.61  tff(c_1696, plain, (![A_282]: (r2_hidden(A_282, '#skF_7') | ~m1_subset_1(A_282, '#skF_7'))), inference(resolution, [status(thm)], [c_317, c_1595])).
% 12.89/5.61  tff(c_6, plain, (![A_5, B_6, C_10]: (~r2_hidden('#skF_1'(A_5, B_6, C_10), C_10) | ~r2_hidden('#skF_1'(A_5, B_6, C_10), B_6) | C_10=B_6 | ~m1_subset_1(C_10, k1_zfmisc_1(A_5)) | ~m1_subset_1(B_6, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 12.89/5.61  tff(c_4550, plain, (![A_432, B_433]: (~r2_hidden('#skF_1'(A_432, B_433, '#skF_7'), B_433) | B_433='#skF_7' | ~m1_subset_1('#skF_7', k1_zfmisc_1(A_432)) | ~m1_subset_1(B_433, k1_zfmisc_1(A_432)) | ~m1_subset_1('#skF_1'(A_432, B_433, '#skF_7'), '#skF_7'))), inference(resolution, [status(thm)], [c_1696, c_6])).
% 12.89/5.61  tff(c_4644, plain, (![A_432]: (u1_struct_0('#skF_6')='#skF_7' | ~m1_subset_1('#skF_7', k1_zfmisc_1(A_432)) | ~m1_subset_1(u1_struct_0('#skF_6'), k1_zfmisc_1(A_432)) | ~m1_subset_1('#skF_1'(A_432, u1_struct_0('#skF_6'), '#skF_7'), '#skF_7'))), inference(resolution, [status(thm)], [c_299, c_4550])).
% 12.89/5.61  tff(c_4646, plain, (![A_432]: (~m1_subset_1('#skF_7', k1_zfmisc_1(A_432)) | ~m1_subset_1(u1_struct_0('#skF_6'), k1_zfmisc_1(A_432)) | ~m1_subset_1('#skF_1'(A_432, u1_struct_0('#skF_6'), '#skF_7'), '#skF_7'))), inference(splitLeft, [status(thm)], [c_4644])).
% 12.89/5.61  tff(c_16743, plain, (![A_842, A_845]: (m1_subset_1('#skF_1'(A_842, u1_struct_0('#skF_6'), '#skF_7'), A_845) | ~m1_subset_1(u1_struct_0('#skF_6'), k1_zfmisc_1(A_845)) | u1_struct_0('#skF_6')='#skF_7' | ~m1_subset_1('#skF_7', k1_zfmisc_1(A_842)) | ~m1_subset_1(u1_struct_0('#skF_6'), k1_zfmisc_1(A_842)))), inference(resolution, [status(thm)], [c_16293, c_4646])).
% 12.89/5.61  tff(c_17050, plain, (u1_struct_0('#skF_6')='#skF_7'), inference(splitLeft, [status(thm)], [c_16743])).
% 12.89/5.61  tff(c_219, plain, (![A_96]: (m1_subset_1(A_96, u1_struct_0('#skF_6')) | ~r2_hidden(A_96, '#skF_7'))), inference(resolution, [status(thm)], [c_60, c_213])).
% 12.89/5.61  tff(c_4, plain, (![A_5, B_6, C_10]: (m1_subset_1('#skF_1'(A_5, B_6, C_10), A_5) | C_10=B_6 | ~m1_subset_1(C_10, k1_zfmisc_1(A_5)) | ~m1_subset_1(B_6, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 12.89/5.61  tff(c_817, plain, (![A_190, B_191, C_192]: (~r2_hidden('#skF_1'(A_190, B_191, C_192), C_192) | ~r2_hidden('#skF_1'(A_190, B_191, C_192), B_191) | C_192=B_191 | ~m1_subset_1(C_192, k1_zfmisc_1(A_190)) | ~m1_subset_1(B_191, k1_zfmisc_1(A_190)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 12.89/5.61  tff(c_1289, plain, (![A_244, B_245, B_246]: (~r2_hidden('#skF_1'(A_244, B_245, B_246), B_245) | B_246=B_245 | ~m1_subset_1(B_246, k1_zfmisc_1(A_244)) | ~m1_subset_1(B_245, k1_zfmisc_1(A_244)) | v1_xboole_0(B_246) | ~m1_subset_1('#skF_1'(A_244, B_245, B_246), B_246))), inference(resolution, [status(thm)], [c_18, c_817])).
% 12.89/5.61  tff(c_2940, plain, (![B_368, B_367, A_369]: (B_368=B_367 | ~m1_subset_1(B_367, k1_zfmisc_1(A_369)) | ~m1_subset_1(B_368, k1_zfmisc_1(A_369)) | v1_xboole_0(B_367) | ~m1_subset_1('#skF_1'(A_369, B_368, B_367), B_367) | v1_xboole_0(B_368) | ~m1_subset_1('#skF_1'(A_369, B_368, B_367), B_368))), inference(resolution, [status(thm)], [c_18, c_1289])).
% 12.89/5.61  tff(c_2954, plain, (![A_5, B_6]: (v1_xboole_0(A_5) | v1_xboole_0(B_6) | ~m1_subset_1('#skF_1'(A_5, B_6, A_5), B_6) | B_6=A_5 | ~m1_subset_1(A_5, k1_zfmisc_1(A_5)) | ~m1_subset_1(B_6, k1_zfmisc_1(A_5)))), inference(resolution, [status(thm)], [c_4, c_2940])).
% 12.89/5.61  tff(c_2973, plain, (![A_370, B_371]: (v1_xboole_0(A_370) | v1_xboole_0(B_371) | ~m1_subset_1('#skF_1'(A_370, B_371, A_370), B_371) | B_371=A_370 | ~m1_subset_1(B_371, k1_zfmisc_1(A_370)))), inference(demodulation, [status(thm), theory('equality')], [c_165, c_2954])).
% 12.89/5.61  tff(c_3024, plain, (![A_370]: (v1_xboole_0(A_370) | v1_xboole_0(u1_struct_0('#skF_6')) | u1_struct_0('#skF_6')=A_370 | ~m1_subset_1(u1_struct_0('#skF_6'), k1_zfmisc_1(A_370)) | ~r2_hidden('#skF_1'(A_370, u1_struct_0('#skF_6'), A_370), '#skF_7'))), inference(resolution, [status(thm)], [c_219, c_2973])).
% 12.89/5.61  tff(c_3135, plain, (v1_xboole_0(u1_struct_0('#skF_6'))), inference(splitLeft, [status(thm)], [c_3024])).
% 12.89/5.61  tff(c_17100, plain, (v1_xboole_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_17050, c_3135])).
% 12.89/5.61  tff(c_17138, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_17100])).
% 12.89/5.61  tff(c_17140, plain, (u1_struct_0('#skF_6')!='#skF_7'), inference(splitRight, [status(thm)], [c_16743])).
% 12.89/5.61  tff(c_431, plain, (![A_136, B_137, C_138]: (m1_subset_1('#skF_1'(A_136, B_137, C_138), A_136) | C_138=B_137 | ~m1_subset_1(C_138, k1_zfmisc_1(A_136)) | ~m1_subset_1(B_137, k1_zfmisc_1(A_136)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 12.89/5.61  tff(c_459, plain, (![A_35, B_137, C_138]: (r2_lattice3(A_35, k1_xboole_0, '#skF_1'(u1_struct_0(A_35), B_137, C_138)) | ~l1_orders_2(A_35) | C_138=B_137 | ~m1_subset_1(C_138, k1_zfmisc_1(u1_struct_0(A_35))) | ~m1_subset_1(B_137, k1_zfmisc_1(u1_struct_0(A_35))))), inference(resolution, [status(thm)], [c_431, c_42])).
% 12.89/5.61  tff(c_17141, plain, (![A_850, A_851]: (m1_subset_1('#skF_1'(A_850, u1_struct_0('#skF_6'), '#skF_7'), A_851) | ~m1_subset_1(u1_struct_0('#skF_6'), k1_zfmisc_1(A_851)) | ~m1_subset_1('#skF_7', k1_zfmisc_1(A_850)) | ~m1_subset_1(u1_struct_0('#skF_6'), k1_zfmisc_1(A_850)))), inference(splitRight, [status(thm)], [c_16743])).
% 12.89/5.61  tff(c_1496, plain, (![D_277]: (r2_hidden(D_277, '#skF_7') | ~r2_lattice3('#skF_6', k1_xboole_0, D_277) | ~m1_subset_1(D_277, u1_struct_0('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_149, c_1482])).
% 12.89/5.61  tff(c_17262, plain, (![A_850]: (r2_hidden('#skF_1'(A_850, u1_struct_0('#skF_6'), '#skF_7'), '#skF_7') | ~r2_lattice3('#skF_6', k1_xboole_0, '#skF_1'(A_850, u1_struct_0('#skF_6'), '#skF_7')) | ~m1_subset_1(u1_struct_0('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~m1_subset_1('#skF_7', k1_zfmisc_1(A_850)) | ~m1_subset_1(u1_struct_0('#skF_6'), k1_zfmisc_1(A_850)))), inference(resolution, [status(thm)], [c_17141, c_1496])).
% 12.89/5.61  tff(c_17402, plain, (![A_852]: (r2_hidden('#skF_1'(A_852, u1_struct_0('#skF_6'), '#skF_7'), '#skF_7') | ~r2_lattice3('#skF_6', k1_xboole_0, '#skF_1'(A_852, u1_struct_0('#skF_6'), '#skF_7')) | ~m1_subset_1('#skF_7', k1_zfmisc_1(A_852)) | ~m1_subset_1(u1_struct_0('#skF_6'), k1_zfmisc_1(A_852)))), inference(demodulation, [status(thm), theory('equality')], [c_165, c_17262])).
% 12.89/5.61  tff(c_17430, plain, (r2_hidden('#skF_1'(u1_struct_0('#skF_6'), u1_struct_0('#skF_6'), '#skF_7'), '#skF_7') | ~l1_orders_2('#skF_6') | u1_struct_0('#skF_6')='#skF_7' | ~m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~m1_subset_1(u1_struct_0('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_6')))), inference(resolution, [status(thm)], [c_459, c_17402])).
% 12.89/5.61  tff(c_17463, plain, (r2_hidden('#skF_1'(u1_struct_0('#skF_6'), u1_struct_0('#skF_6'), '#skF_7'), '#skF_7') | u1_struct_0('#skF_6')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_165, c_60, c_68, c_17430])).
% 12.89/5.61  tff(c_17464, plain, (r2_hidden('#skF_1'(u1_struct_0('#skF_6'), u1_struct_0('#skF_6'), '#skF_7'), '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_17140, c_17463])).
% 12.89/5.61  tff(c_17494, plain, (m1_subset_1('#skF_1'(u1_struct_0('#skF_6'), u1_struct_0('#skF_6'), '#skF_7'), '#skF_7')), inference(resolution, [status(thm)], [c_17464, c_218])).
% 12.89/5.61  tff(c_1959, plain, (![A_299, B_300, C_301, A_302]: (r2_hidden('#skF_1'(A_299, B_300, C_301), A_302) | ~m1_subset_1(C_301, k1_zfmisc_1(A_302)) | r2_hidden('#skF_1'(A_299, B_300, C_301), B_300) | C_301=B_300 | ~m1_subset_1(C_301, k1_zfmisc_1(A_299)) | ~m1_subset_1(B_300, k1_zfmisc_1(A_299)))), inference(resolution, [status(thm)], [c_740, c_2])).
% 12.89/5.61  tff(c_5543, plain, (![C_476, B_475, A_474, A_473, A_477]: (r2_hidden('#skF_1'(A_473, B_475, C_476), A_477) | ~m1_subset_1(A_474, k1_zfmisc_1(A_477)) | ~m1_subset_1(C_476, k1_zfmisc_1(A_474)) | r2_hidden('#skF_1'(A_473, B_475, C_476), B_475) | C_476=B_475 | ~m1_subset_1(C_476, k1_zfmisc_1(A_473)) | ~m1_subset_1(B_475, k1_zfmisc_1(A_473)))), inference(resolution, [status(thm)], [c_1959, c_2])).
% 12.89/5.61  tff(c_5605, plain, (![A_473, B_475, C_476]: (r2_hidden('#skF_1'(A_473, B_475, C_476), u1_struct_0('#skF_6')) | ~m1_subset_1(C_476, k1_zfmisc_1('#skF_7')) | r2_hidden('#skF_1'(A_473, B_475, C_476), B_475) | C_476=B_475 | ~m1_subset_1(C_476, k1_zfmisc_1(A_473)) | ~m1_subset_1(B_475, k1_zfmisc_1(A_473)))), inference(resolution, [status(thm)], [c_60, c_5543])).
% 12.89/5.61  tff(c_6524, plain, (![C_509, A_510]: (~m1_subset_1(C_509, k1_zfmisc_1('#skF_7')) | u1_struct_0('#skF_6')=C_509 | ~m1_subset_1(C_509, k1_zfmisc_1(A_510)) | ~m1_subset_1(u1_struct_0('#skF_6'), k1_zfmisc_1(A_510)) | r2_hidden('#skF_1'(A_510, u1_struct_0('#skF_6'), C_509), u1_struct_0('#skF_6')))), inference(factorization, [status(thm), theory('equality')], [c_5605])).
% 12.89/5.61  tff(c_829, plain, (![A_190, B_191, B_15]: (~r2_hidden('#skF_1'(A_190, B_191, B_15), B_191) | B_191=B_15 | ~m1_subset_1(B_15, k1_zfmisc_1(A_190)) | ~m1_subset_1(B_191, k1_zfmisc_1(A_190)) | v1_xboole_0(B_15) | ~m1_subset_1('#skF_1'(A_190, B_191, B_15), B_15))), inference(resolution, [status(thm)], [c_18, c_817])).
% 12.89/5.61  tff(c_6562, plain, (![C_509, A_510]: (v1_xboole_0(C_509) | ~m1_subset_1('#skF_1'(A_510, u1_struct_0('#skF_6'), C_509), C_509) | ~m1_subset_1(C_509, k1_zfmisc_1('#skF_7')) | u1_struct_0('#skF_6')=C_509 | ~m1_subset_1(C_509, k1_zfmisc_1(A_510)) | ~m1_subset_1(u1_struct_0('#skF_6'), k1_zfmisc_1(A_510)))), inference(resolution, [status(thm)], [c_6524, c_829])).
% 12.89/5.61  tff(c_17500, plain, (v1_xboole_0('#skF_7') | ~m1_subset_1('#skF_7', k1_zfmisc_1('#skF_7')) | u1_struct_0('#skF_6')='#skF_7' | ~m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~m1_subset_1(u1_struct_0('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_6')))), inference(resolution, [status(thm)], [c_17494, c_6562])).
% 12.89/5.61  tff(c_17525, plain, (v1_xboole_0('#skF_7') | u1_struct_0('#skF_6')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_165, c_60, c_165, c_17500])).
% 12.89/5.61  tff(c_17527, plain, $false, inference(negUnitSimplification, [status(thm)], [c_17140, c_66, c_17525])).
% 12.89/5.61  tff(c_17528, plain, (u1_struct_0('#skF_6')='#skF_7'), inference(splitRight, [status(thm)], [c_4644])).
% 12.89/5.61  tff(c_17531, plain, (v1_xboole_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_17528, c_3135])).
% 12.89/5.61  tff(c_17569, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_17531])).
% 12.89/5.61  tff(c_17571, plain, (~v1_xboole_0(u1_struct_0('#skF_6'))), inference(splitRight, [status(thm)], [c_3024])).
% 12.89/5.61  tff(c_900, plain, (![A_208, B_209, C_210]: (m1_subset_1('#skF_1'(A_208, B_209, C_210), C_210) | r2_hidden('#skF_1'(A_208, B_209, C_210), B_209) | C_210=B_209 | ~m1_subset_1(C_210, k1_zfmisc_1(A_208)) | ~m1_subset_1(B_209, k1_zfmisc_1(A_208)))), inference(resolution, [status(thm)], [c_740, c_218])).
% 12.89/5.61  tff(c_978, plain, (![A_208, B_209, C_210]: (m1_subset_1('#skF_1'(A_208, B_209, C_210), B_209) | m1_subset_1('#skF_1'(A_208, B_209, C_210), C_210) | C_210=B_209 | ~m1_subset_1(C_210, k1_zfmisc_1(A_208)) | ~m1_subset_1(B_209, k1_zfmisc_1(A_208)))), inference(resolution, [status(thm)], [c_900, c_218])).
% 12.89/5.61  tff(c_1670, plain, (![A_115]: (r2_hidden(A_115, '#skF_7') | ~m1_subset_1(A_115, '#skF_7'))), inference(resolution, [status(thm)], [c_317, c_1595])).
% 12.89/5.61  tff(c_758, plain, (![A_174, B_175, C_176]: (m1_subset_1('#skF_1'(A_174, B_175, C_176), B_175) | r2_hidden('#skF_1'(A_174, B_175, C_176), C_176) | C_176=B_175 | ~m1_subset_1(C_176, k1_zfmisc_1(A_174)) | ~m1_subset_1(B_175, k1_zfmisc_1(A_174)))), inference(resolution, [status(thm)], [c_740, c_218])).
% 12.89/5.61  tff(c_2991, plain, (![C_176, B_175]: (v1_xboole_0(C_176) | v1_xboole_0(B_175) | r2_hidden('#skF_1'(C_176, B_175, C_176), C_176) | C_176=B_175 | ~m1_subset_1(C_176, k1_zfmisc_1(C_176)) | ~m1_subset_1(B_175, k1_zfmisc_1(C_176)))), inference(resolution, [status(thm)], [c_758, c_2973])).
% 12.89/5.61  tff(c_3081, plain, (![C_374, B_375]: (v1_xboole_0(C_374) | v1_xboole_0(B_375) | r2_hidden('#skF_1'(C_374, B_375, C_374), C_374) | C_374=B_375 | ~m1_subset_1(B_375, k1_zfmisc_1(C_374)))), inference(demodulation, [status(thm), theory('equality')], [c_165, c_2991])).
% 12.89/5.61  tff(c_3104, plain, (![C_374, B_375]: (~r2_hidden('#skF_1'(C_374, B_375, C_374), B_375) | ~m1_subset_1(C_374, k1_zfmisc_1(C_374)) | v1_xboole_0(C_374) | v1_xboole_0(B_375) | C_374=B_375 | ~m1_subset_1(B_375, k1_zfmisc_1(C_374)))), inference(resolution, [status(thm)], [c_3081, c_6])).
% 12.89/5.61  tff(c_17718, plain, (![C_858, B_859]: (~r2_hidden('#skF_1'(C_858, B_859, C_858), B_859) | v1_xboole_0(C_858) | v1_xboole_0(B_859) | C_858=B_859 | ~m1_subset_1(B_859, k1_zfmisc_1(C_858)))), inference(demodulation, [status(thm), theory('equality')], [c_165, c_3104])).
% 12.89/5.61  tff(c_17752, plain, (![C_858]: (v1_xboole_0(C_858) | v1_xboole_0('#skF_7') | C_858='#skF_7' | ~m1_subset_1('#skF_7', k1_zfmisc_1(C_858)) | ~m1_subset_1('#skF_1'(C_858, '#skF_7', C_858), '#skF_7'))), inference(resolution, [status(thm)], [c_1670, c_17718])).
% 12.89/5.61  tff(c_17815, plain, (![C_860]: (v1_xboole_0(C_860) | C_860='#skF_7' | ~m1_subset_1('#skF_7', k1_zfmisc_1(C_860)) | ~m1_subset_1('#skF_1'(C_860, '#skF_7', C_860), '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_66, c_17752])).
% 12.89/5.61  tff(c_17831, plain, (![C_210]: (v1_xboole_0(C_210) | m1_subset_1('#skF_1'(C_210, '#skF_7', C_210), C_210) | C_210='#skF_7' | ~m1_subset_1(C_210, k1_zfmisc_1(C_210)) | ~m1_subset_1('#skF_7', k1_zfmisc_1(C_210)))), inference(resolution, [status(thm)], [c_978, c_17815])).
% 12.89/5.61  tff(c_17974, plain, (![C_866]: (v1_xboole_0(C_866) | m1_subset_1('#skF_1'(C_866, '#skF_7', C_866), C_866) | C_866='#skF_7' | ~m1_subset_1('#skF_7', k1_zfmisc_1(C_866)))), inference(demodulation, [status(thm), theory('equality')], [c_165, c_17831])).
% 12.89/5.61  tff(c_18017, plain, (r2_hidden('#skF_1'(u1_struct_0('#skF_6'), '#skF_7', u1_struct_0('#skF_6')), '#skF_7') | ~r2_lattice3('#skF_6', k1_xboole_0, '#skF_1'(u1_struct_0('#skF_6'), '#skF_7', u1_struct_0('#skF_6'))) | v1_xboole_0(u1_struct_0('#skF_6')) | u1_struct_0('#skF_6')='#skF_7' | ~m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0('#skF_6')))), inference(resolution, [status(thm)], [c_17974, c_1496])).
% 12.89/5.61  tff(c_18088, plain, (r2_hidden('#skF_1'(u1_struct_0('#skF_6'), '#skF_7', u1_struct_0('#skF_6')), '#skF_7') | ~r2_lattice3('#skF_6', k1_xboole_0, '#skF_1'(u1_struct_0('#skF_6'), '#skF_7', u1_struct_0('#skF_6'))) | v1_xboole_0(u1_struct_0('#skF_6')) | u1_struct_0('#skF_6')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_18017])).
% 12.89/5.61  tff(c_18089, plain, (r2_hidden('#skF_1'(u1_struct_0('#skF_6'), '#skF_7', u1_struct_0('#skF_6')), '#skF_7') | ~r2_lattice3('#skF_6', k1_xboole_0, '#skF_1'(u1_struct_0('#skF_6'), '#skF_7', u1_struct_0('#skF_6'))) | u1_struct_0('#skF_6')='#skF_7'), inference(negUnitSimplification, [status(thm)], [c_17571, c_18088])).
% 12.89/5.61  tff(c_18639, plain, (~r2_lattice3('#skF_6', k1_xboole_0, '#skF_1'(u1_struct_0('#skF_6'), '#skF_7', u1_struct_0('#skF_6')))), inference(splitLeft, [status(thm)], [c_18089])).
% 12.89/5.61  tff(c_18642, plain, (~l1_orders_2('#skF_6') | u1_struct_0('#skF_6')='#skF_7' | ~m1_subset_1(u1_struct_0('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0('#skF_6')))), inference(resolution, [status(thm)], [c_459, c_18639])).
% 12.89/5.61  tff(c_18651, plain, (u1_struct_0('#skF_6')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_165, c_68, c_18642])).
% 12.89/5.61  tff(c_1311, plain, (![B_250, A_251]: (u1_struct_0('#skF_6')=B_250 | ~m1_subset_1(B_250, k1_zfmisc_1(A_251)) | ~m1_subset_1(u1_struct_0('#skF_6'), k1_zfmisc_1(A_251)) | v1_xboole_0(B_250) | ~m1_subset_1('#skF_1'(A_251, u1_struct_0('#skF_6'), B_250), B_250) | ~m1_subset_1('#skF_1'(A_251, u1_struct_0('#skF_6'), B_250), '#skF_7'))), inference(resolution, [status(thm)], [c_299, c_1289])).
% 12.89/5.61  tff(c_1322, plain, (![A_5]: (v1_xboole_0(A_5) | ~m1_subset_1('#skF_1'(A_5, u1_struct_0('#skF_6'), A_5), '#skF_7') | u1_struct_0('#skF_6')=A_5 | ~m1_subset_1(A_5, k1_zfmisc_1(A_5)) | ~m1_subset_1(u1_struct_0('#skF_6'), k1_zfmisc_1(A_5)))), inference(resolution, [status(thm)], [c_4, c_1311])).
% 12.89/5.61  tff(c_1338, plain, (![A_252]: (v1_xboole_0(A_252) | ~m1_subset_1('#skF_1'(A_252, u1_struct_0('#skF_6'), A_252), '#skF_7') | u1_struct_0('#skF_6')=A_252 | ~m1_subset_1(u1_struct_0('#skF_6'), k1_zfmisc_1(A_252)))), inference(demodulation, [status(thm), theory('equality')], [c_165, c_1322])).
% 12.89/5.61  tff(c_1346, plain, (v1_xboole_0('#skF_7') | u1_struct_0('#skF_6')='#skF_7' | ~m1_subset_1('#skF_7', k1_zfmisc_1('#skF_7')) | ~m1_subset_1(u1_struct_0('#skF_6'), k1_zfmisc_1('#skF_7'))), inference(resolution, [status(thm)], [c_4, c_1338])).
% 12.89/5.61  tff(c_1349, plain, (v1_xboole_0('#skF_7') | u1_struct_0('#skF_6')='#skF_7' | ~m1_subset_1(u1_struct_0('#skF_6'), k1_zfmisc_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_165, c_1346])).
% 12.89/5.61  tff(c_1350, plain, (u1_struct_0('#skF_6')='#skF_7' | ~m1_subset_1(u1_struct_0('#skF_6'), k1_zfmisc_1('#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_66, c_1349])).
% 12.89/5.61  tff(c_1351, plain, (~m1_subset_1(u1_struct_0('#skF_6'), k1_zfmisc_1('#skF_7'))), inference(splitLeft, [status(thm)], [c_1350])).
% 12.89/5.61  tff(c_18678, plain, (~m1_subset_1('#skF_7', k1_zfmisc_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_18651, c_1351])).
% 12.89/5.61  tff(c_18703, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_165, c_18678])).
% 12.89/5.61  tff(c_18704, plain, (u1_struct_0('#skF_6')='#skF_7' | r2_hidden('#skF_1'(u1_struct_0('#skF_6'), '#skF_7', u1_struct_0('#skF_6')), '#skF_7')), inference(splitRight, [status(thm)], [c_18089])).
% 12.89/5.61  tff(c_18769, plain, (r2_hidden('#skF_1'(u1_struct_0('#skF_6'), '#skF_7', u1_struct_0('#skF_6')), '#skF_7')), inference(splitLeft, [status(thm)], [c_18704])).
% 12.89/5.61  tff(c_3130, plain, (![C_374, B_375]: (~r2_hidden('#skF_1'(C_374, B_375, C_374), B_375) | v1_xboole_0(C_374) | v1_xboole_0(B_375) | C_374=B_375 | ~m1_subset_1(B_375, k1_zfmisc_1(C_374)))), inference(demodulation, [status(thm), theory('equality')], [c_165, c_3104])).
% 12.89/5.61  tff(c_18772, plain, (v1_xboole_0(u1_struct_0('#skF_6')) | v1_xboole_0('#skF_7') | u1_struct_0('#skF_6')='#skF_7' | ~m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0('#skF_6')))), inference(resolution, [status(thm)], [c_18769, c_3130])).
% 12.89/5.61  tff(c_18788, plain, (v1_xboole_0(u1_struct_0('#skF_6')) | v1_xboole_0('#skF_7') | u1_struct_0('#skF_6')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_18772])).
% 12.89/5.61  tff(c_18789, plain, (u1_struct_0('#skF_6')='#skF_7'), inference(negUnitSimplification, [status(thm)], [c_66, c_17571, c_18788])).
% 12.89/5.61  tff(c_18827, plain, (~m1_subset_1('#skF_7', k1_zfmisc_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_18789, c_1351])).
% 12.89/5.61  tff(c_18852, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_165, c_18827])).
% 12.89/5.61  tff(c_18853, plain, (u1_struct_0('#skF_6')='#skF_7'), inference(splitRight, [status(thm)], [c_18704])).
% 12.89/5.61  tff(c_18879, plain, (~m1_subset_1('#skF_7', k1_zfmisc_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_18853, c_1351])).
% 12.89/5.61  tff(c_18904, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_165, c_18879])).
% 12.89/5.61  tff(c_18905, plain, (u1_struct_0('#skF_6')='#skF_7'), inference(splitRight, [status(thm)], [c_1350])).
% 12.89/5.61  tff(c_148, plain, (v1_subset_1('#skF_7', u1_struct_0('#skF_6'))), inference(splitRight, [status(thm)], [c_86])).
% 12.89/5.61  tff(c_18923, plain, (v1_subset_1('#skF_7', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_18905, c_148])).
% 12.89/5.61  tff(c_18928, plain, $false, inference(negUnitSimplification, [status(thm)], [c_166, c_18923])).
% 12.89/5.61  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.89/5.61  
% 12.89/5.61  Inference rules
% 12.89/5.61  ----------------------
% 12.89/5.61  #Ref     : 0
% 12.89/5.61  #Sup     : 3563
% 12.89/5.61  #Fact    : 22
% 12.89/5.61  #Define  : 0
% 12.89/5.61  #Split   : 19
% 12.89/5.61  #Chain   : 0
% 12.89/5.61  #Close   : 0
% 12.89/5.61  
% 12.89/5.61  Ordering : KBO
% 12.89/5.61  
% 12.89/5.61  Simplification rules
% 12.89/5.61  ----------------------
% 12.89/5.61  #Subsume      : 1158
% 12.89/5.61  #Demod        : 1949
% 12.89/5.61  #Tautology    : 323
% 12.89/5.61  #SimpNegUnit  : 240
% 12.89/5.61  #BackRed      : 281
% 12.89/5.61  
% 12.89/5.61  #Partial instantiations: 0
% 12.89/5.61  #Strategies tried      : 1
% 12.89/5.61  
% 12.89/5.61  Timing (in seconds)
% 12.89/5.61  ----------------------
% 12.89/5.61  Preprocessing        : 0.34
% 12.89/5.61  Parsing              : 0.17
% 12.89/5.61  CNF conversion       : 0.03
% 12.89/5.61  Main loop            : 4.47
% 12.89/5.61  Inferencing          : 0.95
% 12.89/5.61  Reduction            : 0.99
% 12.89/5.61  Demodulation         : 0.69
% 12.89/5.61  BG Simplification    : 0.10
% 12.89/5.61  Subsumption          : 2.17
% 12.89/5.61  Abstraction          : 0.15
% 12.89/5.61  MUC search           : 0.00
% 12.89/5.61  Cooper               : 0.00
% 12.89/5.61  Total                : 4.86
% 12.89/5.61  Index Insertion      : 0.00
% 12.89/5.61  Index Deletion       : 0.00
% 12.89/5.61  Index Matching       : 0.00
% 12.89/5.61  BG Taut test         : 0.00
%------------------------------------------------------------------------------
