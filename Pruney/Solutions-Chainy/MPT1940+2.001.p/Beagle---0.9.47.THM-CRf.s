%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:53 EST 2020

% Result     : Theorem 3.98s
% Output     : CNFRefutation 3.98s
% Verified   : 
% Statistics : Number of formulae       :  129 ( 500 expanded)
%              Number of leaves         :   36 ( 195 expanded)
%              Depth                    :   15
%              Number of atoms          :  327 (1853 expanded)
%              Number of equality atoms :   44 ( 265 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > r2_hidden > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_orders_2 > l1_struct_0 > l1_pre_topc > l1_orders_2 > k9_yellow_6 > a_2_0_yellow_6 > #nlpp > u1_struct_0 > u1_orders_2 > k7_lattice3 > k2_yellow_1 > k1_zfmisc_1 > k1_yellow_1 > #skF_1 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(a_2_0_yellow_6,type,(
    a_2_0_yellow_6: ( $i * $i ) > $i )).

tff(v1_orders_2,type,(
    v1_orders_2: $i > $o )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k2_yellow_1,type,(
    k2_yellow_1: $i > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k7_lattice3,type,(
    k7_lattice3: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(k9_yellow_6,type,(
    k9_yellow_6: ( $i * $i ) > $i )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k1_yellow_1,type,(
    k1_yellow_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_orders_2,type,(
    u1_orders_2: $i > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_140,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(k9_yellow_6(A,B)))
               => ? [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                    & D = C
                    & r2_hidden(B,D)
                    & v3_pre_topc(D,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_yellow_6)).

tff(f_50,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_54,axiom,(
    ! [A] :
      ( v1_orders_2(k2_yellow_1(A))
      & l1_orders_2(k2_yellow_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_yellow_1)).

tff(f_58,axiom,(
    ! [A] :
      ( u1_struct_0(k2_yellow_1(A)) = A
      & u1_orders_2(k2_yellow_1(A)) = k1_yellow_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_yellow_1)).

tff(f_70,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => k9_yellow_6(A,B) = k7_lattice3(k2_yellow_1(a_2_0_yellow_6(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d17_yellow_6)).

tff(f_117,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => u1_struct_0(A) = u1_struct_0(k7_lattice3(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_yellow_6)).

tff(f_38,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_113,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(B)
        & v2_pre_topc(B)
        & l1_pre_topc(B)
        & m1_subset_1(C,u1_struct_0(B)) )
     => ( r2_hidden(A,a_2_0_yellow_6(B,C))
      <=> ? [D] :
            ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(B)))
            & A = D
            & r2_hidden(C,D)
            & v3_pre_topc(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_0_yellow_6)).

tff(f_46,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_81,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => l1_orders_2(k9_yellow_6(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_yellow_6)).

tff(f_93,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ~ v2_struct_0(k9_yellow_6(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc20_yellow_6)).

tff(c_50,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_48,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_46,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_12,plain,(
    ! [A_4] :
      ( l1_struct_0(A_4)
      | ~ l1_orders_2(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_44,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_16,plain,(
    ! [A_5] : l1_orders_2(k2_yellow_1(A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_18,plain,(
    ! [A_6] : u1_struct_0(k2_yellow_1(A_6)) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_835,plain,(
    ! [A_157,B_158] :
      ( k7_lattice3(k2_yellow_1(a_2_0_yellow_6(A_157,B_158))) = k9_yellow_6(A_157,B_158)
      | ~ m1_subset_1(B_158,u1_struct_0(A_157))
      | ~ l1_pre_topc(A_157)
      | ~ v2_pre_topc(A_157)
      | v2_struct_0(A_157) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_38,plain,(
    ! [A_20] :
      ( u1_struct_0(k7_lattice3(A_20)) = u1_struct_0(A_20)
      | ~ l1_orders_2(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_844,plain,(
    ! [A_157,B_158] :
      ( u1_struct_0(k2_yellow_1(a_2_0_yellow_6(A_157,B_158))) = u1_struct_0(k9_yellow_6(A_157,B_158))
      | ~ l1_orders_2(k2_yellow_1(a_2_0_yellow_6(A_157,B_158)))
      | ~ m1_subset_1(B_158,u1_struct_0(A_157))
      | ~ l1_pre_topc(A_157)
      | ~ v2_pre_topc(A_157)
      | v2_struct_0(A_157) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_835,c_38])).

tff(c_862,plain,(
    ! [A_165,B_166] :
      ( u1_struct_0(k9_yellow_6(A_165,B_166)) = a_2_0_yellow_6(A_165,B_166)
      | ~ m1_subset_1(B_166,u1_struct_0(A_165))
      | ~ l1_pre_topc(A_165)
      | ~ v2_pre_topc(A_165)
      | v2_struct_0(A_165) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_18,c_844])).

tff(c_875,plain,
    ( u1_struct_0(k9_yellow_6('#skF_2','#skF_3')) = a_2_0_yellow_6('#skF_2','#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_862])).

tff(c_884,plain,
    ( u1_struct_0(k9_yellow_6('#skF_2','#skF_3')) = a_2_0_yellow_6('#skF_2','#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_875])).

tff(c_885,plain,(
    u1_struct_0(k9_yellow_6('#skF_2','#skF_3')) = a_2_0_yellow_6('#skF_2','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_884])).

tff(c_42,plain,(
    m1_subset_1('#skF_4',u1_struct_0(k9_yellow_6('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_82,plain,(
    ! [B_41,A_42] :
      ( v1_xboole_0(B_41)
      | ~ m1_subset_1(B_41,A_42)
      | ~ v1_xboole_0(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_93,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_2','#skF_3'))) ),
    inference(resolution,[status(thm)],[c_42,c_82])).

tff(c_103,plain,(
    ~ v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_2','#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_93])).

tff(c_886,plain,(
    ~ v1_xboole_0(a_2_0_yellow_6('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_885,c_103])).

tff(c_514,plain,(
    ! [A_109,B_110] :
      ( k7_lattice3(k2_yellow_1(a_2_0_yellow_6(A_109,B_110))) = k9_yellow_6(A_109,B_110)
      | ~ m1_subset_1(B_110,u1_struct_0(A_109))
      | ~ l1_pre_topc(A_109)
      | ~ v2_pre_topc(A_109)
      | v2_struct_0(A_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_523,plain,(
    ! [A_109,B_110] :
      ( u1_struct_0(k2_yellow_1(a_2_0_yellow_6(A_109,B_110))) = u1_struct_0(k9_yellow_6(A_109,B_110))
      | ~ l1_orders_2(k2_yellow_1(a_2_0_yellow_6(A_109,B_110)))
      | ~ m1_subset_1(B_110,u1_struct_0(A_109))
      | ~ l1_pre_topc(A_109)
      | ~ v2_pre_topc(A_109)
      | v2_struct_0(A_109) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_514,c_38])).

tff(c_537,plain,(
    ! [A_117,B_118] :
      ( u1_struct_0(k9_yellow_6(A_117,B_118)) = a_2_0_yellow_6(A_117,B_118)
      | ~ m1_subset_1(B_118,u1_struct_0(A_117))
      | ~ l1_pre_topc(A_117)
      | ~ v2_pre_topc(A_117)
      | v2_struct_0(A_117) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_18,c_523])).

tff(c_550,plain,
    ( u1_struct_0(k9_yellow_6('#skF_2','#skF_3')) = a_2_0_yellow_6('#skF_2','#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_537])).

tff(c_559,plain,
    ( u1_struct_0(k9_yellow_6('#skF_2','#skF_3')) = a_2_0_yellow_6('#skF_2','#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_550])).

tff(c_560,plain,(
    u1_struct_0(k9_yellow_6('#skF_2','#skF_3')) = a_2_0_yellow_6('#skF_2','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_559])).

tff(c_561,plain,(
    ~ v1_xboole_0(a_2_0_yellow_6('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_560,c_103])).

tff(c_562,plain,(
    m1_subset_1('#skF_4',a_2_0_yellow_6('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_560,c_42])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( r2_hidden(B_2,A_1)
      | ~ m1_subset_1(B_2,A_1)
      | v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_174,plain,(
    ! [A_60,B_61] :
      ( k7_lattice3(k2_yellow_1(a_2_0_yellow_6(A_60,B_61))) = k9_yellow_6(A_60,B_61)
      | ~ m1_subset_1(B_61,u1_struct_0(A_60))
      | ~ l1_pre_topc(A_60)
      | ~ v2_pre_topc(A_60)
      | v2_struct_0(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_183,plain,(
    ! [A_60,B_61] :
      ( u1_struct_0(k2_yellow_1(a_2_0_yellow_6(A_60,B_61))) = u1_struct_0(k9_yellow_6(A_60,B_61))
      | ~ l1_orders_2(k2_yellow_1(a_2_0_yellow_6(A_60,B_61)))
      | ~ m1_subset_1(B_61,u1_struct_0(A_60))
      | ~ l1_pre_topc(A_60)
      | ~ v2_pre_topc(A_60)
      | v2_struct_0(A_60) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_174,c_38])).

tff(c_194,plain,(
    ! [A_64,B_65] :
      ( u1_struct_0(k9_yellow_6(A_64,B_65)) = a_2_0_yellow_6(A_64,B_65)
      | ~ m1_subset_1(B_65,u1_struct_0(A_64))
      | ~ l1_pre_topc(A_64)
      | ~ v2_pre_topc(A_64)
      | v2_struct_0(A_64) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_18,c_183])).

tff(c_207,plain,
    ( u1_struct_0(k9_yellow_6('#skF_2','#skF_3')) = a_2_0_yellow_6('#skF_2','#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_194])).

tff(c_216,plain,
    ( u1_struct_0(k9_yellow_6('#skF_2','#skF_3')) = a_2_0_yellow_6('#skF_2','#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_207])).

tff(c_217,plain,(
    u1_struct_0(k9_yellow_6('#skF_2','#skF_3')) = a_2_0_yellow_6('#skF_2','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_216])).

tff(c_218,plain,(
    ~ v1_xboole_0(a_2_0_yellow_6('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_217,c_103])).

tff(c_219,plain,(
    m1_subset_1('#skF_4',a_2_0_yellow_6('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_217,c_42])).

tff(c_40,plain,
    ( ~ v3_pre_topc('#skF_4','#skF_2')
    | ~ r2_hidden('#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_105,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_249,plain,(
    ! [A_68,B_69,C_70] :
      ( '#skF_1'(A_68,B_69,C_70) = A_68
      | ~ r2_hidden(A_68,a_2_0_yellow_6(B_69,C_70))
      | ~ m1_subset_1(C_70,u1_struct_0(B_69))
      | ~ l1_pre_topc(B_69)
      | ~ v2_pre_topc(B_69)
      | v2_struct_0(B_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_389,plain,(
    ! [B_95,B_96,C_97] :
      ( '#skF_1'(B_95,B_96,C_97) = B_95
      | ~ m1_subset_1(C_97,u1_struct_0(B_96))
      | ~ l1_pre_topc(B_96)
      | ~ v2_pre_topc(B_96)
      | v2_struct_0(B_96)
      | ~ m1_subset_1(B_95,a_2_0_yellow_6(B_96,C_97))
      | v1_xboole_0(a_2_0_yellow_6(B_96,C_97)) ) ),
    inference(resolution,[status(thm)],[c_4,c_249])).

tff(c_402,plain,(
    ! [B_95] :
      ( '#skF_1'(B_95,'#skF_2','#skF_3') = B_95
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ m1_subset_1(B_95,a_2_0_yellow_6('#skF_2','#skF_3'))
      | v1_xboole_0(a_2_0_yellow_6('#skF_2','#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_44,c_389])).

tff(c_409,plain,(
    ! [B_95] :
      ( '#skF_1'(B_95,'#skF_2','#skF_3') = B_95
      | v2_struct_0('#skF_2')
      | ~ m1_subset_1(B_95,a_2_0_yellow_6('#skF_2','#skF_3'))
      | v1_xboole_0(a_2_0_yellow_6('#skF_2','#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_402])).

tff(c_411,plain,(
    ! [B_98] :
      ( '#skF_1'(B_98,'#skF_2','#skF_3') = B_98
      | ~ m1_subset_1(B_98,a_2_0_yellow_6('#skF_2','#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_218,c_50,c_409])).

tff(c_419,plain,(
    '#skF_1'('#skF_4','#skF_2','#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_219,c_411])).

tff(c_36,plain,(
    ! [A_14,B_15,C_16] :
      ( m1_subset_1('#skF_1'(A_14,B_15,C_16),k1_zfmisc_1(u1_struct_0(B_15)))
      | ~ r2_hidden(A_14,a_2_0_yellow_6(B_15,C_16))
      | ~ m1_subset_1(C_16,u1_struct_0(B_15))
      | ~ l1_pre_topc(B_15)
      | ~ v2_pre_topc(B_15)
      | v2_struct_0(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_424,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ r2_hidden('#skF_4',a_2_0_yellow_6('#skF_2','#skF_3'))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_419,c_36])).

tff(c_431,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ r2_hidden('#skF_4',a_2_0_yellow_6('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_424])).

tff(c_432,plain,(
    ~ r2_hidden('#skF_4',a_2_0_yellow_6('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_105,c_431])).

tff(c_439,plain,
    ( ~ m1_subset_1('#skF_4',a_2_0_yellow_6('#skF_2','#skF_3'))
    | v1_xboole_0(a_2_0_yellow_6('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_4,c_432])).

tff(c_442,plain,(
    v1_xboole_0(a_2_0_yellow_6('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_219,c_439])).

tff(c_444,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_218,c_442])).

tff(c_445,plain,
    ( ~ r2_hidden('#skF_3','#skF_4')
    | ~ v3_pre_topc('#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_451,plain,(
    ~ v3_pre_topc('#skF_4','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_445])).

tff(c_590,plain,(
    ! [A_119,B_120,C_121] :
      ( '#skF_1'(A_119,B_120,C_121) = A_119
      | ~ r2_hidden(A_119,a_2_0_yellow_6(B_120,C_121))
      | ~ m1_subset_1(C_121,u1_struct_0(B_120))
      | ~ l1_pre_topc(B_120)
      | ~ v2_pre_topc(B_120)
      | v2_struct_0(B_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_710,plain,(
    ! [B_145,B_146,C_147] :
      ( '#skF_1'(B_145,B_146,C_147) = B_145
      | ~ m1_subset_1(C_147,u1_struct_0(B_146))
      | ~ l1_pre_topc(B_146)
      | ~ v2_pre_topc(B_146)
      | v2_struct_0(B_146)
      | ~ m1_subset_1(B_145,a_2_0_yellow_6(B_146,C_147))
      | v1_xboole_0(a_2_0_yellow_6(B_146,C_147)) ) ),
    inference(resolution,[status(thm)],[c_4,c_590])).

tff(c_723,plain,(
    ! [B_145] :
      ( '#skF_1'(B_145,'#skF_2','#skF_3') = B_145
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ m1_subset_1(B_145,a_2_0_yellow_6('#skF_2','#skF_3'))
      | v1_xboole_0(a_2_0_yellow_6('#skF_2','#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_44,c_710])).

tff(c_730,plain,(
    ! [B_145] :
      ( '#skF_1'(B_145,'#skF_2','#skF_3') = B_145
      | v2_struct_0('#skF_2')
      | ~ m1_subset_1(B_145,a_2_0_yellow_6('#skF_2','#skF_3'))
      | v1_xboole_0(a_2_0_yellow_6('#skF_2','#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_723])).

tff(c_732,plain,(
    ! [B_148] :
      ( '#skF_1'(B_148,'#skF_2','#skF_3') = B_148
      | ~ m1_subset_1(B_148,a_2_0_yellow_6('#skF_2','#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_561,c_50,c_730])).

tff(c_740,plain,(
    '#skF_1'('#skF_4','#skF_2','#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_562,c_732])).

tff(c_30,plain,(
    ! [A_14,B_15,C_16] :
      ( v3_pre_topc('#skF_1'(A_14,B_15,C_16),B_15)
      | ~ r2_hidden(A_14,a_2_0_yellow_6(B_15,C_16))
      | ~ m1_subset_1(C_16,u1_struct_0(B_15))
      | ~ l1_pre_topc(B_15)
      | ~ v2_pre_topc(B_15)
      | v2_struct_0(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_748,plain,
    ( v3_pre_topc('#skF_4','#skF_2')
    | ~ r2_hidden('#skF_4',a_2_0_yellow_6('#skF_2','#skF_3'))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_740,c_30])).

tff(c_755,plain,
    ( v3_pre_topc('#skF_4','#skF_2')
    | ~ r2_hidden('#skF_4',a_2_0_yellow_6('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_748])).

tff(c_756,plain,(
    ~ r2_hidden('#skF_4',a_2_0_yellow_6('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_451,c_755])).

tff(c_760,plain,
    ( ~ m1_subset_1('#skF_4',a_2_0_yellow_6('#skF_2','#skF_3'))
    | v1_xboole_0(a_2_0_yellow_6('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_4,c_756])).

tff(c_763,plain,(
    v1_xboole_0(a_2_0_yellow_6('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_562,c_760])).

tff(c_765,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_561,c_763])).

tff(c_766,plain,(
    ~ r2_hidden('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_445])).

tff(c_887,plain,(
    m1_subset_1('#skF_4',a_2_0_yellow_6('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_885,c_42])).

tff(c_916,plain,(
    ! [A_167,B_168,C_169] :
      ( '#skF_1'(A_167,B_168,C_169) = A_167
      | ~ r2_hidden(A_167,a_2_0_yellow_6(B_168,C_169))
      | ~ m1_subset_1(C_169,u1_struct_0(B_168))
      | ~ l1_pre_topc(B_168)
      | ~ v2_pre_topc(B_168)
      | v2_struct_0(B_168) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_1037,plain,(
    ! [B_195,B_196,C_197] :
      ( '#skF_1'(B_195,B_196,C_197) = B_195
      | ~ m1_subset_1(C_197,u1_struct_0(B_196))
      | ~ l1_pre_topc(B_196)
      | ~ v2_pre_topc(B_196)
      | v2_struct_0(B_196)
      | ~ m1_subset_1(B_195,a_2_0_yellow_6(B_196,C_197))
      | v1_xboole_0(a_2_0_yellow_6(B_196,C_197)) ) ),
    inference(resolution,[status(thm)],[c_4,c_916])).

tff(c_1050,plain,(
    ! [B_195] :
      ( '#skF_1'(B_195,'#skF_2','#skF_3') = B_195
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ m1_subset_1(B_195,a_2_0_yellow_6('#skF_2','#skF_3'))
      | v1_xboole_0(a_2_0_yellow_6('#skF_2','#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_44,c_1037])).

tff(c_1057,plain,(
    ! [B_195] :
      ( '#skF_1'(B_195,'#skF_2','#skF_3') = B_195
      | v2_struct_0('#skF_2')
      | ~ m1_subset_1(B_195,a_2_0_yellow_6('#skF_2','#skF_3'))
      | v1_xboole_0(a_2_0_yellow_6('#skF_2','#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_1050])).

tff(c_1059,plain,(
    ! [B_198] :
      ( '#skF_1'(B_198,'#skF_2','#skF_3') = B_198
      | ~ m1_subset_1(B_198,a_2_0_yellow_6('#skF_2','#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_886,c_50,c_1057])).

tff(c_1067,plain,(
    '#skF_1'('#skF_4','#skF_2','#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_887,c_1059])).

tff(c_924,plain,(
    ! [C_174,A_175,B_176] :
      ( r2_hidden(C_174,'#skF_1'(A_175,B_176,C_174))
      | ~ r2_hidden(A_175,a_2_0_yellow_6(B_176,C_174))
      | ~ m1_subset_1(C_174,u1_struct_0(B_176))
      | ~ l1_pre_topc(B_176)
      | ~ v2_pre_topc(B_176)
      | v2_struct_0(B_176) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_1237,plain,(
    ! [C_216,B_217,B_218] :
      ( r2_hidden(C_216,'#skF_1'(B_217,B_218,C_216))
      | ~ m1_subset_1(C_216,u1_struct_0(B_218))
      | ~ l1_pre_topc(B_218)
      | ~ v2_pre_topc(B_218)
      | v2_struct_0(B_218)
      | ~ m1_subset_1(B_217,a_2_0_yellow_6(B_218,C_216))
      | v1_xboole_0(a_2_0_yellow_6(B_218,C_216)) ) ),
    inference(resolution,[status(thm)],[c_4,c_924])).

tff(c_1243,plain,
    ( r2_hidden('#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ m1_subset_1('#skF_4',a_2_0_yellow_6('#skF_2','#skF_3'))
    | v1_xboole_0(a_2_0_yellow_6('#skF_2','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1067,c_1237])).

tff(c_1246,plain,
    ( r2_hidden('#skF_3','#skF_4')
    | v2_struct_0('#skF_2')
    | v1_xboole_0(a_2_0_yellow_6('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_887,c_48,c_46,c_44,c_1243])).

tff(c_1248,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_886,c_50,c_766,c_1246])).

tff(c_1250,plain,(
    v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_2','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_93])).

tff(c_10,plain,(
    ! [A_3] :
      ( ~ v1_xboole_0(u1_struct_0(A_3))
      | ~ l1_struct_0(A_3)
      | v2_struct_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_1254,plain,
    ( ~ l1_struct_0(k9_yellow_6('#skF_2','#skF_3'))
    | v2_struct_0(k9_yellow_6('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_1250,c_10])).

tff(c_1262,plain,(
    ~ l1_struct_0(k9_yellow_6('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1254])).

tff(c_1266,plain,(
    ~ l1_orders_2(k9_yellow_6('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_12,c_1262])).

tff(c_1275,plain,(
    ! [A_225,B_226] :
      ( l1_orders_2(k9_yellow_6(A_225,B_226))
      | ~ m1_subset_1(B_226,u1_struct_0(A_225))
      | ~ l1_pre_topc(A_225)
      | ~ v2_pre_topc(A_225)
      | v2_struct_0(A_225) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_1288,plain,
    ( l1_orders_2(k9_yellow_6('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_1275])).

tff(c_1296,plain,
    ( l1_orders_2(k9_yellow_6('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_1288])).

tff(c_1298,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_1266,c_1296])).

tff(c_1299,plain,(
    v2_struct_0(k9_yellow_6('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_1254])).

tff(c_1309,plain,(
    ! [A_228,B_229] :
      ( ~ v2_struct_0(k9_yellow_6(A_228,B_229))
      | ~ m1_subset_1(B_229,u1_struct_0(A_228))
      | ~ l1_pre_topc(A_228)
      | ~ v2_pre_topc(A_228)
      | v2_struct_0(A_228) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_1322,plain,
    ( ~ v2_struct_0(k9_yellow_6('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_1309])).

tff(c_1331,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_1299,c_1322])).

tff(c_1333,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_1331])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.33  % Computer   : n024.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % DateTime   : Tue Dec  1 09:50:51 EST 2020
% 0.14/0.33  % CPUTime    : 
% 0.14/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.98/1.69  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.98/1.71  
% 3.98/1.71  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.98/1.71  %$ v3_pre_topc > r2_hidden > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_orders_2 > l1_struct_0 > l1_pre_topc > l1_orders_2 > k9_yellow_6 > a_2_0_yellow_6 > #nlpp > u1_struct_0 > u1_orders_2 > k7_lattice3 > k2_yellow_1 > k1_zfmisc_1 > k1_yellow_1 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 3.98/1.71  
% 3.98/1.71  %Foreground sorts:
% 3.98/1.71  
% 3.98/1.71  
% 3.98/1.71  %Background operators:
% 3.98/1.71  
% 3.98/1.71  
% 3.98/1.71  %Foreground operators:
% 3.98/1.71  tff(a_2_0_yellow_6, type, a_2_0_yellow_6: ($i * $i) > $i).
% 3.98/1.71  tff(v1_orders_2, type, v1_orders_2: $i > $o).
% 3.98/1.71  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.98/1.71  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.98/1.71  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 3.98/1.71  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.98/1.71  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.98/1.71  tff(k2_yellow_1, type, k2_yellow_1: $i > $i).
% 3.98/1.71  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.98/1.71  tff(k7_lattice3, type, k7_lattice3: $i > $i).
% 3.98/1.71  tff('#skF_2', type, '#skF_2': $i).
% 3.98/1.71  tff('#skF_3', type, '#skF_3': $i).
% 3.98/1.71  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.98/1.71  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.98/1.71  tff(k9_yellow_6, type, k9_yellow_6: ($i * $i) > $i).
% 3.98/1.71  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 3.98/1.71  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.98/1.71  tff('#skF_4', type, '#skF_4': $i).
% 3.98/1.71  tff(k1_yellow_1, type, k1_yellow_1: $i > $i).
% 3.98/1.71  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.98/1.71  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.98/1.71  tff(u1_orders_2, type, u1_orders_2: $i > $i).
% 3.98/1.71  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.98/1.71  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.98/1.71  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.98/1.71  
% 3.98/1.73  tff(f_140, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(k9_yellow_6(A, B))) => (?[D]: (((m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) & (D = C)) & r2_hidden(B, D)) & v3_pre_topc(D, A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_yellow_6)).
% 3.98/1.73  tff(f_50, axiom, (![A]: (l1_orders_2(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 3.98/1.73  tff(f_54, axiom, (![A]: (v1_orders_2(k2_yellow_1(A)) & l1_orders_2(k2_yellow_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_yellow_1)).
% 3.98/1.73  tff(f_58, axiom, (![A]: ((u1_struct_0(k2_yellow_1(A)) = A) & (u1_orders_2(k2_yellow_1(A)) = k1_yellow_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_yellow_1)).
% 3.98/1.73  tff(f_70, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (k9_yellow_6(A, B) = k7_lattice3(k2_yellow_1(a_2_0_yellow_6(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d17_yellow_6)).
% 3.98/1.73  tff(f_117, axiom, (![A]: (l1_orders_2(A) => (u1_struct_0(A) = u1_struct_0(k7_lattice3(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_yellow_6)).
% 3.98/1.73  tff(f_38, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 3.98/1.73  tff(f_113, axiom, (![A, B, C]: ((((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) & m1_subset_1(C, u1_struct_0(B))) => (r2_hidden(A, a_2_0_yellow_6(B, C)) <=> (?[D]: (((m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) & (A = D)) & r2_hidden(C, D)) & v3_pre_topc(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fraenkel_a_2_0_yellow_6)).
% 3.98/1.73  tff(f_46, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 3.98/1.73  tff(f_81, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => l1_orders_2(k9_yellow_6(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k9_yellow_6)).
% 3.98/1.73  tff(f_93, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => ~v2_struct_0(k9_yellow_6(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc20_yellow_6)).
% 3.98/1.73  tff(c_50, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_140])).
% 3.98/1.73  tff(c_48, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_140])).
% 3.98/1.73  tff(c_46, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_140])).
% 3.98/1.73  tff(c_12, plain, (![A_4]: (l1_struct_0(A_4) | ~l1_orders_2(A_4))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.98/1.73  tff(c_44, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_140])).
% 3.98/1.73  tff(c_16, plain, (![A_5]: (l1_orders_2(k2_yellow_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.98/1.73  tff(c_18, plain, (![A_6]: (u1_struct_0(k2_yellow_1(A_6))=A_6)), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.98/1.73  tff(c_835, plain, (![A_157, B_158]: (k7_lattice3(k2_yellow_1(a_2_0_yellow_6(A_157, B_158)))=k9_yellow_6(A_157, B_158) | ~m1_subset_1(B_158, u1_struct_0(A_157)) | ~l1_pre_topc(A_157) | ~v2_pre_topc(A_157) | v2_struct_0(A_157))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.98/1.73  tff(c_38, plain, (![A_20]: (u1_struct_0(k7_lattice3(A_20))=u1_struct_0(A_20) | ~l1_orders_2(A_20))), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.98/1.73  tff(c_844, plain, (![A_157, B_158]: (u1_struct_0(k2_yellow_1(a_2_0_yellow_6(A_157, B_158)))=u1_struct_0(k9_yellow_6(A_157, B_158)) | ~l1_orders_2(k2_yellow_1(a_2_0_yellow_6(A_157, B_158))) | ~m1_subset_1(B_158, u1_struct_0(A_157)) | ~l1_pre_topc(A_157) | ~v2_pre_topc(A_157) | v2_struct_0(A_157))), inference(superposition, [status(thm), theory('equality')], [c_835, c_38])).
% 3.98/1.73  tff(c_862, plain, (![A_165, B_166]: (u1_struct_0(k9_yellow_6(A_165, B_166))=a_2_0_yellow_6(A_165, B_166) | ~m1_subset_1(B_166, u1_struct_0(A_165)) | ~l1_pre_topc(A_165) | ~v2_pre_topc(A_165) | v2_struct_0(A_165))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_18, c_844])).
% 3.98/1.73  tff(c_875, plain, (u1_struct_0(k9_yellow_6('#skF_2', '#skF_3'))=a_2_0_yellow_6('#skF_2', '#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_44, c_862])).
% 3.98/1.73  tff(c_884, plain, (u1_struct_0(k9_yellow_6('#skF_2', '#skF_3'))=a_2_0_yellow_6('#skF_2', '#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_875])).
% 3.98/1.73  tff(c_885, plain, (u1_struct_0(k9_yellow_6('#skF_2', '#skF_3'))=a_2_0_yellow_6('#skF_2', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_50, c_884])).
% 3.98/1.73  tff(c_42, plain, (m1_subset_1('#skF_4', u1_struct_0(k9_yellow_6('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_140])).
% 3.98/1.73  tff(c_82, plain, (![B_41, A_42]: (v1_xboole_0(B_41) | ~m1_subset_1(B_41, A_42) | ~v1_xboole_0(A_42))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.98/1.73  tff(c_93, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_2', '#skF_3')))), inference(resolution, [status(thm)], [c_42, c_82])).
% 3.98/1.73  tff(c_103, plain, (~v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_2', '#skF_3')))), inference(splitLeft, [status(thm)], [c_93])).
% 3.98/1.73  tff(c_886, plain, (~v1_xboole_0(a_2_0_yellow_6('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_885, c_103])).
% 3.98/1.73  tff(c_514, plain, (![A_109, B_110]: (k7_lattice3(k2_yellow_1(a_2_0_yellow_6(A_109, B_110)))=k9_yellow_6(A_109, B_110) | ~m1_subset_1(B_110, u1_struct_0(A_109)) | ~l1_pre_topc(A_109) | ~v2_pre_topc(A_109) | v2_struct_0(A_109))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.98/1.73  tff(c_523, plain, (![A_109, B_110]: (u1_struct_0(k2_yellow_1(a_2_0_yellow_6(A_109, B_110)))=u1_struct_0(k9_yellow_6(A_109, B_110)) | ~l1_orders_2(k2_yellow_1(a_2_0_yellow_6(A_109, B_110))) | ~m1_subset_1(B_110, u1_struct_0(A_109)) | ~l1_pre_topc(A_109) | ~v2_pre_topc(A_109) | v2_struct_0(A_109))), inference(superposition, [status(thm), theory('equality')], [c_514, c_38])).
% 3.98/1.73  tff(c_537, plain, (![A_117, B_118]: (u1_struct_0(k9_yellow_6(A_117, B_118))=a_2_0_yellow_6(A_117, B_118) | ~m1_subset_1(B_118, u1_struct_0(A_117)) | ~l1_pre_topc(A_117) | ~v2_pre_topc(A_117) | v2_struct_0(A_117))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_18, c_523])).
% 3.98/1.73  tff(c_550, plain, (u1_struct_0(k9_yellow_6('#skF_2', '#skF_3'))=a_2_0_yellow_6('#skF_2', '#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_44, c_537])).
% 3.98/1.73  tff(c_559, plain, (u1_struct_0(k9_yellow_6('#skF_2', '#skF_3'))=a_2_0_yellow_6('#skF_2', '#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_550])).
% 3.98/1.73  tff(c_560, plain, (u1_struct_0(k9_yellow_6('#skF_2', '#skF_3'))=a_2_0_yellow_6('#skF_2', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_50, c_559])).
% 3.98/1.73  tff(c_561, plain, (~v1_xboole_0(a_2_0_yellow_6('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_560, c_103])).
% 3.98/1.73  tff(c_562, plain, (m1_subset_1('#skF_4', a_2_0_yellow_6('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_560, c_42])).
% 3.98/1.73  tff(c_4, plain, (![B_2, A_1]: (r2_hidden(B_2, A_1) | ~m1_subset_1(B_2, A_1) | v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.98/1.73  tff(c_174, plain, (![A_60, B_61]: (k7_lattice3(k2_yellow_1(a_2_0_yellow_6(A_60, B_61)))=k9_yellow_6(A_60, B_61) | ~m1_subset_1(B_61, u1_struct_0(A_60)) | ~l1_pre_topc(A_60) | ~v2_pre_topc(A_60) | v2_struct_0(A_60))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.98/1.73  tff(c_183, plain, (![A_60, B_61]: (u1_struct_0(k2_yellow_1(a_2_0_yellow_6(A_60, B_61)))=u1_struct_0(k9_yellow_6(A_60, B_61)) | ~l1_orders_2(k2_yellow_1(a_2_0_yellow_6(A_60, B_61))) | ~m1_subset_1(B_61, u1_struct_0(A_60)) | ~l1_pre_topc(A_60) | ~v2_pre_topc(A_60) | v2_struct_0(A_60))), inference(superposition, [status(thm), theory('equality')], [c_174, c_38])).
% 3.98/1.73  tff(c_194, plain, (![A_64, B_65]: (u1_struct_0(k9_yellow_6(A_64, B_65))=a_2_0_yellow_6(A_64, B_65) | ~m1_subset_1(B_65, u1_struct_0(A_64)) | ~l1_pre_topc(A_64) | ~v2_pre_topc(A_64) | v2_struct_0(A_64))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_18, c_183])).
% 3.98/1.73  tff(c_207, plain, (u1_struct_0(k9_yellow_6('#skF_2', '#skF_3'))=a_2_0_yellow_6('#skF_2', '#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_44, c_194])).
% 3.98/1.73  tff(c_216, plain, (u1_struct_0(k9_yellow_6('#skF_2', '#skF_3'))=a_2_0_yellow_6('#skF_2', '#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_207])).
% 3.98/1.73  tff(c_217, plain, (u1_struct_0(k9_yellow_6('#skF_2', '#skF_3'))=a_2_0_yellow_6('#skF_2', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_50, c_216])).
% 3.98/1.73  tff(c_218, plain, (~v1_xboole_0(a_2_0_yellow_6('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_217, c_103])).
% 3.98/1.73  tff(c_219, plain, (m1_subset_1('#skF_4', a_2_0_yellow_6('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_217, c_42])).
% 3.98/1.73  tff(c_40, plain, (~v3_pre_topc('#skF_4', '#skF_2') | ~r2_hidden('#skF_3', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_140])).
% 3.98/1.73  tff(c_105, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitLeft, [status(thm)], [c_40])).
% 3.98/1.73  tff(c_249, plain, (![A_68, B_69, C_70]: ('#skF_1'(A_68, B_69, C_70)=A_68 | ~r2_hidden(A_68, a_2_0_yellow_6(B_69, C_70)) | ~m1_subset_1(C_70, u1_struct_0(B_69)) | ~l1_pre_topc(B_69) | ~v2_pre_topc(B_69) | v2_struct_0(B_69))), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.98/1.73  tff(c_389, plain, (![B_95, B_96, C_97]: ('#skF_1'(B_95, B_96, C_97)=B_95 | ~m1_subset_1(C_97, u1_struct_0(B_96)) | ~l1_pre_topc(B_96) | ~v2_pre_topc(B_96) | v2_struct_0(B_96) | ~m1_subset_1(B_95, a_2_0_yellow_6(B_96, C_97)) | v1_xboole_0(a_2_0_yellow_6(B_96, C_97)))), inference(resolution, [status(thm)], [c_4, c_249])).
% 3.98/1.73  tff(c_402, plain, (![B_95]: ('#skF_1'(B_95, '#skF_2', '#skF_3')=B_95 | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~m1_subset_1(B_95, a_2_0_yellow_6('#skF_2', '#skF_3')) | v1_xboole_0(a_2_0_yellow_6('#skF_2', '#skF_3')))), inference(resolution, [status(thm)], [c_44, c_389])).
% 3.98/1.73  tff(c_409, plain, (![B_95]: ('#skF_1'(B_95, '#skF_2', '#skF_3')=B_95 | v2_struct_0('#skF_2') | ~m1_subset_1(B_95, a_2_0_yellow_6('#skF_2', '#skF_3')) | v1_xboole_0(a_2_0_yellow_6('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_402])).
% 3.98/1.73  tff(c_411, plain, (![B_98]: ('#skF_1'(B_98, '#skF_2', '#skF_3')=B_98 | ~m1_subset_1(B_98, a_2_0_yellow_6('#skF_2', '#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_218, c_50, c_409])).
% 3.98/1.73  tff(c_419, plain, ('#skF_1'('#skF_4', '#skF_2', '#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_219, c_411])).
% 3.98/1.73  tff(c_36, plain, (![A_14, B_15, C_16]: (m1_subset_1('#skF_1'(A_14, B_15, C_16), k1_zfmisc_1(u1_struct_0(B_15))) | ~r2_hidden(A_14, a_2_0_yellow_6(B_15, C_16)) | ~m1_subset_1(C_16, u1_struct_0(B_15)) | ~l1_pre_topc(B_15) | ~v2_pre_topc(B_15) | v2_struct_0(B_15))), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.98/1.73  tff(c_424, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~r2_hidden('#skF_4', a_2_0_yellow_6('#skF_2', '#skF_3')) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_419, c_36])).
% 3.98/1.73  tff(c_431, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~r2_hidden('#skF_4', a_2_0_yellow_6('#skF_2', '#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_424])).
% 3.98/1.73  tff(c_432, plain, (~r2_hidden('#skF_4', a_2_0_yellow_6('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_50, c_105, c_431])).
% 3.98/1.73  tff(c_439, plain, (~m1_subset_1('#skF_4', a_2_0_yellow_6('#skF_2', '#skF_3')) | v1_xboole_0(a_2_0_yellow_6('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_4, c_432])).
% 3.98/1.73  tff(c_442, plain, (v1_xboole_0(a_2_0_yellow_6('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_219, c_439])).
% 3.98/1.73  tff(c_444, plain, $false, inference(negUnitSimplification, [status(thm)], [c_218, c_442])).
% 3.98/1.73  tff(c_445, plain, (~r2_hidden('#skF_3', '#skF_4') | ~v3_pre_topc('#skF_4', '#skF_2')), inference(splitRight, [status(thm)], [c_40])).
% 3.98/1.73  tff(c_451, plain, (~v3_pre_topc('#skF_4', '#skF_2')), inference(splitLeft, [status(thm)], [c_445])).
% 3.98/1.73  tff(c_590, plain, (![A_119, B_120, C_121]: ('#skF_1'(A_119, B_120, C_121)=A_119 | ~r2_hidden(A_119, a_2_0_yellow_6(B_120, C_121)) | ~m1_subset_1(C_121, u1_struct_0(B_120)) | ~l1_pre_topc(B_120) | ~v2_pre_topc(B_120) | v2_struct_0(B_120))), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.98/1.73  tff(c_710, plain, (![B_145, B_146, C_147]: ('#skF_1'(B_145, B_146, C_147)=B_145 | ~m1_subset_1(C_147, u1_struct_0(B_146)) | ~l1_pre_topc(B_146) | ~v2_pre_topc(B_146) | v2_struct_0(B_146) | ~m1_subset_1(B_145, a_2_0_yellow_6(B_146, C_147)) | v1_xboole_0(a_2_0_yellow_6(B_146, C_147)))), inference(resolution, [status(thm)], [c_4, c_590])).
% 3.98/1.73  tff(c_723, plain, (![B_145]: ('#skF_1'(B_145, '#skF_2', '#skF_3')=B_145 | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~m1_subset_1(B_145, a_2_0_yellow_6('#skF_2', '#skF_3')) | v1_xboole_0(a_2_0_yellow_6('#skF_2', '#skF_3')))), inference(resolution, [status(thm)], [c_44, c_710])).
% 3.98/1.73  tff(c_730, plain, (![B_145]: ('#skF_1'(B_145, '#skF_2', '#skF_3')=B_145 | v2_struct_0('#skF_2') | ~m1_subset_1(B_145, a_2_0_yellow_6('#skF_2', '#skF_3')) | v1_xboole_0(a_2_0_yellow_6('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_723])).
% 3.98/1.73  tff(c_732, plain, (![B_148]: ('#skF_1'(B_148, '#skF_2', '#skF_3')=B_148 | ~m1_subset_1(B_148, a_2_0_yellow_6('#skF_2', '#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_561, c_50, c_730])).
% 3.98/1.73  tff(c_740, plain, ('#skF_1'('#skF_4', '#skF_2', '#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_562, c_732])).
% 3.98/1.73  tff(c_30, plain, (![A_14, B_15, C_16]: (v3_pre_topc('#skF_1'(A_14, B_15, C_16), B_15) | ~r2_hidden(A_14, a_2_0_yellow_6(B_15, C_16)) | ~m1_subset_1(C_16, u1_struct_0(B_15)) | ~l1_pre_topc(B_15) | ~v2_pre_topc(B_15) | v2_struct_0(B_15))), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.98/1.73  tff(c_748, plain, (v3_pre_topc('#skF_4', '#skF_2') | ~r2_hidden('#skF_4', a_2_0_yellow_6('#skF_2', '#skF_3')) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_740, c_30])).
% 3.98/1.73  tff(c_755, plain, (v3_pre_topc('#skF_4', '#skF_2') | ~r2_hidden('#skF_4', a_2_0_yellow_6('#skF_2', '#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_748])).
% 3.98/1.73  tff(c_756, plain, (~r2_hidden('#skF_4', a_2_0_yellow_6('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_50, c_451, c_755])).
% 3.98/1.73  tff(c_760, plain, (~m1_subset_1('#skF_4', a_2_0_yellow_6('#skF_2', '#skF_3')) | v1_xboole_0(a_2_0_yellow_6('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_4, c_756])).
% 3.98/1.73  tff(c_763, plain, (v1_xboole_0(a_2_0_yellow_6('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_562, c_760])).
% 3.98/1.73  tff(c_765, plain, $false, inference(negUnitSimplification, [status(thm)], [c_561, c_763])).
% 3.98/1.73  tff(c_766, plain, (~r2_hidden('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_445])).
% 3.98/1.73  tff(c_887, plain, (m1_subset_1('#skF_4', a_2_0_yellow_6('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_885, c_42])).
% 3.98/1.73  tff(c_916, plain, (![A_167, B_168, C_169]: ('#skF_1'(A_167, B_168, C_169)=A_167 | ~r2_hidden(A_167, a_2_0_yellow_6(B_168, C_169)) | ~m1_subset_1(C_169, u1_struct_0(B_168)) | ~l1_pre_topc(B_168) | ~v2_pre_topc(B_168) | v2_struct_0(B_168))), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.98/1.73  tff(c_1037, plain, (![B_195, B_196, C_197]: ('#skF_1'(B_195, B_196, C_197)=B_195 | ~m1_subset_1(C_197, u1_struct_0(B_196)) | ~l1_pre_topc(B_196) | ~v2_pre_topc(B_196) | v2_struct_0(B_196) | ~m1_subset_1(B_195, a_2_0_yellow_6(B_196, C_197)) | v1_xboole_0(a_2_0_yellow_6(B_196, C_197)))), inference(resolution, [status(thm)], [c_4, c_916])).
% 3.98/1.73  tff(c_1050, plain, (![B_195]: ('#skF_1'(B_195, '#skF_2', '#skF_3')=B_195 | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~m1_subset_1(B_195, a_2_0_yellow_6('#skF_2', '#skF_3')) | v1_xboole_0(a_2_0_yellow_6('#skF_2', '#skF_3')))), inference(resolution, [status(thm)], [c_44, c_1037])).
% 3.98/1.73  tff(c_1057, plain, (![B_195]: ('#skF_1'(B_195, '#skF_2', '#skF_3')=B_195 | v2_struct_0('#skF_2') | ~m1_subset_1(B_195, a_2_0_yellow_6('#skF_2', '#skF_3')) | v1_xboole_0(a_2_0_yellow_6('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_1050])).
% 3.98/1.73  tff(c_1059, plain, (![B_198]: ('#skF_1'(B_198, '#skF_2', '#skF_3')=B_198 | ~m1_subset_1(B_198, a_2_0_yellow_6('#skF_2', '#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_886, c_50, c_1057])).
% 3.98/1.73  tff(c_1067, plain, ('#skF_1'('#skF_4', '#skF_2', '#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_887, c_1059])).
% 3.98/1.73  tff(c_924, plain, (![C_174, A_175, B_176]: (r2_hidden(C_174, '#skF_1'(A_175, B_176, C_174)) | ~r2_hidden(A_175, a_2_0_yellow_6(B_176, C_174)) | ~m1_subset_1(C_174, u1_struct_0(B_176)) | ~l1_pre_topc(B_176) | ~v2_pre_topc(B_176) | v2_struct_0(B_176))), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.98/1.73  tff(c_1237, plain, (![C_216, B_217, B_218]: (r2_hidden(C_216, '#skF_1'(B_217, B_218, C_216)) | ~m1_subset_1(C_216, u1_struct_0(B_218)) | ~l1_pre_topc(B_218) | ~v2_pre_topc(B_218) | v2_struct_0(B_218) | ~m1_subset_1(B_217, a_2_0_yellow_6(B_218, C_216)) | v1_xboole_0(a_2_0_yellow_6(B_218, C_216)))), inference(resolution, [status(thm)], [c_4, c_924])).
% 3.98/1.73  tff(c_1243, plain, (r2_hidden('#skF_3', '#skF_4') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~m1_subset_1('#skF_4', a_2_0_yellow_6('#skF_2', '#skF_3')) | v1_xboole_0(a_2_0_yellow_6('#skF_2', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1067, c_1237])).
% 3.98/1.73  tff(c_1246, plain, (r2_hidden('#skF_3', '#skF_4') | v2_struct_0('#skF_2') | v1_xboole_0(a_2_0_yellow_6('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_887, c_48, c_46, c_44, c_1243])).
% 3.98/1.73  tff(c_1248, plain, $false, inference(negUnitSimplification, [status(thm)], [c_886, c_50, c_766, c_1246])).
% 3.98/1.73  tff(c_1250, plain, (v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_2', '#skF_3')))), inference(splitRight, [status(thm)], [c_93])).
% 3.98/1.73  tff(c_10, plain, (![A_3]: (~v1_xboole_0(u1_struct_0(A_3)) | ~l1_struct_0(A_3) | v2_struct_0(A_3))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.98/1.73  tff(c_1254, plain, (~l1_struct_0(k9_yellow_6('#skF_2', '#skF_3')) | v2_struct_0(k9_yellow_6('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_1250, c_10])).
% 3.98/1.73  tff(c_1262, plain, (~l1_struct_0(k9_yellow_6('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_1254])).
% 3.98/1.73  tff(c_1266, plain, (~l1_orders_2(k9_yellow_6('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_12, c_1262])).
% 3.98/1.73  tff(c_1275, plain, (![A_225, B_226]: (l1_orders_2(k9_yellow_6(A_225, B_226)) | ~m1_subset_1(B_226, u1_struct_0(A_225)) | ~l1_pre_topc(A_225) | ~v2_pre_topc(A_225) | v2_struct_0(A_225))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.98/1.73  tff(c_1288, plain, (l1_orders_2(k9_yellow_6('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_44, c_1275])).
% 3.98/1.73  tff(c_1296, plain, (l1_orders_2(k9_yellow_6('#skF_2', '#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_1288])).
% 3.98/1.73  tff(c_1298, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_1266, c_1296])).
% 3.98/1.73  tff(c_1299, plain, (v2_struct_0(k9_yellow_6('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_1254])).
% 3.98/1.73  tff(c_1309, plain, (![A_228, B_229]: (~v2_struct_0(k9_yellow_6(A_228, B_229)) | ~m1_subset_1(B_229, u1_struct_0(A_228)) | ~l1_pre_topc(A_228) | ~v2_pre_topc(A_228) | v2_struct_0(A_228))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.98/1.73  tff(c_1322, plain, (~v2_struct_0(k9_yellow_6('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_44, c_1309])).
% 3.98/1.73  tff(c_1331, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_1299, c_1322])).
% 3.98/1.73  tff(c_1333, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_1331])).
% 3.98/1.73  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.98/1.73  
% 3.98/1.73  Inference rules
% 3.98/1.73  ----------------------
% 3.98/1.73  #Ref     : 0
% 3.98/1.73  #Sup     : 306
% 3.98/1.73  #Fact    : 0
% 3.98/1.73  #Define  : 0
% 3.98/1.73  #Split   : 14
% 3.98/1.73  #Chain   : 0
% 3.98/1.73  #Close   : 0
% 3.98/1.73  
% 3.98/1.73  Ordering : KBO
% 3.98/1.73  
% 3.98/1.73  Simplification rules
% 3.98/1.73  ----------------------
% 3.98/1.73  #Subsume      : 46
% 3.98/1.73  #Demod        : 121
% 3.98/1.73  #Tautology    : 53
% 3.98/1.73  #SimpNegUnit  : 67
% 3.98/1.73  #BackRed      : 6
% 3.98/1.73  
% 3.98/1.73  #Partial instantiations: 0
% 3.98/1.73  #Strategies tried      : 1
% 3.98/1.73  
% 3.98/1.73  Timing (in seconds)
% 3.98/1.73  ----------------------
% 3.98/1.74  Preprocessing        : 0.32
% 3.98/1.74  Parsing              : 0.17
% 3.98/1.74  CNF conversion       : 0.02
% 3.98/1.74  Main loop            : 0.63
% 3.98/1.74  Inferencing          : 0.24
% 3.98/1.74  Reduction            : 0.19
% 3.98/1.74  Demodulation         : 0.13
% 3.98/1.74  BG Simplification    : 0.03
% 3.98/1.74  Subsumption          : 0.12
% 3.98/1.74  Abstraction          : 0.03
% 3.98/1.74  MUC search           : 0.00
% 3.98/1.74  Cooper               : 0.00
% 3.98/1.74  Total                : 1.00
% 3.98/1.74  Index Insertion      : 0.00
% 3.98/1.74  Index Deletion       : 0.00
% 3.98/1.74  Index Matching       : 0.00
% 3.98/1.74  BG Taut test         : 0.00
%------------------------------------------------------------------------------
