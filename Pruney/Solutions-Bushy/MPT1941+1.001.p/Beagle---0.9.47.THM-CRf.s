%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1941+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:42 EST 2020

% Result     : Theorem 3.32s
% Output     : CNFRefutation 3.53s
% Verified   : 
% Statistics : Number of formulae       :  128 ( 352 expanded)
%              Number of leaves         :   40 ( 142 expanded)
%              Depth                    :   18
%              Number of atoms          :  279 (1045 expanded)
%              Number of equality atoms :   71 ( 171 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v1_partfun1 > r2_hidden > m1_subset_1 > v8_relat_2 > v4_relat_2 > v2_struct_0 > v2_pre_topc > v1_relat_2 > v1_orders_2 > l1_pre_topc > l1_orders_2 > k9_yellow_6 > k2_zfmisc_1 > g1_orders_2 > a_2_0_yellow_6 > #nlpp > u1_struct_0 > u1_orders_2 > k7_lattice3 > k2_yellow_1 > k1_zfmisc_1 > k1_yellow_1 > k1_wellord2 > #skF_1 > #skF_2 > #skF_3 > #skF_4

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

tff(v1_relat_2,type,(
    v1_relat_2: $i > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(v8_relat_2,type,(
    v8_relat_2: $i > $o )).

tff(g1_orders_2,type,(
    g1_orders_2: ( $i * $i ) > $i )).

tff(v4_relat_2,type,(
    v4_relat_2: $i > $o )).

tff(k7_lattice3,type,(
    k7_lattice3: $i > $i )).

tff(k1_wellord2,type,(
    k1_wellord2: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k9_yellow_6,type,(
    k9_yellow_6: ( $i * $i ) > $i )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_119,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( r2_hidden(C,u1_struct_0(k9_yellow_6(A,B)))
                <=> ( r2_hidden(B,C)
                    & v3_pre_topc(C,A) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_yellow_6)).

tff(f_78,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fraenkel_a_2_0_yellow_6)).

tff(f_58,axiom,(
    ! [A] :
      ( v1_orders_2(k2_yellow_1(A))
      & l1_orders_2(k2_yellow_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_yellow_1)).

tff(f_30,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v1_orders_2(A)
       => A = g1_orders_2(u1_struct_0(A),u1_orders_2(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',abstractness_v1_orders_2)).

tff(f_89,axiom,(
    ! [A] : k1_yellow_1(A) = k1_wellord2(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_yellow_1)).

tff(f_54,axiom,(
    ! [A] :
      ( v1_relat_2(k1_yellow_1(A))
      & v4_relat_2(k1_yellow_1(A))
      & v8_relat_2(k1_yellow_1(A))
      & v1_partfun1(k1_yellow_1(A),A)
      & m1_subset_1(k1_yellow_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_yellow_1)).

tff(f_44,axiom,(
    ! [A] : k2_yellow_1(A) = g1_orders_2(A,k1_yellow_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_yellow_1)).

tff(f_87,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A)))
     => ! [C,D] :
          ( g1_orders_2(A,B) = g1_orders_2(C,D)
         => ( A = C
            & B = D ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',free_g1_orders_2)).

tff(f_42,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => k9_yellow_6(A,B) = k7_lattice3(k2_yellow_1(a_2_0_yellow_6(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d17_yellow_6)).

tff(f_93,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => u1_struct_0(A) = u1_struct_0(k7_lattice3(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_yellow_6)).

tff(c_50,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_44,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_62,plain,
    ( r2_hidden('#skF_4',u1_struct_0(k9_yellow_6('#skF_2','#skF_3')))
    | r2_hidden('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_104,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_48,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_46,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_58,plain,
    ( r2_hidden('#skF_4',u1_struct_0(k9_yellow_6('#skF_2','#skF_3')))
    | v3_pre_topc('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_103,plain,(
    v3_pre_topc('#skF_4','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_42,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_462,plain,(
    ! [D_102,B_103,C_104] :
      ( r2_hidden(D_102,a_2_0_yellow_6(B_103,C_104))
      | ~ v3_pre_topc(D_102,B_103)
      | ~ r2_hidden(C_104,D_102)
      | ~ m1_subset_1(D_102,k1_zfmisc_1(u1_struct_0(B_103)))
      | ~ m1_subset_1(C_104,u1_struct_0(B_103))
      | ~ l1_pre_topc(B_103)
      | ~ v2_pre_topc(B_103)
      | v2_struct_0(B_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_474,plain,(
    ! [C_104] :
      ( r2_hidden('#skF_4',a_2_0_yellow_6('#skF_2',C_104))
      | ~ v3_pre_topc('#skF_4','#skF_2')
      | ~ r2_hidden(C_104,'#skF_4')
      | ~ m1_subset_1(C_104,u1_struct_0('#skF_2'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_42,c_462])).

tff(c_480,plain,(
    ! [C_104] :
      ( r2_hidden('#skF_4',a_2_0_yellow_6('#skF_2',C_104))
      | ~ r2_hidden(C_104,'#skF_4')
      | ~ m1_subset_1(C_104,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_103,c_474])).

tff(c_482,plain,(
    ! [C_105] :
      ( r2_hidden('#skF_4',a_2_0_yellow_6('#skF_2',C_105))
      | ~ r2_hidden(C_105,'#skF_4')
      | ~ m1_subset_1(C_105,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_480])).

tff(c_20,plain,(
    ! [A_7] : l1_orders_2(k2_yellow_1(A_7)) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_18,plain,(
    ! [A_7] : v1_orders_2(k2_yellow_1(A_7)) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_2,plain,(
    ! [A_1] :
      ( g1_orders_2(u1_struct_0(A_1),u1_orders_2(A_1)) = A_1
      | ~ v1_orders_2(A_1)
      | ~ l1_orders_2(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_36,plain,(
    ! [A_20] : k1_yellow_1(A_20) = k1_wellord2(A_20) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_16,plain,(
    ! [A_6] : m1_subset_1(k1_yellow_1(A_6),k1_zfmisc_1(k2_zfmisc_1(A_6,A_6))) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_63,plain,(
    ! [A_6] : m1_subset_1(k1_wellord2(A_6),k1_zfmisc_1(k2_zfmisc_1(A_6,A_6))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_16])).

tff(c_6,plain,(
    ! [A_5] : g1_orders_2(A_5,k1_yellow_1(A_5)) = k2_yellow_1(A_5) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_68,plain,(
    ! [A_5] : g1_orders_2(A_5,k1_wellord2(A_5)) = k2_yellow_1(A_5) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_6])).

tff(c_132,plain,(
    ! [C_46,A_47,D_48,B_49] :
      ( C_46 = A_47
      | g1_orders_2(C_46,D_48) != g1_orders_2(A_47,B_49)
      | ~ m1_subset_1(B_49,k1_zfmisc_1(k2_zfmisc_1(A_47,A_47))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_140,plain,(
    ! [C_46,A_5,D_48] :
      ( C_46 = A_5
      | k2_yellow_1(A_5) != g1_orders_2(C_46,D_48)
      | ~ m1_subset_1(k1_wellord2(A_5),k1_zfmisc_1(k2_zfmisc_1(A_5,A_5))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_132])).

tff(c_158,plain,(
    ! [C_54,A_55,D_56] :
      ( C_54 = A_55
      | k2_yellow_1(A_55) != g1_orders_2(C_54,D_56) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_140])).

tff(c_161,plain,(
    ! [A_1,A_55] :
      ( u1_struct_0(A_1) = A_55
      | k2_yellow_1(A_55) != A_1
      | ~ v1_orders_2(A_1)
      | ~ l1_orders_2(A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_158])).

tff(c_199,plain,(
    ! [A_55] :
      ( u1_struct_0(k2_yellow_1(A_55)) = A_55
      | ~ v1_orders_2(k2_yellow_1(A_55))
      | ~ l1_orders_2(k2_yellow_1(A_55)) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_161])).

tff(c_201,plain,(
    ! [A_55] : u1_struct_0(k2_yellow_1(A_55)) = A_55 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_199])).

tff(c_177,plain,(
    ! [A_62,B_63] :
      ( k7_lattice3(k2_yellow_1(a_2_0_yellow_6(A_62,B_63))) = k9_yellow_6(A_62,B_63)
      | ~ m1_subset_1(B_63,u1_struct_0(A_62))
      | ~ l1_pre_topc(A_62)
      | ~ v2_pre_topc(A_62)
      | v2_struct_0(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_38,plain,(
    ! [A_21] :
      ( u1_struct_0(k7_lattice3(A_21)) = u1_struct_0(A_21)
      | ~ l1_orders_2(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_183,plain,(
    ! [A_62,B_63] :
      ( u1_struct_0(k2_yellow_1(a_2_0_yellow_6(A_62,B_63))) = u1_struct_0(k9_yellow_6(A_62,B_63))
      | ~ l1_orders_2(k2_yellow_1(a_2_0_yellow_6(A_62,B_63)))
      | ~ m1_subset_1(B_63,u1_struct_0(A_62))
      | ~ l1_pre_topc(A_62)
      | ~ v2_pre_topc(A_62)
      | v2_struct_0(A_62) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_177,c_38])).

tff(c_189,plain,(
    ! [A_62,B_63] :
      ( u1_struct_0(k2_yellow_1(a_2_0_yellow_6(A_62,B_63))) = u1_struct_0(k9_yellow_6(A_62,B_63))
      | ~ m1_subset_1(B_63,u1_struct_0(A_62))
      | ~ l1_pre_topc(A_62)
      | ~ v2_pre_topc(A_62)
      | v2_struct_0(A_62) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_183])).

tff(c_390,plain,(
    ! [A_99,B_100] :
      ( u1_struct_0(k9_yellow_6(A_99,B_100)) = a_2_0_yellow_6(A_99,B_100)
      | ~ m1_subset_1(B_100,u1_struct_0(A_99))
      | ~ l1_pre_topc(A_99)
      | ~ v2_pre_topc(A_99)
      | v2_struct_0(A_99) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_201,c_189])).

tff(c_402,plain,
    ( u1_struct_0(k9_yellow_6('#skF_2','#skF_3')) = a_2_0_yellow_6('#skF_2','#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_390])).

tff(c_409,plain,
    ( u1_struct_0(k9_yellow_6('#skF_2','#skF_3')) = a_2_0_yellow_6('#skF_2','#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_402])).

tff(c_410,plain,(
    u1_struct_0(k9_yellow_6('#skF_2','#skF_3')) = a_2_0_yellow_6('#skF_2','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_409])).

tff(c_52,plain,
    ( ~ v3_pre_topc('#skF_4','#skF_2')
    | ~ r2_hidden('#skF_3','#skF_4')
    | ~ r2_hidden('#skF_4',u1_struct_0(k9_yellow_6('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_106,plain,(
    ~ r2_hidden('#skF_4',u1_struct_0(k9_yellow_6('#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_103,c_52])).

tff(c_411,plain,(
    ~ r2_hidden('#skF_4',a_2_0_yellow_6('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_410,c_106])).

tff(c_485,plain,
    ( ~ r2_hidden('#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_482,c_411])).

tff(c_494,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_104,c_485])).

tff(c_496,plain,(
    ~ r2_hidden('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_524,plain,(
    ! [C_113,A_114,D_115,B_116] :
      ( C_113 = A_114
      | g1_orders_2(C_113,D_115) != g1_orders_2(A_114,B_116)
      | ~ m1_subset_1(B_116,k1_zfmisc_1(k2_zfmisc_1(A_114,A_114))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_532,plain,(
    ! [C_113,A_5,D_115] :
      ( C_113 = A_5
      | k2_yellow_1(A_5) != g1_orders_2(C_113,D_115)
      | ~ m1_subset_1(k1_wellord2(A_5),k1_zfmisc_1(k2_zfmisc_1(A_5,A_5))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_524])).

tff(c_550,plain,(
    ! [C_121,A_122,D_123] :
      ( C_121 = A_122
      | k2_yellow_1(A_122) != g1_orders_2(C_121,D_123) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_532])).

tff(c_553,plain,(
    ! [A_1,A_122] :
      ( u1_struct_0(A_1) = A_122
      | k2_yellow_1(A_122) != A_1
      | ~ v1_orders_2(A_1)
      | ~ l1_orders_2(A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_550])).

tff(c_591,plain,(
    ! [A_122] :
      ( u1_struct_0(k2_yellow_1(A_122)) = A_122
      | ~ v1_orders_2(k2_yellow_1(A_122))
      | ~ l1_orders_2(k2_yellow_1(A_122)) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_553])).

tff(c_593,plain,(
    ! [A_122] : u1_struct_0(k2_yellow_1(A_122)) = A_122 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_591])).

tff(c_569,plain,(
    ! [A_129,B_130] :
      ( k7_lattice3(k2_yellow_1(a_2_0_yellow_6(A_129,B_130))) = k9_yellow_6(A_129,B_130)
      | ~ m1_subset_1(B_130,u1_struct_0(A_129))
      | ~ l1_pre_topc(A_129)
      | ~ v2_pre_topc(A_129)
      | v2_struct_0(A_129) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_575,plain,(
    ! [A_129,B_130] :
      ( u1_struct_0(k2_yellow_1(a_2_0_yellow_6(A_129,B_130))) = u1_struct_0(k9_yellow_6(A_129,B_130))
      | ~ l1_orders_2(k2_yellow_1(a_2_0_yellow_6(A_129,B_130)))
      | ~ m1_subset_1(B_130,u1_struct_0(A_129))
      | ~ l1_pre_topc(A_129)
      | ~ v2_pre_topc(A_129)
      | v2_struct_0(A_129) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_569,c_38])).

tff(c_581,plain,(
    ! [A_129,B_130] :
      ( u1_struct_0(k2_yellow_1(a_2_0_yellow_6(A_129,B_130))) = u1_struct_0(k9_yellow_6(A_129,B_130))
      | ~ m1_subset_1(B_130,u1_struct_0(A_129))
      | ~ l1_pre_topc(A_129)
      | ~ v2_pre_topc(A_129)
      | v2_struct_0(A_129) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_575])).

tff(c_782,plain,(
    ! [A_166,B_167] :
      ( u1_struct_0(k9_yellow_6(A_166,B_167)) = a_2_0_yellow_6(A_166,B_167)
      | ~ m1_subset_1(B_167,u1_struct_0(A_166))
      | ~ l1_pre_topc(A_166)
      | ~ v2_pre_topc(A_166)
      | v2_struct_0(A_166) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_593,c_581])).

tff(c_794,plain,
    ( u1_struct_0(k9_yellow_6('#skF_2','#skF_3')) = a_2_0_yellow_6('#skF_2','#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_782])).

tff(c_801,plain,
    ( u1_struct_0(k9_yellow_6('#skF_2','#skF_3')) = a_2_0_yellow_6('#skF_2','#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_794])).

tff(c_802,plain,(
    u1_struct_0(k9_yellow_6('#skF_2','#skF_3')) = a_2_0_yellow_6('#skF_2','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_801])).

tff(c_495,plain,(
    r2_hidden('#skF_4',u1_struct_0(k9_yellow_6('#skF_2','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_803,plain,(
    r2_hidden('#skF_4',a_2_0_yellow_6('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_802,c_495])).

tff(c_28,plain,(
    ! [A_8,B_9,C_10] :
      ( '#skF_1'(A_8,B_9,C_10) = A_8
      | ~ r2_hidden(A_8,a_2_0_yellow_6(B_9,C_10))
      | ~ m1_subset_1(C_10,u1_struct_0(B_9))
      | ~ l1_pre_topc(B_9)
      | ~ v2_pre_topc(B_9)
      | v2_struct_0(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_825,plain,
    ( '#skF_1'('#skF_4','#skF_2','#skF_3') = '#skF_4'
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_803,c_28])).

tff(c_832,plain,
    ( '#skF_1'('#skF_4','#skF_2','#skF_3') = '#skF_4'
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_825])).

tff(c_833,plain,(
    '#skF_1'('#skF_4','#skF_2','#skF_3') = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_832])).

tff(c_26,plain,(
    ! [C_10,A_8,B_9] :
      ( r2_hidden(C_10,'#skF_1'(A_8,B_9,C_10))
      | ~ r2_hidden(A_8,a_2_0_yellow_6(B_9,C_10))
      | ~ m1_subset_1(C_10,u1_struct_0(B_9))
      | ~ l1_pre_topc(B_9)
      | ~ v2_pre_topc(B_9)
      | v2_struct_0(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_822,plain,
    ( r2_hidden('#skF_3','#skF_1'('#skF_4','#skF_2','#skF_3'))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_803,c_26])).

tff(c_828,plain,
    ( r2_hidden('#skF_3','#skF_1'('#skF_4','#skF_2','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_822])).

tff(c_829,plain,(
    r2_hidden('#skF_3','#skF_1'('#skF_4','#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_828])).

tff(c_868,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_833,c_829])).

tff(c_869,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_496,c_868])).

tff(c_871,plain,(
    ~ v3_pre_topc('#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_900,plain,(
    ! [C_178,A_179,D_180,B_181] :
      ( C_178 = A_179
      | g1_orders_2(C_178,D_180) != g1_orders_2(A_179,B_181)
      | ~ m1_subset_1(B_181,k1_zfmisc_1(k2_zfmisc_1(A_179,A_179))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_908,plain,(
    ! [C_178,A_5,D_180] :
      ( C_178 = A_5
      | k2_yellow_1(A_5) != g1_orders_2(C_178,D_180)
      | ~ m1_subset_1(k1_wellord2(A_5),k1_zfmisc_1(k2_zfmisc_1(A_5,A_5))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_900])).

tff(c_911,plain,(
    ! [C_182,A_183,D_184] :
      ( C_182 = A_183
      | k2_yellow_1(A_183) != g1_orders_2(C_182,D_184) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_908])).

tff(c_914,plain,(
    ! [A_1,A_183] :
      ( u1_struct_0(A_1) = A_183
      | k2_yellow_1(A_183) != A_1
      | ~ v1_orders_2(A_1)
      | ~ l1_orders_2(A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_911])).

tff(c_926,plain,(
    ! [A_183] :
      ( u1_struct_0(k2_yellow_1(A_183)) = A_183
      | ~ v1_orders_2(k2_yellow_1(A_183))
      | ~ l1_orders_2(k2_yellow_1(A_183)) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_914])).

tff(c_928,plain,(
    ! [A_183] : u1_struct_0(k2_yellow_1(A_183)) = A_183 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_926])).

tff(c_998,plain,(
    ! [A_202,B_203] :
      ( k7_lattice3(k2_yellow_1(a_2_0_yellow_6(A_202,B_203))) = k9_yellow_6(A_202,B_203)
      | ~ m1_subset_1(B_203,u1_struct_0(A_202))
      | ~ l1_pre_topc(A_202)
      | ~ v2_pre_topc(A_202)
      | v2_struct_0(A_202) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_1004,plain,(
    ! [A_202,B_203] :
      ( u1_struct_0(k2_yellow_1(a_2_0_yellow_6(A_202,B_203))) = u1_struct_0(k9_yellow_6(A_202,B_203))
      | ~ l1_orders_2(k2_yellow_1(a_2_0_yellow_6(A_202,B_203)))
      | ~ m1_subset_1(B_203,u1_struct_0(A_202))
      | ~ l1_pre_topc(A_202)
      | ~ v2_pre_topc(A_202)
      | v2_struct_0(A_202) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_998,c_38])).

tff(c_1110,plain,(
    ! [A_222,B_223] :
      ( u1_struct_0(k9_yellow_6(A_222,B_223)) = a_2_0_yellow_6(A_222,B_223)
      | ~ m1_subset_1(B_223,u1_struct_0(A_222))
      | ~ l1_pre_topc(A_222)
      | ~ v2_pre_topc(A_222)
      | v2_struct_0(A_222) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_928,c_1004])).

tff(c_1122,plain,
    ( u1_struct_0(k9_yellow_6('#skF_2','#skF_3')) = a_2_0_yellow_6('#skF_2','#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_1110])).

tff(c_1129,plain,
    ( u1_struct_0(k9_yellow_6('#skF_2','#skF_3')) = a_2_0_yellow_6('#skF_2','#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_1122])).

tff(c_1130,plain,(
    u1_struct_0(k9_yellow_6('#skF_2','#skF_3')) = a_2_0_yellow_6('#skF_2','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_1129])).

tff(c_870,plain,(
    r2_hidden('#skF_4',u1_struct_0(k9_yellow_6('#skF_2','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_1131,plain,(
    r2_hidden('#skF_4',a_2_0_yellow_6('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1130,c_870])).

tff(c_1173,plain,
    ( '#skF_1'('#skF_4','#skF_2','#skF_3') = '#skF_4'
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_1131,c_28])).

tff(c_1176,plain,
    ( '#skF_1'('#skF_4','#skF_2','#skF_3') = '#skF_4'
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_1173])).

tff(c_1177,plain,(
    '#skF_1'('#skF_4','#skF_2','#skF_3') = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_1176])).

tff(c_24,plain,(
    ! [A_8,B_9,C_10] :
      ( v3_pre_topc('#skF_1'(A_8,B_9,C_10),B_9)
      | ~ r2_hidden(A_8,a_2_0_yellow_6(B_9,C_10))
      | ~ m1_subset_1(C_10,u1_struct_0(B_9))
      | ~ l1_pre_topc(B_9)
      | ~ v2_pre_topc(B_9)
      | v2_struct_0(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_1181,plain,
    ( v3_pre_topc('#skF_4','#skF_2')
    | ~ r2_hidden('#skF_4',a_2_0_yellow_6('#skF_2','#skF_3'))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1177,c_24])).

tff(c_1185,plain,
    ( v3_pre_topc('#skF_4','#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_1131,c_1181])).

tff(c_1187,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_871,c_1185])).

%------------------------------------------------------------------------------
