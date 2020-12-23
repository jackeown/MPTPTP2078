%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:08 EST 2020

% Result     : Theorem 2.52s
% Output     : CNFRefutation 2.52s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 412 expanded)
%              Number of leaves         :   41 ( 160 expanded)
%              Depth                    :   17
%              Number of atoms          :  252 (2190 expanded)
%              Number of equality atoms :    2 (  22 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r1_waybel_0 > r1_orders_2 > v6_waybel_0 > v1_yellow_6 > r2_hidden > m1_subset_1 > l1_waybel_0 > v7_waybel_0 > v4_orders_2 > v2_struct_0 > v1_xboole_0 > v1_funct_1 > l1_struct_0 > l1_orders_2 > k3_funct_2 > k2_waybel_0 > k2_relset_1 > u1_waybel_0 > k4_yellow_6 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k4_yellow_6,type,(
    k4_yellow_6: ( $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(v6_waybel_0,type,(
    v6_waybel_0: ( $i * $i ) > $o )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff(k2_waybel_0,type,(
    k2_waybel_0: ( $i * $i * $i ) > $i )).

tff(v7_waybel_0,type,(
    v7_waybel_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(r1_waybel_0,type,(
    r1_waybel_0: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(v1_yellow_6,type,(
    v1_yellow_6: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff(u1_waybel_0,type,(
    u1_waybel_0: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(l1_waybel_0,type,(
    l1_waybel_0: ( $i * $i ) > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k3_funct_2,type,(
    k3_funct_2: ( $i * $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_155,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & l1_struct_0(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & l1_waybel_0(B,A) )
           => r1_waybel_0(A,B,k2_relset_1(u1_struct_0(B),u1_struct_0(A),u1_waybel_0(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_waybel_9)).

tff(f_103,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ! [B] :
          ( l1_waybel_0(B,A)
         => l1_orders_2(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_waybel_0)).

tff(f_56,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_122,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A)
        & l1_waybel_0(B,A) )
     => m1_subset_1(k4_yellow_6(A,B),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_yellow_6)).

tff(f_113,axiom,(
    ! [A,B] :
      ( ( l1_struct_0(A)
        & l1_waybel_0(B,A) )
     => ( v1_funct_1(u1_waybel_0(A,B))
        & v1_funct_2(u1_waybel_0(A,B),u1_struct_0(B),u1_struct_0(A))
        & m1_subset_1(u1_waybel_0(A,B),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B),u1_struct_0(A)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_waybel_0)).

tff(f_80,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & l1_waybel_0(B,A) )
         => ! [C] :
              ( r1_waybel_0(A,B,C)
            <=> ? [D] :
                  ( m1_subset_1(D,u1_struct_0(B))
                  & ! [E] :
                      ( m1_subset_1(E,u1_struct_0(B))
                     => ( r1_orders_2(B,D,E)
                       => r2_hidden(k2_waybel_0(A,B,E),C) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_waybel_0)).

tff(f_96,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & l1_waybel_0(B,A) )
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(B))
             => k2_waybel_0(A,B,C) = k3_funct_2(u1_struct_0(B),u1_struct_0(A),u1_waybel_0(A,B),C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_waybel_0)).

tff(f_44,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ~ v1_xboole_0(B)
         => ! [C] :
              ( m1_subset_1(C,A)
             => ! [D] :
                  ( ( v1_funct_1(D)
                    & v1_funct_2(D,A,B)
                    & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
                 => r2_hidden(k3_funct_2(A,B,D,C),k2_relset_1(A,B,D)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t189_funct_2)).

tff(f_52,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_141,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ? [B] :
          ( l1_waybel_0(B,A)
          & ~ v2_struct_0(B)
          & v4_orders_2(B)
          & v6_waybel_0(B,A)
          & v7_waybel_0(B)
          & v1_yellow_6(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc7_yellow_6)).

tff(c_46,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_48,plain,(
    l1_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_44,plain,(
    l1_waybel_0('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_56,plain,(
    ! [B_93,A_94] :
      ( l1_orders_2(B_93)
      | ~ l1_waybel_0(B_93,A_94)
      | ~ l1_struct_0(A_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_59,plain,
    ( l1_orders_2('#skF_5')
    | ~ l1_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_56])).

tff(c_62,plain,(
    l1_orders_2('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_59])).

tff(c_6,plain,(
    ! [A_17] :
      ( l1_struct_0(A_17)
      | ~ l1_orders_2(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_50,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_28,plain,(
    ! [A_83,B_84] :
      ( m1_subset_1(k4_yellow_6(A_83,B_84),u1_struct_0(A_83))
      | ~ l1_waybel_0(B_84,A_83)
      | ~ l1_struct_0(A_83)
      | v2_struct_0(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_22,plain,(
    ! [A_81,B_82] :
      ( m1_subset_1(u1_waybel_0(A_81,B_82),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_82),u1_struct_0(A_81))))
      | ~ l1_waybel_0(B_82,A_81)
      | ~ l1_struct_0(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_16,plain,(
    ! [A_18,B_46,C_60,D_67] :
      ( m1_subset_1('#skF_1'(A_18,B_46,C_60,D_67),u1_struct_0(B_46))
      | r1_waybel_0(A_18,B_46,C_60)
      | ~ m1_subset_1(D_67,u1_struct_0(B_46))
      | ~ l1_waybel_0(B_46,A_18)
      | v2_struct_0(B_46)
      | ~ l1_struct_0(A_18)
      | v2_struct_0(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_18,plain,(
    ! [B_75,A_71,C_77] :
      ( k3_funct_2(u1_struct_0(B_75),u1_struct_0(A_71),u1_waybel_0(A_71,B_75),C_77) = k2_waybel_0(A_71,B_75,C_77)
      | ~ m1_subset_1(C_77,u1_struct_0(B_75))
      | ~ l1_waybel_0(B_75,A_71)
      | v2_struct_0(B_75)
      | ~ l1_struct_0(A_71)
      | v2_struct_0(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_88,plain,(
    ! [A_125,B_126,D_127,C_128] :
      ( r2_hidden(k3_funct_2(A_125,B_126,D_127,C_128),k2_relset_1(A_125,B_126,D_127))
      | ~ m1_subset_1(D_127,k1_zfmisc_1(k2_zfmisc_1(A_125,B_126)))
      | ~ v1_funct_2(D_127,A_125,B_126)
      | ~ v1_funct_1(D_127)
      | ~ m1_subset_1(C_128,A_125)
      | v1_xboole_0(B_126)
      | v1_xboole_0(A_125) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_104,plain,(
    ! [A_138,B_139,C_140] :
      ( r2_hidden(k2_waybel_0(A_138,B_139,C_140),k2_relset_1(u1_struct_0(B_139),u1_struct_0(A_138),u1_waybel_0(A_138,B_139)))
      | ~ m1_subset_1(u1_waybel_0(A_138,B_139),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_139),u1_struct_0(A_138))))
      | ~ v1_funct_2(u1_waybel_0(A_138,B_139),u1_struct_0(B_139),u1_struct_0(A_138))
      | ~ v1_funct_1(u1_waybel_0(A_138,B_139))
      | ~ m1_subset_1(C_140,u1_struct_0(B_139))
      | v1_xboole_0(u1_struct_0(A_138))
      | v1_xboole_0(u1_struct_0(B_139))
      | ~ m1_subset_1(C_140,u1_struct_0(B_139))
      | ~ l1_waybel_0(B_139,A_138)
      | v2_struct_0(B_139)
      | ~ l1_struct_0(A_138)
      | v2_struct_0(A_138) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_88])).

tff(c_12,plain,(
    ! [A_18,B_46,C_60,D_67] :
      ( ~ r2_hidden(k2_waybel_0(A_18,B_46,'#skF_1'(A_18,B_46,C_60,D_67)),C_60)
      | r1_waybel_0(A_18,B_46,C_60)
      | ~ m1_subset_1(D_67,u1_struct_0(B_46))
      | ~ l1_waybel_0(B_46,A_18)
      | v2_struct_0(B_46)
      | ~ l1_struct_0(A_18)
      | v2_struct_0(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_110,plain,(
    ! [A_141,B_142,D_143] :
      ( r1_waybel_0(A_141,B_142,k2_relset_1(u1_struct_0(B_142),u1_struct_0(A_141),u1_waybel_0(A_141,B_142)))
      | ~ m1_subset_1(D_143,u1_struct_0(B_142))
      | ~ m1_subset_1(u1_waybel_0(A_141,B_142),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_142),u1_struct_0(A_141))))
      | ~ v1_funct_2(u1_waybel_0(A_141,B_142),u1_struct_0(B_142),u1_struct_0(A_141))
      | ~ v1_funct_1(u1_waybel_0(A_141,B_142))
      | v1_xboole_0(u1_struct_0(A_141))
      | v1_xboole_0(u1_struct_0(B_142))
      | ~ m1_subset_1('#skF_1'(A_141,B_142,k2_relset_1(u1_struct_0(B_142),u1_struct_0(A_141),u1_waybel_0(A_141,B_142)),D_143),u1_struct_0(B_142))
      | ~ l1_waybel_0(B_142,A_141)
      | v2_struct_0(B_142)
      | ~ l1_struct_0(A_141)
      | v2_struct_0(A_141) ) ),
    inference(resolution,[status(thm)],[c_104,c_12])).

tff(c_116,plain,(
    ! [A_144,B_145,D_146] :
      ( ~ m1_subset_1(u1_waybel_0(A_144,B_145),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_145),u1_struct_0(A_144))))
      | ~ v1_funct_2(u1_waybel_0(A_144,B_145),u1_struct_0(B_145),u1_struct_0(A_144))
      | ~ v1_funct_1(u1_waybel_0(A_144,B_145))
      | v1_xboole_0(u1_struct_0(A_144))
      | v1_xboole_0(u1_struct_0(B_145))
      | r1_waybel_0(A_144,B_145,k2_relset_1(u1_struct_0(B_145),u1_struct_0(A_144),u1_waybel_0(A_144,B_145)))
      | ~ m1_subset_1(D_146,u1_struct_0(B_145))
      | ~ l1_waybel_0(B_145,A_144)
      | v2_struct_0(B_145)
      | ~ l1_struct_0(A_144)
      | v2_struct_0(A_144) ) ),
    inference(resolution,[status(thm)],[c_16,c_110])).

tff(c_120,plain,(
    ! [A_147,B_148,D_149] :
      ( ~ v1_funct_2(u1_waybel_0(A_147,B_148),u1_struct_0(B_148),u1_struct_0(A_147))
      | ~ v1_funct_1(u1_waybel_0(A_147,B_148))
      | v1_xboole_0(u1_struct_0(A_147))
      | v1_xboole_0(u1_struct_0(B_148))
      | r1_waybel_0(A_147,B_148,k2_relset_1(u1_struct_0(B_148),u1_struct_0(A_147),u1_waybel_0(A_147,B_148)))
      | ~ m1_subset_1(D_149,u1_struct_0(B_148))
      | v2_struct_0(B_148)
      | v2_struct_0(A_147)
      | ~ l1_waybel_0(B_148,A_147)
      | ~ l1_struct_0(A_147) ) ),
    inference(resolution,[status(thm)],[c_22,c_116])).

tff(c_130,plain,(
    ! [A_150,A_151,B_152] :
      ( ~ v1_funct_2(u1_waybel_0(A_150,A_151),u1_struct_0(A_151),u1_struct_0(A_150))
      | ~ v1_funct_1(u1_waybel_0(A_150,A_151))
      | v1_xboole_0(u1_struct_0(A_150))
      | v1_xboole_0(u1_struct_0(A_151))
      | r1_waybel_0(A_150,A_151,k2_relset_1(u1_struct_0(A_151),u1_struct_0(A_150),u1_waybel_0(A_150,A_151)))
      | v2_struct_0(A_150)
      | ~ l1_waybel_0(A_151,A_150)
      | ~ l1_struct_0(A_150)
      | ~ l1_waybel_0(B_152,A_151)
      | ~ l1_struct_0(A_151)
      | v2_struct_0(A_151) ) ),
    inference(resolution,[status(thm)],[c_28,c_120])).

tff(c_134,plain,(
    ! [A_150] :
      ( ~ v1_funct_2(u1_waybel_0(A_150,'#skF_4'),u1_struct_0('#skF_4'),u1_struct_0(A_150))
      | ~ v1_funct_1(u1_waybel_0(A_150,'#skF_4'))
      | v1_xboole_0(u1_struct_0(A_150))
      | v1_xboole_0(u1_struct_0('#skF_4'))
      | r1_waybel_0(A_150,'#skF_4',k2_relset_1(u1_struct_0('#skF_4'),u1_struct_0(A_150),u1_waybel_0(A_150,'#skF_4')))
      | v2_struct_0(A_150)
      | ~ l1_waybel_0('#skF_4',A_150)
      | ~ l1_struct_0(A_150)
      | ~ l1_struct_0('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_44,c_130])).

tff(c_138,plain,(
    ! [A_150] :
      ( ~ v1_funct_2(u1_waybel_0(A_150,'#skF_4'),u1_struct_0('#skF_4'),u1_struct_0(A_150))
      | ~ v1_funct_1(u1_waybel_0(A_150,'#skF_4'))
      | v1_xboole_0(u1_struct_0(A_150))
      | v1_xboole_0(u1_struct_0('#skF_4'))
      | r1_waybel_0(A_150,'#skF_4',k2_relset_1(u1_struct_0('#skF_4'),u1_struct_0(A_150),u1_waybel_0(A_150,'#skF_4')))
      | v2_struct_0(A_150)
      | ~ l1_waybel_0('#skF_4',A_150)
      | ~ l1_struct_0(A_150)
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_134])).

tff(c_139,plain,(
    ! [A_150] :
      ( ~ v1_funct_2(u1_waybel_0(A_150,'#skF_4'),u1_struct_0('#skF_4'),u1_struct_0(A_150))
      | ~ v1_funct_1(u1_waybel_0(A_150,'#skF_4'))
      | v1_xboole_0(u1_struct_0(A_150))
      | v1_xboole_0(u1_struct_0('#skF_4'))
      | r1_waybel_0(A_150,'#skF_4',k2_relset_1(u1_struct_0('#skF_4'),u1_struct_0(A_150),u1_waybel_0(A_150,'#skF_4')))
      | v2_struct_0(A_150)
      | ~ l1_waybel_0('#skF_4',A_150)
      | ~ l1_struct_0(A_150) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_138])).

tff(c_140,plain,(
    v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_139])).

tff(c_4,plain,(
    ! [A_16] :
      ( ~ v1_xboole_0(u1_struct_0(A_16))
      | ~ l1_struct_0(A_16)
      | v2_struct_0(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_143,plain,
    ( ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_140,c_4])).

tff(c_146,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_143])).

tff(c_148,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_146])).

tff(c_150,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_139])).

tff(c_40,plain,(
    ! [A_85] :
      ( l1_waybel_0('#skF_3'(A_85),A_85)
      | ~ l1_struct_0(A_85)
      | v2_struct_0(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_157,plain,(
    ! [A_158,A_159] :
      ( ~ v1_funct_2(u1_waybel_0(A_158,A_159),u1_struct_0(A_159),u1_struct_0(A_158))
      | ~ v1_funct_1(u1_waybel_0(A_158,A_159))
      | v1_xboole_0(u1_struct_0(A_158))
      | v1_xboole_0(u1_struct_0(A_159))
      | r1_waybel_0(A_158,A_159,k2_relset_1(u1_struct_0(A_159),u1_struct_0(A_158),u1_waybel_0(A_158,A_159)))
      | v2_struct_0(A_158)
      | ~ l1_waybel_0(A_159,A_158)
      | ~ l1_struct_0(A_158)
      | ~ l1_struct_0(A_159)
      | v2_struct_0(A_159) ) ),
    inference(resolution,[status(thm)],[c_40,c_130])).

tff(c_42,plain,(
    ~ r1_waybel_0('#skF_4','#skF_5',k2_relset_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),u1_waybel_0('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_162,plain,
    ( ~ v1_funct_2(u1_waybel_0('#skF_4','#skF_5'),u1_struct_0('#skF_5'),u1_struct_0('#skF_4'))
    | ~ v1_funct_1(u1_waybel_0('#skF_4','#skF_5'))
    | v1_xboole_0(u1_struct_0('#skF_4'))
    | v1_xboole_0(u1_struct_0('#skF_5'))
    | v2_struct_0('#skF_4')
    | ~ l1_waybel_0('#skF_5','#skF_4')
    | ~ l1_struct_0('#skF_4')
    | ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_157,c_42])).

tff(c_166,plain,
    ( ~ v1_funct_2(u1_waybel_0('#skF_4','#skF_5'),u1_struct_0('#skF_5'),u1_struct_0('#skF_4'))
    | ~ v1_funct_1(u1_waybel_0('#skF_4','#skF_5'))
    | v1_xboole_0(u1_struct_0('#skF_4'))
    | v1_xboole_0(u1_struct_0('#skF_5'))
    | v2_struct_0('#skF_4')
    | ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_44,c_162])).

tff(c_167,plain,
    ( ~ v1_funct_2(u1_waybel_0('#skF_4','#skF_5'),u1_struct_0('#skF_5'),u1_struct_0('#skF_4'))
    | ~ v1_funct_1(u1_waybel_0('#skF_4','#skF_5'))
    | v1_xboole_0(u1_struct_0('#skF_5'))
    | ~ l1_struct_0('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_50,c_150,c_166])).

tff(c_168,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_167])).

tff(c_171,plain,(
    ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_6,c_168])).

tff(c_175,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_171])).

tff(c_177,plain,(
    l1_struct_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_167])).

tff(c_26,plain,(
    ! [A_81,B_82] :
      ( v1_funct_1(u1_waybel_0(A_81,B_82))
      | ~ l1_waybel_0(B_82,A_81)
      | ~ l1_struct_0(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_24,plain,(
    ! [A_81,B_82] :
      ( v1_funct_2(u1_waybel_0(A_81,B_82),u1_struct_0(B_82),u1_struct_0(A_81))
      | ~ l1_waybel_0(B_82,A_81)
      | ~ l1_struct_0(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_176,plain,
    ( ~ v1_funct_1(u1_waybel_0('#skF_4','#skF_5'))
    | ~ v1_funct_2(u1_waybel_0('#skF_4','#skF_5'),u1_struct_0('#skF_5'),u1_struct_0('#skF_4'))
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_167])).

tff(c_178,plain,(
    ~ v1_funct_2(u1_waybel_0('#skF_4','#skF_5'),u1_struct_0('#skF_5'),u1_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_176])).

tff(c_181,plain,
    ( ~ l1_waybel_0('#skF_5','#skF_4')
    | ~ l1_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_24,c_178])).

tff(c_185,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_44,c_181])).

tff(c_186,plain,
    ( ~ v1_funct_1(u1_waybel_0('#skF_4','#skF_5'))
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_176])).

tff(c_188,plain,(
    ~ v1_funct_1(u1_waybel_0('#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_186])).

tff(c_191,plain,
    ( ~ l1_waybel_0('#skF_5','#skF_4')
    | ~ l1_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_26,c_188])).

tff(c_195,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_44,c_191])).

tff(c_196,plain,(
    v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_186])).

tff(c_200,plain,
    ( ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_196,c_4])).

tff(c_203,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_177,c_200])).

tff(c_205,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_203])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:48:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.52/1.33  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.52/1.34  
% 2.52/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.52/1.34  %$ v1_funct_2 > r1_waybel_0 > r1_orders_2 > v6_waybel_0 > v1_yellow_6 > r2_hidden > m1_subset_1 > l1_waybel_0 > v7_waybel_0 > v4_orders_2 > v2_struct_0 > v1_xboole_0 > v1_funct_1 > l1_struct_0 > l1_orders_2 > k3_funct_2 > k2_waybel_0 > k2_relset_1 > u1_waybel_0 > k4_yellow_6 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 2.52/1.34  
% 2.52/1.34  %Foreground sorts:
% 2.52/1.34  
% 2.52/1.34  
% 2.52/1.34  %Background operators:
% 2.52/1.34  
% 2.52/1.34  
% 2.52/1.34  %Foreground operators:
% 2.52/1.34  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.52/1.34  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.52/1.34  tff(k4_yellow_6, type, k4_yellow_6: ($i * $i) > $i).
% 2.52/1.34  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.52/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.52/1.34  tff(v6_waybel_0, type, v6_waybel_0: ($i * $i) > $o).
% 2.52/1.34  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.52/1.34  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 2.52/1.34  tff(k2_waybel_0, type, k2_waybel_0: ($i * $i * $i) > $i).
% 2.52/1.34  tff(v7_waybel_0, type, v7_waybel_0: $i > $o).
% 2.52/1.34  tff('#skF_5', type, '#skF_5': $i).
% 2.52/1.34  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.52/1.34  tff(r1_waybel_0, type, r1_waybel_0: ($i * $i * $i) > $o).
% 2.52/1.34  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.52/1.34  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.52/1.34  tff(v1_yellow_6, type, v1_yellow_6: ($i * $i) > $o).
% 2.52/1.34  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.52/1.34  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.52/1.34  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.52/1.34  tff(u1_waybel_0, type, u1_waybel_0: ($i * $i) > $i).
% 2.52/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.52/1.34  tff(l1_waybel_0, type, l1_waybel_0: ($i * $i) > $o).
% 2.52/1.34  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.52/1.34  tff('#skF_4', type, '#skF_4': $i).
% 2.52/1.34  tff('#skF_3', type, '#skF_3': $i > $i).
% 2.52/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.52/1.34  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 2.52/1.34  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.52/1.34  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.52/1.34  tff(k3_funct_2, type, k3_funct_2: ($i * $i * $i * $i) > $i).
% 2.52/1.34  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.52/1.34  
% 2.52/1.36  tff(f_155, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((~v2_struct_0(B) & l1_waybel_0(B, A)) => r1_waybel_0(A, B, k2_relset_1(u1_struct_0(B), u1_struct_0(A), u1_waybel_0(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_waybel_9)).
% 2.52/1.36  tff(f_103, axiom, (![A]: (l1_struct_0(A) => (![B]: (l1_waybel_0(B, A) => l1_orders_2(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_waybel_0)).
% 2.52/1.36  tff(f_56, axiom, (![A]: (l1_orders_2(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 2.52/1.36  tff(f_122, axiom, (![A, B]: (((~v2_struct_0(A) & l1_struct_0(A)) & l1_waybel_0(B, A)) => m1_subset_1(k4_yellow_6(A, B), u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_yellow_6)).
% 2.52/1.36  tff(f_113, axiom, (![A, B]: ((l1_struct_0(A) & l1_waybel_0(B, A)) => ((v1_funct_1(u1_waybel_0(A, B)) & v1_funct_2(u1_waybel_0(A, B), u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(u1_waybel_0(A, B), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_u1_waybel_0)).
% 2.52/1.36  tff(f_80, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((~v2_struct_0(B) & l1_waybel_0(B, A)) => (![C]: (r1_waybel_0(A, B, C) <=> (?[D]: (m1_subset_1(D, u1_struct_0(B)) & (![E]: (m1_subset_1(E, u1_struct_0(B)) => (r1_orders_2(B, D, E) => r2_hidden(k2_waybel_0(A, B, E), C)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d11_waybel_0)).
% 2.52/1.36  tff(f_96, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((~v2_struct_0(B) & l1_waybel_0(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(B)) => (k2_waybel_0(A, B, C) = k3_funct_2(u1_struct_0(B), u1_struct_0(A), u1_waybel_0(A, B), C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_waybel_0)).
% 2.52/1.36  tff(f_44, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, A) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_hidden(k3_funct_2(A, B, D, C), k2_relset_1(A, B, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t189_funct_2)).
% 2.52/1.36  tff(f_52, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 2.52/1.36  tff(f_141, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (?[B]: (((((l1_waybel_0(B, A) & ~v2_struct_0(B)) & v4_orders_2(B)) & v6_waybel_0(B, A)) & v7_waybel_0(B)) & v1_yellow_6(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc7_yellow_6)).
% 2.52/1.36  tff(c_46, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_155])).
% 2.52/1.36  tff(c_48, plain, (l1_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_155])).
% 2.52/1.36  tff(c_44, plain, (l1_waybel_0('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_155])).
% 2.52/1.36  tff(c_56, plain, (![B_93, A_94]: (l1_orders_2(B_93) | ~l1_waybel_0(B_93, A_94) | ~l1_struct_0(A_94))), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.52/1.36  tff(c_59, plain, (l1_orders_2('#skF_5') | ~l1_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_44, c_56])).
% 2.52/1.36  tff(c_62, plain, (l1_orders_2('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_59])).
% 2.52/1.36  tff(c_6, plain, (![A_17]: (l1_struct_0(A_17) | ~l1_orders_2(A_17))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.52/1.36  tff(c_50, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_155])).
% 2.52/1.36  tff(c_28, plain, (![A_83, B_84]: (m1_subset_1(k4_yellow_6(A_83, B_84), u1_struct_0(A_83)) | ~l1_waybel_0(B_84, A_83) | ~l1_struct_0(A_83) | v2_struct_0(A_83))), inference(cnfTransformation, [status(thm)], [f_122])).
% 2.52/1.36  tff(c_22, plain, (![A_81, B_82]: (m1_subset_1(u1_waybel_0(A_81, B_82), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_82), u1_struct_0(A_81)))) | ~l1_waybel_0(B_82, A_81) | ~l1_struct_0(A_81))), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.52/1.36  tff(c_16, plain, (![A_18, B_46, C_60, D_67]: (m1_subset_1('#skF_1'(A_18, B_46, C_60, D_67), u1_struct_0(B_46)) | r1_waybel_0(A_18, B_46, C_60) | ~m1_subset_1(D_67, u1_struct_0(B_46)) | ~l1_waybel_0(B_46, A_18) | v2_struct_0(B_46) | ~l1_struct_0(A_18) | v2_struct_0(A_18))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.52/1.36  tff(c_18, plain, (![B_75, A_71, C_77]: (k3_funct_2(u1_struct_0(B_75), u1_struct_0(A_71), u1_waybel_0(A_71, B_75), C_77)=k2_waybel_0(A_71, B_75, C_77) | ~m1_subset_1(C_77, u1_struct_0(B_75)) | ~l1_waybel_0(B_75, A_71) | v2_struct_0(B_75) | ~l1_struct_0(A_71) | v2_struct_0(A_71))), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.52/1.36  tff(c_88, plain, (![A_125, B_126, D_127, C_128]: (r2_hidden(k3_funct_2(A_125, B_126, D_127, C_128), k2_relset_1(A_125, B_126, D_127)) | ~m1_subset_1(D_127, k1_zfmisc_1(k2_zfmisc_1(A_125, B_126))) | ~v1_funct_2(D_127, A_125, B_126) | ~v1_funct_1(D_127) | ~m1_subset_1(C_128, A_125) | v1_xboole_0(B_126) | v1_xboole_0(A_125))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.52/1.36  tff(c_104, plain, (![A_138, B_139, C_140]: (r2_hidden(k2_waybel_0(A_138, B_139, C_140), k2_relset_1(u1_struct_0(B_139), u1_struct_0(A_138), u1_waybel_0(A_138, B_139))) | ~m1_subset_1(u1_waybel_0(A_138, B_139), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_139), u1_struct_0(A_138)))) | ~v1_funct_2(u1_waybel_0(A_138, B_139), u1_struct_0(B_139), u1_struct_0(A_138)) | ~v1_funct_1(u1_waybel_0(A_138, B_139)) | ~m1_subset_1(C_140, u1_struct_0(B_139)) | v1_xboole_0(u1_struct_0(A_138)) | v1_xboole_0(u1_struct_0(B_139)) | ~m1_subset_1(C_140, u1_struct_0(B_139)) | ~l1_waybel_0(B_139, A_138) | v2_struct_0(B_139) | ~l1_struct_0(A_138) | v2_struct_0(A_138))), inference(superposition, [status(thm), theory('equality')], [c_18, c_88])).
% 2.52/1.36  tff(c_12, plain, (![A_18, B_46, C_60, D_67]: (~r2_hidden(k2_waybel_0(A_18, B_46, '#skF_1'(A_18, B_46, C_60, D_67)), C_60) | r1_waybel_0(A_18, B_46, C_60) | ~m1_subset_1(D_67, u1_struct_0(B_46)) | ~l1_waybel_0(B_46, A_18) | v2_struct_0(B_46) | ~l1_struct_0(A_18) | v2_struct_0(A_18))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.52/1.36  tff(c_110, plain, (![A_141, B_142, D_143]: (r1_waybel_0(A_141, B_142, k2_relset_1(u1_struct_0(B_142), u1_struct_0(A_141), u1_waybel_0(A_141, B_142))) | ~m1_subset_1(D_143, u1_struct_0(B_142)) | ~m1_subset_1(u1_waybel_0(A_141, B_142), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_142), u1_struct_0(A_141)))) | ~v1_funct_2(u1_waybel_0(A_141, B_142), u1_struct_0(B_142), u1_struct_0(A_141)) | ~v1_funct_1(u1_waybel_0(A_141, B_142)) | v1_xboole_0(u1_struct_0(A_141)) | v1_xboole_0(u1_struct_0(B_142)) | ~m1_subset_1('#skF_1'(A_141, B_142, k2_relset_1(u1_struct_0(B_142), u1_struct_0(A_141), u1_waybel_0(A_141, B_142)), D_143), u1_struct_0(B_142)) | ~l1_waybel_0(B_142, A_141) | v2_struct_0(B_142) | ~l1_struct_0(A_141) | v2_struct_0(A_141))), inference(resolution, [status(thm)], [c_104, c_12])).
% 2.52/1.36  tff(c_116, plain, (![A_144, B_145, D_146]: (~m1_subset_1(u1_waybel_0(A_144, B_145), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_145), u1_struct_0(A_144)))) | ~v1_funct_2(u1_waybel_0(A_144, B_145), u1_struct_0(B_145), u1_struct_0(A_144)) | ~v1_funct_1(u1_waybel_0(A_144, B_145)) | v1_xboole_0(u1_struct_0(A_144)) | v1_xboole_0(u1_struct_0(B_145)) | r1_waybel_0(A_144, B_145, k2_relset_1(u1_struct_0(B_145), u1_struct_0(A_144), u1_waybel_0(A_144, B_145))) | ~m1_subset_1(D_146, u1_struct_0(B_145)) | ~l1_waybel_0(B_145, A_144) | v2_struct_0(B_145) | ~l1_struct_0(A_144) | v2_struct_0(A_144))), inference(resolution, [status(thm)], [c_16, c_110])).
% 2.52/1.36  tff(c_120, plain, (![A_147, B_148, D_149]: (~v1_funct_2(u1_waybel_0(A_147, B_148), u1_struct_0(B_148), u1_struct_0(A_147)) | ~v1_funct_1(u1_waybel_0(A_147, B_148)) | v1_xboole_0(u1_struct_0(A_147)) | v1_xboole_0(u1_struct_0(B_148)) | r1_waybel_0(A_147, B_148, k2_relset_1(u1_struct_0(B_148), u1_struct_0(A_147), u1_waybel_0(A_147, B_148))) | ~m1_subset_1(D_149, u1_struct_0(B_148)) | v2_struct_0(B_148) | v2_struct_0(A_147) | ~l1_waybel_0(B_148, A_147) | ~l1_struct_0(A_147))), inference(resolution, [status(thm)], [c_22, c_116])).
% 2.52/1.36  tff(c_130, plain, (![A_150, A_151, B_152]: (~v1_funct_2(u1_waybel_0(A_150, A_151), u1_struct_0(A_151), u1_struct_0(A_150)) | ~v1_funct_1(u1_waybel_0(A_150, A_151)) | v1_xboole_0(u1_struct_0(A_150)) | v1_xboole_0(u1_struct_0(A_151)) | r1_waybel_0(A_150, A_151, k2_relset_1(u1_struct_0(A_151), u1_struct_0(A_150), u1_waybel_0(A_150, A_151))) | v2_struct_0(A_150) | ~l1_waybel_0(A_151, A_150) | ~l1_struct_0(A_150) | ~l1_waybel_0(B_152, A_151) | ~l1_struct_0(A_151) | v2_struct_0(A_151))), inference(resolution, [status(thm)], [c_28, c_120])).
% 2.52/1.36  tff(c_134, plain, (![A_150]: (~v1_funct_2(u1_waybel_0(A_150, '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0(A_150)) | ~v1_funct_1(u1_waybel_0(A_150, '#skF_4')) | v1_xboole_0(u1_struct_0(A_150)) | v1_xboole_0(u1_struct_0('#skF_4')) | r1_waybel_0(A_150, '#skF_4', k2_relset_1(u1_struct_0('#skF_4'), u1_struct_0(A_150), u1_waybel_0(A_150, '#skF_4'))) | v2_struct_0(A_150) | ~l1_waybel_0('#skF_4', A_150) | ~l1_struct_0(A_150) | ~l1_struct_0('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_44, c_130])).
% 2.52/1.36  tff(c_138, plain, (![A_150]: (~v1_funct_2(u1_waybel_0(A_150, '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0(A_150)) | ~v1_funct_1(u1_waybel_0(A_150, '#skF_4')) | v1_xboole_0(u1_struct_0(A_150)) | v1_xboole_0(u1_struct_0('#skF_4')) | r1_waybel_0(A_150, '#skF_4', k2_relset_1(u1_struct_0('#skF_4'), u1_struct_0(A_150), u1_waybel_0(A_150, '#skF_4'))) | v2_struct_0(A_150) | ~l1_waybel_0('#skF_4', A_150) | ~l1_struct_0(A_150) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_134])).
% 2.52/1.36  tff(c_139, plain, (![A_150]: (~v1_funct_2(u1_waybel_0(A_150, '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0(A_150)) | ~v1_funct_1(u1_waybel_0(A_150, '#skF_4')) | v1_xboole_0(u1_struct_0(A_150)) | v1_xboole_0(u1_struct_0('#skF_4')) | r1_waybel_0(A_150, '#skF_4', k2_relset_1(u1_struct_0('#skF_4'), u1_struct_0(A_150), u1_waybel_0(A_150, '#skF_4'))) | v2_struct_0(A_150) | ~l1_waybel_0('#skF_4', A_150) | ~l1_struct_0(A_150))), inference(negUnitSimplification, [status(thm)], [c_50, c_138])).
% 2.52/1.36  tff(c_140, plain, (v1_xboole_0(u1_struct_0('#skF_4'))), inference(splitLeft, [status(thm)], [c_139])).
% 2.52/1.36  tff(c_4, plain, (![A_16]: (~v1_xboole_0(u1_struct_0(A_16)) | ~l1_struct_0(A_16) | v2_struct_0(A_16))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.52/1.36  tff(c_143, plain, (~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_140, c_4])).
% 2.52/1.36  tff(c_146, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_143])).
% 2.52/1.36  tff(c_148, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_146])).
% 2.52/1.36  tff(c_150, plain, (~v1_xboole_0(u1_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_139])).
% 2.52/1.36  tff(c_40, plain, (![A_85]: (l1_waybel_0('#skF_3'(A_85), A_85) | ~l1_struct_0(A_85) | v2_struct_0(A_85))), inference(cnfTransformation, [status(thm)], [f_141])).
% 2.52/1.36  tff(c_157, plain, (![A_158, A_159]: (~v1_funct_2(u1_waybel_0(A_158, A_159), u1_struct_0(A_159), u1_struct_0(A_158)) | ~v1_funct_1(u1_waybel_0(A_158, A_159)) | v1_xboole_0(u1_struct_0(A_158)) | v1_xboole_0(u1_struct_0(A_159)) | r1_waybel_0(A_158, A_159, k2_relset_1(u1_struct_0(A_159), u1_struct_0(A_158), u1_waybel_0(A_158, A_159))) | v2_struct_0(A_158) | ~l1_waybel_0(A_159, A_158) | ~l1_struct_0(A_158) | ~l1_struct_0(A_159) | v2_struct_0(A_159))), inference(resolution, [status(thm)], [c_40, c_130])).
% 2.52/1.36  tff(c_42, plain, (~r1_waybel_0('#skF_4', '#skF_5', k2_relset_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'), u1_waybel_0('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_155])).
% 2.52/1.36  tff(c_162, plain, (~v1_funct_2(u1_waybel_0('#skF_4', '#skF_5'), u1_struct_0('#skF_5'), u1_struct_0('#skF_4')) | ~v1_funct_1(u1_waybel_0('#skF_4', '#skF_5')) | v1_xboole_0(u1_struct_0('#skF_4')) | v1_xboole_0(u1_struct_0('#skF_5')) | v2_struct_0('#skF_4') | ~l1_waybel_0('#skF_5', '#skF_4') | ~l1_struct_0('#skF_4') | ~l1_struct_0('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_157, c_42])).
% 2.52/1.36  tff(c_166, plain, (~v1_funct_2(u1_waybel_0('#skF_4', '#skF_5'), u1_struct_0('#skF_5'), u1_struct_0('#skF_4')) | ~v1_funct_1(u1_waybel_0('#skF_4', '#skF_5')) | v1_xboole_0(u1_struct_0('#skF_4')) | v1_xboole_0(u1_struct_0('#skF_5')) | v2_struct_0('#skF_4') | ~l1_struct_0('#skF_5') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_44, c_162])).
% 2.52/1.36  tff(c_167, plain, (~v1_funct_2(u1_waybel_0('#skF_4', '#skF_5'), u1_struct_0('#skF_5'), u1_struct_0('#skF_4')) | ~v1_funct_1(u1_waybel_0('#skF_4', '#skF_5')) | v1_xboole_0(u1_struct_0('#skF_5')) | ~l1_struct_0('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_46, c_50, c_150, c_166])).
% 2.52/1.36  tff(c_168, plain, (~l1_struct_0('#skF_5')), inference(splitLeft, [status(thm)], [c_167])).
% 2.52/1.36  tff(c_171, plain, (~l1_orders_2('#skF_5')), inference(resolution, [status(thm)], [c_6, c_168])).
% 2.52/1.36  tff(c_175, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_62, c_171])).
% 2.52/1.36  tff(c_177, plain, (l1_struct_0('#skF_5')), inference(splitRight, [status(thm)], [c_167])).
% 2.52/1.36  tff(c_26, plain, (![A_81, B_82]: (v1_funct_1(u1_waybel_0(A_81, B_82)) | ~l1_waybel_0(B_82, A_81) | ~l1_struct_0(A_81))), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.52/1.36  tff(c_24, plain, (![A_81, B_82]: (v1_funct_2(u1_waybel_0(A_81, B_82), u1_struct_0(B_82), u1_struct_0(A_81)) | ~l1_waybel_0(B_82, A_81) | ~l1_struct_0(A_81))), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.52/1.36  tff(c_176, plain, (~v1_funct_1(u1_waybel_0('#skF_4', '#skF_5')) | ~v1_funct_2(u1_waybel_0('#skF_4', '#skF_5'), u1_struct_0('#skF_5'), u1_struct_0('#skF_4')) | v1_xboole_0(u1_struct_0('#skF_5'))), inference(splitRight, [status(thm)], [c_167])).
% 2.52/1.36  tff(c_178, plain, (~v1_funct_2(u1_waybel_0('#skF_4', '#skF_5'), u1_struct_0('#skF_5'), u1_struct_0('#skF_4'))), inference(splitLeft, [status(thm)], [c_176])).
% 2.52/1.36  tff(c_181, plain, (~l1_waybel_0('#skF_5', '#skF_4') | ~l1_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_24, c_178])).
% 2.52/1.36  tff(c_185, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_44, c_181])).
% 2.52/1.36  tff(c_186, plain, (~v1_funct_1(u1_waybel_0('#skF_4', '#skF_5')) | v1_xboole_0(u1_struct_0('#skF_5'))), inference(splitRight, [status(thm)], [c_176])).
% 2.52/1.36  tff(c_188, plain, (~v1_funct_1(u1_waybel_0('#skF_4', '#skF_5'))), inference(splitLeft, [status(thm)], [c_186])).
% 2.52/1.36  tff(c_191, plain, (~l1_waybel_0('#skF_5', '#skF_4') | ~l1_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_26, c_188])).
% 2.52/1.36  tff(c_195, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_44, c_191])).
% 2.52/1.36  tff(c_196, plain, (v1_xboole_0(u1_struct_0('#skF_5'))), inference(splitRight, [status(thm)], [c_186])).
% 2.52/1.36  tff(c_200, plain, (~l1_struct_0('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_196, c_4])).
% 2.52/1.36  tff(c_203, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_177, c_200])).
% 2.52/1.36  tff(c_205, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_203])).
% 2.52/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.52/1.36  
% 2.52/1.36  Inference rules
% 2.52/1.36  ----------------------
% 2.52/1.36  #Ref     : 0
% 2.52/1.36  #Sup     : 23
% 2.52/1.36  #Fact    : 0
% 2.52/1.36  #Define  : 0
% 2.52/1.36  #Split   : 4
% 2.52/1.36  #Chain   : 0
% 2.52/1.36  #Close   : 0
% 2.52/1.36  
% 2.52/1.36  Ordering : KBO
% 2.52/1.36  
% 2.52/1.36  Simplification rules
% 2.52/1.36  ----------------------
% 2.52/1.36  #Subsume      : 6
% 2.52/1.36  #Demod        : 11
% 2.52/1.36  #Tautology    : 3
% 2.52/1.36  #SimpNegUnit  : 5
% 2.52/1.36  #BackRed      : 0
% 2.52/1.36  
% 2.52/1.36  #Partial instantiations: 0
% 2.52/1.36  #Strategies tried      : 1
% 2.52/1.36  
% 2.52/1.36  Timing (in seconds)
% 2.52/1.36  ----------------------
% 2.78/1.36  Preprocessing        : 0.33
% 2.78/1.36  Parsing              : 0.18
% 2.78/1.36  CNF conversion       : 0.03
% 2.78/1.36  Main loop            : 0.26
% 2.78/1.36  Inferencing          : 0.12
% 2.78/1.36  Reduction            : 0.06
% 2.78/1.36  Demodulation         : 0.04
% 2.78/1.36  BG Simplification    : 0.02
% 2.78/1.36  Subsumption          : 0.05
% 2.78/1.36  Abstraction          : 0.01
% 2.78/1.36  MUC search           : 0.00
% 2.78/1.36  Cooper               : 0.00
% 2.78/1.36  Total                : 0.63
% 2.78/1.36  Index Insertion      : 0.00
% 2.78/1.37  Index Deletion       : 0.00
% 2.78/1.37  Index Matching       : 0.00
% 2.78/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
