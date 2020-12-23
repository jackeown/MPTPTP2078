%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:07 EST 2020

% Result     : Theorem 2.58s
% Output     : CNFRefutation 2.78s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 413 expanded)
%              Number of leaves         :   42 ( 161 expanded)
%              Depth                    :   17
%              Number of atoms          :  251 (2185 expanded)
%              Number of equality atoms :    2 (  22 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r1_waybel_0 > r1_orders_2 > v6_waybel_0 > r2_hidden > m1_subset_1 > l1_waybel_0 > v7_waybel_0 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > v1_funct_1 > l1_struct_0 > l1_orders_2 > k3_funct_2 > k2_waybel_0 > k2_relset_1 > u1_waybel_0 > k4_yellow_6 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k4_yellow_6,type,(
    k4_yellow_6: ( $i * $i ) > $i )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

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

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

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

tff(f_154,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & l1_struct_0(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & l1_waybel_0(B,A) )
           => r1_waybel_0(A,B,k2_relset_1(u1_struct_0(B),u1_struct_0(A),u1_waybel_0(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_waybel_9)).

tff(f_103,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ! [B] :
          ( l1_waybel_0(B,A)
         => l1_orders_2(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_waybel_0)).

tff(f_56,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_122,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A)
        & l1_waybel_0(B,A) )
     => m1_subset_1(k4_yellow_6(A,B),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_yellow_6)).

tff(f_113,axiom,(
    ! [A,B] :
      ( ( l1_struct_0(A)
        & l1_waybel_0(B,A) )
     => ( v1_funct_1(u1_waybel_0(A,B))
        & v1_funct_2(u1_waybel_0(A,B),u1_struct_0(B),u1_struct_0(A))
        & m1_subset_1(u1_waybel_0(A,B),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B),u1_struct_0(A)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_waybel_0)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_waybel_0)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_waybel_0)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t189_funct_2)).

tff(f_52,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_140,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ? [B] :
          ( l1_waybel_0(B,A)
          & ~ v2_struct_0(B)
          & v3_orders_2(B)
          & v4_orders_2(B)
          & v5_orders_2(B)
          & v6_waybel_0(B,A)
          & v7_waybel_0(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc5_waybel_0)).

tff(c_48,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_50,plain,(
    l1_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_46,plain,(
    l1_waybel_0('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_62,plain,(
    ! [B_97,A_98] :
      ( l1_orders_2(B_97)
      | ~ l1_waybel_0(B_97,A_98)
      | ~ l1_struct_0(A_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_68,plain,
    ( l1_orders_2('#skF_5')
    | ~ l1_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_62])).

tff(c_72,plain,(
    l1_orders_2('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_68])).

tff(c_6,plain,(
    ! [A_17] :
      ( l1_struct_0(A_17)
      | ~ l1_orders_2(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_52,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

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

tff(c_91,plain,(
    ! [A_126,B_127,D_128,C_129] :
      ( r2_hidden(k3_funct_2(A_126,B_127,D_128,C_129),k2_relset_1(A_126,B_127,D_128))
      | ~ m1_subset_1(D_128,k1_zfmisc_1(k2_zfmisc_1(A_126,B_127)))
      | ~ v1_funct_2(D_128,A_126,B_127)
      | ~ v1_funct_1(D_128)
      | ~ m1_subset_1(C_129,A_126)
      | v1_xboole_0(B_127)
      | v1_xboole_0(A_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_107,plain,(
    ! [A_139,B_140,C_141] :
      ( r2_hidden(k2_waybel_0(A_139,B_140,C_141),k2_relset_1(u1_struct_0(B_140),u1_struct_0(A_139),u1_waybel_0(A_139,B_140)))
      | ~ m1_subset_1(u1_waybel_0(A_139,B_140),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_140),u1_struct_0(A_139))))
      | ~ v1_funct_2(u1_waybel_0(A_139,B_140),u1_struct_0(B_140),u1_struct_0(A_139))
      | ~ v1_funct_1(u1_waybel_0(A_139,B_140))
      | ~ m1_subset_1(C_141,u1_struct_0(B_140))
      | v1_xboole_0(u1_struct_0(A_139))
      | v1_xboole_0(u1_struct_0(B_140))
      | ~ m1_subset_1(C_141,u1_struct_0(B_140))
      | ~ l1_waybel_0(B_140,A_139)
      | v2_struct_0(B_140)
      | ~ l1_struct_0(A_139)
      | v2_struct_0(A_139) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_91])).

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

tff(c_113,plain,(
    ! [A_142,B_143,D_144] :
      ( r1_waybel_0(A_142,B_143,k2_relset_1(u1_struct_0(B_143),u1_struct_0(A_142),u1_waybel_0(A_142,B_143)))
      | ~ m1_subset_1(D_144,u1_struct_0(B_143))
      | ~ m1_subset_1(u1_waybel_0(A_142,B_143),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_143),u1_struct_0(A_142))))
      | ~ v1_funct_2(u1_waybel_0(A_142,B_143),u1_struct_0(B_143),u1_struct_0(A_142))
      | ~ v1_funct_1(u1_waybel_0(A_142,B_143))
      | v1_xboole_0(u1_struct_0(A_142))
      | v1_xboole_0(u1_struct_0(B_143))
      | ~ m1_subset_1('#skF_1'(A_142,B_143,k2_relset_1(u1_struct_0(B_143),u1_struct_0(A_142),u1_waybel_0(A_142,B_143)),D_144),u1_struct_0(B_143))
      | ~ l1_waybel_0(B_143,A_142)
      | v2_struct_0(B_143)
      | ~ l1_struct_0(A_142)
      | v2_struct_0(A_142) ) ),
    inference(resolution,[status(thm)],[c_107,c_12])).

tff(c_119,plain,(
    ! [A_145,B_146,D_147] :
      ( ~ m1_subset_1(u1_waybel_0(A_145,B_146),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_146),u1_struct_0(A_145))))
      | ~ v1_funct_2(u1_waybel_0(A_145,B_146),u1_struct_0(B_146),u1_struct_0(A_145))
      | ~ v1_funct_1(u1_waybel_0(A_145,B_146))
      | v1_xboole_0(u1_struct_0(A_145))
      | v1_xboole_0(u1_struct_0(B_146))
      | r1_waybel_0(A_145,B_146,k2_relset_1(u1_struct_0(B_146),u1_struct_0(A_145),u1_waybel_0(A_145,B_146)))
      | ~ m1_subset_1(D_147,u1_struct_0(B_146))
      | ~ l1_waybel_0(B_146,A_145)
      | v2_struct_0(B_146)
      | ~ l1_struct_0(A_145)
      | v2_struct_0(A_145) ) ),
    inference(resolution,[status(thm)],[c_16,c_113])).

tff(c_123,plain,(
    ! [A_148,B_149,D_150] :
      ( ~ v1_funct_2(u1_waybel_0(A_148,B_149),u1_struct_0(B_149),u1_struct_0(A_148))
      | ~ v1_funct_1(u1_waybel_0(A_148,B_149))
      | v1_xboole_0(u1_struct_0(A_148))
      | v1_xboole_0(u1_struct_0(B_149))
      | r1_waybel_0(A_148,B_149,k2_relset_1(u1_struct_0(B_149),u1_struct_0(A_148),u1_waybel_0(A_148,B_149)))
      | ~ m1_subset_1(D_150,u1_struct_0(B_149))
      | v2_struct_0(B_149)
      | v2_struct_0(A_148)
      | ~ l1_waybel_0(B_149,A_148)
      | ~ l1_struct_0(A_148) ) ),
    inference(resolution,[status(thm)],[c_22,c_119])).

tff(c_133,plain,(
    ! [A_151,A_152,B_153] :
      ( ~ v1_funct_2(u1_waybel_0(A_151,A_152),u1_struct_0(A_152),u1_struct_0(A_151))
      | ~ v1_funct_1(u1_waybel_0(A_151,A_152))
      | v1_xboole_0(u1_struct_0(A_151))
      | v1_xboole_0(u1_struct_0(A_152))
      | r1_waybel_0(A_151,A_152,k2_relset_1(u1_struct_0(A_152),u1_struct_0(A_151),u1_waybel_0(A_151,A_152)))
      | v2_struct_0(A_151)
      | ~ l1_waybel_0(A_152,A_151)
      | ~ l1_struct_0(A_151)
      | ~ l1_waybel_0(B_153,A_152)
      | ~ l1_struct_0(A_152)
      | v2_struct_0(A_152) ) ),
    inference(resolution,[status(thm)],[c_28,c_123])).

tff(c_137,plain,(
    ! [A_151] :
      ( ~ v1_funct_2(u1_waybel_0(A_151,'#skF_4'),u1_struct_0('#skF_4'),u1_struct_0(A_151))
      | ~ v1_funct_1(u1_waybel_0(A_151,'#skF_4'))
      | v1_xboole_0(u1_struct_0(A_151))
      | v1_xboole_0(u1_struct_0('#skF_4'))
      | r1_waybel_0(A_151,'#skF_4',k2_relset_1(u1_struct_0('#skF_4'),u1_struct_0(A_151),u1_waybel_0(A_151,'#skF_4')))
      | v2_struct_0(A_151)
      | ~ l1_waybel_0('#skF_4',A_151)
      | ~ l1_struct_0(A_151)
      | ~ l1_struct_0('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_46,c_133])).

tff(c_141,plain,(
    ! [A_151] :
      ( ~ v1_funct_2(u1_waybel_0(A_151,'#skF_4'),u1_struct_0('#skF_4'),u1_struct_0(A_151))
      | ~ v1_funct_1(u1_waybel_0(A_151,'#skF_4'))
      | v1_xboole_0(u1_struct_0(A_151))
      | v1_xboole_0(u1_struct_0('#skF_4'))
      | r1_waybel_0(A_151,'#skF_4',k2_relset_1(u1_struct_0('#skF_4'),u1_struct_0(A_151),u1_waybel_0(A_151,'#skF_4')))
      | v2_struct_0(A_151)
      | ~ l1_waybel_0('#skF_4',A_151)
      | ~ l1_struct_0(A_151)
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_137])).

tff(c_142,plain,(
    ! [A_151] :
      ( ~ v1_funct_2(u1_waybel_0(A_151,'#skF_4'),u1_struct_0('#skF_4'),u1_struct_0(A_151))
      | ~ v1_funct_1(u1_waybel_0(A_151,'#skF_4'))
      | v1_xboole_0(u1_struct_0(A_151))
      | v1_xboole_0(u1_struct_0('#skF_4'))
      | r1_waybel_0(A_151,'#skF_4',k2_relset_1(u1_struct_0('#skF_4'),u1_struct_0(A_151),u1_waybel_0(A_151,'#skF_4')))
      | v2_struct_0(A_151)
      | ~ l1_waybel_0('#skF_4',A_151)
      | ~ l1_struct_0(A_151) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_141])).

tff(c_143,plain,(
    v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_142])).

tff(c_4,plain,(
    ! [A_16] :
      ( ~ v1_xboole_0(u1_struct_0(A_16))
      | ~ l1_struct_0(A_16)
      | v2_struct_0(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_147,plain,
    ( ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_143,c_4])).

tff(c_150,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_147])).

tff(c_152,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_150])).

tff(c_154,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_142])).

tff(c_42,plain,(
    ! [A_85] :
      ( l1_waybel_0('#skF_3'(A_85),A_85)
      | ~ l1_struct_0(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_156,plain,(
    ! [A_159,A_160] :
      ( ~ v1_funct_2(u1_waybel_0(A_159,A_160),u1_struct_0(A_160),u1_struct_0(A_159))
      | ~ v1_funct_1(u1_waybel_0(A_159,A_160))
      | v1_xboole_0(u1_struct_0(A_159))
      | v1_xboole_0(u1_struct_0(A_160))
      | r1_waybel_0(A_159,A_160,k2_relset_1(u1_struct_0(A_160),u1_struct_0(A_159),u1_waybel_0(A_159,A_160)))
      | v2_struct_0(A_159)
      | ~ l1_waybel_0(A_160,A_159)
      | ~ l1_struct_0(A_159)
      | v2_struct_0(A_160)
      | ~ l1_struct_0(A_160) ) ),
    inference(resolution,[status(thm)],[c_42,c_133])).

tff(c_44,plain,(
    ~ r1_waybel_0('#skF_4','#skF_5',k2_relset_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),u1_waybel_0('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_159,plain,
    ( ~ v1_funct_2(u1_waybel_0('#skF_4','#skF_5'),u1_struct_0('#skF_5'),u1_struct_0('#skF_4'))
    | ~ v1_funct_1(u1_waybel_0('#skF_4','#skF_5'))
    | v1_xboole_0(u1_struct_0('#skF_4'))
    | v1_xboole_0(u1_struct_0('#skF_5'))
    | v2_struct_0('#skF_4')
    | ~ l1_waybel_0('#skF_5','#skF_4')
    | ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_5')
    | ~ l1_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_156,c_44])).

tff(c_162,plain,
    ( ~ v1_funct_2(u1_waybel_0('#skF_4','#skF_5'),u1_struct_0('#skF_5'),u1_struct_0('#skF_4'))
    | ~ v1_funct_1(u1_waybel_0('#skF_4','#skF_5'))
    | v1_xboole_0(u1_struct_0('#skF_4'))
    | v1_xboole_0(u1_struct_0('#skF_5'))
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_5')
    | ~ l1_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_46,c_159])).

tff(c_163,plain,
    ( ~ v1_funct_2(u1_waybel_0('#skF_4','#skF_5'),u1_struct_0('#skF_5'),u1_struct_0('#skF_4'))
    | ~ v1_funct_1(u1_waybel_0('#skF_4','#skF_5'))
    | v1_xboole_0(u1_struct_0('#skF_5'))
    | ~ l1_struct_0('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_52,c_154,c_162])).

tff(c_164,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_163])).

tff(c_167,plain,(
    ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_6,c_164])).

tff(c_171,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_167])).

tff(c_173,plain,(
    l1_struct_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_163])).

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

tff(c_172,plain,
    ( ~ v1_funct_1(u1_waybel_0('#skF_4','#skF_5'))
    | ~ v1_funct_2(u1_waybel_0('#skF_4','#skF_5'),u1_struct_0('#skF_5'),u1_struct_0('#skF_4'))
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_163])).

tff(c_174,plain,(
    ~ v1_funct_2(u1_waybel_0('#skF_4','#skF_5'),u1_struct_0('#skF_5'),u1_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_172])).

tff(c_177,plain,
    ( ~ l1_waybel_0('#skF_5','#skF_4')
    | ~ l1_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_24,c_174])).

tff(c_181,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_46,c_177])).

tff(c_182,plain,
    ( ~ v1_funct_1(u1_waybel_0('#skF_4','#skF_5'))
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_172])).

tff(c_192,plain,(
    ~ v1_funct_1(u1_waybel_0('#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_182])).

tff(c_195,plain,
    ( ~ l1_waybel_0('#skF_5','#skF_4')
    | ~ l1_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_26,c_192])).

tff(c_199,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_46,c_195])).

tff(c_200,plain,(
    v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_182])).

tff(c_204,plain,
    ( ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_200,c_4])).

tff(c_207,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_173,c_204])).

tff(c_209,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_207])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n019.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 13:09:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.58/1.40  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.58/1.41  
% 2.58/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.58/1.41  %$ v1_funct_2 > r1_waybel_0 > r1_orders_2 > v6_waybel_0 > r2_hidden > m1_subset_1 > l1_waybel_0 > v7_waybel_0 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > v1_funct_1 > l1_struct_0 > l1_orders_2 > k3_funct_2 > k2_waybel_0 > k2_relset_1 > u1_waybel_0 > k4_yellow_6 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 2.58/1.41  
% 2.58/1.41  %Foreground sorts:
% 2.58/1.41  
% 2.58/1.41  
% 2.58/1.41  %Background operators:
% 2.58/1.41  
% 2.58/1.41  
% 2.58/1.41  %Foreground operators:
% 2.58/1.41  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.58/1.41  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.58/1.41  tff(k4_yellow_6, type, k4_yellow_6: ($i * $i) > $i).
% 2.58/1.41  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 2.58/1.41  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.58/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.58/1.41  tff(v6_waybel_0, type, v6_waybel_0: ($i * $i) > $o).
% 2.58/1.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.58/1.41  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 2.58/1.41  tff(k2_waybel_0, type, k2_waybel_0: ($i * $i * $i) > $i).
% 2.58/1.41  tff(v7_waybel_0, type, v7_waybel_0: $i > $o).
% 2.58/1.41  tff('#skF_5', type, '#skF_5': $i).
% 2.58/1.41  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.58/1.41  tff(r1_waybel_0, type, r1_waybel_0: ($i * $i * $i) > $o).
% 2.58/1.41  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.58/1.41  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.58/1.41  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 2.58/1.41  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.58/1.41  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.58/1.41  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.58/1.41  tff(u1_waybel_0, type, u1_waybel_0: ($i * $i) > $i).
% 2.58/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.58/1.41  tff(l1_waybel_0, type, l1_waybel_0: ($i * $i) > $o).
% 2.58/1.41  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.58/1.41  tff('#skF_4', type, '#skF_4': $i).
% 2.58/1.41  tff('#skF_3', type, '#skF_3': $i > $i).
% 2.58/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.58/1.41  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 2.58/1.41  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.58/1.41  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.58/1.41  tff(k3_funct_2, type, k3_funct_2: ($i * $i * $i * $i) > $i).
% 2.58/1.41  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.58/1.41  
% 2.78/1.43  tff(f_154, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((~v2_struct_0(B) & l1_waybel_0(B, A)) => r1_waybel_0(A, B, k2_relset_1(u1_struct_0(B), u1_struct_0(A), u1_waybel_0(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_waybel_9)).
% 2.78/1.43  tff(f_103, axiom, (![A]: (l1_struct_0(A) => (![B]: (l1_waybel_0(B, A) => l1_orders_2(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_waybel_0)).
% 2.78/1.43  tff(f_56, axiom, (![A]: (l1_orders_2(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 2.78/1.43  tff(f_122, axiom, (![A, B]: (((~v2_struct_0(A) & l1_struct_0(A)) & l1_waybel_0(B, A)) => m1_subset_1(k4_yellow_6(A, B), u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_yellow_6)).
% 2.78/1.43  tff(f_113, axiom, (![A, B]: ((l1_struct_0(A) & l1_waybel_0(B, A)) => ((v1_funct_1(u1_waybel_0(A, B)) & v1_funct_2(u1_waybel_0(A, B), u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(u1_waybel_0(A, B), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_u1_waybel_0)).
% 2.78/1.43  tff(f_80, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((~v2_struct_0(B) & l1_waybel_0(B, A)) => (![C]: (r1_waybel_0(A, B, C) <=> (?[D]: (m1_subset_1(D, u1_struct_0(B)) & (![E]: (m1_subset_1(E, u1_struct_0(B)) => (r1_orders_2(B, D, E) => r2_hidden(k2_waybel_0(A, B, E), C)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d11_waybel_0)).
% 2.78/1.43  tff(f_96, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((~v2_struct_0(B) & l1_waybel_0(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(B)) => (k2_waybel_0(A, B, C) = k3_funct_2(u1_struct_0(B), u1_struct_0(A), u1_waybel_0(A, B), C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_waybel_0)).
% 2.78/1.43  tff(f_44, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, A) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_hidden(k3_funct_2(A, B, D, C), k2_relset_1(A, B, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t189_funct_2)).
% 2.78/1.43  tff(f_52, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 2.78/1.43  tff(f_140, axiom, (![A]: (l1_struct_0(A) => (?[B]: ((((((l1_waybel_0(B, A) & ~v2_struct_0(B)) & v3_orders_2(B)) & v4_orders_2(B)) & v5_orders_2(B)) & v6_waybel_0(B, A)) & v7_waybel_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc5_waybel_0)).
% 2.78/1.43  tff(c_48, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_154])).
% 2.78/1.43  tff(c_50, plain, (l1_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_154])).
% 2.78/1.43  tff(c_46, plain, (l1_waybel_0('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_154])).
% 2.78/1.43  tff(c_62, plain, (![B_97, A_98]: (l1_orders_2(B_97) | ~l1_waybel_0(B_97, A_98) | ~l1_struct_0(A_98))), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.78/1.43  tff(c_68, plain, (l1_orders_2('#skF_5') | ~l1_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_46, c_62])).
% 2.78/1.43  tff(c_72, plain, (l1_orders_2('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_68])).
% 2.78/1.43  tff(c_6, plain, (![A_17]: (l1_struct_0(A_17) | ~l1_orders_2(A_17))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.78/1.43  tff(c_52, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_154])).
% 2.78/1.43  tff(c_28, plain, (![A_83, B_84]: (m1_subset_1(k4_yellow_6(A_83, B_84), u1_struct_0(A_83)) | ~l1_waybel_0(B_84, A_83) | ~l1_struct_0(A_83) | v2_struct_0(A_83))), inference(cnfTransformation, [status(thm)], [f_122])).
% 2.78/1.43  tff(c_22, plain, (![A_81, B_82]: (m1_subset_1(u1_waybel_0(A_81, B_82), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_82), u1_struct_0(A_81)))) | ~l1_waybel_0(B_82, A_81) | ~l1_struct_0(A_81))), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.78/1.43  tff(c_16, plain, (![A_18, B_46, C_60, D_67]: (m1_subset_1('#skF_1'(A_18, B_46, C_60, D_67), u1_struct_0(B_46)) | r1_waybel_0(A_18, B_46, C_60) | ~m1_subset_1(D_67, u1_struct_0(B_46)) | ~l1_waybel_0(B_46, A_18) | v2_struct_0(B_46) | ~l1_struct_0(A_18) | v2_struct_0(A_18))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.78/1.43  tff(c_18, plain, (![B_75, A_71, C_77]: (k3_funct_2(u1_struct_0(B_75), u1_struct_0(A_71), u1_waybel_0(A_71, B_75), C_77)=k2_waybel_0(A_71, B_75, C_77) | ~m1_subset_1(C_77, u1_struct_0(B_75)) | ~l1_waybel_0(B_75, A_71) | v2_struct_0(B_75) | ~l1_struct_0(A_71) | v2_struct_0(A_71))), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.78/1.43  tff(c_91, plain, (![A_126, B_127, D_128, C_129]: (r2_hidden(k3_funct_2(A_126, B_127, D_128, C_129), k2_relset_1(A_126, B_127, D_128)) | ~m1_subset_1(D_128, k1_zfmisc_1(k2_zfmisc_1(A_126, B_127))) | ~v1_funct_2(D_128, A_126, B_127) | ~v1_funct_1(D_128) | ~m1_subset_1(C_129, A_126) | v1_xboole_0(B_127) | v1_xboole_0(A_126))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.78/1.43  tff(c_107, plain, (![A_139, B_140, C_141]: (r2_hidden(k2_waybel_0(A_139, B_140, C_141), k2_relset_1(u1_struct_0(B_140), u1_struct_0(A_139), u1_waybel_0(A_139, B_140))) | ~m1_subset_1(u1_waybel_0(A_139, B_140), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_140), u1_struct_0(A_139)))) | ~v1_funct_2(u1_waybel_0(A_139, B_140), u1_struct_0(B_140), u1_struct_0(A_139)) | ~v1_funct_1(u1_waybel_0(A_139, B_140)) | ~m1_subset_1(C_141, u1_struct_0(B_140)) | v1_xboole_0(u1_struct_0(A_139)) | v1_xboole_0(u1_struct_0(B_140)) | ~m1_subset_1(C_141, u1_struct_0(B_140)) | ~l1_waybel_0(B_140, A_139) | v2_struct_0(B_140) | ~l1_struct_0(A_139) | v2_struct_0(A_139))), inference(superposition, [status(thm), theory('equality')], [c_18, c_91])).
% 2.78/1.43  tff(c_12, plain, (![A_18, B_46, C_60, D_67]: (~r2_hidden(k2_waybel_0(A_18, B_46, '#skF_1'(A_18, B_46, C_60, D_67)), C_60) | r1_waybel_0(A_18, B_46, C_60) | ~m1_subset_1(D_67, u1_struct_0(B_46)) | ~l1_waybel_0(B_46, A_18) | v2_struct_0(B_46) | ~l1_struct_0(A_18) | v2_struct_0(A_18))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.78/1.43  tff(c_113, plain, (![A_142, B_143, D_144]: (r1_waybel_0(A_142, B_143, k2_relset_1(u1_struct_0(B_143), u1_struct_0(A_142), u1_waybel_0(A_142, B_143))) | ~m1_subset_1(D_144, u1_struct_0(B_143)) | ~m1_subset_1(u1_waybel_0(A_142, B_143), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_143), u1_struct_0(A_142)))) | ~v1_funct_2(u1_waybel_0(A_142, B_143), u1_struct_0(B_143), u1_struct_0(A_142)) | ~v1_funct_1(u1_waybel_0(A_142, B_143)) | v1_xboole_0(u1_struct_0(A_142)) | v1_xboole_0(u1_struct_0(B_143)) | ~m1_subset_1('#skF_1'(A_142, B_143, k2_relset_1(u1_struct_0(B_143), u1_struct_0(A_142), u1_waybel_0(A_142, B_143)), D_144), u1_struct_0(B_143)) | ~l1_waybel_0(B_143, A_142) | v2_struct_0(B_143) | ~l1_struct_0(A_142) | v2_struct_0(A_142))), inference(resolution, [status(thm)], [c_107, c_12])).
% 2.78/1.43  tff(c_119, plain, (![A_145, B_146, D_147]: (~m1_subset_1(u1_waybel_0(A_145, B_146), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_146), u1_struct_0(A_145)))) | ~v1_funct_2(u1_waybel_0(A_145, B_146), u1_struct_0(B_146), u1_struct_0(A_145)) | ~v1_funct_1(u1_waybel_0(A_145, B_146)) | v1_xboole_0(u1_struct_0(A_145)) | v1_xboole_0(u1_struct_0(B_146)) | r1_waybel_0(A_145, B_146, k2_relset_1(u1_struct_0(B_146), u1_struct_0(A_145), u1_waybel_0(A_145, B_146))) | ~m1_subset_1(D_147, u1_struct_0(B_146)) | ~l1_waybel_0(B_146, A_145) | v2_struct_0(B_146) | ~l1_struct_0(A_145) | v2_struct_0(A_145))), inference(resolution, [status(thm)], [c_16, c_113])).
% 2.78/1.43  tff(c_123, plain, (![A_148, B_149, D_150]: (~v1_funct_2(u1_waybel_0(A_148, B_149), u1_struct_0(B_149), u1_struct_0(A_148)) | ~v1_funct_1(u1_waybel_0(A_148, B_149)) | v1_xboole_0(u1_struct_0(A_148)) | v1_xboole_0(u1_struct_0(B_149)) | r1_waybel_0(A_148, B_149, k2_relset_1(u1_struct_0(B_149), u1_struct_0(A_148), u1_waybel_0(A_148, B_149))) | ~m1_subset_1(D_150, u1_struct_0(B_149)) | v2_struct_0(B_149) | v2_struct_0(A_148) | ~l1_waybel_0(B_149, A_148) | ~l1_struct_0(A_148))), inference(resolution, [status(thm)], [c_22, c_119])).
% 2.78/1.43  tff(c_133, plain, (![A_151, A_152, B_153]: (~v1_funct_2(u1_waybel_0(A_151, A_152), u1_struct_0(A_152), u1_struct_0(A_151)) | ~v1_funct_1(u1_waybel_0(A_151, A_152)) | v1_xboole_0(u1_struct_0(A_151)) | v1_xboole_0(u1_struct_0(A_152)) | r1_waybel_0(A_151, A_152, k2_relset_1(u1_struct_0(A_152), u1_struct_0(A_151), u1_waybel_0(A_151, A_152))) | v2_struct_0(A_151) | ~l1_waybel_0(A_152, A_151) | ~l1_struct_0(A_151) | ~l1_waybel_0(B_153, A_152) | ~l1_struct_0(A_152) | v2_struct_0(A_152))), inference(resolution, [status(thm)], [c_28, c_123])).
% 2.78/1.43  tff(c_137, plain, (![A_151]: (~v1_funct_2(u1_waybel_0(A_151, '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0(A_151)) | ~v1_funct_1(u1_waybel_0(A_151, '#skF_4')) | v1_xboole_0(u1_struct_0(A_151)) | v1_xboole_0(u1_struct_0('#skF_4')) | r1_waybel_0(A_151, '#skF_4', k2_relset_1(u1_struct_0('#skF_4'), u1_struct_0(A_151), u1_waybel_0(A_151, '#skF_4'))) | v2_struct_0(A_151) | ~l1_waybel_0('#skF_4', A_151) | ~l1_struct_0(A_151) | ~l1_struct_0('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_46, c_133])).
% 2.78/1.43  tff(c_141, plain, (![A_151]: (~v1_funct_2(u1_waybel_0(A_151, '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0(A_151)) | ~v1_funct_1(u1_waybel_0(A_151, '#skF_4')) | v1_xboole_0(u1_struct_0(A_151)) | v1_xboole_0(u1_struct_0('#skF_4')) | r1_waybel_0(A_151, '#skF_4', k2_relset_1(u1_struct_0('#skF_4'), u1_struct_0(A_151), u1_waybel_0(A_151, '#skF_4'))) | v2_struct_0(A_151) | ~l1_waybel_0('#skF_4', A_151) | ~l1_struct_0(A_151) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_137])).
% 2.78/1.43  tff(c_142, plain, (![A_151]: (~v1_funct_2(u1_waybel_0(A_151, '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0(A_151)) | ~v1_funct_1(u1_waybel_0(A_151, '#skF_4')) | v1_xboole_0(u1_struct_0(A_151)) | v1_xboole_0(u1_struct_0('#skF_4')) | r1_waybel_0(A_151, '#skF_4', k2_relset_1(u1_struct_0('#skF_4'), u1_struct_0(A_151), u1_waybel_0(A_151, '#skF_4'))) | v2_struct_0(A_151) | ~l1_waybel_0('#skF_4', A_151) | ~l1_struct_0(A_151))), inference(negUnitSimplification, [status(thm)], [c_52, c_141])).
% 2.78/1.43  tff(c_143, plain, (v1_xboole_0(u1_struct_0('#skF_4'))), inference(splitLeft, [status(thm)], [c_142])).
% 2.78/1.43  tff(c_4, plain, (![A_16]: (~v1_xboole_0(u1_struct_0(A_16)) | ~l1_struct_0(A_16) | v2_struct_0(A_16))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.78/1.43  tff(c_147, plain, (~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_143, c_4])).
% 2.78/1.43  tff(c_150, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_147])).
% 2.78/1.43  tff(c_152, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_150])).
% 2.78/1.43  tff(c_154, plain, (~v1_xboole_0(u1_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_142])).
% 2.78/1.43  tff(c_42, plain, (![A_85]: (l1_waybel_0('#skF_3'(A_85), A_85) | ~l1_struct_0(A_85))), inference(cnfTransformation, [status(thm)], [f_140])).
% 2.78/1.43  tff(c_156, plain, (![A_159, A_160]: (~v1_funct_2(u1_waybel_0(A_159, A_160), u1_struct_0(A_160), u1_struct_0(A_159)) | ~v1_funct_1(u1_waybel_0(A_159, A_160)) | v1_xboole_0(u1_struct_0(A_159)) | v1_xboole_0(u1_struct_0(A_160)) | r1_waybel_0(A_159, A_160, k2_relset_1(u1_struct_0(A_160), u1_struct_0(A_159), u1_waybel_0(A_159, A_160))) | v2_struct_0(A_159) | ~l1_waybel_0(A_160, A_159) | ~l1_struct_0(A_159) | v2_struct_0(A_160) | ~l1_struct_0(A_160))), inference(resolution, [status(thm)], [c_42, c_133])).
% 2.78/1.43  tff(c_44, plain, (~r1_waybel_0('#skF_4', '#skF_5', k2_relset_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'), u1_waybel_0('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_154])).
% 2.78/1.43  tff(c_159, plain, (~v1_funct_2(u1_waybel_0('#skF_4', '#skF_5'), u1_struct_0('#skF_5'), u1_struct_0('#skF_4')) | ~v1_funct_1(u1_waybel_0('#skF_4', '#skF_5')) | v1_xboole_0(u1_struct_0('#skF_4')) | v1_xboole_0(u1_struct_0('#skF_5')) | v2_struct_0('#skF_4') | ~l1_waybel_0('#skF_5', '#skF_4') | ~l1_struct_0('#skF_4') | v2_struct_0('#skF_5') | ~l1_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_156, c_44])).
% 2.78/1.43  tff(c_162, plain, (~v1_funct_2(u1_waybel_0('#skF_4', '#skF_5'), u1_struct_0('#skF_5'), u1_struct_0('#skF_4')) | ~v1_funct_1(u1_waybel_0('#skF_4', '#skF_5')) | v1_xboole_0(u1_struct_0('#skF_4')) | v1_xboole_0(u1_struct_0('#skF_5')) | v2_struct_0('#skF_4') | v2_struct_0('#skF_5') | ~l1_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_46, c_159])).
% 2.78/1.43  tff(c_163, plain, (~v1_funct_2(u1_waybel_0('#skF_4', '#skF_5'), u1_struct_0('#skF_5'), u1_struct_0('#skF_4')) | ~v1_funct_1(u1_waybel_0('#skF_4', '#skF_5')) | v1_xboole_0(u1_struct_0('#skF_5')) | ~l1_struct_0('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_48, c_52, c_154, c_162])).
% 2.78/1.43  tff(c_164, plain, (~l1_struct_0('#skF_5')), inference(splitLeft, [status(thm)], [c_163])).
% 2.78/1.43  tff(c_167, plain, (~l1_orders_2('#skF_5')), inference(resolution, [status(thm)], [c_6, c_164])).
% 2.78/1.43  tff(c_171, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_72, c_167])).
% 2.78/1.43  tff(c_173, plain, (l1_struct_0('#skF_5')), inference(splitRight, [status(thm)], [c_163])).
% 2.78/1.43  tff(c_26, plain, (![A_81, B_82]: (v1_funct_1(u1_waybel_0(A_81, B_82)) | ~l1_waybel_0(B_82, A_81) | ~l1_struct_0(A_81))), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.78/1.43  tff(c_24, plain, (![A_81, B_82]: (v1_funct_2(u1_waybel_0(A_81, B_82), u1_struct_0(B_82), u1_struct_0(A_81)) | ~l1_waybel_0(B_82, A_81) | ~l1_struct_0(A_81))), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.78/1.43  tff(c_172, plain, (~v1_funct_1(u1_waybel_0('#skF_4', '#skF_5')) | ~v1_funct_2(u1_waybel_0('#skF_4', '#skF_5'), u1_struct_0('#skF_5'), u1_struct_0('#skF_4')) | v1_xboole_0(u1_struct_0('#skF_5'))), inference(splitRight, [status(thm)], [c_163])).
% 2.78/1.43  tff(c_174, plain, (~v1_funct_2(u1_waybel_0('#skF_4', '#skF_5'), u1_struct_0('#skF_5'), u1_struct_0('#skF_4'))), inference(splitLeft, [status(thm)], [c_172])).
% 2.78/1.43  tff(c_177, plain, (~l1_waybel_0('#skF_5', '#skF_4') | ~l1_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_24, c_174])).
% 2.78/1.43  tff(c_181, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_46, c_177])).
% 2.78/1.43  tff(c_182, plain, (~v1_funct_1(u1_waybel_0('#skF_4', '#skF_5')) | v1_xboole_0(u1_struct_0('#skF_5'))), inference(splitRight, [status(thm)], [c_172])).
% 2.78/1.43  tff(c_192, plain, (~v1_funct_1(u1_waybel_0('#skF_4', '#skF_5'))), inference(splitLeft, [status(thm)], [c_182])).
% 2.78/1.43  tff(c_195, plain, (~l1_waybel_0('#skF_5', '#skF_4') | ~l1_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_26, c_192])).
% 2.78/1.43  tff(c_199, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_46, c_195])).
% 2.78/1.43  tff(c_200, plain, (v1_xboole_0(u1_struct_0('#skF_5'))), inference(splitRight, [status(thm)], [c_182])).
% 2.78/1.43  tff(c_204, plain, (~l1_struct_0('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_200, c_4])).
% 2.78/1.43  tff(c_207, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_173, c_204])).
% 2.78/1.43  tff(c_209, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_207])).
% 2.78/1.43  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.78/1.43  
% 2.78/1.43  Inference rules
% 2.78/1.43  ----------------------
% 2.78/1.43  #Ref     : 0
% 2.78/1.43  #Sup     : 23
% 2.78/1.43  #Fact    : 0
% 2.78/1.43  #Define  : 0
% 2.78/1.43  #Split   : 4
% 2.78/1.43  #Chain   : 0
% 2.78/1.43  #Close   : 0
% 2.78/1.43  
% 2.78/1.43  Ordering : KBO
% 2.78/1.43  
% 2.78/1.43  Simplification rules
% 2.78/1.43  ----------------------
% 2.78/1.43  #Subsume      : 6
% 2.78/1.43  #Demod        : 11
% 2.78/1.43  #Tautology    : 3
% 2.78/1.43  #SimpNegUnit  : 5
% 2.78/1.43  #BackRed      : 0
% 2.78/1.43  
% 2.78/1.43  #Partial instantiations: 0
% 2.78/1.43  #Strategies tried      : 1
% 2.78/1.43  
% 2.78/1.43  Timing (in seconds)
% 2.78/1.43  ----------------------
% 2.78/1.43  Preprocessing        : 0.34
% 2.78/1.43  Parsing              : 0.19
% 2.78/1.43  CNF conversion       : 0.03
% 2.78/1.43  Main loop            : 0.26
% 2.78/1.43  Inferencing          : 0.11
% 2.78/1.43  Reduction            : 0.06
% 2.78/1.43  Demodulation         : 0.04
% 2.78/1.43  BG Simplification    : 0.02
% 2.78/1.43  Subsumption          : 0.06
% 2.78/1.43  Abstraction          : 0.01
% 2.78/1.43  MUC search           : 0.00
% 2.78/1.43  Cooper               : 0.00
% 2.78/1.43  Total                : 0.64
% 2.78/1.43  Index Insertion      : 0.00
% 2.78/1.43  Index Deletion       : 0.00
% 2.78/1.43  Index Matching       : 0.00
% 2.78/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
