%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:07 EST 2020

% Result     : Theorem 2.47s
% Output     : CNFRefutation 2.47s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 408 expanded)
%              Number of leaves         :   37 ( 156 expanded)
%              Depth                    :   17
%              Number of atoms          :  245 (2155 expanded)
%              Number of equality atoms :    2 (  22 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r1_waybel_0 > r1_orders_2 > r2_hidden > m1_subset_1 > l1_waybel_0 > v2_struct_0 > v1_xboole_0 > v1_funct_1 > l1_struct_0 > l1_orders_2 > k3_funct_2 > k2_waybel_0 > k2_relset_1 > u1_waybel_0 > k4_yellow_6 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1

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

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff(k2_waybel_0,type,(
    k2_waybel_0: ( $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(r1_waybel_0,type,(
    r1_waybel_0: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

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

tff(f_141,negated_conjecture,(
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

tff(f_127,axiom,(
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

tff(f_118,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ? [B] : l1_waybel_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_l1_waybel_0)).

tff(c_36,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_38,plain,(
    l1_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_34,plain,(
    l1_waybel_0('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_43,plain,(
    ! [B_90,A_91] :
      ( l1_orders_2(B_90)
      | ~ l1_waybel_0(B_90,A_91)
      | ~ l1_struct_0(A_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_49,plain,
    ( l1_orders_2('#skF_5')
    | ~ l1_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_34,c_43])).

tff(c_53,plain,(
    l1_orders_2('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_49])).

tff(c_6,plain,(
    ! [A_17] :
      ( l1_struct_0(A_17)
      | ~ l1_orders_2(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_40,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_30,plain,(
    ! [A_85,B_86] :
      ( m1_subset_1(k4_yellow_6(A_85,B_86),u1_struct_0(A_85))
      | ~ l1_waybel_0(B_86,A_85)
      | ~ l1_struct_0(A_85)
      | v2_struct_0(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

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

tff(c_73,plain,(
    ! [A_120,B_121,D_122,C_123] :
      ( r2_hidden(k3_funct_2(A_120,B_121,D_122,C_123),k2_relset_1(A_120,B_121,D_122))
      | ~ m1_subset_1(D_122,k1_zfmisc_1(k2_zfmisc_1(A_120,B_121)))
      | ~ v1_funct_2(D_122,A_120,B_121)
      | ~ v1_funct_1(D_122)
      | ~ m1_subset_1(C_123,A_120)
      | v1_xboole_0(B_121)
      | v1_xboole_0(A_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_89,plain,(
    ! [A_133,B_134,C_135] :
      ( r2_hidden(k2_waybel_0(A_133,B_134,C_135),k2_relset_1(u1_struct_0(B_134),u1_struct_0(A_133),u1_waybel_0(A_133,B_134)))
      | ~ m1_subset_1(u1_waybel_0(A_133,B_134),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_134),u1_struct_0(A_133))))
      | ~ v1_funct_2(u1_waybel_0(A_133,B_134),u1_struct_0(B_134),u1_struct_0(A_133))
      | ~ v1_funct_1(u1_waybel_0(A_133,B_134))
      | ~ m1_subset_1(C_135,u1_struct_0(B_134))
      | v1_xboole_0(u1_struct_0(A_133))
      | v1_xboole_0(u1_struct_0(B_134))
      | ~ m1_subset_1(C_135,u1_struct_0(B_134))
      | ~ l1_waybel_0(B_134,A_133)
      | v2_struct_0(B_134)
      | ~ l1_struct_0(A_133)
      | v2_struct_0(A_133) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_73])).

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

tff(c_95,plain,(
    ! [A_136,B_137,D_138] :
      ( r1_waybel_0(A_136,B_137,k2_relset_1(u1_struct_0(B_137),u1_struct_0(A_136),u1_waybel_0(A_136,B_137)))
      | ~ m1_subset_1(D_138,u1_struct_0(B_137))
      | ~ m1_subset_1(u1_waybel_0(A_136,B_137),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_137),u1_struct_0(A_136))))
      | ~ v1_funct_2(u1_waybel_0(A_136,B_137),u1_struct_0(B_137),u1_struct_0(A_136))
      | ~ v1_funct_1(u1_waybel_0(A_136,B_137))
      | v1_xboole_0(u1_struct_0(A_136))
      | v1_xboole_0(u1_struct_0(B_137))
      | ~ m1_subset_1('#skF_1'(A_136,B_137,k2_relset_1(u1_struct_0(B_137),u1_struct_0(A_136),u1_waybel_0(A_136,B_137)),D_138),u1_struct_0(B_137))
      | ~ l1_waybel_0(B_137,A_136)
      | v2_struct_0(B_137)
      | ~ l1_struct_0(A_136)
      | v2_struct_0(A_136) ) ),
    inference(resolution,[status(thm)],[c_89,c_12])).

tff(c_101,plain,(
    ! [A_139,B_140,D_141] :
      ( ~ m1_subset_1(u1_waybel_0(A_139,B_140),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_140),u1_struct_0(A_139))))
      | ~ v1_funct_2(u1_waybel_0(A_139,B_140),u1_struct_0(B_140),u1_struct_0(A_139))
      | ~ v1_funct_1(u1_waybel_0(A_139,B_140))
      | v1_xboole_0(u1_struct_0(A_139))
      | v1_xboole_0(u1_struct_0(B_140))
      | r1_waybel_0(A_139,B_140,k2_relset_1(u1_struct_0(B_140),u1_struct_0(A_139),u1_waybel_0(A_139,B_140)))
      | ~ m1_subset_1(D_141,u1_struct_0(B_140))
      | ~ l1_waybel_0(B_140,A_139)
      | v2_struct_0(B_140)
      | ~ l1_struct_0(A_139)
      | v2_struct_0(A_139) ) ),
    inference(resolution,[status(thm)],[c_16,c_95])).

tff(c_105,plain,(
    ! [A_142,B_143,D_144] :
      ( ~ v1_funct_2(u1_waybel_0(A_142,B_143),u1_struct_0(B_143),u1_struct_0(A_142))
      | ~ v1_funct_1(u1_waybel_0(A_142,B_143))
      | v1_xboole_0(u1_struct_0(A_142))
      | v1_xboole_0(u1_struct_0(B_143))
      | r1_waybel_0(A_142,B_143,k2_relset_1(u1_struct_0(B_143),u1_struct_0(A_142),u1_waybel_0(A_142,B_143)))
      | ~ m1_subset_1(D_144,u1_struct_0(B_143))
      | v2_struct_0(B_143)
      | v2_struct_0(A_142)
      | ~ l1_waybel_0(B_143,A_142)
      | ~ l1_struct_0(A_142) ) ),
    inference(resolution,[status(thm)],[c_22,c_101])).

tff(c_115,plain,(
    ! [A_145,A_146,B_147] :
      ( ~ v1_funct_2(u1_waybel_0(A_145,A_146),u1_struct_0(A_146),u1_struct_0(A_145))
      | ~ v1_funct_1(u1_waybel_0(A_145,A_146))
      | v1_xboole_0(u1_struct_0(A_145))
      | v1_xboole_0(u1_struct_0(A_146))
      | r1_waybel_0(A_145,A_146,k2_relset_1(u1_struct_0(A_146),u1_struct_0(A_145),u1_waybel_0(A_145,A_146)))
      | v2_struct_0(A_145)
      | ~ l1_waybel_0(A_146,A_145)
      | ~ l1_struct_0(A_145)
      | ~ l1_waybel_0(B_147,A_146)
      | ~ l1_struct_0(A_146)
      | v2_struct_0(A_146) ) ),
    inference(resolution,[status(thm)],[c_30,c_105])).

tff(c_119,plain,(
    ! [A_145] :
      ( ~ v1_funct_2(u1_waybel_0(A_145,'#skF_4'),u1_struct_0('#skF_4'),u1_struct_0(A_145))
      | ~ v1_funct_1(u1_waybel_0(A_145,'#skF_4'))
      | v1_xboole_0(u1_struct_0(A_145))
      | v1_xboole_0(u1_struct_0('#skF_4'))
      | r1_waybel_0(A_145,'#skF_4',k2_relset_1(u1_struct_0('#skF_4'),u1_struct_0(A_145),u1_waybel_0(A_145,'#skF_4')))
      | v2_struct_0(A_145)
      | ~ l1_waybel_0('#skF_4',A_145)
      | ~ l1_struct_0(A_145)
      | ~ l1_struct_0('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_34,c_115])).

tff(c_123,plain,(
    ! [A_145] :
      ( ~ v1_funct_2(u1_waybel_0(A_145,'#skF_4'),u1_struct_0('#skF_4'),u1_struct_0(A_145))
      | ~ v1_funct_1(u1_waybel_0(A_145,'#skF_4'))
      | v1_xboole_0(u1_struct_0(A_145))
      | v1_xboole_0(u1_struct_0('#skF_4'))
      | r1_waybel_0(A_145,'#skF_4',k2_relset_1(u1_struct_0('#skF_4'),u1_struct_0(A_145),u1_waybel_0(A_145,'#skF_4')))
      | v2_struct_0(A_145)
      | ~ l1_waybel_0('#skF_4',A_145)
      | ~ l1_struct_0(A_145)
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_119])).

tff(c_124,plain,(
    ! [A_145] :
      ( ~ v1_funct_2(u1_waybel_0(A_145,'#skF_4'),u1_struct_0('#skF_4'),u1_struct_0(A_145))
      | ~ v1_funct_1(u1_waybel_0(A_145,'#skF_4'))
      | v1_xboole_0(u1_struct_0(A_145))
      | v1_xboole_0(u1_struct_0('#skF_4'))
      | r1_waybel_0(A_145,'#skF_4',k2_relset_1(u1_struct_0('#skF_4'),u1_struct_0(A_145),u1_waybel_0(A_145,'#skF_4')))
      | v2_struct_0(A_145)
      | ~ l1_waybel_0('#skF_4',A_145)
      | ~ l1_struct_0(A_145) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_123])).

tff(c_125,plain,(
    v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_124])).

tff(c_4,plain,(
    ! [A_16] :
      ( ~ v1_xboole_0(u1_struct_0(A_16))
      | ~ l1_struct_0(A_16)
      | v2_struct_0(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_128,plain,
    ( ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_125,c_4])).

tff(c_131,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_128])).

tff(c_133,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_131])).

tff(c_135,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_124])).

tff(c_28,plain,(
    ! [A_83] :
      ( l1_waybel_0('#skF_3'(A_83),A_83)
      | ~ l1_struct_0(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_137,plain,(
    ! [A_149,A_150] :
      ( ~ v1_funct_2(u1_waybel_0(A_149,A_150),u1_struct_0(A_150),u1_struct_0(A_149))
      | ~ v1_funct_1(u1_waybel_0(A_149,A_150))
      | v1_xboole_0(u1_struct_0(A_149))
      | v1_xboole_0(u1_struct_0(A_150))
      | r1_waybel_0(A_149,A_150,k2_relset_1(u1_struct_0(A_150),u1_struct_0(A_149),u1_waybel_0(A_149,A_150)))
      | v2_struct_0(A_149)
      | ~ l1_waybel_0(A_150,A_149)
      | ~ l1_struct_0(A_149)
      | v2_struct_0(A_150)
      | ~ l1_struct_0(A_150) ) ),
    inference(resolution,[status(thm)],[c_28,c_115])).

tff(c_32,plain,(
    ~ r1_waybel_0('#skF_4','#skF_5',k2_relset_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),u1_waybel_0('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_140,plain,
    ( ~ v1_funct_2(u1_waybel_0('#skF_4','#skF_5'),u1_struct_0('#skF_5'),u1_struct_0('#skF_4'))
    | ~ v1_funct_1(u1_waybel_0('#skF_4','#skF_5'))
    | v1_xboole_0(u1_struct_0('#skF_4'))
    | v1_xboole_0(u1_struct_0('#skF_5'))
    | v2_struct_0('#skF_4')
    | ~ l1_waybel_0('#skF_5','#skF_4')
    | ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_5')
    | ~ l1_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_137,c_32])).

tff(c_143,plain,
    ( ~ v1_funct_2(u1_waybel_0('#skF_4','#skF_5'),u1_struct_0('#skF_5'),u1_struct_0('#skF_4'))
    | ~ v1_funct_1(u1_waybel_0('#skF_4','#skF_5'))
    | v1_xboole_0(u1_struct_0('#skF_4'))
    | v1_xboole_0(u1_struct_0('#skF_5'))
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_5')
    | ~ l1_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_34,c_140])).

tff(c_144,plain,
    ( ~ v1_funct_2(u1_waybel_0('#skF_4','#skF_5'),u1_struct_0('#skF_5'),u1_struct_0('#skF_4'))
    | ~ v1_funct_1(u1_waybel_0('#skF_4','#skF_5'))
    | v1_xboole_0(u1_struct_0('#skF_5'))
    | ~ l1_struct_0('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_40,c_135,c_143])).

tff(c_145,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_144])).

tff(c_148,plain,(
    ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_6,c_145])).

tff(c_152,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_148])).

tff(c_154,plain,(
    l1_struct_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_144])).

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

tff(c_153,plain,
    ( ~ v1_funct_1(u1_waybel_0('#skF_4','#skF_5'))
    | ~ v1_funct_2(u1_waybel_0('#skF_4','#skF_5'),u1_struct_0('#skF_5'),u1_struct_0('#skF_4'))
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_144])).

tff(c_163,plain,(
    ~ v1_funct_2(u1_waybel_0('#skF_4','#skF_5'),u1_struct_0('#skF_5'),u1_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_153])).

tff(c_166,plain,
    ( ~ l1_waybel_0('#skF_5','#skF_4')
    | ~ l1_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_24,c_163])).

tff(c_170,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_34,c_166])).

tff(c_171,plain,
    ( ~ v1_funct_1(u1_waybel_0('#skF_4','#skF_5'))
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_153])).

tff(c_173,plain,(
    ~ v1_funct_1(u1_waybel_0('#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_171])).

tff(c_176,plain,
    ( ~ l1_waybel_0('#skF_5','#skF_4')
    | ~ l1_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_26,c_173])).

tff(c_180,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_34,c_176])).

tff(c_181,plain,(
    v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_171])).

tff(c_185,plain,
    ( ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_181,c_4])).

tff(c_188,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_185])).

tff(c_190,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_188])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n004.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 14:19:53 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.47/1.30  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.47/1.30  
% 2.47/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.47/1.31  %$ v1_funct_2 > r1_waybel_0 > r1_orders_2 > r2_hidden > m1_subset_1 > l1_waybel_0 > v2_struct_0 > v1_xboole_0 > v1_funct_1 > l1_struct_0 > l1_orders_2 > k3_funct_2 > k2_waybel_0 > k2_relset_1 > u1_waybel_0 > k4_yellow_6 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 2.47/1.31  
% 2.47/1.31  %Foreground sorts:
% 2.47/1.31  
% 2.47/1.31  
% 2.47/1.31  %Background operators:
% 2.47/1.31  
% 2.47/1.31  
% 2.47/1.31  %Foreground operators:
% 2.47/1.31  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.47/1.31  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.47/1.31  tff(k4_yellow_6, type, k4_yellow_6: ($i * $i) > $i).
% 2.47/1.31  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.47/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.47/1.31  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.47/1.31  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 2.47/1.31  tff(k2_waybel_0, type, k2_waybel_0: ($i * $i * $i) > $i).
% 2.47/1.31  tff('#skF_5', type, '#skF_5': $i).
% 2.47/1.31  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.47/1.31  tff(r1_waybel_0, type, r1_waybel_0: ($i * $i * $i) > $o).
% 2.47/1.31  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.47/1.31  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.47/1.31  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.47/1.31  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.47/1.31  tff(u1_waybel_0, type, u1_waybel_0: ($i * $i) > $i).
% 2.47/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.47/1.31  tff(l1_waybel_0, type, l1_waybel_0: ($i * $i) > $o).
% 2.47/1.31  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.47/1.31  tff('#skF_4', type, '#skF_4': $i).
% 2.47/1.31  tff('#skF_3', type, '#skF_3': $i > $i).
% 2.47/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.47/1.31  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 2.47/1.31  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.47/1.31  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.47/1.31  tff(k3_funct_2, type, k3_funct_2: ($i * $i * $i * $i) > $i).
% 2.47/1.31  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.47/1.31  
% 2.47/1.33  tff(f_141, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((~v2_struct_0(B) & l1_waybel_0(B, A)) => r1_waybel_0(A, B, k2_relset_1(u1_struct_0(B), u1_struct_0(A), u1_waybel_0(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_waybel_9)).
% 2.47/1.33  tff(f_103, axiom, (![A]: (l1_struct_0(A) => (![B]: (l1_waybel_0(B, A) => l1_orders_2(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_waybel_0)).
% 2.47/1.33  tff(f_56, axiom, (![A]: (l1_orders_2(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 2.47/1.33  tff(f_127, axiom, (![A, B]: (((~v2_struct_0(A) & l1_struct_0(A)) & l1_waybel_0(B, A)) => m1_subset_1(k4_yellow_6(A, B), u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_yellow_6)).
% 2.47/1.33  tff(f_113, axiom, (![A, B]: ((l1_struct_0(A) & l1_waybel_0(B, A)) => ((v1_funct_1(u1_waybel_0(A, B)) & v1_funct_2(u1_waybel_0(A, B), u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(u1_waybel_0(A, B), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_u1_waybel_0)).
% 2.47/1.33  tff(f_80, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((~v2_struct_0(B) & l1_waybel_0(B, A)) => (![C]: (r1_waybel_0(A, B, C) <=> (?[D]: (m1_subset_1(D, u1_struct_0(B)) & (![E]: (m1_subset_1(E, u1_struct_0(B)) => (r1_orders_2(B, D, E) => r2_hidden(k2_waybel_0(A, B, E), C)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d11_waybel_0)).
% 2.47/1.33  tff(f_96, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((~v2_struct_0(B) & l1_waybel_0(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(B)) => (k2_waybel_0(A, B, C) = k3_funct_2(u1_struct_0(B), u1_struct_0(A), u1_waybel_0(A, B), C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_waybel_0)).
% 2.47/1.33  tff(f_44, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, A) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_hidden(k3_funct_2(A, B, D, C), k2_relset_1(A, B, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t189_funct_2)).
% 2.47/1.33  tff(f_52, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 2.47/1.33  tff(f_118, axiom, (![A]: (l1_struct_0(A) => (?[B]: l1_waybel_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', existence_l1_waybel_0)).
% 2.47/1.33  tff(c_36, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_141])).
% 2.47/1.33  tff(c_38, plain, (l1_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_141])).
% 2.47/1.33  tff(c_34, plain, (l1_waybel_0('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_141])).
% 2.47/1.33  tff(c_43, plain, (![B_90, A_91]: (l1_orders_2(B_90) | ~l1_waybel_0(B_90, A_91) | ~l1_struct_0(A_91))), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.47/1.33  tff(c_49, plain, (l1_orders_2('#skF_5') | ~l1_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_34, c_43])).
% 2.47/1.33  tff(c_53, plain, (l1_orders_2('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_49])).
% 2.47/1.33  tff(c_6, plain, (![A_17]: (l1_struct_0(A_17) | ~l1_orders_2(A_17))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.47/1.33  tff(c_40, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_141])).
% 2.47/1.33  tff(c_30, plain, (![A_85, B_86]: (m1_subset_1(k4_yellow_6(A_85, B_86), u1_struct_0(A_85)) | ~l1_waybel_0(B_86, A_85) | ~l1_struct_0(A_85) | v2_struct_0(A_85))), inference(cnfTransformation, [status(thm)], [f_127])).
% 2.47/1.33  tff(c_22, plain, (![A_81, B_82]: (m1_subset_1(u1_waybel_0(A_81, B_82), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_82), u1_struct_0(A_81)))) | ~l1_waybel_0(B_82, A_81) | ~l1_struct_0(A_81))), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.47/1.33  tff(c_16, plain, (![A_18, B_46, C_60, D_67]: (m1_subset_1('#skF_1'(A_18, B_46, C_60, D_67), u1_struct_0(B_46)) | r1_waybel_0(A_18, B_46, C_60) | ~m1_subset_1(D_67, u1_struct_0(B_46)) | ~l1_waybel_0(B_46, A_18) | v2_struct_0(B_46) | ~l1_struct_0(A_18) | v2_struct_0(A_18))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.47/1.33  tff(c_18, plain, (![B_75, A_71, C_77]: (k3_funct_2(u1_struct_0(B_75), u1_struct_0(A_71), u1_waybel_0(A_71, B_75), C_77)=k2_waybel_0(A_71, B_75, C_77) | ~m1_subset_1(C_77, u1_struct_0(B_75)) | ~l1_waybel_0(B_75, A_71) | v2_struct_0(B_75) | ~l1_struct_0(A_71) | v2_struct_0(A_71))), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.47/1.33  tff(c_73, plain, (![A_120, B_121, D_122, C_123]: (r2_hidden(k3_funct_2(A_120, B_121, D_122, C_123), k2_relset_1(A_120, B_121, D_122)) | ~m1_subset_1(D_122, k1_zfmisc_1(k2_zfmisc_1(A_120, B_121))) | ~v1_funct_2(D_122, A_120, B_121) | ~v1_funct_1(D_122) | ~m1_subset_1(C_123, A_120) | v1_xboole_0(B_121) | v1_xboole_0(A_120))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.47/1.33  tff(c_89, plain, (![A_133, B_134, C_135]: (r2_hidden(k2_waybel_0(A_133, B_134, C_135), k2_relset_1(u1_struct_0(B_134), u1_struct_0(A_133), u1_waybel_0(A_133, B_134))) | ~m1_subset_1(u1_waybel_0(A_133, B_134), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_134), u1_struct_0(A_133)))) | ~v1_funct_2(u1_waybel_0(A_133, B_134), u1_struct_0(B_134), u1_struct_0(A_133)) | ~v1_funct_1(u1_waybel_0(A_133, B_134)) | ~m1_subset_1(C_135, u1_struct_0(B_134)) | v1_xboole_0(u1_struct_0(A_133)) | v1_xboole_0(u1_struct_0(B_134)) | ~m1_subset_1(C_135, u1_struct_0(B_134)) | ~l1_waybel_0(B_134, A_133) | v2_struct_0(B_134) | ~l1_struct_0(A_133) | v2_struct_0(A_133))), inference(superposition, [status(thm), theory('equality')], [c_18, c_73])).
% 2.47/1.33  tff(c_12, plain, (![A_18, B_46, C_60, D_67]: (~r2_hidden(k2_waybel_0(A_18, B_46, '#skF_1'(A_18, B_46, C_60, D_67)), C_60) | r1_waybel_0(A_18, B_46, C_60) | ~m1_subset_1(D_67, u1_struct_0(B_46)) | ~l1_waybel_0(B_46, A_18) | v2_struct_0(B_46) | ~l1_struct_0(A_18) | v2_struct_0(A_18))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.47/1.33  tff(c_95, plain, (![A_136, B_137, D_138]: (r1_waybel_0(A_136, B_137, k2_relset_1(u1_struct_0(B_137), u1_struct_0(A_136), u1_waybel_0(A_136, B_137))) | ~m1_subset_1(D_138, u1_struct_0(B_137)) | ~m1_subset_1(u1_waybel_0(A_136, B_137), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_137), u1_struct_0(A_136)))) | ~v1_funct_2(u1_waybel_0(A_136, B_137), u1_struct_0(B_137), u1_struct_0(A_136)) | ~v1_funct_1(u1_waybel_0(A_136, B_137)) | v1_xboole_0(u1_struct_0(A_136)) | v1_xboole_0(u1_struct_0(B_137)) | ~m1_subset_1('#skF_1'(A_136, B_137, k2_relset_1(u1_struct_0(B_137), u1_struct_0(A_136), u1_waybel_0(A_136, B_137)), D_138), u1_struct_0(B_137)) | ~l1_waybel_0(B_137, A_136) | v2_struct_0(B_137) | ~l1_struct_0(A_136) | v2_struct_0(A_136))), inference(resolution, [status(thm)], [c_89, c_12])).
% 2.47/1.33  tff(c_101, plain, (![A_139, B_140, D_141]: (~m1_subset_1(u1_waybel_0(A_139, B_140), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_140), u1_struct_0(A_139)))) | ~v1_funct_2(u1_waybel_0(A_139, B_140), u1_struct_0(B_140), u1_struct_0(A_139)) | ~v1_funct_1(u1_waybel_0(A_139, B_140)) | v1_xboole_0(u1_struct_0(A_139)) | v1_xboole_0(u1_struct_0(B_140)) | r1_waybel_0(A_139, B_140, k2_relset_1(u1_struct_0(B_140), u1_struct_0(A_139), u1_waybel_0(A_139, B_140))) | ~m1_subset_1(D_141, u1_struct_0(B_140)) | ~l1_waybel_0(B_140, A_139) | v2_struct_0(B_140) | ~l1_struct_0(A_139) | v2_struct_0(A_139))), inference(resolution, [status(thm)], [c_16, c_95])).
% 2.47/1.33  tff(c_105, plain, (![A_142, B_143, D_144]: (~v1_funct_2(u1_waybel_0(A_142, B_143), u1_struct_0(B_143), u1_struct_0(A_142)) | ~v1_funct_1(u1_waybel_0(A_142, B_143)) | v1_xboole_0(u1_struct_0(A_142)) | v1_xboole_0(u1_struct_0(B_143)) | r1_waybel_0(A_142, B_143, k2_relset_1(u1_struct_0(B_143), u1_struct_0(A_142), u1_waybel_0(A_142, B_143))) | ~m1_subset_1(D_144, u1_struct_0(B_143)) | v2_struct_0(B_143) | v2_struct_0(A_142) | ~l1_waybel_0(B_143, A_142) | ~l1_struct_0(A_142))), inference(resolution, [status(thm)], [c_22, c_101])).
% 2.47/1.33  tff(c_115, plain, (![A_145, A_146, B_147]: (~v1_funct_2(u1_waybel_0(A_145, A_146), u1_struct_0(A_146), u1_struct_0(A_145)) | ~v1_funct_1(u1_waybel_0(A_145, A_146)) | v1_xboole_0(u1_struct_0(A_145)) | v1_xboole_0(u1_struct_0(A_146)) | r1_waybel_0(A_145, A_146, k2_relset_1(u1_struct_0(A_146), u1_struct_0(A_145), u1_waybel_0(A_145, A_146))) | v2_struct_0(A_145) | ~l1_waybel_0(A_146, A_145) | ~l1_struct_0(A_145) | ~l1_waybel_0(B_147, A_146) | ~l1_struct_0(A_146) | v2_struct_0(A_146))), inference(resolution, [status(thm)], [c_30, c_105])).
% 2.47/1.33  tff(c_119, plain, (![A_145]: (~v1_funct_2(u1_waybel_0(A_145, '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0(A_145)) | ~v1_funct_1(u1_waybel_0(A_145, '#skF_4')) | v1_xboole_0(u1_struct_0(A_145)) | v1_xboole_0(u1_struct_0('#skF_4')) | r1_waybel_0(A_145, '#skF_4', k2_relset_1(u1_struct_0('#skF_4'), u1_struct_0(A_145), u1_waybel_0(A_145, '#skF_4'))) | v2_struct_0(A_145) | ~l1_waybel_0('#skF_4', A_145) | ~l1_struct_0(A_145) | ~l1_struct_0('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_34, c_115])).
% 2.47/1.33  tff(c_123, plain, (![A_145]: (~v1_funct_2(u1_waybel_0(A_145, '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0(A_145)) | ~v1_funct_1(u1_waybel_0(A_145, '#skF_4')) | v1_xboole_0(u1_struct_0(A_145)) | v1_xboole_0(u1_struct_0('#skF_4')) | r1_waybel_0(A_145, '#skF_4', k2_relset_1(u1_struct_0('#skF_4'), u1_struct_0(A_145), u1_waybel_0(A_145, '#skF_4'))) | v2_struct_0(A_145) | ~l1_waybel_0('#skF_4', A_145) | ~l1_struct_0(A_145) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_119])).
% 2.47/1.33  tff(c_124, plain, (![A_145]: (~v1_funct_2(u1_waybel_0(A_145, '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0(A_145)) | ~v1_funct_1(u1_waybel_0(A_145, '#skF_4')) | v1_xboole_0(u1_struct_0(A_145)) | v1_xboole_0(u1_struct_0('#skF_4')) | r1_waybel_0(A_145, '#skF_4', k2_relset_1(u1_struct_0('#skF_4'), u1_struct_0(A_145), u1_waybel_0(A_145, '#skF_4'))) | v2_struct_0(A_145) | ~l1_waybel_0('#skF_4', A_145) | ~l1_struct_0(A_145))), inference(negUnitSimplification, [status(thm)], [c_40, c_123])).
% 2.47/1.33  tff(c_125, plain, (v1_xboole_0(u1_struct_0('#skF_4'))), inference(splitLeft, [status(thm)], [c_124])).
% 2.47/1.33  tff(c_4, plain, (![A_16]: (~v1_xboole_0(u1_struct_0(A_16)) | ~l1_struct_0(A_16) | v2_struct_0(A_16))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.47/1.33  tff(c_128, plain, (~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_125, c_4])).
% 2.47/1.33  tff(c_131, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_128])).
% 2.47/1.33  tff(c_133, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_131])).
% 2.47/1.33  tff(c_135, plain, (~v1_xboole_0(u1_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_124])).
% 2.47/1.33  tff(c_28, plain, (![A_83]: (l1_waybel_0('#skF_3'(A_83), A_83) | ~l1_struct_0(A_83))), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.47/1.33  tff(c_137, plain, (![A_149, A_150]: (~v1_funct_2(u1_waybel_0(A_149, A_150), u1_struct_0(A_150), u1_struct_0(A_149)) | ~v1_funct_1(u1_waybel_0(A_149, A_150)) | v1_xboole_0(u1_struct_0(A_149)) | v1_xboole_0(u1_struct_0(A_150)) | r1_waybel_0(A_149, A_150, k2_relset_1(u1_struct_0(A_150), u1_struct_0(A_149), u1_waybel_0(A_149, A_150))) | v2_struct_0(A_149) | ~l1_waybel_0(A_150, A_149) | ~l1_struct_0(A_149) | v2_struct_0(A_150) | ~l1_struct_0(A_150))), inference(resolution, [status(thm)], [c_28, c_115])).
% 2.47/1.33  tff(c_32, plain, (~r1_waybel_0('#skF_4', '#skF_5', k2_relset_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'), u1_waybel_0('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_141])).
% 2.47/1.33  tff(c_140, plain, (~v1_funct_2(u1_waybel_0('#skF_4', '#skF_5'), u1_struct_0('#skF_5'), u1_struct_0('#skF_4')) | ~v1_funct_1(u1_waybel_0('#skF_4', '#skF_5')) | v1_xboole_0(u1_struct_0('#skF_4')) | v1_xboole_0(u1_struct_0('#skF_5')) | v2_struct_0('#skF_4') | ~l1_waybel_0('#skF_5', '#skF_4') | ~l1_struct_0('#skF_4') | v2_struct_0('#skF_5') | ~l1_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_137, c_32])).
% 2.47/1.33  tff(c_143, plain, (~v1_funct_2(u1_waybel_0('#skF_4', '#skF_5'), u1_struct_0('#skF_5'), u1_struct_0('#skF_4')) | ~v1_funct_1(u1_waybel_0('#skF_4', '#skF_5')) | v1_xboole_0(u1_struct_0('#skF_4')) | v1_xboole_0(u1_struct_0('#skF_5')) | v2_struct_0('#skF_4') | v2_struct_0('#skF_5') | ~l1_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_34, c_140])).
% 2.47/1.33  tff(c_144, plain, (~v1_funct_2(u1_waybel_0('#skF_4', '#skF_5'), u1_struct_0('#skF_5'), u1_struct_0('#skF_4')) | ~v1_funct_1(u1_waybel_0('#skF_4', '#skF_5')) | v1_xboole_0(u1_struct_0('#skF_5')) | ~l1_struct_0('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_36, c_40, c_135, c_143])).
% 2.47/1.33  tff(c_145, plain, (~l1_struct_0('#skF_5')), inference(splitLeft, [status(thm)], [c_144])).
% 2.47/1.33  tff(c_148, plain, (~l1_orders_2('#skF_5')), inference(resolution, [status(thm)], [c_6, c_145])).
% 2.47/1.33  tff(c_152, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_53, c_148])).
% 2.47/1.33  tff(c_154, plain, (l1_struct_0('#skF_5')), inference(splitRight, [status(thm)], [c_144])).
% 2.47/1.33  tff(c_26, plain, (![A_81, B_82]: (v1_funct_1(u1_waybel_0(A_81, B_82)) | ~l1_waybel_0(B_82, A_81) | ~l1_struct_0(A_81))), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.47/1.33  tff(c_24, plain, (![A_81, B_82]: (v1_funct_2(u1_waybel_0(A_81, B_82), u1_struct_0(B_82), u1_struct_0(A_81)) | ~l1_waybel_0(B_82, A_81) | ~l1_struct_0(A_81))), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.47/1.33  tff(c_153, plain, (~v1_funct_1(u1_waybel_0('#skF_4', '#skF_5')) | ~v1_funct_2(u1_waybel_0('#skF_4', '#skF_5'), u1_struct_0('#skF_5'), u1_struct_0('#skF_4')) | v1_xboole_0(u1_struct_0('#skF_5'))), inference(splitRight, [status(thm)], [c_144])).
% 2.47/1.33  tff(c_163, plain, (~v1_funct_2(u1_waybel_0('#skF_4', '#skF_5'), u1_struct_0('#skF_5'), u1_struct_0('#skF_4'))), inference(splitLeft, [status(thm)], [c_153])).
% 2.47/1.33  tff(c_166, plain, (~l1_waybel_0('#skF_5', '#skF_4') | ~l1_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_24, c_163])).
% 2.47/1.33  tff(c_170, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_34, c_166])).
% 2.47/1.33  tff(c_171, plain, (~v1_funct_1(u1_waybel_0('#skF_4', '#skF_5')) | v1_xboole_0(u1_struct_0('#skF_5'))), inference(splitRight, [status(thm)], [c_153])).
% 2.47/1.33  tff(c_173, plain, (~v1_funct_1(u1_waybel_0('#skF_4', '#skF_5'))), inference(splitLeft, [status(thm)], [c_171])).
% 2.47/1.33  tff(c_176, plain, (~l1_waybel_0('#skF_5', '#skF_4') | ~l1_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_26, c_173])).
% 2.47/1.33  tff(c_180, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_34, c_176])).
% 2.47/1.33  tff(c_181, plain, (v1_xboole_0(u1_struct_0('#skF_5'))), inference(splitRight, [status(thm)], [c_171])).
% 2.47/1.33  tff(c_185, plain, (~l1_struct_0('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_181, c_4])).
% 2.47/1.33  tff(c_188, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_154, c_185])).
% 2.47/1.33  tff(c_190, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_188])).
% 2.47/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.47/1.33  
% 2.47/1.33  Inference rules
% 2.47/1.33  ----------------------
% 2.47/1.33  #Ref     : 0
% 2.47/1.33  #Sup     : 23
% 2.47/1.33  #Fact    : 0
% 2.47/1.33  #Define  : 0
% 2.47/1.33  #Split   : 4
% 2.47/1.33  #Chain   : 0
% 2.47/1.33  #Close   : 0
% 2.47/1.33  
% 2.47/1.33  Ordering : KBO
% 2.47/1.33  
% 2.47/1.33  Simplification rules
% 2.47/1.33  ----------------------
% 2.47/1.33  #Subsume      : 6
% 2.47/1.33  #Demod        : 11
% 2.47/1.33  #Tautology    : 3
% 2.47/1.33  #SimpNegUnit  : 5
% 2.47/1.33  #BackRed      : 0
% 2.47/1.33  
% 2.47/1.33  #Partial instantiations: 0
% 2.47/1.33  #Strategies tried      : 1
% 2.47/1.33  
% 2.47/1.33  Timing (in seconds)
% 2.47/1.33  ----------------------
% 2.47/1.33  Preprocessing        : 0.32
% 2.47/1.33  Parsing              : 0.18
% 2.47/1.33  CNF conversion       : 0.03
% 2.47/1.33  Main loop            : 0.23
% 2.47/1.33  Inferencing          : 0.10
% 2.47/1.33  Reduction            : 0.05
% 2.47/1.33  Demodulation         : 0.04
% 2.47/1.33  BG Simplification    : 0.01
% 2.47/1.33  Subsumption          : 0.05
% 2.47/1.33  Abstraction          : 0.01
% 2.47/1.33  MUC search           : 0.00
% 2.47/1.33  Cooper               : 0.00
% 2.47/1.33  Total                : 0.60
% 2.47/1.33  Index Insertion      : 0.00
% 2.47/1.33  Index Deletion       : 0.00
% 2.47/1.33  Index Matching       : 0.00
% 2.47/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
