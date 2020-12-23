%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:07 EST 2020

% Result     : Theorem 2.58s
% Output     : CNFRefutation 2.58s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 409 expanded)
%              Number of leaves         :   38 ( 157 expanded)
%              Depth                    :   17
%              Number of atoms          :  246 (2160 expanded)
%              Number of equality atoms :    2 (  22 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r1_waybel_0 > r1_orders_2 > v6_waybel_0 > r2_hidden > m1_subset_1 > l1_waybel_0 > v2_struct_0 > v1_xboole_0 > v1_funct_1 > l1_struct_0 > l1_orders_2 > k3_funct_2 > k2_waybel_0 > k2_relset_1 > u1_waybel_0 > k4_yellow_6 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1

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

tff(f_143,negated_conjecture,(
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

tff(f_129,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ? [B] :
          ( l1_waybel_0(B,A)
          & v6_waybel_0(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc4_waybel_0)).

tff(c_38,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_40,plain,(
    l1_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_36,plain,(
    l1_waybel_0('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_46,plain,(
    ! [B_91,A_92] :
      ( l1_orders_2(B_91)
      | ~ l1_waybel_0(B_91,A_92)
      | ~ l1_struct_0(A_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_52,plain,
    ( l1_orders_2('#skF_5')
    | ~ l1_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_46])).

tff(c_56,plain,(
    l1_orders_2('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_52])).

tff(c_6,plain,(
    ! [A_17] :
      ( l1_struct_0(A_17)
      | ~ l1_orders_2(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_42,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

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

tff(c_76,plain,(
    ! [A_121,B_122,D_123,C_124] :
      ( r2_hidden(k3_funct_2(A_121,B_122,D_123,C_124),k2_relset_1(A_121,B_122,D_123))
      | ~ m1_subset_1(D_123,k1_zfmisc_1(k2_zfmisc_1(A_121,B_122)))
      | ~ v1_funct_2(D_123,A_121,B_122)
      | ~ v1_funct_1(D_123)
      | ~ m1_subset_1(C_124,A_121)
      | v1_xboole_0(B_122)
      | v1_xboole_0(A_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_92,plain,(
    ! [A_134,B_135,C_136] :
      ( r2_hidden(k2_waybel_0(A_134,B_135,C_136),k2_relset_1(u1_struct_0(B_135),u1_struct_0(A_134),u1_waybel_0(A_134,B_135)))
      | ~ m1_subset_1(u1_waybel_0(A_134,B_135),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_135),u1_struct_0(A_134))))
      | ~ v1_funct_2(u1_waybel_0(A_134,B_135),u1_struct_0(B_135),u1_struct_0(A_134))
      | ~ v1_funct_1(u1_waybel_0(A_134,B_135))
      | ~ m1_subset_1(C_136,u1_struct_0(B_135))
      | v1_xboole_0(u1_struct_0(A_134))
      | v1_xboole_0(u1_struct_0(B_135))
      | ~ m1_subset_1(C_136,u1_struct_0(B_135))
      | ~ l1_waybel_0(B_135,A_134)
      | v2_struct_0(B_135)
      | ~ l1_struct_0(A_134)
      | v2_struct_0(A_134) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_76])).

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

tff(c_98,plain,(
    ! [A_137,B_138,D_139] :
      ( r1_waybel_0(A_137,B_138,k2_relset_1(u1_struct_0(B_138),u1_struct_0(A_137),u1_waybel_0(A_137,B_138)))
      | ~ m1_subset_1(D_139,u1_struct_0(B_138))
      | ~ m1_subset_1(u1_waybel_0(A_137,B_138),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_138),u1_struct_0(A_137))))
      | ~ v1_funct_2(u1_waybel_0(A_137,B_138),u1_struct_0(B_138),u1_struct_0(A_137))
      | ~ v1_funct_1(u1_waybel_0(A_137,B_138))
      | v1_xboole_0(u1_struct_0(A_137))
      | v1_xboole_0(u1_struct_0(B_138))
      | ~ m1_subset_1('#skF_1'(A_137,B_138,k2_relset_1(u1_struct_0(B_138),u1_struct_0(A_137),u1_waybel_0(A_137,B_138)),D_139),u1_struct_0(B_138))
      | ~ l1_waybel_0(B_138,A_137)
      | v2_struct_0(B_138)
      | ~ l1_struct_0(A_137)
      | v2_struct_0(A_137) ) ),
    inference(resolution,[status(thm)],[c_92,c_12])).

tff(c_104,plain,(
    ! [A_140,B_141,D_142] :
      ( ~ m1_subset_1(u1_waybel_0(A_140,B_141),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_141),u1_struct_0(A_140))))
      | ~ v1_funct_2(u1_waybel_0(A_140,B_141),u1_struct_0(B_141),u1_struct_0(A_140))
      | ~ v1_funct_1(u1_waybel_0(A_140,B_141))
      | v1_xboole_0(u1_struct_0(A_140))
      | v1_xboole_0(u1_struct_0(B_141))
      | r1_waybel_0(A_140,B_141,k2_relset_1(u1_struct_0(B_141),u1_struct_0(A_140),u1_waybel_0(A_140,B_141)))
      | ~ m1_subset_1(D_142,u1_struct_0(B_141))
      | ~ l1_waybel_0(B_141,A_140)
      | v2_struct_0(B_141)
      | ~ l1_struct_0(A_140)
      | v2_struct_0(A_140) ) ),
    inference(resolution,[status(thm)],[c_16,c_98])).

tff(c_108,plain,(
    ! [A_143,B_144,D_145] :
      ( ~ v1_funct_2(u1_waybel_0(A_143,B_144),u1_struct_0(B_144),u1_struct_0(A_143))
      | ~ v1_funct_1(u1_waybel_0(A_143,B_144))
      | v1_xboole_0(u1_struct_0(A_143))
      | v1_xboole_0(u1_struct_0(B_144))
      | r1_waybel_0(A_143,B_144,k2_relset_1(u1_struct_0(B_144),u1_struct_0(A_143),u1_waybel_0(A_143,B_144)))
      | ~ m1_subset_1(D_145,u1_struct_0(B_144))
      | v2_struct_0(B_144)
      | v2_struct_0(A_143)
      | ~ l1_waybel_0(B_144,A_143)
      | ~ l1_struct_0(A_143) ) ),
    inference(resolution,[status(thm)],[c_22,c_104])).

tff(c_118,plain,(
    ! [A_146,A_147,B_148] :
      ( ~ v1_funct_2(u1_waybel_0(A_146,A_147),u1_struct_0(A_147),u1_struct_0(A_146))
      | ~ v1_funct_1(u1_waybel_0(A_146,A_147))
      | v1_xboole_0(u1_struct_0(A_146))
      | v1_xboole_0(u1_struct_0(A_147))
      | r1_waybel_0(A_146,A_147,k2_relset_1(u1_struct_0(A_147),u1_struct_0(A_146),u1_waybel_0(A_146,A_147)))
      | v2_struct_0(A_146)
      | ~ l1_waybel_0(A_147,A_146)
      | ~ l1_struct_0(A_146)
      | ~ l1_waybel_0(B_148,A_147)
      | ~ l1_struct_0(A_147)
      | v2_struct_0(A_147) ) ),
    inference(resolution,[status(thm)],[c_28,c_108])).

tff(c_122,plain,(
    ! [A_146] :
      ( ~ v1_funct_2(u1_waybel_0(A_146,'#skF_4'),u1_struct_0('#skF_4'),u1_struct_0(A_146))
      | ~ v1_funct_1(u1_waybel_0(A_146,'#skF_4'))
      | v1_xboole_0(u1_struct_0(A_146))
      | v1_xboole_0(u1_struct_0('#skF_4'))
      | r1_waybel_0(A_146,'#skF_4',k2_relset_1(u1_struct_0('#skF_4'),u1_struct_0(A_146),u1_waybel_0(A_146,'#skF_4')))
      | v2_struct_0(A_146)
      | ~ l1_waybel_0('#skF_4',A_146)
      | ~ l1_struct_0(A_146)
      | ~ l1_struct_0('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_36,c_118])).

tff(c_126,plain,(
    ! [A_146] :
      ( ~ v1_funct_2(u1_waybel_0(A_146,'#skF_4'),u1_struct_0('#skF_4'),u1_struct_0(A_146))
      | ~ v1_funct_1(u1_waybel_0(A_146,'#skF_4'))
      | v1_xboole_0(u1_struct_0(A_146))
      | v1_xboole_0(u1_struct_0('#skF_4'))
      | r1_waybel_0(A_146,'#skF_4',k2_relset_1(u1_struct_0('#skF_4'),u1_struct_0(A_146),u1_waybel_0(A_146,'#skF_4')))
      | v2_struct_0(A_146)
      | ~ l1_waybel_0('#skF_4',A_146)
      | ~ l1_struct_0(A_146)
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_122])).

tff(c_127,plain,(
    ! [A_146] :
      ( ~ v1_funct_2(u1_waybel_0(A_146,'#skF_4'),u1_struct_0('#skF_4'),u1_struct_0(A_146))
      | ~ v1_funct_1(u1_waybel_0(A_146,'#skF_4'))
      | v1_xboole_0(u1_struct_0(A_146))
      | v1_xboole_0(u1_struct_0('#skF_4'))
      | r1_waybel_0(A_146,'#skF_4',k2_relset_1(u1_struct_0('#skF_4'),u1_struct_0(A_146),u1_waybel_0(A_146,'#skF_4')))
      | v2_struct_0(A_146)
      | ~ l1_waybel_0('#skF_4',A_146)
      | ~ l1_struct_0(A_146) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_126])).

tff(c_128,plain,(
    v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_127])).

tff(c_4,plain,(
    ! [A_16] :
      ( ~ v1_xboole_0(u1_struct_0(A_16))
      | ~ l1_struct_0(A_16)
      | v2_struct_0(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_131,plain,
    ( ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_128,c_4])).

tff(c_134,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_131])).

tff(c_136,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_134])).

tff(c_138,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_127])).

tff(c_32,plain,(
    ! [A_85] :
      ( l1_waybel_0('#skF_3'(A_85),A_85)
      | ~ l1_struct_0(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_140,plain,(
    ! [A_150,A_151] :
      ( ~ v1_funct_2(u1_waybel_0(A_150,A_151),u1_struct_0(A_151),u1_struct_0(A_150))
      | ~ v1_funct_1(u1_waybel_0(A_150,A_151))
      | v1_xboole_0(u1_struct_0(A_150))
      | v1_xboole_0(u1_struct_0(A_151))
      | r1_waybel_0(A_150,A_151,k2_relset_1(u1_struct_0(A_151),u1_struct_0(A_150),u1_waybel_0(A_150,A_151)))
      | v2_struct_0(A_150)
      | ~ l1_waybel_0(A_151,A_150)
      | ~ l1_struct_0(A_150)
      | v2_struct_0(A_151)
      | ~ l1_struct_0(A_151) ) ),
    inference(resolution,[status(thm)],[c_32,c_118])).

tff(c_34,plain,(
    ~ r1_waybel_0('#skF_4','#skF_5',k2_relset_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),u1_waybel_0('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_143,plain,
    ( ~ v1_funct_2(u1_waybel_0('#skF_4','#skF_5'),u1_struct_0('#skF_5'),u1_struct_0('#skF_4'))
    | ~ v1_funct_1(u1_waybel_0('#skF_4','#skF_5'))
    | v1_xboole_0(u1_struct_0('#skF_4'))
    | v1_xboole_0(u1_struct_0('#skF_5'))
    | v2_struct_0('#skF_4')
    | ~ l1_waybel_0('#skF_5','#skF_4')
    | ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_5')
    | ~ l1_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_140,c_34])).

tff(c_146,plain,
    ( ~ v1_funct_2(u1_waybel_0('#skF_4','#skF_5'),u1_struct_0('#skF_5'),u1_struct_0('#skF_4'))
    | ~ v1_funct_1(u1_waybel_0('#skF_4','#skF_5'))
    | v1_xboole_0(u1_struct_0('#skF_4'))
    | v1_xboole_0(u1_struct_0('#skF_5'))
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_5')
    | ~ l1_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_36,c_143])).

tff(c_147,plain,
    ( ~ v1_funct_2(u1_waybel_0('#skF_4','#skF_5'),u1_struct_0('#skF_5'),u1_struct_0('#skF_4'))
    | ~ v1_funct_1(u1_waybel_0('#skF_4','#skF_5'))
    | v1_xboole_0(u1_struct_0('#skF_5'))
    | ~ l1_struct_0('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_42,c_138,c_146])).

tff(c_148,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_147])).

tff(c_159,plain,(
    ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_6,c_148])).

tff(c_163,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_159])).

tff(c_165,plain,(
    l1_struct_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_147])).

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

tff(c_164,plain,
    ( ~ v1_funct_1(u1_waybel_0('#skF_4','#skF_5'))
    | ~ v1_funct_2(u1_waybel_0('#skF_4','#skF_5'),u1_struct_0('#skF_5'),u1_struct_0('#skF_4'))
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_147])).

tff(c_166,plain,(
    ~ v1_funct_2(u1_waybel_0('#skF_4','#skF_5'),u1_struct_0('#skF_5'),u1_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_164])).

tff(c_169,plain,
    ( ~ l1_waybel_0('#skF_5','#skF_4')
    | ~ l1_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_24,c_166])).

tff(c_173,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_36,c_169])).

tff(c_174,plain,
    ( ~ v1_funct_1(u1_waybel_0('#skF_4','#skF_5'))
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_164])).

tff(c_176,plain,(
    ~ v1_funct_1(u1_waybel_0('#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_174])).

tff(c_179,plain,
    ( ~ l1_waybel_0('#skF_5','#skF_4')
    | ~ l1_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_26,c_176])).

tff(c_183,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_36,c_179])).

tff(c_184,plain,(
    v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_174])).

tff(c_188,plain,
    ( ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_184,c_4])).

tff(c_191,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_165,c_188])).

tff(c_193,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_191])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:40:02 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.58/1.32  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.58/1.33  
% 2.58/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.58/1.33  %$ v1_funct_2 > r1_waybel_0 > r1_orders_2 > v6_waybel_0 > r2_hidden > m1_subset_1 > l1_waybel_0 > v2_struct_0 > v1_xboole_0 > v1_funct_1 > l1_struct_0 > l1_orders_2 > k3_funct_2 > k2_waybel_0 > k2_relset_1 > u1_waybel_0 > k4_yellow_6 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 2.58/1.33  
% 2.58/1.33  %Foreground sorts:
% 2.58/1.33  
% 2.58/1.33  
% 2.58/1.33  %Background operators:
% 2.58/1.33  
% 2.58/1.33  
% 2.58/1.33  %Foreground operators:
% 2.58/1.33  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.58/1.33  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.58/1.33  tff(k4_yellow_6, type, k4_yellow_6: ($i * $i) > $i).
% 2.58/1.33  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.58/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.58/1.33  tff(v6_waybel_0, type, v6_waybel_0: ($i * $i) > $o).
% 2.58/1.33  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.58/1.33  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 2.58/1.33  tff(k2_waybel_0, type, k2_waybel_0: ($i * $i * $i) > $i).
% 2.58/1.33  tff('#skF_5', type, '#skF_5': $i).
% 2.58/1.33  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.58/1.33  tff(r1_waybel_0, type, r1_waybel_0: ($i * $i * $i) > $o).
% 2.58/1.33  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.58/1.33  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.58/1.33  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.58/1.33  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.58/1.33  tff(u1_waybel_0, type, u1_waybel_0: ($i * $i) > $i).
% 2.58/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.58/1.33  tff(l1_waybel_0, type, l1_waybel_0: ($i * $i) > $o).
% 2.58/1.33  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.58/1.33  tff('#skF_4', type, '#skF_4': $i).
% 2.58/1.33  tff('#skF_3', type, '#skF_3': $i > $i).
% 2.58/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.58/1.33  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 2.58/1.33  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.58/1.33  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.58/1.33  tff(k3_funct_2, type, k3_funct_2: ($i * $i * $i * $i) > $i).
% 2.58/1.33  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.58/1.33  
% 2.58/1.35  tff(f_143, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((~v2_struct_0(B) & l1_waybel_0(B, A)) => r1_waybel_0(A, B, k2_relset_1(u1_struct_0(B), u1_struct_0(A), u1_waybel_0(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_waybel_9)).
% 2.58/1.35  tff(f_103, axiom, (![A]: (l1_struct_0(A) => (![B]: (l1_waybel_0(B, A) => l1_orders_2(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_waybel_0)).
% 2.58/1.35  tff(f_56, axiom, (![A]: (l1_orders_2(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 2.58/1.35  tff(f_122, axiom, (![A, B]: (((~v2_struct_0(A) & l1_struct_0(A)) & l1_waybel_0(B, A)) => m1_subset_1(k4_yellow_6(A, B), u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_yellow_6)).
% 2.58/1.35  tff(f_113, axiom, (![A, B]: ((l1_struct_0(A) & l1_waybel_0(B, A)) => ((v1_funct_1(u1_waybel_0(A, B)) & v1_funct_2(u1_waybel_0(A, B), u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(u1_waybel_0(A, B), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_u1_waybel_0)).
% 2.58/1.35  tff(f_80, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((~v2_struct_0(B) & l1_waybel_0(B, A)) => (![C]: (r1_waybel_0(A, B, C) <=> (?[D]: (m1_subset_1(D, u1_struct_0(B)) & (![E]: (m1_subset_1(E, u1_struct_0(B)) => (r1_orders_2(B, D, E) => r2_hidden(k2_waybel_0(A, B, E), C)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d11_waybel_0)).
% 2.58/1.35  tff(f_96, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((~v2_struct_0(B) & l1_waybel_0(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(B)) => (k2_waybel_0(A, B, C) = k3_funct_2(u1_struct_0(B), u1_struct_0(A), u1_waybel_0(A, B), C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_waybel_0)).
% 2.58/1.35  tff(f_44, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, A) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_hidden(k3_funct_2(A, B, D, C), k2_relset_1(A, B, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t189_funct_2)).
% 2.58/1.35  tff(f_52, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 2.58/1.35  tff(f_129, axiom, (![A]: (l1_struct_0(A) => (?[B]: (l1_waybel_0(B, A) & v6_waybel_0(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc4_waybel_0)).
% 2.58/1.35  tff(c_38, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_143])).
% 2.58/1.35  tff(c_40, plain, (l1_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_143])).
% 2.58/1.35  tff(c_36, plain, (l1_waybel_0('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_143])).
% 2.58/1.35  tff(c_46, plain, (![B_91, A_92]: (l1_orders_2(B_91) | ~l1_waybel_0(B_91, A_92) | ~l1_struct_0(A_92))), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.58/1.35  tff(c_52, plain, (l1_orders_2('#skF_5') | ~l1_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_36, c_46])).
% 2.58/1.35  tff(c_56, plain, (l1_orders_2('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_52])).
% 2.58/1.35  tff(c_6, plain, (![A_17]: (l1_struct_0(A_17) | ~l1_orders_2(A_17))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.58/1.35  tff(c_42, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_143])).
% 2.58/1.35  tff(c_28, plain, (![A_83, B_84]: (m1_subset_1(k4_yellow_6(A_83, B_84), u1_struct_0(A_83)) | ~l1_waybel_0(B_84, A_83) | ~l1_struct_0(A_83) | v2_struct_0(A_83))), inference(cnfTransformation, [status(thm)], [f_122])).
% 2.58/1.35  tff(c_22, plain, (![A_81, B_82]: (m1_subset_1(u1_waybel_0(A_81, B_82), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_82), u1_struct_0(A_81)))) | ~l1_waybel_0(B_82, A_81) | ~l1_struct_0(A_81))), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.58/1.35  tff(c_16, plain, (![A_18, B_46, C_60, D_67]: (m1_subset_1('#skF_1'(A_18, B_46, C_60, D_67), u1_struct_0(B_46)) | r1_waybel_0(A_18, B_46, C_60) | ~m1_subset_1(D_67, u1_struct_0(B_46)) | ~l1_waybel_0(B_46, A_18) | v2_struct_0(B_46) | ~l1_struct_0(A_18) | v2_struct_0(A_18))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.58/1.35  tff(c_18, plain, (![B_75, A_71, C_77]: (k3_funct_2(u1_struct_0(B_75), u1_struct_0(A_71), u1_waybel_0(A_71, B_75), C_77)=k2_waybel_0(A_71, B_75, C_77) | ~m1_subset_1(C_77, u1_struct_0(B_75)) | ~l1_waybel_0(B_75, A_71) | v2_struct_0(B_75) | ~l1_struct_0(A_71) | v2_struct_0(A_71))), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.58/1.35  tff(c_76, plain, (![A_121, B_122, D_123, C_124]: (r2_hidden(k3_funct_2(A_121, B_122, D_123, C_124), k2_relset_1(A_121, B_122, D_123)) | ~m1_subset_1(D_123, k1_zfmisc_1(k2_zfmisc_1(A_121, B_122))) | ~v1_funct_2(D_123, A_121, B_122) | ~v1_funct_1(D_123) | ~m1_subset_1(C_124, A_121) | v1_xboole_0(B_122) | v1_xboole_0(A_121))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.58/1.35  tff(c_92, plain, (![A_134, B_135, C_136]: (r2_hidden(k2_waybel_0(A_134, B_135, C_136), k2_relset_1(u1_struct_0(B_135), u1_struct_0(A_134), u1_waybel_0(A_134, B_135))) | ~m1_subset_1(u1_waybel_0(A_134, B_135), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_135), u1_struct_0(A_134)))) | ~v1_funct_2(u1_waybel_0(A_134, B_135), u1_struct_0(B_135), u1_struct_0(A_134)) | ~v1_funct_1(u1_waybel_0(A_134, B_135)) | ~m1_subset_1(C_136, u1_struct_0(B_135)) | v1_xboole_0(u1_struct_0(A_134)) | v1_xboole_0(u1_struct_0(B_135)) | ~m1_subset_1(C_136, u1_struct_0(B_135)) | ~l1_waybel_0(B_135, A_134) | v2_struct_0(B_135) | ~l1_struct_0(A_134) | v2_struct_0(A_134))), inference(superposition, [status(thm), theory('equality')], [c_18, c_76])).
% 2.58/1.35  tff(c_12, plain, (![A_18, B_46, C_60, D_67]: (~r2_hidden(k2_waybel_0(A_18, B_46, '#skF_1'(A_18, B_46, C_60, D_67)), C_60) | r1_waybel_0(A_18, B_46, C_60) | ~m1_subset_1(D_67, u1_struct_0(B_46)) | ~l1_waybel_0(B_46, A_18) | v2_struct_0(B_46) | ~l1_struct_0(A_18) | v2_struct_0(A_18))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.58/1.35  tff(c_98, plain, (![A_137, B_138, D_139]: (r1_waybel_0(A_137, B_138, k2_relset_1(u1_struct_0(B_138), u1_struct_0(A_137), u1_waybel_0(A_137, B_138))) | ~m1_subset_1(D_139, u1_struct_0(B_138)) | ~m1_subset_1(u1_waybel_0(A_137, B_138), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_138), u1_struct_0(A_137)))) | ~v1_funct_2(u1_waybel_0(A_137, B_138), u1_struct_0(B_138), u1_struct_0(A_137)) | ~v1_funct_1(u1_waybel_0(A_137, B_138)) | v1_xboole_0(u1_struct_0(A_137)) | v1_xboole_0(u1_struct_0(B_138)) | ~m1_subset_1('#skF_1'(A_137, B_138, k2_relset_1(u1_struct_0(B_138), u1_struct_0(A_137), u1_waybel_0(A_137, B_138)), D_139), u1_struct_0(B_138)) | ~l1_waybel_0(B_138, A_137) | v2_struct_0(B_138) | ~l1_struct_0(A_137) | v2_struct_0(A_137))), inference(resolution, [status(thm)], [c_92, c_12])).
% 2.58/1.35  tff(c_104, plain, (![A_140, B_141, D_142]: (~m1_subset_1(u1_waybel_0(A_140, B_141), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_141), u1_struct_0(A_140)))) | ~v1_funct_2(u1_waybel_0(A_140, B_141), u1_struct_0(B_141), u1_struct_0(A_140)) | ~v1_funct_1(u1_waybel_0(A_140, B_141)) | v1_xboole_0(u1_struct_0(A_140)) | v1_xboole_0(u1_struct_0(B_141)) | r1_waybel_0(A_140, B_141, k2_relset_1(u1_struct_0(B_141), u1_struct_0(A_140), u1_waybel_0(A_140, B_141))) | ~m1_subset_1(D_142, u1_struct_0(B_141)) | ~l1_waybel_0(B_141, A_140) | v2_struct_0(B_141) | ~l1_struct_0(A_140) | v2_struct_0(A_140))), inference(resolution, [status(thm)], [c_16, c_98])).
% 2.58/1.35  tff(c_108, plain, (![A_143, B_144, D_145]: (~v1_funct_2(u1_waybel_0(A_143, B_144), u1_struct_0(B_144), u1_struct_0(A_143)) | ~v1_funct_1(u1_waybel_0(A_143, B_144)) | v1_xboole_0(u1_struct_0(A_143)) | v1_xboole_0(u1_struct_0(B_144)) | r1_waybel_0(A_143, B_144, k2_relset_1(u1_struct_0(B_144), u1_struct_0(A_143), u1_waybel_0(A_143, B_144))) | ~m1_subset_1(D_145, u1_struct_0(B_144)) | v2_struct_0(B_144) | v2_struct_0(A_143) | ~l1_waybel_0(B_144, A_143) | ~l1_struct_0(A_143))), inference(resolution, [status(thm)], [c_22, c_104])).
% 2.58/1.35  tff(c_118, plain, (![A_146, A_147, B_148]: (~v1_funct_2(u1_waybel_0(A_146, A_147), u1_struct_0(A_147), u1_struct_0(A_146)) | ~v1_funct_1(u1_waybel_0(A_146, A_147)) | v1_xboole_0(u1_struct_0(A_146)) | v1_xboole_0(u1_struct_0(A_147)) | r1_waybel_0(A_146, A_147, k2_relset_1(u1_struct_0(A_147), u1_struct_0(A_146), u1_waybel_0(A_146, A_147))) | v2_struct_0(A_146) | ~l1_waybel_0(A_147, A_146) | ~l1_struct_0(A_146) | ~l1_waybel_0(B_148, A_147) | ~l1_struct_0(A_147) | v2_struct_0(A_147))), inference(resolution, [status(thm)], [c_28, c_108])).
% 2.58/1.35  tff(c_122, plain, (![A_146]: (~v1_funct_2(u1_waybel_0(A_146, '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0(A_146)) | ~v1_funct_1(u1_waybel_0(A_146, '#skF_4')) | v1_xboole_0(u1_struct_0(A_146)) | v1_xboole_0(u1_struct_0('#skF_4')) | r1_waybel_0(A_146, '#skF_4', k2_relset_1(u1_struct_0('#skF_4'), u1_struct_0(A_146), u1_waybel_0(A_146, '#skF_4'))) | v2_struct_0(A_146) | ~l1_waybel_0('#skF_4', A_146) | ~l1_struct_0(A_146) | ~l1_struct_0('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_36, c_118])).
% 2.58/1.35  tff(c_126, plain, (![A_146]: (~v1_funct_2(u1_waybel_0(A_146, '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0(A_146)) | ~v1_funct_1(u1_waybel_0(A_146, '#skF_4')) | v1_xboole_0(u1_struct_0(A_146)) | v1_xboole_0(u1_struct_0('#skF_4')) | r1_waybel_0(A_146, '#skF_4', k2_relset_1(u1_struct_0('#skF_4'), u1_struct_0(A_146), u1_waybel_0(A_146, '#skF_4'))) | v2_struct_0(A_146) | ~l1_waybel_0('#skF_4', A_146) | ~l1_struct_0(A_146) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_122])).
% 2.58/1.35  tff(c_127, plain, (![A_146]: (~v1_funct_2(u1_waybel_0(A_146, '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0(A_146)) | ~v1_funct_1(u1_waybel_0(A_146, '#skF_4')) | v1_xboole_0(u1_struct_0(A_146)) | v1_xboole_0(u1_struct_0('#skF_4')) | r1_waybel_0(A_146, '#skF_4', k2_relset_1(u1_struct_0('#skF_4'), u1_struct_0(A_146), u1_waybel_0(A_146, '#skF_4'))) | v2_struct_0(A_146) | ~l1_waybel_0('#skF_4', A_146) | ~l1_struct_0(A_146))), inference(negUnitSimplification, [status(thm)], [c_42, c_126])).
% 2.58/1.35  tff(c_128, plain, (v1_xboole_0(u1_struct_0('#skF_4'))), inference(splitLeft, [status(thm)], [c_127])).
% 2.58/1.35  tff(c_4, plain, (![A_16]: (~v1_xboole_0(u1_struct_0(A_16)) | ~l1_struct_0(A_16) | v2_struct_0(A_16))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.58/1.35  tff(c_131, plain, (~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_128, c_4])).
% 2.58/1.35  tff(c_134, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_131])).
% 2.58/1.35  tff(c_136, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_134])).
% 2.58/1.35  tff(c_138, plain, (~v1_xboole_0(u1_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_127])).
% 2.58/1.35  tff(c_32, plain, (![A_85]: (l1_waybel_0('#skF_3'(A_85), A_85) | ~l1_struct_0(A_85))), inference(cnfTransformation, [status(thm)], [f_129])).
% 2.58/1.35  tff(c_140, plain, (![A_150, A_151]: (~v1_funct_2(u1_waybel_0(A_150, A_151), u1_struct_0(A_151), u1_struct_0(A_150)) | ~v1_funct_1(u1_waybel_0(A_150, A_151)) | v1_xboole_0(u1_struct_0(A_150)) | v1_xboole_0(u1_struct_0(A_151)) | r1_waybel_0(A_150, A_151, k2_relset_1(u1_struct_0(A_151), u1_struct_0(A_150), u1_waybel_0(A_150, A_151))) | v2_struct_0(A_150) | ~l1_waybel_0(A_151, A_150) | ~l1_struct_0(A_150) | v2_struct_0(A_151) | ~l1_struct_0(A_151))), inference(resolution, [status(thm)], [c_32, c_118])).
% 2.58/1.35  tff(c_34, plain, (~r1_waybel_0('#skF_4', '#skF_5', k2_relset_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'), u1_waybel_0('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_143])).
% 2.58/1.35  tff(c_143, plain, (~v1_funct_2(u1_waybel_0('#skF_4', '#skF_5'), u1_struct_0('#skF_5'), u1_struct_0('#skF_4')) | ~v1_funct_1(u1_waybel_0('#skF_4', '#skF_5')) | v1_xboole_0(u1_struct_0('#skF_4')) | v1_xboole_0(u1_struct_0('#skF_5')) | v2_struct_0('#skF_4') | ~l1_waybel_0('#skF_5', '#skF_4') | ~l1_struct_0('#skF_4') | v2_struct_0('#skF_5') | ~l1_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_140, c_34])).
% 2.58/1.35  tff(c_146, plain, (~v1_funct_2(u1_waybel_0('#skF_4', '#skF_5'), u1_struct_0('#skF_5'), u1_struct_0('#skF_4')) | ~v1_funct_1(u1_waybel_0('#skF_4', '#skF_5')) | v1_xboole_0(u1_struct_0('#skF_4')) | v1_xboole_0(u1_struct_0('#skF_5')) | v2_struct_0('#skF_4') | v2_struct_0('#skF_5') | ~l1_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_36, c_143])).
% 2.58/1.35  tff(c_147, plain, (~v1_funct_2(u1_waybel_0('#skF_4', '#skF_5'), u1_struct_0('#skF_5'), u1_struct_0('#skF_4')) | ~v1_funct_1(u1_waybel_0('#skF_4', '#skF_5')) | v1_xboole_0(u1_struct_0('#skF_5')) | ~l1_struct_0('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_38, c_42, c_138, c_146])).
% 2.58/1.35  tff(c_148, plain, (~l1_struct_0('#skF_5')), inference(splitLeft, [status(thm)], [c_147])).
% 2.58/1.35  tff(c_159, plain, (~l1_orders_2('#skF_5')), inference(resolution, [status(thm)], [c_6, c_148])).
% 2.58/1.35  tff(c_163, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_159])).
% 2.58/1.35  tff(c_165, plain, (l1_struct_0('#skF_5')), inference(splitRight, [status(thm)], [c_147])).
% 2.58/1.35  tff(c_26, plain, (![A_81, B_82]: (v1_funct_1(u1_waybel_0(A_81, B_82)) | ~l1_waybel_0(B_82, A_81) | ~l1_struct_0(A_81))), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.58/1.35  tff(c_24, plain, (![A_81, B_82]: (v1_funct_2(u1_waybel_0(A_81, B_82), u1_struct_0(B_82), u1_struct_0(A_81)) | ~l1_waybel_0(B_82, A_81) | ~l1_struct_0(A_81))), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.58/1.35  tff(c_164, plain, (~v1_funct_1(u1_waybel_0('#skF_4', '#skF_5')) | ~v1_funct_2(u1_waybel_0('#skF_4', '#skF_5'), u1_struct_0('#skF_5'), u1_struct_0('#skF_4')) | v1_xboole_0(u1_struct_0('#skF_5'))), inference(splitRight, [status(thm)], [c_147])).
% 2.58/1.35  tff(c_166, plain, (~v1_funct_2(u1_waybel_0('#skF_4', '#skF_5'), u1_struct_0('#skF_5'), u1_struct_0('#skF_4'))), inference(splitLeft, [status(thm)], [c_164])).
% 2.58/1.35  tff(c_169, plain, (~l1_waybel_0('#skF_5', '#skF_4') | ~l1_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_24, c_166])).
% 2.58/1.35  tff(c_173, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_36, c_169])).
% 2.58/1.35  tff(c_174, plain, (~v1_funct_1(u1_waybel_0('#skF_4', '#skF_5')) | v1_xboole_0(u1_struct_0('#skF_5'))), inference(splitRight, [status(thm)], [c_164])).
% 2.58/1.35  tff(c_176, plain, (~v1_funct_1(u1_waybel_0('#skF_4', '#skF_5'))), inference(splitLeft, [status(thm)], [c_174])).
% 2.58/1.35  tff(c_179, plain, (~l1_waybel_0('#skF_5', '#skF_4') | ~l1_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_26, c_176])).
% 2.58/1.35  tff(c_183, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_36, c_179])).
% 2.58/1.35  tff(c_184, plain, (v1_xboole_0(u1_struct_0('#skF_5'))), inference(splitRight, [status(thm)], [c_174])).
% 2.58/1.35  tff(c_188, plain, (~l1_struct_0('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_184, c_4])).
% 2.58/1.35  tff(c_191, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_165, c_188])).
% 2.58/1.35  tff(c_193, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_191])).
% 2.58/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.58/1.35  
% 2.58/1.35  Inference rules
% 2.58/1.35  ----------------------
% 2.58/1.35  #Ref     : 0
% 2.58/1.35  #Sup     : 23
% 2.58/1.35  #Fact    : 0
% 2.58/1.35  #Define  : 0
% 2.58/1.35  #Split   : 4
% 2.58/1.35  #Chain   : 0
% 2.58/1.35  #Close   : 0
% 2.58/1.35  
% 2.58/1.35  Ordering : KBO
% 2.58/1.35  
% 2.58/1.35  Simplification rules
% 2.58/1.35  ----------------------
% 2.58/1.35  #Subsume      : 6
% 2.58/1.35  #Demod        : 11
% 2.58/1.35  #Tautology    : 3
% 2.58/1.35  #SimpNegUnit  : 5
% 2.58/1.35  #BackRed      : 0
% 2.58/1.35  
% 2.58/1.35  #Partial instantiations: 0
% 2.58/1.35  #Strategies tried      : 1
% 2.58/1.35  
% 2.58/1.35  Timing (in seconds)
% 2.58/1.35  ----------------------
% 2.58/1.35  Preprocessing        : 0.34
% 2.58/1.35  Parsing              : 0.18
% 2.58/1.35  CNF conversion       : 0.03
% 2.58/1.35  Main loop            : 0.25
% 2.58/1.35  Inferencing          : 0.11
% 2.58/1.35  Reduction            : 0.06
% 2.58/1.35  Demodulation         : 0.04
% 2.58/1.35  BG Simplification    : 0.02
% 2.58/1.35  Subsumption          : 0.05
% 2.58/1.35  Abstraction          : 0.01
% 2.58/1.35  MUC search           : 0.00
% 2.58/1.35  Cooper               : 0.00
% 2.58/1.35  Total                : 0.62
% 2.58/1.35  Index Insertion      : 0.00
% 2.58/1.36  Index Deletion       : 0.00
% 2.58/1.36  Index Matching       : 0.00
% 2.58/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
