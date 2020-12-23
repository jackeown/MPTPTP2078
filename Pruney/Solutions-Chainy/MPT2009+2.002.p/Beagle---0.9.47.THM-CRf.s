%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:07 EST 2020

% Result     : Theorem 2.18s
% Output     : CNFRefutation 2.58s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 198 expanded)
%              Number of leaves         :   35 (  85 expanded)
%              Depth                    :   16
%              Number of atoms          :  190 ( 807 expanded)
%              Number of equality atoms :    2 (   8 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r1_waybel_0 > r1_orders_2 > r2_hidden > m1_subset_1 > l1_waybel_0 > v2_struct_0 > v1_xboole_0 > v1_funct_1 > l1_struct_0 > l1_orders_2 > k3_funct_2 > k2_waybel_0 > k2_relset_1 > u1_waybel_0 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

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
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

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
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k3_funct_2,type,(
    k3_funct_2: ( $i * $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_128,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & l1_struct_0(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & l1_waybel_0(B,A) )
           => r1_waybel_0(A,B,k2_relset_1(u1_struct_0(B),u1_struct_0(A),u1_waybel_0(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_waybel_9)).

tff(f_98,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ! [B] :
          ( l1_waybel_0(B,A)
         => l1_orders_2(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_waybel_0)).

tff(f_51,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_108,axiom,(
    ! [A,B] :
      ( ( l1_struct_0(A)
        & l1_waybel_0(B,A) )
     => ( v1_funct_1(u1_waybel_0(A,B))
        & v1_funct_2(u1_waybel_0(A,B),u1_struct_0(B),u1_struct_0(A))
        & m1_subset_1(u1_waybel_0(A,B),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B),u1_struct_0(A)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_waybel_0)).

tff(f_28,axiom,(
    ! [A] :
    ? [B] : m1_subset_1(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).

tff(f_75,axiom,(
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

tff(f_91,axiom,(
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

tff(f_47,axiom,(
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

tff(f_114,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ( v2_struct_0(A)
      <=> v1_xboole_0(u1_struct_0(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_struct_0)).

tff(c_40,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_38,plain,(
    l1_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_34,plain,(
    l1_waybel_0('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_49,plain,(
    ! [B_90,A_91] :
      ( l1_orders_2(B_90)
      | ~ l1_waybel_0(B_90,A_91)
      | ~ l1_struct_0(A_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_52,plain,
    ( l1_orders_2('#skF_5')
    | ~ l1_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_34,c_49])).

tff(c_55,plain,(
    l1_orders_2('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_52])).

tff(c_6,plain,(
    ! [A_18] :
      ( l1_struct_0(A_18)
      | ~ l1_orders_2(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_36,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_24,plain,(
    ! [A_82,B_83] :
      ( v1_funct_2(u1_waybel_0(A_82,B_83),u1_struct_0(B_83),u1_struct_0(A_82))
      | ~ l1_waybel_0(B_83,A_82)
      | ~ l1_struct_0(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_26,plain,(
    ! [A_82,B_83] :
      ( v1_funct_1(u1_waybel_0(A_82,B_83))
      | ~ l1_waybel_0(B_83,A_82)
      | ~ l1_struct_0(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_2,plain,(
    ! [A_1] : m1_subset_1('#skF_1'(A_1),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_22,plain,(
    ! [A_82,B_83] :
      ( m1_subset_1(u1_waybel_0(A_82,B_83),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_83),u1_struct_0(A_82))))
      | ~ l1_waybel_0(B_83,A_82)
      | ~ l1_struct_0(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_16,plain,(
    ! [A_19,B_47,C_61,D_68] :
      ( m1_subset_1('#skF_2'(A_19,B_47,C_61,D_68),u1_struct_0(B_47))
      | r1_waybel_0(A_19,B_47,C_61)
      | ~ m1_subset_1(D_68,u1_struct_0(B_47))
      | ~ l1_waybel_0(B_47,A_19)
      | v2_struct_0(B_47)
      | ~ l1_struct_0(A_19)
      | v2_struct_0(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_18,plain,(
    ! [B_76,A_72,C_78] :
      ( k3_funct_2(u1_struct_0(B_76),u1_struct_0(A_72),u1_waybel_0(A_72,B_76),C_78) = k2_waybel_0(A_72,B_76,C_78)
      | ~ m1_subset_1(C_78,u1_struct_0(B_76))
      | ~ l1_waybel_0(B_76,A_72)
      | v2_struct_0(B_76)
      | ~ l1_struct_0(A_72)
      | v2_struct_0(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_72,plain,(
    ! [A_116,B_117,D_118,C_119] :
      ( r2_hidden(k3_funct_2(A_116,B_117,D_118,C_119),k2_relset_1(A_116,B_117,D_118))
      | ~ m1_subset_1(D_118,k1_zfmisc_1(k2_zfmisc_1(A_116,B_117)))
      | ~ v1_funct_2(D_118,A_116,B_117)
      | ~ v1_funct_1(D_118)
      | ~ m1_subset_1(C_119,A_116)
      | v1_xboole_0(B_117)
      | v1_xboole_0(A_116) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_88,plain,(
    ! [A_129,B_130,C_131] :
      ( r2_hidden(k2_waybel_0(A_129,B_130,C_131),k2_relset_1(u1_struct_0(B_130),u1_struct_0(A_129),u1_waybel_0(A_129,B_130)))
      | ~ m1_subset_1(u1_waybel_0(A_129,B_130),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_130),u1_struct_0(A_129))))
      | ~ v1_funct_2(u1_waybel_0(A_129,B_130),u1_struct_0(B_130),u1_struct_0(A_129))
      | ~ v1_funct_1(u1_waybel_0(A_129,B_130))
      | ~ m1_subset_1(C_131,u1_struct_0(B_130))
      | v1_xboole_0(u1_struct_0(A_129))
      | v1_xboole_0(u1_struct_0(B_130))
      | ~ m1_subset_1(C_131,u1_struct_0(B_130))
      | ~ l1_waybel_0(B_130,A_129)
      | v2_struct_0(B_130)
      | ~ l1_struct_0(A_129)
      | v2_struct_0(A_129) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_72])).

tff(c_12,plain,(
    ! [A_19,B_47,C_61,D_68] :
      ( ~ r2_hidden(k2_waybel_0(A_19,B_47,'#skF_2'(A_19,B_47,C_61,D_68)),C_61)
      | r1_waybel_0(A_19,B_47,C_61)
      | ~ m1_subset_1(D_68,u1_struct_0(B_47))
      | ~ l1_waybel_0(B_47,A_19)
      | v2_struct_0(B_47)
      | ~ l1_struct_0(A_19)
      | v2_struct_0(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_94,plain,(
    ! [A_132,B_133,D_134] :
      ( r1_waybel_0(A_132,B_133,k2_relset_1(u1_struct_0(B_133),u1_struct_0(A_132),u1_waybel_0(A_132,B_133)))
      | ~ m1_subset_1(D_134,u1_struct_0(B_133))
      | ~ m1_subset_1(u1_waybel_0(A_132,B_133),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_133),u1_struct_0(A_132))))
      | ~ v1_funct_2(u1_waybel_0(A_132,B_133),u1_struct_0(B_133),u1_struct_0(A_132))
      | ~ v1_funct_1(u1_waybel_0(A_132,B_133))
      | v1_xboole_0(u1_struct_0(A_132))
      | v1_xboole_0(u1_struct_0(B_133))
      | ~ m1_subset_1('#skF_2'(A_132,B_133,k2_relset_1(u1_struct_0(B_133),u1_struct_0(A_132),u1_waybel_0(A_132,B_133)),D_134),u1_struct_0(B_133))
      | ~ l1_waybel_0(B_133,A_132)
      | v2_struct_0(B_133)
      | ~ l1_struct_0(A_132)
      | v2_struct_0(A_132) ) ),
    inference(resolution,[status(thm)],[c_88,c_12])).

tff(c_100,plain,(
    ! [A_135,B_136,D_137] :
      ( ~ m1_subset_1(u1_waybel_0(A_135,B_136),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_136),u1_struct_0(A_135))))
      | ~ v1_funct_2(u1_waybel_0(A_135,B_136),u1_struct_0(B_136),u1_struct_0(A_135))
      | ~ v1_funct_1(u1_waybel_0(A_135,B_136))
      | v1_xboole_0(u1_struct_0(A_135))
      | v1_xboole_0(u1_struct_0(B_136))
      | r1_waybel_0(A_135,B_136,k2_relset_1(u1_struct_0(B_136),u1_struct_0(A_135),u1_waybel_0(A_135,B_136)))
      | ~ m1_subset_1(D_137,u1_struct_0(B_136))
      | ~ l1_waybel_0(B_136,A_135)
      | v2_struct_0(B_136)
      | ~ l1_struct_0(A_135)
      | v2_struct_0(A_135) ) ),
    inference(resolution,[status(thm)],[c_16,c_94])).

tff(c_104,plain,(
    ! [A_138,B_139,D_140] :
      ( ~ v1_funct_2(u1_waybel_0(A_138,B_139),u1_struct_0(B_139),u1_struct_0(A_138))
      | ~ v1_funct_1(u1_waybel_0(A_138,B_139))
      | v1_xboole_0(u1_struct_0(A_138))
      | v1_xboole_0(u1_struct_0(B_139))
      | r1_waybel_0(A_138,B_139,k2_relset_1(u1_struct_0(B_139),u1_struct_0(A_138),u1_waybel_0(A_138,B_139)))
      | ~ m1_subset_1(D_140,u1_struct_0(B_139))
      | v2_struct_0(B_139)
      | v2_struct_0(A_138)
      | ~ l1_waybel_0(B_139,A_138)
      | ~ l1_struct_0(A_138) ) ),
    inference(resolution,[status(thm)],[c_22,c_100])).

tff(c_114,plain,(
    ! [A_141,B_142] :
      ( ~ v1_funct_2(u1_waybel_0(A_141,B_142),u1_struct_0(B_142),u1_struct_0(A_141))
      | ~ v1_funct_1(u1_waybel_0(A_141,B_142))
      | v1_xboole_0(u1_struct_0(A_141))
      | v1_xboole_0(u1_struct_0(B_142))
      | r1_waybel_0(A_141,B_142,k2_relset_1(u1_struct_0(B_142),u1_struct_0(A_141),u1_waybel_0(A_141,B_142)))
      | v2_struct_0(B_142)
      | v2_struct_0(A_141)
      | ~ l1_waybel_0(B_142,A_141)
      | ~ l1_struct_0(A_141) ) ),
    inference(resolution,[status(thm)],[c_2,c_104])).

tff(c_32,plain,(
    ~ r1_waybel_0('#skF_4','#skF_5',k2_relset_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),u1_waybel_0('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_117,plain,
    ( ~ v1_funct_2(u1_waybel_0('#skF_4','#skF_5'),u1_struct_0('#skF_5'),u1_struct_0('#skF_4'))
    | ~ v1_funct_1(u1_waybel_0('#skF_4','#skF_5'))
    | v1_xboole_0(u1_struct_0('#skF_4'))
    | v1_xboole_0(u1_struct_0('#skF_5'))
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_4')
    | ~ l1_waybel_0('#skF_5','#skF_4')
    | ~ l1_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_114,c_32])).

tff(c_120,plain,
    ( ~ v1_funct_2(u1_waybel_0('#skF_4','#skF_5'),u1_struct_0('#skF_5'),u1_struct_0('#skF_4'))
    | ~ v1_funct_1(u1_waybel_0('#skF_4','#skF_5'))
    | v1_xboole_0(u1_struct_0('#skF_4'))
    | v1_xboole_0(u1_struct_0('#skF_5'))
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_34,c_117])).

tff(c_121,plain,
    ( ~ v1_funct_2(u1_waybel_0('#skF_4','#skF_5'),u1_struct_0('#skF_5'),u1_struct_0('#skF_4'))
    | ~ v1_funct_1(u1_waybel_0('#skF_4','#skF_5'))
    | v1_xboole_0(u1_struct_0('#skF_4'))
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_36,c_120])).

tff(c_122,plain,(
    ~ v1_funct_1(u1_waybel_0('#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_121])).

tff(c_125,plain,
    ( ~ l1_waybel_0('#skF_5','#skF_4')
    | ~ l1_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_26,c_122])).

tff(c_129,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_34,c_125])).

tff(c_130,plain,
    ( ~ v1_funct_2(u1_waybel_0('#skF_4','#skF_5'),u1_struct_0('#skF_5'),u1_struct_0('#skF_4'))
    | v1_xboole_0(u1_struct_0('#skF_5'))
    | v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_121])).

tff(c_132,plain,(
    ~ v1_funct_2(u1_waybel_0('#skF_4','#skF_5'),u1_struct_0('#skF_5'),u1_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_130])).

tff(c_135,plain,
    ( ~ l1_waybel_0('#skF_5','#skF_4')
    | ~ l1_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_24,c_132])).

tff(c_139,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_34,c_135])).

tff(c_140,plain,
    ( v1_xboole_0(u1_struct_0('#skF_4'))
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_130])).

tff(c_142,plain,(
    v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_140])).

tff(c_28,plain,(
    ! [A_84] :
      ( v2_struct_0(A_84)
      | ~ v1_xboole_0(u1_struct_0(A_84))
      | ~ l1_struct_0(A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_145,plain,
    ( v2_struct_0('#skF_5')
    | ~ l1_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_142,c_28])).

tff(c_148,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_145])).

tff(c_151,plain,(
    ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_6,c_148])).

tff(c_155,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_151])).

tff(c_156,plain,(
    v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_140])).

tff(c_160,plain,
    ( v2_struct_0('#skF_4')
    | ~ l1_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_156,c_28])).

tff(c_163,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_160])).

tff(c_165,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_163])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 20:47:20 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.18/1.32  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.18/1.32  
% 2.18/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.18/1.33  %$ v1_funct_2 > r1_waybel_0 > r1_orders_2 > r2_hidden > m1_subset_1 > l1_waybel_0 > v2_struct_0 > v1_xboole_0 > v1_funct_1 > l1_struct_0 > l1_orders_2 > k3_funct_2 > k2_waybel_0 > k2_relset_1 > u1_waybel_0 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3
% 2.18/1.33  
% 2.18/1.33  %Foreground sorts:
% 2.18/1.33  
% 2.18/1.33  
% 2.18/1.33  %Background operators:
% 2.18/1.33  
% 2.18/1.33  
% 2.18/1.33  %Foreground operators:
% 2.18/1.33  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.18/1.33  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.18/1.33  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.18/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.18/1.33  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.18/1.33  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.18/1.33  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 2.18/1.33  tff(k2_waybel_0, type, k2_waybel_0: ($i * $i * $i) > $i).
% 2.18/1.33  tff('#skF_5', type, '#skF_5': $i).
% 2.18/1.33  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.18/1.33  tff(r1_waybel_0, type, r1_waybel_0: ($i * $i * $i) > $o).
% 2.18/1.33  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.18/1.33  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.18/1.33  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.18/1.33  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.18/1.33  tff(u1_waybel_0, type, u1_waybel_0: ($i * $i) > $i).
% 2.18/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.18/1.33  tff(l1_waybel_0, type, l1_waybel_0: ($i * $i) > $o).
% 2.18/1.33  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.18/1.33  tff('#skF_4', type, '#skF_4': $i).
% 2.18/1.33  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.18/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.18/1.33  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.18/1.33  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.18/1.33  tff(k3_funct_2, type, k3_funct_2: ($i * $i * $i * $i) > $i).
% 2.18/1.33  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.18/1.33  
% 2.58/1.34  tff(f_128, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((~v2_struct_0(B) & l1_waybel_0(B, A)) => r1_waybel_0(A, B, k2_relset_1(u1_struct_0(B), u1_struct_0(A), u1_waybel_0(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_waybel_9)).
% 2.58/1.34  tff(f_98, axiom, (![A]: (l1_struct_0(A) => (![B]: (l1_waybel_0(B, A) => l1_orders_2(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_waybel_0)).
% 2.58/1.34  tff(f_51, axiom, (![A]: (l1_orders_2(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 2.58/1.34  tff(f_108, axiom, (![A, B]: ((l1_struct_0(A) & l1_waybel_0(B, A)) => ((v1_funct_1(u1_waybel_0(A, B)) & v1_funct_2(u1_waybel_0(A, B), u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(u1_waybel_0(A, B), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_u1_waybel_0)).
% 2.58/1.34  tff(f_28, axiom, (![A]: (?[B]: m1_subset_1(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', existence_m1_subset_1)).
% 2.58/1.34  tff(f_75, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((~v2_struct_0(B) & l1_waybel_0(B, A)) => (![C]: (r1_waybel_0(A, B, C) <=> (?[D]: (m1_subset_1(D, u1_struct_0(B)) & (![E]: (m1_subset_1(E, u1_struct_0(B)) => (r1_orders_2(B, D, E) => r2_hidden(k2_waybel_0(A, B, E), C)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d11_waybel_0)).
% 2.58/1.34  tff(f_91, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((~v2_struct_0(B) & l1_waybel_0(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(B)) => (k2_waybel_0(A, B, C) = k3_funct_2(u1_struct_0(B), u1_struct_0(A), u1_waybel_0(A, B), C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_waybel_0)).
% 2.58/1.34  tff(f_47, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, A) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_hidden(k3_funct_2(A, B, D, C), k2_relset_1(A, B, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t189_funct_2)).
% 2.58/1.34  tff(f_114, axiom, (![A]: (l1_struct_0(A) => (v2_struct_0(A) <=> v1_xboole_0(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_struct_0)).
% 2.58/1.34  tff(c_40, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_128])).
% 2.58/1.34  tff(c_38, plain, (l1_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_128])).
% 2.58/1.34  tff(c_34, plain, (l1_waybel_0('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_128])).
% 2.58/1.34  tff(c_49, plain, (![B_90, A_91]: (l1_orders_2(B_90) | ~l1_waybel_0(B_90, A_91) | ~l1_struct_0(A_91))), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.58/1.34  tff(c_52, plain, (l1_orders_2('#skF_5') | ~l1_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_34, c_49])).
% 2.58/1.34  tff(c_55, plain, (l1_orders_2('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_52])).
% 2.58/1.34  tff(c_6, plain, (![A_18]: (l1_struct_0(A_18) | ~l1_orders_2(A_18))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.58/1.34  tff(c_36, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_128])).
% 2.58/1.34  tff(c_24, plain, (![A_82, B_83]: (v1_funct_2(u1_waybel_0(A_82, B_83), u1_struct_0(B_83), u1_struct_0(A_82)) | ~l1_waybel_0(B_83, A_82) | ~l1_struct_0(A_82))), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.58/1.34  tff(c_26, plain, (![A_82, B_83]: (v1_funct_1(u1_waybel_0(A_82, B_83)) | ~l1_waybel_0(B_83, A_82) | ~l1_struct_0(A_82))), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.58/1.34  tff(c_2, plain, (![A_1]: (m1_subset_1('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_28])).
% 2.58/1.34  tff(c_22, plain, (![A_82, B_83]: (m1_subset_1(u1_waybel_0(A_82, B_83), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_83), u1_struct_0(A_82)))) | ~l1_waybel_0(B_83, A_82) | ~l1_struct_0(A_82))), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.58/1.34  tff(c_16, plain, (![A_19, B_47, C_61, D_68]: (m1_subset_1('#skF_2'(A_19, B_47, C_61, D_68), u1_struct_0(B_47)) | r1_waybel_0(A_19, B_47, C_61) | ~m1_subset_1(D_68, u1_struct_0(B_47)) | ~l1_waybel_0(B_47, A_19) | v2_struct_0(B_47) | ~l1_struct_0(A_19) | v2_struct_0(A_19))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.58/1.34  tff(c_18, plain, (![B_76, A_72, C_78]: (k3_funct_2(u1_struct_0(B_76), u1_struct_0(A_72), u1_waybel_0(A_72, B_76), C_78)=k2_waybel_0(A_72, B_76, C_78) | ~m1_subset_1(C_78, u1_struct_0(B_76)) | ~l1_waybel_0(B_76, A_72) | v2_struct_0(B_76) | ~l1_struct_0(A_72) | v2_struct_0(A_72))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.58/1.34  tff(c_72, plain, (![A_116, B_117, D_118, C_119]: (r2_hidden(k3_funct_2(A_116, B_117, D_118, C_119), k2_relset_1(A_116, B_117, D_118)) | ~m1_subset_1(D_118, k1_zfmisc_1(k2_zfmisc_1(A_116, B_117))) | ~v1_funct_2(D_118, A_116, B_117) | ~v1_funct_1(D_118) | ~m1_subset_1(C_119, A_116) | v1_xboole_0(B_117) | v1_xboole_0(A_116))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.58/1.34  tff(c_88, plain, (![A_129, B_130, C_131]: (r2_hidden(k2_waybel_0(A_129, B_130, C_131), k2_relset_1(u1_struct_0(B_130), u1_struct_0(A_129), u1_waybel_0(A_129, B_130))) | ~m1_subset_1(u1_waybel_0(A_129, B_130), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_130), u1_struct_0(A_129)))) | ~v1_funct_2(u1_waybel_0(A_129, B_130), u1_struct_0(B_130), u1_struct_0(A_129)) | ~v1_funct_1(u1_waybel_0(A_129, B_130)) | ~m1_subset_1(C_131, u1_struct_0(B_130)) | v1_xboole_0(u1_struct_0(A_129)) | v1_xboole_0(u1_struct_0(B_130)) | ~m1_subset_1(C_131, u1_struct_0(B_130)) | ~l1_waybel_0(B_130, A_129) | v2_struct_0(B_130) | ~l1_struct_0(A_129) | v2_struct_0(A_129))), inference(superposition, [status(thm), theory('equality')], [c_18, c_72])).
% 2.58/1.34  tff(c_12, plain, (![A_19, B_47, C_61, D_68]: (~r2_hidden(k2_waybel_0(A_19, B_47, '#skF_2'(A_19, B_47, C_61, D_68)), C_61) | r1_waybel_0(A_19, B_47, C_61) | ~m1_subset_1(D_68, u1_struct_0(B_47)) | ~l1_waybel_0(B_47, A_19) | v2_struct_0(B_47) | ~l1_struct_0(A_19) | v2_struct_0(A_19))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.58/1.34  tff(c_94, plain, (![A_132, B_133, D_134]: (r1_waybel_0(A_132, B_133, k2_relset_1(u1_struct_0(B_133), u1_struct_0(A_132), u1_waybel_0(A_132, B_133))) | ~m1_subset_1(D_134, u1_struct_0(B_133)) | ~m1_subset_1(u1_waybel_0(A_132, B_133), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_133), u1_struct_0(A_132)))) | ~v1_funct_2(u1_waybel_0(A_132, B_133), u1_struct_0(B_133), u1_struct_0(A_132)) | ~v1_funct_1(u1_waybel_0(A_132, B_133)) | v1_xboole_0(u1_struct_0(A_132)) | v1_xboole_0(u1_struct_0(B_133)) | ~m1_subset_1('#skF_2'(A_132, B_133, k2_relset_1(u1_struct_0(B_133), u1_struct_0(A_132), u1_waybel_0(A_132, B_133)), D_134), u1_struct_0(B_133)) | ~l1_waybel_0(B_133, A_132) | v2_struct_0(B_133) | ~l1_struct_0(A_132) | v2_struct_0(A_132))), inference(resolution, [status(thm)], [c_88, c_12])).
% 2.58/1.34  tff(c_100, plain, (![A_135, B_136, D_137]: (~m1_subset_1(u1_waybel_0(A_135, B_136), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_136), u1_struct_0(A_135)))) | ~v1_funct_2(u1_waybel_0(A_135, B_136), u1_struct_0(B_136), u1_struct_0(A_135)) | ~v1_funct_1(u1_waybel_0(A_135, B_136)) | v1_xboole_0(u1_struct_0(A_135)) | v1_xboole_0(u1_struct_0(B_136)) | r1_waybel_0(A_135, B_136, k2_relset_1(u1_struct_0(B_136), u1_struct_0(A_135), u1_waybel_0(A_135, B_136))) | ~m1_subset_1(D_137, u1_struct_0(B_136)) | ~l1_waybel_0(B_136, A_135) | v2_struct_0(B_136) | ~l1_struct_0(A_135) | v2_struct_0(A_135))), inference(resolution, [status(thm)], [c_16, c_94])).
% 2.58/1.34  tff(c_104, plain, (![A_138, B_139, D_140]: (~v1_funct_2(u1_waybel_0(A_138, B_139), u1_struct_0(B_139), u1_struct_0(A_138)) | ~v1_funct_1(u1_waybel_0(A_138, B_139)) | v1_xboole_0(u1_struct_0(A_138)) | v1_xboole_0(u1_struct_0(B_139)) | r1_waybel_0(A_138, B_139, k2_relset_1(u1_struct_0(B_139), u1_struct_0(A_138), u1_waybel_0(A_138, B_139))) | ~m1_subset_1(D_140, u1_struct_0(B_139)) | v2_struct_0(B_139) | v2_struct_0(A_138) | ~l1_waybel_0(B_139, A_138) | ~l1_struct_0(A_138))), inference(resolution, [status(thm)], [c_22, c_100])).
% 2.58/1.34  tff(c_114, plain, (![A_141, B_142]: (~v1_funct_2(u1_waybel_0(A_141, B_142), u1_struct_0(B_142), u1_struct_0(A_141)) | ~v1_funct_1(u1_waybel_0(A_141, B_142)) | v1_xboole_0(u1_struct_0(A_141)) | v1_xboole_0(u1_struct_0(B_142)) | r1_waybel_0(A_141, B_142, k2_relset_1(u1_struct_0(B_142), u1_struct_0(A_141), u1_waybel_0(A_141, B_142))) | v2_struct_0(B_142) | v2_struct_0(A_141) | ~l1_waybel_0(B_142, A_141) | ~l1_struct_0(A_141))), inference(resolution, [status(thm)], [c_2, c_104])).
% 2.58/1.34  tff(c_32, plain, (~r1_waybel_0('#skF_4', '#skF_5', k2_relset_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'), u1_waybel_0('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_128])).
% 2.58/1.34  tff(c_117, plain, (~v1_funct_2(u1_waybel_0('#skF_4', '#skF_5'), u1_struct_0('#skF_5'), u1_struct_0('#skF_4')) | ~v1_funct_1(u1_waybel_0('#skF_4', '#skF_5')) | v1_xboole_0(u1_struct_0('#skF_4')) | v1_xboole_0(u1_struct_0('#skF_5')) | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | ~l1_waybel_0('#skF_5', '#skF_4') | ~l1_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_114, c_32])).
% 2.58/1.34  tff(c_120, plain, (~v1_funct_2(u1_waybel_0('#skF_4', '#skF_5'), u1_struct_0('#skF_5'), u1_struct_0('#skF_4')) | ~v1_funct_1(u1_waybel_0('#skF_4', '#skF_5')) | v1_xboole_0(u1_struct_0('#skF_4')) | v1_xboole_0(u1_struct_0('#skF_5')) | v2_struct_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_34, c_117])).
% 2.58/1.34  tff(c_121, plain, (~v1_funct_2(u1_waybel_0('#skF_4', '#skF_5'), u1_struct_0('#skF_5'), u1_struct_0('#skF_4')) | ~v1_funct_1(u1_waybel_0('#skF_4', '#skF_5')) | v1_xboole_0(u1_struct_0('#skF_4')) | v1_xboole_0(u1_struct_0('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_40, c_36, c_120])).
% 2.58/1.34  tff(c_122, plain, (~v1_funct_1(u1_waybel_0('#skF_4', '#skF_5'))), inference(splitLeft, [status(thm)], [c_121])).
% 2.58/1.34  tff(c_125, plain, (~l1_waybel_0('#skF_5', '#skF_4') | ~l1_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_26, c_122])).
% 2.58/1.34  tff(c_129, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_34, c_125])).
% 2.58/1.34  tff(c_130, plain, (~v1_funct_2(u1_waybel_0('#skF_4', '#skF_5'), u1_struct_0('#skF_5'), u1_struct_0('#skF_4')) | v1_xboole_0(u1_struct_0('#skF_5')) | v1_xboole_0(u1_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_121])).
% 2.58/1.34  tff(c_132, plain, (~v1_funct_2(u1_waybel_0('#skF_4', '#skF_5'), u1_struct_0('#skF_5'), u1_struct_0('#skF_4'))), inference(splitLeft, [status(thm)], [c_130])).
% 2.58/1.34  tff(c_135, plain, (~l1_waybel_0('#skF_5', '#skF_4') | ~l1_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_24, c_132])).
% 2.58/1.34  tff(c_139, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_34, c_135])).
% 2.58/1.34  tff(c_140, plain, (v1_xboole_0(u1_struct_0('#skF_4')) | v1_xboole_0(u1_struct_0('#skF_5'))), inference(splitRight, [status(thm)], [c_130])).
% 2.58/1.34  tff(c_142, plain, (v1_xboole_0(u1_struct_0('#skF_5'))), inference(splitLeft, [status(thm)], [c_140])).
% 2.58/1.34  tff(c_28, plain, (![A_84]: (v2_struct_0(A_84) | ~v1_xboole_0(u1_struct_0(A_84)) | ~l1_struct_0(A_84))), inference(cnfTransformation, [status(thm)], [f_114])).
% 2.58/1.34  tff(c_145, plain, (v2_struct_0('#skF_5') | ~l1_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_142, c_28])).
% 2.58/1.34  tff(c_148, plain, (~l1_struct_0('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_36, c_145])).
% 2.58/1.34  tff(c_151, plain, (~l1_orders_2('#skF_5')), inference(resolution, [status(thm)], [c_6, c_148])).
% 2.58/1.34  tff(c_155, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_55, c_151])).
% 2.58/1.34  tff(c_156, plain, (v1_xboole_0(u1_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_140])).
% 2.58/1.34  tff(c_160, plain, (v2_struct_0('#skF_4') | ~l1_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_156, c_28])).
% 2.58/1.34  tff(c_163, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_160])).
% 2.58/1.34  tff(c_165, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_163])).
% 2.58/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.58/1.34  
% 2.58/1.34  Inference rules
% 2.58/1.34  ----------------------
% 2.58/1.34  #Ref     : 0
% 2.58/1.34  #Sup     : 19
% 2.58/1.34  #Fact    : 0
% 2.58/1.34  #Define  : 0
% 2.58/1.34  #Split   : 3
% 2.58/1.34  #Chain   : 0
% 2.58/1.34  #Close   : 0
% 2.58/1.35  
% 2.58/1.35  Ordering : KBO
% 2.58/1.35  
% 2.58/1.35  Simplification rules
% 2.58/1.35  ----------------------
% 2.58/1.35  #Subsume      : 5
% 2.58/1.35  #Demod        : 9
% 2.58/1.35  #Tautology    : 4
% 2.58/1.35  #SimpNegUnit  : 3
% 2.58/1.35  #BackRed      : 0
% 2.58/1.35  
% 2.58/1.35  #Partial instantiations: 0
% 2.58/1.35  #Strategies tried      : 1
% 2.58/1.35  
% 2.58/1.35  Timing (in seconds)
% 2.58/1.35  ----------------------
% 2.58/1.35  Preprocessing        : 0.32
% 2.58/1.35  Parsing              : 0.17
% 2.58/1.35  CNF conversion       : 0.03
% 2.58/1.35  Main loop            : 0.24
% 2.58/1.35  Inferencing          : 0.11
% 2.58/1.35  Reduction            : 0.06
% 2.58/1.35  Demodulation         : 0.04
% 2.58/1.35  BG Simplification    : 0.02
% 2.58/1.35  Subsumption          : 0.05
% 2.58/1.35  Abstraction          : 0.01
% 2.58/1.35  MUC search           : 0.00
% 2.58/1.35  Cooper               : 0.00
% 2.58/1.35  Total                : 0.60
% 2.58/1.35  Index Insertion      : 0.00
% 2.58/1.35  Index Deletion       : 0.00
% 2.58/1.35  Index Matching       : 0.00
% 2.58/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
