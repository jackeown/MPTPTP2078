%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:08 EST 2020

% Result     : Theorem 2.06s
% Output     : CNFRefutation 2.06s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 223 expanded)
%              Number of leaves         :   35 (  93 expanded)
%              Depth                    :   18
%              Number of atoms          :  229 ( 994 expanded)
%              Number of equality atoms :    2 (   8 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r1_waybel_0 > r1_orders_2 > r2_hidden > m1_subset_1 > l1_waybel_0 > v2_struct_0 > v1_xboole_0 > v1_funct_1 > l1_struct_0 > l1_orders_2 > k3_funct_2 > k2_waybel_0 > k2_relset_1 > u1_waybel_0 > o_2_4_waybel_9 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_3 > #skF_2 > #skF_4 > #skF_1

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

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff(k2_waybel_0,type,(
    k2_waybel_0: ( $i * $i * $i ) > $i )).

tff(o_2_4_waybel_9,type,(
    o_2_4_waybel_9: ( $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(r1_waybel_0,type,(
    r1_waybel_0: ( $i * $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(f_139,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & l1_struct_0(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & l1_waybel_0(B,A) )
           => r1_waybel_0(A,B,k2_relset_1(u1_struct_0(B),u1_struct_0(A),u1_waybel_0(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_waybel_9)).

tff(f_113,axiom,(
    ! [A,B] :
      ( ( l1_struct_0(A)
        & l1_waybel_0(B,A) )
     => ( v1_funct_1(u1_waybel_0(A,B))
        & v1_funct_2(u1_waybel_0(A,B),u1_struct_0(B),u1_struct_0(A))
        & m1_subset_1(u1_waybel_0(A,B),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B),u1_struct_0(A)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_waybel_0)).

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

tff(f_125,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A)
        & ~ v2_struct_0(B)
        & l1_waybel_0(B,A) )
     => m1_subset_1(o_2_4_waybel_9(A,B),u1_struct_0(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_o_2_4_waybel_9)).

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

tff(c_38,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_36,plain,(
    l1_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_32,plain,(
    l1_waybel_0('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_24,plain,(
    ! [A_81,B_82] :
      ( v1_funct_2(u1_waybel_0(A_81,B_82),u1_struct_0(B_82),u1_struct_0(A_81))
      | ~ l1_waybel_0(B_82,A_81)
      | ~ l1_struct_0(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_26,plain,(
    ! [A_81,B_82] :
      ( v1_funct_1(u1_waybel_0(A_81,B_82))
      | ~ l1_waybel_0(B_82,A_81)
      | ~ l1_struct_0(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_41,plain,(
    ! [B_88,A_89] :
      ( l1_orders_2(B_88)
      | ~ l1_waybel_0(B_88,A_89)
      | ~ l1_struct_0(A_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_44,plain,
    ( l1_orders_2('#skF_4')
    | ~ l1_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_41])).

tff(c_47,plain,(
    l1_orders_2('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_44])).

tff(c_6,plain,(
    ! [A_17] :
      ( l1_struct_0(A_17)
      | ~ l1_orders_2(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_34,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_28,plain,(
    ! [A_83,B_84] :
      ( m1_subset_1(o_2_4_waybel_9(A_83,B_84),u1_struct_0(B_84))
      | ~ l1_waybel_0(B_84,A_83)
      | v2_struct_0(B_84)
      | ~ l1_struct_0(A_83)
      | v2_struct_0(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

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

tff(c_65,plain,(
    ! [A_116,B_117,D_118,C_119] :
      ( r2_hidden(k3_funct_2(A_116,B_117,D_118,C_119),k2_relset_1(A_116,B_117,D_118))
      | ~ m1_subset_1(D_118,k1_zfmisc_1(k2_zfmisc_1(A_116,B_117)))
      | ~ v1_funct_2(D_118,A_116,B_117)
      | ~ v1_funct_1(D_118)
      | ~ m1_subset_1(C_119,A_116)
      | v1_xboole_0(B_117)
      | v1_xboole_0(A_116) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_81,plain,(
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
    inference(superposition,[status(thm),theory(equality)],[c_18,c_65])).

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

tff(c_87,plain,(
    ! [A_132,B_133,D_134] :
      ( r1_waybel_0(A_132,B_133,k2_relset_1(u1_struct_0(B_133),u1_struct_0(A_132),u1_waybel_0(A_132,B_133)))
      | ~ m1_subset_1(D_134,u1_struct_0(B_133))
      | ~ m1_subset_1(u1_waybel_0(A_132,B_133),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_133),u1_struct_0(A_132))))
      | ~ v1_funct_2(u1_waybel_0(A_132,B_133),u1_struct_0(B_133),u1_struct_0(A_132))
      | ~ v1_funct_1(u1_waybel_0(A_132,B_133))
      | v1_xboole_0(u1_struct_0(A_132))
      | v1_xboole_0(u1_struct_0(B_133))
      | ~ m1_subset_1('#skF_1'(A_132,B_133,k2_relset_1(u1_struct_0(B_133),u1_struct_0(A_132),u1_waybel_0(A_132,B_133)),D_134),u1_struct_0(B_133))
      | ~ l1_waybel_0(B_133,A_132)
      | v2_struct_0(B_133)
      | ~ l1_struct_0(A_132)
      | v2_struct_0(A_132) ) ),
    inference(resolution,[status(thm)],[c_81,c_12])).

tff(c_93,plain,(
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
    inference(resolution,[status(thm)],[c_16,c_87])).

tff(c_97,plain,(
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
    inference(resolution,[status(thm)],[c_22,c_93])).

tff(c_107,plain,(
    ! [A_141,B_142,A_143] :
      ( ~ v1_funct_2(u1_waybel_0(A_141,B_142),u1_struct_0(B_142),u1_struct_0(A_141))
      | ~ v1_funct_1(u1_waybel_0(A_141,B_142))
      | v1_xboole_0(u1_struct_0(A_141))
      | v1_xboole_0(u1_struct_0(B_142))
      | r1_waybel_0(A_141,B_142,k2_relset_1(u1_struct_0(B_142),u1_struct_0(A_141),u1_waybel_0(A_141,B_142)))
      | v2_struct_0(A_141)
      | ~ l1_waybel_0(B_142,A_141)
      | ~ l1_struct_0(A_141)
      | ~ l1_waybel_0(B_142,A_143)
      | v2_struct_0(B_142)
      | ~ l1_struct_0(A_143)
      | v2_struct_0(A_143) ) ),
    inference(resolution,[status(thm)],[c_28,c_97])).

tff(c_109,plain,(
    ! [A_141] :
      ( ~ v1_funct_2(u1_waybel_0(A_141,'#skF_4'),u1_struct_0('#skF_4'),u1_struct_0(A_141))
      | ~ v1_funct_1(u1_waybel_0(A_141,'#skF_4'))
      | v1_xboole_0(u1_struct_0(A_141))
      | v1_xboole_0(u1_struct_0('#skF_4'))
      | r1_waybel_0(A_141,'#skF_4',k2_relset_1(u1_struct_0('#skF_4'),u1_struct_0(A_141),u1_waybel_0(A_141,'#skF_4')))
      | v2_struct_0(A_141)
      | ~ l1_waybel_0('#skF_4',A_141)
      | ~ l1_struct_0(A_141)
      | v2_struct_0('#skF_4')
      | ~ l1_struct_0('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_32,c_107])).

tff(c_112,plain,(
    ! [A_141] :
      ( ~ v1_funct_2(u1_waybel_0(A_141,'#skF_4'),u1_struct_0('#skF_4'),u1_struct_0(A_141))
      | ~ v1_funct_1(u1_waybel_0(A_141,'#skF_4'))
      | v1_xboole_0(u1_struct_0(A_141))
      | v1_xboole_0(u1_struct_0('#skF_4'))
      | r1_waybel_0(A_141,'#skF_4',k2_relset_1(u1_struct_0('#skF_4'),u1_struct_0(A_141),u1_waybel_0(A_141,'#skF_4')))
      | v2_struct_0(A_141)
      | ~ l1_waybel_0('#skF_4',A_141)
      | ~ l1_struct_0(A_141)
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_109])).

tff(c_113,plain,(
    ! [A_141] :
      ( ~ v1_funct_2(u1_waybel_0(A_141,'#skF_4'),u1_struct_0('#skF_4'),u1_struct_0(A_141))
      | ~ v1_funct_1(u1_waybel_0(A_141,'#skF_4'))
      | v1_xboole_0(u1_struct_0(A_141))
      | v1_xboole_0(u1_struct_0('#skF_4'))
      | r1_waybel_0(A_141,'#skF_4',k2_relset_1(u1_struct_0('#skF_4'),u1_struct_0(A_141),u1_waybel_0(A_141,'#skF_4')))
      | v2_struct_0(A_141)
      | ~ l1_waybel_0('#skF_4',A_141)
      | ~ l1_struct_0(A_141) ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_34,c_112])).

tff(c_114,plain,(
    v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_113])).

tff(c_4,plain,(
    ! [A_16] :
      ( ~ v1_xboole_0(u1_struct_0(A_16))
      | ~ l1_struct_0(A_16)
      | v2_struct_0(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_117,plain,
    ( ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_114,c_4])).

tff(c_120,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_117])).

tff(c_123,plain,(
    ~ l1_orders_2('#skF_4') ),
    inference(resolution,[status(thm)],[c_6,c_120])).

tff(c_127,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_47,c_123])).

tff(c_130,plain,(
    ! [A_144] :
      ( ~ v1_funct_2(u1_waybel_0(A_144,'#skF_4'),u1_struct_0('#skF_4'),u1_struct_0(A_144))
      | ~ v1_funct_1(u1_waybel_0(A_144,'#skF_4'))
      | v1_xboole_0(u1_struct_0(A_144))
      | r1_waybel_0(A_144,'#skF_4',k2_relset_1(u1_struct_0('#skF_4'),u1_struct_0(A_144),u1_waybel_0(A_144,'#skF_4')))
      | v2_struct_0(A_144)
      | ~ l1_waybel_0('#skF_4',A_144)
      | ~ l1_struct_0(A_144) ) ),
    inference(splitRight,[status(thm)],[c_113])).

tff(c_30,plain,(
    ~ r1_waybel_0('#skF_3','#skF_4',k2_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),u1_waybel_0('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_133,plain,
    ( ~ v1_funct_2(u1_waybel_0('#skF_3','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1(u1_waybel_0('#skF_3','#skF_4'))
    | v1_xboole_0(u1_struct_0('#skF_3'))
    | v2_struct_0('#skF_3')
    | ~ l1_waybel_0('#skF_4','#skF_3')
    | ~ l1_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_130,c_30])).

tff(c_136,plain,
    ( ~ v1_funct_2(u1_waybel_0('#skF_3','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1(u1_waybel_0('#skF_3','#skF_4'))
    | v1_xboole_0(u1_struct_0('#skF_3'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_133])).

tff(c_137,plain,
    ( ~ v1_funct_2(u1_waybel_0('#skF_3','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1(u1_waybel_0('#skF_3','#skF_4'))
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_136])).

tff(c_138,plain,(
    ~ v1_funct_1(u1_waybel_0('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_137])).

tff(c_141,plain,
    ( ~ l1_waybel_0('#skF_4','#skF_3')
    | ~ l1_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_138])).

tff(c_145,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_141])).

tff(c_146,plain,
    ( ~ v1_funct_2(u1_waybel_0('#skF_3','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_137])).

tff(c_148,plain,(
    ~ v1_funct_2(u1_waybel_0('#skF_3','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_146])).

tff(c_151,plain,
    ( ~ l1_waybel_0('#skF_4','#skF_3')
    | ~ l1_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_148])).

tff(c_155,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_151])).

tff(c_156,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_146])).

tff(c_160,plain,
    ( ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_156,c_4])).

tff(c_163,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_160])).

tff(c_165,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_163])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.07  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.08  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.07/0.26  % Computer   : n016.cluster.edu
% 0.07/0.26  % Model      : x86_64 x86_64
% 0.07/0.26  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.07/0.26  % Memory     : 8042.1875MB
% 0.07/0.26  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.07/0.26  % CPULimit   : 60
% 0.07/0.26  % DateTime   : Tue Dec  1 19:59:49 EST 2020
% 0.07/0.26  % CPUTime    : 
% 0.07/0.27  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.06/1.23  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.06/1.24  
% 2.06/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.06/1.24  %$ v1_funct_2 > r1_waybel_0 > r1_orders_2 > r2_hidden > m1_subset_1 > l1_waybel_0 > v2_struct_0 > v1_xboole_0 > v1_funct_1 > l1_struct_0 > l1_orders_2 > k3_funct_2 > k2_waybel_0 > k2_relset_1 > u1_waybel_0 > o_2_4_waybel_9 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_3 > #skF_2 > #skF_4 > #skF_1
% 2.06/1.24  
% 2.06/1.24  %Foreground sorts:
% 2.06/1.24  
% 2.06/1.24  
% 2.06/1.24  %Background operators:
% 2.06/1.24  
% 2.06/1.24  
% 2.06/1.24  %Foreground operators:
% 2.06/1.24  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.06/1.24  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.06/1.24  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.06/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.06/1.24  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.06/1.24  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 2.06/1.24  tff(k2_waybel_0, type, k2_waybel_0: ($i * $i * $i) > $i).
% 2.06/1.24  tff(o_2_4_waybel_9, type, o_2_4_waybel_9: ($i * $i) > $i).
% 2.06/1.24  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.06/1.24  tff(r1_waybel_0, type, r1_waybel_0: ($i * $i * $i) > $o).
% 2.06/1.24  tff('#skF_3', type, '#skF_3': $i).
% 2.06/1.24  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.06/1.24  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.06/1.24  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.06/1.24  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.06/1.24  tff(u1_waybel_0, type, u1_waybel_0: ($i * $i) > $i).
% 2.06/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.06/1.24  tff(l1_waybel_0, type, l1_waybel_0: ($i * $i) > $o).
% 2.06/1.24  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.06/1.24  tff('#skF_4', type, '#skF_4': $i).
% 2.06/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.06/1.24  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 2.06/1.24  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.06/1.24  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.06/1.24  tff(k3_funct_2, type, k3_funct_2: ($i * $i * $i * $i) > $i).
% 2.06/1.24  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.06/1.24  
% 2.06/1.26  tff(f_139, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((~v2_struct_0(B) & l1_waybel_0(B, A)) => r1_waybel_0(A, B, k2_relset_1(u1_struct_0(B), u1_struct_0(A), u1_waybel_0(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_waybel_9)).
% 2.06/1.26  tff(f_113, axiom, (![A, B]: ((l1_struct_0(A) & l1_waybel_0(B, A)) => ((v1_funct_1(u1_waybel_0(A, B)) & v1_funct_2(u1_waybel_0(A, B), u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(u1_waybel_0(A, B), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_u1_waybel_0)).
% 2.06/1.26  tff(f_103, axiom, (![A]: (l1_struct_0(A) => (![B]: (l1_waybel_0(B, A) => l1_orders_2(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_waybel_0)).
% 2.06/1.26  tff(f_56, axiom, (![A]: (l1_orders_2(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 2.06/1.26  tff(f_125, axiom, (![A, B]: ((((~v2_struct_0(A) & l1_struct_0(A)) & ~v2_struct_0(B)) & l1_waybel_0(B, A)) => m1_subset_1(o_2_4_waybel_9(A, B), u1_struct_0(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_o_2_4_waybel_9)).
% 2.06/1.26  tff(f_80, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((~v2_struct_0(B) & l1_waybel_0(B, A)) => (![C]: (r1_waybel_0(A, B, C) <=> (?[D]: (m1_subset_1(D, u1_struct_0(B)) & (![E]: (m1_subset_1(E, u1_struct_0(B)) => (r1_orders_2(B, D, E) => r2_hidden(k2_waybel_0(A, B, E), C)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d11_waybel_0)).
% 2.06/1.26  tff(f_96, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((~v2_struct_0(B) & l1_waybel_0(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(B)) => (k2_waybel_0(A, B, C) = k3_funct_2(u1_struct_0(B), u1_struct_0(A), u1_waybel_0(A, B), C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_waybel_0)).
% 2.06/1.26  tff(f_44, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, A) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_hidden(k3_funct_2(A, B, D, C), k2_relset_1(A, B, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t189_funct_2)).
% 2.06/1.26  tff(f_52, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 2.06/1.26  tff(c_38, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_139])).
% 2.06/1.26  tff(c_36, plain, (l1_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_139])).
% 2.06/1.26  tff(c_32, plain, (l1_waybel_0('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_139])).
% 2.06/1.26  tff(c_24, plain, (![A_81, B_82]: (v1_funct_2(u1_waybel_0(A_81, B_82), u1_struct_0(B_82), u1_struct_0(A_81)) | ~l1_waybel_0(B_82, A_81) | ~l1_struct_0(A_81))), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.06/1.26  tff(c_26, plain, (![A_81, B_82]: (v1_funct_1(u1_waybel_0(A_81, B_82)) | ~l1_waybel_0(B_82, A_81) | ~l1_struct_0(A_81))), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.06/1.26  tff(c_41, plain, (![B_88, A_89]: (l1_orders_2(B_88) | ~l1_waybel_0(B_88, A_89) | ~l1_struct_0(A_89))), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.06/1.26  tff(c_44, plain, (l1_orders_2('#skF_4') | ~l1_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_32, c_41])).
% 2.06/1.26  tff(c_47, plain, (l1_orders_2('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_44])).
% 2.06/1.26  tff(c_6, plain, (![A_17]: (l1_struct_0(A_17) | ~l1_orders_2(A_17))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.06/1.26  tff(c_34, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_139])).
% 2.06/1.26  tff(c_28, plain, (![A_83, B_84]: (m1_subset_1(o_2_4_waybel_9(A_83, B_84), u1_struct_0(B_84)) | ~l1_waybel_0(B_84, A_83) | v2_struct_0(B_84) | ~l1_struct_0(A_83) | v2_struct_0(A_83))), inference(cnfTransformation, [status(thm)], [f_125])).
% 2.06/1.26  tff(c_22, plain, (![A_81, B_82]: (m1_subset_1(u1_waybel_0(A_81, B_82), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_82), u1_struct_0(A_81)))) | ~l1_waybel_0(B_82, A_81) | ~l1_struct_0(A_81))), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.06/1.26  tff(c_16, plain, (![A_18, B_46, C_60, D_67]: (m1_subset_1('#skF_1'(A_18, B_46, C_60, D_67), u1_struct_0(B_46)) | r1_waybel_0(A_18, B_46, C_60) | ~m1_subset_1(D_67, u1_struct_0(B_46)) | ~l1_waybel_0(B_46, A_18) | v2_struct_0(B_46) | ~l1_struct_0(A_18) | v2_struct_0(A_18))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.06/1.26  tff(c_18, plain, (![B_75, A_71, C_77]: (k3_funct_2(u1_struct_0(B_75), u1_struct_0(A_71), u1_waybel_0(A_71, B_75), C_77)=k2_waybel_0(A_71, B_75, C_77) | ~m1_subset_1(C_77, u1_struct_0(B_75)) | ~l1_waybel_0(B_75, A_71) | v2_struct_0(B_75) | ~l1_struct_0(A_71) | v2_struct_0(A_71))), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.06/1.26  tff(c_65, plain, (![A_116, B_117, D_118, C_119]: (r2_hidden(k3_funct_2(A_116, B_117, D_118, C_119), k2_relset_1(A_116, B_117, D_118)) | ~m1_subset_1(D_118, k1_zfmisc_1(k2_zfmisc_1(A_116, B_117))) | ~v1_funct_2(D_118, A_116, B_117) | ~v1_funct_1(D_118) | ~m1_subset_1(C_119, A_116) | v1_xboole_0(B_117) | v1_xboole_0(A_116))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.06/1.26  tff(c_81, plain, (![A_129, B_130, C_131]: (r2_hidden(k2_waybel_0(A_129, B_130, C_131), k2_relset_1(u1_struct_0(B_130), u1_struct_0(A_129), u1_waybel_0(A_129, B_130))) | ~m1_subset_1(u1_waybel_0(A_129, B_130), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_130), u1_struct_0(A_129)))) | ~v1_funct_2(u1_waybel_0(A_129, B_130), u1_struct_0(B_130), u1_struct_0(A_129)) | ~v1_funct_1(u1_waybel_0(A_129, B_130)) | ~m1_subset_1(C_131, u1_struct_0(B_130)) | v1_xboole_0(u1_struct_0(A_129)) | v1_xboole_0(u1_struct_0(B_130)) | ~m1_subset_1(C_131, u1_struct_0(B_130)) | ~l1_waybel_0(B_130, A_129) | v2_struct_0(B_130) | ~l1_struct_0(A_129) | v2_struct_0(A_129))), inference(superposition, [status(thm), theory('equality')], [c_18, c_65])).
% 2.06/1.26  tff(c_12, plain, (![A_18, B_46, C_60, D_67]: (~r2_hidden(k2_waybel_0(A_18, B_46, '#skF_1'(A_18, B_46, C_60, D_67)), C_60) | r1_waybel_0(A_18, B_46, C_60) | ~m1_subset_1(D_67, u1_struct_0(B_46)) | ~l1_waybel_0(B_46, A_18) | v2_struct_0(B_46) | ~l1_struct_0(A_18) | v2_struct_0(A_18))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.06/1.26  tff(c_87, plain, (![A_132, B_133, D_134]: (r1_waybel_0(A_132, B_133, k2_relset_1(u1_struct_0(B_133), u1_struct_0(A_132), u1_waybel_0(A_132, B_133))) | ~m1_subset_1(D_134, u1_struct_0(B_133)) | ~m1_subset_1(u1_waybel_0(A_132, B_133), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_133), u1_struct_0(A_132)))) | ~v1_funct_2(u1_waybel_0(A_132, B_133), u1_struct_0(B_133), u1_struct_0(A_132)) | ~v1_funct_1(u1_waybel_0(A_132, B_133)) | v1_xboole_0(u1_struct_0(A_132)) | v1_xboole_0(u1_struct_0(B_133)) | ~m1_subset_1('#skF_1'(A_132, B_133, k2_relset_1(u1_struct_0(B_133), u1_struct_0(A_132), u1_waybel_0(A_132, B_133)), D_134), u1_struct_0(B_133)) | ~l1_waybel_0(B_133, A_132) | v2_struct_0(B_133) | ~l1_struct_0(A_132) | v2_struct_0(A_132))), inference(resolution, [status(thm)], [c_81, c_12])).
% 2.06/1.26  tff(c_93, plain, (![A_135, B_136, D_137]: (~m1_subset_1(u1_waybel_0(A_135, B_136), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_136), u1_struct_0(A_135)))) | ~v1_funct_2(u1_waybel_0(A_135, B_136), u1_struct_0(B_136), u1_struct_0(A_135)) | ~v1_funct_1(u1_waybel_0(A_135, B_136)) | v1_xboole_0(u1_struct_0(A_135)) | v1_xboole_0(u1_struct_0(B_136)) | r1_waybel_0(A_135, B_136, k2_relset_1(u1_struct_0(B_136), u1_struct_0(A_135), u1_waybel_0(A_135, B_136))) | ~m1_subset_1(D_137, u1_struct_0(B_136)) | ~l1_waybel_0(B_136, A_135) | v2_struct_0(B_136) | ~l1_struct_0(A_135) | v2_struct_0(A_135))), inference(resolution, [status(thm)], [c_16, c_87])).
% 2.06/1.26  tff(c_97, plain, (![A_138, B_139, D_140]: (~v1_funct_2(u1_waybel_0(A_138, B_139), u1_struct_0(B_139), u1_struct_0(A_138)) | ~v1_funct_1(u1_waybel_0(A_138, B_139)) | v1_xboole_0(u1_struct_0(A_138)) | v1_xboole_0(u1_struct_0(B_139)) | r1_waybel_0(A_138, B_139, k2_relset_1(u1_struct_0(B_139), u1_struct_0(A_138), u1_waybel_0(A_138, B_139))) | ~m1_subset_1(D_140, u1_struct_0(B_139)) | v2_struct_0(B_139) | v2_struct_0(A_138) | ~l1_waybel_0(B_139, A_138) | ~l1_struct_0(A_138))), inference(resolution, [status(thm)], [c_22, c_93])).
% 2.06/1.26  tff(c_107, plain, (![A_141, B_142, A_143]: (~v1_funct_2(u1_waybel_0(A_141, B_142), u1_struct_0(B_142), u1_struct_0(A_141)) | ~v1_funct_1(u1_waybel_0(A_141, B_142)) | v1_xboole_0(u1_struct_0(A_141)) | v1_xboole_0(u1_struct_0(B_142)) | r1_waybel_0(A_141, B_142, k2_relset_1(u1_struct_0(B_142), u1_struct_0(A_141), u1_waybel_0(A_141, B_142))) | v2_struct_0(A_141) | ~l1_waybel_0(B_142, A_141) | ~l1_struct_0(A_141) | ~l1_waybel_0(B_142, A_143) | v2_struct_0(B_142) | ~l1_struct_0(A_143) | v2_struct_0(A_143))), inference(resolution, [status(thm)], [c_28, c_97])).
% 2.06/1.26  tff(c_109, plain, (![A_141]: (~v1_funct_2(u1_waybel_0(A_141, '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0(A_141)) | ~v1_funct_1(u1_waybel_0(A_141, '#skF_4')) | v1_xboole_0(u1_struct_0(A_141)) | v1_xboole_0(u1_struct_0('#skF_4')) | r1_waybel_0(A_141, '#skF_4', k2_relset_1(u1_struct_0('#skF_4'), u1_struct_0(A_141), u1_waybel_0(A_141, '#skF_4'))) | v2_struct_0(A_141) | ~l1_waybel_0('#skF_4', A_141) | ~l1_struct_0(A_141) | v2_struct_0('#skF_4') | ~l1_struct_0('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_32, c_107])).
% 2.06/1.26  tff(c_112, plain, (![A_141]: (~v1_funct_2(u1_waybel_0(A_141, '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0(A_141)) | ~v1_funct_1(u1_waybel_0(A_141, '#skF_4')) | v1_xboole_0(u1_struct_0(A_141)) | v1_xboole_0(u1_struct_0('#skF_4')) | r1_waybel_0(A_141, '#skF_4', k2_relset_1(u1_struct_0('#skF_4'), u1_struct_0(A_141), u1_waybel_0(A_141, '#skF_4'))) | v2_struct_0(A_141) | ~l1_waybel_0('#skF_4', A_141) | ~l1_struct_0(A_141) | v2_struct_0('#skF_4') | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_109])).
% 2.06/1.26  tff(c_113, plain, (![A_141]: (~v1_funct_2(u1_waybel_0(A_141, '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0(A_141)) | ~v1_funct_1(u1_waybel_0(A_141, '#skF_4')) | v1_xboole_0(u1_struct_0(A_141)) | v1_xboole_0(u1_struct_0('#skF_4')) | r1_waybel_0(A_141, '#skF_4', k2_relset_1(u1_struct_0('#skF_4'), u1_struct_0(A_141), u1_waybel_0(A_141, '#skF_4'))) | v2_struct_0(A_141) | ~l1_waybel_0('#skF_4', A_141) | ~l1_struct_0(A_141))), inference(negUnitSimplification, [status(thm)], [c_38, c_34, c_112])).
% 2.06/1.26  tff(c_114, plain, (v1_xboole_0(u1_struct_0('#skF_4'))), inference(splitLeft, [status(thm)], [c_113])).
% 2.06/1.26  tff(c_4, plain, (![A_16]: (~v1_xboole_0(u1_struct_0(A_16)) | ~l1_struct_0(A_16) | v2_struct_0(A_16))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.06/1.26  tff(c_117, plain, (~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_114, c_4])).
% 2.06/1.26  tff(c_120, plain, (~l1_struct_0('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_34, c_117])).
% 2.06/1.26  tff(c_123, plain, (~l1_orders_2('#skF_4')), inference(resolution, [status(thm)], [c_6, c_120])).
% 2.06/1.26  tff(c_127, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_47, c_123])).
% 2.06/1.26  tff(c_130, plain, (![A_144]: (~v1_funct_2(u1_waybel_0(A_144, '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0(A_144)) | ~v1_funct_1(u1_waybel_0(A_144, '#skF_4')) | v1_xboole_0(u1_struct_0(A_144)) | r1_waybel_0(A_144, '#skF_4', k2_relset_1(u1_struct_0('#skF_4'), u1_struct_0(A_144), u1_waybel_0(A_144, '#skF_4'))) | v2_struct_0(A_144) | ~l1_waybel_0('#skF_4', A_144) | ~l1_struct_0(A_144))), inference(splitRight, [status(thm)], [c_113])).
% 2.06/1.26  tff(c_30, plain, (~r1_waybel_0('#skF_3', '#skF_4', k2_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), u1_waybel_0('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_139])).
% 2.06/1.26  tff(c_133, plain, (~v1_funct_2(u1_waybel_0('#skF_3', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1(u1_waybel_0('#skF_3', '#skF_4')) | v1_xboole_0(u1_struct_0('#skF_3')) | v2_struct_0('#skF_3') | ~l1_waybel_0('#skF_4', '#skF_3') | ~l1_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_130, c_30])).
% 2.06/1.26  tff(c_136, plain, (~v1_funct_2(u1_waybel_0('#skF_3', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1(u1_waybel_0('#skF_3', '#skF_4')) | v1_xboole_0(u1_struct_0('#skF_3')) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_32, c_133])).
% 2.06/1.26  tff(c_137, plain, (~v1_funct_2(u1_waybel_0('#skF_3', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1(u1_waybel_0('#skF_3', '#skF_4')) | v1_xboole_0(u1_struct_0('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_38, c_136])).
% 2.06/1.26  tff(c_138, plain, (~v1_funct_1(u1_waybel_0('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_137])).
% 2.06/1.26  tff(c_141, plain, (~l1_waybel_0('#skF_4', '#skF_3') | ~l1_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_26, c_138])).
% 2.06/1.26  tff(c_145, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_32, c_141])).
% 2.06/1.26  tff(c_146, plain, (~v1_funct_2(u1_waybel_0('#skF_3', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_137])).
% 2.06/1.26  tff(c_148, plain, (~v1_funct_2(u1_waybel_0('#skF_3', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_146])).
% 2.06/1.26  tff(c_151, plain, (~l1_waybel_0('#skF_4', '#skF_3') | ~l1_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_24, c_148])).
% 2.06/1.26  tff(c_155, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_32, c_151])).
% 2.06/1.26  tff(c_156, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_146])).
% 2.06/1.26  tff(c_160, plain, (~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_156, c_4])).
% 2.06/1.26  tff(c_163, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_160])).
% 2.06/1.26  tff(c_165, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_163])).
% 2.06/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.06/1.26  
% 2.06/1.26  Inference rules
% 2.06/1.26  ----------------------
% 2.06/1.26  #Ref     : 0
% 2.06/1.26  #Sup     : 19
% 2.06/1.26  #Fact    : 0
% 2.06/1.26  #Define  : 0
% 2.06/1.26  #Split   : 3
% 2.06/1.26  #Chain   : 0
% 2.06/1.26  #Close   : 0
% 2.06/1.26  
% 2.06/1.26  Ordering : KBO
% 2.06/1.26  
% 2.06/1.26  Simplification rules
% 2.06/1.26  ----------------------
% 2.06/1.26  #Subsume      : 4
% 2.06/1.26  #Demod        : 10
% 2.06/1.26  #Tautology    : 3
% 2.06/1.26  #SimpNegUnit  : 4
% 2.06/1.26  #BackRed      : 0
% 2.06/1.26  
% 2.06/1.26  #Partial instantiations: 0
% 2.06/1.26  #Strategies tried      : 1
% 2.06/1.26  
% 2.06/1.26  Timing (in seconds)
% 2.06/1.26  ----------------------
% 2.06/1.26  Preprocessing        : 0.28
% 2.06/1.26  Parsing              : 0.15
% 2.06/1.26  CNF conversion       : 0.03
% 2.06/1.26  Main loop            : 0.21
% 2.06/1.26  Inferencing          : 0.09
% 2.06/1.26  Reduction            : 0.05
% 2.06/1.26  Demodulation         : 0.03
% 2.06/1.26  BG Simplification    : 0.01
% 2.06/1.26  Subsumption          : 0.04
% 2.06/1.26  Abstraction          : 0.01
% 2.06/1.26  MUC search           : 0.00
% 2.06/1.26  Cooper               : 0.00
% 2.06/1.26  Total                : 0.53
% 2.06/1.26  Index Insertion      : 0.00
% 2.06/1.26  Index Deletion       : 0.00
% 2.06/1.26  Index Matching       : 0.00
% 2.06/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
