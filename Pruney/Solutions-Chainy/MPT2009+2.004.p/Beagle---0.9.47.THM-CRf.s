%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:07 EST 2020

% Result     : Theorem 2.16s
% Output     : CNFRefutation 2.16s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 210 expanded)
%              Number of leaves         :   36 (  89 expanded)
%              Depth                    :   16
%              Number of atoms          :  198 ( 839 expanded)
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

tff(f_137,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & l1_struct_0(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & l1_waybel_0(B,A) )
           => r1_waybel_0(A,B,k2_relset_1(u1_struct_0(B),u1_struct_0(A),u1_waybel_0(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_waybel_9)).

tff(f_113,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ! [B] :
          ( l1_waybel_0(B,A)
         => l1_orders_2(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_waybel_0)).

tff(f_66,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_123,axiom,(
    ! [A,B] :
      ( ( l1_struct_0(A)
        & l1_waybel_0(B,A) )
     => ( v1_funct_1(u1_waybel_0(A,B))
        & v1_funct_2(u1_waybel_0(A,B),u1_struct_0(B),u1_struct_0(A))
        & m1_subset_1(u1_waybel_0(A,B),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B),u1_struct_0(A)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_waybel_0)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(f_90,axiom,(
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

tff(f_106,axiom,(
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

tff(f_54,axiom,(
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

tff(f_62,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(c_42,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_40,plain,(
    l1_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_36,plain,(
    l1_waybel_0('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_57,plain,(
    ! [B_98,A_99] :
      ( l1_orders_2(B_98)
      | ~ l1_waybel_0(B_98,A_99)
      | ~ l1_struct_0(A_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_60,plain,
    ( l1_orders_2('#skF_5')
    | ~ l1_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_57])).

tff(c_63,plain,(
    l1_orders_2('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_60])).

tff(c_12,plain,(
    ! [A_23] :
      ( l1_struct_0(A_23)
      | ~ l1_orders_2(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_38,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_30,plain,(
    ! [A_87,B_88] :
      ( v1_funct_2(u1_waybel_0(A_87,B_88),u1_struct_0(B_88),u1_struct_0(A_87))
      | ~ l1_waybel_0(B_88,A_87)
      | ~ l1_struct_0(A_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_32,plain,(
    ! [A_87,B_88] :
      ( v1_funct_1(u1_waybel_0(A_87,B_88))
      | ~ l1_waybel_0(B_88,A_87)
      | ~ l1_struct_0(A_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_50,plain,(
    ! [A_94,B_95] :
      ( m1_subset_1(A_94,B_95)
      | ~ r2_hidden(A_94,B_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_54,plain,(
    ! [A_1] :
      ( m1_subset_1('#skF_1'(A_1),A_1)
      | v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_4,c_50])).

tff(c_28,plain,(
    ! [A_87,B_88] :
      ( m1_subset_1(u1_waybel_0(A_87,B_88),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_88),u1_struct_0(A_87))))
      | ~ l1_waybel_0(B_88,A_87)
      | ~ l1_struct_0(A_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_22,plain,(
    ! [A_24,B_52,C_66,D_73] :
      ( m1_subset_1('#skF_2'(A_24,B_52,C_66,D_73),u1_struct_0(B_52))
      | r1_waybel_0(A_24,B_52,C_66)
      | ~ m1_subset_1(D_73,u1_struct_0(B_52))
      | ~ l1_waybel_0(B_52,A_24)
      | v2_struct_0(B_52)
      | ~ l1_struct_0(A_24)
      | v2_struct_0(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_24,plain,(
    ! [B_81,A_77,C_83] :
      ( k3_funct_2(u1_struct_0(B_81),u1_struct_0(A_77),u1_waybel_0(A_77,B_81),C_83) = k2_waybel_0(A_77,B_81,C_83)
      | ~ m1_subset_1(C_83,u1_struct_0(B_81))
      | ~ l1_waybel_0(B_81,A_77)
      | v2_struct_0(B_81)
      | ~ l1_struct_0(A_77)
      | v2_struct_0(A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_80,plain,(
    ! [A_124,B_125,D_126,C_127] :
      ( r2_hidden(k3_funct_2(A_124,B_125,D_126,C_127),k2_relset_1(A_124,B_125,D_126))
      | ~ m1_subset_1(D_126,k1_zfmisc_1(k2_zfmisc_1(A_124,B_125)))
      | ~ v1_funct_2(D_126,A_124,B_125)
      | ~ v1_funct_1(D_126)
      | ~ m1_subset_1(C_127,A_124)
      | v1_xboole_0(B_125)
      | v1_xboole_0(A_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_142,plain,(
    ! [A_171,B_172,C_173] :
      ( r2_hidden(k2_waybel_0(A_171,B_172,C_173),k2_relset_1(u1_struct_0(B_172),u1_struct_0(A_171),u1_waybel_0(A_171,B_172)))
      | ~ m1_subset_1(u1_waybel_0(A_171,B_172),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_172),u1_struct_0(A_171))))
      | ~ v1_funct_2(u1_waybel_0(A_171,B_172),u1_struct_0(B_172),u1_struct_0(A_171))
      | ~ v1_funct_1(u1_waybel_0(A_171,B_172))
      | ~ m1_subset_1(C_173,u1_struct_0(B_172))
      | v1_xboole_0(u1_struct_0(A_171))
      | v1_xboole_0(u1_struct_0(B_172))
      | ~ m1_subset_1(C_173,u1_struct_0(B_172))
      | ~ l1_waybel_0(B_172,A_171)
      | v2_struct_0(B_172)
      | ~ l1_struct_0(A_171)
      | v2_struct_0(A_171) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_80])).

tff(c_18,plain,(
    ! [A_24,B_52,C_66,D_73] :
      ( ~ r2_hidden(k2_waybel_0(A_24,B_52,'#skF_2'(A_24,B_52,C_66,D_73)),C_66)
      | r1_waybel_0(A_24,B_52,C_66)
      | ~ m1_subset_1(D_73,u1_struct_0(B_52))
      | ~ l1_waybel_0(B_52,A_24)
      | v2_struct_0(B_52)
      | ~ l1_struct_0(A_24)
      | v2_struct_0(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_157,plain,(
    ! [A_177,B_178,D_179] :
      ( r1_waybel_0(A_177,B_178,k2_relset_1(u1_struct_0(B_178),u1_struct_0(A_177),u1_waybel_0(A_177,B_178)))
      | ~ m1_subset_1(D_179,u1_struct_0(B_178))
      | ~ m1_subset_1(u1_waybel_0(A_177,B_178),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_178),u1_struct_0(A_177))))
      | ~ v1_funct_2(u1_waybel_0(A_177,B_178),u1_struct_0(B_178),u1_struct_0(A_177))
      | ~ v1_funct_1(u1_waybel_0(A_177,B_178))
      | v1_xboole_0(u1_struct_0(A_177))
      | v1_xboole_0(u1_struct_0(B_178))
      | ~ m1_subset_1('#skF_2'(A_177,B_178,k2_relset_1(u1_struct_0(B_178),u1_struct_0(A_177),u1_waybel_0(A_177,B_178)),D_179),u1_struct_0(B_178))
      | ~ l1_waybel_0(B_178,A_177)
      | v2_struct_0(B_178)
      | ~ l1_struct_0(A_177)
      | v2_struct_0(A_177) ) ),
    inference(resolution,[status(thm)],[c_142,c_18])).

tff(c_163,plain,(
    ! [A_180,B_181,D_182] :
      ( ~ m1_subset_1(u1_waybel_0(A_180,B_181),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_181),u1_struct_0(A_180))))
      | ~ v1_funct_2(u1_waybel_0(A_180,B_181),u1_struct_0(B_181),u1_struct_0(A_180))
      | ~ v1_funct_1(u1_waybel_0(A_180,B_181))
      | v1_xboole_0(u1_struct_0(A_180))
      | v1_xboole_0(u1_struct_0(B_181))
      | r1_waybel_0(A_180,B_181,k2_relset_1(u1_struct_0(B_181),u1_struct_0(A_180),u1_waybel_0(A_180,B_181)))
      | ~ m1_subset_1(D_182,u1_struct_0(B_181))
      | ~ l1_waybel_0(B_181,A_180)
      | v2_struct_0(B_181)
      | ~ l1_struct_0(A_180)
      | v2_struct_0(A_180) ) ),
    inference(resolution,[status(thm)],[c_22,c_157])).

tff(c_167,plain,(
    ! [A_183,B_184,D_185] :
      ( ~ v1_funct_2(u1_waybel_0(A_183,B_184),u1_struct_0(B_184),u1_struct_0(A_183))
      | ~ v1_funct_1(u1_waybel_0(A_183,B_184))
      | v1_xboole_0(u1_struct_0(A_183))
      | v1_xboole_0(u1_struct_0(B_184))
      | r1_waybel_0(A_183,B_184,k2_relset_1(u1_struct_0(B_184),u1_struct_0(A_183),u1_waybel_0(A_183,B_184)))
      | ~ m1_subset_1(D_185,u1_struct_0(B_184))
      | v2_struct_0(B_184)
      | v2_struct_0(A_183)
      | ~ l1_waybel_0(B_184,A_183)
      | ~ l1_struct_0(A_183) ) ),
    inference(resolution,[status(thm)],[c_28,c_163])).

tff(c_182,plain,(
    ! [A_186,B_187] :
      ( ~ v1_funct_2(u1_waybel_0(A_186,B_187),u1_struct_0(B_187),u1_struct_0(A_186))
      | ~ v1_funct_1(u1_waybel_0(A_186,B_187))
      | v1_xboole_0(u1_struct_0(A_186))
      | r1_waybel_0(A_186,B_187,k2_relset_1(u1_struct_0(B_187),u1_struct_0(A_186),u1_waybel_0(A_186,B_187)))
      | v2_struct_0(B_187)
      | v2_struct_0(A_186)
      | ~ l1_waybel_0(B_187,A_186)
      | ~ l1_struct_0(A_186)
      | v1_xboole_0(u1_struct_0(B_187)) ) ),
    inference(resolution,[status(thm)],[c_54,c_167])).

tff(c_34,plain,(
    ~ r1_waybel_0('#skF_4','#skF_5',k2_relset_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),u1_waybel_0('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_187,plain,
    ( ~ v1_funct_2(u1_waybel_0('#skF_4','#skF_5'),u1_struct_0('#skF_5'),u1_struct_0('#skF_4'))
    | ~ v1_funct_1(u1_waybel_0('#skF_4','#skF_5'))
    | v1_xboole_0(u1_struct_0('#skF_4'))
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_4')
    | ~ l1_waybel_0('#skF_5','#skF_4')
    | ~ l1_struct_0('#skF_4')
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_182,c_34])).

tff(c_191,plain,
    ( ~ v1_funct_2(u1_waybel_0('#skF_4','#skF_5'),u1_struct_0('#skF_5'),u1_struct_0('#skF_4'))
    | ~ v1_funct_1(u1_waybel_0('#skF_4','#skF_5'))
    | v1_xboole_0(u1_struct_0('#skF_4'))
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_4')
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_36,c_187])).

tff(c_192,plain,
    ( ~ v1_funct_2(u1_waybel_0('#skF_4','#skF_5'),u1_struct_0('#skF_5'),u1_struct_0('#skF_4'))
    | ~ v1_funct_1(u1_waybel_0('#skF_4','#skF_5'))
    | v1_xboole_0(u1_struct_0('#skF_4'))
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_38,c_191])).

tff(c_193,plain,(
    ~ v1_funct_1(u1_waybel_0('#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_192])).

tff(c_196,plain,
    ( ~ l1_waybel_0('#skF_5','#skF_4')
    | ~ l1_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_193])).

tff(c_200,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_36,c_196])).

tff(c_201,plain,
    ( ~ v1_funct_2(u1_waybel_0('#skF_4','#skF_5'),u1_struct_0('#skF_5'),u1_struct_0('#skF_4'))
    | v1_xboole_0(u1_struct_0('#skF_5'))
    | v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_192])).

tff(c_203,plain,(
    ~ v1_funct_2(u1_waybel_0('#skF_4','#skF_5'),u1_struct_0('#skF_5'),u1_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_201])).

tff(c_206,plain,
    ( ~ l1_waybel_0('#skF_5','#skF_4')
    | ~ l1_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_203])).

tff(c_210,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_36,c_206])).

tff(c_211,plain,
    ( v1_xboole_0(u1_struct_0('#skF_4'))
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_201])).

tff(c_213,plain,(
    v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_211])).

tff(c_10,plain,(
    ! [A_22] :
      ( ~ v1_xboole_0(u1_struct_0(A_22))
      | ~ l1_struct_0(A_22)
      | v2_struct_0(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_217,plain,
    ( ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_213,c_10])).

tff(c_220,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_217])).

tff(c_223,plain,(
    ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_12,c_220])).

tff(c_227,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_223])).

tff(c_228,plain,(
    v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_211])).

tff(c_232,plain,
    ( ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_228,c_10])).

tff(c_235,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_232])).

tff(c_237,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_235])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:04:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.16/1.25  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.16/1.26  
% 2.16/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.16/1.26  %$ v1_funct_2 > r1_waybel_0 > r1_orders_2 > r2_hidden > m1_subset_1 > l1_waybel_0 > v2_struct_0 > v1_xboole_0 > v1_funct_1 > l1_struct_0 > l1_orders_2 > k3_funct_2 > k2_waybel_0 > k2_relset_1 > u1_waybel_0 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3
% 2.16/1.26  
% 2.16/1.26  %Foreground sorts:
% 2.16/1.26  
% 2.16/1.26  
% 2.16/1.26  %Background operators:
% 2.16/1.26  
% 2.16/1.26  
% 2.16/1.26  %Foreground operators:
% 2.16/1.26  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.16/1.26  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.16/1.26  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.16/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.16/1.26  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.16/1.26  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.16/1.26  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 2.16/1.26  tff(k2_waybel_0, type, k2_waybel_0: ($i * $i * $i) > $i).
% 2.16/1.26  tff('#skF_5', type, '#skF_5': $i).
% 2.16/1.26  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.16/1.26  tff(r1_waybel_0, type, r1_waybel_0: ($i * $i * $i) > $o).
% 2.16/1.26  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.16/1.26  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.16/1.26  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.16/1.26  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.16/1.26  tff(u1_waybel_0, type, u1_waybel_0: ($i * $i) > $i).
% 2.16/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.16/1.26  tff(l1_waybel_0, type, l1_waybel_0: ($i * $i) > $o).
% 2.16/1.26  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.16/1.26  tff('#skF_4', type, '#skF_4': $i).
% 2.16/1.26  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.16/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.16/1.26  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.16/1.26  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.16/1.26  tff(k3_funct_2, type, k3_funct_2: ($i * $i * $i * $i) > $i).
% 2.16/1.26  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.16/1.26  
% 2.16/1.28  tff(f_137, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((~v2_struct_0(B) & l1_waybel_0(B, A)) => r1_waybel_0(A, B, k2_relset_1(u1_struct_0(B), u1_struct_0(A), u1_waybel_0(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_waybel_9)).
% 2.16/1.28  tff(f_113, axiom, (![A]: (l1_struct_0(A) => (![B]: (l1_waybel_0(B, A) => l1_orders_2(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_waybel_0)).
% 2.16/1.28  tff(f_66, axiom, (![A]: (l1_orders_2(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 2.16/1.28  tff(f_123, axiom, (![A, B]: ((l1_struct_0(A) & l1_waybel_0(B, A)) => ((v1_funct_1(u1_waybel_0(A, B)) & v1_funct_2(u1_waybel_0(A, B), u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(u1_waybel_0(A, B), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_u1_waybel_0)).
% 2.16/1.28  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.16/1.28  tff(f_35, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 2.16/1.28  tff(f_90, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((~v2_struct_0(B) & l1_waybel_0(B, A)) => (![C]: (r1_waybel_0(A, B, C) <=> (?[D]: (m1_subset_1(D, u1_struct_0(B)) & (![E]: (m1_subset_1(E, u1_struct_0(B)) => (r1_orders_2(B, D, E) => r2_hidden(k2_waybel_0(A, B, E), C)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d11_waybel_0)).
% 2.16/1.28  tff(f_106, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((~v2_struct_0(B) & l1_waybel_0(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(B)) => (k2_waybel_0(A, B, C) = k3_funct_2(u1_struct_0(B), u1_struct_0(A), u1_waybel_0(A, B), C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_waybel_0)).
% 2.16/1.28  tff(f_54, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, A) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_hidden(k3_funct_2(A, B, D, C), k2_relset_1(A, B, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t189_funct_2)).
% 2.16/1.28  tff(f_62, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 2.16/1.28  tff(c_42, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_137])).
% 2.16/1.28  tff(c_40, plain, (l1_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_137])).
% 2.16/1.28  tff(c_36, plain, (l1_waybel_0('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_137])).
% 2.16/1.28  tff(c_57, plain, (![B_98, A_99]: (l1_orders_2(B_98) | ~l1_waybel_0(B_98, A_99) | ~l1_struct_0(A_99))), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.16/1.28  tff(c_60, plain, (l1_orders_2('#skF_5') | ~l1_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_36, c_57])).
% 2.16/1.28  tff(c_63, plain, (l1_orders_2('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_60])).
% 2.16/1.28  tff(c_12, plain, (![A_23]: (l1_struct_0(A_23) | ~l1_orders_2(A_23))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.16/1.28  tff(c_38, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_137])).
% 2.16/1.28  tff(c_30, plain, (![A_87, B_88]: (v1_funct_2(u1_waybel_0(A_87, B_88), u1_struct_0(B_88), u1_struct_0(A_87)) | ~l1_waybel_0(B_88, A_87) | ~l1_struct_0(A_87))), inference(cnfTransformation, [status(thm)], [f_123])).
% 2.16/1.28  tff(c_32, plain, (![A_87, B_88]: (v1_funct_1(u1_waybel_0(A_87, B_88)) | ~l1_waybel_0(B_88, A_87) | ~l1_struct_0(A_87))), inference(cnfTransformation, [status(thm)], [f_123])).
% 2.16/1.28  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.16/1.28  tff(c_50, plain, (![A_94, B_95]: (m1_subset_1(A_94, B_95) | ~r2_hidden(A_94, B_95))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.16/1.28  tff(c_54, plain, (![A_1]: (m1_subset_1('#skF_1'(A_1), A_1) | v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_4, c_50])).
% 2.16/1.28  tff(c_28, plain, (![A_87, B_88]: (m1_subset_1(u1_waybel_0(A_87, B_88), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_88), u1_struct_0(A_87)))) | ~l1_waybel_0(B_88, A_87) | ~l1_struct_0(A_87))), inference(cnfTransformation, [status(thm)], [f_123])).
% 2.16/1.28  tff(c_22, plain, (![A_24, B_52, C_66, D_73]: (m1_subset_1('#skF_2'(A_24, B_52, C_66, D_73), u1_struct_0(B_52)) | r1_waybel_0(A_24, B_52, C_66) | ~m1_subset_1(D_73, u1_struct_0(B_52)) | ~l1_waybel_0(B_52, A_24) | v2_struct_0(B_52) | ~l1_struct_0(A_24) | v2_struct_0(A_24))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.16/1.28  tff(c_24, plain, (![B_81, A_77, C_83]: (k3_funct_2(u1_struct_0(B_81), u1_struct_0(A_77), u1_waybel_0(A_77, B_81), C_83)=k2_waybel_0(A_77, B_81, C_83) | ~m1_subset_1(C_83, u1_struct_0(B_81)) | ~l1_waybel_0(B_81, A_77) | v2_struct_0(B_81) | ~l1_struct_0(A_77) | v2_struct_0(A_77))), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.16/1.28  tff(c_80, plain, (![A_124, B_125, D_126, C_127]: (r2_hidden(k3_funct_2(A_124, B_125, D_126, C_127), k2_relset_1(A_124, B_125, D_126)) | ~m1_subset_1(D_126, k1_zfmisc_1(k2_zfmisc_1(A_124, B_125))) | ~v1_funct_2(D_126, A_124, B_125) | ~v1_funct_1(D_126) | ~m1_subset_1(C_127, A_124) | v1_xboole_0(B_125) | v1_xboole_0(A_124))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.16/1.28  tff(c_142, plain, (![A_171, B_172, C_173]: (r2_hidden(k2_waybel_0(A_171, B_172, C_173), k2_relset_1(u1_struct_0(B_172), u1_struct_0(A_171), u1_waybel_0(A_171, B_172))) | ~m1_subset_1(u1_waybel_0(A_171, B_172), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_172), u1_struct_0(A_171)))) | ~v1_funct_2(u1_waybel_0(A_171, B_172), u1_struct_0(B_172), u1_struct_0(A_171)) | ~v1_funct_1(u1_waybel_0(A_171, B_172)) | ~m1_subset_1(C_173, u1_struct_0(B_172)) | v1_xboole_0(u1_struct_0(A_171)) | v1_xboole_0(u1_struct_0(B_172)) | ~m1_subset_1(C_173, u1_struct_0(B_172)) | ~l1_waybel_0(B_172, A_171) | v2_struct_0(B_172) | ~l1_struct_0(A_171) | v2_struct_0(A_171))), inference(superposition, [status(thm), theory('equality')], [c_24, c_80])).
% 2.16/1.28  tff(c_18, plain, (![A_24, B_52, C_66, D_73]: (~r2_hidden(k2_waybel_0(A_24, B_52, '#skF_2'(A_24, B_52, C_66, D_73)), C_66) | r1_waybel_0(A_24, B_52, C_66) | ~m1_subset_1(D_73, u1_struct_0(B_52)) | ~l1_waybel_0(B_52, A_24) | v2_struct_0(B_52) | ~l1_struct_0(A_24) | v2_struct_0(A_24))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.16/1.28  tff(c_157, plain, (![A_177, B_178, D_179]: (r1_waybel_0(A_177, B_178, k2_relset_1(u1_struct_0(B_178), u1_struct_0(A_177), u1_waybel_0(A_177, B_178))) | ~m1_subset_1(D_179, u1_struct_0(B_178)) | ~m1_subset_1(u1_waybel_0(A_177, B_178), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_178), u1_struct_0(A_177)))) | ~v1_funct_2(u1_waybel_0(A_177, B_178), u1_struct_0(B_178), u1_struct_0(A_177)) | ~v1_funct_1(u1_waybel_0(A_177, B_178)) | v1_xboole_0(u1_struct_0(A_177)) | v1_xboole_0(u1_struct_0(B_178)) | ~m1_subset_1('#skF_2'(A_177, B_178, k2_relset_1(u1_struct_0(B_178), u1_struct_0(A_177), u1_waybel_0(A_177, B_178)), D_179), u1_struct_0(B_178)) | ~l1_waybel_0(B_178, A_177) | v2_struct_0(B_178) | ~l1_struct_0(A_177) | v2_struct_0(A_177))), inference(resolution, [status(thm)], [c_142, c_18])).
% 2.16/1.28  tff(c_163, plain, (![A_180, B_181, D_182]: (~m1_subset_1(u1_waybel_0(A_180, B_181), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_181), u1_struct_0(A_180)))) | ~v1_funct_2(u1_waybel_0(A_180, B_181), u1_struct_0(B_181), u1_struct_0(A_180)) | ~v1_funct_1(u1_waybel_0(A_180, B_181)) | v1_xboole_0(u1_struct_0(A_180)) | v1_xboole_0(u1_struct_0(B_181)) | r1_waybel_0(A_180, B_181, k2_relset_1(u1_struct_0(B_181), u1_struct_0(A_180), u1_waybel_0(A_180, B_181))) | ~m1_subset_1(D_182, u1_struct_0(B_181)) | ~l1_waybel_0(B_181, A_180) | v2_struct_0(B_181) | ~l1_struct_0(A_180) | v2_struct_0(A_180))), inference(resolution, [status(thm)], [c_22, c_157])).
% 2.16/1.28  tff(c_167, plain, (![A_183, B_184, D_185]: (~v1_funct_2(u1_waybel_0(A_183, B_184), u1_struct_0(B_184), u1_struct_0(A_183)) | ~v1_funct_1(u1_waybel_0(A_183, B_184)) | v1_xboole_0(u1_struct_0(A_183)) | v1_xboole_0(u1_struct_0(B_184)) | r1_waybel_0(A_183, B_184, k2_relset_1(u1_struct_0(B_184), u1_struct_0(A_183), u1_waybel_0(A_183, B_184))) | ~m1_subset_1(D_185, u1_struct_0(B_184)) | v2_struct_0(B_184) | v2_struct_0(A_183) | ~l1_waybel_0(B_184, A_183) | ~l1_struct_0(A_183))), inference(resolution, [status(thm)], [c_28, c_163])).
% 2.16/1.28  tff(c_182, plain, (![A_186, B_187]: (~v1_funct_2(u1_waybel_0(A_186, B_187), u1_struct_0(B_187), u1_struct_0(A_186)) | ~v1_funct_1(u1_waybel_0(A_186, B_187)) | v1_xboole_0(u1_struct_0(A_186)) | r1_waybel_0(A_186, B_187, k2_relset_1(u1_struct_0(B_187), u1_struct_0(A_186), u1_waybel_0(A_186, B_187))) | v2_struct_0(B_187) | v2_struct_0(A_186) | ~l1_waybel_0(B_187, A_186) | ~l1_struct_0(A_186) | v1_xboole_0(u1_struct_0(B_187)))), inference(resolution, [status(thm)], [c_54, c_167])).
% 2.16/1.28  tff(c_34, plain, (~r1_waybel_0('#skF_4', '#skF_5', k2_relset_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'), u1_waybel_0('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_137])).
% 2.16/1.28  tff(c_187, plain, (~v1_funct_2(u1_waybel_0('#skF_4', '#skF_5'), u1_struct_0('#skF_5'), u1_struct_0('#skF_4')) | ~v1_funct_1(u1_waybel_0('#skF_4', '#skF_5')) | v1_xboole_0(u1_struct_0('#skF_4')) | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | ~l1_waybel_0('#skF_5', '#skF_4') | ~l1_struct_0('#skF_4') | v1_xboole_0(u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_182, c_34])).
% 2.16/1.28  tff(c_191, plain, (~v1_funct_2(u1_waybel_0('#skF_4', '#skF_5'), u1_struct_0('#skF_5'), u1_struct_0('#skF_4')) | ~v1_funct_1(u1_waybel_0('#skF_4', '#skF_5')) | v1_xboole_0(u1_struct_0('#skF_4')) | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | v1_xboole_0(u1_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_36, c_187])).
% 2.16/1.28  tff(c_192, plain, (~v1_funct_2(u1_waybel_0('#skF_4', '#skF_5'), u1_struct_0('#skF_5'), u1_struct_0('#skF_4')) | ~v1_funct_1(u1_waybel_0('#skF_4', '#skF_5')) | v1_xboole_0(u1_struct_0('#skF_4')) | v1_xboole_0(u1_struct_0('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_42, c_38, c_191])).
% 2.16/1.28  tff(c_193, plain, (~v1_funct_1(u1_waybel_0('#skF_4', '#skF_5'))), inference(splitLeft, [status(thm)], [c_192])).
% 2.16/1.28  tff(c_196, plain, (~l1_waybel_0('#skF_5', '#skF_4') | ~l1_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_32, c_193])).
% 2.16/1.28  tff(c_200, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_36, c_196])).
% 2.16/1.28  tff(c_201, plain, (~v1_funct_2(u1_waybel_0('#skF_4', '#skF_5'), u1_struct_0('#skF_5'), u1_struct_0('#skF_4')) | v1_xboole_0(u1_struct_0('#skF_5')) | v1_xboole_0(u1_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_192])).
% 2.16/1.28  tff(c_203, plain, (~v1_funct_2(u1_waybel_0('#skF_4', '#skF_5'), u1_struct_0('#skF_5'), u1_struct_0('#skF_4'))), inference(splitLeft, [status(thm)], [c_201])).
% 2.16/1.28  tff(c_206, plain, (~l1_waybel_0('#skF_5', '#skF_4') | ~l1_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_30, c_203])).
% 2.16/1.28  tff(c_210, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_36, c_206])).
% 2.16/1.28  tff(c_211, plain, (v1_xboole_0(u1_struct_0('#skF_4')) | v1_xboole_0(u1_struct_0('#skF_5'))), inference(splitRight, [status(thm)], [c_201])).
% 2.16/1.28  tff(c_213, plain, (v1_xboole_0(u1_struct_0('#skF_5'))), inference(splitLeft, [status(thm)], [c_211])).
% 2.16/1.28  tff(c_10, plain, (![A_22]: (~v1_xboole_0(u1_struct_0(A_22)) | ~l1_struct_0(A_22) | v2_struct_0(A_22))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.16/1.28  tff(c_217, plain, (~l1_struct_0('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_213, c_10])).
% 2.16/1.28  tff(c_220, plain, (~l1_struct_0('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_38, c_217])).
% 2.16/1.28  tff(c_223, plain, (~l1_orders_2('#skF_5')), inference(resolution, [status(thm)], [c_12, c_220])).
% 2.16/1.28  tff(c_227, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_63, c_223])).
% 2.16/1.28  tff(c_228, plain, (v1_xboole_0(u1_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_211])).
% 2.16/1.28  tff(c_232, plain, (~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_228, c_10])).
% 2.16/1.28  tff(c_235, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_232])).
% 2.16/1.28  tff(c_237, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_235])).
% 2.16/1.28  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.16/1.28  
% 2.16/1.28  Inference rules
% 2.16/1.28  ----------------------
% 2.16/1.28  #Ref     : 0
% 2.16/1.28  #Sup     : 34
% 2.16/1.28  #Fact    : 0
% 2.16/1.28  #Define  : 0
% 2.16/1.28  #Split   : 3
% 2.16/1.28  #Chain   : 0
% 2.16/1.28  #Close   : 0
% 2.16/1.28  
% 2.16/1.28  Ordering : KBO
% 2.16/1.28  
% 2.16/1.28  Simplification rules
% 2.16/1.28  ----------------------
% 2.16/1.28  #Subsume      : 8
% 2.16/1.28  #Demod        : 9
% 2.16/1.28  #Tautology    : 4
% 2.16/1.28  #SimpNegUnit  : 3
% 2.16/1.28  #BackRed      : 0
% 2.16/1.28  
% 2.16/1.28  #Partial instantiations: 0
% 2.16/1.28  #Strategies tried      : 1
% 2.16/1.28  
% 2.16/1.28  Timing (in seconds)
% 2.16/1.28  ----------------------
% 2.67/1.28  Preprocessing        : 0.29
% 2.67/1.28  Parsing              : 0.16
% 2.67/1.28  CNF conversion       : 0.03
% 2.67/1.28  Main loop            : 0.26
% 2.67/1.28  Inferencing          : 0.12
% 2.67/1.28  Reduction            : 0.06
% 2.67/1.28  Demodulation         : 0.04
% 2.67/1.28  BG Simplification    : 0.02
% 2.67/1.28  Subsumption          : 0.05
% 2.67/1.28  Abstraction          : 0.01
% 2.67/1.28  MUC search           : 0.00
% 2.67/1.28  Cooper               : 0.00
% 2.67/1.28  Total                : 0.58
% 2.67/1.28  Index Insertion      : 0.00
% 2.67/1.28  Index Deletion       : 0.00
% 2.67/1.28  Index Matching       : 0.00
% 2.67/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
