%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1935+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:42 EST 2020

% Result     : Theorem 4.78s
% Output     : CNFRefutation 4.85s
% Verified   : 
% Statistics : Number of formulae       :  122 ( 394 expanded)
%              Number of leaves         :   30 ( 156 expanded)
%              Depth                    :   18
%              Number of atoms          :  372 (1929 expanded)
%              Number of equality atoms :   10 (  60 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m3_yellow_6 > v4_relat_1 > v1_partfun1 > r2_hidden > l1_waybel_0 > v7_waybel_0 > v4_orders_2 > v2_struct_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_1 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_9 > #skF_8 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(v7_waybel_0,type,(
    v7_waybel_0: $i > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(l1_waybel_0,type,(
    l1_waybel_0: ( $i * $i ) > $o )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(m3_yellow_6,type,(
    m3_yellow_6: ( $i * $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_111,negated_conjecture,(
    ~ ! [A,B] :
        ( l1_struct_0(B)
       => ! [C] :
            ( ( v1_relat_1(C)
              & v4_relat_1(C,A)
              & v1_funct_1(C)
              & v1_partfun1(C,A) )
           => ( m3_yellow_6(C,A,B)
            <=> ! [D] :
                  ( r2_hidden(D,A)
                 => ( ~ v2_struct_0(k1_funct_1(C,D))
                    & v4_orders_2(k1_funct_1(C,D))
                    & v7_waybel_0(k1_funct_1(C,D))
                    & l1_waybel_0(k1_funct_1(C,D),B) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_yellow_6)).

tff(f_49,axiom,(
    ! [A,B] :
      ( l1_struct_0(B)
     => ! [C] :
          ( ( v1_relat_1(C)
            & v4_relat_1(C,A)
            & v1_funct_1(C)
            & v1_partfun1(C,A) )
         => ( m3_yellow_6(C,A,B)
          <=> ! [D] :
                ( r2_hidden(D,k2_relat_1(C))
               => ( ~ v2_struct_0(D)
                  & v4_orders_2(D)
                  & v7_waybel_0(D)
                  & l1_waybel_0(D,B) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d15_yellow_6)).

tff(f_57,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_72,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( B = k2_relat_1(A)
        <=> ! [C] :
              ( r2_hidden(C,B)
            <=> ? [D] :
                  ( r2_hidden(D,k1_relat_1(A))
                  & C = k1_funct_1(A,D) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).

tff(c_48,plain,(
    v4_relat_1('#skF_8','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_44,plain,(
    v1_partfun1('#skF_8','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_52,plain,(
    l1_struct_0('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_50,plain,(
    v1_relat_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_46,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_363,plain,(
    ! [A_129,B_130,C_131] :
      ( r2_hidden('#skF_1'(A_129,B_130,C_131),k2_relat_1(C_131))
      | m3_yellow_6(C_131,A_129,B_130)
      | ~ v1_partfun1(C_131,A_129)
      | ~ v1_funct_1(C_131)
      | ~ v4_relat_1(C_131,A_129)
      | ~ v1_relat_1(C_131)
      | ~ l1_struct_0(B_130) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_99,plain,(
    ! [B_82,A_83] :
      ( k1_relat_1(B_82) = A_83
      | ~ v1_partfun1(B_82,A_83)
      | ~ v4_relat_1(B_82,A_83)
      | ~ v1_relat_1(B_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_102,plain,
    ( k1_relat_1('#skF_8') = '#skF_6'
    | ~ v1_partfun1('#skF_8','#skF_6')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_48,c_99])).

tff(c_105,plain,(
    k1_relat_1('#skF_8') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_44,c_102])).

tff(c_154,plain,(
    ! [A_89,C_90] :
      ( r2_hidden('#skF_5'(A_89,k2_relat_1(A_89),C_90),k1_relat_1(A_89))
      | ~ r2_hidden(C_90,k2_relat_1(A_89))
      | ~ v1_funct_1(A_89)
      | ~ v1_relat_1(A_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_157,plain,(
    ! [C_90] :
      ( r2_hidden('#skF_5'('#skF_8',k2_relat_1('#skF_8'),C_90),'#skF_6')
      | ~ r2_hidden(C_90,k2_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_105,c_154])).

tff(c_159,plain,(
    ! [C_90] :
      ( r2_hidden('#skF_5'('#skF_8',k2_relat_1('#skF_8'),C_90),'#skF_6')
      | ~ r2_hidden(C_90,k2_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_46,c_157])).

tff(c_118,plain,(
    ! [A_87,C_88] :
      ( k1_funct_1(A_87,'#skF_5'(A_87,k2_relat_1(A_87),C_88)) = C_88
      | ~ r2_hidden(C_88,k2_relat_1(A_87))
      | ~ v1_funct_1(A_87)
      | ~ v1_relat_1(A_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_56,plain,
    ( r2_hidden('#skF_9','#skF_6')
    | ~ m3_yellow_6('#skF_8','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_83,plain,(
    ~ m3_yellow_6('#skF_8','#skF_6','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_76,plain,(
    ! [D_65] :
      ( m3_yellow_6('#skF_8','#skF_6','#skF_7')
      | v4_orders_2(k1_funct_1('#skF_8',D_65))
      | ~ r2_hidden(D_65,'#skF_6') ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_97,plain,(
    ! [D_65] :
      ( v4_orders_2(k1_funct_1('#skF_8',D_65))
      | ~ r2_hidden(D_65,'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_83,c_76])).

tff(c_132,plain,(
    ! [C_88] :
      ( v4_orders_2(C_88)
      | ~ r2_hidden('#skF_5'('#skF_8',k2_relat_1('#skF_8'),C_88),'#skF_6')
      | ~ r2_hidden(C_88,k2_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_118,c_97])).

tff(c_161,plain,(
    ! [C_92] :
      ( v4_orders_2(C_92)
      | ~ r2_hidden('#skF_5'('#skF_8',k2_relat_1('#skF_8'),C_92),'#skF_6')
      | ~ r2_hidden(C_92,k2_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_46,c_132])).

tff(c_165,plain,(
    ! [C_90] :
      ( v4_orders_2(C_90)
      | ~ r2_hidden(C_90,k2_relat_1('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_159,c_161])).

tff(c_387,plain,(
    ! [A_129,B_130] :
      ( v4_orders_2('#skF_1'(A_129,B_130,'#skF_8'))
      | m3_yellow_6('#skF_8',A_129,B_130)
      | ~ v1_partfun1('#skF_8',A_129)
      | ~ v1_funct_1('#skF_8')
      | ~ v4_relat_1('#skF_8',A_129)
      | ~ v1_relat_1('#skF_8')
      | ~ l1_struct_0(B_130) ) ),
    inference(resolution,[status(thm)],[c_363,c_165])).

tff(c_403,plain,(
    ! [A_129,B_130] :
      ( v4_orders_2('#skF_1'(A_129,B_130,'#skF_8'))
      | m3_yellow_6('#skF_8',A_129,B_130)
      | ~ v1_partfun1('#skF_8',A_129)
      | ~ v4_relat_1('#skF_8',A_129)
      | ~ l1_struct_0(B_130) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_46,c_387])).

tff(c_70,plain,(
    ! [D_65] :
      ( m3_yellow_6('#skF_8','#skF_6','#skF_7')
      | v7_waybel_0(k1_funct_1('#skF_8',D_65))
      | ~ r2_hidden(D_65,'#skF_6') ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_92,plain,(
    ! [D_65] :
      ( v7_waybel_0(k1_funct_1('#skF_8',D_65))
      | ~ r2_hidden(D_65,'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_83,c_70])).

tff(c_140,plain,(
    ! [C_88] :
      ( v7_waybel_0(C_88)
      | ~ r2_hidden('#skF_5'('#skF_8',k2_relat_1('#skF_8'),C_88),'#skF_6')
      | ~ r2_hidden(C_88,k2_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_118,c_92])).

tff(c_174,plain,(
    ! [C_94] :
      ( v7_waybel_0(C_94)
      | ~ r2_hidden('#skF_5'('#skF_8',k2_relat_1('#skF_8'),C_94),'#skF_6')
      | ~ r2_hidden(C_94,k2_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_46,c_140])).

tff(c_178,plain,(
    ! [C_90] :
      ( v7_waybel_0(C_90)
      | ~ r2_hidden(C_90,k2_relat_1('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_159,c_174])).

tff(c_383,plain,(
    ! [A_129,B_130] :
      ( v7_waybel_0('#skF_1'(A_129,B_130,'#skF_8'))
      | m3_yellow_6('#skF_8',A_129,B_130)
      | ~ v1_partfun1('#skF_8',A_129)
      | ~ v1_funct_1('#skF_8')
      | ~ v4_relat_1('#skF_8',A_129)
      | ~ v1_relat_1('#skF_8')
      | ~ l1_struct_0(B_130) ) ),
    inference(resolution,[status(thm)],[c_363,c_178])).

tff(c_400,plain,(
    ! [A_129,B_130] :
      ( v7_waybel_0('#skF_1'(A_129,B_130,'#skF_8'))
      | m3_yellow_6('#skF_8',A_129,B_130)
      | ~ v1_partfun1('#skF_8',A_129)
      | ~ v4_relat_1('#skF_8',A_129)
      | ~ l1_struct_0(B_130) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_46,c_383])).

tff(c_64,plain,(
    ! [D_65] :
      ( m3_yellow_6('#skF_8','#skF_6','#skF_7')
      | l1_waybel_0(k1_funct_1('#skF_8',D_65),'#skF_7')
      | ~ r2_hidden(D_65,'#skF_6') ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_115,plain,(
    ! [D_65] :
      ( l1_waybel_0(k1_funct_1('#skF_8',D_65),'#skF_7')
      | ~ r2_hidden(D_65,'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_83,c_64])).

tff(c_128,plain,(
    ! [C_88] :
      ( l1_waybel_0(C_88,'#skF_7')
      | ~ r2_hidden('#skF_5'('#skF_8',k2_relat_1('#skF_8'),C_88),'#skF_6')
      | ~ r2_hidden(C_88,k2_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_118,c_115])).

tff(c_200,plain,(
    ! [C_98] :
      ( l1_waybel_0(C_98,'#skF_7')
      | ~ r2_hidden('#skF_5'('#skF_8',k2_relat_1('#skF_8'),C_98),'#skF_6')
      | ~ r2_hidden(C_98,k2_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_46,c_128])).

tff(c_204,plain,(
    ! [C_90] :
      ( l1_waybel_0(C_90,'#skF_7')
      | ~ r2_hidden(C_90,k2_relat_1('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_159,c_200])).

tff(c_375,plain,(
    ! [A_129,B_130] :
      ( l1_waybel_0('#skF_1'(A_129,B_130,'#skF_8'),'#skF_7')
      | m3_yellow_6('#skF_8',A_129,B_130)
      | ~ v1_partfun1('#skF_8',A_129)
      | ~ v1_funct_1('#skF_8')
      | ~ v4_relat_1('#skF_8',A_129)
      | ~ v1_relat_1('#skF_8')
      | ~ l1_struct_0(B_130) ) ),
    inference(resolution,[status(thm)],[c_363,c_204])).

tff(c_394,plain,(
    ! [A_129,B_130] :
      ( l1_waybel_0('#skF_1'(A_129,B_130,'#skF_8'),'#skF_7')
      | m3_yellow_6('#skF_8',A_129,B_130)
      | ~ v1_partfun1('#skF_8',A_129)
      | ~ v4_relat_1('#skF_8',A_129)
      | ~ l1_struct_0(B_130) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_46,c_375])).

tff(c_549,plain,(
    ! [A_165,B_166,C_167] :
      ( ~ l1_waybel_0('#skF_1'(A_165,B_166,C_167),B_166)
      | ~ v7_waybel_0('#skF_1'(A_165,B_166,C_167))
      | ~ v4_orders_2('#skF_1'(A_165,B_166,C_167))
      | v2_struct_0('#skF_1'(A_165,B_166,C_167))
      | m3_yellow_6(C_167,A_165,B_166)
      | ~ v1_partfun1(C_167,A_165)
      | ~ v1_funct_1(C_167)
      | ~ v4_relat_1(C_167,A_165)
      | ~ v1_relat_1(C_167)
      | ~ l1_struct_0(B_166) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_553,plain,(
    ! [A_129] :
      ( ~ v7_waybel_0('#skF_1'(A_129,'#skF_7','#skF_8'))
      | ~ v4_orders_2('#skF_1'(A_129,'#skF_7','#skF_8'))
      | v2_struct_0('#skF_1'(A_129,'#skF_7','#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8')
      | m3_yellow_6('#skF_8',A_129,'#skF_7')
      | ~ v1_partfun1('#skF_8',A_129)
      | ~ v4_relat_1('#skF_8',A_129)
      | ~ l1_struct_0('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_394,c_549])).

tff(c_873,plain,(
    ! [A_175] :
      ( ~ v7_waybel_0('#skF_1'(A_175,'#skF_7','#skF_8'))
      | ~ v4_orders_2('#skF_1'(A_175,'#skF_7','#skF_8'))
      | v2_struct_0('#skF_1'(A_175,'#skF_7','#skF_8'))
      | m3_yellow_6('#skF_8',A_175,'#skF_7')
      | ~ v1_partfun1('#skF_8',A_175)
      | ~ v4_relat_1('#skF_8',A_175) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_46,c_553])).

tff(c_877,plain,(
    ! [A_129] :
      ( ~ v4_orders_2('#skF_1'(A_129,'#skF_7','#skF_8'))
      | v2_struct_0('#skF_1'(A_129,'#skF_7','#skF_8'))
      | m3_yellow_6('#skF_8',A_129,'#skF_7')
      | ~ v1_partfun1('#skF_8',A_129)
      | ~ v4_relat_1('#skF_8',A_129)
      | ~ l1_struct_0('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_400,c_873])).

tff(c_882,plain,(
    ! [A_181] :
      ( ~ v4_orders_2('#skF_1'(A_181,'#skF_7','#skF_8'))
      | v2_struct_0('#skF_1'(A_181,'#skF_7','#skF_8'))
      | m3_yellow_6('#skF_8',A_181,'#skF_7')
      | ~ v1_partfun1('#skF_8',A_181)
      | ~ v4_relat_1('#skF_8',A_181) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_877])).

tff(c_886,plain,(
    ! [A_129] :
      ( v2_struct_0('#skF_1'(A_129,'#skF_7','#skF_8'))
      | m3_yellow_6('#skF_8',A_129,'#skF_7')
      | ~ v1_partfun1('#skF_8',A_129)
      | ~ v4_relat_1('#skF_8',A_129)
      | ~ l1_struct_0('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_403,c_882])).

tff(c_890,plain,(
    ! [A_182] :
      ( v2_struct_0('#skF_1'(A_182,'#skF_7','#skF_8'))
      | m3_yellow_6('#skF_8',A_182,'#skF_7')
      | ~ v1_partfun1('#skF_8',A_182)
      | ~ v4_relat_1('#skF_8',A_182) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_886])).

tff(c_82,plain,(
    ! [D_65] :
      ( m3_yellow_6('#skF_8','#skF_6','#skF_7')
      | ~ v2_struct_0(k1_funct_1('#skF_8',D_65))
      | ~ r2_hidden(D_65,'#skF_6') ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_95,plain,(
    ! [D_65] :
      ( ~ v2_struct_0(k1_funct_1('#skF_8',D_65))
      | ~ r2_hidden(D_65,'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_83,c_82])).

tff(c_136,plain,(
    ! [C_88] :
      ( ~ v2_struct_0(C_88)
      | ~ r2_hidden('#skF_5'('#skF_8',k2_relat_1('#skF_8'),C_88),'#skF_6')
      | ~ r2_hidden(C_88,k2_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_118,c_95])).

tff(c_187,plain,(
    ! [C_96] :
      ( ~ v2_struct_0(C_96)
      | ~ r2_hidden('#skF_5'('#skF_8',k2_relat_1('#skF_8'),C_96),'#skF_6')
      | ~ r2_hidden(C_96,k2_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_46,c_136])).

tff(c_191,plain,(
    ! [C_90] :
      ( ~ v2_struct_0(C_90)
      | ~ r2_hidden(C_90,k2_relat_1('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_159,c_187])).

tff(c_379,plain,(
    ! [A_129,B_130] :
      ( ~ v2_struct_0('#skF_1'(A_129,B_130,'#skF_8'))
      | m3_yellow_6('#skF_8',A_129,B_130)
      | ~ v1_partfun1('#skF_8',A_129)
      | ~ v1_funct_1('#skF_8')
      | ~ v4_relat_1('#skF_8',A_129)
      | ~ v1_relat_1('#skF_8')
      | ~ l1_struct_0(B_130) ) ),
    inference(resolution,[status(thm)],[c_363,c_191])).

tff(c_397,plain,(
    ! [A_129,B_130] :
      ( ~ v2_struct_0('#skF_1'(A_129,B_130,'#skF_8'))
      | m3_yellow_6('#skF_8',A_129,B_130)
      | ~ v1_partfun1('#skF_8',A_129)
      | ~ v4_relat_1('#skF_8',A_129)
      | ~ l1_struct_0(B_130) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_46,c_379])).

tff(c_895,plain,(
    ! [A_182] :
      ( ~ l1_struct_0('#skF_7')
      | m3_yellow_6('#skF_8',A_182,'#skF_7')
      | ~ v1_partfun1('#skF_8',A_182)
      | ~ v4_relat_1('#skF_8',A_182) ) ),
    inference(resolution,[status(thm)],[c_890,c_397])).

tff(c_902,plain,(
    ! [A_183] :
      ( m3_yellow_6('#skF_8',A_183,'#skF_7')
      | ~ v1_partfun1('#skF_8',A_183)
      | ~ v4_relat_1('#skF_8',A_183) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_895])).

tff(c_925,plain,
    ( ~ v1_partfun1('#skF_8','#skF_6')
    | ~ v4_relat_1('#skF_8','#skF_6') ),
    inference(resolution,[status(thm)],[c_902,c_83])).

tff(c_953,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_44,c_925])).

tff(c_954,plain,(
    r2_hidden('#skF_9','#skF_6') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_991,plain,(
    ! [B_197,A_198] :
      ( k1_relat_1(B_197) = A_198
      | ~ v1_partfun1(B_197,A_198)
      | ~ v4_relat_1(B_197,A_198)
      | ~ v1_relat_1(B_197) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_994,plain,
    ( k1_relat_1('#skF_8') = '#skF_6'
    | ~ v1_partfun1('#skF_8','#skF_6')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_48,c_991])).

tff(c_997,plain,(
    k1_relat_1('#skF_8') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_44,c_994])).

tff(c_955,plain,(
    m3_yellow_6('#skF_8','#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_18,plain,(
    ! [A_14,D_53] :
      ( r2_hidden(k1_funct_1(A_14,D_53),k2_relat_1(A_14))
      | ~ r2_hidden(D_53,k1_relat_1(A_14))
      | ~ v1_funct_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_1900,plain,(
    ! [D_411,C_412,A_413,B_414] :
      ( v7_waybel_0(D_411)
      | ~ r2_hidden(D_411,k2_relat_1(C_412))
      | ~ m3_yellow_6(C_412,A_413,B_414)
      | ~ v1_partfun1(C_412,A_413)
      | ~ v1_funct_1(C_412)
      | ~ v4_relat_1(C_412,A_413)
      | ~ v1_relat_1(C_412)
      | ~ l1_struct_0(B_414) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1986,plain,(
    ! [A_433,D_434,A_435,B_436] :
      ( v7_waybel_0(k1_funct_1(A_433,D_434))
      | ~ m3_yellow_6(A_433,A_435,B_436)
      | ~ v1_partfun1(A_433,A_435)
      | ~ v4_relat_1(A_433,A_435)
      | ~ l1_struct_0(B_436)
      | ~ r2_hidden(D_434,k1_relat_1(A_433))
      | ~ v1_funct_1(A_433)
      | ~ v1_relat_1(A_433) ) ),
    inference(resolution,[status(thm)],[c_18,c_1900])).

tff(c_1988,plain,(
    ! [D_434] :
      ( v7_waybel_0(k1_funct_1('#skF_8',D_434))
      | ~ v1_partfun1('#skF_8','#skF_6')
      | ~ v4_relat_1('#skF_8','#skF_6')
      | ~ l1_struct_0('#skF_7')
      | ~ r2_hidden(D_434,k1_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_955,c_1986])).

tff(c_1994,plain,(
    ! [D_437] :
      ( v7_waybel_0(k1_funct_1('#skF_8',D_437))
      | ~ r2_hidden(D_437,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_46,c_997,c_52,c_48,c_44,c_1988])).

tff(c_1592,plain,(
    ! [D_353,B_354,C_355,A_356] :
      ( l1_waybel_0(D_353,B_354)
      | ~ r2_hidden(D_353,k2_relat_1(C_355))
      | ~ m3_yellow_6(C_355,A_356,B_354)
      | ~ v1_partfun1(C_355,A_356)
      | ~ v1_funct_1(C_355)
      | ~ v4_relat_1(C_355,A_356)
      | ~ v1_relat_1(C_355)
      | ~ l1_struct_0(B_354) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1843,plain,(
    ! [A_393,D_394,B_395,A_396] :
      ( l1_waybel_0(k1_funct_1(A_393,D_394),B_395)
      | ~ m3_yellow_6(A_393,A_396,B_395)
      | ~ v1_partfun1(A_393,A_396)
      | ~ v4_relat_1(A_393,A_396)
      | ~ l1_struct_0(B_395)
      | ~ r2_hidden(D_394,k1_relat_1(A_393))
      | ~ v1_funct_1(A_393)
      | ~ v1_relat_1(A_393) ) ),
    inference(resolution,[status(thm)],[c_18,c_1592])).

tff(c_1845,plain,(
    ! [D_394] :
      ( l1_waybel_0(k1_funct_1('#skF_8',D_394),'#skF_7')
      | ~ v1_partfun1('#skF_8','#skF_6')
      | ~ v4_relat_1('#skF_8','#skF_6')
      | ~ l1_struct_0('#skF_7')
      | ~ r2_hidden(D_394,k1_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_955,c_1843])).

tff(c_1849,plain,(
    ! [D_397] :
      ( l1_waybel_0(k1_funct_1('#skF_8',D_397),'#skF_7')
      | ~ r2_hidden(D_397,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_46,c_997,c_52,c_48,c_44,c_1845])).

tff(c_1085,plain,(
    ! [D_221,C_222,A_223,B_224] :
      ( v4_orders_2(D_221)
      | ~ r2_hidden(D_221,k2_relat_1(C_222))
      | ~ m3_yellow_6(C_222,A_223,B_224)
      | ~ v1_partfun1(C_222,A_223)
      | ~ v1_funct_1(C_222)
      | ~ v4_relat_1(C_222,A_223)
      | ~ v1_relat_1(C_222)
      | ~ l1_struct_0(B_224) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1186,plain,(
    ! [A_248,D_249,A_250,B_251] :
      ( v4_orders_2(k1_funct_1(A_248,D_249))
      | ~ m3_yellow_6(A_248,A_250,B_251)
      | ~ v1_partfun1(A_248,A_250)
      | ~ v4_relat_1(A_248,A_250)
      | ~ l1_struct_0(B_251)
      | ~ r2_hidden(D_249,k1_relat_1(A_248))
      | ~ v1_funct_1(A_248)
      | ~ v1_relat_1(A_248) ) ),
    inference(resolution,[status(thm)],[c_18,c_1085])).

tff(c_1188,plain,(
    ! [D_249] :
      ( v4_orders_2(k1_funct_1('#skF_8',D_249))
      | ~ v1_partfun1('#skF_8','#skF_6')
      | ~ v4_relat_1('#skF_8','#skF_6')
      | ~ l1_struct_0('#skF_7')
      | ~ r2_hidden(D_249,k1_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_955,c_1186])).

tff(c_1197,plain,(
    ! [D_255] :
      ( v4_orders_2(k1_funct_1('#skF_8',D_255))
      | ~ r2_hidden(D_255,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_46,c_997,c_52,c_48,c_44,c_1188])).

tff(c_54,plain,
    ( ~ l1_waybel_0(k1_funct_1('#skF_8','#skF_9'),'#skF_7')
    | ~ v7_waybel_0(k1_funct_1('#skF_8','#skF_9'))
    | ~ v4_orders_2(k1_funct_1('#skF_8','#skF_9'))
    | v2_struct_0(k1_funct_1('#skF_8','#skF_9'))
    | ~ m3_yellow_6('#skF_8','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_1024,plain,
    ( ~ l1_waybel_0(k1_funct_1('#skF_8','#skF_9'),'#skF_7')
    | ~ v7_waybel_0(k1_funct_1('#skF_8','#skF_9'))
    | ~ v4_orders_2(k1_funct_1('#skF_8','#skF_9'))
    | v2_struct_0(k1_funct_1('#skF_8','#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_955,c_54])).

tff(c_1025,plain,(
    ~ v4_orders_2(k1_funct_1('#skF_8','#skF_9')) ),
    inference(splitLeft,[status(thm)],[c_1024])).

tff(c_1200,plain,(
    ~ r2_hidden('#skF_9','#skF_6') ),
    inference(resolution,[status(thm)],[c_1197,c_1025])).

tff(c_1210,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_954,c_1200])).

tff(c_1211,plain,
    ( ~ v7_waybel_0(k1_funct_1('#skF_8','#skF_9'))
    | ~ l1_waybel_0(k1_funct_1('#skF_8','#skF_9'),'#skF_7')
    | v2_struct_0(k1_funct_1('#skF_8','#skF_9')) ),
    inference(splitRight,[status(thm)],[c_1024])).

tff(c_1213,plain,(
    ~ l1_waybel_0(k1_funct_1('#skF_8','#skF_9'),'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_1211])).

tff(c_1852,plain,(
    ~ r2_hidden('#skF_9','#skF_6') ),
    inference(resolution,[status(thm)],[c_1849,c_1213])).

tff(c_1866,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_954,c_1852])).

tff(c_1867,plain,
    ( ~ v7_waybel_0(k1_funct_1('#skF_8','#skF_9'))
    | v2_struct_0(k1_funct_1('#skF_8','#skF_9')) ),
    inference(splitRight,[status(thm)],[c_1211])).

tff(c_1869,plain,(
    ~ v7_waybel_0(k1_funct_1('#skF_8','#skF_9')) ),
    inference(splitLeft,[status(thm)],[c_1867])).

tff(c_1997,plain,(
    ~ r2_hidden('#skF_9','#skF_6') ),
    inference(resolution,[status(thm)],[c_1994,c_1869])).

tff(c_2007,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_954,c_1997])).

tff(c_2008,plain,(
    v2_struct_0(k1_funct_1('#skF_8','#skF_9')) ),
    inference(splitRight,[status(thm)],[c_1867])).

tff(c_2055,plain,(
    ! [D_452,C_453,A_454,B_455] :
      ( ~ v2_struct_0(D_452)
      | ~ r2_hidden(D_452,k2_relat_1(C_453))
      | ~ m3_yellow_6(C_453,A_454,B_455)
      | ~ v1_partfun1(C_453,A_454)
      | ~ v1_funct_1(C_453)
      | ~ v4_relat_1(C_453,A_454)
      | ~ v1_relat_1(C_453)
      | ~ l1_struct_0(B_455) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_2304,plain,(
    ! [A_499,D_500,A_501,B_502] :
      ( ~ v2_struct_0(k1_funct_1(A_499,D_500))
      | ~ m3_yellow_6(A_499,A_501,B_502)
      | ~ v1_partfun1(A_499,A_501)
      | ~ v4_relat_1(A_499,A_501)
      | ~ l1_struct_0(B_502)
      | ~ r2_hidden(D_500,k1_relat_1(A_499))
      | ~ v1_funct_1(A_499)
      | ~ v1_relat_1(A_499) ) ),
    inference(resolution,[status(thm)],[c_18,c_2055])).

tff(c_2306,plain,(
    ! [D_500] :
      ( ~ v2_struct_0(k1_funct_1('#skF_8',D_500))
      | ~ v1_partfun1('#skF_8','#skF_6')
      | ~ v4_relat_1('#skF_8','#skF_6')
      | ~ l1_struct_0('#skF_7')
      | ~ r2_hidden(D_500,k1_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_955,c_2304])).

tff(c_2310,plain,(
    ! [D_503] :
      ( ~ v2_struct_0(k1_funct_1('#skF_8',D_503))
      | ~ r2_hidden(D_503,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_46,c_997,c_52,c_48,c_44,c_2306])).

tff(c_2319,plain,(
    ~ r2_hidden('#skF_9','#skF_6') ),
    inference(resolution,[status(thm)],[c_2008,c_2310])).

tff(c_2327,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_954,c_2319])).

%------------------------------------------------------------------------------
