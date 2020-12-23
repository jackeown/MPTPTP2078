%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:53 EST 2020

% Result     : Theorem 4.88s
% Output     : CNFRefutation 4.88s
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
%$ m3_yellow_6 > v4_relat_1 > v1_partfun1 > r2_hidden > l1_waybel_0 > v7_waybel_0 > v4_orders_2 > v2_struct_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_4 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_9 > #skF_8 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(v7_waybel_0,type,(
    v7_waybel_0: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_112,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_yellow_6)).

tff(f_73,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d15_yellow_6)).

tff(f_48,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_40,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).

tff(c_48,plain,(
    v4_relat_1('#skF_8','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_44,plain,(
    v1_partfun1('#skF_8','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_52,plain,(
    l1_struct_0('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_50,plain,(
    v1_relat_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_46,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_418,plain,(
    ! [A_130,B_131,C_132] :
      ( r2_hidden('#skF_5'(A_130,B_131,C_132),k2_relat_1(C_132))
      | m3_yellow_6(C_132,A_130,B_131)
      | ~ v1_partfun1(C_132,A_130)
      | ~ v1_funct_1(C_132)
      | ~ v4_relat_1(C_132,A_130)
      | ~ v1_relat_1(C_132)
      | ~ l1_struct_0(B_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_92,plain,(
    ! [B_79,A_80] :
      ( k1_relat_1(B_79) = A_80
      | ~ v1_partfun1(B_79,A_80)
      | ~ v4_relat_1(B_79,A_80)
      | ~ v1_relat_1(B_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_95,plain,
    ( k1_relat_1('#skF_8') = '#skF_6'
    | ~ v1_partfun1('#skF_8','#skF_6')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_48,c_92])).

tff(c_98,plain,(
    k1_relat_1('#skF_8') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_44,c_95])).

tff(c_118,plain,(
    ! [A_87,C_88] :
      ( r2_hidden('#skF_4'(A_87,k2_relat_1(A_87),C_88),k1_relat_1(A_87))
      | ~ r2_hidden(C_88,k2_relat_1(A_87))
      | ~ v1_funct_1(A_87)
      | ~ v1_relat_1(A_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_121,plain,(
    ! [C_88] :
      ( r2_hidden('#skF_4'('#skF_8',k2_relat_1('#skF_8'),C_88),'#skF_6')
      | ~ r2_hidden(C_88,k2_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_98,c_118])).

tff(c_123,plain,(
    ! [C_88] :
      ( r2_hidden('#skF_4'('#skF_8',k2_relat_1('#skF_8'),C_88),'#skF_6')
      | ~ r2_hidden(C_88,k2_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_46,c_121])).

tff(c_124,plain,(
    ! [A_89,C_90] :
      ( k1_funct_1(A_89,'#skF_4'(A_89,k2_relat_1(A_89),C_90)) = C_90
      | ~ r2_hidden(C_90,k2_relat_1(A_89))
      | ~ v1_funct_1(A_89)
      | ~ v1_relat_1(A_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_56,plain,
    ( r2_hidden('#skF_9','#skF_6')
    | ~ m3_yellow_6('#skF_8','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_83,plain,(
    ~ m3_yellow_6('#skF_8','#skF_6','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_76,plain,(
    ! [D_65] :
      ( m3_yellow_6('#skF_8','#skF_6','#skF_7')
      | v4_orders_2(k1_funct_1('#skF_8',D_65))
      | ~ r2_hidden(D_65,'#skF_6') ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_108,plain,(
    ! [D_65] :
      ( v4_orders_2(k1_funct_1('#skF_8',D_65))
      | ~ r2_hidden(D_65,'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_83,c_76])).

tff(c_146,plain,(
    ! [C_90] :
      ( v4_orders_2(C_90)
      | ~ r2_hidden('#skF_4'('#skF_8',k2_relat_1('#skF_8'),C_90),'#skF_6')
      | ~ r2_hidden(C_90,k2_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_124,c_108])).

tff(c_187,plain,(
    ! [C_96] :
      ( v4_orders_2(C_96)
      | ~ r2_hidden('#skF_4'('#skF_8',k2_relat_1('#skF_8'),C_96),'#skF_6')
      | ~ r2_hidden(C_96,k2_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_46,c_146])).

tff(c_191,plain,(
    ! [C_88] :
      ( v4_orders_2(C_88)
      | ~ r2_hidden(C_88,k2_relat_1('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_123,c_187])).

tff(c_432,plain,(
    ! [A_130,B_131] :
      ( v4_orders_2('#skF_5'(A_130,B_131,'#skF_8'))
      | m3_yellow_6('#skF_8',A_130,B_131)
      | ~ v1_partfun1('#skF_8',A_130)
      | ~ v1_funct_1('#skF_8')
      | ~ v4_relat_1('#skF_8',A_130)
      | ~ v1_relat_1('#skF_8')
      | ~ l1_struct_0(B_131) ) ),
    inference(resolution,[status(thm)],[c_418,c_191])).

tff(c_449,plain,(
    ! [A_130,B_131] :
      ( v4_orders_2('#skF_5'(A_130,B_131,'#skF_8'))
      | m3_yellow_6('#skF_8',A_130,B_131)
      | ~ v1_partfun1('#skF_8',A_130)
      | ~ v4_relat_1('#skF_8',A_130)
      | ~ l1_struct_0(B_131) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_46,c_432])).

tff(c_70,plain,(
    ! [D_65] :
      ( m3_yellow_6('#skF_8','#skF_6','#skF_7')
      | v7_waybel_0(k1_funct_1('#skF_8',D_65))
      | ~ r2_hidden(D_65,'#skF_6') ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_110,plain,(
    ! [D_65] :
      ( v7_waybel_0(k1_funct_1('#skF_8',D_65))
      | ~ r2_hidden(D_65,'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_83,c_70])).

tff(c_142,plain,(
    ! [C_90] :
      ( v7_waybel_0(C_90)
      | ~ r2_hidden('#skF_4'('#skF_8',k2_relat_1('#skF_8'),C_90),'#skF_6')
      | ~ r2_hidden(C_90,k2_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_124,c_110])).

tff(c_174,plain,(
    ! [C_94] :
      ( v7_waybel_0(C_94)
      | ~ r2_hidden('#skF_4'('#skF_8',k2_relat_1('#skF_8'),C_94),'#skF_6')
      | ~ r2_hidden(C_94,k2_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_46,c_142])).

tff(c_178,plain,(
    ! [C_88] :
      ( v7_waybel_0(C_88)
      | ~ r2_hidden(C_88,k2_relat_1('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_123,c_174])).

tff(c_436,plain,(
    ! [A_130,B_131] :
      ( v7_waybel_0('#skF_5'(A_130,B_131,'#skF_8'))
      | m3_yellow_6('#skF_8',A_130,B_131)
      | ~ v1_partfun1('#skF_8',A_130)
      | ~ v1_funct_1('#skF_8')
      | ~ v4_relat_1('#skF_8',A_130)
      | ~ v1_relat_1('#skF_8')
      | ~ l1_struct_0(B_131) ) ),
    inference(resolution,[status(thm)],[c_418,c_178])).

tff(c_452,plain,(
    ! [A_130,B_131] :
      ( v7_waybel_0('#skF_5'(A_130,B_131,'#skF_8'))
      | m3_yellow_6('#skF_8',A_130,B_131)
      | ~ v1_partfun1('#skF_8',A_130)
      | ~ v4_relat_1('#skF_8',A_130)
      | ~ l1_struct_0(B_131) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_46,c_436])).

tff(c_64,plain,(
    ! [D_65] :
      ( m3_yellow_6('#skF_8','#skF_6','#skF_7')
      | l1_waybel_0(k1_funct_1('#skF_8',D_65),'#skF_7')
      | ~ r2_hidden(D_65,'#skF_6') ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_115,plain,(
    ! [D_65] :
      ( l1_waybel_0(k1_funct_1('#skF_8',D_65),'#skF_7')
      | ~ r2_hidden(D_65,'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_83,c_64])).

tff(c_134,plain,(
    ! [C_90] :
      ( l1_waybel_0(C_90,'#skF_7')
      | ~ r2_hidden('#skF_4'('#skF_8',k2_relat_1('#skF_8'),C_90),'#skF_6')
      | ~ r2_hidden(C_90,k2_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_124,c_115])).

tff(c_200,plain,(
    ! [C_98] :
      ( l1_waybel_0(C_98,'#skF_7')
      | ~ r2_hidden('#skF_4'('#skF_8',k2_relat_1('#skF_8'),C_98),'#skF_6')
      | ~ r2_hidden(C_98,k2_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_46,c_134])).

tff(c_204,plain,(
    ! [C_88] :
      ( l1_waybel_0(C_88,'#skF_7')
      | ~ r2_hidden(C_88,k2_relat_1('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_123,c_200])).

tff(c_428,plain,(
    ! [A_130,B_131] :
      ( l1_waybel_0('#skF_5'(A_130,B_131,'#skF_8'),'#skF_7')
      | m3_yellow_6('#skF_8',A_130,B_131)
      | ~ v1_partfun1('#skF_8',A_130)
      | ~ v1_funct_1('#skF_8')
      | ~ v4_relat_1('#skF_8',A_130)
      | ~ v1_relat_1('#skF_8')
      | ~ l1_struct_0(B_131) ) ),
    inference(resolution,[status(thm)],[c_418,c_204])).

tff(c_446,plain,(
    ! [A_130,B_131] :
      ( l1_waybel_0('#skF_5'(A_130,B_131,'#skF_8'),'#skF_7')
      | m3_yellow_6('#skF_8',A_130,B_131)
      | ~ v1_partfun1('#skF_8',A_130)
      | ~ v4_relat_1('#skF_8',A_130)
      | ~ l1_struct_0(B_131) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_46,c_428])).

tff(c_768,plain,(
    ! [A_176,B_177,C_178] :
      ( ~ l1_waybel_0('#skF_5'(A_176,B_177,C_178),B_177)
      | ~ v7_waybel_0('#skF_5'(A_176,B_177,C_178))
      | ~ v4_orders_2('#skF_5'(A_176,B_177,C_178))
      | v2_struct_0('#skF_5'(A_176,B_177,C_178))
      | m3_yellow_6(C_178,A_176,B_177)
      | ~ v1_partfun1(C_178,A_176)
      | ~ v1_funct_1(C_178)
      | ~ v4_relat_1(C_178,A_176)
      | ~ v1_relat_1(C_178)
      | ~ l1_struct_0(B_177) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_772,plain,(
    ! [A_130] :
      ( ~ v7_waybel_0('#skF_5'(A_130,'#skF_7','#skF_8'))
      | ~ v4_orders_2('#skF_5'(A_130,'#skF_7','#skF_8'))
      | v2_struct_0('#skF_5'(A_130,'#skF_7','#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8')
      | m3_yellow_6('#skF_8',A_130,'#skF_7')
      | ~ v1_partfun1('#skF_8',A_130)
      | ~ v4_relat_1('#skF_8',A_130)
      | ~ l1_struct_0('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_446,c_768])).

tff(c_1321,plain,(
    ! [A_187] :
      ( ~ v7_waybel_0('#skF_5'(A_187,'#skF_7','#skF_8'))
      | ~ v4_orders_2('#skF_5'(A_187,'#skF_7','#skF_8'))
      | v2_struct_0('#skF_5'(A_187,'#skF_7','#skF_8'))
      | m3_yellow_6('#skF_8',A_187,'#skF_7')
      | ~ v1_partfun1('#skF_8',A_187)
      | ~ v4_relat_1('#skF_8',A_187) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_46,c_772])).

tff(c_1325,plain,(
    ! [A_130] :
      ( ~ v4_orders_2('#skF_5'(A_130,'#skF_7','#skF_8'))
      | v2_struct_0('#skF_5'(A_130,'#skF_7','#skF_8'))
      | m3_yellow_6('#skF_8',A_130,'#skF_7')
      | ~ v1_partfun1('#skF_8',A_130)
      | ~ v4_relat_1('#skF_8',A_130)
      | ~ l1_struct_0('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_452,c_1321])).

tff(c_1330,plain,(
    ! [A_193] :
      ( ~ v4_orders_2('#skF_5'(A_193,'#skF_7','#skF_8'))
      | v2_struct_0('#skF_5'(A_193,'#skF_7','#skF_8'))
      | m3_yellow_6('#skF_8',A_193,'#skF_7')
      | ~ v1_partfun1('#skF_8',A_193)
      | ~ v4_relat_1('#skF_8',A_193) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_1325])).

tff(c_1334,plain,(
    ! [A_130] :
      ( v2_struct_0('#skF_5'(A_130,'#skF_7','#skF_8'))
      | m3_yellow_6('#skF_8',A_130,'#skF_7')
      | ~ v1_partfun1('#skF_8',A_130)
      | ~ v4_relat_1('#skF_8',A_130)
      | ~ l1_struct_0('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_449,c_1330])).

tff(c_1338,plain,(
    ! [A_194] :
      ( v2_struct_0('#skF_5'(A_194,'#skF_7','#skF_8'))
      | m3_yellow_6('#skF_8',A_194,'#skF_7')
      | ~ v1_partfun1('#skF_8',A_194)
      | ~ v4_relat_1('#skF_8',A_194) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_1334])).

tff(c_82,plain,(
    ! [D_65] :
      ( m3_yellow_6('#skF_8','#skF_6','#skF_7')
      | ~ v2_struct_0(k1_funct_1('#skF_8',D_65))
      | ~ r2_hidden(D_65,'#skF_6') ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_112,plain,(
    ! [D_65] :
      ( ~ v2_struct_0(k1_funct_1('#skF_8',D_65))
      | ~ r2_hidden(D_65,'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_83,c_82])).

tff(c_138,plain,(
    ! [C_90] :
      ( ~ v2_struct_0(C_90)
      | ~ r2_hidden('#skF_4'('#skF_8',k2_relat_1('#skF_8'),C_90),'#skF_6')
      | ~ r2_hidden(C_90,k2_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_124,c_112])).

tff(c_161,plain,(
    ! [C_92] :
      ( ~ v2_struct_0(C_92)
      | ~ r2_hidden('#skF_4'('#skF_8',k2_relat_1('#skF_8'),C_92),'#skF_6')
      | ~ r2_hidden(C_92,k2_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_46,c_138])).

tff(c_165,plain,(
    ! [C_88] :
      ( ~ v2_struct_0(C_88)
      | ~ r2_hidden(C_88,k2_relat_1('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_123,c_161])).

tff(c_440,plain,(
    ! [A_130,B_131] :
      ( ~ v2_struct_0('#skF_5'(A_130,B_131,'#skF_8'))
      | m3_yellow_6('#skF_8',A_130,B_131)
      | ~ v1_partfun1('#skF_8',A_130)
      | ~ v1_funct_1('#skF_8')
      | ~ v4_relat_1('#skF_8',A_130)
      | ~ v1_relat_1('#skF_8')
      | ~ l1_struct_0(B_131) ) ),
    inference(resolution,[status(thm)],[c_418,c_165])).

tff(c_455,plain,(
    ! [A_130,B_131] :
      ( ~ v2_struct_0('#skF_5'(A_130,B_131,'#skF_8'))
      | m3_yellow_6('#skF_8',A_130,B_131)
      | ~ v1_partfun1('#skF_8',A_130)
      | ~ v4_relat_1('#skF_8',A_130)
      | ~ l1_struct_0(B_131) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_46,c_440])).

tff(c_1341,plain,(
    ! [A_194] :
      ( ~ l1_struct_0('#skF_7')
      | m3_yellow_6('#skF_8',A_194,'#skF_7')
      | ~ v1_partfun1('#skF_8',A_194)
      | ~ v4_relat_1('#skF_8',A_194) ) ),
    inference(resolution,[status(thm)],[c_1338,c_455])).

tff(c_1345,plain,(
    ! [A_195] :
      ( m3_yellow_6('#skF_8',A_195,'#skF_7')
      | ~ v1_partfun1('#skF_8',A_195)
      | ~ v4_relat_1('#skF_8',A_195) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_1341])).

tff(c_1370,plain,
    ( ~ v1_partfun1('#skF_8','#skF_6')
    | ~ v4_relat_1('#skF_8','#skF_6') ),
    inference(resolution,[status(thm)],[c_1345,c_83])).

tff(c_1401,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_44,c_1370])).

tff(c_1402,plain,(
    r2_hidden('#skF_9','#skF_6') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_1439,plain,(
    ! [B_209,A_210] :
      ( k1_relat_1(B_209) = A_210
      | ~ v1_partfun1(B_209,A_210)
      | ~ v4_relat_1(B_209,A_210)
      | ~ v1_relat_1(B_209) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_1442,plain,
    ( k1_relat_1('#skF_8') = '#skF_6'
    | ~ v1_partfun1('#skF_8','#skF_6')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_48,c_1439])).

tff(c_1445,plain,(
    k1_relat_1('#skF_8') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_44,c_1442])).

tff(c_1403,plain,(
    m3_yellow_6('#skF_8','#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_2,plain,(
    ! [A_1,D_40] :
      ( r2_hidden(k1_funct_1(A_1,D_40),k2_relat_1(A_1))
      | ~ r2_hidden(D_40,k1_relat_1(A_1))
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_2183,plain,(
    ! [D_371,C_372,A_373,B_374] :
      ( v7_waybel_0(D_371)
      | ~ r2_hidden(D_371,k2_relat_1(C_372))
      | ~ m3_yellow_6(C_372,A_373,B_374)
      | ~ v1_partfun1(C_372,A_373)
      | ~ v1_funct_1(C_372)
      | ~ v4_relat_1(C_372,A_373)
      | ~ v1_relat_1(C_372)
      | ~ l1_struct_0(B_374) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_2284,plain,(
    ! [A_396,D_397,A_398,B_399] :
      ( v7_waybel_0(k1_funct_1(A_396,D_397))
      | ~ m3_yellow_6(A_396,A_398,B_399)
      | ~ v1_partfun1(A_396,A_398)
      | ~ v4_relat_1(A_396,A_398)
      | ~ l1_struct_0(B_399)
      | ~ r2_hidden(D_397,k1_relat_1(A_396))
      | ~ v1_funct_1(A_396)
      | ~ v1_relat_1(A_396) ) ),
    inference(resolution,[status(thm)],[c_2,c_2183])).

tff(c_2286,plain,(
    ! [D_397] :
      ( v7_waybel_0(k1_funct_1('#skF_8',D_397))
      | ~ v1_partfun1('#skF_8','#skF_6')
      | ~ v4_relat_1('#skF_8','#skF_6')
      | ~ l1_struct_0('#skF_7')
      | ~ r2_hidden(D_397,k1_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_1403,c_2284])).

tff(c_2290,plain,(
    ! [D_400] :
      ( v7_waybel_0(k1_funct_1('#skF_8',D_400))
      | ~ r2_hidden(D_400,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_46,c_1445,c_52,c_48,c_44,c_2286])).

tff(c_1807,plain,(
    ! [D_301,B_302,C_303,A_304] :
      ( l1_waybel_0(D_301,B_302)
      | ~ r2_hidden(D_301,k2_relat_1(C_303))
      | ~ m3_yellow_6(C_303,A_304,B_302)
      | ~ v1_partfun1(C_303,A_304)
      | ~ v1_funct_1(C_303)
      | ~ v4_relat_1(C_303,A_304)
      | ~ v1_relat_1(C_303)
      | ~ l1_struct_0(B_302) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_2125,plain,(
    ! [A_356,D_357,B_358,A_359] :
      ( l1_waybel_0(k1_funct_1(A_356,D_357),B_358)
      | ~ m3_yellow_6(A_356,A_359,B_358)
      | ~ v1_partfun1(A_356,A_359)
      | ~ v4_relat_1(A_356,A_359)
      | ~ l1_struct_0(B_358)
      | ~ r2_hidden(D_357,k1_relat_1(A_356))
      | ~ v1_funct_1(A_356)
      | ~ v1_relat_1(A_356) ) ),
    inference(resolution,[status(thm)],[c_2,c_1807])).

tff(c_2127,plain,(
    ! [D_357] :
      ( l1_waybel_0(k1_funct_1('#skF_8',D_357),'#skF_7')
      | ~ v1_partfun1('#skF_8','#skF_6')
      | ~ v4_relat_1('#skF_8','#skF_6')
      | ~ l1_struct_0('#skF_7')
      | ~ r2_hidden(D_357,k1_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_1403,c_2125])).

tff(c_2131,plain,(
    ! [D_360] :
      ( l1_waybel_0(k1_funct_1('#skF_8',D_360),'#skF_7')
      | ~ r2_hidden(D_360,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_46,c_1445,c_52,c_48,c_44,c_2127])).

tff(c_1542,plain,(
    ! [D_236,C_237,A_238,B_239] :
      ( v4_orders_2(D_236)
      | ~ r2_hidden(D_236,k2_relat_1(C_237))
      | ~ m3_yellow_6(C_237,A_238,B_239)
      | ~ v1_partfun1(C_237,A_238)
      | ~ v1_funct_1(C_237)
      | ~ v4_relat_1(C_237,A_238)
      | ~ v1_relat_1(C_237)
      | ~ l1_struct_0(B_239) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1671,plain,(
    ! [A_265,D_266,A_267,B_268] :
      ( v4_orders_2(k1_funct_1(A_265,D_266))
      | ~ m3_yellow_6(A_265,A_267,B_268)
      | ~ v1_partfun1(A_265,A_267)
      | ~ v4_relat_1(A_265,A_267)
      | ~ l1_struct_0(B_268)
      | ~ r2_hidden(D_266,k1_relat_1(A_265))
      | ~ v1_funct_1(A_265)
      | ~ v1_relat_1(A_265) ) ),
    inference(resolution,[status(thm)],[c_2,c_1542])).

tff(c_1673,plain,(
    ! [D_266] :
      ( v4_orders_2(k1_funct_1('#skF_8',D_266))
      | ~ v1_partfun1('#skF_8','#skF_6')
      | ~ v4_relat_1('#skF_8','#skF_6')
      | ~ l1_struct_0('#skF_7')
      | ~ r2_hidden(D_266,k1_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_1403,c_1671])).

tff(c_1677,plain,(
    ! [D_269] :
      ( v4_orders_2(k1_funct_1('#skF_8',D_269))
      | ~ r2_hidden(D_269,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_46,c_1445,c_52,c_48,c_44,c_1673])).

tff(c_54,plain,
    ( ~ l1_waybel_0(k1_funct_1('#skF_8','#skF_9'),'#skF_7')
    | ~ v7_waybel_0(k1_funct_1('#skF_8','#skF_9'))
    | ~ v4_orders_2(k1_funct_1('#skF_8','#skF_9'))
    | v2_struct_0(k1_funct_1('#skF_8','#skF_9'))
    | ~ m3_yellow_6('#skF_8','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_1472,plain,
    ( ~ l1_waybel_0(k1_funct_1('#skF_8','#skF_9'),'#skF_7')
    | ~ v7_waybel_0(k1_funct_1('#skF_8','#skF_9'))
    | ~ v4_orders_2(k1_funct_1('#skF_8','#skF_9'))
    | v2_struct_0(k1_funct_1('#skF_8','#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1403,c_54])).

tff(c_1473,plain,(
    ~ v4_orders_2(k1_funct_1('#skF_8','#skF_9')) ),
    inference(splitLeft,[status(thm)],[c_1472])).

tff(c_1680,plain,(
    ~ r2_hidden('#skF_9','#skF_6') ),
    inference(resolution,[status(thm)],[c_1677,c_1473])).

tff(c_1690,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1402,c_1680])).

tff(c_1691,plain,
    ( ~ v7_waybel_0(k1_funct_1('#skF_8','#skF_9'))
    | ~ l1_waybel_0(k1_funct_1('#skF_8','#skF_9'),'#skF_7')
    | v2_struct_0(k1_funct_1('#skF_8','#skF_9')) ),
    inference(splitRight,[status(thm)],[c_1472])).

tff(c_1699,plain,(
    ~ l1_waybel_0(k1_funct_1('#skF_8','#skF_9'),'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_1691])).

tff(c_2134,plain,(
    ~ r2_hidden('#skF_9','#skF_6') ),
    inference(resolution,[status(thm)],[c_2131,c_1699])).

tff(c_2148,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1402,c_2134])).

tff(c_2149,plain,
    ( ~ v7_waybel_0(k1_funct_1('#skF_8','#skF_9'))
    | v2_struct_0(k1_funct_1('#skF_8','#skF_9')) ),
    inference(splitRight,[status(thm)],[c_1691])).

tff(c_2151,plain,(
    ~ v7_waybel_0(k1_funct_1('#skF_8','#skF_9')) ),
    inference(splitLeft,[status(thm)],[c_2149])).

tff(c_2293,plain,(
    ~ r2_hidden('#skF_9','#skF_6') ),
    inference(resolution,[status(thm)],[c_2290,c_2151])).

tff(c_2303,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1402,c_2293])).

tff(c_2304,plain,(
    v2_struct_0(k1_funct_1('#skF_8','#skF_9')) ),
    inference(splitRight,[status(thm)],[c_2149])).

tff(c_2377,plain,(
    ! [D_419,C_420,A_421,B_422] :
      ( ~ v2_struct_0(D_419)
      | ~ r2_hidden(D_419,k2_relat_1(C_420))
      | ~ m3_yellow_6(C_420,A_421,B_422)
      | ~ v1_partfun1(C_420,A_421)
      | ~ v1_funct_1(C_420)
      | ~ v4_relat_1(C_420,A_421)
      | ~ v1_relat_1(C_420)
      | ~ l1_struct_0(B_422) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_2655,plain,(
    ! [A_469,D_470,A_471,B_472] :
      ( ~ v2_struct_0(k1_funct_1(A_469,D_470))
      | ~ m3_yellow_6(A_469,A_471,B_472)
      | ~ v1_partfun1(A_469,A_471)
      | ~ v4_relat_1(A_469,A_471)
      | ~ l1_struct_0(B_472)
      | ~ r2_hidden(D_470,k1_relat_1(A_469))
      | ~ v1_funct_1(A_469)
      | ~ v1_relat_1(A_469) ) ),
    inference(resolution,[status(thm)],[c_2,c_2377])).

tff(c_2657,plain,(
    ! [D_470] :
      ( ~ v2_struct_0(k1_funct_1('#skF_8',D_470))
      | ~ v1_partfun1('#skF_8','#skF_6')
      | ~ v4_relat_1('#skF_8','#skF_6')
      | ~ l1_struct_0('#skF_7')
      | ~ r2_hidden(D_470,k1_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_1403,c_2655])).

tff(c_2661,plain,(
    ! [D_473] :
      ( ~ v2_struct_0(k1_funct_1('#skF_8',D_473))
      | ~ r2_hidden(D_473,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_46,c_1445,c_52,c_48,c_44,c_2657])).

tff(c_2670,plain,(
    ~ r2_hidden('#skF_9','#skF_6') ),
    inference(resolution,[status(thm)],[c_2304,c_2661])).

tff(c_2678,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1402,c_2670])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 12:35:59 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.19/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.88/2.04  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.88/2.05  
% 4.88/2.05  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.88/2.06  %$ m3_yellow_6 > v4_relat_1 > v1_partfun1 > r2_hidden > l1_waybel_0 > v7_waybel_0 > v4_orders_2 > v2_struct_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_4 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_9 > #skF_8 > #skF_2 > #skF_1
% 4.88/2.06  
% 4.88/2.06  %Foreground sorts:
% 4.88/2.06  
% 4.88/2.06  
% 4.88/2.06  %Background operators:
% 4.88/2.06  
% 4.88/2.06  
% 4.88/2.06  %Foreground operators:
% 4.88/2.06  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.88/2.06  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.88/2.06  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.88/2.06  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.88/2.06  tff(v7_waybel_0, type, v7_waybel_0: $i > $o).
% 4.88/2.06  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 4.88/2.06  tff('#skF_7', type, '#skF_7': $i).
% 4.88/2.06  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.88/2.06  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.88/2.06  tff('#skF_6', type, '#skF_6': $i).
% 4.88/2.06  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 4.88/2.06  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 4.88/2.06  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 4.88/2.06  tff('#skF_9', type, '#skF_9': $i).
% 4.88/2.06  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 4.88/2.06  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.88/2.06  tff('#skF_8', type, '#skF_8': $i).
% 4.88/2.06  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.88/2.06  tff(l1_waybel_0, type, l1_waybel_0: ($i * $i) > $o).
% 4.88/2.06  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.88/2.06  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.88/2.06  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.88/2.06  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.88/2.06  tff(m3_yellow_6, type, m3_yellow_6: ($i * $i * $i) > $o).
% 4.88/2.06  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.88/2.06  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.88/2.06  
% 4.88/2.08  tff(f_112, negated_conjecture, ~(![A, B]: (l1_struct_0(B) => (![C]: ((((v1_relat_1(C) & v4_relat_1(C, A)) & v1_funct_1(C)) & v1_partfun1(C, A)) => (m3_yellow_6(C, A, B) <=> (![D]: (r2_hidden(D, A) => (((~v2_struct_0(k1_funct_1(C, D)) & v4_orders_2(k1_funct_1(C, D))) & v7_waybel_0(k1_funct_1(C, D))) & l1_waybel_0(k1_funct_1(C, D), B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t33_yellow_6)).
% 4.88/2.08  tff(f_73, axiom, (![A, B]: (l1_struct_0(B) => (![C]: ((((v1_relat_1(C) & v4_relat_1(C, A)) & v1_funct_1(C)) & v1_partfun1(C, A)) => (m3_yellow_6(C, A, B) <=> (![D]: (r2_hidden(D, k2_relat_1(C)) => (((~v2_struct_0(D) & v4_orders_2(D)) & v7_waybel_0(D)) & l1_waybel_0(D, B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d15_yellow_6)).
% 4.88/2.08  tff(f_48, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_partfun1)).
% 4.88/2.08  tff(f_40, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_funct_1)).
% 4.88/2.08  tff(c_48, plain, (v4_relat_1('#skF_8', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_112])).
% 4.88/2.08  tff(c_44, plain, (v1_partfun1('#skF_8', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_112])).
% 4.88/2.08  tff(c_52, plain, (l1_struct_0('#skF_7')), inference(cnfTransformation, [status(thm)], [f_112])).
% 4.88/2.08  tff(c_50, plain, (v1_relat_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_112])).
% 4.88/2.08  tff(c_46, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_112])).
% 4.88/2.08  tff(c_418, plain, (![A_130, B_131, C_132]: (r2_hidden('#skF_5'(A_130, B_131, C_132), k2_relat_1(C_132)) | m3_yellow_6(C_132, A_130, B_131) | ~v1_partfun1(C_132, A_130) | ~v1_funct_1(C_132) | ~v4_relat_1(C_132, A_130) | ~v1_relat_1(C_132) | ~l1_struct_0(B_131))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.88/2.08  tff(c_92, plain, (![B_79, A_80]: (k1_relat_1(B_79)=A_80 | ~v1_partfun1(B_79, A_80) | ~v4_relat_1(B_79, A_80) | ~v1_relat_1(B_79))), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.88/2.08  tff(c_95, plain, (k1_relat_1('#skF_8')='#skF_6' | ~v1_partfun1('#skF_8', '#skF_6') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_48, c_92])).
% 4.88/2.08  tff(c_98, plain, (k1_relat_1('#skF_8')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_50, c_44, c_95])).
% 4.88/2.08  tff(c_118, plain, (![A_87, C_88]: (r2_hidden('#skF_4'(A_87, k2_relat_1(A_87), C_88), k1_relat_1(A_87)) | ~r2_hidden(C_88, k2_relat_1(A_87)) | ~v1_funct_1(A_87) | ~v1_relat_1(A_87))), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.88/2.08  tff(c_121, plain, (![C_88]: (r2_hidden('#skF_4'('#skF_8', k2_relat_1('#skF_8'), C_88), '#skF_6') | ~r2_hidden(C_88, k2_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_98, c_118])).
% 4.88/2.08  tff(c_123, plain, (![C_88]: (r2_hidden('#skF_4'('#skF_8', k2_relat_1('#skF_8'), C_88), '#skF_6') | ~r2_hidden(C_88, k2_relat_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_46, c_121])).
% 4.88/2.08  tff(c_124, plain, (![A_89, C_90]: (k1_funct_1(A_89, '#skF_4'(A_89, k2_relat_1(A_89), C_90))=C_90 | ~r2_hidden(C_90, k2_relat_1(A_89)) | ~v1_funct_1(A_89) | ~v1_relat_1(A_89))), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.88/2.08  tff(c_56, plain, (r2_hidden('#skF_9', '#skF_6') | ~m3_yellow_6('#skF_8', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_112])).
% 4.88/2.08  tff(c_83, plain, (~m3_yellow_6('#skF_8', '#skF_6', '#skF_7')), inference(splitLeft, [status(thm)], [c_56])).
% 4.88/2.08  tff(c_76, plain, (![D_65]: (m3_yellow_6('#skF_8', '#skF_6', '#skF_7') | v4_orders_2(k1_funct_1('#skF_8', D_65)) | ~r2_hidden(D_65, '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_112])).
% 4.88/2.08  tff(c_108, plain, (![D_65]: (v4_orders_2(k1_funct_1('#skF_8', D_65)) | ~r2_hidden(D_65, '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_83, c_76])).
% 4.88/2.08  tff(c_146, plain, (![C_90]: (v4_orders_2(C_90) | ~r2_hidden('#skF_4'('#skF_8', k2_relat_1('#skF_8'), C_90), '#skF_6') | ~r2_hidden(C_90, k2_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_124, c_108])).
% 4.88/2.08  tff(c_187, plain, (![C_96]: (v4_orders_2(C_96) | ~r2_hidden('#skF_4'('#skF_8', k2_relat_1('#skF_8'), C_96), '#skF_6') | ~r2_hidden(C_96, k2_relat_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_46, c_146])).
% 4.88/2.08  tff(c_191, plain, (![C_88]: (v4_orders_2(C_88) | ~r2_hidden(C_88, k2_relat_1('#skF_8')))), inference(resolution, [status(thm)], [c_123, c_187])).
% 4.88/2.08  tff(c_432, plain, (![A_130, B_131]: (v4_orders_2('#skF_5'(A_130, B_131, '#skF_8')) | m3_yellow_6('#skF_8', A_130, B_131) | ~v1_partfun1('#skF_8', A_130) | ~v1_funct_1('#skF_8') | ~v4_relat_1('#skF_8', A_130) | ~v1_relat_1('#skF_8') | ~l1_struct_0(B_131))), inference(resolution, [status(thm)], [c_418, c_191])).
% 4.88/2.08  tff(c_449, plain, (![A_130, B_131]: (v4_orders_2('#skF_5'(A_130, B_131, '#skF_8')) | m3_yellow_6('#skF_8', A_130, B_131) | ~v1_partfun1('#skF_8', A_130) | ~v4_relat_1('#skF_8', A_130) | ~l1_struct_0(B_131))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_46, c_432])).
% 4.88/2.08  tff(c_70, plain, (![D_65]: (m3_yellow_6('#skF_8', '#skF_6', '#skF_7') | v7_waybel_0(k1_funct_1('#skF_8', D_65)) | ~r2_hidden(D_65, '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_112])).
% 4.88/2.08  tff(c_110, plain, (![D_65]: (v7_waybel_0(k1_funct_1('#skF_8', D_65)) | ~r2_hidden(D_65, '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_83, c_70])).
% 4.88/2.08  tff(c_142, plain, (![C_90]: (v7_waybel_0(C_90) | ~r2_hidden('#skF_4'('#skF_8', k2_relat_1('#skF_8'), C_90), '#skF_6') | ~r2_hidden(C_90, k2_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_124, c_110])).
% 4.88/2.08  tff(c_174, plain, (![C_94]: (v7_waybel_0(C_94) | ~r2_hidden('#skF_4'('#skF_8', k2_relat_1('#skF_8'), C_94), '#skF_6') | ~r2_hidden(C_94, k2_relat_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_46, c_142])).
% 4.88/2.08  tff(c_178, plain, (![C_88]: (v7_waybel_0(C_88) | ~r2_hidden(C_88, k2_relat_1('#skF_8')))), inference(resolution, [status(thm)], [c_123, c_174])).
% 4.88/2.08  tff(c_436, plain, (![A_130, B_131]: (v7_waybel_0('#skF_5'(A_130, B_131, '#skF_8')) | m3_yellow_6('#skF_8', A_130, B_131) | ~v1_partfun1('#skF_8', A_130) | ~v1_funct_1('#skF_8') | ~v4_relat_1('#skF_8', A_130) | ~v1_relat_1('#skF_8') | ~l1_struct_0(B_131))), inference(resolution, [status(thm)], [c_418, c_178])).
% 4.88/2.08  tff(c_452, plain, (![A_130, B_131]: (v7_waybel_0('#skF_5'(A_130, B_131, '#skF_8')) | m3_yellow_6('#skF_8', A_130, B_131) | ~v1_partfun1('#skF_8', A_130) | ~v4_relat_1('#skF_8', A_130) | ~l1_struct_0(B_131))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_46, c_436])).
% 4.88/2.08  tff(c_64, plain, (![D_65]: (m3_yellow_6('#skF_8', '#skF_6', '#skF_7') | l1_waybel_0(k1_funct_1('#skF_8', D_65), '#skF_7') | ~r2_hidden(D_65, '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_112])).
% 4.88/2.08  tff(c_115, plain, (![D_65]: (l1_waybel_0(k1_funct_1('#skF_8', D_65), '#skF_7') | ~r2_hidden(D_65, '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_83, c_64])).
% 4.88/2.08  tff(c_134, plain, (![C_90]: (l1_waybel_0(C_90, '#skF_7') | ~r2_hidden('#skF_4'('#skF_8', k2_relat_1('#skF_8'), C_90), '#skF_6') | ~r2_hidden(C_90, k2_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_124, c_115])).
% 4.88/2.08  tff(c_200, plain, (![C_98]: (l1_waybel_0(C_98, '#skF_7') | ~r2_hidden('#skF_4'('#skF_8', k2_relat_1('#skF_8'), C_98), '#skF_6') | ~r2_hidden(C_98, k2_relat_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_46, c_134])).
% 4.88/2.08  tff(c_204, plain, (![C_88]: (l1_waybel_0(C_88, '#skF_7') | ~r2_hidden(C_88, k2_relat_1('#skF_8')))), inference(resolution, [status(thm)], [c_123, c_200])).
% 4.88/2.08  tff(c_428, plain, (![A_130, B_131]: (l1_waybel_0('#skF_5'(A_130, B_131, '#skF_8'), '#skF_7') | m3_yellow_6('#skF_8', A_130, B_131) | ~v1_partfun1('#skF_8', A_130) | ~v1_funct_1('#skF_8') | ~v4_relat_1('#skF_8', A_130) | ~v1_relat_1('#skF_8') | ~l1_struct_0(B_131))), inference(resolution, [status(thm)], [c_418, c_204])).
% 4.88/2.08  tff(c_446, plain, (![A_130, B_131]: (l1_waybel_0('#skF_5'(A_130, B_131, '#skF_8'), '#skF_7') | m3_yellow_6('#skF_8', A_130, B_131) | ~v1_partfun1('#skF_8', A_130) | ~v4_relat_1('#skF_8', A_130) | ~l1_struct_0(B_131))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_46, c_428])).
% 4.88/2.08  tff(c_768, plain, (![A_176, B_177, C_178]: (~l1_waybel_0('#skF_5'(A_176, B_177, C_178), B_177) | ~v7_waybel_0('#skF_5'(A_176, B_177, C_178)) | ~v4_orders_2('#skF_5'(A_176, B_177, C_178)) | v2_struct_0('#skF_5'(A_176, B_177, C_178)) | m3_yellow_6(C_178, A_176, B_177) | ~v1_partfun1(C_178, A_176) | ~v1_funct_1(C_178) | ~v4_relat_1(C_178, A_176) | ~v1_relat_1(C_178) | ~l1_struct_0(B_177))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.88/2.08  tff(c_772, plain, (![A_130]: (~v7_waybel_0('#skF_5'(A_130, '#skF_7', '#skF_8')) | ~v4_orders_2('#skF_5'(A_130, '#skF_7', '#skF_8')) | v2_struct_0('#skF_5'(A_130, '#skF_7', '#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | m3_yellow_6('#skF_8', A_130, '#skF_7') | ~v1_partfun1('#skF_8', A_130) | ~v4_relat_1('#skF_8', A_130) | ~l1_struct_0('#skF_7'))), inference(resolution, [status(thm)], [c_446, c_768])).
% 4.88/2.08  tff(c_1321, plain, (![A_187]: (~v7_waybel_0('#skF_5'(A_187, '#skF_7', '#skF_8')) | ~v4_orders_2('#skF_5'(A_187, '#skF_7', '#skF_8')) | v2_struct_0('#skF_5'(A_187, '#skF_7', '#skF_8')) | m3_yellow_6('#skF_8', A_187, '#skF_7') | ~v1_partfun1('#skF_8', A_187) | ~v4_relat_1('#skF_8', A_187))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_46, c_772])).
% 4.88/2.08  tff(c_1325, plain, (![A_130]: (~v4_orders_2('#skF_5'(A_130, '#skF_7', '#skF_8')) | v2_struct_0('#skF_5'(A_130, '#skF_7', '#skF_8')) | m3_yellow_6('#skF_8', A_130, '#skF_7') | ~v1_partfun1('#skF_8', A_130) | ~v4_relat_1('#skF_8', A_130) | ~l1_struct_0('#skF_7'))), inference(resolution, [status(thm)], [c_452, c_1321])).
% 4.88/2.08  tff(c_1330, plain, (![A_193]: (~v4_orders_2('#skF_5'(A_193, '#skF_7', '#skF_8')) | v2_struct_0('#skF_5'(A_193, '#skF_7', '#skF_8')) | m3_yellow_6('#skF_8', A_193, '#skF_7') | ~v1_partfun1('#skF_8', A_193) | ~v4_relat_1('#skF_8', A_193))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_1325])).
% 4.88/2.08  tff(c_1334, plain, (![A_130]: (v2_struct_0('#skF_5'(A_130, '#skF_7', '#skF_8')) | m3_yellow_6('#skF_8', A_130, '#skF_7') | ~v1_partfun1('#skF_8', A_130) | ~v4_relat_1('#skF_8', A_130) | ~l1_struct_0('#skF_7'))), inference(resolution, [status(thm)], [c_449, c_1330])).
% 4.88/2.08  tff(c_1338, plain, (![A_194]: (v2_struct_0('#skF_5'(A_194, '#skF_7', '#skF_8')) | m3_yellow_6('#skF_8', A_194, '#skF_7') | ~v1_partfun1('#skF_8', A_194) | ~v4_relat_1('#skF_8', A_194))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_1334])).
% 4.88/2.08  tff(c_82, plain, (![D_65]: (m3_yellow_6('#skF_8', '#skF_6', '#skF_7') | ~v2_struct_0(k1_funct_1('#skF_8', D_65)) | ~r2_hidden(D_65, '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_112])).
% 4.88/2.08  tff(c_112, plain, (![D_65]: (~v2_struct_0(k1_funct_1('#skF_8', D_65)) | ~r2_hidden(D_65, '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_83, c_82])).
% 4.88/2.08  tff(c_138, plain, (![C_90]: (~v2_struct_0(C_90) | ~r2_hidden('#skF_4'('#skF_8', k2_relat_1('#skF_8'), C_90), '#skF_6') | ~r2_hidden(C_90, k2_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_124, c_112])).
% 4.88/2.08  tff(c_161, plain, (![C_92]: (~v2_struct_0(C_92) | ~r2_hidden('#skF_4'('#skF_8', k2_relat_1('#skF_8'), C_92), '#skF_6') | ~r2_hidden(C_92, k2_relat_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_46, c_138])).
% 4.88/2.08  tff(c_165, plain, (![C_88]: (~v2_struct_0(C_88) | ~r2_hidden(C_88, k2_relat_1('#skF_8')))), inference(resolution, [status(thm)], [c_123, c_161])).
% 4.88/2.08  tff(c_440, plain, (![A_130, B_131]: (~v2_struct_0('#skF_5'(A_130, B_131, '#skF_8')) | m3_yellow_6('#skF_8', A_130, B_131) | ~v1_partfun1('#skF_8', A_130) | ~v1_funct_1('#skF_8') | ~v4_relat_1('#skF_8', A_130) | ~v1_relat_1('#skF_8') | ~l1_struct_0(B_131))), inference(resolution, [status(thm)], [c_418, c_165])).
% 4.88/2.08  tff(c_455, plain, (![A_130, B_131]: (~v2_struct_0('#skF_5'(A_130, B_131, '#skF_8')) | m3_yellow_6('#skF_8', A_130, B_131) | ~v1_partfun1('#skF_8', A_130) | ~v4_relat_1('#skF_8', A_130) | ~l1_struct_0(B_131))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_46, c_440])).
% 4.88/2.08  tff(c_1341, plain, (![A_194]: (~l1_struct_0('#skF_7') | m3_yellow_6('#skF_8', A_194, '#skF_7') | ~v1_partfun1('#skF_8', A_194) | ~v4_relat_1('#skF_8', A_194))), inference(resolution, [status(thm)], [c_1338, c_455])).
% 4.88/2.08  tff(c_1345, plain, (![A_195]: (m3_yellow_6('#skF_8', A_195, '#skF_7') | ~v1_partfun1('#skF_8', A_195) | ~v4_relat_1('#skF_8', A_195))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_1341])).
% 4.88/2.08  tff(c_1370, plain, (~v1_partfun1('#skF_8', '#skF_6') | ~v4_relat_1('#skF_8', '#skF_6')), inference(resolution, [status(thm)], [c_1345, c_83])).
% 4.88/2.08  tff(c_1401, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_44, c_1370])).
% 4.88/2.08  tff(c_1402, plain, (r2_hidden('#skF_9', '#skF_6')), inference(splitRight, [status(thm)], [c_56])).
% 4.88/2.08  tff(c_1439, plain, (![B_209, A_210]: (k1_relat_1(B_209)=A_210 | ~v1_partfun1(B_209, A_210) | ~v4_relat_1(B_209, A_210) | ~v1_relat_1(B_209))), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.88/2.08  tff(c_1442, plain, (k1_relat_1('#skF_8')='#skF_6' | ~v1_partfun1('#skF_8', '#skF_6') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_48, c_1439])).
% 4.88/2.08  tff(c_1445, plain, (k1_relat_1('#skF_8')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_50, c_44, c_1442])).
% 4.88/2.08  tff(c_1403, plain, (m3_yellow_6('#skF_8', '#skF_6', '#skF_7')), inference(splitRight, [status(thm)], [c_56])).
% 4.88/2.08  tff(c_2, plain, (![A_1, D_40]: (r2_hidden(k1_funct_1(A_1, D_40), k2_relat_1(A_1)) | ~r2_hidden(D_40, k1_relat_1(A_1)) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.88/2.08  tff(c_2183, plain, (![D_371, C_372, A_373, B_374]: (v7_waybel_0(D_371) | ~r2_hidden(D_371, k2_relat_1(C_372)) | ~m3_yellow_6(C_372, A_373, B_374) | ~v1_partfun1(C_372, A_373) | ~v1_funct_1(C_372) | ~v4_relat_1(C_372, A_373) | ~v1_relat_1(C_372) | ~l1_struct_0(B_374))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.88/2.08  tff(c_2284, plain, (![A_396, D_397, A_398, B_399]: (v7_waybel_0(k1_funct_1(A_396, D_397)) | ~m3_yellow_6(A_396, A_398, B_399) | ~v1_partfun1(A_396, A_398) | ~v4_relat_1(A_396, A_398) | ~l1_struct_0(B_399) | ~r2_hidden(D_397, k1_relat_1(A_396)) | ~v1_funct_1(A_396) | ~v1_relat_1(A_396))), inference(resolution, [status(thm)], [c_2, c_2183])).
% 4.88/2.08  tff(c_2286, plain, (![D_397]: (v7_waybel_0(k1_funct_1('#skF_8', D_397)) | ~v1_partfun1('#skF_8', '#skF_6') | ~v4_relat_1('#skF_8', '#skF_6') | ~l1_struct_0('#skF_7') | ~r2_hidden(D_397, k1_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_1403, c_2284])).
% 4.88/2.08  tff(c_2290, plain, (![D_400]: (v7_waybel_0(k1_funct_1('#skF_8', D_400)) | ~r2_hidden(D_400, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_46, c_1445, c_52, c_48, c_44, c_2286])).
% 4.88/2.08  tff(c_1807, plain, (![D_301, B_302, C_303, A_304]: (l1_waybel_0(D_301, B_302) | ~r2_hidden(D_301, k2_relat_1(C_303)) | ~m3_yellow_6(C_303, A_304, B_302) | ~v1_partfun1(C_303, A_304) | ~v1_funct_1(C_303) | ~v4_relat_1(C_303, A_304) | ~v1_relat_1(C_303) | ~l1_struct_0(B_302))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.88/2.08  tff(c_2125, plain, (![A_356, D_357, B_358, A_359]: (l1_waybel_0(k1_funct_1(A_356, D_357), B_358) | ~m3_yellow_6(A_356, A_359, B_358) | ~v1_partfun1(A_356, A_359) | ~v4_relat_1(A_356, A_359) | ~l1_struct_0(B_358) | ~r2_hidden(D_357, k1_relat_1(A_356)) | ~v1_funct_1(A_356) | ~v1_relat_1(A_356))), inference(resolution, [status(thm)], [c_2, c_1807])).
% 4.88/2.08  tff(c_2127, plain, (![D_357]: (l1_waybel_0(k1_funct_1('#skF_8', D_357), '#skF_7') | ~v1_partfun1('#skF_8', '#skF_6') | ~v4_relat_1('#skF_8', '#skF_6') | ~l1_struct_0('#skF_7') | ~r2_hidden(D_357, k1_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_1403, c_2125])).
% 4.88/2.08  tff(c_2131, plain, (![D_360]: (l1_waybel_0(k1_funct_1('#skF_8', D_360), '#skF_7') | ~r2_hidden(D_360, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_46, c_1445, c_52, c_48, c_44, c_2127])).
% 4.88/2.08  tff(c_1542, plain, (![D_236, C_237, A_238, B_239]: (v4_orders_2(D_236) | ~r2_hidden(D_236, k2_relat_1(C_237)) | ~m3_yellow_6(C_237, A_238, B_239) | ~v1_partfun1(C_237, A_238) | ~v1_funct_1(C_237) | ~v4_relat_1(C_237, A_238) | ~v1_relat_1(C_237) | ~l1_struct_0(B_239))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.88/2.08  tff(c_1671, plain, (![A_265, D_266, A_267, B_268]: (v4_orders_2(k1_funct_1(A_265, D_266)) | ~m3_yellow_6(A_265, A_267, B_268) | ~v1_partfun1(A_265, A_267) | ~v4_relat_1(A_265, A_267) | ~l1_struct_0(B_268) | ~r2_hidden(D_266, k1_relat_1(A_265)) | ~v1_funct_1(A_265) | ~v1_relat_1(A_265))), inference(resolution, [status(thm)], [c_2, c_1542])).
% 4.88/2.08  tff(c_1673, plain, (![D_266]: (v4_orders_2(k1_funct_1('#skF_8', D_266)) | ~v1_partfun1('#skF_8', '#skF_6') | ~v4_relat_1('#skF_8', '#skF_6') | ~l1_struct_0('#skF_7') | ~r2_hidden(D_266, k1_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_1403, c_1671])).
% 4.88/2.08  tff(c_1677, plain, (![D_269]: (v4_orders_2(k1_funct_1('#skF_8', D_269)) | ~r2_hidden(D_269, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_46, c_1445, c_52, c_48, c_44, c_1673])).
% 4.88/2.08  tff(c_54, plain, (~l1_waybel_0(k1_funct_1('#skF_8', '#skF_9'), '#skF_7') | ~v7_waybel_0(k1_funct_1('#skF_8', '#skF_9')) | ~v4_orders_2(k1_funct_1('#skF_8', '#skF_9')) | v2_struct_0(k1_funct_1('#skF_8', '#skF_9')) | ~m3_yellow_6('#skF_8', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_112])).
% 4.88/2.08  tff(c_1472, plain, (~l1_waybel_0(k1_funct_1('#skF_8', '#skF_9'), '#skF_7') | ~v7_waybel_0(k1_funct_1('#skF_8', '#skF_9')) | ~v4_orders_2(k1_funct_1('#skF_8', '#skF_9')) | v2_struct_0(k1_funct_1('#skF_8', '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_1403, c_54])).
% 4.88/2.08  tff(c_1473, plain, (~v4_orders_2(k1_funct_1('#skF_8', '#skF_9'))), inference(splitLeft, [status(thm)], [c_1472])).
% 4.88/2.08  tff(c_1680, plain, (~r2_hidden('#skF_9', '#skF_6')), inference(resolution, [status(thm)], [c_1677, c_1473])).
% 4.88/2.08  tff(c_1690, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1402, c_1680])).
% 4.88/2.08  tff(c_1691, plain, (~v7_waybel_0(k1_funct_1('#skF_8', '#skF_9')) | ~l1_waybel_0(k1_funct_1('#skF_8', '#skF_9'), '#skF_7') | v2_struct_0(k1_funct_1('#skF_8', '#skF_9'))), inference(splitRight, [status(thm)], [c_1472])).
% 4.88/2.08  tff(c_1699, plain, (~l1_waybel_0(k1_funct_1('#skF_8', '#skF_9'), '#skF_7')), inference(splitLeft, [status(thm)], [c_1691])).
% 4.88/2.08  tff(c_2134, plain, (~r2_hidden('#skF_9', '#skF_6')), inference(resolution, [status(thm)], [c_2131, c_1699])).
% 4.88/2.08  tff(c_2148, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1402, c_2134])).
% 4.88/2.08  tff(c_2149, plain, (~v7_waybel_0(k1_funct_1('#skF_8', '#skF_9')) | v2_struct_0(k1_funct_1('#skF_8', '#skF_9'))), inference(splitRight, [status(thm)], [c_1691])).
% 4.88/2.08  tff(c_2151, plain, (~v7_waybel_0(k1_funct_1('#skF_8', '#skF_9'))), inference(splitLeft, [status(thm)], [c_2149])).
% 4.88/2.08  tff(c_2293, plain, (~r2_hidden('#skF_9', '#skF_6')), inference(resolution, [status(thm)], [c_2290, c_2151])).
% 4.88/2.08  tff(c_2303, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1402, c_2293])).
% 4.88/2.08  tff(c_2304, plain, (v2_struct_0(k1_funct_1('#skF_8', '#skF_9'))), inference(splitRight, [status(thm)], [c_2149])).
% 4.88/2.08  tff(c_2377, plain, (![D_419, C_420, A_421, B_422]: (~v2_struct_0(D_419) | ~r2_hidden(D_419, k2_relat_1(C_420)) | ~m3_yellow_6(C_420, A_421, B_422) | ~v1_partfun1(C_420, A_421) | ~v1_funct_1(C_420) | ~v4_relat_1(C_420, A_421) | ~v1_relat_1(C_420) | ~l1_struct_0(B_422))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.88/2.08  tff(c_2655, plain, (![A_469, D_470, A_471, B_472]: (~v2_struct_0(k1_funct_1(A_469, D_470)) | ~m3_yellow_6(A_469, A_471, B_472) | ~v1_partfun1(A_469, A_471) | ~v4_relat_1(A_469, A_471) | ~l1_struct_0(B_472) | ~r2_hidden(D_470, k1_relat_1(A_469)) | ~v1_funct_1(A_469) | ~v1_relat_1(A_469))), inference(resolution, [status(thm)], [c_2, c_2377])).
% 4.88/2.08  tff(c_2657, plain, (![D_470]: (~v2_struct_0(k1_funct_1('#skF_8', D_470)) | ~v1_partfun1('#skF_8', '#skF_6') | ~v4_relat_1('#skF_8', '#skF_6') | ~l1_struct_0('#skF_7') | ~r2_hidden(D_470, k1_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_1403, c_2655])).
% 4.88/2.08  tff(c_2661, plain, (![D_473]: (~v2_struct_0(k1_funct_1('#skF_8', D_473)) | ~r2_hidden(D_473, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_46, c_1445, c_52, c_48, c_44, c_2657])).
% 4.88/2.08  tff(c_2670, plain, (~r2_hidden('#skF_9', '#skF_6')), inference(resolution, [status(thm)], [c_2304, c_2661])).
% 4.88/2.08  tff(c_2678, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1402, c_2670])).
% 4.88/2.08  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.88/2.08  
% 4.88/2.08  Inference rules
% 4.88/2.08  ----------------------
% 4.88/2.08  #Ref     : 0
% 4.88/2.08  #Sup     : 489
% 4.88/2.08  #Fact    : 0
% 4.88/2.08  #Define  : 0
% 4.88/2.08  #Split   : 7
% 4.88/2.08  #Chain   : 0
% 4.88/2.08  #Close   : 0
% 4.88/2.08  
% 4.88/2.08  Ordering : KBO
% 4.88/2.08  
% 4.88/2.08  Simplification rules
% 4.88/2.08  ----------------------
% 4.88/2.08  #Subsume      : 52
% 4.88/2.08  #Demod        : 385
% 4.88/2.08  #Tautology    : 166
% 4.88/2.08  #SimpNegUnit  : 4
% 4.88/2.08  #BackRed      : 0
% 4.88/2.08  
% 4.88/2.08  #Partial instantiations: 0
% 4.88/2.08  #Strategies tried      : 1
% 4.88/2.08  
% 4.88/2.08  Timing (in seconds)
% 4.88/2.08  ----------------------
% 4.88/2.08  Preprocessing        : 0.45
% 4.88/2.08  Parsing              : 0.24
% 4.88/2.08  CNF conversion       : 0.04
% 4.88/2.08  Main loop            : 0.79
% 4.88/2.08  Inferencing          : 0.33
% 4.88/2.08  Reduction            : 0.20
% 4.88/2.08  Demodulation         : 0.14
% 4.88/2.08  BG Simplification    : 0.05
% 4.88/2.08  Subsumption          : 0.15
% 4.88/2.08  Abstraction          : 0.04
% 4.88/2.08  MUC search           : 0.00
% 4.88/2.08  Cooper               : 0.00
% 4.88/2.08  Total                : 1.29
% 4.88/2.08  Index Insertion      : 0.00
% 4.88/2.08  Index Deletion       : 0.00
% 4.88/2.08  Index Matching       : 0.00
% 4.88/2.08  BG Taut test         : 0.00
%------------------------------------------------------------------------------
