%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1928+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:41 EST 2020

% Result     : Theorem 2.63s
% Output     : CNFRefutation 2.63s
% Verified   : 
% Statistics : Number of formulae       :   59 (  77 expanded)
%              Number of leaves         :   31 (  45 expanded)
%              Depth                    :   10
%              Number of atoms          :  167 ( 307 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_waybel_0 > r1_orders_2 > r2_hidden > r1_xboole_0 > m1_subset_1 > l1_waybel_0 > v7_waybel_0 > v4_orders_2 > v2_struct_0 > l1_struct_0 > l1_orders_2 > k2_waybel_0 > #nlpp > u1_struct_0 > #skF_5 > #skF_6 > #skF_4 > #skF_7 > #skF_10 > #skF_2 > #skF_9 > #skF_8 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': $i > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff(k2_waybel_0,type,(
    k2_waybel_0: ( $i * $i * $i ) > $i )).

tff(v7_waybel_0,type,(
    v7_waybel_0: $i > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(r1_waybel_0,type,(
    r1_waybel_0: ( $i * $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(l1_waybel_0,type,(
    l1_waybel_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_117,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & l1_struct_0(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & v4_orders_2(B)
              & v7_waybel_0(B)
              & l1_waybel_0(B,A) )
           => ! [C,D] :
                ~ ( r1_waybel_0(A,B,C)
                  & r1_waybel_0(A,B,D)
                  & r1_xboole_0(C,D) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_yellow_6)).

tff(f_75,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ! [B] :
          ( l1_waybel_0(B,A)
         => l1_orders_2(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_waybel_0)).

tff(f_48,axiom,(
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

tff(f_68,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_orders_2(A) )
     => ( v7_waybel_0(A)
      <=> ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => ? [D] :
                    ( m1_subset_1(D,u1_struct_0(A))
                    & r1_orders_2(A,B,D)
                    & r1_orders_2(A,C,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_yellow_6)).

tff(f_93,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(c_48,plain,(
    ~ v2_struct_0('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_44,plain,(
    ~ v2_struct_0('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_46,plain,(
    l1_struct_0('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_38,plain,(
    l1_waybel_0('#skF_8','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_36,plain,(
    r1_waybel_0('#skF_7','#skF_8','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_49,plain,(
    ! [B_95,A_96] :
      ( l1_orders_2(B_95)
      | ~ l1_waybel_0(B_95,A_96)
      | ~ l1_struct_0(A_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_52,plain,
    ( l1_orders_2('#skF_8')
    | ~ l1_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_38,c_49])).

tff(c_55,plain,(
    l1_orders_2('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_52])).

tff(c_40,plain,(
    v7_waybel_0('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_34,plain,(
    r1_waybel_0('#skF_7','#skF_8','#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_4,plain,(
    ! [A_1,B_29,C_43] :
      ( m1_subset_1('#skF_2'(A_1,B_29,C_43),u1_struct_0(B_29))
      | ~ r1_waybel_0(A_1,B_29,C_43)
      | ~ l1_waybel_0(B_29,A_1)
      | v2_struct_0(B_29)
      | ~ l1_struct_0(A_1)
      | v2_struct_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_22,plain,(
    ! [A_54,B_69,C_73] :
      ( m1_subset_1('#skF_3'(A_54,B_69,C_73),u1_struct_0(A_54))
      | ~ m1_subset_1(C_73,u1_struct_0(A_54))
      | ~ m1_subset_1(B_69,u1_struct_0(A_54))
      | ~ v7_waybel_0(A_54)
      | ~ l1_orders_2(A_54)
      | v2_struct_0(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_20,plain,(
    ! [A_54,B_69,C_73] :
      ( r1_orders_2(A_54,B_69,'#skF_3'(A_54,B_69,C_73))
      | ~ m1_subset_1(C_73,u1_struct_0(A_54))
      | ~ m1_subset_1(B_69,u1_struct_0(A_54))
      | ~ v7_waybel_0(A_54)
      | ~ l1_orders_2(A_54)
      | v2_struct_0(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_114,plain,(
    ! [A_135,B_136,E_137,C_138] :
      ( r2_hidden(k2_waybel_0(A_135,B_136,E_137),C_138)
      | ~ r1_orders_2(B_136,'#skF_2'(A_135,B_136,C_138),E_137)
      | ~ m1_subset_1(E_137,u1_struct_0(B_136))
      | ~ r1_waybel_0(A_135,B_136,C_138)
      | ~ l1_waybel_0(B_136,A_135)
      | v2_struct_0(B_136)
      | ~ l1_struct_0(A_135)
      | v2_struct_0(A_135) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_129,plain,(
    ! [A_135,A_54,C_138,C_73] :
      ( r2_hidden(k2_waybel_0(A_135,A_54,'#skF_3'(A_54,'#skF_2'(A_135,A_54,C_138),C_73)),C_138)
      | ~ m1_subset_1('#skF_3'(A_54,'#skF_2'(A_135,A_54,C_138),C_73),u1_struct_0(A_54))
      | ~ r1_waybel_0(A_135,A_54,C_138)
      | ~ l1_waybel_0(A_54,A_135)
      | ~ l1_struct_0(A_135)
      | v2_struct_0(A_135)
      | ~ m1_subset_1(C_73,u1_struct_0(A_54))
      | ~ m1_subset_1('#skF_2'(A_135,A_54,C_138),u1_struct_0(A_54))
      | ~ v7_waybel_0(A_54)
      | ~ l1_orders_2(A_54)
      | v2_struct_0(A_54) ) ),
    inference(resolution,[status(thm)],[c_20,c_114])).

tff(c_18,plain,(
    ! [A_54,C_73,B_69] :
      ( r1_orders_2(A_54,C_73,'#skF_3'(A_54,B_69,C_73))
      | ~ m1_subset_1(C_73,u1_struct_0(A_54))
      | ~ m1_subset_1(B_69,u1_struct_0(A_54))
      | ~ v7_waybel_0(A_54)
      | ~ l1_orders_2(A_54)
      | v2_struct_0(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_131,plain,(
    ! [A_142,A_143,B_144,C_145] :
      ( r2_hidden(k2_waybel_0(A_142,A_143,'#skF_3'(A_143,B_144,'#skF_2'(A_142,A_143,C_145))),C_145)
      | ~ m1_subset_1('#skF_3'(A_143,B_144,'#skF_2'(A_142,A_143,C_145)),u1_struct_0(A_143))
      | ~ r1_waybel_0(A_142,A_143,C_145)
      | ~ l1_waybel_0(A_143,A_142)
      | ~ l1_struct_0(A_142)
      | v2_struct_0(A_142)
      | ~ m1_subset_1('#skF_2'(A_142,A_143,C_145),u1_struct_0(A_143))
      | ~ m1_subset_1(B_144,u1_struct_0(A_143))
      | ~ v7_waybel_0(A_143)
      | ~ l1_orders_2(A_143)
      | v2_struct_0(A_143) ) ),
    inference(resolution,[status(thm)],[c_18,c_114])).

tff(c_32,plain,(
    r1_xboole_0('#skF_9','#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_58,plain,(
    ! [A_101,B_102,C_103] :
      ( ~ r1_xboole_0(A_101,B_102)
      | ~ r2_hidden(C_103,B_102)
      | ~ r2_hidden(C_103,A_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_61,plain,(
    ! [C_103] :
      ( ~ r2_hidden(C_103,'#skF_10')
      | ~ r2_hidden(C_103,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_32,c_58])).

tff(c_143,plain,(
    ! [A_150,A_151,B_152] :
      ( ~ r2_hidden(k2_waybel_0(A_150,A_151,'#skF_3'(A_151,B_152,'#skF_2'(A_150,A_151,'#skF_10'))),'#skF_9')
      | ~ m1_subset_1('#skF_3'(A_151,B_152,'#skF_2'(A_150,A_151,'#skF_10')),u1_struct_0(A_151))
      | ~ r1_waybel_0(A_150,A_151,'#skF_10')
      | ~ l1_waybel_0(A_151,A_150)
      | ~ l1_struct_0(A_150)
      | v2_struct_0(A_150)
      | ~ m1_subset_1('#skF_2'(A_150,A_151,'#skF_10'),u1_struct_0(A_151))
      | ~ m1_subset_1(B_152,u1_struct_0(A_151))
      | ~ v7_waybel_0(A_151)
      | ~ l1_orders_2(A_151)
      | v2_struct_0(A_151) ) ),
    inference(resolution,[status(thm)],[c_131,c_61])).

tff(c_149,plain,(
    ! [A_153,A_154] :
      ( ~ r1_waybel_0(A_153,A_154,'#skF_10')
      | ~ m1_subset_1('#skF_3'(A_154,'#skF_2'(A_153,A_154,'#skF_9'),'#skF_2'(A_153,A_154,'#skF_10')),u1_struct_0(A_154))
      | ~ r1_waybel_0(A_153,A_154,'#skF_9')
      | ~ l1_waybel_0(A_154,A_153)
      | ~ l1_struct_0(A_153)
      | v2_struct_0(A_153)
      | ~ m1_subset_1('#skF_2'(A_153,A_154,'#skF_10'),u1_struct_0(A_154))
      | ~ m1_subset_1('#skF_2'(A_153,A_154,'#skF_9'),u1_struct_0(A_154))
      | ~ v7_waybel_0(A_154)
      | ~ l1_orders_2(A_154)
      | v2_struct_0(A_154) ) ),
    inference(resolution,[status(thm)],[c_129,c_143])).

tff(c_155,plain,(
    ! [A_155,A_156] :
      ( ~ r1_waybel_0(A_155,A_156,'#skF_10')
      | ~ r1_waybel_0(A_155,A_156,'#skF_9')
      | ~ l1_waybel_0(A_156,A_155)
      | ~ l1_struct_0(A_155)
      | v2_struct_0(A_155)
      | ~ m1_subset_1('#skF_2'(A_155,A_156,'#skF_10'),u1_struct_0(A_156))
      | ~ m1_subset_1('#skF_2'(A_155,A_156,'#skF_9'),u1_struct_0(A_156))
      | ~ v7_waybel_0(A_156)
      | ~ l1_orders_2(A_156)
      | v2_struct_0(A_156) ) ),
    inference(resolution,[status(thm)],[c_22,c_149])).

tff(c_172,plain,(
    ! [A_162,B_163] :
      ( ~ r1_waybel_0(A_162,B_163,'#skF_9')
      | ~ m1_subset_1('#skF_2'(A_162,B_163,'#skF_9'),u1_struct_0(B_163))
      | ~ v7_waybel_0(B_163)
      | ~ l1_orders_2(B_163)
      | ~ r1_waybel_0(A_162,B_163,'#skF_10')
      | ~ l1_waybel_0(B_163,A_162)
      | v2_struct_0(B_163)
      | ~ l1_struct_0(A_162)
      | v2_struct_0(A_162) ) ),
    inference(resolution,[status(thm)],[c_4,c_155])).

tff(c_178,plain,(
    ! [B_164,A_165] :
      ( ~ v7_waybel_0(B_164)
      | ~ l1_orders_2(B_164)
      | ~ r1_waybel_0(A_165,B_164,'#skF_10')
      | ~ r1_waybel_0(A_165,B_164,'#skF_9')
      | ~ l1_waybel_0(B_164,A_165)
      | v2_struct_0(B_164)
      | ~ l1_struct_0(A_165)
      | v2_struct_0(A_165) ) ),
    inference(resolution,[status(thm)],[c_4,c_172])).

tff(c_181,plain,
    ( ~ v7_waybel_0('#skF_8')
    | ~ l1_orders_2('#skF_8')
    | ~ r1_waybel_0('#skF_7','#skF_8','#skF_9')
    | ~ l1_waybel_0('#skF_8','#skF_7')
    | v2_struct_0('#skF_8')
    | ~ l1_struct_0('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_34,c_178])).

tff(c_184,plain,
    ( v2_struct_0('#skF_8')
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_38,c_36,c_55,c_40,c_181])).

tff(c_186,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_44,c_184])).

%------------------------------------------------------------------------------
