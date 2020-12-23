%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:46 EST 2020

% Result     : Theorem 2.38s
% Output     : CNFRefutation 2.38s
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
%$ r1_waybel_0 > r1_orders_2 > r2_hidden > r1_xboole_0 > m1_subset_1 > l1_waybel_0 > v7_waybel_0 > v4_orders_2 > v2_struct_0 > l1_struct_0 > l1_orders_2 > k2_waybel_0 > #nlpp > u1_struct_0 > #skF_5 > #skF_4 > #skF_7 > #skF_10 > #skF_2 > #skF_9 > #skF_8 > #skF_3 > #skF_1 > #skF_6

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': $i > $i )).

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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(r1_waybel_0,type,(
    r1_waybel_0: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_118,negated_conjecture,(
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

tff(f_74,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ! [B] :
          ( l1_waybel_0(B,A)
         => l1_orders_2(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_waybel_0)).

tff(f_67,axiom,(
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

tff(f_94,axiom,(
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

tff(f_43,axiom,(
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
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_44,plain,(
    ~ v2_struct_0('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_46,plain,(
    l1_struct_0('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_38,plain,(
    l1_waybel_0('#skF_8','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_36,plain,(
    r1_waybel_0('#skF_7','#skF_8','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_49,plain,(
    ! [B_95,A_96] :
      ( l1_orders_2(B_95)
      | ~ l1_waybel_0(B_95,A_96)
      | ~ l1_struct_0(A_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_52,plain,
    ( l1_orders_2('#skF_8')
    | ~ l1_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_38,c_49])).

tff(c_55,plain,(
    l1_orders_2('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_52])).

tff(c_40,plain,(
    v7_waybel_0('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_34,plain,(
    r1_waybel_0('#skF_7','#skF_8','#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_10,plain,(
    ! [A_6,B_34,C_48] :
      ( m1_subset_1('#skF_3'(A_6,B_34,C_48),u1_struct_0(B_34))
      | ~ r1_waybel_0(A_6,B_34,C_48)
      | ~ l1_waybel_0(B_34,A_6)
      | v2_struct_0(B_34)
      | ~ l1_struct_0(A_6)
      | v2_struct_0(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_30,plain,(
    ! [A_62,B_77,C_81] :
      ( m1_subset_1('#skF_4'(A_62,B_77,C_81),u1_struct_0(A_62))
      | ~ m1_subset_1(C_81,u1_struct_0(A_62))
      | ~ m1_subset_1(B_77,u1_struct_0(A_62))
      | ~ v7_waybel_0(A_62)
      | ~ l1_orders_2(A_62)
      | v2_struct_0(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_28,plain,(
    ! [A_62,B_77,C_81] :
      ( r1_orders_2(A_62,B_77,'#skF_4'(A_62,B_77,C_81))
      | ~ m1_subset_1(C_81,u1_struct_0(A_62))
      | ~ m1_subset_1(B_77,u1_struct_0(A_62))
      | ~ v7_waybel_0(A_62)
      | ~ l1_orders_2(A_62)
      | v2_struct_0(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_114,plain,(
    ! [A_135,B_136,E_137,C_138] :
      ( r2_hidden(k2_waybel_0(A_135,B_136,E_137),C_138)
      | ~ r1_orders_2(B_136,'#skF_3'(A_135,B_136,C_138),E_137)
      | ~ m1_subset_1(E_137,u1_struct_0(B_136))
      | ~ r1_waybel_0(A_135,B_136,C_138)
      | ~ l1_waybel_0(B_136,A_135)
      | v2_struct_0(B_136)
      | ~ l1_struct_0(A_135)
      | v2_struct_0(A_135) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_129,plain,(
    ! [A_135,A_62,C_138,C_81] :
      ( r2_hidden(k2_waybel_0(A_135,A_62,'#skF_4'(A_62,'#skF_3'(A_135,A_62,C_138),C_81)),C_138)
      | ~ m1_subset_1('#skF_4'(A_62,'#skF_3'(A_135,A_62,C_138),C_81),u1_struct_0(A_62))
      | ~ r1_waybel_0(A_135,A_62,C_138)
      | ~ l1_waybel_0(A_62,A_135)
      | ~ l1_struct_0(A_135)
      | v2_struct_0(A_135)
      | ~ m1_subset_1(C_81,u1_struct_0(A_62))
      | ~ m1_subset_1('#skF_3'(A_135,A_62,C_138),u1_struct_0(A_62))
      | ~ v7_waybel_0(A_62)
      | ~ l1_orders_2(A_62)
      | v2_struct_0(A_62) ) ),
    inference(resolution,[status(thm)],[c_28,c_114])).

tff(c_26,plain,(
    ! [A_62,C_81,B_77] :
      ( r1_orders_2(A_62,C_81,'#skF_4'(A_62,B_77,C_81))
      | ~ m1_subset_1(C_81,u1_struct_0(A_62))
      | ~ m1_subset_1(B_77,u1_struct_0(A_62))
      | ~ v7_waybel_0(A_62)
      | ~ l1_orders_2(A_62)
      | v2_struct_0(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_131,plain,(
    ! [A_142,A_143,B_144,C_145] :
      ( r2_hidden(k2_waybel_0(A_142,A_143,'#skF_4'(A_143,B_144,'#skF_3'(A_142,A_143,C_145))),C_145)
      | ~ m1_subset_1('#skF_4'(A_143,B_144,'#skF_3'(A_142,A_143,C_145)),u1_struct_0(A_143))
      | ~ r1_waybel_0(A_142,A_143,C_145)
      | ~ l1_waybel_0(A_143,A_142)
      | ~ l1_struct_0(A_142)
      | v2_struct_0(A_142)
      | ~ m1_subset_1('#skF_3'(A_142,A_143,C_145),u1_struct_0(A_143))
      | ~ m1_subset_1(B_144,u1_struct_0(A_143))
      | ~ v7_waybel_0(A_143)
      | ~ l1_orders_2(A_143)
      | v2_struct_0(A_143) ) ),
    inference(resolution,[status(thm)],[c_26,c_114])).

tff(c_32,plain,(
    r1_xboole_0('#skF_9','#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_58,plain,(
    ! [A_101,B_102,C_103] :
      ( ~ r1_xboole_0(A_101,B_102)
      | ~ r2_hidden(C_103,B_102)
      | ~ r2_hidden(C_103,A_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_61,plain,(
    ! [C_103] :
      ( ~ r2_hidden(C_103,'#skF_10')
      | ~ r2_hidden(C_103,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_32,c_58])).

tff(c_143,plain,(
    ! [A_150,A_151,B_152] :
      ( ~ r2_hidden(k2_waybel_0(A_150,A_151,'#skF_4'(A_151,B_152,'#skF_3'(A_150,A_151,'#skF_10'))),'#skF_9')
      | ~ m1_subset_1('#skF_4'(A_151,B_152,'#skF_3'(A_150,A_151,'#skF_10')),u1_struct_0(A_151))
      | ~ r1_waybel_0(A_150,A_151,'#skF_10')
      | ~ l1_waybel_0(A_151,A_150)
      | ~ l1_struct_0(A_150)
      | v2_struct_0(A_150)
      | ~ m1_subset_1('#skF_3'(A_150,A_151,'#skF_10'),u1_struct_0(A_151))
      | ~ m1_subset_1(B_152,u1_struct_0(A_151))
      | ~ v7_waybel_0(A_151)
      | ~ l1_orders_2(A_151)
      | v2_struct_0(A_151) ) ),
    inference(resolution,[status(thm)],[c_131,c_61])).

tff(c_149,plain,(
    ! [A_153,A_154] :
      ( ~ r1_waybel_0(A_153,A_154,'#skF_10')
      | ~ m1_subset_1('#skF_4'(A_154,'#skF_3'(A_153,A_154,'#skF_9'),'#skF_3'(A_153,A_154,'#skF_10')),u1_struct_0(A_154))
      | ~ r1_waybel_0(A_153,A_154,'#skF_9')
      | ~ l1_waybel_0(A_154,A_153)
      | ~ l1_struct_0(A_153)
      | v2_struct_0(A_153)
      | ~ m1_subset_1('#skF_3'(A_153,A_154,'#skF_10'),u1_struct_0(A_154))
      | ~ m1_subset_1('#skF_3'(A_153,A_154,'#skF_9'),u1_struct_0(A_154))
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
      | ~ m1_subset_1('#skF_3'(A_155,A_156,'#skF_10'),u1_struct_0(A_156))
      | ~ m1_subset_1('#skF_3'(A_155,A_156,'#skF_9'),u1_struct_0(A_156))
      | ~ v7_waybel_0(A_156)
      | ~ l1_orders_2(A_156)
      | v2_struct_0(A_156) ) ),
    inference(resolution,[status(thm)],[c_30,c_149])).

tff(c_172,plain,(
    ! [A_162,B_163] :
      ( ~ r1_waybel_0(A_162,B_163,'#skF_9')
      | ~ m1_subset_1('#skF_3'(A_162,B_163,'#skF_9'),u1_struct_0(B_163))
      | ~ v7_waybel_0(B_163)
      | ~ l1_orders_2(B_163)
      | ~ r1_waybel_0(A_162,B_163,'#skF_10')
      | ~ l1_waybel_0(B_163,A_162)
      | v2_struct_0(B_163)
      | ~ l1_struct_0(A_162)
      | v2_struct_0(A_162) ) ),
    inference(resolution,[status(thm)],[c_10,c_155])).

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
    inference(resolution,[status(thm)],[c_10,c_172])).

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
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n018.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 13:06:41 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.38/1.27  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.38/1.27  
% 2.38/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.38/1.28  %$ r1_waybel_0 > r1_orders_2 > r2_hidden > r1_xboole_0 > m1_subset_1 > l1_waybel_0 > v7_waybel_0 > v4_orders_2 > v2_struct_0 > l1_struct_0 > l1_orders_2 > k2_waybel_0 > #nlpp > u1_struct_0 > #skF_5 > #skF_4 > #skF_7 > #skF_10 > #skF_2 > #skF_9 > #skF_8 > #skF_3 > #skF_1 > #skF_6
% 2.38/1.28  
% 2.38/1.28  %Foreground sorts:
% 2.38/1.28  
% 2.38/1.28  
% 2.38/1.28  %Background operators:
% 2.38/1.28  
% 2.38/1.28  
% 2.38/1.28  %Foreground operators:
% 2.38/1.28  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.38/1.28  tff('#skF_5', type, '#skF_5': $i > $i).
% 2.38/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.38/1.28  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.38/1.28  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 2.38/1.28  tff(k2_waybel_0, type, k2_waybel_0: ($i * $i * $i) > $i).
% 2.38/1.28  tff(v7_waybel_0, type, v7_waybel_0: $i > $o).
% 2.38/1.28  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.38/1.28  tff('#skF_7', type, '#skF_7': $i).
% 2.38/1.28  tff('#skF_10', type, '#skF_10': $i).
% 2.38/1.28  tff(r1_waybel_0, type, r1_waybel_0: ($i * $i * $i) > $o).
% 2.38/1.28  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.38/1.28  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.38/1.28  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.38/1.28  tff('#skF_9', type, '#skF_9': $i).
% 2.38/1.28  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.38/1.28  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.38/1.28  tff('#skF_8', type, '#skF_8': $i).
% 2.38/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.38/1.28  tff(l1_waybel_0, type, l1_waybel_0: ($i * $i) > $o).
% 2.38/1.28  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.38/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.38/1.28  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.38/1.28  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.38/1.28  tff('#skF_6', type, '#skF_6': $i > $i).
% 2.38/1.28  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.38/1.28  
% 2.38/1.29  tff(f_118, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => (![C, D]: ~((r1_waybel_0(A, B, C) & r1_waybel_0(A, B, D)) & r1_xboole_0(C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_yellow_6)).
% 2.38/1.29  tff(f_74, axiom, (![A]: (l1_struct_0(A) => (![B]: (l1_waybel_0(B, A) => l1_orders_2(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_waybel_0)).
% 2.38/1.29  tff(f_67, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((~v2_struct_0(B) & l1_waybel_0(B, A)) => (![C]: (r1_waybel_0(A, B, C) <=> (?[D]: (m1_subset_1(D, u1_struct_0(B)) & (![E]: (m1_subset_1(E, u1_struct_0(B)) => (r1_orders_2(B, D, E) => r2_hidden(k2_waybel_0(A, B, E), C)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d11_waybel_0)).
% 2.38/1.29  tff(f_94, axiom, (![A]: ((~v2_struct_0(A) & l1_orders_2(A)) => (v7_waybel_0(A) <=> (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (?[D]: ((m1_subset_1(D, u1_struct_0(A)) & r1_orders_2(A, B, D)) & r1_orders_2(A, C, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_yellow_6)).
% 2.38/1.29  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.38/1.29  tff(c_48, plain, (~v2_struct_0('#skF_7')), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.38/1.29  tff(c_44, plain, (~v2_struct_0('#skF_8')), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.38/1.29  tff(c_46, plain, (l1_struct_0('#skF_7')), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.38/1.29  tff(c_38, plain, (l1_waybel_0('#skF_8', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.38/1.29  tff(c_36, plain, (r1_waybel_0('#skF_7', '#skF_8', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.38/1.29  tff(c_49, plain, (![B_95, A_96]: (l1_orders_2(B_95) | ~l1_waybel_0(B_95, A_96) | ~l1_struct_0(A_96))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.38/1.29  tff(c_52, plain, (l1_orders_2('#skF_8') | ~l1_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_38, c_49])).
% 2.38/1.29  tff(c_55, plain, (l1_orders_2('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_52])).
% 2.38/1.29  tff(c_40, plain, (v7_waybel_0('#skF_8')), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.38/1.29  tff(c_34, plain, (r1_waybel_0('#skF_7', '#skF_8', '#skF_10')), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.38/1.29  tff(c_10, plain, (![A_6, B_34, C_48]: (m1_subset_1('#skF_3'(A_6, B_34, C_48), u1_struct_0(B_34)) | ~r1_waybel_0(A_6, B_34, C_48) | ~l1_waybel_0(B_34, A_6) | v2_struct_0(B_34) | ~l1_struct_0(A_6) | v2_struct_0(A_6))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.38/1.29  tff(c_30, plain, (![A_62, B_77, C_81]: (m1_subset_1('#skF_4'(A_62, B_77, C_81), u1_struct_0(A_62)) | ~m1_subset_1(C_81, u1_struct_0(A_62)) | ~m1_subset_1(B_77, u1_struct_0(A_62)) | ~v7_waybel_0(A_62) | ~l1_orders_2(A_62) | v2_struct_0(A_62))), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.38/1.29  tff(c_28, plain, (![A_62, B_77, C_81]: (r1_orders_2(A_62, B_77, '#skF_4'(A_62, B_77, C_81)) | ~m1_subset_1(C_81, u1_struct_0(A_62)) | ~m1_subset_1(B_77, u1_struct_0(A_62)) | ~v7_waybel_0(A_62) | ~l1_orders_2(A_62) | v2_struct_0(A_62))), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.38/1.29  tff(c_114, plain, (![A_135, B_136, E_137, C_138]: (r2_hidden(k2_waybel_0(A_135, B_136, E_137), C_138) | ~r1_orders_2(B_136, '#skF_3'(A_135, B_136, C_138), E_137) | ~m1_subset_1(E_137, u1_struct_0(B_136)) | ~r1_waybel_0(A_135, B_136, C_138) | ~l1_waybel_0(B_136, A_135) | v2_struct_0(B_136) | ~l1_struct_0(A_135) | v2_struct_0(A_135))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.38/1.29  tff(c_129, plain, (![A_135, A_62, C_138, C_81]: (r2_hidden(k2_waybel_0(A_135, A_62, '#skF_4'(A_62, '#skF_3'(A_135, A_62, C_138), C_81)), C_138) | ~m1_subset_1('#skF_4'(A_62, '#skF_3'(A_135, A_62, C_138), C_81), u1_struct_0(A_62)) | ~r1_waybel_0(A_135, A_62, C_138) | ~l1_waybel_0(A_62, A_135) | ~l1_struct_0(A_135) | v2_struct_0(A_135) | ~m1_subset_1(C_81, u1_struct_0(A_62)) | ~m1_subset_1('#skF_3'(A_135, A_62, C_138), u1_struct_0(A_62)) | ~v7_waybel_0(A_62) | ~l1_orders_2(A_62) | v2_struct_0(A_62))), inference(resolution, [status(thm)], [c_28, c_114])).
% 2.38/1.29  tff(c_26, plain, (![A_62, C_81, B_77]: (r1_orders_2(A_62, C_81, '#skF_4'(A_62, B_77, C_81)) | ~m1_subset_1(C_81, u1_struct_0(A_62)) | ~m1_subset_1(B_77, u1_struct_0(A_62)) | ~v7_waybel_0(A_62) | ~l1_orders_2(A_62) | v2_struct_0(A_62))), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.38/1.29  tff(c_131, plain, (![A_142, A_143, B_144, C_145]: (r2_hidden(k2_waybel_0(A_142, A_143, '#skF_4'(A_143, B_144, '#skF_3'(A_142, A_143, C_145))), C_145) | ~m1_subset_1('#skF_4'(A_143, B_144, '#skF_3'(A_142, A_143, C_145)), u1_struct_0(A_143)) | ~r1_waybel_0(A_142, A_143, C_145) | ~l1_waybel_0(A_143, A_142) | ~l1_struct_0(A_142) | v2_struct_0(A_142) | ~m1_subset_1('#skF_3'(A_142, A_143, C_145), u1_struct_0(A_143)) | ~m1_subset_1(B_144, u1_struct_0(A_143)) | ~v7_waybel_0(A_143) | ~l1_orders_2(A_143) | v2_struct_0(A_143))), inference(resolution, [status(thm)], [c_26, c_114])).
% 2.38/1.29  tff(c_32, plain, (r1_xboole_0('#skF_9', '#skF_10')), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.38/1.29  tff(c_58, plain, (![A_101, B_102, C_103]: (~r1_xboole_0(A_101, B_102) | ~r2_hidden(C_103, B_102) | ~r2_hidden(C_103, A_101))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.38/1.29  tff(c_61, plain, (![C_103]: (~r2_hidden(C_103, '#skF_10') | ~r2_hidden(C_103, '#skF_9'))), inference(resolution, [status(thm)], [c_32, c_58])).
% 2.38/1.29  tff(c_143, plain, (![A_150, A_151, B_152]: (~r2_hidden(k2_waybel_0(A_150, A_151, '#skF_4'(A_151, B_152, '#skF_3'(A_150, A_151, '#skF_10'))), '#skF_9') | ~m1_subset_1('#skF_4'(A_151, B_152, '#skF_3'(A_150, A_151, '#skF_10')), u1_struct_0(A_151)) | ~r1_waybel_0(A_150, A_151, '#skF_10') | ~l1_waybel_0(A_151, A_150) | ~l1_struct_0(A_150) | v2_struct_0(A_150) | ~m1_subset_1('#skF_3'(A_150, A_151, '#skF_10'), u1_struct_0(A_151)) | ~m1_subset_1(B_152, u1_struct_0(A_151)) | ~v7_waybel_0(A_151) | ~l1_orders_2(A_151) | v2_struct_0(A_151))), inference(resolution, [status(thm)], [c_131, c_61])).
% 2.38/1.29  tff(c_149, plain, (![A_153, A_154]: (~r1_waybel_0(A_153, A_154, '#skF_10') | ~m1_subset_1('#skF_4'(A_154, '#skF_3'(A_153, A_154, '#skF_9'), '#skF_3'(A_153, A_154, '#skF_10')), u1_struct_0(A_154)) | ~r1_waybel_0(A_153, A_154, '#skF_9') | ~l1_waybel_0(A_154, A_153) | ~l1_struct_0(A_153) | v2_struct_0(A_153) | ~m1_subset_1('#skF_3'(A_153, A_154, '#skF_10'), u1_struct_0(A_154)) | ~m1_subset_1('#skF_3'(A_153, A_154, '#skF_9'), u1_struct_0(A_154)) | ~v7_waybel_0(A_154) | ~l1_orders_2(A_154) | v2_struct_0(A_154))), inference(resolution, [status(thm)], [c_129, c_143])).
% 2.38/1.29  tff(c_155, plain, (![A_155, A_156]: (~r1_waybel_0(A_155, A_156, '#skF_10') | ~r1_waybel_0(A_155, A_156, '#skF_9') | ~l1_waybel_0(A_156, A_155) | ~l1_struct_0(A_155) | v2_struct_0(A_155) | ~m1_subset_1('#skF_3'(A_155, A_156, '#skF_10'), u1_struct_0(A_156)) | ~m1_subset_1('#skF_3'(A_155, A_156, '#skF_9'), u1_struct_0(A_156)) | ~v7_waybel_0(A_156) | ~l1_orders_2(A_156) | v2_struct_0(A_156))), inference(resolution, [status(thm)], [c_30, c_149])).
% 2.38/1.29  tff(c_172, plain, (![A_162, B_163]: (~r1_waybel_0(A_162, B_163, '#skF_9') | ~m1_subset_1('#skF_3'(A_162, B_163, '#skF_9'), u1_struct_0(B_163)) | ~v7_waybel_0(B_163) | ~l1_orders_2(B_163) | ~r1_waybel_0(A_162, B_163, '#skF_10') | ~l1_waybel_0(B_163, A_162) | v2_struct_0(B_163) | ~l1_struct_0(A_162) | v2_struct_0(A_162))), inference(resolution, [status(thm)], [c_10, c_155])).
% 2.38/1.29  tff(c_178, plain, (![B_164, A_165]: (~v7_waybel_0(B_164) | ~l1_orders_2(B_164) | ~r1_waybel_0(A_165, B_164, '#skF_10') | ~r1_waybel_0(A_165, B_164, '#skF_9') | ~l1_waybel_0(B_164, A_165) | v2_struct_0(B_164) | ~l1_struct_0(A_165) | v2_struct_0(A_165))), inference(resolution, [status(thm)], [c_10, c_172])).
% 2.38/1.29  tff(c_181, plain, (~v7_waybel_0('#skF_8') | ~l1_orders_2('#skF_8') | ~r1_waybel_0('#skF_7', '#skF_8', '#skF_9') | ~l1_waybel_0('#skF_8', '#skF_7') | v2_struct_0('#skF_8') | ~l1_struct_0('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_34, c_178])).
% 2.38/1.29  tff(c_184, plain, (v2_struct_0('#skF_8') | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_38, c_36, c_55, c_40, c_181])).
% 2.38/1.29  tff(c_186, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_44, c_184])).
% 2.38/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.38/1.29  
% 2.38/1.29  Inference rules
% 2.38/1.29  ----------------------
% 2.38/1.29  #Ref     : 0
% 2.38/1.29  #Sup     : 22
% 2.38/1.29  #Fact    : 0
% 2.38/1.29  #Define  : 0
% 2.38/1.29  #Split   : 0
% 2.38/1.29  #Chain   : 0
% 2.38/1.29  #Close   : 0
% 2.38/1.29  
% 2.38/1.29  Ordering : KBO
% 2.38/1.29  
% 2.38/1.29  Simplification rules
% 2.38/1.29  ----------------------
% 2.38/1.29  #Subsume      : 4
% 2.38/1.29  #Demod        : 7
% 2.38/1.29  #Tautology    : 4
% 2.38/1.29  #SimpNegUnit  : 1
% 2.38/1.29  #BackRed      : 0
% 2.38/1.29  
% 2.38/1.29  #Partial instantiations: 0
% 2.38/1.29  #Strategies tried      : 1
% 2.38/1.29  
% 2.38/1.29  Timing (in seconds)
% 2.38/1.29  ----------------------
% 2.38/1.29  Preprocessing        : 0.30
% 2.38/1.29  Parsing              : 0.16
% 2.38/1.30  CNF conversion       : 0.03
% 2.38/1.30  Main loop            : 0.23
% 2.38/1.30  Inferencing          : 0.11
% 2.38/1.30  Reduction            : 0.05
% 2.38/1.30  Demodulation         : 0.04
% 2.38/1.30  BG Simplification    : 0.02
% 2.38/1.30  Subsumption          : 0.04
% 2.38/1.30  Abstraction          : 0.01
% 2.38/1.30  MUC search           : 0.00
% 2.38/1.30  Cooper               : 0.00
% 2.38/1.30  Total                : 0.57
% 2.38/1.30  Index Insertion      : 0.00
% 2.38/1.30  Index Deletion       : 0.00
% 2.38/1.30  Index Matching       : 0.00
% 2.38/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
