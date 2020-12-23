%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:49 EST 2020

% Result     : Theorem 2.14s
% Output     : CNFRefutation 2.45s
% Verified   : 
% Statistics : Number of formulae       :   67 (  92 expanded)
%              Number of leaves         :   38 (  52 expanded)
%              Depth                    :   12
%              Number of atoms          :  124 ( 223 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_waybel_0 > r1_waybel_0 > r1_orders_2 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > l1_waybel_0 > v7_waybel_0 > v4_orders_2 > v2_struct_0 > l1_struct_0 > k2_waybel_0 > k6_subset_1 > k4_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(r2_waybel_0,type,(
    r2_waybel_0: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_waybel_0,type,(
    k2_waybel_0: ( $i * $i * $i ) > $i )).

tff(v7_waybel_0,type,(
    v7_waybel_0: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_waybel_0,type,(
    r1_waybel_0: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_129,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & l1_struct_0(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & v4_orders_2(B)
              & v7_waybel_0(B)
              & l1_waybel_0(B,A) )
           => r1_waybel_0(A,B,u1_struct_0(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_yellow_6)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_36,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),B)
        & r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l24_zfmisc_1)).

tff(f_34,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_48,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_89,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & l1_waybel_0(B,A) )
         => ! [C] :
              ( r2_waybel_0(A,B,C)
            <=> ~ r1_waybel_0(A,B,k6_subset_1(u1_struct_0(A),C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_waybel_0)).

tff(f_111,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & l1_waybel_0(B,A) )
         => ! [C,D] :
              ( r1_tarski(C,D)
             => ( ( r1_waybel_0(A,B,C)
                 => r1_waybel_0(A,B,D) )
                & ( r2_waybel_0(A,B,C)
                 => r2_waybel_0(A,B,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_waybel_0)).

tff(f_46,axiom,(
    ! [A] :
    ? [B] : m1_subset_1(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).

tff(f_72,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & l1_waybel_0(B,A) )
         => ! [C] :
              ( r2_waybel_0(A,B,C)
            <=> ! [D] :
                  ( m1_subset_1(D,u1_struct_0(B))
                 => ? [E] :
                      ( m1_subset_1(E,u1_struct_0(B))
                      & r1_orders_2(B,D,E)
                      & r2_hidden(k2_waybel_0(A,B,E),C) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_waybel_0)).

tff(c_50,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_46,plain,(
    ~ v2_struct_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_48,plain,(
    l1_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_40,plain,(
    l1_waybel_0('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_89,plain,(
    ! [A_96,B_97] :
      ( r2_hidden('#skF_1'(A_96,B_97),A_96)
      | r1_tarski(A_96,B_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_10,plain,(
    ! [A_7] : r1_xboole_0(A_7,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_82,plain,(
    ! [A_93,B_94] :
      ( ~ r2_hidden(A_93,B_94)
      | ~ r1_xboole_0(k1_tarski(A_93),B_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_87,plain,(
    ! [A_93] : ~ r2_hidden(A_93,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_10,c_82])).

tff(c_94,plain,(
    ! [B_97] : r1_tarski(k1_xboole_0,B_97) ),
    inference(resolution,[status(thm)],[c_89,c_87])).

tff(c_8,plain,(
    ! [A_6] : k4_xboole_0(A_6,k1_xboole_0) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_18,plain,(
    ! [A_13,B_14] : k6_subset_1(A_13,B_14) = k4_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_32,plain,(
    ! [A_68,B_72,C_74] :
      ( r2_waybel_0(A_68,B_72,C_74)
      | r1_waybel_0(A_68,B_72,k6_subset_1(u1_struct_0(A_68),C_74))
      | ~ l1_waybel_0(B_72,A_68)
      | v2_struct_0(B_72)
      | ~ l1_struct_0(A_68)
      | v2_struct_0(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_146,plain,(
    ! [A_122,B_123,C_124] :
      ( r2_waybel_0(A_122,B_123,C_124)
      | r1_waybel_0(A_122,B_123,k4_xboole_0(u1_struct_0(A_122),C_124))
      | ~ l1_waybel_0(B_123,A_122)
      | v2_struct_0(B_123)
      | ~ l1_struct_0(A_122)
      | v2_struct_0(A_122) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_32])).

tff(c_155,plain,(
    ! [A_125,B_126] :
      ( r2_waybel_0(A_125,B_126,k1_xboole_0)
      | r1_waybel_0(A_125,B_126,u1_struct_0(A_125))
      | ~ l1_waybel_0(B_126,A_125)
      | v2_struct_0(B_126)
      | ~ l1_struct_0(A_125)
      | v2_struct_0(A_125) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_146])).

tff(c_38,plain,(
    ~ r1_waybel_0('#skF_5','#skF_6',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_161,plain,
    ( r2_waybel_0('#skF_5','#skF_6',k1_xboole_0)
    | ~ l1_waybel_0('#skF_6','#skF_5')
    | v2_struct_0('#skF_6')
    | ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_155,c_38])).

tff(c_165,plain,
    ( r2_waybel_0('#skF_5','#skF_6',k1_xboole_0)
    | v2_struct_0('#skF_6')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_40,c_161])).

tff(c_166,plain,(
    r2_waybel_0('#skF_5','#skF_6',k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_46,c_165])).

tff(c_167,plain,(
    ! [A_127,B_128,D_129,C_130] :
      ( r2_waybel_0(A_127,B_128,D_129)
      | ~ r2_waybel_0(A_127,B_128,C_130)
      | ~ r1_tarski(C_130,D_129)
      | ~ l1_waybel_0(B_128,A_127)
      | v2_struct_0(B_128)
      | ~ l1_struct_0(A_127)
      | v2_struct_0(A_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_169,plain,(
    ! [D_129] :
      ( r2_waybel_0('#skF_5','#skF_6',D_129)
      | ~ r1_tarski(k1_xboole_0,D_129)
      | ~ l1_waybel_0('#skF_6','#skF_5')
      | v2_struct_0('#skF_6')
      | ~ l1_struct_0('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_166,c_167])).

tff(c_172,plain,(
    ! [D_129] :
      ( r2_waybel_0('#skF_5','#skF_6',D_129)
      | v2_struct_0('#skF_6')
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_40,c_94,c_169])).

tff(c_173,plain,(
    ! [D_129] : r2_waybel_0('#skF_5','#skF_6',D_129) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_46,c_172])).

tff(c_16,plain,(
    ! [A_11] : m1_subset_1('#skF_2'(A_11),A_11) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_204,plain,(
    ! [A_151,B_152,C_153,D_154] :
      ( r2_hidden(k2_waybel_0(A_151,B_152,'#skF_4'(A_151,B_152,C_153,D_154)),C_153)
      | ~ m1_subset_1(D_154,u1_struct_0(B_152))
      | ~ r2_waybel_0(A_151,B_152,C_153)
      | ~ l1_waybel_0(B_152,A_151)
      | v2_struct_0(B_152)
      | ~ l1_struct_0(A_151)
      | v2_struct_0(A_151) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_213,plain,(
    ! [D_155,B_156,A_157] :
      ( ~ m1_subset_1(D_155,u1_struct_0(B_156))
      | ~ r2_waybel_0(A_157,B_156,k1_xboole_0)
      | ~ l1_waybel_0(B_156,A_157)
      | v2_struct_0(B_156)
      | ~ l1_struct_0(A_157)
      | v2_struct_0(A_157) ) ),
    inference(resolution,[status(thm)],[c_204,c_87])).

tff(c_223,plain,(
    ! [A_158,B_159] :
      ( ~ r2_waybel_0(A_158,B_159,k1_xboole_0)
      | ~ l1_waybel_0(B_159,A_158)
      | v2_struct_0(B_159)
      | ~ l1_struct_0(A_158)
      | v2_struct_0(A_158) ) ),
    inference(resolution,[status(thm)],[c_16,c_213])).

tff(c_227,plain,
    ( ~ l1_waybel_0('#skF_6','#skF_5')
    | v2_struct_0('#skF_6')
    | ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_173,c_223])).

tff(c_230,plain,
    ( v2_struct_0('#skF_6')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_40,c_227])).

tff(c_232,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_46,c_230])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:02:23 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.14/1.30  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.14/1.30  
% 2.14/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.14/1.31  %$ r2_waybel_0 > r1_waybel_0 > r1_orders_2 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > l1_waybel_0 > v7_waybel_0 > v4_orders_2 > v2_struct_0 > l1_struct_0 > k2_waybel_0 > k6_subset_1 > k4_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_1
% 2.14/1.31  
% 2.14/1.31  %Foreground sorts:
% 2.14/1.31  
% 2.14/1.31  
% 2.14/1.31  %Background operators:
% 2.14/1.31  
% 2.14/1.31  
% 2.14/1.31  %Foreground operators:
% 2.14/1.31  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.14/1.31  tff(r2_waybel_0, type, r2_waybel_0: ($i * $i * $i) > $o).
% 2.14/1.31  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.14/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.14/1.31  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.14/1.31  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.14/1.31  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.14/1.31  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 2.14/1.31  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.14/1.31  tff(k2_waybel_0, type, k2_waybel_0: ($i * $i * $i) > $i).
% 2.14/1.31  tff(v7_waybel_0, type, v7_waybel_0: $i > $o).
% 2.14/1.31  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.14/1.31  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.14/1.31  tff('#skF_5', type, '#skF_5': $i).
% 2.14/1.31  tff(r1_waybel_0, type, r1_waybel_0: ($i * $i * $i) > $o).
% 2.14/1.31  tff('#skF_6', type, '#skF_6': $i).
% 2.14/1.31  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.14/1.31  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 2.14/1.31  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.14/1.31  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.14/1.31  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 2.14/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.14/1.31  tff(l1_waybel_0, type, l1_waybel_0: ($i * $i) > $o).
% 2.14/1.31  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.14/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.14/1.31  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.14/1.31  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.14/1.31  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.14/1.31  
% 2.45/1.32  tff(f_129, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => r1_waybel_0(A, B, u1_struct_0(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_yellow_6)).
% 2.45/1.32  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.45/1.32  tff(f_36, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.45/1.32  tff(f_43, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), B) & r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 2.45/1.32  tff(f_34, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 2.45/1.32  tff(f_48, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 2.45/1.32  tff(f_89, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((~v2_struct_0(B) & l1_waybel_0(B, A)) => (![C]: (r2_waybel_0(A, B, C) <=> ~r1_waybel_0(A, B, k6_subset_1(u1_struct_0(A), C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_waybel_0)).
% 2.45/1.32  tff(f_111, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((~v2_struct_0(B) & l1_waybel_0(B, A)) => (![C, D]: (r1_tarski(C, D) => ((r1_waybel_0(A, B, C) => r1_waybel_0(A, B, D)) & (r2_waybel_0(A, B, C) => r2_waybel_0(A, B, D))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_waybel_0)).
% 2.45/1.32  tff(f_46, axiom, (![A]: (?[B]: m1_subset_1(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', existence_m1_subset_1)).
% 2.45/1.32  tff(f_72, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((~v2_struct_0(B) & l1_waybel_0(B, A)) => (![C]: (r2_waybel_0(A, B, C) <=> (![D]: (m1_subset_1(D, u1_struct_0(B)) => (?[E]: ((m1_subset_1(E, u1_struct_0(B)) & r1_orders_2(B, D, E)) & r2_hidden(k2_waybel_0(A, B, E), C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d12_waybel_0)).
% 2.45/1.32  tff(c_50, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_129])).
% 2.45/1.32  tff(c_46, plain, (~v2_struct_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_129])).
% 2.45/1.32  tff(c_48, plain, (l1_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_129])).
% 2.45/1.32  tff(c_40, plain, (l1_waybel_0('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_129])).
% 2.45/1.32  tff(c_89, plain, (![A_96, B_97]: (r2_hidden('#skF_1'(A_96, B_97), A_96) | r1_tarski(A_96, B_97))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.45/1.32  tff(c_10, plain, (![A_7]: (r1_xboole_0(A_7, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.45/1.32  tff(c_82, plain, (![A_93, B_94]: (~r2_hidden(A_93, B_94) | ~r1_xboole_0(k1_tarski(A_93), B_94))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.45/1.32  tff(c_87, plain, (![A_93]: (~r2_hidden(A_93, k1_xboole_0))), inference(resolution, [status(thm)], [c_10, c_82])).
% 2.45/1.32  tff(c_94, plain, (![B_97]: (r1_tarski(k1_xboole_0, B_97))), inference(resolution, [status(thm)], [c_89, c_87])).
% 2.45/1.32  tff(c_8, plain, (![A_6]: (k4_xboole_0(A_6, k1_xboole_0)=A_6)), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.45/1.32  tff(c_18, plain, (![A_13, B_14]: (k6_subset_1(A_13, B_14)=k4_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.45/1.32  tff(c_32, plain, (![A_68, B_72, C_74]: (r2_waybel_0(A_68, B_72, C_74) | r1_waybel_0(A_68, B_72, k6_subset_1(u1_struct_0(A_68), C_74)) | ~l1_waybel_0(B_72, A_68) | v2_struct_0(B_72) | ~l1_struct_0(A_68) | v2_struct_0(A_68))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.45/1.32  tff(c_146, plain, (![A_122, B_123, C_124]: (r2_waybel_0(A_122, B_123, C_124) | r1_waybel_0(A_122, B_123, k4_xboole_0(u1_struct_0(A_122), C_124)) | ~l1_waybel_0(B_123, A_122) | v2_struct_0(B_123) | ~l1_struct_0(A_122) | v2_struct_0(A_122))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_32])).
% 2.45/1.32  tff(c_155, plain, (![A_125, B_126]: (r2_waybel_0(A_125, B_126, k1_xboole_0) | r1_waybel_0(A_125, B_126, u1_struct_0(A_125)) | ~l1_waybel_0(B_126, A_125) | v2_struct_0(B_126) | ~l1_struct_0(A_125) | v2_struct_0(A_125))), inference(superposition, [status(thm), theory('equality')], [c_8, c_146])).
% 2.45/1.32  tff(c_38, plain, (~r1_waybel_0('#skF_5', '#skF_6', u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_129])).
% 2.45/1.32  tff(c_161, plain, (r2_waybel_0('#skF_5', '#skF_6', k1_xboole_0) | ~l1_waybel_0('#skF_6', '#skF_5') | v2_struct_0('#skF_6') | ~l1_struct_0('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_155, c_38])).
% 2.45/1.32  tff(c_165, plain, (r2_waybel_0('#skF_5', '#skF_6', k1_xboole_0) | v2_struct_0('#skF_6') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_40, c_161])).
% 2.45/1.32  tff(c_166, plain, (r2_waybel_0('#skF_5', '#skF_6', k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_50, c_46, c_165])).
% 2.45/1.32  tff(c_167, plain, (![A_127, B_128, D_129, C_130]: (r2_waybel_0(A_127, B_128, D_129) | ~r2_waybel_0(A_127, B_128, C_130) | ~r1_tarski(C_130, D_129) | ~l1_waybel_0(B_128, A_127) | v2_struct_0(B_128) | ~l1_struct_0(A_127) | v2_struct_0(A_127))), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.45/1.32  tff(c_169, plain, (![D_129]: (r2_waybel_0('#skF_5', '#skF_6', D_129) | ~r1_tarski(k1_xboole_0, D_129) | ~l1_waybel_0('#skF_6', '#skF_5') | v2_struct_0('#skF_6') | ~l1_struct_0('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_166, c_167])).
% 2.45/1.32  tff(c_172, plain, (![D_129]: (r2_waybel_0('#skF_5', '#skF_6', D_129) | v2_struct_0('#skF_6') | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_40, c_94, c_169])).
% 2.45/1.32  tff(c_173, plain, (![D_129]: (r2_waybel_0('#skF_5', '#skF_6', D_129))), inference(negUnitSimplification, [status(thm)], [c_50, c_46, c_172])).
% 2.45/1.32  tff(c_16, plain, (![A_11]: (m1_subset_1('#skF_2'(A_11), A_11))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.45/1.32  tff(c_204, plain, (![A_151, B_152, C_153, D_154]: (r2_hidden(k2_waybel_0(A_151, B_152, '#skF_4'(A_151, B_152, C_153, D_154)), C_153) | ~m1_subset_1(D_154, u1_struct_0(B_152)) | ~r2_waybel_0(A_151, B_152, C_153) | ~l1_waybel_0(B_152, A_151) | v2_struct_0(B_152) | ~l1_struct_0(A_151) | v2_struct_0(A_151))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.45/1.32  tff(c_213, plain, (![D_155, B_156, A_157]: (~m1_subset_1(D_155, u1_struct_0(B_156)) | ~r2_waybel_0(A_157, B_156, k1_xboole_0) | ~l1_waybel_0(B_156, A_157) | v2_struct_0(B_156) | ~l1_struct_0(A_157) | v2_struct_0(A_157))), inference(resolution, [status(thm)], [c_204, c_87])).
% 2.45/1.32  tff(c_223, plain, (![A_158, B_159]: (~r2_waybel_0(A_158, B_159, k1_xboole_0) | ~l1_waybel_0(B_159, A_158) | v2_struct_0(B_159) | ~l1_struct_0(A_158) | v2_struct_0(A_158))), inference(resolution, [status(thm)], [c_16, c_213])).
% 2.45/1.32  tff(c_227, plain, (~l1_waybel_0('#skF_6', '#skF_5') | v2_struct_0('#skF_6') | ~l1_struct_0('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_173, c_223])).
% 2.45/1.32  tff(c_230, plain, (v2_struct_0('#skF_6') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_40, c_227])).
% 2.45/1.32  tff(c_232, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_46, c_230])).
% 2.45/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.45/1.32  
% 2.45/1.32  Inference rules
% 2.45/1.32  ----------------------
% 2.45/1.32  #Ref     : 0
% 2.45/1.32  #Sup     : 35
% 2.45/1.32  #Fact    : 0
% 2.45/1.32  #Define  : 0
% 2.45/1.32  #Split   : 0
% 2.45/1.32  #Chain   : 0
% 2.45/1.32  #Close   : 0
% 2.45/1.32  
% 2.45/1.32  Ordering : KBO
% 2.45/1.32  
% 2.45/1.32  Simplification rules
% 2.45/1.32  ----------------------
% 2.45/1.32  #Subsume      : 8
% 2.45/1.32  #Demod        : 15
% 2.45/1.32  #Tautology    : 13
% 2.45/1.32  #SimpNegUnit  : 4
% 2.45/1.32  #BackRed      : 0
% 2.45/1.32  
% 2.45/1.32  #Partial instantiations: 0
% 2.45/1.32  #Strategies tried      : 1
% 2.45/1.32  
% 2.45/1.32  Timing (in seconds)
% 2.45/1.32  ----------------------
% 2.45/1.32  Preprocessing        : 0.32
% 2.45/1.32  Parsing              : 0.17
% 2.45/1.32  CNF conversion       : 0.03
% 2.45/1.32  Main loop            : 0.20
% 2.45/1.32  Inferencing          : 0.08
% 2.45/1.32  Reduction            : 0.06
% 2.45/1.32  Demodulation         : 0.04
% 2.45/1.32  BG Simplification    : 0.01
% 2.45/1.33  Subsumption          : 0.03
% 2.45/1.33  Abstraction          : 0.01
% 2.45/1.33  MUC search           : 0.00
% 2.45/1.33  Cooper               : 0.00
% 2.45/1.33  Total                : 0.55
% 2.45/1.33  Index Insertion      : 0.00
% 2.45/1.33  Index Deletion       : 0.00
% 2.45/1.33  Index Matching       : 0.00
% 2.45/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
