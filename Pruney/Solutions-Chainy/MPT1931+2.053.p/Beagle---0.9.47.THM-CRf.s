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

% Result     : Theorem 2.41s
% Output     : CNFRefutation 2.41s
% Verified   : 
% Statistics : Number of formulae       :   69 (  89 expanded)
%              Number of leaves         :   39 (  51 expanded)
%              Depth                    :   13
%              Number of atoms          :  131 ( 223 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_waybel_0 > r1_waybel_0 > r1_orders_2 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > l1_waybel_0 > v7_waybel_0 > v4_orders_2 > v2_struct_0 > l1_struct_0 > k2_waybel_0 > k6_subset_1 > k4_xboole_0 > k3_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_1

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

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_141,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & l1_struct_0(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & v4_orders_2(B)
              & v7_waybel_0(B)
              & l1_waybel_0(B,A) )
           => r1_waybel_0(A,B,u1_struct_0(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_yellow_6)).

tff(f_50,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_41,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_48,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_101,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & l1_waybel_0(B,A) )
         => ! [C] :
              ( r2_waybel_0(A,B,C)
            <=> ~ r1_waybel_0(A,B,k6_subset_1(u1_struct_0(A),C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_waybel_0)).

tff(f_123,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_waybel_0)).

tff(f_46,axiom,(
    ! [A] :
    ? [B] : m1_subset_1(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).

tff(f_84,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_waybel_0)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_43,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(c_52,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_48,plain,(
    ~ v2_struct_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_50,plain,(
    l1_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_42,plain,(
    l1_waybel_0('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_14,plain,(
    ! [A_12] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_12)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_77,plain,(
    ! [A_98,B_99] :
      ( r1_tarski(A_98,B_99)
      | ~ m1_subset_1(A_98,k1_zfmisc_1(B_99)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_90,plain,(
    ! [A_12] : r1_tarski(k1_xboole_0,A_12) ),
    inference(resolution,[status(thm)],[c_14,c_77])).

tff(c_6,plain,(
    ! [A_6] : k4_xboole_0(A_6,k1_xboole_0) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_12,plain,(
    ! [A_10,B_11] : k6_subset_1(A_10,B_11) = k4_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_34,plain,(
    ! [A_71,B_75,C_77] :
      ( r2_waybel_0(A_71,B_75,C_77)
      | r1_waybel_0(A_71,B_75,k6_subset_1(u1_struct_0(A_71),C_77))
      | ~ l1_waybel_0(B_75,A_71)
      | v2_struct_0(B_75)
      | ~ l1_struct_0(A_71)
      | v2_struct_0(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_118,plain,(
    ! [A_123,B_124,C_125] :
      ( r2_waybel_0(A_123,B_124,C_125)
      | r1_waybel_0(A_123,B_124,k4_xboole_0(u1_struct_0(A_123),C_125))
      | ~ l1_waybel_0(B_124,A_123)
      | v2_struct_0(B_124)
      | ~ l1_struct_0(A_123)
      | v2_struct_0(A_123) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_34])).

tff(c_132,plain,(
    ! [A_129,B_130] :
      ( r2_waybel_0(A_129,B_130,k1_xboole_0)
      | r1_waybel_0(A_129,B_130,u1_struct_0(A_129))
      | ~ l1_waybel_0(B_130,A_129)
      | v2_struct_0(B_130)
      | ~ l1_struct_0(A_129)
      | v2_struct_0(A_129) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_118])).

tff(c_40,plain,(
    ~ r1_waybel_0('#skF_5','#skF_6',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_135,plain,
    ( r2_waybel_0('#skF_5','#skF_6',k1_xboole_0)
    | ~ l1_waybel_0('#skF_6','#skF_5')
    | v2_struct_0('#skF_6')
    | ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_132,c_40])).

tff(c_138,plain,
    ( r2_waybel_0('#skF_5','#skF_6',k1_xboole_0)
    | v2_struct_0('#skF_6')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_42,c_135])).

tff(c_139,plain,(
    r2_waybel_0('#skF_5','#skF_6',k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_48,c_138])).

tff(c_152,plain,(
    ! [A_137,B_138,D_139,C_140] :
      ( r2_waybel_0(A_137,B_138,D_139)
      | ~ r2_waybel_0(A_137,B_138,C_140)
      | ~ r1_tarski(C_140,D_139)
      | ~ l1_waybel_0(B_138,A_137)
      | v2_struct_0(B_138)
      | ~ l1_struct_0(A_137)
      | v2_struct_0(A_137) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_154,plain,(
    ! [D_139] :
      ( r2_waybel_0('#skF_5','#skF_6',D_139)
      | ~ r1_tarski(k1_xboole_0,D_139)
      | ~ l1_waybel_0('#skF_6','#skF_5')
      | v2_struct_0('#skF_6')
      | ~ l1_struct_0('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_139,c_152])).

tff(c_157,plain,(
    ! [D_139] :
      ( r2_waybel_0('#skF_5','#skF_6',D_139)
      | v2_struct_0('#skF_6')
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_42,c_90,c_154])).

tff(c_158,plain,(
    ! [D_139] : r2_waybel_0('#skF_5','#skF_6',D_139) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_48,c_157])).

tff(c_10,plain,(
    ! [A_8] : m1_subset_1('#skF_2'(A_8),A_8) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_174,plain,(
    ! [A_157,B_158,C_159,D_160] :
      ( r2_hidden(k2_waybel_0(A_157,B_158,'#skF_4'(A_157,B_158,C_159,D_160)),C_159)
      | ~ m1_subset_1(D_160,u1_struct_0(B_158))
      | ~ r2_waybel_0(A_157,B_158,C_159)
      | ~ l1_waybel_0(B_158,A_157)
      | v2_struct_0(B_158)
      | ~ l1_struct_0(A_157)
      | v2_struct_0(A_157) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_4,plain,(
    ! [A_1,B_2,C_5] :
      ( ~ r1_xboole_0(A_1,B_2)
      | ~ r2_hidden(C_5,k3_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_192,plain,(
    ! [D_161,B_163,A_164,B_165,A_162] :
      ( ~ r1_xboole_0(A_164,B_163)
      | ~ m1_subset_1(D_161,u1_struct_0(B_165))
      | ~ r2_waybel_0(A_162,B_165,k3_xboole_0(A_164,B_163))
      | ~ l1_waybel_0(B_165,A_162)
      | v2_struct_0(B_165)
      | ~ l1_struct_0(A_162)
      | v2_struct_0(A_162) ) ),
    inference(resolution,[status(thm)],[c_174,c_4])).

tff(c_202,plain,(
    ! [A_166,B_167,A_168,B_169] :
      ( ~ r1_xboole_0(A_166,B_167)
      | ~ r2_waybel_0(A_168,B_169,k3_xboole_0(A_166,B_167))
      | ~ l1_waybel_0(B_169,A_168)
      | v2_struct_0(B_169)
      | ~ l1_struct_0(A_168)
      | v2_struct_0(A_168) ) ),
    inference(resolution,[status(thm)],[c_10,c_192])).

tff(c_206,plain,(
    ! [A_166,B_167] :
      ( ~ r1_xboole_0(A_166,B_167)
      | ~ l1_waybel_0('#skF_6','#skF_5')
      | v2_struct_0('#skF_6')
      | ~ l1_struct_0('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_158,c_202])).

tff(c_209,plain,(
    ! [A_166,B_167] :
      ( ~ r1_xboole_0(A_166,B_167)
      | v2_struct_0('#skF_6')
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_42,c_206])).

tff(c_210,plain,(
    ! [A_166,B_167] : ~ r1_xboole_0(A_166,B_167) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_48,c_209])).

tff(c_8,plain,(
    ! [A_7] : r1_xboole_0(A_7,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_214,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_210,c_8])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n010.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 09:14:29 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.41/1.35  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.41/1.36  
% 2.41/1.36  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.41/1.36  %$ r2_waybel_0 > r1_waybel_0 > r1_orders_2 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > l1_waybel_0 > v7_waybel_0 > v4_orders_2 > v2_struct_0 > l1_struct_0 > k2_waybel_0 > k6_subset_1 > k4_xboole_0 > k3_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_1
% 2.41/1.36  
% 2.41/1.36  %Foreground sorts:
% 2.41/1.36  
% 2.41/1.36  
% 2.41/1.36  %Background operators:
% 2.41/1.36  
% 2.41/1.36  
% 2.41/1.36  %Foreground operators:
% 2.41/1.36  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.41/1.36  tff(r2_waybel_0, type, r2_waybel_0: ($i * $i * $i) > $o).
% 2.41/1.36  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.41/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.41/1.36  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.41/1.36  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.41/1.36  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 2.41/1.36  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.41/1.36  tff(k2_waybel_0, type, k2_waybel_0: ($i * $i * $i) > $i).
% 2.41/1.36  tff(v7_waybel_0, type, v7_waybel_0: $i > $o).
% 2.41/1.36  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.41/1.36  tff('#skF_5', type, '#skF_5': $i).
% 2.41/1.36  tff(r1_waybel_0, type, r1_waybel_0: ($i * $i * $i) > $o).
% 2.41/1.36  tff('#skF_6', type, '#skF_6': $i).
% 2.41/1.36  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.41/1.36  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 2.41/1.36  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.41/1.36  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.41/1.36  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.41/1.36  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 2.41/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.41/1.36  tff(l1_waybel_0, type, l1_waybel_0: ($i * $i) > $o).
% 2.41/1.36  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.41/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.41/1.36  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.41/1.36  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.41/1.36  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.41/1.36  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.41/1.36  
% 2.41/1.38  tff(f_141, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => r1_waybel_0(A, B, u1_struct_0(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_yellow_6)).
% 2.41/1.38  tff(f_50, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 2.41/1.38  tff(f_54, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.41/1.38  tff(f_41, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 2.41/1.38  tff(f_48, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 2.41/1.38  tff(f_101, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((~v2_struct_0(B) & l1_waybel_0(B, A)) => (![C]: (r2_waybel_0(A, B, C) <=> ~r1_waybel_0(A, B, k6_subset_1(u1_struct_0(A), C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_waybel_0)).
% 2.41/1.38  tff(f_123, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((~v2_struct_0(B) & l1_waybel_0(B, A)) => (![C, D]: (r1_tarski(C, D) => ((r1_waybel_0(A, B, C) => r1_waybel_0(A, B, D)) & (r2_waybel_0(A, B, C) => r2_waybel_0(A, B, D))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_waybel_0)).
% 2.41/1.38  tff(f_46, axiom, (![A]: (?[B]: m1_subset_1(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', existence_m1_subset_1)).
% 2.41/1.38  tff(f_84, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((~v2_struct_0(B) & l1_waybel_0(B, A)) => (![C]: (r2_waybel_0(A, B, C) <=> (![D]: (m1_subset_1(D, u1_struct_0(B)) => (?[E]: ((m1_subset_1(E, u1_struct_0(B)) & r1_orders_2(B, D, E)) & r2_hidden(k2_waybel_0(A, B, E), C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_waybel_0)).
% 2.41/1.38  tff(f_39, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.41/1.38  tff(f_43, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.41/1.38  tff(c_52, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_141])).
% 2.41/1.38  tff(c_48, plain, (~v2_struct_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_141])).
% 2.41/1.38  tff(c_50, plain, (l1_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_141])).
% 2.41/1.38  tff(c_42, plain, (l1_waybel_0('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_141])).
% 2.41/1.38  tff(c_14, plain, (![A_12]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.41/1.38  tff(c_77, plain, (![A_98, B_99]: (r1_tarski(A_98, B_99) | ~m1_subset_1(A_98, k1_zfmisc_1(B_99)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.41/1.38  tff(c_90, plain, (![A_12]: (r1_tarski(k1_xboole_0, A_12))), inference(resolution, [status(thm)], [c_14, c_77])).
% 2.41/1.38  tff(c_6, plain, (![A_6]: (k4_xboole_0(A_6, k1_xboole_0)=A_6)), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.41/1.38  tff(c_12, plain, (![A_10, B_11]: (k6_subset_1(A_10, B_11)=k4_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.41/1.38  tff(c_34, plain, (![A_71, B_75, C_77]: (r2_waybel_0(A_71, B_75, C_77) | r1_waybel_0(A_71, B_75, k6_subset_1(u1_struct_0(A_71), C_77)) | ~l1_waybel_0(B_75, A_71) | v2_struct_0(B_75) | ~l1_struct_0(A_71) | v2_struct_0(A_71))), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.41/1.38  tff(c_118, plain, (![A_123, B_124, C_125]: (r2_waybel_0(A_123, B_124, C_125) | r1_waybel_0(A_123, B_124, k4_xboole_0(u1_struct_0(A_123), C_125)) | ~l1_waybel_0(B_124, A_123) | v2_struct_0(B_124) | ~l1_struct_0(A_123) | v2_struct_0(A_123))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_34])).
% 2.41/1.38  tff(c_132, plain, (![A_129, B_130]: (r2_waybel_0(A_129, B_130, k1_xboole_0) | r1_waybel_0(A_129, B_130, u1_struct_0(A_129)) | ~l1_waybel_0(B_130, A_129) | v2_struct_0(B_130) | ~l1_struct_0(A_129) | v2_struct_0(A_129))), inference(superposition, [status(thm), theory('equality')], [c_6, c_118])).
% 2.41/1.38  tff(c_40, plain, (~r1_waybel_0('#skF_5', '#skF_6', u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_141])).
% 2.41/1.38  tff(c_135, plain, (r2_waybel_0('#skF_5', '#skF_6', k1_xboole_0) | ~l1_waybel_0('#skF_6', '#skF_5') | v2_struct_0('#skF_6') | ~l1_struct_0('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_132, c_40])).
% 2.41/1.38  tff(c_138, plain, (r2_waybel_0('#skF_5', '#skF_6', k1_xboole_0) | v2_struct_0('#skF_6') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_42, c_135])).
% 2.41/1.38  tff(c_139, plain, (r2_waybel_0('#skF_5', '#skF_6', k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_52, c_48, c_138])).
% 2.41/1.38  tff(c_152, plain, (![A_137, B_138, D_139, C_140]: (r2_waybel_0(A_137, B_138, D_139) | ~r2_waybel_0(A_137, B_138, C_140) | ~r1_tarski(C_140, D_139) | ~l1_waybel_0(B_138, A_137) | v2_struct_0(B_138) | ~l1_struct_0(A_137) | v2_struct_0(A_137))), inference(cnfTransformation, [status(thm)], [f_123])).
% 2.41/1.38  tff(c_154, plain, (![D_139]: (r2_waybel_0('#skF_5', '#skF_6', D_139) | ~r1_tarski(k1_xboole_0, D_139) | ~l1_waybel_0('#skF_6', '#skF_5') | v2_struct_0('#skF_6') | ~l1_struct_0('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_139, c_152])).
% 2.41/1.38  tff(c_157, plain, (![D_139]: (r2_waybel_0('#skF_5', '#skF_6', D_139) | v2_struct_0('#skF_6') | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_42, c_90, c_154])).
% 2.41/1.38  tff(c_158, plain, (![D_139]: (r2_waybel_0('#skF_5', '#skF_6', D_139))), inference(negUnitSimplification, [status(thm)], [c_52, c_48, c_157])).
% 2.41/1.38  tff(c_10, plain, (![A_8]: (m1_subset_1('#skF_2'(A_8), A_8))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.41/1.38  tff(c_174, plain, (![A_157, B_158, C_159, D_160]: (r2_hidden(k2_waybel_0(A_157, B_158, '#skF_4'(A_157, B_158, C_159, D_160)), C_159) | ~m1_subset_1(D_160, u1_struct_0(B_158)) | ~r2_waybel_0(A_157, B_158, C_159) | ~l1_waybel_0(B_158, A_157) | v2_struct_0(B_158) | ~l1_struct_0(A_157) | v2_struct_0(A_157))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.41/1.38  tff(c_4, plain, (![A_1, B_2, C_5]: (~r1_xboole_0(A_1, B_2) | ~r2_hidden(C_5, k3_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.41/1.38  tff(c_192, plain, (![D_161, B_163, A_164, B_165, A_162]: (~r1_xboole_0(A_164, B_163) | ~m1_subset_1(D_161, u1_struct_0(B_165)) | ~r2_waybel_0(A_162, B_165, k3_xboole_0(A_164, B_163)) | ~l1_waybel_0(B_165, A_162) | v2_struct_0(B_165) | ~l1_struct_0(A_162) | v2_struct_0(A_162))), inference(resolution, [status(thm)], [c_174, c_4])).
% 2.41/1.38  tff(c_202, plain, (![A_166, B_167, A_168, B_169]: (~r1_xboole_0(A_166, B_167) | ~r2_waybel_0(A_168, B_169, k3_xboole_0(A_166, B_167)) | ~l1_waybel_0(B_169, A_168) | v2_struct_0(B_169) | ~l1_struct_0(A_168) | v2_struct_0(A_168))), inference(resolution, [status(thm)], [c_10, c_192])).
% 2.41/1.38  tff(c_206, plain, (![A_166, B_167]: (~r1_xboole_0(A_166, B_167) | ~l1_waybel_0('#skF_6', '#skF_5') | v2_struct_0('#skF_6') | ~l1_struct_0('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_158, c_202])).
% 2.41/1.38  tff(c_209, plain, (![A_166, B_167]: (~r1_xboole_0(A_166, B_167) | v2_struct_0('#skF_6') | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_42, c_206])).
% 2.41/1.38  tff(c_210, plain, (![A_166, B_167]: (~r1_xboole_0(A_166, B_167))), inference(negUnitSimplification, [status(thm)], [c_52, c_48, c_209])).
% 2.41/1.38  tff(c_8, plain, (![A_7]: (r1_xboole_0(A_7, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.41/1.38  tff(c_214, plain, $false, inference(negUnitSimplification, [status(thm)], [c_210, c_8])).
% 2.41/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.41/1.38  
% 2.41/1.38  Inference rules
% 2.41/1.38  ----------------------
% 2.41/1.38  #Ref     : 0
% 2.41/1.38  #Sup     : 30
% 2.41/1.38  #Fact    : 0
% 2.41/1.38  #Define  : 0
% 2.41/1.38  #Split   : 0
% 2.41/1.38  #Chain   : 0
% 2.41/1.38  #Close   : 0
% 2.41/1.38  
% 2.41/1.38  Ordering : KBO
% 2.41/1.38  
% 2.41/1.38  Simplification rules
% 2.41/1.38  ----------------------
% 2.41/1.38  #Subsume      : 5
% 2.41/1.38  #Demod        : 13
% 2.41/1.38  #Tautology    : 10
% 2.41/1.38  #SimpNegUnit  : 7
% 2.41/1.38  #BackRed      : 3
% 2.41/1.38  
% 2.41/1.38  #Partial instantiations: 0
% 2.41/1.38  #Strategies tried      : 1
% 2.41/1.38  
% 2.41/1.38  Timing (in seconds)
% 2.41/1.38  ----------------------
% 2.41/1.38  Preprocessing        : 0.35
% 2.41/1.38  Parsing              : 0.19
% 2.41/1.38  CNF conversion       : 0.03
% 2.60/1.38  Main loop            : 0.20
% 2.60/1.38  Inferencing          : 0.08
% 2.60/1.38  Reduction            : 0.06
% 2.60/1.38  Demodulation         : 0.04
% 2.60/1.38  BG Simplification    : 0.02
% 2.60/1.38  Subsumption          : 0.03
% 2.60/1.38  Abstraction          : 0.01
% 2.60/1.38  MUC search           : 0.00
% 2.60/1.38  Cooper               : 0.00
% 2.60/1.38  Total                : 0.59
% 2.60/1.38  Index Insertion      : 0.00
% 2.60/1.38  Index Deletion       : 0.00
% 2.60/1.38  Index Matching       : 0.00
% 2.60/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
