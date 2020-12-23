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
% DateTime   : Thu Dec  3 10:30:50 EST 2020

% Result     : Theorem 2.15s
% Output     : CNFRefutation 2.50s
% Verified   : 
% Statistics : Number of formulae       :   64 (  90 expanded)
%              Number of leaves         :   35 (  50 expanded)
%              Depth                    :   12
%              Number of atoms          :  124 ( 225 expanded)
%              Number of equality atoms :    6 (  12 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_waybel_0 > r1_waybel_0 > r1_orders_2 > r2_hidden > r1_tarski > m1_subset_1 > l1_waybel_0 > v7_waybel_0 > v4_orders_2 > v2_struct_0 > l1_struct_0 > k2_waybel_0 > k6_subset_1 > k4_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k1_xboole_0 > #skF_2 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_1

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

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_waybel_0,type,(
    r1_waybel_0: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff(f_128,negated_conjecture,(
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

tff(f_34,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( k4_xboole_0(k2_tarski(A,B),C) = k2_tarski(A,B)
    <=> ( ~ r2_hidden(A,C)
        & ~ r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_zfmisc_1)).

tff(f_47,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_88,axiom,(
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

tff(f_110,axiom,(
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

tff(f_45,axiom,(
    ! [A] :
    ? [B] : m1_subset_1(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).

tff(f_71,axiom,(
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
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_46,plain,(
    ~ v2_struct_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_48,plain,(
    l1_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_40,plain,(
    l1_waybel_0('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_8,plain,(
    ! [A_6] : k4_xboole_0(A_6,k1_xboole_0) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_84,plain,(
    ! [B_98,C_99,A_100] :
      ( ~ r2_hidden(B_98,C_99)
      | k4_xboole_0(k2_tarski(A_100,B_98),C_99) != k2_tarski(A_100,B_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_96,plain,(
    ! [B_104] : ~ r2_hidden(B_104,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_84])).

tff(c_101,plain,(
    ! [B_2] : r1_tarski(k1_xboole_0,B_2) ),
    inference(resolution,[status(thm)],[c_6,c_96])).

tff(c_18,plain,(
    ! [A_12,B_13] : k6_subset_1(A_12,B_13) = k4_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_32,plain,(
    ! [A_67,B_71,C_73] :
      ( r2_waybel_0(A_67,B_71,C_73)
      | r1_waybel_0(A_67,B_71,k6_subset_1(u1_struct_0(A_67),C_73))
      | ~ l1_waybel_0(B_71,A_67)
      | v2_struct_0(B_71)
      | ~ l1_struct_0(A_67)
      | v2_struct_0(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_165,plain,(
    ! [A_122,B_123,C_124] :
      ( r2_waybel_0(A_122,B_123,C_124)
      | r1_waybel_0(A_122,B_123,k4_xboole_0(u1_struct_0(A_122),C_124))
      | ~ l1_waybel_0(B_123,A_122)
      | v2_struct_0(B_123)
      | ~ l1_struct_0(A_122)
      | v2_struct_0(A_122) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_32])).

tff(c_174,plain,(
    ! [A_129,B_130] :
      ( r2_waybel_0(A_129,B_130,k1_xboole_0)
      | r1_waybel_0(A_129,B_130,u1_struct_0(A_129))
      | ~ l1_waybel_0(B_130,A_129)
      | v2_struct_0(B_130)
      | ~ l1_struct_0(A_129)
      | v2_struct_0(A_129) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_165])).

tff(c_38,plain,(
    ~ r1_waybel_0('#skF_5','#skF_6',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_179,plain,
    ( r2_waybel_0('#skF_5','#skF_6',k1_xboole_0)
    | ~ l1_waybel_0('#skF_6','#skF_5')
    | v2_struct_0('#skF_6')
    | ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_174,c_38])).

tff(c_183,plain,
    ( r2_waybel_0('#skF_5','#skF_6',k1_xboole_0)
    | v2_struct_0('#skF_6')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_40,c_179])).

tff(c_184,plain,(
    r2_waybel_0('#skF_5','#skF_6',k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_46,c_183])).

tff(c_34,plain,(
    ! [A_74,B_80,D_84,C_83] :
      ( r2_waybel_0(A_74,B_80,D_84)
      | ~ r2_waybel_0(A_74,B_80,C_83)
      | ~ r1_tarski(C_83,D_84)
      | ~ l1_waybel_0(B_80,A_74)
      | v2_struct_0(B_80)
      | ~ l1_struct_0(A_74)
      | v2_struct_0(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_186,plain,(
    ! [D_84] :
      ( r2_waybel_0('#skF_5','#skF_6',D_84)
      | ~ r1_tarski(k1_xboole_0,D_84)
      | ~ l1_waybel_0('#skF_6','#skF_5')
      | v2_struct_0('#skF_6')
      | ~ l1_struct_0('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_184,c_34])).

tff(c_189,plain,(
    ! [D_84] :
      ( r2_waybel_0('#skF_5','#skF_6',D_84)
      | v2_struct_0('#skF_6')
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_40,c_101,c_186])).

tff(c_190,plain,(
    ! [D_84] : r2_waybel_0('#skF_5','#skF_6',D_84) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_46,c_189])).

tff(c_16,plain,(
    ! [A_10] : m1_subset_1('#skF_2'(A_10),A_10) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_229,plain,(
    ! [A_155,B_156,C_157,D_158] :
      ( r2_hidden(k2_waybel_0(A_155,B_156,'#skF_4'(A_155,B_156,C_157,D_158)),C_157)
      | ~ m1_subset_1(D_158,u1_struct_0(B_156))
      | ~ r2_waybel_0(A_155,B_156,C_157)
      | ~ l1_waybel_0(B_156,A_155)
      | v2_struct_0(B_156)
      | ~ l1_struct_0(A_155)
      | v2_struct_0(A_155) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_89,plain,(
    ! [B_98] : ~ r2_hidden(B_98,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_84])).

tff(c_238,plain,(
    ! [D_159,B_160,A_161] :
      ( ~ m1_subset_1(D_159,u1_struct_0(B_160))
      | ~ r2_waybel_0(A_161,B_160,k1_xboole_0)
      | ~ l1_waybel_0(B_160,A_161)
      | v2_struct_0(B_160)
      | ~ l1_struct_0(A_161)
      | v2_struct_0(A_161) ) ),
    inference(resolution,[status(thm)],[c_229,c_89])).

tff(c_248,plain,(
    ! [A_162,B_163] :
      ( ~ r2_waybel_0(A_162,B_163,k1_xboole_0)
      | ~ l1_waybel_0(B_163,A_162)
      | v2_struct_0(B_163)
      | ~ l1_struct_0(A_162)
      | v2_struct_0(A_162) ) ),
    inference(resolution,[status(thm)],[c_16,c_238])).

tff(c_252,plain,
    ( ~ l1_waybel_0('#skF_6','#skF_5')
    | v2_struct_0('#skF_6')
    | ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_190,c_248])).

tff(c_255,plain,
    ( v2_struct_0('#skF_6')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_40,c_252])).

tff(c_257,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_46,c_255])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n014.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 09:31:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.15/1.30  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.15/1.30  
% 2.15/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.15/1.31  %$ r2_waybel_0 > r1_waybel_0 > r1_orders_2 > r2_hidden > r1_tarski > m1_subset_1 > l1_waybel_0 > v7_waybel_0 > v4_orders_2 > v2_struct_0 > l1_struct_0 > k2_waybel_0 > k6_subset_1 > k4_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k1_xboole_0 > #skF_2 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_1
% 2.15/1.31  
% 2.15/1.31  %Foreground sorts:
% 2.15/1.31  
% 2.15/1.31  
% 2.15/1.31  %Background operators:
% 2.15/1.31  
% 2.15/1.31  
% 2.15/1.31  %Foreground operators:
% 2.15/1.31  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.15/1.31  tff(r2_waybel_0, type, r2_waybel_0: ($i * $i * $i) > $o).
% 2.15/1.31  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.15/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.15/1.31  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.15/1.31  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.15/1.31  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 2.15/1.31  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.15/1.31  tff(k2_waybel_0, type, k2_waybel_0: ($i * $i * $i) > $i).
% 2.15/1.31  tff(v7_waybel_0, type, v7_waybel_0: $i > $o).
% 2.15/1.31  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.15/1.31  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.15/1.31  tff('#skF_5', type, '#skF_5': $i).
% 2.15/1.31  tff(r1_waybel_0, type, r1_waybel_0: ($i * $i * $i) > $o).
% 2.15/1.31  tff('#skF_6', type, '#skF_6': $i).
% 2.15/1.31  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 2.15/1.31  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.15/1.31  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.15/1.31  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 2.15/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.15/1.31  tff(l1_waybel_0, type, l1_waybel_0: ($i * $i) > $o).
% 2.15/1.31  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.15/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.15/1.31  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.15/1.31  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.15/1.31  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.15/1.31  
% 2.50/1.32  tff(f_128, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => r1_waybel_0(A, B, u1_struct_0(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_yellow_6)).
% 2.50/1.32  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.50/1.32  tff(f_34, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 2.50/1.32  tff(f_42, axiom, (![A, B, C]: ((k4_xboole_0(k2_tarski(A, B), C) = k2_tarski(A, B)) <=> (~r2_hidden(A, C) & ~r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_zfmisc_1)).
% 2.50/1.32  tff(f_47, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 2.50/1.32  tff(f_88, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((~v2_struct_0(B) & l1_waybel_0(B, A)) => (![C]: (r2_waybel_0(A, B, C) <=> ~r1_waybel_0(A, B, k6_subset_1(u1_struct_0(A), C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_waybel_0)).
% 2.50/1.32  tff(f_110, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((~v2_struct_0(B) & l1_waybel_0(B, A)) => (![C, D]: (r1_tarski(C, D) => ((r1_waybel_0(A, B, C) => r1_waybel_0(A, B, D)) & (r2_waybel_0(A, B, C) => r2_waybel_0(A, B, D))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_waybel_0)).
% 2.50/1.32  tff(f_45, axiom, (![A]: (?[B]: m1_subset_1(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', existence_m1_subset_1)).
% 2.50/1.32  tff(f_71, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((~v2_struct_0(B) & l1_waybel_0(B, A)) => (![C]: (r2_waybel_0(A, B, C) <=> (![D]: (m1_subset_1(D, u1_struct_0(B)) => (?[E]: ((m1_subset_1(E, u1_struct_0(B)) & r1_orders_2(B, D, E)) & r2_hidden(k2_waybel_0(A, B, E), C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d12_waybel_0)).
% 2.50/1.32  tff(c_50, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_128])).
% 2.50/1.32  tff(c_46, plain, (~v2_struct_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_128])).
% 2.50/1.32  tff(c_48, plain, (l1_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_128])).
% 2.50/1.32  tff(c_40, plain, (l1_waybel_0('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_128])).
% 2.50/1.32  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.50/1.32  tff(c_8, plain, (![A_6]: (k4_xboole_0(A_6, k1_xboole_0)=A_6)), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.50/1.32  tff(c_84, plain, (![B_98, C_99, A_100]: (~r2_hidden(B_98, C_99) | k4_xboole_0(k2_tarski(A_100, B_98), C_99)!=k2_tarski(A_100, B_98))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.50/1.32  tff(c_96, plain, (![B_104]: (~r2_hidden(B_104, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_84])).
% 2.50/1.32  tff(c_101, plain, (![B_2]: (r1_tarski(k1_xboole_0, B_2))), inference(resolution, [status(thm)], [c_6, c_96])).
% 2.50/1.32  tff(c_18, plain, (![A_12, B_13]: (k6_subset_1(A_12, B_13)=k4_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.50/1.32  tff(c_32, plain, (![A_67, B_71, C_73]: (r2_waybel_0(A_67, B_71, C_73) | r1_waybel_0(A_67, B_71, k6_subset_1(u1_struct_0(A_67), C_73)) | ~l1_waybel_0(B_71, A_67) | v2_struct_0(B_71) | ~l1_struct_0(A_67) | v2_struct_0(A_67))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.50/1.32  tff(c_165, plain, (![A_122, B_123, C_124]: (r2_waybel_0(A_122, B_123, C_124) | r1_waybel_0(A_122, B_123, k4_xboole_0(u1_struct_0(A_122), C_124)) | ~l1_waybel_0(B_123, A_122) | v2_struct_0(B_123) | ~l1_struct_0(A_122) | v2_struct_0(A_122))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_32])).
% 2.50/1.32  tff(c_174, plain, (![A_129, B_130]: (r2_waybel_0(A_129, B_130, k1_xboole_0) | r1_waybel_0(A_129, B_130, u1_struct_0(A_129)) | ~l1_waybel_0(B_130, A_129) | v2_struct_0(B_130) | ~l1_struct_0(A_129) | v2_struct_0(A_129))), inference(superposition, [status(thm), theory('equality')], [c_8, c_165])).
% 2.50/1.32  tff(c_38, plain, (~r1_waybel_0('#skF_5', '#skF_6', u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_128])).
% 2.50/1.32  tff(c_179, plain, (r2_waybel_0('#skF_5', '#skF_6', k1_xboole_0) | ~l1_waybel_0('#skF_6', '#skF_5') | v2_struct_0('#skF_6') | ~l1_struct_0('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_174, c_38])).
% 2.50/1.32  tff(c_183, plain, (r2_waybel_0('#skF_5', '#skF_6', k1_xboole_0) | v2_struct_0('#skF_6') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_40, c_179])).
% 2.50/1.32  tff(c_184, plain, (r2_waybel_0('#skF_5', '#skF_6', k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_50, c_46, c_183])).
% 2.50/1.32  tff(c_34, plain, (![A_74, B_80, D_84, C_83]: (r2_waybel_0(A_74, B_80, D_84) | ~r2_waybel_0(A_74, B_80, C_83) | ~r1_tarski(C_83, D_84) | ~l1_waybel_0(B_80, A_74) | v2_struct_0(B_80) | ~l1_struct_0(A_74) | v2_struct_0(A_74))), inference(cnfTransformation, [status(thm)], [f_110])).
% 2.50/1.32  tff(c_186, plain, (![D_84]: (r2_waybel_0('#skF_5', '#skF_6', D_84) | ~r1_tarski(k1_xboole_0, D_84) | ~l1_waybel_0('#skF_6', '#skF_5') | v2_struct_0('#skF_6') | ~l1_struct_0('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_184, c_34])).
% 2.50/1.32  tff(c_189, plain, (![D_84]: (r2_waybel_0('#skF_5', '#skF_6', D_84) | v2_struct_0('#skF_6') | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_40, c_101, c_186])).
% 2.50/1.32  tff(c_190, plain, (![D_84]: (r2_waybel_0('#skF_5', '#skF_6', D_84))), inference(negUnitSimplification, [status(thm)], [c_50, c_46, c_189])).
% 2.50/1.32  tff(c_16, plain, (![A_10]: (m1_subset_1('#skF_2'(A_10), A_10))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.50/1.32  tff(c_229, plain, (![A_155, B_156, C_157, D_158]: (r2_hidden(k2_waybel_0(A_155, B_156, '#skF_4'(A_155, B_156, C_157, D_158)), C_157) | ~m1_subset_1(D_158, u1_struct_0(B_156)) | ~r2_waybel_0(A_155, B_156, C_157) | ~l1_waybel_0(B_156, A_155) | v2_struct_0(B_156) | ~l1_struct_0(A_155) | v2_struct_0(A_155))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.50/1.32  tff(c_89, plain, (![B_98]: (~r2_hidden(B_98, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_84])).
% 2.50/1.32  tff(c_238, plain, (![D_159, B_160, A_161]: (~m1_subset_1(D_159, u1_struct_0(B_160)) | ~r2_waybel_0(A_161, B_160, k1_xboole_0) | ~l1_waybel_0(B_160, A_161) | v2_struct_0(B_160) | ~l1_struct_0(A_161) | v2_struct_0(A_161))), inference(resolution, [status(thm)], [c_229, c_89])).
% 2.50/1.32  tff(c_248, plain, (![A_162, B_163]: (~r2_waybel_0(A_162, B_163, k1_xboole_0) | ~l1_waybel_0(B_163, A_162) | v2_struct_0(B_163) | ~l1_struct_0(A_162) | v2_struct_0(A_162))), inference(resolution, [status(thm)], [c_16, c_238])).
% 2.50/1.32  tff(c_252, plain, (~l1_waybel_0('#skF_6', '#skF_5') | v2_struct_0('#skF_6') | ~l1_struct_0('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_190, c_248])).
% 2.50/1.32  tff(c_255, plain, (v2_struct_0('#skF_6') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_40, c_252])).
% 2.50/1.32  tff(c_257, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_46, c_255])).
% 2.50/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.50/1.32  
% 2.50/1.32  Inference rules
% 2.50/1.32  ----------------------
% 2.50/1.32  #Ref     : 0
% 2.50/1.32  #Sup     : 40
% 2.50/1.32  #Fact    : 0
% 2.50/1.32  #Define  : 0
% 2.50/1.32  #Split   : 0
% 2.50/1.32  #Chain   : 0
% 2.50/1.32  #Close   : 0
% 2.50/1.32  
% 2.50/1.32  Ordering : KBO
% 2.50/1.32  
% 2.50/1.32  Simplification rules
% 2.50/1.32  ----------------------
% 2.50/1.32  #Subsume      : 9
% 2.50/1.32  #Demod        : 15
% 2.50/1.32  #Tautology    : 17
% 2.50/1.32  #SimpNegUnit  : 6
% 2.50/1.32  #BackRed      : 0
% 2.50/1.32  
% 2.50/1.32  #Partial instantiations: 0
% 2.50/1.32  #Strategies tried      : 1
% 2.50/1.32  
% 2.50/1.32  Timing (in seconds)
% 2.50/1.32  ----------------------
% 2.50/1.32  Preprocessing        : 0.34
% 2.50/1.32  Parsing              : 0.18
% 2.50/1.32  CNF conversion       : 0.03
% 2.50/1.32  Main loop            : 0.21
% 2.50/1.32  Inferencing          : 0.08
% 2.50/1.33  Reduction            : 0.06
% 2.50/1.33  Demodulation         : 0.04
% 2.50/1.33  BG Simplification    : 0.02
% 2.50/1.33  Subsumption          : 0.04
% 2.50/1.33  Abstraction          : 0.01
% 2.50/1.33  MUC search           : 0.00
% 2.50/1.33  Cooper               : 0.00
% 2.50/1.33  Total                : 0.58
% 2.50/1.33  Index Insertion      : 0.00
% 2.50/1.33  Index Deletion       : 0.00
% 2.50/1.33  Index Matching       : 0.00
% 2.50/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
