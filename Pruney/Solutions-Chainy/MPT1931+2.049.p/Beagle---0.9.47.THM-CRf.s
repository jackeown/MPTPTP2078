%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:52 EST 2020

% Result     : Theorem 2.15s
% Output     : CNFRefutation 2.15s
% Verified   : 
% Statistics : Number of formulae       :   66 (  88 expanded)
%              Number of leaves         :   37 (  50 expanded)
%              Depth                    :   13
%              Number of atoms          :  127 ( 221 expanded)
%              Number of equality atoms :    4 (   6 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_waybel_0 > r1_waybel_0 > r1_orders_2 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > l1_waybel_0 > v7_waybel_0 > v4_orders_2 > v2_struct_0 > l1_struct_0 > k2_waybel_0 > k6_subset_1 > k4_xboole_0 > k3_xboole_0 > #nlpp > u1_struct_0 > k1_xboole_0 > #skF_2 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_1

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

tff(f_131,negated_conjecture,(
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

tff(f_41,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_43,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_50,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_91,axiom,(
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

tff(f_113,axiom,(
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

tff(f_48,axiom,(
    ! [A] :
    ? [B] : m1_subset_1(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).

tff(f_74,axiom,(
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

tff(f_39,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(c_46,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_42,plain,(
    ~ v2_struct_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_44,plain,(
    l1_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_36,plain,(
    l1_waybel_0('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_6,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_8,plain,(
    ! [A_7] : k4_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_14,plain,(
    ! [A_12,B_13] : k6_subset_1(A_12,B_13) = k4_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_28,plain,(
    ! [A_67,B_71,C_73] :
      ( r2_waybel_0(A_67,B_71,C_73)
      | r1_waybel_0(A_67,B_71,k6_subset_1(u1_struct_0(A_67),C_73))
      | ~ l1_waybel_0(B_71,A_67)
      | v2_struct_0(B_71)
      | ~ l1_struct_0(A_67)
      | v2_struct_0(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_87,plain,(
    ! [A_107,B_108,C_109] :
      ( r2_waybel_0(A_107,B_108,C_109)
      | r1_waybel_0(A_107,B_108,k4_xboole_0(u1_struct_0(A_107),C_109))
      | ~ l1_waybel_0(B_108,A_107)
      | v2_struct_0(B_108)
      | ~ l1_struct_0(A_107)
      | v2_struct_0(A_107) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_28])).

tff(c_97,plain,(
    ! [A_114,B_115] :
      ( r2_waybel_0(A_114,B_115,k1_xboole_0)
      | r1_waybel_0(A_114,B_115,u1_struct_0(A_114))
      | ~ l1_waybel_0(B_115,A_114)
      | v2_struct_0(B_115)
      | ~ l1_struct_0(A_114)
      | v2_struct_0(A_114) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_87])).

tff(c_34,plain,(
    ~ r1_waybel_0('#skF_5','#skF_6',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_103,plain,
    ( r2_waybel_0('#skF_5','#skF_6',k1_xboole_0)
    | ~ l1_waybel_0('#skF_6','#skF_5')
    | v2_struct_0('#skF_6')
    | ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_97,c_34])).

tff(c_107,plain,
    ( r2_waybel_0('#skF_5','#skF_6',k1_xboole_0)
    | v2_struct_0('#skF_6')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_36,c_103])).

tff(c_108,plain,(
    r2_waybel_0('#skF_5','#skF_6',k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_42,c_107])).

tff(c_30,plain,(
    ! [A_74,B_80,D_84,C_83] :
      ( r2_waybel_0(A_74,B_80,D_84)
      | ~ r2_waybel_0(A_74,B_80,C_83)
      | ~ r1_tarski(C_83,D_84)
      | ~ l1_waybel_0(B_80,A_74)
      | v2_struct_0(B_80)
      | ~ l1_struct_0(A_74)
      | v2_struct_0(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_110,plain,(
    ! [D_84] :
      ( r2_waybel_0('#skF_5','#skF_6',D_84)
      | ~ r1_tarski(k1_xboole_0,D_84)
      | ~ l1_waybel_0('#skF_6','#skF_5')
      | v2_struct_0('#skF_6')
      | ~ l1_struct_0('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_108,c_30])).

tff(c_113,plain,(
    ! [D_84] :
      ( r2_waybel_0('#skF_5','#skF_6',D_84)
      | v2_struct_0('#skF_6')
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_36,c_6,c_110])).

tff(c_114,plain,(
    ! [D_84] : r2_waybel_0('#skF_5','#skF_6',D_84) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_42,c_113])).

tff(c_12,plain,(
    ! [A_10] : m1_subset_1('#skF_2'(A_10),A_10) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_137,plain,(
    ! [A_136,B_137,C_138,D_139] :
      ( r2_hidden(k2_waybel_0(A_136,B_137,'#skF_4'(A_136,B_137,C_138,D_139)),C_138)
      | ~ m1_subset_1(D_139,u1_struct_0(B_137))
      | ~ r2_waybel_0(A_136,B_137,C_138)
      | ~ l1_waybel_0(B_137,A_136)
      | v2_struct_0(B_137)
      | ~ l1_struct_0(A_136)
      | v2_struct_0(A_136) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_4,plain,(
    ! [A_1,B_2,C_5] :
      ( ~ r1_xboole_0(A_1,B_2)
      | ~ r2_hidden(C_5,k3_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_149,plain,(
    ! [D_144,A_148,B_146,B_145,A_147] :
      ( ~ r1_xboole_0(A_147,B_145)
      | ~ m1_subset_1(D_144,u1_struct_0(B_146))
      | ~ r2_waybel_0(A_148,B_146,k3_xboole_0(A_147,B_145))
      | ~ l1_waybel_0(B_146,A_148)
      | v2_struct_0(B_146)
      | ~ l1_struct_0(A_148)
      | v2_struct_0(A_148) ) ),
    inference(resolution,[status(thm)],[c_137,c_4])).

tff(c_159,plain,(
    ! [A_149,B_150,A_151,B_152] :
      ( ~ r1_xboole_0(A_149,B_150)
      | ~ r2_waybel_0(A_151,B_152,k3_xboole_0(A_149,B_150))
      | ~ l1_waybel_0(B_152,A_151)
      | v2_struct_0(B_152)
      | ~ l1_struct_0(A_151)
      | v2_struct_0(A_151) ) ),
    inference(resolution,[status(thm)],[c_12,c_149])).

tff(c_163,plain,(
    ! [A_149,B_150] :
      ( ~ r1_xboole_0(A_149,B_150)
      | ~ l1_waybel_0('#skF_6','#skF_5')
      | v2_struct_0('#skF_6')
      | ~ l1_struct_0('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_114,c_159])).

tff(c_166,plain,(
    ! [A_149,B_150] :
      ( ~ r1_xboole_0(A_149,B_150)
      | v2_struct_0('#skF_6')
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_36,c_163])).

tff(c_167,plain,(
    ! [A_149,B_150] : ~ r1_xboole_0(A_149,B_150) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_42,c_166])).

tff(c_60,plain,(
    ! [A_89,B_90] : r1_xboole_0(k4_xboole_0(A_89,B_90),B_90) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_63,plain,(
    ! [A_7] : r1_xboole_0(A_7,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_60])).

tff(c_171,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_167,c_63])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:14:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.15/1.30  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.15/1.30  
% 2.15/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.15/1.31  %$ r2_waybel_0 > r1_waybel_0 > r1_orders_2 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > l1_waybel_0 > v7_waybel_0 > v4_orders_2 > v2_struct_0 > l1_struct_0 > k2_waybel_0 > k6_subset_1 > k4_xboole_0 > k3_xboole_0 > #nlpp > u1_struct_0 > k1_xboole_0 > #skF_2 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_1
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
% 2.15/1.31  tff('#skF_5', type, '#skF_5': $i).
% 2.15/1.31  tff(r1_waybel_0, type, r1_waybel_0: ($i * $i * $i) > $o).
% 2.15/1.31  tff('#skF_6', type, '#skF_6': $i).
% 2.15/1.31  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.15/1.31  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 2.15/1.31  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.15/1.31  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.15/1.31  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 2.15/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.15/1.31  tff(l1_waybel_0, type, l1_waybel_0: ($i * $i) > $o).
% 2.15/1.31  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.15/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.15/1.31  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.15/1.31  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.15/1.31  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.15/1.31  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.15/1.31  
% 2.15/1.32  tff(f_131, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => r1_waybel_0(A, B, u1_struct_0(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_yellow_6)).
% 2.15/1.32  tff(f_41, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.15/1.32  tff(f_43, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 2.15/1.32  tff(f_50, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 2.15/1.32  tff(f_91, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((~v2_struct_0(B) & l1_waybel_0(B, A)) => (![C]: (r2_waybel_0(A, B, C) <=> ~r1_waybel_0(A, B, k6_subset_1(u1_struct_0(A), C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_waybel_0)).
% 2.15/1.32  tff(f_113, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((~v2_struct_0(B) & l1_waybel_0(B, A)) => (![C, D]: (r1_tarski(C, D) => ((r1_waybel_0(A, B, C) => r1_waybel_0(A, B, D)) & (r2_waybel_0(A, B, C) => r2_waybel_0(A, B, D))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_waybel_0)).
% 2.15/1.32  tff(f_48, axiom, (![A]: (?[B]: m1_subset_1(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', existence_m1_subset_1)).
% 2.15/1.32  tff(f_74, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((~v2_struct_0(B) & l1_waybel_0(B, A)) => (![C]: (r2_waybel_0(A, B, C) <=> (![D]: (m1_subset_1(D, u1_struct_0(B)) => (?[E]: ((m1_subset_1(E, u1_struct_0(B)) & r1_orders_2(B, D, E)) & r2_hidden(k2_waybel_0(A, B, E), C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d12_waybel_0)).
% 2.15/1.32  tff(f_39, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.15/1.32  tff(f_45, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 2.15/1.32  tff(c_46, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_131])).
% 2.15/1.32  tff(c_42, plain, (~v2_struct_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_131])).
% 2.15/1.32  tff(c_44, plain, (l1_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_131])).
% 2.15/1.32  tff(c_36, plain, (l1_waybel_0('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_131])).
% 2.15/1.32  tff(c_6, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.15/1.32  tff(c_8, plain, (![A_7]: (k4_xboole_0(A_7, k1_xboole_0)=A_7)), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.15/1.32  tff(c_14, plain, (![A_12, B_13]: (k6_subset_1(A_12, B_13)=k4_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.15/1.32  tff(c_28, plain, (![A_67, B_71, C_73]: (r2_waybel_0(A_67, B_71, C_73) | r1_waybel_0(A_67, B_71, k6_subset_1(u1_struct_0(A_67), C_73)) | ~l1_waybel_0(B_71, A_67) | v2_struct_0(B_71) | ~l1_struct_0(A_67) | v2_struct_0(A_67))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.15/1.32  tff(c_87, plain, (![A_107, B_108, C_109]: (r2_waybel_0(A_107, B_108, C_109) | r1_waybel_0(A_107, B_108, k4_xboole_0(u1_struct_0(A_107), C_109)) | ~l1_waybel_0(B_108, A_107) | v2_struct_0(B_108) | ~l1_struct_0(A_107) | v2_struct_0(A_107))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_28])).
% 2.15/1.32  tff(c_97, plain, (![A_114, B_115]: (r2_waybel_0(A_114, B_115, k1_xboole_0) | r1_waybel_0(A_114, B_115, u1_struct_0(A_114)) | ~l1_waybel_0(B_115, A_114) | v2_struct_0(B_115) | ~l1_struct_0(A_114) | v2_struct_0(A_114))), inference(superposition, [status(thm), theory('equality')], [c_8, c_87])).
% 2.15/1.32  tff(c_34, plain, (~r1_waybel_0('#skF_5', '#skF_6', u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_131])).
% 2.15/1.32  tff(c_103, plain, (r2_waybel_0('#skF_5', '#skF_6', k1_xboole_0) | ~l1_waybel_0('#skF_6', '#skF_5') | v2_struct_0('#skF_6') | ~l1_struct_0('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_97, c_34])).
% 2.15/1.32  tff(c_107, plain, (r2_waybel_0('#skF_5', '#skF_6', k1_xboole_0) | v2_struct_0('#skF_6') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_36, c_103])).
% 2.15/1.32  tff(c_108, plain, (r2_waybel_0('#skF_5', '#skF_6', k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_46, c_42, c_107])).
% 2.15/1.32  tff(c_30, plain, (![A_74, B_80, D_84, C_83]: (r2_waybel_0(A_74, B_80, D_84) | ~r2_waybel_0(A_74, B_80, C_83) | ~r1_tarski(C_83, D_84) | ~l1_waybel_0(B_80, A_74) | v2_struct_0(B_80) | ~l1_struct_0(A_74) | v2_struct_0(A_74))), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.15/1.32  tff(c_110, plain, (![D_84]: (r2_waybel_0('#skF_5', '#skF_6', D_84) | ~r1_tarski(k1_xboole_0, D_84) | ~l1_waybel_0('#skF_6', '#skF_5') | v2_struct_0('#skF_6') | ~l1_struct_0('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_108, c_30])).
% 2.15/1.32  tff(c_113, plain, (![D_84]: (r2_waybel_0('#skF_5', '#skF_6', D_84) | v2_struct_0('#skF_6') | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_36, c_6, c_110])).
% 2.15/1.32  tff(c_114, plain, (![D_84]: (r2_waybel_0('#skF_5', '#skF_6', D_84))), inference(negUnitSimplification, [status(thm)], [c_46, c_42, c_113])).
% 2.15/1.32  tff(c_12, plain, (![A_10]: (m1_subset_1('#skF_2'(A_10), A_10))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.15/1.32  tff(c_137, plain, (![A_136, B_137, C_138, D_139]: (r2_hidden(k2_waybel_0(A_136, B_137, '#skF_4'(A_136, B_137, C_138, D_139)), C_138) | ~m1_subset_1(D_139, u1_struct_0(B_137)) | ~r2_waybel_0(A_136, B_137, C_138) | ~l1_waybel_0(B_137, A_136) | v2_struct_0(B_137) | ~l1_struct_0(A_136) | v2_struct_0(A_136))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.15/1.32  tff(c_4, plain, (![A_1, B_2, C_5]: (~r1_xboole_0(A_1, B_2) | ~r2_hidden(C_5, k3_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.15/1.32  tff(c_149, plain, (![D_144, A_148, B_146, B_145, A_147]: (~r1_xboole_0(A_147, B_145) | ~m1_subset_1(D_144, u1_struct_0(B_146)) | ~r2_waybel_0(A_148, B_146, k3_xboole_0(A_147, B_145)) | ~l1_waybel_0(B_146, A_148) | v2_struct_0(B_146) | ~l1_struct_0(A_148) | v2_struct_0(A_148))), inference(resolution, [status(thm)], [c_137, c_4])).
% 2.15/1.32  tff(c_159, plain, (![A_149, B_150, A_151, B_152]: (~r1_xboole_0(A_149, B_150) | ~r2_waybel_0(A_151, B_152, k3_xboole_0(A_149, B_150)) | ~l1_waybel_0(B_152, A_151) | v2_struct_0(B_152) | ~l1_struct_0(A_151) | v2_struct_0(A_151))), inference(resolution, [status(thm)], [c_12, c_149])).
% 2.15/1.32  tff(c_163, plain, (![A_149, B_150]: (~r1_xboole_0(A_149, B_150) | ~l1_waybel_0('#skF_6', '#skF_5') | v2_struct_0('#skF_6') | ~l1_struct_0('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_114, c_159])).
% 2.15/1.32  tff(c_166, plain, (![A_149, B_150]: (~r1_xboole_0(A_149, B_150) | v2_struct_0('#skF_6') | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_36, c_163])).
% 2.15/1.32  tff(c_167, plain, (![A_149, B_150]: (~r1_xboole_0(A_149, B_150))), inference(negUnitSimplification, [status(thm)], [c_46, c_42, c_166])).
% 2.15/1.32  tff(c_60, plain, (![A_89, B_90]: (r1_xboole_0(k4_xboole_0(A_89, B_90), B_90))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.15/1.32  tff(c_63, plain, (![A_7]: (r1_xboole_0(A_7, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_60])).
% 2.15/1.32  tff(c_171, plain, $false, inference(negUnitSimplification, [status(thm)], [c_167, c_63])).
% 2.15/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.15/1.32  
% 2.15/1.32  Inference rules
% 2.15/1.32  ----------------------
% 2.15/1.32  #Ref     : 0
% 2.15/1.32  #Sup     : 22
% 2.15/1.32  #Fact    : 0
% 2.15/1.32  #Define  : 0
% 2.15/1.32  #Split   : 0
% 2.15/1.32  #Chain   : 0
% 2.15/1.32  #Close   : 0
% 2.15/1.32  
% 2.15/1.32  Ordering : KBO
% 2.15/1.32  
% 2.15/1.32  Simplification rules
% 2.15/1.32  ----------------------
% 2.15/1.32  #Subsume      : 5
% 2.15/1.32  #Demod        : 13
% 2.15/1.32  #Tautology    : 9
% 2.15/1.32  #SimpNegUnit  : 7
% 2.15/1.32  #BackRed      : 3
% 2.15/1.32  
% 2.15/1.32  #Partial instantiations: 0
% 2.15/1.32  #Strategies tried      : 1
% 2.15/1.32  
% 2.15/1.32  Timing (in seconds)
% 2.15/1.32  ----------------------
% 2.15/1.32  Preprocessing        : 0.33
% 2.15/1.32  Parsing              : 0.18
% 2.15/1.32  CNF conversion       : 0.03
% 2.15/1.32  Main loop            : 0.17
% 2.15/1.32  Inferencing          : 0.07
% 2.15/1.32  Reduction            : 0.05
% 2.15/1.32  Demodulation         : 0.04
% 2.15/1.32  BG Simplification    : 0.01
% 2.15/1.32  Subsumption          : 0.03
% 2.15/1.32  Abstraction          : 0.01
% 2.15/1.33  MUC search           : 0.00
% 2.15/1.33  Cooper               : 0.00
% 2.15/1.33  Total                : 0.54
% 2.15/1.33  Index Insertion      : 0.00
% 2.15/1.33  Index Deletion       : 0.00
% 2.15/1.33  Index Matching       : 0.00
% 2.15/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
