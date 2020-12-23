%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:51 EST 2020

% Result     : Theorem 23.41s
% Output     : CNFRefutation 23.44s
% Verified   : 
% Statistics : Number of formulae       :   61 (  78 expanded)
%              Number of leaves         :   34 (  45 expanded)
%              Depth                    :   11
%              Number of atoms          :  111 ( 181 expanded)
%              Number of equality atoms :    8 (   9 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_waybel_0 > r1_waybel_0 > r1_orders_2 > r2_hidden > r1_tarski > m1_subset_1 > l1_waybel_0 > v7_waybel_0 > v4_orders_2 > v2_struct_0 > l1_struct_0 > k2_waybel_0 > k6_subset_1 > k4_xboole_0 > #nlpp > u1_struct_0 > k1_xboole_0 > #skF_1 > #skF_4 > #skF_7 > #skF_6 > #skF_2 > #skF_5 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(r2_waybel_0,type,(
    r2_waybel_0: ( $i * $i * $i ) > $o )).

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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_waybel_0,type,(
    r1_waybel_0: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(l1_waybel_0,type,(
    l1_waybel_0: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_106,negated_conjecture,(
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

tff(f_37,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_47,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_42,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_88,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & l1_waybel_0(B,A) )
         => ! [C] :
              ( r1_waybel_0(A,B,C)
            <=> ~ r2_waybel_0(A,B,k6_subset_1(u1_struct_0(A),C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_waybel_0)).

tff(f_40,axiom,(
    ! [A] :
    ? [B] : m1_subset_1(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_waybel_0)).

tff(c_54,plain,(
    ~ v2_struct_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_50,plain,(
    ~ v2_struct_0('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_52,plain,(
    l1_struct_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_44,plain,(
    l1_waybel_0('#skF_7','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_20,plain,(
    ! [A_7] : r1_tarski(k1_xboole_0,A_7) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_96,plain,(
    ! [A_99,B_100,C_101] :
      ( r2_hidden('#skF_1'(A_99,B_100,C_101),A_99)
      | r2_hidden('#skF_2'(A_99,B_100,C_101),C_101)
      | k4_xboole_0(A_99,B_100) = C_101 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_16,plain,(
    ! [A_1,B_2,C_3] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2,C_3),B_2)
      | r2_hidden('#skF_2'(A_1,B_2,C_3),C_3)
      | k4_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_150,plain,(
    ! [A_107,C_108] :
      ( r2_hidden('#skF_2'(A_107,A_107,C_108),C_108)
      | k4_xboole_0(A_107,A_107) = C_108 ) ),
    inference(resolution,[status(thm)],[c_96,c_16])).

tff(c_26,plain,(
    ! [B_13,A_12] :
      ( ~ r1_tarski(B_13,A_12)
      | ~ r2_hidden(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_225,plain,(
    ! [C_119,A_120] :
      ( ~ r1_tarski(C_119,'#skF_2'(A_120,A_120,C_119))
      | k4_xboole_0(A_120,A_120) = C_119 ) ),
    inference(resolution,[status(thm)],[c_150,c_26])).

tff(c_233,plain,(
    ! [A_121] : k4_xboole_0(A_121,A_121) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_20,c_225])).

tff(c_24,plain,(
    ! [A_10,B_11] : k6_subset_1(A_10,B_11) = k4_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_40,plain,(
    ! [A_67,B_71,C_73] :
      ( r1_waybel_0(A_67,B_71,C_73)
      | r2_waybel_0(A_67,B_71,k6_subset_1(u1_struct_0(A_67),C_73))
      | ~ l1_waybel_0(B_71,A_67)
      | v2_struct_0(B_71)
      | ~ l1_struct_0(A_67)
      | v2_struct_0(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_55,plain,(
    ! [A_67,B_71,C_73] :
      ( r1_waybel_0(A_67,B_71,C_73)
      | r2_waybel_0(A_67,B_71,k4_xboole_0(u1_struct_0(A_67),C_73))
      | ~ l1_waybel_0(B_71,A_67)
      | v2_struct_0(B_71)
      | ~ l1_struct_0(A_67)
      | v2_struct_0(A_67) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_40])).

tff(c_81577,plain,(
    ! [A_1262,B_1263] :
      ( r1_waybel_0(A_1262,B_1263,u1_struct_0(A_1262))
      | r2_waybel_0(A_1262,B_1263,k1_xboole_0)
      | ~ l1_waybel_0(B_1263,A_1262)
      | v2_struct_0(B_1263)
      | ~ l1_struct_0(A_1262)
      | v2_struct_0(A_1262) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_233,c_55])).

tff(c_42,plain,(
    ~ r1_waybel_0('#skF_6','#skF_7',u1_struct_0('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_81580,plain,
    ( r2_waybel_0('#skF_6','#skF_7',k1_xboole_0)
    | ~ l1_waybel_0('#skF_7','#skF_6')
    | v2_struct_0('#skF_7')
    | ~ l1_struct_0('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_81577,c_42])).

tff(c_81583,plain,
    ( r2_waybel_0('#skF_6','#skF_7',k1_xboole_0)
    | v2_struct_0('#skF_7')
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_44,c_81580])).

tff(c_81584,plain,(
    r2_waybel_0('#skF_6','#skF_7',k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_50,c_81583])).

tff(c_22,plain,(
    ! [A_8] : m1_subset_1('#skF_3'(A_8),A_8) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_823,plain,(
    ! [A_187,B_188,C_189,D_190] :
      ( r2_hidden(k2_waybel_0(A_187,B_188,'#skF_5'(A_187,B_188,C_189,D_190)),C_189)
      | ~ m1_subset_1(D_190,u1_struct_0(B_188))
      | ~ r2_waybel_0(A_187,B_188,C_189)
      | ~ l1_waybel_0(B_188,A_187)
      | v2_struct_0(B_188)
      | ~ l1_struct_0(A_187)
      | v2_struct_0(A_187) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_9329,plain,(
    ! [C_415,A_416,B_417,D_418] :
      ( ~ r1_tarski(C_415,k2_waybel_0(A_416,B_417,'#skF_5'(A_416,B_417,C_415,D_418)))
      | ~ m1_subset_1(D_418,u1_struct_0(B_417))
      | ~ r2_waybel_0(A_416,B_417,C_415)
      | ~ l1_waybel_0(B_417,A_416)
      | v2_struct_0(B_417)
      | ~ l1_struct_0(A_416)
      | v2_struct_0(A_416) ) ),
    inference(resolution,[status(thm)],[c_823,c_26])).

tff(c_13258,plain,(
    ! [D_494,B_495,A_496] :
      ( ~ m1_subset_1(D_494,u1_struct_0(B_495))
      | ~ r2_waybel_0(A_496,B_495,k1_xboole_0)
      | ~ l1_waybel_0(B_495,A_496)
      | v2_struct_0(B_495)
      | ~ l1_struct_0(A_496)
      | v2_struct_0(A_496) ) ),
    inference(resolution,[status(thm)],[c_20,c_9329])).

tff(c_13267,plain,(
    ! [A_496,B_495] :
      ( ~ r2_waybel_0(A_496,B_495,k1_xboole_0)
      | ~ l1_waybel_0(B_495,A_496)
      | v2_struct_0(B_495)
      | ~ l1_struct_0(A_496)
      | v2_struct_0(A_496) ) ),
    inference(resolution,[status(thm)],[c_22,c_13258])).

tff(c_81587,plain,
    ( ~ l1_waybel_0('#skF_7','#skF_6')
    | v2_struct_0('#skF_7')
    | ~ l1_struct_0('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_81584,c_13267])).

tff(c_81590,plain,
    ( v2_struct_0('#skF_7')
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_44,c_81587])).

tff(c_81592,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_50,c_81590])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n023.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 19:01:05 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 23.41/15.35  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 23.44/15.36  
% 23.44/15.36  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 23.44/15.36  %$ r2_waybel_0 > r1_waybel_0 > r1_orders_2 > r2_hidden > r1_tarski > m1_subset_1 > l1_waybel_0 > v7_waybel_0 > v4_orders_2 > v2_struct_0 > l1_struct_0 > k2_waybel_0 > k6_subset_1 > k4_xboole_0 > #nlpp > u1_struct_0 > k1_xboole_0 > #skF_1 > #skF_4 > #skF_7 > #skF_6 > #skF_2 > #skF_5 > #skF_3
% 23.44/15.36  
% 23.44/15.36  %Foreground sorts:
% 23.44/15.36  
% 23.44/15.36  
% 23.44/15.36  %Background operators:
% 23.44/15.36  
% 23.44/15.36  
% 23.44/15.36  %Foreground operators:
% 23.44/15.36  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 23.44/15.36  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 23.44/15.36  tff(r2_waybel_0, type, r2_waybel_0: ($i * $i * $i) > $o).
% 23.44/15.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 23.44/15.36  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 23.44/15.36  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 23.44/15.36  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 23.44/15.36  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 23.44/15.36  tff(k2_waybel_0, type, k2_waybel_0: ($i * $i * $i) > $i).
% 23.44/15.36  tff(v7_waybel_0, type, v7_waybel_0: $i > $o).
% 23.44/15.36  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 23.44/15.36  tff('#skF_7', type, '#skF_7': $i).
% 23.44/15.36  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 23.44/15.36  tff(r1_waybel_0, type, r1_waybel_0: ($i * $i * $i) > $o).
% 23.44/15.36  tff('#skF_6', type, '#skF_6': $i).
% 23.44/15.36  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 23.44/15.36  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 23.44/15.36  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 23.44/15.36  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 23.44/15.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 23.44/15.36  tff(l1_waybel_0, type, l1_waybel_0: ($i * $i) > $o).
% 23.44/15.36  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i) > $i).
% 23.44/15.36  tff('#skF_3', type, '#skF_3': $i > $i).
% 23.44/15.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 23.44/15.36  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 23.44/15.36  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 23.44/15.36  
% 23.44/15.37  tff(f_106, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => r1_waybel_0(A, B, u1_struct_0(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_yellow_6)).
% 23.44/15.37  tff(f_37, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 23.44/15.37  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 23.44/15.37  tff(f_47, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 23.44/15.37  tff(f_42, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 23.44/15.37  tff(f_88, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((~v2_struct_0(B) & l1_waybel_0(B, A)) => (![C]: (r1_waybel_0(A, B, C) <=> ~r2_waybel_0(A, B, k6_subset_1(u1_struct_0(A), C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_waybel_0)).
% 23.44/15.37  tff(f_40, axiom, (![A]: (?[B]: m1_subset_1(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', existence_m1_subset_1)).
% 23.44/15.37  tff(f_71, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((~v2_struct_0(B) & l1_waybel_0(B, A)) => (![C]: (r2_waybel_0(A, B, C) <=> (![D]: (m1_subset_1(D, u1_struct_0(B)) => (?[E]: ((m1_subset_1(E, u1_struct_0(B)) & r1_orders_2(B, D, E)) & r2_hidden(k2_waybel_0(A, B, E), C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_waybel_0)).
% 23.44/15.37  tff(c_54, plain, (~v2_struct_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_106])).
% 23.44/15.37  tff(c_50, plain, (~v2_struct_0('#skF_7')), inference(cnfTransformation, [status(thm)], [f_106])).
% 23.44/15.37  tff(c_52, plain, (l1_struct_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_106])).
% 23.44/15.37  tff(c_44, plain, (l1_waybel_0('#skF_7', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_106])).
% 23.44/15.37  tff(c_20, plain, (![A_7]: (r1_tarski(k1_xboole_0, A_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 23.44/15.37  tff(c_96, plain, (![A_99, B_100, C_101]: (r2_hidden('#skF_1'(A_99, B_100, C_101), A_99) | r2_hidden('#skF_2'(A_99, B_100, C_101), C_101) | k4_xboole_0(A_99, B_100)=C_101)), inference(cnfTransformation, [status(thm)], [f_35])).
% 23.44/15.37  tff(c_16, plain, (![A_1, B_2, C_3]: (~r2_hidden('#skF_1'(A_1, B_2, C_3), B_2) | r2_hidden('#skF_2'(A_1, B_2, C_3), C_3) | k4_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_35])).
% 23.44/15.37  tff(c_150, plain, (![A_107, C_108]: (r2_hidden('#skF_2'(A_107, A_107, C_108), C_108) | k4_xboole_0(A_107, A_107)=C_108)), inference(resolution, [status(thm)], [c_96, c_16])).
% 23.44/15.37  tff(c_26, plain, (![B_13, A_12]: (~r1_tarski(B_13, A_12) | ~r2_hidden(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_47])).
% 23.44/15.37  tff(c_225, plain, (![C_119, A_120]: (~r1_tarski(C_119, '#skF_2'(A_120, A_120, C_119)) | k4_xboole_0(A_120, A_120)=C_119)), inference(resolution, [status(thm)], [c_150, c_26])).
% 23.44/15.37  tff(c_233, plain, (![A_121]: (k4_xboole_0(A_121, A_121)=k1_xboole_0)), inference(resolution, [status(thm)], [c_20, c_225])).
% 23.44/15.37  tff(c_24, plain, (![A_10, B_11]: (k6_subset_1(A_10, B_11)=k4_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_42])).
% 23.44/15.37  tff(c_40, plain, (![A_67, B_71, C_73]: (r1_waybel_0(A_67, B_71, C_73) | r2_waybel_0(A_67, B_71, k6_subset_1(u1_struct_0(A_67), C_73)) | ~l1_waybel_0(B_71, A_67) | v2_struct_0(B_71) | ~l1_struct_0(A_67) | v2_struct_0(A_67))), inference(cnfTransformation, [status(thm)], [f_88])).
% 23.44/15.37  tff(c_55, plain, (![A_67, B_71, C_73]: (r1_waybel_0(A_67, B_71, C_73) | r2_waybel_0(A_67, B_71, k4_xboole_0(u1_struct_0(A_67), C_73)) | ~l1_waybel_0(B_71, A_67) | v2_struct_0(B_71) | ~l1_struct_0(A_67) | v2_struct_0(A_67))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_40])).
% 23.44/15.37  tff(c_81577, plain, (![A_1262, B_1263]: (r1_waybel_0(A_1262, B_1263, u1_struct_0(A_1262)) | r2_waybel_0(A_1262, B_1263, k1_xboole_0) | ~l1_waybel_0(B_1263, A_1262) | v2_struct_0(B_1263) | ~l1_struct_0(A_1262) | v2_struct_0(A_1262))), inference(superposition, [status(thm), theory('equality')], [c_233, c_55])).
% 23.44/15.37  tff(c_42, plain, (~r1_waybel_0('#skF_6', '#skF_7', u1_struct_0('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_106])).
% 23.44/15.37  tff(c_81580, plain, (r2_waybel_0('#skF_6', '#skF_7', k1_xboole_0) | ~l1_waybel_0('#skF_7', '#skF_6') | v2_struct_0('#skF_7') | ~l1_struct_0('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_81577, c_42])).
% 23.44/15.37  tff(c_81583, plain, (r2_waybel_0('#skF_6', '#skF_7', k1_xboole_0) | v2_struct_0('#skF_7') | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_44, c_81580])).
% 23.44/15.37  tff(c_81584, plain, (r2_waybel_0('#skF_6', '#skF_7', k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_54, c_50, c_81583])).
% 23.44/15.37  tff(c_22, plain, (![A_8]: (m1_subset_1('#skF_3'(A_8), A_8))), inference(cnfTransformation, [status(thm)], [f_40])).
% 23.44/15.37  tff(c_823, plain, (![A_187, B_188, C_189, D_190]: (r2_hidden(k2_waybel_0(A_187, B_188, '#skF_5'(A_187, B_188, C_189, D_190)), C_189) | ~m1_subset_1(D_190, u1_struct_0(B_188)) | ~r2_waybel_0(A_187, B_188, C_189) | ~l1_waybel_0(B_188, A_187) | v2_struct_0(B_188) | ~l1_struct_0(A_187) | v2_struct_0(A_187))), inference(cnfTransformation, [status(thm)], [f_71])).
% 23.44/15.37  tff(c_9329, plain, (![C_415, A_416, B_417, D_418]: (~r1_tarski(C_415, k2_waybel_0(A_416, B_417, '#skF_5'(A_416, B_417, C_415, D_418))) | ~m1_subset_1(D_418, u1_struct_0(B_417)) | ~r2_waybel_0(A_416, B_417, C_415) | ~l1_waybel_0(B_417, A_416) | v2_struct_0(B_417) | ~l1_struct_0(A_416) | v2_struct_0(A_416))), inference(resolution, [status(thm)], [c_823, c_26])).
% 23.44/15.37  tff(c_13258, plain, (![D_494, B_495, A_496]: (~m1_subset_1(D_494, u1_struct_0(B_495)) | ~r2_waybel_0(A_496, B_495, k1_xboole_0) | ~l1_waybel_0(B_495, A_496) | v2_struct_0(B_495) | ~l1_struct_0(A_496) | v2_struct_0(A_496))), inference(resolution, [status(thm)], [c_20, c_9329])).
% 23.44/15.37  tff(c_13267, plain, (![A_496, B_495]: (~r2_waybel_0(A_496, B_495, k1_xboole_0) | ~l1_waybel_0(B_495, A_496) | v2_struct_0(B_495) | ~l1_struct_0(A_496) | v2_struct_0(A_496))), inference(resolution, [status(thm)], [c_22, c_13258])).
% 23.44/15.37  tff(c_81587, plain, (~l1_waybel_0('#skF_7', '#skF_6') | v2_struct_0('#skF_7') | ~l1_struct_0('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_81584, c_13267])).
% 23.44/15.37  tff(c_81590, plain, (v2_struct_0('#skF_7') | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_44, c_81587])).
% 23.44/15.37  tff(c_81592, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_50, c_81590])).
% 23.44/15.37  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 23.44/15.37  
% 23.44/15.37  Inference rules
% 23.44/15.37  ----------------------
% 23.44/15.37  #Ref     : 0
% 23.44/15.37  #Sup     : 20637
% 23.44/15.37  #Fact    : 2
% 23.44/15.37  #Define  : 0
% 23.44/15.37  #Split   : 0
% 23.44/15.37  #Chain   : 0
% 23.44/15.37  #Close   : 0
% 23.44/15.37  
% 23.44/15.37  Ordering : KBO
% 23.44/15.37  
% 23.44/15.37  Simplification rules
% 23.44/15.37  ----------------------
% 23.44/15.37  #Subsume      : 10694
% 23.44/15.37  #Demod        : 23619
% 23.44/15.37  #Tautology    : 4800
% 23.44/15.37  #SimpNegUnit  : 2
% 23.44/15.37  #BackRed      : 2
% 23.44/15.37  
% 23.44/15.37  #Partial instantiations: 0
% 23.44/15.37  #Strategies tried      : 1
% 23.44/15.37  
% 23.44/15.37  Timing (in seconds)
% 23.44/15.37  ----------------------
% 23.44/15.38  Preprocessing        : 0.32
% 23.44/15.38  Parsing              : 0.16
% 23.44/15.38  CNF conversion       : 0.03
% 23.44/15.38  Main loop            : 14.28
% 23.44/15.38  Inferencing          : 2.36
% 23.44/15.38  Reduction            : 7.52
% 23.44/15.38  Demodulation         : 6.92
% 23.44/15.38  BG Simplification    : 0.19
% 23.44/15.38  Subsumption          : 3.79
% 23.44/15.38  Abstraction          : 0.56
% 23.44/15.38  MUC search           : 0.00
% 23.44/15.38  Cooper               : 0.00
% 23.44/15.38  Total                : 14.63
% 23.44/15.38  Index Insertion      : 0.00
% 23.44/15.38  Index Deletion       : 0.00
% 23.44/15.38  Index Matching       : 0.00
% 23.44/15.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
