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
% DateTime   : Thu Dec  3 10:30:52 EST 2020

% Result     : Theorem 2.48s
% Output     : CNFRefutation 2.65s
% Verified   : 
% Statistics : Number of formulae       :   63 (  77 expanded)
%              Number of leaves         :   35 (  44 expanded)
%              Depth                    :   10
%              Number of atoms          :  103 ( 165 expanded)
%              Number of equality atoms :    9 (  11 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_waybel_0 > r1_waybel_0 > r1_orders_2 > r2_hidden > r1_xboole_0 > m1_subset_1 > l1_waybel_0 > v7_waybel_0 > v4_orders_2 > v2_struct_0 > l1_struct_0 > k2_waybel_0 > k6_subset_1 > k4_xboole_0 > #nlpp > u1_struct_0 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(r2_waybel_0,type,(
    r2_waybel_0: ( $i * $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_waybel_0,type,(
    k2_waybel_0: ( $i * $i * $i ) > $i )).

tff(v7_waybel_0,type,(
    v7_waybel_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_waybel_0,type,(
    r1_waybel_0: ( $i * $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_yellow_6)).

tff(f_31,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

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

tff(f_33,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(c_46,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_42,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_44,plain,(
    l1_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_36,plain,(
    l1_waybel_0('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_4,plain,(
    ! [A_3] : k4_xboole_0(A_3,k1_xboole_0) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

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

tff(c_248,plain,(
    ! [A_104,B_105,C_106] :
      ( r2_waybel_0(A_104,B_105,C_106)
      | r1_waybel_0(A_104,B_105,k4_xboole_0(u1_struct_0(A_104),C_106))
      | ~ l1_waybel_0(B_105,A_104)
      | v2_struct_0(B_105)
      | ~ l1_struct_0(A_104)
      | v2_struct_0(A_104) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_32])).

tff(c_453,plain,(
    ! [A_128,B_129] :
      ( r2_waybel_0(A_128,B_129,k1_xboole_0)
      | r1_waybel_0(A_128,B_129,u1_struct_0(A_128))
      | ~ l1_waybel_0(B_129,A_128)
      | v2_struct_0(B_129)
      | ~ l1_struct_0(A_128)
      | v2_struct_0(A_128) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_248])).

tff(c_34,plain,(
    ~ r1_waybel_0('#skF_4','#skF_5',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_456,plain,
    ( r2_waybel_0('#skF_4','#skF_5',k1_xboole_0)
    | ~ l1_waybel_0('#skF_5','#skF_4')
    | v2_struct_0('#skF_5')
    | ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_453,c_34])).

tff(c_459,plain,
    ( r2_waybel_0('#skF_4','#skF_5',k1_xboole_0)
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_36,c_456])).

tff(c_460,plain,(
    r2_waybel_0('#skF_4','#skF_5',k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_42,c_459])).

tff(c_16,plain,(
    ! [A_10] : m1_subset_1('#skF_1'(A_10),A_10) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_509,plain,(
    ! [A_151,B_152,C_153,D_154] :
      ( r2_hidden(k2_waybel_0(A_151,B_152,'#skF_3'(A_151,B_152,C_153,D_154)),C_153)
      | ~ m1_subset_1(D_154,u1_struct_0(B_152))
      | ~ r2_waybel_0(A_151,B_152,C_153)
      | ~ l1_waybel_0(B_152,A_151)
      | v2_struct_0(B_152)
      | ~ l1_struct_0(A_151)
      | v2_struct_0(A_151) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_59,plain,(
    ! [A_77,B_78] : r1_xboole_0(k4_xboole_0(A_77,B_78),B_78) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_62,plain,(
    ! [A_3] : r1_xboole_0(A_3,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_59])).

tff(c_73,plain,(
    ! [B_82,A_83] :
      ( r1_xboole_0(B_82,A_83)
      | ~ r1_xboole_0(A_83,B_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_78,plain,(
    ! [A_3] : r1_xboole_0(k1_xboole_0,A_3) ),
    inference(resolution,[status(thm)],[c_62,c_73])).

tff(c_98,plain,(
    ! [A_89,B_90] :
      ( k4_xboole_0(A_89,B_90) = A_89
      | ~ r1_xboole_0(A_89,B_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_116,plain,(
    ! [A_3] : k4_xboole_0(k1_xboole_0,A_3) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_78,c_98])).

tff(c_238,plain,(
    ! [B_102,A_103] :
      ( ~ r2_hidden(B_102,A_103)
      | k4_xboole_0(A_103,k1_tarski(B_102)) != A_103 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_247,plain,(
    ! [B_102] : ~ r2_hidden(B_102,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_116,c_238])).

tff(c_519,plain,(
    ! [D_155,B_156,A_157] :
      ( ~ m1_subset_1(D_155,u1_struct_0(B_156))
      | ~ r2_waybel_0(A_157,B_156,k1_xboole_0)
      | ~ l1_waybel_0(B_156,A_157)
      | v2_struct_0(B_156)
      | ~ l1_struct_0(A_157)
      | v2_struct_0(A_157) ) ),
    inference(resolution,[status(thm)],[c_509,c_247])).

tff(c_529,plain,(
    ! [A_158,B_159] :
      ( ~ r2_waybel_0(A_158,B_159,k1_xboole_0)
      | ~ l1_waybel_0(B_159,A_158)
      | v2_struct_0(B_159)
      | ~ l1_struct_0(A_158)
      | v2_struct_0(A_158) ) ),
    inference(resolution,[status(thm)],[c_16,c_519])).

tff(c_532,plain,
    ( ~ l1_waybel_0('#skF_5','#skF_4')
    | v2_struct_0('#skF_5')
    | ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_460,c_529])).

tff(c_535,plain,
    ( v2_struct_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_36,c_532])).

tff(c_537,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_42,c_535])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:28:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.48/1.35  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.48/1.35  
% 2.48/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.48/1.35  %$ r2_waybel_0 > r1_waybel_0 > r1_orders_2 > r2_hidden > r1_xboole_0 > m1_subset_1 > l1_waybel_0 > v7_waybel_0 > v4_orders_2 > v2_struct_0 > l1_struct_0 > k2_waybel_0 > k6_subset_1 > k4_xboole_0 > #nlpp > u1_struct_0 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3
% 2.48/1.35  
% 2.48/1.35  %Foreground sorts:
% 2.48/1.35  
% 2.48/1.35  
% 2.48/1.35  %Background operators:
% 2.48/1.35  
% 2.48/1.35  
% 2.48/1.35  %Foreground operators:
% 2.48/1.35  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.48/1.35  tff(r2_waybel_0, type, r2_waybel_0: ($i * $i * $i) > $o).
% 2.48/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.48/1.35  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.48/1.35  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.48/1.35  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.48/1.35  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.48/1.35  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 2.48/1.35  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.48/1.35  tff(k2_waybel_0, type, k2_waybel_0: ($i * $i * $i) > $i).
% 2.48/1.35  tff(v7_waybel_0, type, v7_waybel_0: $i > $o).
% 2.48/1.35  tff('#skF_5', type, '#skF_5': $i).
% 2.48/1.35  tff(r1_waybel_0, type, r1_waybel_0: ($i * $i * $i) > $o).
% 2.48/1.35  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.48/1.35  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 2.48/1.35  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.48/1.35  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.48/1.35  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.48/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.48/1.35  tff(l1_waybel_0, type, l1_waybel_0: ($i * $i) > $o).
% 2.48/1.35  tff('#skF_4', type, '#skF_4': $i).
% 2.48/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.48/1.35  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 2.48/1.35  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.48/1.35  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.48/1.35  
% 2.65/1.37  tff(f_106, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => r1_waybel_0(A, B, u1_struct_0(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_yellow_6)).
% 2.65/1.37  tff(f_31, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 2.65/1.37  tff(f_47, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 2.65/1.37  tff(f_88, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((~v2_struct_0(B) & l1_waybel_0(B, A)) => (![C]: (r2_waybel_0(A, B, C) <=> ~r1_waybel_0(A, B, k6_subset_1(u1_struct_0(A), C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_waybel_0)).
% 2.65/1.37  tff(f_45, axiom, (![A]: (?[B]: m1_subset_1(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', existence_m1_subset_1)).
% 2.65/1.37  tff(f_71, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((~v2_struct_0(B) & l1_waybel_0(B, A)) => (![C]: (r2_waybel_0(A, B, C) <=> (![D]: (m1_subset_1(D, u1_struct_0(B)) => (?[E]: ((m1_subset_1(E, u1_struct_0(B)) & r1_orders_2(B, D, E)) & r2_hidden(k2_waybel_0(A, B, E), C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d12_waybel_0)).
% 2.65/1.37  tff(f_33, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 2.65/1.37  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 2.65/1.37  tff(f_37, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.65/1.37  tff(f_42, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 2.65/1.37  tff(c_46, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.65/1.37  tff(c_42, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.65/1.37  tff(c_44, plain, (l1_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.65/1.37  tff(c_36, plain, (l1_waybel_0('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.65/1.37  tff(c_4, plain, (![A_3]: (k4_xboole_0(A_3, k1_xboole_0)=A_3)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.65/1.37  tff(c_18, plain, (![A_12, B_13]: (k6_subset_1(A_12, B_13)=k4_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.65/1.37  tff(c_32, plain, (![A_67, B_71, C_73]: (r2_waybel_0(A_67, B_71, C_73) | r1_waybel_0(A_67, B_71, k6_subset_1(u1_struct_0(A_67), C_73)) | ~l1_waybel_0(B_71, A_67) | v2_struct_0(B_71) | ~l1_struct_0(A_67) | v2_struct_0(A_67))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.65/1.37  tff(c_248, plain, (![A_104, B_105, C_106]: (r2_waybel_0(A_104, B_105, C_106) | r1_waybel_0(A_104, B_105, k4_xboole_0(u1_struct_0(A_104), C_106)) | ~l1_waybel_0(B_105, A_104) | v2_struct_0(B_105) | ~l1_struct_0(A_104) | v2_struct_0(A_104))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_32])).
% 2.65/1.37  tff(c_453, plain, (![A_128, B_129]: (r2_waybel_0(A_128, B_129, k1_xboole_0) | r1_waybel_0(A_128, B_129, u1_struct_0(A_128)) | ~l1_waybel_0(B_129, A_128) | v2_struct_0(B_129) | ~l1_struct_0(A_128) | v2_struct_0(A_128))), inference(superposition, [status(thm), theory('equality')], [c_4, c_248])).
% 2.65/1.37  tff(c_34, plain, (~r1_waybel_0('#skF_4', '#skF_5', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.65/1.37  tff(c_456, plain, (r2_waybel_0('#skF_4', '#skF_5', k1_xboole_0) | ~l1_waybel_0('#skF_5', '#skF_4') | v2_struct_0('#skF_5') | ~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_453, c_34])).
% 2.65/1.37  tff(c_459, plain, (r2_waybel_0('#skF_4', '#skF_5', k1_xboole_0) | v2_struct_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_36, c_456])).
% 2.65/1.37  tff(c_460, plain, (r2_waybel_0('#skF_4', '#skF_5', k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_46, c_42, c_459])).
% 2.65/1.37  tff(c_16, plain, (![A_10]: (m1_subset_1('#skF_1'(A_10), A_10))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.65/1.37  tff(c_509, plain, (![A_151, B_152, C_153, D_154]: (r2_hidden(k2_waybel_0(A_151, B_152, '#skF_3'(A_151, B_152, C_153, D_154)), C_153) | ~m1_subset_1(D_154, u1_struct_0(B_152)) | ~r2_waybel_0(A_151, B_152, C_153) | ~l1_waybel_0(B_152, A_151) | v2_struct_0(B_152) | ~l1_struct_0(A_151) | v2_struct_0(A_151))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.65/1.37  tff(c_59, plain, (![A_77, B_78]: (r1_xboole_0(k4_xboole_0(A_77, B_78), B_78))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.65/1.37  tff(c_62, plain, (![A_3]: (r1_xboole_0(A_3, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_4, c_59])).
% 2.65/1.37  tff(c_73, plain, (![B_82, A_83]: (r1_xboole_0(B_82, A_83) | ~r1_xboole_0(A_83, B_82))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.65/1.37  tff(c_78, plain, (![A_3]: (r1_xboole_0(k1_xboole_0, A_3))), inference(resolution, [status(thm)], [c_62, c_73])).
% 2.65/1.37  tff(c_98, plain, (![A_89, B_90]: (k4_xboole_0(A_89, B_90)=A_89 | ~r1_xboole_0(A_89, B_90))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.65/1.37  tff(c_116, plain, (![A_3]: (k4_xboole_0(k1_xboole_0, A_3)=k1_xboole_0)), inference(resolution, [status(thm)], [c_78, c_98])).
% 2.65/1.37  tff(c_238, plain, (![B_102, A_103]: (~r2_hidden(B_102, A_103) | k4_xboole_0(A_103, k1_tarski(B_102))!=A_103)), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.65/1.37  tff(c_247, plain, (![B_102]: (~r2_hidden(B_102, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_116, c_238])).
% 2.65/1.37  tff(c_519, plain, (![D_155, B_156, A_157]: (~m1_subset_1(D_155, u1_struct_0(B_156)) | ~r2_waybel_0(A_157, B_156, k1_xboole_0) | ~l1_waybel_0(B_156, A_157) | v2_struct_0(B_156) | ~l1_struct_0(A_157) | v2_struct_0(A_157))), inference(resolution, [status(thm)], [c_509, c_247])).
% 2.65/1.37  tff(c_529, plain, (![A_158, B_159]: (~r2_waybel_0(A_158, B_159, k1_xboole_0) | ~l1_waybel_0(B_159, A_158) | v2_struct_0(B_159) | ~l1_struct_0(A_158) | v2_struct_0(A_158))), inference(resolution, [status(thm)], [c_16, c_519])).
% 2.65/1.37  tff(c_532, plain, (~l1_waybel_0('#skF_5', '#skF_4') | v2_struct_0('#skF_5') | ~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_460, c_529])).
% 2.65/1.37  tff(c_535, plain, (v2_struct_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_36, c_532])).
% 2.65/1.37  tff(c_537, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_42, c_535])).
% 2.65/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.65/1.37  
% 2.65/1.37  Inference rules
% 2.65/1.37  ----------------------
% 2.65/1.37  #Ref     : 0
% 2.65/1.37  #Sup     : 111
% 2.65/1.37  #Fact    : 0
% 2.65/1.37  #Define  : 0
% 2.65/1.37  #Split   : 0
% 2.65/1.37  #Chain   : 0
% 2.65/1.37  #Close   : 0
% 2.65/1.37  
% 2.65/1.37  Ordering : KBO
% 2.65/1.37  
% 2.65/1.37  Simplification rules
% 2.65/1.37  ----------------------
% 2.65/1.37  #Subsume      : 21
% 2.65/1.37  #Demod        : 39
% 2.65/1.37  #Tautology    : 62
% 2.65/1.37  #SimpNegUnit  : 6
% 2.65/1.37  #BackRed      : 0
% 2.65/1.37  
% 2.65/1.37  #Partial instantiations: 0
% 2.65/1.37  #Strategies tried      : 1
% 2.65/1.37  
% 2.65/1.37  Timing (in seconds)
% 2.65/1.37  ----------------------
% 2.65/1.37  Preprocessing        : 0.34
% 2.65/1.37  Parsing              : 0.17
% 2.65/1.37  CNF conversion       : 0.03
% 2.65/1.37  Main loop            : 0.26
% 2.65/1.37  Inferencing          : 0.11
% 2.65/1.37  Reduction            : 0.08
% 2.65/1.37  Demodulation         : 0.06
% 2.65/1.37  BG Simplification    : 0.02
% 2.65/1.37  Subsumption          : 0.04
% 2.65/1.37  Abstraction          : 0.02
% 2.65/1.37  MUC search           : 0.00
% 2.65/1.37  Cooper               : 0.00
% 2.65/1.37  Total                : 0.63
% 2.65/1.37  Index Insertion      : 0.00
% 2.65/1.37  Index Deletion       : 0.00
% 2.65/1.37  Index Matching       : 0.00
% 2.65/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
