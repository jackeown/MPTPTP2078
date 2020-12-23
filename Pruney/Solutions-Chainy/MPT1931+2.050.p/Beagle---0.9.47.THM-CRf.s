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

% Result     : Theorem 2.50s
% Output     : CNFRefutation 2.59s
% Verified   : 
% Statistics : Number of formulae       :   55 (  67 expanded)
%              Number of leaves         :   32 (  40 expanded)
%              Depth                    :    9
%              Number of atoms          :   98 ( 158 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_waybel_0 > r1_waybel_0 > r1_orders_2 > r2_hidden > r1_tarski > m1_subset_1 > l1_waybel_0 > v7_waybel_0 > v4_orders_2 > v2_struct_0 > l1_struct_0 > k2_waybel_0 > k6_subset_1 > k4_xboole_0 > #nlpp > u1_struct_0 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_waybel_0,type,(
    r1_waybel_0: ( $i * $i * $i ) > $o )).

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

tff(f_98,negated_conjecture,(
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

tff(f_29,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_34,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_80,axiom,(
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

tff(f_32,axiom,(
    ! [A] :
    ? [B] : m1_subset_1(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_63,axiom,(
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
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_38,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_34,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_36,plain,(
    l1_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_28,plain,(
    l1_waybel_0('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_4,plain,(
    ! [A_2] : k4_xboole_0(A_2,k1_xboole_0) = A_2 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_8,plain,(
    ! [A_5,B_6] : k6_subset_1(A_5,B_6) = k4_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_24,plain,(
    ! [A_62,B_66,C_68] :
      ( r2_waybel_0(A_62,B_66,C_68)
      | r1_waybel_0(A_62,B_66,k6_subset_1(u1_struct_0(A_62),C_68))
      | ~ l1_waybel_0(B_66,A_62)
      | v2_struct_0(B_66)
      | ~ l1_struct_0(A_62)
      | v2_struct_0(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_63,plain,(
    ! [A_80,B_81,C_82] :
      ( r2_waybel_0(A_80,B_81,C_82)
      | r1_waybel_0(A_80,B_81,k4_xboole_0(u1_struct_0(A_80),C_82))
      | ~ l1_waybel_0(B_81,A_80)
      | v2_struct_0(B_81)
      | ~ l1_struct_0(A_80)
      | v2_struct_0(A_80) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_24])).

tff(c_68,plain,(
    ! [A_83,B_84] :
      ( r2_waybel_0(A_83,B_84,k1_xboole_0)
      | r1_waybel_0(A_83,B_84,u1_struct_0(A_83))
      | ~ l1_waybel_0(B_84,A_83)
      | v2_struct_0(B_84)
      | ~ l1_struct_0(A_83)
      | v2_struct_0(A_83) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_63])).

tff(c_26,plain,(
    ~ r1_waybel_0('#skF_4','#skF_5',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_71,plain,
    ( r2_waybel_0('#skF_4','#skF_5',k1_xboole_0)
    | ~ l1_waybel_0('#skF_5','#skF_4')
    | v2_struct_0('#skF_5')
    | ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_26])).

tff(c_74,plain,
    ( r2_waybel_0('#skF_4','#skF_5',k1_xboole_0)
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_28,c_71])).

tff(c_75,plain,(
    r2_waybel_0('#skF_4','#skF_5',k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_34,c_74])).

tff(c_6,plain,(
    ! [A_3] : m1_subset_1('#skF_1'(A_3),A_3) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_92,plain,(
    ! [A_98,B_99,C_100,D_101] :
      ( r2_hidden(k2_waybel_0(A_98,B_99,'#skF_3'(A_98,B_99,C_100,D_101)),C_100)
      | ~ m1_subset_1(D_101,u1_struct_0(B_99))
      | ~ r2_waybel_0(A_98,B_99,C_100)
      | ~ l1_waybel_0(B_99,A_98)
      | v2_struct_0(B_99)
      | ~ l1_struct_0(A_98)
      | v2_struct_0(A_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_10,plain,(
    ! [B_8,A_7] :
      ( ~ r1_tarski(B_8,A_7)
      | ~ r2_hidden(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_97,plain,(
    ! [C_102,A_103,B_104,D_105] :
      ( ~ r1_tarski(C_102,k2_waybel_0(A_103,B_104,'#skF_3'(A_103,B_104,C_102,D_105)))
      | ~ m1_subset_1(D_105,u1_struct_0(B_104))
      | ~ r2_waybel_0(A_103,B_104,C_102)
      | ~ l1_waybel_0(B_104,A_103)
      | v2_struct_0(B_104)
      | ~ l1_struct_0(A_103)
      | v2_struct_0(A_103) ) ),
    inference(resolution,[status(thm)],[c_92,c_10])).

tff(c_103,plain,(
    ! [D_106,B_107,A_108] :
      ( ~ m1_subset_1(D_106,u1_struct_0(B_107))
      | ~ r2_waybel_0(A_108,B_107,k1_xboole_0)
      | ~ l1_waybel_0(B_107,A_108)
      | v2_struct_0(B_107)
      | ~ l1_struct_0(A_108)
      | v2_struct_0(A_108) ) ),
    inference(resolution,[status(thm)],[c_2,c_97])).

tff(c_113,plain,(
    ! [A_109,B_110] :
      ( ~ r2_waybel_0(A_109,B_110,k1_xboole_0)
      | ~ l1_waybel_0(B_110,A_109)
      | v2_struct_0(B_110)
      | ~ l1_struct_0(A_109)
      | v2_struct_0(A_109) ) ),
    inference(resolution,[status(thm)],[c_6,c_103])).

tff(c_116,plain,
    ( ~ l1_waybel_0('#skF_5','#skF_4')
    | v2_struct_0('#skF_5')
    | ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_75,c_113])).

tff(c_119,plain,
    ( v2_struct_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_28,c_116])).

tff(c_121,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_34,c_119])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:49:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.50/1.66  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.59/1.67  
% 2.59/1.67  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.59/1.67  %$ r2_waybel_0 > r1_waybel_0 > r1_orders_2 > r2_hidden > r1_tarski > m1_subset_1 > l1_waybel_0 > v7_waybel_0 > v4_orders_2 > v2_struct_0 > l1_struct_0 > k2_waybel_0 > k6_subset_1 > k4_xboole_0 > #nlpp > u1_struct_0 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3
% 2.59/1.67  
% 2.59/1.67  %Foreground sorts:
% 2.59/1.67  
% 2.59/1.67  
% 2.59/1.67  %Background operators:
% 2.59/1.67  
% 2.59/1.67  
% 2.59/1.67  %Foreground operators:
% 2.59/1.67  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.59/1.67  tff(r2_waybel_0, type, r2_waybel_0: ($i * $i * $i) > $o).
% 2.59/1.67  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.59/1.67  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.59/1.67  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.59/1.67  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.59/1.67  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 2.59/1.67  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.59/1.67  tff(k2_waybel_0, type, k2_waybel_0: ($i * $i * $i) > $i).
% 2.59/1.67  tff(v7_waybel_0, type, v7_waybel_0: $i > $o).
% 2.59/1.67  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.59/1.67  tff('#skF_5', type, '#skF_5': $i).
% 2.59/1.67  tff(r1_waybel_0, type, r1_waybel_0: ($i * $i * $i) > $o).
% 2.59/1.67  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 2.59/1.67  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.59/1.67  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.59/1.67  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.59/1.67  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.59/1.67  tff(l1_waybel_0, type, l1_waybel_0: ($i * $i) > $o).
% 2.59/1.67  tff('#skF_4', type, '#skF_4': $i).
% 2.59/1.67  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.59/1.67  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 2.59/1.67  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.59/1.67  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.59/1.67  
% 2.59/1.69  tff(f_98, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => r1_waybel_0(A, B, u1_struct_0(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_yellow_6)).
% 2.59/1.69  tff(f_29, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 2.59/1.69  tff(f_34, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 2.59/1.69  tff(f_80, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((~v2_struct_0(B) & l1_waybel_0(B, A)) => (![C]: (r2_waybel_0(A, B, C) <=> ~r1_waybel_0(A, B, k6_subset_1(u1_struct_0(A), C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_waybel_0)).
% 2.59/1.69  tff(f_32, axiom, (![A]: (?[B]: m1_subset_1(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', existence_m1_subset_1)).
% 2.59/1.69  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.59/1.69  tff(f_63, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((~v2_struct_0(B) & l1_waybel_0(B, A)) => (![C]: (r2_waybel_0(A, B, C) <=> (![D]: (m1_subset_1(D, u1_struct_0(B)) => (?[E]: ((m1_subset_1(E, u1_struct_0(B)) & r1_orders_2(B, D, E)) & r2_hidden(k2_waybel_0(A, B, E), C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d12_waybel_0)).
% 2.59/1.69  tff(f_39, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 2.59/1.69  tff(c_38, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.59/1.69  tff(c_34, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.59/1.69  tff(c_36, plain, (l1_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.59/1.69  tff(c_28, plain, (l1_waybel_0('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.59/1.69  tff(c_4, plain, (![A_2]: (k4_xboole_0(A_2, k1_xboole_0)=A_2)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.59/1.69  tff(c_8, plain, (![A_5, B_6]: (k6_subset_1(A_5, B_6)=k4_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.59/1.69  tff(c_24, plain, (![A_62, B_66, C_68]: (r2_waybel_0(A_62, B_66, C_68) | r1_waybel_0(A_62, B_66, k6_subset_1(u1_struct_0(A_62), C_68)) | ~l1_waybel_0(B_66, A_62) | v2_struct_0(B_66) | ~l1_struct_0(A_62) | v2_struct_0(A_62))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.59/1.69  tff(c_63, plain, (![A_80, B_81, C_82]: (r2_waybel_0(A_80, B_81, C_82) | r1_waybel_0(A_80, B_81, k4_xboole_0(u1_struct_0(A_80), C_82)) | ~l1_waybel_0(B_81, A_80) | v2_struct_0(B_81) | ~l1_struct_0(A_80) | v2_struct_0(A_80))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_24])).
% 2.59/1.69  tff(c_68, plain, (![A_83, B_84]: (r2_waybel_0(A_83, B_84, k1_xboole_0) | r1_waybel_0(A_83, B_84, u1_struct_0(A_83)) | ~l1_waybel_0(B_84, A_83) | v2_struct_0(B_84) | ~l1_struct_0(A_83) | v2_struct_0(A_83))), inference(superposition, [status(thm), theory('equality')], [c_4, c_63])).
% 2.59/1.69  tff(c_26, plain, (~r1_waybel_0('#skF_4', '#skF_5', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.59/1.69  tff(c_71, plain, (r2_waybel_0('#skF_4', '#skF_5', k1_xboole_0) | ~l1_waybel_0('#skF_5', '#skF_4') | v2_struct_0('#skF_5') | ~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_68, c_26])).
% 2.59/1.69  tff(c_74, plain, (r2_waybel_0('#skF_4', '#skF_5', k1_xboole_0) | v2_struct_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_28, c_71])).
% 2.59/1.69  tff(c_75, plain, (r2_waybel_0('#skF_4', '#skF_5', k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_38, c_34, c_74])).
% 2.59/1.69  tff(c_6, plain, (![A_3]: (m1_subset_1('#skF_1'(A_3), A_3))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.59/1.69  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.59/1.69  tff(c_92, plain, (![A_98, B_99, C_100, D_101]: (r2_hidden(k2_waybel_0(A_98, B_99, '#skF_3'(A_98, B_99, C_100, D_101)), C_100) | ~m1_subset_1(D_101, u1_struct_0(B_99)) | ~r2_waybel_0(A_98, B_99, C_100) | ~l1_waybel_0(B_99, A_98) | v2_struct_0(B_99) | ~l1_struct_0(A_98) | v2_struct_0(A_98))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.59/1.69  tff(c_10, plain, (![B_8, A_7]: (~r1_tarski(B_8, A_7) | ~r2_hidden(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.59/1.69  tff(c_97, plain, (![C_102, A_103, B_104, D_105]: (~r1_tarski(C_102, k2_waybel_0(A_103, B_104, '#skF_3'(A_103, B_104, C_102, D_105))) | ~m1_subset_1(D_105, u1_struct_0(B_104)) | ~r2_waybel_0(A_103, B_104, C_102) | ~l1_waybel_0(B_104, A_103) | v2_struct_0(B_104) | ~l1_struct_0(A_103) | v2_struct_0(A_103))), inference(resolution, [status(thm)], [c_92, c_10])).
% 2.59/1.69  tff(c_103, plain, (![D_106, B_107, A_108]: (~m1_subset_1(D_106, u1_struct_0(B_107)) | ~r2_waybel_0(A_108, B_107, k1_xboole_0) | ~l1_waybel_0(B_107, A_108) | v2_struct_0(B_107) | ~l1_struct_0(A_108) | v2_struct_0(A_108))), inference(resolution, [status(thm)], [c_2, c_97])).
% 2.59/1.69  tff(c_113, plain, (![A_109, B_110]: (~r2_waybel_0(A_109, B_110, k1_xboole_0) | ~l1_waybel_0(B_110, A_109) | v2_struct_0(B_110) | ~l1_struct_0(A_109) | v2_struct_0(A_109))), inference(resolution, [status(thm)], [c_6, c_103])).
% 2.59/1.69  tff(c_116, plain, (~l1_waybel_0('#skF_5', '#skF_4') | v2_struct_0('#skF_5') | ~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_75, c_113])).
% 2.59/1.69  tff(c_119, plain, (v2_struct_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_28, c_116])).
% 2.59/1.69  tff(c_121, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_34, c_119])).
% 2.59/1.69  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.59/1.69  
% 2.59/1.69  Inference rules
% 2.59/1.69  ----------------------
% 2.59/1.69  #Ref     : 0
% 2.59/1.69  #Sup     : 15
% 2.59/1.69  #Fact    : 0
% 2.59/1.69  #Define  : 0
% 2.59/1.69  #Split   : 0
% 2.59/1.69  #Chain   : 0
% 2.59/1.69  #Close   : 0
% 2.59/1.69  
% 2.59/1.69  Ordering : KBO
% 2.59/1.70  
% 2.59/1.70  Simplification rules
% 2.59/1.70  ----------------------
% 2.59/1.70  #Subsume      : 3
% 2.59/1.70  #Demod        : 6
% 2.59/1.70  #Tautology    : 6
% 2.59/1.70  #SimpNegUnit  : 2
% 2.59/1.70  #BackRed      : 0
% 2.59/1.70  
% 2.59/1.70  #Partial instantiations: 0
% 2.59/1.70  #Strategies tried      : 1
% 2.59/1.70  
% 2.59/1.70  Timing (in seconds)
% 2.59/1.70  ----------------------
% 2.59/1.70  Preprocessing        : 0.50
% 2.59/1.70  Parsing              : 0.25
% 2.59/1.70  CNF conversion       : 0.04
% 2.59/1.70  Main loop            : 0.27
% 2.59/1.70  Inferencing          : 0.11
% 2.59/1.70  Reduction            : 0.08
% 2.59/1.70  Demodulation         : 0.06
% 2.59/1.70  BG Simplification    : 0.02
% 2.59/1.70  Subsumption          : 0.04
% 2.59/1.70  Abstraction          : 0.02
% 2.59/1.70  MUC search           : 0.00
% 2.59/1.70  Cooper               : 0.00
% 2.59/1.70  Total                : 0.82
% 2.59/1.70  Index Insertion      : 0.00
% 2.59/1.70  Index Deletion       : 0.00
% 2.59/1.70  Index Matching       : 0.00
% 2.59/1.70  BG Taut test         : 0.00
%------------------------------------------------------------------------------
