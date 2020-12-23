%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:53 EST 2020

% Result     : Theorem 2.04s
% Output     : CNFRefutation 2.04s
% Verified   : 
% Statistics : Number of formulae       :   59 (  71 expanded)
%              Number of leaves         :   34 (  42 expanded)
%              Depth                    :    9
%              Number of atoms          :  103 ( 163 expanded)
%              Number of equality atoms :    5 (   5 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_waybel_0 > r1_waybel_0 > r1_orders_2 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > l1_waybel_0 > v7_waybel_0 > v4_orders_2 > v2_struct_0 > l1_struct_0 > k2_waybel_0 > k6_subset_1 > k4_xboole_0 > #nlpp > u1_struct_0 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3

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

tff(f_102,negated_conjecture,(
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

tff(f_29,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_38,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_84,axiom,(
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

tff(f_36,axiom,(
    ! [A] :
    ? [B] : m1_subset_1(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_67,axiom,(
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

tff(f_43,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_42,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_38,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_40,plain,(
    l1_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_32,plain,(
    l1_waybel_0('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_4,plain,(
    ! [A_2] : r1_xboole_0(A_2,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_59,plain,(
    ! [A_81,B_82] :
      ( k4_xboole_0(A_81,B_82) = A_81
      | ~ r1_xboole_0(A_81,B_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_67,plain,(
    ! [A_2] : k4_xboole_0(A_2,k1_xboole_0) = A_2 ),
    inference(resolution,[status(thm)],[c_4,c_59])).

tff(c_12,plain,(
    ! [A_7,B_8] : k6_subset_1(A_7,B_8) = k4_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_28,plain,(
    ! [A_64,B_68,C_70] :
      ( r2_waybel_0(A_64,B_68,C_70)
      | r1_waybel_0(A_64,B_68,k6_subset_1(u1_struct_0(A_64),C_70))
      | ~ l1_waybel_0(B_68,A_64)
      | v2_struct_0(B_68)
      | ~ l1_struct_0(A_64)
      | v2_struct_0(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_84,plain,(
    ! [A_92,B_93,C_94] :
      ( r2_waybel_0(A_92,B_93,C_94)
      | r1_waybel_0(A_92,B_93,k4_xboole_0(u1_struct_0(A_92),C_94))
      | ~ l1_waybel_0(B_93,A_92)
      | v2_struct_0(B_93)
      | ~ l1_struct_0(A_92)
      | v2_struct_0(A_92) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_28])).

tff(c_94,plain,(
    ! [A_99,B_100] :
      ( r2_waybel_0(A_99,B_100,k1_xboole_0)
      | r1_waybel_0(A_99,B_100,u1_struct_0(A_99))
      | ~ l1_waybel_0(B_100,A_99)
      | v2_struct_0(B_100)
      | ~ l1_struct_0(A_99)
      | v2_struct_0(A_99) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_67,c_84])).

tff(c_30,plain,(
    ~ r1_waybel_0('#skF_4','#skF_5',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_100,plain,
    ( r2_waybel_0('#skF_4','#skF_5',k1_xboole_0)
    | ~ l1_waybel_0('#skF_5','#skF_4')
    | v2_struct_0('#skF_5')
    | ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_94,c_30])).

tff(c_104,plain,
    ( r2_waybel_0('#skF_4','#skF_5',k1_xboole_0)
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_32,c_100])).

tff(c_105,plain,(
    r2_waybel_0('#skF_4','#skF_5',k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_38,c_104])).

tff(c_10,plain,(
    ! [A_5] : m1_subset_1('#skF_1'(A_5),A_5) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_107,plain,(
    ! [A_105,B_106,C_107,D_108] :
      ( r2_hidden(k2_waybel_0(A_105,B_106,'#skF_3'(A_105,B_106,C_107,D_108)),C_107)
      | ~ m1_subset_1(D_108,u1_struct_0(B_106))
      | ~ r2_waybel_0(A_105,B_106,C_107)
      | ~ l1_waybel_0(B_106,A_105)
      | v2_struct_0(B_106)
      | ~ l1_struct_0(A_105)
      | v2_struct_0(A_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_14,plain,(
    ! [B_10,A_9] :
      ( ~ r1_tarski(B_10,A_9)
      | ~ r2_hidden(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_112,plain,(
    ! [C_109,A_110,B_111,D_112] :
      ( ~ r1_tarski(C_109,k2_waybel_0(A_110,B_111,'#skF_3'(A_110,B_111,C_109,D_112)))
      | ~ m1_subset_1(D_112,u1_struct_0(B_111))
      | ~ r2_waybel_0(A_110,B_111,C_109)
      | ~ l1_waybel_0(B_111,A_110)
      | v2_struct_0(B_111)
      | ~ l1_struct_0(A_110)
      | v2_struct_0(A_110) ) ),
    inference(resolution,[status(thm)],[c_107,c_14])).

tff(c_124,plain,(
    ! [D_117,B_118,A_119] :
      ( ~ m1_subset_1(D_117,u1_struct_0(B_118))
      | ~ r2_waybel_0(A_119,B_118,k1_xboole_0)
      | ~ l1_waybel_0(B_118,A_119)
      | v2_struct_0(B_118)
      | ~ l1_struct_0(A_119)
      | v2_struct_0(A_119) ) ),
    inference(resolution,[status(thm)],[c_2,c_112])).

tff(c_134,plain,(
    ! [A_120,B_121] :
      ( ~ r2_waybel_0(A_120,B_121,k1_xboole_0)
      | ~ l1_waybel_0(B_121,A_120)
      | v2_struct_0(B_121)
      | ~ l1_struct_0(A_120)
      | v2_struct_0(A_120) ) ),
    inference(resolution,[status(thm)],[c_10,c_124])).

tff(c_137,plain,
    ( ~ l1_waybel_0('#skF_5','#skF_4')
    | v2_struct_0('#skF_5')
    | ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_105,c_134])).

tff(c_140,plain,
    ( v2_struct_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_32,c_137])).

tff(c_142,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_38,c_140])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:06:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.04/1.19  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.04/1.19  
% 2.04/1.19  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.04/1.19  %$ r2_waybel_0 > r1_waybel_0 > r1_orders_2 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > l1_waybel_0 > v7_waybel_0 > v4_orders_2 > v2_struct_0 > l1_struct_0 > k2_waybel_0 > k6_subset_1 > k4_xboole_0 > #nlpp > u1_struct_0 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3
% 2.04/1.19  
% 2.04/1.19  %Foreground sorts:
% 2.04/1.19  
% 2.04/1.19  
% 2.04/1.19  %Background operators:
% 2.04/1.19  
% 2.04/1.19  
% 2.04/1.19  %Foreground operators:
% 2.04/1.19  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.04/1.19  tff(r2_waybel_0, type, r2_waybel_0: ($i * $i * $i) > $o).
% 2.04/1.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.04/1.19  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.04/1.19  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.04/1.19  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.04/1.19  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 2.04/1.19  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.04/1.19  tff(k2_waybel_0, type, k2_waybel_0: ($i * $i * $i) > $i).
% 2.04/1.19  tff(v7_waybel_0, type, v7_waybel_0: $i > $o).
% 2.04/1.19  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.04/1.19  tff('#skF_5', type, '#skF_5': $i).
% 2.04/1.19  tff(r1_waybel_0, type, r1_waybel_0: ($i * $i * $i) > $o).
% 2.04/1.19  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.04/1.20  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 2.04/1.20  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.04/1.20  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.04/1.20  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.04/1.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.04/1.20  tff(l1_waybel_0, type, l1_waybel_0: ($i * $i) > $o).
% 2.04/1.20  tff('#skF_4', type, '#skF_4': $i).
% 2.04/1.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.04/1.20  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 2.04/1.20  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.04/1.20  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.04/1.20  
% 2.04/1.21  tff(f_102, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => r1_waybel_0(A, B, u1_struct_0(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_yellow_6)).
% 2.04/1.21  tff(f_29, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.04/1.21  tff(f_33, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.04/1.21  tff(f_38, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 2.04/1.21  tff(f_84, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((~v2_struct_0(B) & l1_waybel_0(B, A)) => (![C]: (r2_waybel_0(A, B, C) <=> ~r1_waybel_0(A, B, k6_subset_1(u1_struct_0(A), C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_waybel_0)).
% 2.04/1.21  tff(f_36, axiom, (![A]: (?[B]: m1_subset_1(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', existence_m1_subset_1)).
% 2.04/1.21  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.04/1.21  tff(f_67, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((~v2_struct_0(B) & l1_waybel_0(B, A)) => (![C]: (r2_waybel_0(A, B, C) <=> (![D]: (m1_subset_1(D, u1_struct_0(B)) => (?[E]: ((m1_subset_1(E, u1_struct_0(B)) & r1_orders_2(B, D, E)) & r2_hidden(k2_waybel_0(A, B, E), C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_waybel_0)).
% 2.04/1.21  tff(f_43, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 2.04/1.21  tff(c_42, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.04/1.21  tff(c_38, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.04/1.21  tff(c_40, plain, (l1_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.04/1.21  tff(c_32, plain, (l1_waybel_0('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.04/1.21  tff(c_4, plain, (![A_2]: (r1_xboole_0(A_2, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.04/1.21  tff(c_59, plain, (![A_81, B_82]: (k4_xboole_0(A_81, B_82)=A_81 | ~r1_xboole_0(A_81, B_82))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.04/1.21  tff(c_67, plain, (![A_2]: (k4_xboole_0(A_2, k1_xboole_0)=A_2)), inference(resolution, [status(thm)], [c_4, c_59])).
% 2.04/1.21  tff(c_12, plain, (![A_7, B_8]: (k6_subset_1(A_7, B_8)=k4_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.04/1.21  tff(c_28, plain, (![A_64, B_68, C_70]: (r2_waybel_0(A_64, B_68, C_70) | r1_waybel_0(A_64, B_68, k6_subset_1(u1_struct_0(A_64), C_70)) | ~l1_waybel_0(B_68, A_64) | v2_struct_0(B_68) | ~l1_struct_0(A_64) | v2_struct_0(A_64))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.04/1.21  tff(c_84, plain, (![A_92, B_93, C_94]: (r2_waybel_0(A_92, B_93, C_94) | r1_waybel_0(A_92, B_93, k4_xboole_0(u1_struct_0(A_92), C_94)) | ~l1_waybel_0(B_93, A_92) | v2_struct_0(B_93) | ~l1_struct_0(A_92) | v2_struct_0(A_92))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_28])).
% 2.04/1.21  tff(c_94, plain, (![A_99, B_100]: (r2_waybel_0(A_99, B_100, k1_xboole_0) | r1_waybel_0(A_99, B_100, u1_struct_0(A_99)) | ~l1_waybel_0(B_100, A_99) | v2_struct_0(B_100) | ~l1_struct_0(A_99) | v2_struct_0(A_99))), inference(superposition, [status(thm), theory('equality')], [c_67, c_84])).
% 2.04/1.21  tff(c_30, plain, (~r1_waybel_0('#skF_4', '#skF_5', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.04/1.21  tff(c_100, plain, (r2_waybel_0('#skF_4', '#skF_5', k1_xboole_0) | ~l1_waybel_0('#skF_5', '#skF_4') | v2_struct_0('#skF_5') | ~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_94, c_30])).
% 2.04/1.21  tff(c_104, plain, (r2_waybel_0('#skF_4', '#skF_5', k1_xboole_0) | v2_struct_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_32, c_100])).
% 2.04/1.21  tff(c_105, plain, (r2_waybel_0('#skF_4', '#skF_5', k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_42, c_38, c_104])).
% 2.04/1.21  tff(c_10, plain, (![A_5]: (m1_subset_1('#skF_1'(A_5), A_5))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.04/1.21  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.04/1.21  tff(c_107, plain, (![A_105, B_106, C_107, D_108]: (r2_hidden(k2_waybel_0(A_105, B_106, '#skF_3'(A_105, B_106, C_107, D_108)), C_107) | ~m1_subset_1(D_108, u1_struct_0(B_106)) | ~r2_waybel_0(A_105, B_106, C_107) | ~l1_waybel_0(B_106, A_105) | v2_struct_0(B_106) | ~l1_struct_0(A_105) | v2_struct_0(A_105))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.04/1.21  tff(c_14, plain, (![B_10, A_9]: (~r1_tarski(B_10, A_9) | ~r2_hidden(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.04/1.21  tff(c_112, plain, (![C_109, A_110, B_111, D_112]: (~r1_tarski(C_109, k2_waybel_0(A_110, B_111, '#skF_3'(A_110, B_111, C_109, D_112))) | ~m1_subset_1(D_112, u1_struct_0(B_111)) | ~r2_waybel_0(A_110, B_111, C_109) | ~l1_waybel_0(B_111, A_110) | v2_struct_0(B_111) | ~l1_struct_0(A_110) | v2_struct_0(A_110))), inference(resolution, [status(thm)], [c_107, c_14])).
% 2.04/1.21  tff(c_124, plain, (![D_117, B_118, A_119]: (~m1_subset_1(D_117, u1_struct_0(B_118)) | ~r2_waybel_0(A_119, B_118, k1_xboole_0) | ~l1_waybel_0(B_118, A_119) | v2_struct_0(B_118) | ~l1_struct_0(A_119) | v2_struct_0(A_119))), inference(resolution, [status(thm)], [c_2, c_112])).
% 2.04/1.21  tff(c_134, plain, (![A_120, B_121]: (~r2_waybel_0(A_120, B_121, k1_xboole_0) | ~l1_waybel_0(B_121, A_120) | v2_struct_0(B_121) | ~l1_struct_0(A_120) | v2_struct_0(A_120))), inference(resolution, [status(thm)], [c_10, c_124])).
% 2.04/1.21  tff(c_137, plain, (~l1_waybel_0('#skF_5', '#skF_4') | v2_struct_0('#skF_5') | ~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_105, c_134])).
% 2.04/1.21  tff(c_140, plain, (v2_struct_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_32, c_137])).
% 2.04/1.21  tff(c_142, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_38, c_140])).
% 2.04/1.21  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.04/1.21  
% 2.04/1.21  Inference rules
% 2.04/1.21  ----------------------
% 2.04/1.21  #Ref     : 0
% 2.04/1.21  #Sup     : 18
% 2.04/1.21  #Fact    : 0
% 2.04/1.21  #Define  : 0
% 2.04/1.21  #Split   : 0
% 2.04/1.21  #Chain   : 0
% 2.04/1.21  #Close   : 0
% 2.04/1.21  
% 2.04/1.21  Ordering : KBO
% 2.04/1.21  
% 2.04/1.21  Simplification rules
% 2.04/1.21  ----------------------
% 2.04/1.21  #Subsume      : 3
% 2.04/1.21  #Demod        : 6
% 2.04/1.21  #Tautology    : 7
% 2.04/1.21  #SimpNegUnit  : 2
% 2.04/1.21  #BackRed      : 0
% 2.04/1.21  
% 2.04/1.21  #Partial instantiations: 0
% 2.04/1.21  #Strategies tried      : 1
% 2.04/1.21  
% 2.04/1.21  Timing (in seconds)
% 2.04/1.21  ----------------------
% 2.04/1.21  Preprocessing        : 0.30
% 2.04/1.21  Parsing              : 0.16
% 2.04/1.21  CNF conversion       : 0.03
% 2.04/1.21  Main loop            : 0.15
% 2.04/1.21  Inferencing          : 0.07
% 2.04/1.21  Reduction            : 0.04
% 2.04/1.21  Demodulation         : 0.03
% 2.04/1.21  BG Simplification    : 0.01
% 2.04/1.21  Subsumption          : 0.02
% 2.04/1.21  Abstraction          : 0.01
% 2.04/1.21  MUC search           : 0.00
% 2.04/1.21  Cooper               : 0.00
% 2.04/1.21  Total                : 0.49
% 2.04/1.21  Index Insertion      : 0.00
% 2.04/1.21  Index Deletion       : 0.00
% 2.04/1.21  Index Matching       : 0.00
% 2.04/1.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
