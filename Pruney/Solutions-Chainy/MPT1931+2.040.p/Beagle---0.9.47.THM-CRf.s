%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:51 EST 2020

% Result     : Theorem 2.10s
% Output     : CNFRefutation 2.10s
% Verified   : 
% Statistics : Number of formulae       :   60 (  80 expanded)
%              Number of leaves         :   32 (  45 expanded)
%              Depth                    :   12
%              Number of atoms          :  131 ( 229 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_waybel_0 > r1_waybel_0 > r1_orders_2 > r2_hidden > r1_tarski > m1_subset_1 > l1_waybel_0 > v7_waybel_0 > v4_orders_2 > v2_struct_0 > l1_struct_0 > k2_waybel_0 > o_2_2_yellow_6 > k6_subset_1 > k4_xboole_0 > #nlpp > u1_struct_0 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(o_2_2_yellow_6,type,(
    o_2_2_yellow_6: ( $i * $i ) > $i )).

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_waybel_0,type,(
    r1_waybel_0: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_111,negated_conjecture,(
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
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_31,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_77,axiom,(
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

tff(f_93,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A)
        & ~ v2_struct_0(B)
        & v4_orders_2(B)
        & v7_waybel_0(B)
        & l1_waybel_0(B,A) )
     => m1_subset_1(o_2_2_yellow_6(A,B),u1_struct_0(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_o_2_2_yellow_6)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_60,axiom,(
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

tff(f_36,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_38,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_36,plain,(
    l1_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_28,plain,(
    l1_waybel_0('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_34,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_32,plain,(
    v4_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_30,plain,(
    v7_waybel_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_4,plain,(
    ! [A_2] : k4_xboole_0(A_2,k1_xboole_0) = A_2 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6,plain,(
    ! [A_3,B_4] : k6_subset_1(A_3,B_4) = k4_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_22,plain,(
    ! [A_60,B_64,C_66] :
      ( r2_waybel_0(A_60,B_64,C_66)
      | r1_waybel_0(A_60,B_64,k6_subset_1(u1_struct_0(A_60),C_66))
      | ~ l1_waybel_0(B_64,A_60)
      | v2_struct_0(B_64)
      | ~ l1_struct_0(A_60)
      | v2_struct_0(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_63,plain,(
    ! [A_81,B_82,C_83] :
      ( r2_waybel_0(A_81,B_82,C_83)
      | r1_waybel_0(A_81,B_82,k4_xboole_0(u1_struct_0(A_81),C_83))
      | ~ l1_waybel_0(B_82,A_81)
      | v2_struct_0(B_82)
      | ~ l1_struct_0(A_81)
      | v2_struct_0(A_81) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_22])).

tff(c_68,plain,(
    ! [A_84,B_85] :
      ( r2_waybel_0(A_84,B_85,k1_xboole_0)
      | r1_waybel_0(A_84,B_85,u1_struct_0(A_84))
      | ~ l1_waybel_0(B_85,A_84)
      | v2_struct_0(B_85)
      | ~ l1_struct_0(A_84)
      | v2_struct_0(A_84) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_63])).

tff(c_26,plain,(
    ~ r1_waybel_0('#skF_3','#skF_4',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_71,plain,
    ( r2_waybel_0('#skF_3','#skF_4',k1_xboole_0)
    | ~ l1_waybel_0('#skF_4','#skF_3')
    | v2_struct_0('#skF_4')
    | ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_26])).

tff(c_74,plain,
    ( r2_waybel_0('#skF_3','#skF_4',k1_xboole_0)
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_28,c_71])).

tff(c_75,plain,(
    r2_waybel_0('#skF_3','#skF_4',k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_34,c_74])).

tff(c_24,plain,(
    ! [A_67,B_68] :
      ( m1_subset_1(o_2_2_yellow_6(A_67,B_68),u1_struct_0(B_68))
      | ~ l1_waybel_0(B_68,A_67)
      | ~ v7_waybel_0(B_68)
      | ~ v4_orders_2(B_68)
      | v2_struct_0(B_68)
      | ~ l1_struct_0(A_67)
      | v2_struct_0(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_92,plain,(
    ! [A_99,B_100,C_101,D_102] :
      ( r2_hidden(k2_waybel_0(A_99,B_100,'#skF_2'(A_99,B_100,C_101,D_102)),C_101)
      | ~ m1_subset_1(D_102,u1_struct_0(B_100))
      | ~ r2_waybel_0(A_99,B_100,C_101)
      | ~ l1_waybel_0(B_100,A_99)
      | v2_struct_0(B_100)
      | ~ l1_struct_0(A_99)
      | v2_struct_0(A_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_8,plain,(
    ! [B_6,A_5] :
      ( ~ r1_tarski(B_6,A_5)
      | ~ r2_hidden(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_97,plain,(
    ! [C_103,A_104,B_105,D_106] :
      ( ~ r1_tarski(C_103,k2_waybel_0(A_104,B_105,'#skF_2'(A_104,B_105,C_103,D_106)))
      | ~ m1_subset_1(D_106,u1_struct_0(B_105))
      | ~ r2_waybel_0(A_104,B_105,C_103)
      | ~ l1_waybel_0(B_105,A_104)
      | v2_struct_0(B_105)
      | ~ l1_struct_0(A_104)
      | v2_struct_0(A_104) ) ),
    inference(resolution,[status(thm)],[c_92,c_8])).

tff(c_103,plain,(
    ! [D_107,B_108,A_109] :
      ( ~ m1_subset_1(D_107,u1_struct_0(B_108))
      | ~ r2_waybel_0(A_109,B_108,k1_xboole_0)
      | ~ l1_waybel_0(B_108,A_109)
      | v2_struct_0(B_108)
      | ~ l1_struct_0(A_109)
      | v2_struct_0(A_109) ) ),
    inference(resolution,[status(thm)],[c_2,c_97])).

tff(c_132,plain,(
    ! [A_120,B_121,A_122] :
      ( ~ r2_waybel_0(A_120,B_121,k1_xboole_0)
      | ~ l1_waybel_0(B_121,A_120)
      | ~ l1_struct_0(A_120)
      | v2_struct_0(A_120)
      | ~ l1_waybel_0(B_121,A_122)
      | ~ v7_waybel_0(B_121)
      | ~ v4_orders_2(B_121)
      | v2_struct_0(B_121)
      | ~ l1_struct_0(A_122)
      | v2_struct_0(A_122) ) ),
    inference(resolution,[status(thm)],[c_24,c_103])).

tff(c_137,plain,(
    ! [A_122] :
      ( ~ l1_waybel_0('#skF_4','#skF_3')
      | ~ l1_struct_0('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ l1_waybel_0('#skF_4',A_122)
      | ~ v7_waybel_0('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ l1_struct_0(A_122)
      | v2_struct_0(A_122) ) ),
    inference(resolution,[status(thm)],[c_75,c_132])).

tff(c_144,plain,(
    ! [A_122] :
      ( v2_struct_0('#skF_3')
      | ~ l1_waybel_0('#skF_4',A_122)
      | v2_struct_0('#skF_4')
      | ~ l1_struct_0(A_122)
      | v2_struct_0(A_122) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_36,c_28,c_137])).

tff(c_146,plain,(
    ! [A_123] :
      ( ~ l1_waybel_0('#skF_4',A_123)
      | ~ l1_struct_0(A_123)
      | v2_struct_0(A_123) ) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_38,c_144])).

tff(c_149,plain,
    ( ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_146])).

tff(c_152,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_149])).

tff(c_154,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_152])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n011.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:44:42 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.10/1.20  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.10/1.21  
% 2.10/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.10/1.21  %$ r2_waybel_0 > r1_waybel_0 > r1_orders_2 > r2_hidden > r1_tarski > m1_subset_1 > l1_waybel_0 > v7_waybel_0 > v4_orders_2 > v2_struct_0 > l1_struct_0 > k2_waybel_0 > o_2_2_yellow_6 > k6_subset_1 > k4_xboole_0 > #nlpp > u1_struct_0 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 2.10/1.21  
% 2.10/1.21  %Foreground sorts:
% 2.10/1.21  
% 2.10/1.21  
% 2.10/1.21  %Background operators:
% 2.10/1.21  
% 2.10/1.21  
% 2.10/1.21  %Foreground operators:
% 2.10/1.21  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.10/1.21  tff(o_2_2_yellow_6, type, o_2_2_yellow_6: ($i * $i) > $i).
% 2.10/1.21  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.10/1.21  tff(r2_waybel_0, type, r2_waybel_0: ($i * $i * $i) > $o).
% 2.10/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.10/1.21  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.10/1.21  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.10/1.21  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 2.10/1.21  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.10/1.21  tff(k2_waybel_0, type, k2_waybel_0: ($i * $i * $i) > $i).
% 2.10/1.21  tff(v7_waybel_0, type, v7_waybel_0: $i > $o).
% 2.10/1.21  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.10/1.21  tff(r1_waybel_0, type, r1_waybel_0: ($i * $i * $i) > $o).
% 2.10/1.21  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.10/1.21  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 2.10/1.21  tff('#skF_3', type, '#skF_3': $i).
% 2.10/1.21  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.10/1.21  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.10/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.10/1.21  tff(l1_waybel_0, type, l1_waybel_0: ($i * $i) > $o).
% 2.10/1.21  tff('#skF_4', type, '#skF_4': $i).
% 2.10/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.10/1.21  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.10/1.21  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.10/1.21  
% 2.10/1.22  tff(f_111, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => r1_waybel_0(A, B, u1_struct_0(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_yellow_6)).
% 2.10/1.22  tff(f_29, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 2.10/1.22  tff(f_31, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 2.10/1.22  tff(f_77, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((~v2_struct_0(B) & l1_waybel_0(B, A)) => (![C]: (r2_waybel_0(A, B, C) <=> ~r1_waybel_0(A, B, k6_subset_1(u1_struct_0(A), C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_waybel_0)).
% 2.10/1.22  tff(f_93, axiom, (![A, B]: ((((((~v2_struct_0(A) & l1_struct_0(A)) & ~v2_struct_0(B)) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => m1_subset_1(o_2_2_yellow_6(A, B), u1_struct_0(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_o_2_2_yellow_6)).
% 2.10/1.22  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.10/1.22  tff(f_60, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((~v2_struct_0(B) & l1_waybel_0(B, A)) => (![C]: (r2_waybel_0(A, B, C) <=> (![D]: (m1_subset_1(D, u1_struct_0(B)) => (?[E]: ((m1_subset_1(E, u1_struct_0(B)) & r1_orders_2(B, D, E)) & r2_hidden(k2_waybel_0(A, B, E), C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_waybel_0)).
% 2.10/1.22  tff(f_36, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 2.10/1.22  tff(c_38, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.10/1.22  tff(c_36, plain, (l1_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.10/1.22  tff(c_28, plain, (l1_waybel_0('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.10/1.22  tff(c_34, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.10/1.22  tff(c_32, plain, (v4_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.10/1.22  tff(c_30, plain, (v7_waybel_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.10/1.22  tff(c_4, plain, (![A_2]: (k4_xboole_0(A_2, k1_xboole_0)=A_2)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.10/1.22  tff(c_6, plain, (![A_3, B_4]: (k6_subset_1(A_3, B_4)=k4_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.10/1.22  tff(c_22, plain, (![A_60, B_64, C_66]: (r2_waybel_0(A_60, B_64, C_66) | r1_waybel_0(A_60, B_64, k6_subset_1(u1_struct_0(A_60), C_66)) | ~l1_waybel_0(B_64, A_60) | v2_struct_0(B_64) | ~l1_struct_0(A_60) | v2_struct_0(A_60))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.10/1.22  tff(c_63, plain, (![A_81, B_82, C_83]: (r2_waybel_0(A_81, B_82, C_83) | r1_waybel_0(A_81, B_82, k4_xboole_0(u1_struct_0(A_81), C_83)) | ~l1_waybel_0(B_82, A_81) | v2_struct_0(B_82) | ~l1_struct_0(A_81) | v2_struct_0(A_81))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_22])).
% 2.10/1.22  tff(c_68, plain, (![A_84, B_85]: (r2_waybel_0(A_84, B_85, k1_xboole_0) | r1_waybel_0(A_84, B_85, u1_struct_0(A_84)) | ~l1_waybel_0(B_85, A_84) | v2_struct_0(B_85) | ~l1_struct_0(A_84) | v2_struct_0(A_84))), inference(superposition, [status(thm), theory('equality')], [c_4, c_63])).
% 2.10/1.22  tff(c_26, plain, (~r1_waybel_0('#skF_3', '#skF_4', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.10/1.22  tff(c_71, plain, (r2_waybel_0('#skF_3', '#skF_4', k1_xboole_0) | ~l1_waybel_0('#skF_4', '#skF_3') | v2_struct_0('#skF_4') | ~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_68, c_26])).
% 2.10/1.22  tff(c_74, plain, (r2_waybel_0('#skF_3', '#skF_4', k1_xboole_0) | v2_struct_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_28, c_71])).
% 2.10/1.22  tff(c_75, plain, (r2_waybel_0('#skF_3', '#skF_4', k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_38, c_34, c_74])).
% 2.10/1.22  tff(c_24, plain, (![A_67, B_68]: (m1_subset_1(o_2_2_yellow_6(A_67, B_68), u1_struct_0(B_68)) | ~l1_waybel_0(B_68, A_67) | ~v7_waybel_0(B_68) | ~v4_orders_2(B_68) | v2_struct_0(B_68) | ~l1_struct_0(A_67) | v2_struct_0(A_67))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.10/1.22  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.10/1.22  tff(c_92, plain, (![A_99, B_100, C_101, D_102]: (r2_hidden(k2_waybel_0(A_99, B_100, '#skF_2'(A_99, B_100, C_101, D_102)), C_101) | ~m1_subset_1(D_102, u1_struct_0(B_100)) | ~r2_waybel_0(A_99, B_100, C_101) | ~l1_waybel_0(B_100, A_99) | v2_struct_0(B_100) | ~l1_struct_0(A_99) | v2_struct_0(A_99))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.10/1.22  tff(c_8, plain, (![B_6, A_5]: (~r1_tarski(B_6, A_5) | ~r2_hidden(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.10/1.22  tff(c_97, plain, (![C_103, A_104, B_105, D_106]: (~r1_tarski(C_103, k2_waybel_0(A_104, B_105, '#skF_2'(A_104, B_105, C_103, D_106))) | ~m1_subset_1(D_106, u1_struct_0(B_105)) | ~r2_waybel_0(A_104, B_105, C_103) | ~l1_waybel_0(B_105, A_104) | v2_struct_0(B_105) | ~l1_struct_0(A_104) | v2_struct_0(A_104))), inference(resolution, [status(thm)], [c_92, c_8])).
% 2.10/1.22  tff(c_103, plain, (![D_107, B_108, A_109]: (~m1_subset_1(D_107, u1_struct_0(B_108)) | ~r2_waybel_0(A_109, B_108, k1_xboole_0) | ~l1_waybel_0(B_108, A_109) | v2_struct_0(B_108) | ~l1_struct_0(A_109) | v2_struct_0(A_109))), inference(resolution, [status(thm)], [c_2, c_97])).
% 2.10/1.22  tff(c_132, plain, (![A_120, B_121, A_122]: (~r2_waybel_0(A_120, B_121, k1_xboole_0) | ~l1_waybel_0(B_121, A_120) | ~l1_struct_0(A_120) | v2_struct_0(A_120) | ~l1_waybel_0(B_121, A_122) | ~v7_waybel_0(B_121) | ~v4_orders_2(B_121) | v2_struct_0(B_121) | ~l1_struct_0(A_122) | v2_struct_0(A_122))), inference(resolution, [status(thm)], [c_24, c_103])).
% 2.10/1.22  tff(c_137, plain, (![A_122]: (~l1_waybel_0('#skF_4', '#skF_3') | ~l1_struct_0('#skF_3') | v2_struct_0('#skF_3') | ~l1_waybel_0('#skF_4', A_122) | ~v7_waybel_0('#skF_4') | ~v4_orders_2('#skF_4') | v2_struct_0('#skF_4') | ~l1_struct_0(A_122) | v2_struct_0(A_122))), inference(resolution, [status(thm)], [c_75, c_132])).
% 2.10/1.22  tff(c_144, plain, (![A_122]: (v2_struct_0('#skF_3') | ~l1_waybel_0('#skF_4', A_122) | v2_struct_0('#skF_4') | ~l1_struct_0(A_122) | v2_struct_0(A_122))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_36, c_28, c_137])).
% 2.10/1.22  tff(c_146, plain, (![A_123]: (~l1_waybel_0('#skF_4', A_123) | ~l1_struct_0(A_123) | v2_struct_0(A_123))), inference(negUnitSimplification, [status(thm)], [c_34, c_38, c_144])).
% 2.10/1.22  tff(c_149, plain, (~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_28, c_146])).
% 2.10/1.22  tff(c_152, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_149])).
% 2.10/1.22  tff(c_154, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_152])).
% 2.10/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.10/1.22  
% 2.10/1.22  Inference rules
% 2.10/1.22  ----------------------
% 2.10/1.22  #Ref     : 0
% 2.10/1.22  #Sup     : 20
% 2.10/1.22  #Fact    : 0
% 2.10/1.22  #Define  : 0
% 2.10/1.22  #Split   : 0
% 2.10/1.22  #Chain   : 0
% 2.10/1.22  #Close   : 0
% 2.10/1.22  
% 2.10/1.22  Ordering : KBO
% 2.10/1.22  
% 2.10/1.22  Simplification rules
% 2.10/1.22  ----------------------
% 2.10/1.22  #Subsume      : 3
% 2.10/1.22  #Demod        : 13
% 2.10/1.22  #Tautology    : 6
% 2.10/1.22  #SimpNegUnit  : 6
% 2.10/1.22  #BackRed      : 0
% 2.10/1.22  
% 2.10/1.22  #Partial instantiations: 0
% 2.10/1.22  #Strategies tried      : 1
% 2.10/1.22  
% 2.10/1.22  Timing (in seconds)
% 2.10/1.22  ----------------------
% 2.10/1.23  Preprocessing        : 0.30
% 2.10/1.23  Parsing              : 0.16
% 2.10/1.23  CNF conversion       : 0.03
% 2.10/1.23  Main loop            : 0.16
% 2.10/1.23  Inferencing          : 0.07
% 2.10/1.23  Reduction            : 0.04
% 2.10/1.23  Demodulation         : 0.03
% 2.10/1.23  BG Simplification    : 0.01
% 2.10/1.23  Subsumption          : 0.02
% 2.10/1.23  Abstraction          : 0.01
% 2.10/1.23  MUC search           : 0.00
% 2.10/1.23  Cooper               : 0.00
% 2.10/1.23  Total                : 0.50
% 2.10/1.23  Index Insertion      : 0.00
% 2.10/1.23  Index Deletion       : 0.00
% 2.10/1.23  Index Matching       : 0.00
% 2.10/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
