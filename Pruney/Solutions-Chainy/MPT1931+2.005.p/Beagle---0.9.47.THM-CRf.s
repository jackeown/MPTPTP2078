%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:47 EST 2020

% Result     : Theorem 2.07s
% Output     : CNFRefutation 2.07s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 110 expanded)
%              Number of leaves         :   30 (  52 expanded)
%              Depth                    :   13
%              Number of atoms          :  135 ( 360 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_waybel_0 > r1_orders_2 > r2_hidden > m1_subset_1 > l1_waybel_0 > v7_waybel_0 > v4_orders_2 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > k2_waybel_0 > #nlpp > u1_struct_0 > #skF_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff(k2_waybel_0,type,(
    k2_waybel_0: ( $i * $i * $i ) > $i )).

tff(v7_waybel_0,type,(
    v7_waybel_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_waybel_0,type,(
    r1_waybel_0: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(l1_waybel_0,type,(
    l1_waybel_0: ( $i * $i ) > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_116,negated_conjecture,(
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

tff(f_98,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ! [B] :
          ( l1_waybel_0(B,A)
         => l1_orders_2(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_waybel_0)).

tff(f_53,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_77,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_waybel_0)).

tff(f_91,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A)
        & ~ v2_struct_0(B)
        & l1_waybel_0(B,A)
        & m1_subset_1(C,u1_struct_0(B)) )
     => m1_subset_1(k2_waybel_0(A,B,C),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_waybel_0)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_49,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(c_40,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_38,plain,(
    l1_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_30,plain,(
    l1_waybel_0('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_54,plain,(
    ! [B_78,A_79] :
      ( l1_orders_2(B_78)
      | ~ l1_waybel_0(B_78,A_79)
      | ~ l1_struct_0(A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_57,plain,
    ( l1_orders_2('#skF_5')
    | ~ l1_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_54])).

tff(c_60,plain,(
    l1_orders_2('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_57])).

tff(c_12,plain,(
    ! [A_10] :
      ( l1_struct_0(A_10)
      | ~ l1_orders_2(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_36,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_44,plain,(
    ! [A_76] :
      ( v1_xboole_0(A_76)
      | r2_hidden('#skF_1'(A_76),A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( m1_subset_1(A_5,B_6)
      | ~ r2_hidden(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_51,plain,(
    ! [A_76] :
      ( m1_subset_1('#skF_1'(A_76),A_76)
      | v1_xboole_0(A_76) ) ),
    inference(resolution,[status(thm)],[c_44,c_6])).

tff(c_22,plain,(
    ! [A_11,B_39,C_53,D_60] :
      ( m1_subset_1('#skF_2'(A_11,B_39,C_53,D_60),u1_struct_0(B_39))
      | r1_waybel_0(A_11,B_39,C_53)
      | ~ m1_subset_1(D_60,u1_struct_0(B_39))
      | ~ l1_waybel_0(B_39,A_11)
      | v2_struct_0(B_39)
      | ~ l1_struct_0(A_11)
      | v2_struct_0(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_24,plain,(
    ! [A_64,B_65,C_66] :
      ( m1_subset_1(k2_waybel_0(A_64,B_65,C_66),u1_struct_0(A_64))
      | ~ m1_subset_1(C_66,u1_struct_0(B_65))
      | ~ l1_waybel_0(B_65,A_64)
      | v2_struct_0(B_65)
      | ~ l1_struct_0(A_64)
      | v2_struct_0(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_8,plain,(
    ! [A_7,B_8] :
      ( r2_hidden(A_7,B_8)
      | v1_xboole_0(B_8)
      | ~ m1_subset_1(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_75,plain,(
    ! [A_97,B_98,C_99,D_100] :
      ( ~ r2_hidden(k2_waybel_0(A_97,B_98,'#skF_2'(A_97,B_98,C_99,D_100)),C_99)
      | r1_waybel_0(A_97,B_98,C_99)
      | ~ m1_subset_1(D_100,u1_struct_0(B_98))
      | ~ l1_waybel_0(B_98,A_97)
      | v2_struct_0(B_98)
      | ~ l1_struct_0(A_97)
      | v2_struct_0(A_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_81,plain,(
    ! [A_101,B_102,B_103,D_104] :
      ( r1_waybel_0(A_101,B_102,B_103)
      | ~ m1_subset_1(D_104,u1_struct_0(B_102))
      | ~ l1_waybel_0(B_102,A_101)
      | v2_struct_0(B_102)
      | ~ l1_struct_0(A_101)
      | v2_struct_0(A_101)
      | v1_xboole_0(B_103)
      | ~ m1_subset_1(k2_waybel_0(A_101,B_102,'#skF_2'(A_101,B_102,B_103,D_104)),B_103) ) ),
    inference(resolution,[status(thm)],[c_8,c_75])).

tff(c_93,plain,(
    ! [A_109,B_110,D_111] :
      ( r1_waybel_0(A_109,B_110,u1_struct_0(A_109))
      | ~ m1_subset_1(D_111,u1_struct_0(B_110))
      | v1_xboole_0(u1_struct_0(A_109))
      | ~ m1_subset_1('#skF_2'(A_109,B_110,u1_struct_0(A_109),D_111),u1_struct_0(B_110))
      | ~ l1_waybel_0(B_110,A_109)
      | v2_struct_0(B_110)
      | ~ l1_struct_0(A_109)
      | v2_struct_0(A_109) ) ),
    inference(resolution,[status(thm)],[c_24,c_81])).

tff(c_99,plain,(
    ! [A_112,B_113,D_114] :
      ( v1_xboole_0(u1_struct_0(A_112))
      | r1_waybel_0(A_112,B_113,u1_struct_0(A_112))
      | ~ m1_subset_1(D_114,u1_struct_0(B_113))
      | ~ l1_waybel_0(B_113,A_112)
      | v2_struct_0(B_113)
      | ~ l1_struct_0(A_112)
      | v2_struct_0(A_112) ) ),
    inference(resolution,[status(thm)],[c_22,c_93])).

tff(c_127,plain,(
    ! [A_120,B_121] :
      ( v1_xboole_0(u1_struct_0(A_120))
      | r1_waybel_0(A_120,B_121,u1_struct_0(A_120))
      | ~ l1_waybel_0(B_121,A_120)
      | v2_struct_0(B_121)
      | ~ l1_struct_0(A_120)
      | v2_struct_0(A_120)
      | v1_xboole_0(u1_struct_0(B_121)) ) ),
    inference(resolution,[status(thm)],[c_51,c_99])).

tff(c_28,plain,(
    ~ r1_waybel_0('#skF_4','#skF_5',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_130,plain,
    ( v1_xboole_0(u1_struct_0('#skF_4'))
    | ~ l1_waybel_0('#skF_5','#skF_4')
    | v2_struct_0('#skF_5')
    | ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4')
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_127,c_28])).

tff(c_133,plain,
    ( v1_xboole_0(u1_struct_0('#skF_4'))
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_4')
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_30,c_130])).

tff(c_134,plain,
    ( v1_xboole_0(u1_struct_0('#skF_4'))
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_36,c_133])).

tff(c_135,plain,(
    v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_134])).

tff(c_10,plain,(
    ! [A_9] :
      ( ~ v1_xboole_0(u1_struct_0(A_9))
      | ~ l1_struct_0(A_9)
      | v2_struct_0(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_138,plain,
    ( ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_135,c_10])).

tff(c_141,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_138])).

tff(c_144,plain,(
    ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_12,c_141])).

tff(c_148,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_144])).

tff(c_149,plain,(
    v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_134])).

tff(c_153,plain,
    ( ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_149,c_10])).

tff(c_156,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_153])).

tff(c_158,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_156])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n001.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 13:54:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.07/1.28  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.07/1.28  
% 2.07/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.07/1.28  %$ r1_waybel_0 > r1_orders_2 > r2_hidden > m1_subset_1 > l1_waybel_0 > v7_waybel_0 > v4_orders_2 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > k2_waybel_0 > #nlpp > u1_struct_0 > #skF_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3
% 2.07/1.28  
% 2.07/1.28  %Foreground sorts:
% 2.07/1.28  
% 2.07/1.28  
% 2.07/1.28  %Background operators:
% 2.07/1.28  
% 2.07/1.28  
% 2.07/1.28  %Foreground operators:
% 2.07/1.28  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.07/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.07/1.28  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.07/1.28  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.07/1.28  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 2.07/1.28  tff(k2_waybel_0, type, k2_waybel_0: ($i * $i * $i) > $i).
% 2.07/1.28  tff(v7_waybel_0, type, v7_waybel_0: $i > $o).
% 2.07/1.28  tff('#skF_5', type, '#skF_5': $i).
% 2.07/1.28  tff(r1_waybel_0, type, r1_waybel_0: ($i * $i * $i) > $o).
% 2.07/1.28  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.07/1.28  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.07/1.28  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.07/1.28  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.07/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.07/1.28  tff(l1_waybel_0, type, l1_waybel_0: ($i * $i) > $o).
% 2.07/1.28  tff('#skF_4', type, '#skF_4': $i).
% 2.07/1.28  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.07/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.07/1.28  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.07/1.28  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.07/1.28  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.07/1.28  
% 2.07/1.30  tff(f_116, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => r1_waybel_0(A, B, u1_struct_0(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_yellow_6)).
% 2.07/1.30  tff(f_98, axiom, (![A]: (l1_struct_0(A) => (![B]: (l1_waybel_0(B, A) => l1_orders_2(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_waybel_0)).
% 2.07/1.30  tff(f_53, axiom, (![A]: (l1_orders_2(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 2.07/1.30  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.07/1.30  tff(f_35, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 2.07/1.30  tff(f_77, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((~v2_struct_0(B) & l1_waybel_0(B, A)) => (![C]: (r1_waybel_0(A, B, C) <=> (?[D]: (m1_subset_1(D, u1_struct_0(B)) & (![E]: (m1_subset_1(E, u1_struct_0(B)) => (r1_orders_2(B, D, E) => r2_hidden(k2_waybel_0(A, B, E), C)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d11_waybel_0)).
% 2.07/1.30  tff(f_91, axiom, (![A, B, C]: (((((~v2_struct_0(A) & l1_struct_0(A)) & ~v2_struct_0(B)) & l1_waybel_0(B, A)) & m1_subset_1(C, u1_struct_0(B))) => m1_subset_1(k2_waybel_0(A, B, C), u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_waybel_0)).
% 2.07/1.30  tff(f_41, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 2.07/1.30  tff(f_49, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 2.07/1.30  tff(c_40, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_116])).
% 2.07/1.30  tff(c_38, plain, (l1_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_116])).
% 2.07/1.30  tff(c_30, plain, (l1_waybel_0('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_116])).
% 2.07/1.30  tff(c_54, plain, (![B_78, A_79]: (l1_orders_2(B_78) | ~l1_waybel_0(B_78, A_79) | ~l1_struct_0(A_79))), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.07/1.30  tff(c_57, plain, (l1_orders_2('#skF_5') | ~l1_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_30, c_54])).
% 2.07/1.30  tff(c_60, plain, (l1_orders_2('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_57])).
% 2.07/1.30  tff(c_12, plain, (![A_10]: (l1_struct_0(A_10) | ~l1_orders_2(A_10))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.07/1.30  tff(c_36, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_116])).
% 2.07/1.30  tff(c_44, plain, (![A_76]: (v1_xboole_0(A_76) | r2_hidden('#skF_1'(A_76), A_76))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.07/1.30  tff(c_6, plain, (![A_5, B_6]: (m1_subset_1(A_5, B_6) | ~r2_hidden(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.07/1.30  tff(c_51, plain, (![A_76]: (m1_subset_1('#skF_1'(A_76), A_76) | v1_xboole_0(A_76))), inference(resolution, [status(thm)], [c_44, c_6])).
% 2.07/1.30  tff(c_22, plain, (![A_11, B_39, C_53, D_60]: (m1_subset_1('#skF_2'(A_11, B_39, C_53, D_60), u1_struct_0(B_39)) | r1_waybel_0(A_11, B_39, C_53) | ~m1_subset_1(D_60, u1_struct_0(B_39)) | ~l1_waybel_0(B_39, A_11) | v2_struct_0(B_39) | ~l1_struct_0(A_11) | v2_struct_0(A_11))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.07/1.30  tff(c_24, plain, (![A_64, B_65, C_66]: (m1_subset_1(k2_waybel_0(A_64, B_65, C_66), u1_struct_0(A_64)) | ~m1_subset_1(C_66, u1_struct_0(B_65)) | ~l1_waybel_0(B_65, A_64) | v2_struct_0(B_65) | ~l1_struct_0(A_64) | v2_struct_0(A_64))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.07/1.30  tff(c_8, plain, (![A_7, B_8]: (r2_hidden(A_7, B_8) | v1_xboole_0(B_8) | ~m1_subset_1(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.07/1.30  tff(c_75, plain, (![A_97, B_98, C_99, D_100]: (~r2_hidden(k2_waybel_0(A_97, B_98, '#skF_2'(A_97, B_98, C_99, D_100)), C_99) | r1_waybel_0(A_97, B_98, C_99) | ~m1_subset_1(D_100, u1_struct_0(B_98)) | ~l1_waybel_0(B_98, A_97) | v2_struct_0(B_98) | ~l1_struct_0(A_97) | v2_struct_0(A_97))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.07/1.30  tff(c_81, plain, (![A_101, B_102, B_103, D_104]: (r1_waybel_0(A_101, B_102, B_103) | ~m1_subset_1(D_104, u1_struct_0(B_102)) | ~l1_waybel_0(B_102, A_101) | v2_struct_0(B_102) | ~l1_struct_0(A_101) | v2_struct_0(A_101) | v1_xboole_0(B_103) | ~m1_subset_1(k2_waybel_0(A_101, B_102, '#skF_2'(A_101, B_102, B_103, D_104)), B_103))), inference(resolution, [status(thm)], [c_8, c_75])).
% 2.07/1.30  tff(c_93, plain, (![A_109, B_110, D_111]: (r1_waybel_0(A_109, B_110, u1_struct_0(A_109)) | ~m1_subset_1(D_111, u1_struct_0(B_110)) | v1_xboole_0(u1_struct_0(A_109)) | ~m1_subset_1('#skF_2'(A_109, B_110, u1_struct_0(A_109), D_111), u1_struct_0(B_110)) | ~l1_waybel_0(B_110, A_109) | v2_struct_0(B_110) | ~l1_struct_0(A_109) | v2_struct_0(A_109))), inference(resolution, [status(thm)], [c_24, c_81])).
% 2.07/1.30  tff(c_99, plain, (![A_112, B_113, D_114]: (v1_xboole_0(u1_struct_0(A_112)) | r1_waybel_0(A_112, B_113, u1_struct_0(A_112)) | ~m1_subset_1(D_114, u1_struct_0(B_113)) | ~l1_waybel_0(B_113, A_112) | v2_struct_0(B_113) | ~l1_struct_0(A_112) | v2_struct_0(A_112))), inference(resolution, [status(thm)], [c_22, c_93])).
% 2.07/1.30  tff(c_127, plain, (![A_120, B_121]: (v1_xboole_0(u1_struct_0(A_120)) | r1_waybel_0(A_120, B_121, u1_struct_0(A_120)) | ~l1_waybel_0(B_121, A_120) | v2_struct_0(B_121) | ~l1_struct_0(A_120) | v2_struct_0(A_120) | v1_xboole_0(u1_struct_0(B_121)))), inference(resolution, [status(thm)], [c_51, c_99])).
% 2.07/1.30  tff(c_28, plain, (~r1_waybel_0('#skF_4', '#skF_5', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_116])).
% 2.07/1.30  tff(c_130, plain, (v1_xboole_0(u1_struct_0('#skF_4')) | ~l1_waybel_0('#skF_5', '#skF_4') | v2_struct_0('#skF_5') | ~l1_struct_0('#skF_4') | v2_struct_0('#skF_4') | v1_xboole_0(u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_127, c_28])).
% 2.07/1.30  tff(c_133, plain, (v1_xboole_0(u1_struct_0('#skF_4')) | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | v1_xboole_0(u1_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_30, c_130])).
% 2.07/1.30  tff(c_134, plain, (v1_xboole_0(u1_struct_0('#skF_4')) | v1_xboole_0(u1_struct_0('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_40, c_36, c_133])).
% 2.07/1.30  tff(c_135, plain, (v1_xboole_0(u1_struct_0('#skF_5'))), inference(splitLeft, [status(thm)], [c_134])).
% 2.07/1.30  tff(c_10, plain, (![A_9]: (~v1_xboole_0(u1_struct_0(A_9)) | ~l1_struct_0(A_9) | v2_struct_0(A_9))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.07/1.30  tff(c_138, plain, (~l1_struct_0('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_135, c_10])).
% 2.07/1.30  tff(c_141, plain, (~l1_struct_0('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_36, c_138])).
% 2.07/1.30  tff(c_144, plain, (~l1_orders_2('#skF_5')), inference(resolution, [status(thm)], [c_12, c_141])).
% 2.07/1.30  tff(c_148, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_144])).
% 2.07/1.30  tff(c_149, plain, (v1_xboole_0(u1_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_134])).
% 2.07/1.30  tff(c_153, plain, (~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_149, c_10])).
% 2.07/1.30  tff(c_156, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_153])).
% 2.07/1.30  tff(c_158, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_156])).
% 2.07/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.07/1.30  
% 2.07/1.30  Inference rules
% 2.07/1.30  ----------------------
% 2.07/1.30  #Ref     : 0
% 2.07/1.30  #Sup     : 20
% 2.07/1.30  #Fact    : 0
% 2.07/1.30  #Define  : 0
% 2.07/1.30  #Split   : 1
% 2.07/1.30  #Chain   : 0
% 2.07/1.30  #Close   : 0
% 2.07/1.30  
% 2.07/1.30  Ordering : KBO
% 2.07/1.30  
% 2.07/1.30  Simplification rules
% 2.07/1.30  ----------------------
% 2.07/1.30  #Subsume      : 2
% 2.07/1.30  #Demod        : 5
% 2.07/1.30  #Tautology    : 4
% 2.07/1.30  #SimpNegUnit  : 3
% 2.07/1.30  #BackRed      : 0
% 2.07/1.30  
% 2.07/1.30  #Partial instantiations: 0
% 2.07/1.30  #Strategies tried      : 1
% 2.07/1.30  
% 2.07/1.30  Timing (in seconds)
% 2.07/1.30  ----------------------
% 2.35/1.30  Preprocessing        : 0.31
% 2.35/1.30  Parsing              : 0.17
% 2.35/1.30  CNF conversion       : 0.03
% 2.35/1.30  Main loop            : 0.20
% 2.35/1.30  Inferencing          : 0.09
% 2.35/1.30  Reduction            : 0.05
% 2.35/1.30  Demodulation         : 0.03
% 2.35/1.30  BG Simplification    : 0.02
% 2.35/1.30  Subsumption          : 0.04
% 2.35/1.30  Abstraction          : 0.01
% 2.35/1.30  MUC search           : 0.00
% 2.35/1.30  Cooper               : 0.00
% 2.35/1.30  Total                : 0.54
% 2.35/1.30  Index Insertion      : 0.00
% 2.35/1.30  Index Deletion       : 0.00
% 2.35/1.30  Index Matching       : 0.00
% 2.35/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
