%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:09 EST 2020

% Result     : Theorem 2.81s
% Output     : CNFRefutation 3.18s
% Verified   : 
% Statistics : Number of formulae       :   62 (  87 expanded)
%              Number of leaves         :   28 (  44 expanded)
%              Depth                    :   13
%              Number of atoms          :  147 ( 250 expanded)
%              Number of equality atoms :    7 (   8 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_orders_2 > r2_hidden > r1_tarski > m1_subset_1 > l1_waybel_0 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > k4_waybel_9 > a_3_0_waybel_9 > #nlpp > u1_struct_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff(k4_waybel_9,type,(
    k4_waybel_9: ( $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(a_3_0_waybel_9,type,(
    a_3_0_waybel_9: ( $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_109,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & l1_struct_0(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & l1_waybel_0(B,A) )
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(B))
               => r1_tarski(u1_struct_0(k4_waybel_9(A,B,C)),u1_struct_0(B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_waybel_9)).

tff(f_49,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ! [B] :
          ( l1_waybel_0(B,A)
         => l1_orders_2(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_waybel_0)).

tff(f_42,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_76,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v2_struct_0(B)
        & l1_struct_0(B)
        & ~ v2_struct_0(C)
        & l1_waybel_0(C,B)
        & m1_subset_1(D,u1_struct_0(C)) )
     => ( r2_hidden(A,a_3_0_waybel_9(B,C,D))
      <=> ? [E] :
            ( m1_subset_1(E,u1_struct_0(C))
            & A = E
            & r1_orders_2(C,D,E) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_3_0_waybel_9)).

tff(f_38,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_92,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & l1_waybel_0(B,A) )
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(B))
             => u1_struct_0(k4_waybel_9(A,B,C)) = a_3_0_waybel_9(A,B,C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_waybel_9)).

tff(f_55,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ( v2_struct_0(A)
      <=> v1_xboole_0(u1_struct_0(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_struct_0)).

tff(c_36,plain,(
    l1_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_32,plain,(
    l1_waybel_0('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_40,plain,(
    ! [B_32,A_33] :
      ( l1_orders_2(B_32)
      | ~ l1_waybel_0(B_32,A_33)
      | ~ l1_struct_0(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_43,plain,
    ( l1_orders_2('#skF_4')
    | ~ l1_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_40])).

tff(c_46,plain,(
    l1_orders_2('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_43])).

tff(c_10,plain,(
    ! [A_8] :
      ( l1_struct_0(A_8)
      | ~ l1_orders_2(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_34,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_38,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_30,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_127,plain,(
    ! [A_64,B_65,C_66,D_67] :
      ( '#skF_2'(A_64,B_65,C_66,D_67) = A_64
      | ~ r2_hidden(A_64,a_3_0_waybel_9(B_65,C_66,D_67))
      | ~ m1_subset_1(D_67,u1_struct_0(C_66))
      | ~ l1_waybel_0(C_66,B_65)
      | v2_struct_0(C_66)
      | ~ l1_struct_0(B_65)
      | v2_struct_0(B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_212,plain,(
    ! [B_103,C_104,D_105,B_106] :
      ( '#skF_2'('#skF_1'(a_3_0_waybel_9(B_103,C_104,D_105),B_106),B_103,C_104,D_105) = '#skF_1'(a_3_0_waybel_9(B_103,C_104,D_105),B_106)
      | ~ m1_subset_1(D_105,u1_struct_0(C_104))
      | ~ l1_waybel_0(C_104,B_103)
      | v2_struct_0(C_104)
      | ~ l1_struct_0(B_103)
      | v2_struct_0(B_103)
      | r1_tarski(a_3_0_waybel_9(B_103,C_104,D_105),B_106) ) ),
    inference(resolution,[status(thm)],[c_6,c_127])).

tff(c_24,plain,(
    ! [A_13,B_14,C_15,D_16] :
      ( m1_subset_1('#skF_2'(A_13,B_14,C_15,D_16),u1_struct_0(C_15))
      | ~ r2_hidden(A_13,a_3_0_waybel_9(B_14,C_15,D_16))
      | ~ m1_subset_1(D_16,u1_struct_0(C_15))
      | ~ l1_waybel_0(C_15,B_14)
      | v2_struct_0(C_15)
      | ~ l1_struct_0(B_14)
      | v2_struct_0(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_326,plain,(
    ! [B_138,C_139,D_140,B_141] :
      ( m1_subset_1('#skF_1'(a_3_0_waybel_9(B_138,C_139,D_140),B_141),u1_struct_0(C_139))
      | ~ r2_hidden('#skF_1'(a_3_0_waybel_9(B_138,C_139,D_140),B_141),a_3_0_waybel_9(B_138,C_139,D_140))
      | ~ m1_subset_1(D_140,u1_struct_0(C_139))
      | ~ l1_waybel_0(C_139,B_138)
      | v2_struct_0(C_139)
      | ~ l1_struct_0(B_138)
      | v2_struct_0(B_138)
      | ~ m1_subset_1(D_140,u1_struct_0(C_139))
      | ~ l1_waybel_0(C_139,B_138)
      | v2_struct_0(C_139)
      | ~ l1_struct_0(B_138)
      | v2_struct_0(B_138)
      | r1_tarski(a_3_0_waybel_9(B_138,C_139,D_140),B_141) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_212,c_24])).

tff(c_348,plain,(
    ! [B_142,C_143,D_144,B_145] :
      ( m1_subset_1('#skF_1'(a_3_0_waybel_9(B_142,C_143,D_144),B_145),u1_struct_0(C_143))
      | ~ m1_subset_1(D_144,u1_struct_0(C_143))
      | ~ l1_waybel_0(C_143,B_142)
      | v2_struct_0(C_143)
      | ~ l1_struct_0(B_142)
      | v2_struct_0(B_142)
      | r1_tarski(a_3_0_waybel_9(B_142,C_143,D_144),B_145) ) ),
    inference(resolution,[status(thm)],[c_6,c_326])).

tff(c_61,plain,(
    ! [A_41,B_42] :
      ( r2_hidden(A_41,B_42)
      | v1_xboole_0(B_42)
      | ~ m1_subset_1(A_41,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_66,plain,(
    ! [A_1,B_42] :
      ( r1_tarski(A_1,B_42)
      | v1_xboole_0(B_42)
      | ~ m1_subset_1('#skF_1'(A_1,B_42),B_42) ) ),
    inference(resolution,[status(thm)],[c_61,c_4])).

tff(c_378,plain,(
    ! [C_146,D_147,B_148] :
      ( v1_xboole_0(u1_struct_0(C_146))
      | ~ m1_subset_1(D_147,u1_struct_0(C_146))
      | ~ l1_waybel_0(C_146,B_148)
      | v2_struct_0(C_146)
      | ~ l1_struct_0(B_148)
      | v2_struct_0(B_148)
      | r1_tarski(a_3_0_waybel_9(B_148,C_146,D_147),u1_struct_0(C_146)) ) ),
    inference(resolution,[status(thm)],[c_348,c_66])).

tff(c_88,plain,(
    ! [A_54,B_55,C_56] :
      ( u1_struct_0(k4_waybel_9(A_54,B_55,C_56)) = a_3_0_waybel_9(A_54,B_55,C_56)
      | ~ m1_subset_1(C_56,u1_struct_0(B_55))
      | ~ l1_waybel_0(B_55,A_54)
      | v2_struct_0(B_55)
      | ~ l1_struct_0(A_54)
      | v2_struct_0(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_90,plain,(
    ! [A_54] :
      ( u1_struct_0(k4_waybel_9(A_54,'#skF_4','#skF_5')) = a_3_0_waybel_9(A_54,'#skF_4','#skF_5')
      | ~ l1_waybel_0('#skF_4',A_54)
      | v2_struct_0('#skF_4')
      | ~ l1_struct_0(A_54)
      | v2_struct_0(A_54) ) ),
    inference(resolution,[status(thm)],[c_30,c_88])).

tff(c_98,plain,(
    ! [A_61] :
      ( u1_struct_0(k4_waybel_9(A_61,'#skF_4','#skF_5')) = a_3_0_waybel_9(A_61,'#skF_4','#skF_5')
      | ~ l1_waybel_0('#skF_4',A_61)
      | ~ l1_struct_0(A_61)
      | v2_struct_0(A_61) ) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_90])).

tff(c_28,plain,(
    ~ r1_tarski(u1_struct_0(k4_waybel_9('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_109,plain,
    ( ~ r1_tarski(a_3_0_waybel_9('#skF_3','#skF_4','#skF_5'),u1_struct_0('#skF_4'))
    | ~ l1_waybel_0('#skF_4','#skF_3')
    | ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_98,c_28])).

tff(c_118,plain,
    ( ~ r1_tarski(a_3_0_waybel_9('#skF_3','#skF_4','#skF_5'),u1_struct_0('#skF_4'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_109])).

tff(c_119,plain,(
    ~ r1_tarski(a_3_0_waybel_9('#skF_3','#skF_4','#skF_5'),u1_struct_0('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_118])).

tff(c_383,plain,
    ( v1_xboole_0(u1_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ l1_waybel_0('#skF_4','#skF_3')
    | v2_struct_0('#skF_4')
    | ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_378,c_119])).

tff(c_400,plain,
    ( v1_xboole_0(u1_struct_0('#skF_4'))
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_30,c_383])).

tff(c_401,plain,(
    v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_34,c_400])).

tff(c_14,plain,(
    ! [A_12] :
      ( v2_struct_0(A_12)
      | ~ v1_xboole_0(u1_struct_0(A_12))
      | ~ l1_struct_0(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_406,plain,
    ( v2_struct_0('#skF_4')
    | ~ l1_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_401,c_14])).

tff(c_409,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_406])).

tff(c_412,plain,(
    ~ l1_orders_2('#skF_4') ),
    inference(resolution,[status(thm)],[c_10,c_409])).

tff(c_416,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_412])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:22:19 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.81/1.44  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.81/1.45  
% 2.81/1.45  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.81/1.45  %$ r1_orders_2 > r2_hidden > r1_tarski > m1_subset_1 > l1_waybel_0 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > k4_waybel_9 > a_3_0_waybel_9 > #nlpp > u1_struct_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.81/1.45  
% 2.81/1.45  %Foreground sorts:
% 2.81/1.45  
% 2.81/1.45  
% 2.81/1.45  %Background operators:
% 2.81/1.45  
% 2.81/1.45  
% 2.81/1.45  %Foreground operators:
% 2.81/1.45  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.81/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.81/1.45  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.81/1.45  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 2.81/1.45  tff(k4_waybel_9, type, k4_waybel_9: ($i * $i * $i) > $i).
% 2.81/1.45  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.81/1.45  tff('#skF_5', type, '#skF_5': $i).
% 2.81/1.45  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.81/1.45  tff('#skF_3', type, '#skF_3': $i).
% 2.81/1.45  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.81/1.45  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.81/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.81/1.45  tff(l1_waybel_0, type, l1_waybel_0: ($i * $i) > $o).
% 2.81/1.45  tff('#skF_4', type, '#skF_4': $i).
% 2.81/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.81/1.45  tff(a_3_0_waybel_9, type, a_3_0_waybel_9: ($i * $i * $i) > $i).
% 2.81/1.45  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.81/1.45  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.81/1.45  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.81/1.45  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.81/1.45  
% 3.18/1.47  tff(f_109, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((~v2_struct_0(B) & l1_waybel_0(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(B)) => r1_tarski(u1_struct_0(k4_waybel_9(A, B, C)), u1_struct_0(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_waybel_9)).
% 3.18/1.47  tff(f_49, axiom, (![A]: (l1_struct_0(A) => (![B]: (l1_waybel_0(B, A) => l1_orders_2(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_waybel_0)).
% 3.18/1.47  tff(f_42, axiom, (![A]: (l1_orders_2(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 3.18/1.47  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 3.18/1.47  tff(f_76, axiom, (![A, B, C, D]: (((((~v2_struct_0(B) & l1_struct_0(B)) & ~v2_struct_0(C)) & l1_waybel_0(C, B)) & m1_subset_1(D, u1_struct_0(C))) => (r2_hidden(A, a_3_0_waybel_9(B, C, D)) <=> (?[E]: ((m1_subset_1(E, u1_struct_0(C)) & (A = E)) & r1_orders_2(C, D, E)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fraenkel_a_3_0_waybel_9)).
% 3.18/1.47  tff(f_38, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 3.18/1.47  tff(f_92, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((~v2_struct_0(B) & l1_waybel_0(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(B)) => (u1_struct_0(k4_waybel_9(A, B, C)) = a_3_0_waybel_9(A, B, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_waybel_9)).
% 3.18/1.47  tff(f_55, axiom, (![A]: (l1_struct_0(A) => (v2_struct_0(A) <=> v1_xboole_0(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_struct_0)).
% 3.18/1.47  tff(c_36, plain, (l1_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.18/1.47  tff(c_32, plain, (l1_waybel_0('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.18/1.47  tff(c_40, plain, (![B_32, A_33]: (l1_orders_2(B_32) | ~l1_waybel_0(B_32, A_33) | ~l1_struct_0(A_33))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.18/1.47  tff(c_43, plain, (l1_orders_2('#skF_4') | ~l1_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_32, c_40])).
% 3.18/1.47  tff(c_46, plain, (l1_orders_2('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_43])).
% 3.18/1.47  tff(c_10, plain, (![A_8]: (l1_struct_0(A_8) | ~l1_orders_2(A_8))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.18/1.47  tff(c_34, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.18/1.47  tff(c_38, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.18/1.47  tff(c_30, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.18/1.47  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.18/1.47  tff(c_127, plain, (![A_64, B_65, C_66, D_67]: ('#skF_2'(A_64, B_65, C_66, D_67)=A_64 | ~r2_hidden(A_64, a_3_0_waybel_9(B_65, C_66, D_67)) | ~m1_subset_1(D_67, u1_struct_0(C_66)) | ~l1_waybel_0(C_66, B_65) | v2_struct_0(C_66) | ~l1_struct_0(B_65) | v2_struct_0(B_65))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.18/1.47  tff(c_212, plain, (![B_103, C_104, D_105, B_106]: ('#skF_2'('#skF_1'(a_3_0_waybel_9(B_103, C_104, D_105), B_106), B_103, C_104, D_105)='#skF_1'(a_3_0_waybel_9(B_103, C_104, D_105), B_106) | ~m1_subset_1(D_105, u1_struct_0(C_104)) | ~l1_waybel_0(C_104, B_103) | v2_struct_0(C_104) | ~l1_struct_0(B_103) | v2_struct_0(B_103) | r1_tarski(a_3_0_waybel_9(B_103, C_104, D_105), B_106))), inference(resolution, [status(thm)], [c_6, c_127])).
% 3.18/1.47  tff(c_24, plain, (![A_13, B_14, C_15, D_16]: (m1_subset_1('#skF_2'(A_13, B_14, C_15, D_16), u1_struct_0(C_15)) | ~r2_hidden(A_13, a_3_0_waybel_9(B_14, C_15, D_16)) | ~m1_subset_1(D_16, u1_struct_0(C_15)) | ~l1_waybel_0(C_15, B_14) | v2_struct_0(C_15) | ~l1_struct_0(B_14) | v2_struct_0(B_14))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.18/1.47  tff(c_326, plain, (![B_138, C_139, D_140, B_141]: (m1_subset_1('#skF_1'(a_3_0_waybel_9(B_138, C_139, D_140), B_141), u1_struct_0(C_139)) | ~r2_hidden('#skF_1'(a_3_0_waybel_9(B_138, C_139, D_140), B_141), a_3_0_waybel_9(B_138, C_139, D_140)) | ~m1_subset_1(D_140, u1_struct_0(C_139)) | ~l1_waybel_0(C_139, B_138) | v2_struct_0(C_139) | ~l1_struct_0(B_138) | v2_struct_0(B_138) | ~m1_subset_1(D_140, u1_struct_0(C_139)) | ~l1_waybel_0(C_139, B_138) | v2_struct_0(C_139) | ~l1_struct_0(B_138) | v2_struct_0(B_138) | r1_tarski(a_3_0_waybel_9(B_138, C_139, D_140), B_141))), inference(superposition, [status(thm), theory('equality')], [c_212, c_24])).
% 3.18/1.47  tff(c_348, plain, (![B_142, C_143, D_144, B_145]: (m1_subset_1('#skF_1'(a_3_0_waybel_9(B_142, C_143, D_144), B_145), u1_struct_0(C_143)) | ~m1_subset_1(D_144, u1_struct_0(C_143)) | ~l1_waybel_0(C_143, B_142) | v2_struct_0(C_143) | ~l1_struct_0(B_142) | v2_struct_0(B_142) | r1_tarski(a_3_0_waybel_9(B_142, C_143, D_144), B_145))), inference(resolution, [status(thm)], [c_6, c_326])).
% 3.18/1.47  tff(c_61, plain, (![A_41, B_42]: (r2_hidden(A_41, B_42) | v1_xboole_0(B_42) | ~m1_subset_1(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.18/1.47  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.18/1.47  tff(c_66, plain, (![A_1, B_42]: (r1_tarski(A_1, B_42) | v1_xboole_0(B_42) | ~m1_subset_1('#skF_1'(A_1, B_42), B_42))), inference(resolution, [status(thm)], [c_61, c_4])).
% 3.18/1.47  tff(c_378, plain, (![C_146, D_147, B_148]: (v1_xboole_0(u1_struct_0(C_146)) | ~m1_subset_1(D_147, u1_struct_0(C_146)) | ~l1_waybel_0(C_146, B_148) | v2_struct_0(C_146) | ~l1_struct_0(B_148) | v2_struct_0(B_148) | r1_tarski(a_3_0_waybel_9(B_148, C_146, D_147), u1_struct_0(C_146)))), inference(resolution, [status(thm)], [c_348, c_66])).
% 3.18/1.47  tff(c_88, plain, (![A_54, B_55, C_56]: (u1_struct_0(k4_waybel_9(A_54, B_55, C_56))=a_3_0_waybel_9(A_54, B_55, C_56) | ~m1_subset_1(C_56, u1_struct_0(B_55)) | ~l1_waybel_0(B_55, A_54) | v2_struct_0(B_55) | ~l1_struct_0(A_54) | v2_struct_0(A_54))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.18/1.47  tff(c_90, plain, (![A_54]: (u1_struct_0(k4_waybel_9(A_54, '#skF_4', '#skF_5'))=a_3_0_waybel_9(A_54, '#skF_4', '#skF_5') | ~l1_waybel_0('#skF_4', A_54) | v2_struct_0('#skF_4') | ~l1_struct_0(A_54) | v2_struct_0(A_54))), inference(resolution, [status(thm)], [c_30, c_88])).
% 3.18/1.47  tff(c_98, plain, (![A_61]: (u1_struct_0(k4_waybel_9(A_61, '#skF_4', '#skF_5'))=a_3_0_waybel_9(A_61, '#skF_4', '#skF_5') | ~l1_waybel_0('#skF_4', A_61) | ~l1_struct_0(A_61) | v2_struct_0(A_61))), inference(negUnitSimplification, [status(thm)], [c_34, c_90])).
% 3.18/1.47  tff(c_28, plain, (~r1_tarski(u1_struct_0(k4_waybel_9('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.18/1.47  tff(c_109, plain, (~r1_tarski(a_3_0_waybel_9('#skF_3', '#skF_4', '#skF_5'), u1_struct_0('#skF_4')) | ~l1_waybel_0('#skF_4', '#skF_3') | ~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_98, c_28])).
% 3.18/1.47  tff(c_118, plain, (~r1_tarski(a_3_0_waybel_9('#skF_3', '#skF_4', '#skF_5'), u1_struct_0('#skF_4')) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_32, c_109])).
% 3.18/1.47  tff(c_119, plain, (~r1_tarski(a_3_0_waybel_9('#skF_3', '#skF_4', '#skF_5'), u1_struct_0('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_38, c_118])).
% 3.18/1.47  tff(c_383, plain, (v1_xboole_0(u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~l1_waybel_0('#skF_4', '#skF_3') | v2_struct_0('#skF_4') | ~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_378, c_119])).
% 3.18/1.47  tff(c_400, plain, (v1_xboole_0(u1_struct_0('#skF_4')) | v2_struct_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_32, c_30, c_383])).
% 3.18/1.47  tff(c_401, plain, (v1_xboole_0(u1_struct_0('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_38, c_34, c_400])).
% 3.18/1.47  tff(c_14, plain, (![A_12]: (v2_struct_0(A_12) | ~v1_xboole_0(u1_struct_0(A_12)) | ~l1_struct_0(A_12))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.18/1.47  tff(c_406, plain, (v2_struct_0('#skF_4') | ~l1_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_401, c_14])).
% 3.18/1.47  tff(c_409, plain, (~l1_struct_0('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_34, c_406])).
% 3.18/1.47  tff(c_412, plain, (~l1_orders_2('#skF_4')), inference(resolution, [status(thm)], [c_10, c_409])).
% 3.18/1.47  tff(c_416, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_412])).
% 3.18/1.47  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.18/1.47  
% 3.18/1.47  Inference rules
% 3.18/1.47  ----------------------
% 3.18/1.47  #Ref     : 0
% 3.18/1.47  #Sup     : 92
% 3.18/1.47  #Fact    : 0
% 3.18/1.47  #Define  : 0
% 3.18/1.47  #Split   : 1
% 3.18/1.47  #Chain   : 0
% 3.18/1.47  #Close   : 0
% 3.18/1.47  
% 3.18/1.47  Ordering : KBO
% 3.18/1.47  
% 3.18/1.47  Simplification rules
% 3.18/1.47  ----------------------
% 3.18/1.47  #Subsume      : 7
% 3.18/1.47  #Demod        : 8
% 3.18/1.47  #Tautology    : 14
% 3.18/1.47  #SimpNegUnit  : 8
% 3.18/1.47  #BackRed      : 0
% 3.18/1.47  
% 3.18/1.47  #Partial instantiations: 0
% 3.18/1.47  #Strategies tried      : 1
% 3.18/1.47  
% 3.18/1.47  Timing (in seconds)
% 3.18/1.47  ----------------------
% 3.18/1.47  Preprocessing        : 0.31
% 3.18/1.47  Parsing              : 0.17
% 3.18/1.47  CNF conversion       : 0.02
% 3.18/1.47  Main loop            : 0.39
% 3.18/1.47  Inferencing          : 0.16
% 3.18/1.47  Reduction            : 0.09
% 3.18/1.47  Demodulation         : 0.06
% 3.18/1.47  BG Simplification    : 0.03
% 3.18/1.47  Subsumption          : 0.09
% 3.18/1.47  Abstraction          : 0.02
% 3.18/1.47  MUC search           : 0.00
% 3.18/1.47  Cooper               : 0.00
% 3.18/1.47  Total                : 0.73
% 3.18/1.47  Index Insertion      : 0.00
% 3.18/1.47  Index Deletion       : 0.00
% 3.18/1.47  Index Matching       : 0.00
% 3.18/1.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
