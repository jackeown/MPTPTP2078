%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:47 EST 2020

% Result     : Theorem 2.47s
% Output     : CNFRefutation 2.76s
% Verified   : 
% Statistics : Number of formulae       :   52 (  69 expanded)
%              Number of leaves         :   26 (  38 expanded)
%              Depth                    :   14
%              Number of atoms          :  145 ( 236 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_waybel_0 > r1_orders_2 > r2_hidden > m1_subset_1 > l1_waybel_0 > v7_waybel_0 > v4_orders_2 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > k2_waybel_0 > o_2_2_yellow_6 > #nlpp > u1_struct_0 > #skF_3 > #skF_2 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(o_2_2_yellow_6,type,(
    o_2_2_yellow_6: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff(k2_waybel_0,type,(
    k2_waybel_0: ( $i * $i * $i ) > $i )).

tff(v7_waybel_0,type,(
    v7_waybel_0: $i > $o )).

tff(r1_waybel_0,type,(
    r1_waybel_0: ( $i * $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_118,negated_conjecture,(
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

tff(f_100,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A)
        & ~ v2_struct_0(B)
        & v4_orders_2(B)
        & v7_waybel_0(B)
        & l1_waybel_0(B,A) )
     => m1_subset_1(o_2_2_yellow_6(A,B),u1_struct_0(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_o_2_2_yellow_6)).

tff(f_70,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_waybel_0)).

tff(f_84,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A)
        & ~ v2_struct_0(B)
        & l1_waybel_0(B,A)
        & m1_subset_1(C,u1_struct_0(B)) )
     => m1_subset_1(k2_waybel_0(A,B,C),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_waybel_0)).

tff(f_38,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_46,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(c_38,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_36,plain,(
    l1_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_28,plain,(
    l1_waybel_0('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_34,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_32,plain,(
    v4_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_30,plain,(
    v7_waybel_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_24,plain,(
    ! [A_60,B_61] :
      ( m1_subset_1(o_2_2_yellow_6(A_60,B_61),u1_struct_0(B_61))
      | ~ l1_waybel_0(B_61,A_60)
      | ~ v7_waybel_0(B_61)
      | ~ v4_orders_2(B_61)
      | v2_struct_0(B_61)
      | ~ l1_struct_0(A_60)
      | v2_struct_0(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_20,plain,(
    ! [A_4,B_32,C_46,D_53] :
      ( m1_subset_1('#skF_1'(A_4,B_32,C_46,D_53),u1_struct_0(B_32))
      | r1_waybel_0(A_4,B_32,C_46)
      | ~ m1_subset_1(D_53,u1_struct_0(B_32))
      | ~ l1_waybel_0(B_32,A_4)
      | v2_struct_0(B_32)
      | ~ l1_struct_0(A_4)
      | v2_struct_0(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_22,plain,(
    ! [A_57,B_58,C_59] :
      ( m1_subset_1(k2_waybel_0(A_57,B_58,C_59),u1_struct_0(A_57))
      | ~ m1_subset_1(C_59,u1_struct_0(B_58))
      | ~ l1_waybel_0(B_58,A_57)
      | v2_struct_0(B_58)
      | ~ l1_struct_0(A_57)
      | v2_struct_0(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( r2_hidden(B_2,A_1)
      | ~ m1_subset_1(B_2,A_1)
      | v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_75,plain,(
    ! [A_93,B_94,C_95,D_96] :
      ( ~ r2_hidden(k2_waybel_0(A_93,B_94,'#skF_1'(A_93,B_94,C_95,D_96)),C_95)
      | r1_waybel_0(A_93,B_94,C_95)
      | ~ m1_subset_1(D_96,u1_struct_0(B_94))
      | ~ l1_waybel_0(B_94,A_93)
      | v2_struct_0(B_94)
      | ~ l1_struct_0(A_93)
      | v2_struct_0(A_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_99,plain,(
    ! [A_105,B_106,A_107,D_108] :
      ( r1_waybel_0(A_105,B_106,A_107)
      | ~ m1_subset_1(D_108,u1_struct_0(B_106))
      | ~ l1_waybel_0(B_106,A_105)
      | v2_struct_0(B_106)
      | ~ l1_struct_0(A_105)
      | v2_struct_0(A_105)
      | ~ m1_subset_1(k2_waybel_0(A_105,B_106,'#skF_1'(A_105,B_106,A_107,D_108)),A_107)
      | v1_xboole_0(A_107) ) ),
    inference(resolution,[status(thm)],[c_4,c_75])).

tff(c_116,plain,(
    ! [A_113,B_114,D_115] :
      ( r1_waybel_0(A_113,B_114,u1_struct_0(A_113))
      | ~ m1_subset_1(D_115,u1_struct_0(B_114))
      | v1_xboole_0(u1_struct_0(A_113))
      | ~ m1_subset_1('#skF_1'(A_113,B_114,u1_struct_0(A_113),D_115),u1_struct_0(B_114))
      | ~ l1_waybel_0(B_114,A_113)
      | v2_struct_0(B_114)
      | ~ l1_struct_0(A_113)
      | v2_struct_0(A_113) ) ),
    inference(resolution,[status(thm)],[c_22,c_99])).

tff(c_136,plain,(
    ! [A_121,B_122,D_123] :
      ( v1_xboole_0(u1_struct_0(A_121))
      | r1_waybel_0(A_121,B_122,u1_struct_0(A_121))
      | ~ m1_subset_1(D_123,u1_struct_0(B_122))
      | ~ l1_waybel_0(B_122,A_121)
      | v2_struct_0(B_122)
      | ~ l1_struct_0(A_121)
      | v2_struct_0(A_121) ) ),
    inference(resolution,[status(thm)],[c_20,c_116])).

tff(c_263,plain,(
    ! [A_158,B_159,A_160] :
      ( v1_xboole_0(u1_struct_0(A_158))
      | r1_waybel_0(A_158,B_159,u1_struct_0(A_158))
      | ~ l1_waybel_0(B_159,A_158)
      | ~ l1_struct_0(A_158)
      | v2_struct_0(A_158)
      | ~ l1_waybel_0(B_159,A_160)
      | ~ v7_waybel_0(B_159)
      | ~ v4_orders_2(B_159)
      | v2_struct_0(B_159)
      | ~ l1_struct_0(A_160)
      | v2_struct_0(A_160) ) ),
    inference(resolution,[status(thm)],[c_24,c_136])).

tff(c_265,plain,(
    ! [A_158] :
      ( v1_xboole_0(u1_struct_0(A_158))
      | r1_waybel_0(A_158,'#skF_4',u1_struct_0(A_158))
      | ~ l1_waybel_0('#skF_4',A_158)
      | ~ l1_struct_0(A_158)
      | v2_struct_0(A_158)
      | ~ v7_waybel_0('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ l1_struct_0('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_28,c_263])).

tff(c_268,plain,(
    ! [A_158] :
      ( v1_xboole_0(u1_struct_0(A_158))
      | r1_waybel_0(A_158,'#skF_4',u1_struct_0(A_158))
      | ~ l1_waybel_0('#skF_4',A_158)
      | ~ l1_struct_0(A_158)
      | v2_struct_0(A_158)
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_30,c_265])).

tff(c_270,plain,(
    ! [A_161] :
      ( v1_xboole_0(u1_struct_0(A_161))
      | r1_waybel_0(A_161,'#skF_4',u1_struct_0(A_161))
      | ~ l1_waybel_0('#skF_4',A_161)
      | ~ l1_struct_0(A_161)
      | v2_struct_0(A_161) ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_34,c_268])).

tff(c_26,plain,(
    ~ r1_waybel_0('#skF_3','#skF_4',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_275,plain,
    ( v1_xboole_0(u1_struct_0('#skF_3'))
    | ~ l1_waybel_0('#skF_4','#skF_3')
    | ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_270,c_26])).

tff(c_280,plain,
    ( v1_xboole_0(u1_struct_0('#skF_3'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_28,c_275])).

tff(c_281,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_280])).

tff(c_10,plain,(
    ! [A_3] :
      ( ~ v1_xboole_0(u1_struct_0(A_3))
      | ~ l1_struct_0(A_3)
      | v2_struct_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_288,plain,
    ( ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_281,c_10])).

tff(c_297,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_288])).

tff(c_299,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_297])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:18:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.47/1.37  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.47/1.38  
% 2.47/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.47/1.38  %$ r1_waybel_0 > r1_orders_2 > r2_hidden > m1_subset_1 > l1_waybel_0 > v7_waybel_0 > v4_orders_2 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > k2_waybel_0 > o_2_2_yellow_6 > #nlpp > u1_struct_0 > #skF_3 > #skF_2 > #skF_4 > #skF_1
% 2.47/1.38  
% 2.47/1.38  %Foreground sorts:
% 2.47/1.38  
% 2.47/1.38  
% 2.47/1.38  %Background operators:
% 2.47/1.38  
% 2.47/1.38  
% 2.47/1.38  %Foreground operators:
% 2.47/1.38  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.47/1.38  tff(o_2_2_yellow_6, type, o_2_2_yellow_6: ($i * $i) > $i).
% 2.47/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.47/1.38  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.47/1.38  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 2.47/1.38  tff(k2_waybel_0, type, k2_waybel_0: ($i * $i * $i) > $i).
% 2.47/1.38  tff(v7_waybel_0, type, v7_waybel_0: $i > $o).
% 2.47/1.38  tff(r1_waybel_0, type, r1_waybel_0: ($i * $i * $i) > $o).
% 2.47/1.38  tff('#skF_3', type, '#skF_3': $i).
% 2.47/1.38  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.47/1.38  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.47/1.38  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.47/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.47/1.38  tff(l1_waybel_0, type, l1_waybel_0: ($i * $i) > $o).
% 2.47/1.38  tff('#skF_4', type, '#skF_4': $i).
% 2.47/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.47/1.38  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 2.47/1.38  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.47/1.38  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.47/1.38  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.47/1.38  
% 2.76/1.40  tff(f_118, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => r1_waybel_0(A, B, u1_struct_0(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_yellow_6)).
% 2.76/1.40  tff(f_100, axiom, (![A, B]: ((((((~v2_struct_0(A) & l1_struct_0(A)) & ~v2_struct_0(B)) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => m1_subset_1(o_2_2_yellow_6(A, B), u1_struct_0(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_o_2_2_yellow_6)).
% 2.76/1.40  tff(f_70, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((~v2_struct_0(B) & l1_waybel_0(B, A)) => (![C]: (r1_waybel_0(A, B, C) <=> (?[D]: (m1_subset_1(D, u1_struct_0(B)) & (![E]: (m1_subset_1(E, u1_struct_0(B)) => (r1_orders_2(B, D, E) => r2_hidden(k2_waybel_0(A, B, E), C)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d11_waybel_0)).
% 2.76/1.40  tff(f_84, axiom, (![A, B, C]: (((((~v2_struct_0(A) & l1_struct_0(A)) & ~v2_struct_0(B)) & l1_waybel_0(B, A)) & m1_subset_1(C, u1_struct_0(B))) => m1_subset_1(k2_waybel_0(A, B, C), u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_waybel_0)).
% 2.76/1.40  tff(f_38, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 2.76/1.40  tff(f_46, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 2.76/1.40  tff(c_38, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.76/1.40  tff(c_36, plain, (l1_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.76/1.40  tff(c_28, plain, (l1_waybel_0('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.76/1.40  tff(c_34, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.76/1.40  tff(c_32, plain, (v4_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.76/1.40  tff(c_30, plain, (v7_waybel_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.76/1.40  tff(c_24, plain, (![A_60, B_61]: (m1_subset_1(o_2_2_yellow_6(A_60, B_61), u1_struct_0(B_61)) | ~l1_waybel_0(B_61, A_60) | ~v7_waybel_0(B_61) | ~v4_orders_2(B_61) | v2_struct_0(B_61) | ~l1_struct_0(A_60) | v2_struct_0(A_60))), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.76/1.40  tff(c_20, plain, (![A_4, B_32, C_46, D_53]: (m1_subset_1('#skF_1'(A_4, B_32, C_46, D_53), u1_struct_0(B_32)) | r1_waybel_0(A_4, B_32, C_46) | ~m1_subset_1(D_53, u1_struct_0(B_32)) | ~l1_waybel_0(B_32, A_4) | v2_struct_0(B_32) | ~l1_struct_0(A_4) | v2_struct_0(A_4))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.76/1.40  tff(c_22, plain, (![A_57, B_58, C_59]: (m1_subset_1(k2_waybel_0(A_57, B_58, C_59), u1_struct_0(A_57)) | ~m1_subset_1(C_59, u1_struct_0(B_58)) | ~l1_waybel_0(B_58, A_57) | v2_struct_0(B_58) | ~l1_struct_0(A_57) | v2_struct_0(A_57))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.76/1.40  tff(c_4, plain, (![B_2, A_1]: (r2_hidden(B_2, A_1) | ~m1_subset_1(B_2, A_1) | v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.76/1.40  tff(c_75, plain, (![A_93, B_94, C_95, D_96]: (~r2_hidden(k2_waybel_0(A_93, B_94, '#skF_1'(A_93, B_94, C_95, D_96)), C_95) | r1_waybel_0(A_93, B_94, C_95) | ~m1_subset_1(D_96, u1_struct_0(B_94)) | ~l1_waybel_0(B_94, A_93) | v2_struct_0(B_94) | ~l1_struct_0(A_93) | v2_struct_0(A_93))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.76/1.40  tff(c_99, plain, (![A_105, B_106, A_107, D_108]: (r1_waybel_0(A_105, B_106, A_107) | ~m1_subset_1(D_108, u1_struct_0(B_106)) | ~l1_waybel_0(B_106, A_105) | v2_struct_0(B_106) | ~l1_struct_0(A_105) | v2_struct_0(A_105) | ~m1_subset_1(k2_waybel_0(A_105, B_106, '#skF_1'(A_105, B_106, A_107, D_108)), A_107) | v1_xboole_0(A_107))), inference(resolution, [status(thm)], [c_4, c_75])).
% 2.76/1.40  tff(c_116, plain, (![A_113, B_114, D_115]: (r1_waybel_0(A_113, B_114, u1_struct_0(A_113)) | ~m1_subset_1(D_115, u1_struct_0(B_114)) | v1_xboole_0(u1_struct_0(A_113)) | ~m1_subset_1('#skF_1'(A_113, B_114, u1_struct_0(A_113), D_115), u1_struct_0(B_114)) | ~l1_waybel_0(B_114, A_113) | v2_struct_0(B_114) | ~l1_struct_0(A_113) | v2_struct_0(A_113))), inference(resolution, [status(thm)], [c_22, c_99])).
% 2.76/1.40  tff(c_136, plain, (![A_121, B_122, D_123]: (v1_xboole_0(u1_struct_0(A_121)) | r1_waybel_0(A_121, B_122, u1_struct_0(A_121)) | ~m1_subset_1(D_123, u1_struct_0(B_122)) | ~l1_waybel_0(B_122, A_121) | v2_struct_0(B_122) | ~l1_struct_0(A_121) | v2_struct_0(A_121))), inference(resolution, [status(thm)], [c_20, c_116])).
% 2.76/1.40  tff(c_263, plain, (![A_158, B_159, A_160]: (v1_xboole_0(u1_struct_0(A_158)) | r1_waybel_0(A_158, B_159, u1_struct_0(A_158)) | ~l1_waybel_0(B_159, A_158) | ~l1_struct_0(A_158) | v2_struct_0(A_158) | ~l1_waybel_0(B_159, A_160) | ~v7_waybel_0(B_159) | ~v4_orders_2(B_159) | v2_struct_0(B_159) | ~l1_struct_0(A_160) | v2_struct_0(A_160))), inference(resolution, [status(thm)], [c_24, c_136])).
% 2.76/1.40  tff(c_265, plain, (![A_158]: (v1_xboole_0(u1_struct_0(A_158)) | r1_waybel_0(A_158, '#skF_4', u1_struct_0(A_158)) | ~l1_waybel_0('#skF_4', A_158) | ~l1_struct_0(A_158) | v2_struct_0(A_158) | ~v7_waybel_0('#skF_4') | ~v4_orders_2('#skF_4') | v2_struct_0('#skF_4') | ~l1_struct_0('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_28, c_263])).
% 2.76/1.40  tff(c_268, plain, (![A_158]: (v1_xboole_0(u1_struct_0(A_158)) | r1_waybel_0(A_158, '#skF_4', u1_struct_0(A_158)) | ~l1_waybel_0('#skF_4', A_158) | ~l1_struct_0(A_158) | v2_struct_0(A_158) | v2_struct_0('#skF_4') | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_32, c_30, c_265])).
% 2.76/1.40  tff(c_270, plain, (![A_161]: (v1_xboole_0(u1_struct_0(A_161)) | r1_waybel_0(A_161, '#skF_4', u1_struct_0(A_161)) | ~l1_waybel_0('#skF_4', A_161) | ~l1_struct_0(A_161) | v2_struct_0(A_161))), inference(negUnitSimplification, [status(thm)], [c_38, c_34, c_268])).
% 2.76/1.40  tff(c_26, plain, (~r1_waybel_0('#skF_3', '#skF_4', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.76/1.40  tff(c_275, plain, (v1_xboole_0(u1_struct_0('#skF_3')) | ~l1_waybel_0('#skF_4', '#skF_3') | ~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_270, c_26])).
% 2.76/1.40  tff(c_280, plain, (v1_xboole_0(u1_struct_0('#skF_3')) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_28, c_275])).
% 2.76/1.40  tff(c_281, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_38, c_280])).
% 2.76/1.40  tff(c_10, plain, (![A_3]: (~v1_xboole_0(u1_struct_0(A_3)) | ~l1_struct_0(A_3) | v2_struct_0(A_3))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.76/1.40  tff(c_288, plain, (~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_281, c_10])).
% 2.76/1.40  tff(c_297, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_288])).
% 2.76/1.40  tff(c_299, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_297])).
% 2.76/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.76/1.40  
% 2.76/1.40  Inference rules
% 2.76/1.40  ----------------------
% 2.76/1.40  #Ref     : 0
% 2.76/1.40  #Sup     : 52
% 2.76/1.40  #Fact    : 0
% 2.76/1.40  #Define  : 0
% 2.76/1.40  #Split   : 2
% 2.76/1.40  #Chain   : 0
% 2.76/1.40  #Close   : 0
% 2.76/1.40  
% 2.76/1.40  Ordering : KBO
% 2.76/1.40  
% 2.76/1.40  Simplification rules
% 2.76/1.40  ----------------------
% 2.76/1.40  #Subsume      : 18
% 2.76/1.40  #Demod        : 13
% 2.76/1.40  #Tautology    : 5
% 2.76/1.40  #SimpNegUnit  : 19
% 2.76/1.40  #BackRed      : 4
% 2.76/1.40  
% 2.76/1.40  #Partial instantiations: 0
% 2.76/1.40  #Strategies tried      : 1
% 2.76/1.40  
% 2.76/1.40  Timing (in seconds)
% 2.76/1.40  ----------------------
% 2.76/1.40  Preprocessing        : 0.32
% 2.76/1.40  Parsing              : 0.18
% 2.76/1.40  CNF conversion       : 0.03
% 2.76/1.40  Main loop            : 0.28
% 2.76/1.40  Inferencing          : 0.12
% 2.76/1.40  Reduction            : 0.06
% 2.76/1.40  Demodulation         : 0.03
% 2.76/1.40  BG Simplification    : 0.02
% 2.76/1.40  Subsumption          : 0.07
% 2.76/1.40  Abstraction          : 0.01
% 2.76/1.40  MUC search           : 0.00
% 2.76/1.40  Cooper               : 0.00
% 2.76/1.40  Total                : 0.63
% 2.76/1.40  Index Insertion      : 0.00
% 2.76/1.40  Index Deletion       : 0.00
% 2.76/1.40  Index Matching       : 0.00
% 2.76/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
