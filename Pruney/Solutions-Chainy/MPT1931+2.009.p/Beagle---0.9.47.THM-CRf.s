%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:48 EST 2020

% Result     : Theorem 2.14s
% Output     : CNFRefutation 2.32s
% Verified   : 
% Statistics : Number of formulae       :   52 (  69 expanded)
%              Number of leaves         :   26 (  38 expanded)
%              Depth                    :   14
%              Number of atoms          :  142 ( 233 expanded)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_yellow_6)).

tff(f_93,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A)
        & ~ v2_struct_0(B)
        & v4_orders_2(B)
        & v7_waybel_0(B)
        & l1_waybel_0(B,A) )
     => m1_subset_1(o_2_2_yellow_6(A,B),u1_struct_0(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_o_2_2_yellow_6)).

tff(f_63,axiom,(
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

tff(f_77,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A)
        & ~ v2_struct_0(B)
        & l1_waybel_0(B,A)
        & m1_subset_1(C,u1_struct_0(B)) )
     => m1_subset_1(k2_waybel_0(A,B,C),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_waybel_0)).

tff(f_31,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_39,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(c_32,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_30,plain,(
    l1_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_22,plain,(
    l1_waybel_0('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_28,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_26,plain,(
    v4_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_24,plain,(
    v7_waybel_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_18,plain,(
    ! [A_60,B_61] :
      ( m1_subset_1(o_2_2_yellow_6(A_60,B_61),u1_struct_0(B_61))
      | ~ l1_waybel_0(B_61,A_60)
      | ~ v7_waybel_0(B_61)
      | ~ v4_orders_2(B_61)
      | v2_struct_0(B_61)
      | ~ l1_struct_0(A_60)
      | v2_struct_0(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_14,plain,(
    ! [A_4,B_32,C_46,D_53] :
      ( m1_subset_1('#skF_1'(A_4,B_32,C_46,D_53),u1_struct_0(B_32))
      | r1_waybel_0(A_4,B_32,C_46)
      | ~ m1_subset_1(D_53,u1_struct_0(B_32))
      | ~ l1_waybel_0(B_32,A_4)
      | v2_struct_0(B_32)
      | ~ l1_struct_0(A_4)
      | v2_struct_0(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_16,plain,(
    ! [A_57,B_58,C_59] :
      ( m1_subset_1(k2_waybel_0(A_57,B_58,C_59),u1_struct_0(A_57))
      | ~ m1_subset_1(C_59,u1_struct_0(B_58))
      | ~ l1_waybel_0(B_58,A_57)
      | v2_struct_0(B_58)
      | ~ l1_struct_0(A_57)
      | v2_struct_0(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r2_hidden(A_1,B_2)
      | v1_xboole_0(B_2)
      | ~ m1_subset_1(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_40,plain,(
    ! [A_82,B_83,C_84,D_85] :
      ( ~ r2_hidden(k2_waybel_0(A_82,B_83,'#skF_1'(A_82,B_83,C_84,D_85)),C_84)
      | r1_waybel_0(A_82,B_83,C_84)
      | ~ m1_subset_1(D_85,u1_struct_0(B_83))
      | ~ l1_waybel_0(B_83,A_82)
      | v2_struct_0(B_83)
      | ~ l1_struct_0(A_82)
      | v2_struct_0(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_52,plain,(
    ! [A_90,B_91,B_92,D_93] :
      ( r1_waybel_0(A_90,B_91,B_92)
      | ~ m1_subset_1(D_93,u1_struct_0(B_91))
      | ~ l1_waybel_0(B_91,A_90)
      | v2_struct_0(B_91)
      | ~ l1_struct_0(A_90)
      | v2_struct_0(A_90)
      | v1_xboole_0(B_92)
      | ~ m1_subset_1(k2_waybel_0(A_90,B_91,'#skF_1'(A_90,B_91,B_92,D_93)),B_92) ) ),
    inference(resolution,[status(thm)],[c_2,c_40])).

tff(c_58,plain,(
    ! [A_94,B_95,D_96] :
      ( r1_waybel_0(A_94,B_95,u1_struct_0(A_94))
      | ~ m1_subset_1(D_96,u1_struct_0(B_95))
      | v1_xboole_0(u1_struct_0(A_94))
      | ~ m1_subset_1('#skF_1'(A_94,B_95,u1_struct_0(A_94),D_96),u1_struct_0(B_95))
      | ~ l1_waybel_0(B_95,A_94)
      | v2_struct_0(B_95)
      | ~ l1_struct_0(A_94)
      | v2_struct_0(A_94) ) ),
    inference(resolution,[status(thm)],[c_16,c_52])).

tff(c_64,plain,(
    ! [A_97,B_98,D_99] :
      ( v1_xboole_0(u1_struct_0(A_97))
      | r1_waybel_0(A_97,B_98,u1_struct_0(A_97))
      | ~ m1_subset_1(D_99,u1_struct_0(B_98))
      | ~ l1_waybel_0(B_98,A_97)
      | v2_struct_0(B_98)
      | ~ l1_struct_0(A_97)
      | v2_struct_0(A_97) ) ),
    inference(resolution,[status(thm)],[c_14,c_58])).

tff(c_91,plain,(
    ! [A_108,B_109,A_110] :
      ( v1_xboole_0(u1_struct_0(A_108))
      | r1_waybel_0(A_108,B_109,u1_struct_0(A_108))
      | ~ l1_waybel_0(B_109,A_108)
      | ~ l1_struct_0(A_108)
      | v2_struct_0(A_108)
      | ~ l1_waybel_0(B_109,A_110)
      | ~ v7_waybel_0(B_109)
      | ~ v4_orders_2(B_109)
      | v2_struct_0(B_109)
      | ~ l1_struct_0(A_110)
      | v2_struct_0(A_110) ) ),
    inference(resolution,[status(thm)],[c_18,c_64])).

tff(c_93,plain,(
    ! [A_108] :
      ( v1_xboole_0(u1_struct_0(A_108))
      | r1_waybel_0(A_108,'#skF_4',u1_struct_0(A_108))
      | ~ l1_waybel_0('#skF_4',A_108)
      | ~ l1_struct_0(A_108)
      | v2_struct_0(A_108)
      | ~ v7_waybel_0('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ l1_struct_0('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_22,c_91])).

tff(c_96,plain,(
    ! [A_108] :
      ( v1_xboole_0(u1_struct_0(A_108))
      | r1_waybel_0(A_108,'#skF_4',u1_struct_0(A_108))
      | ~ l1_waybel_0('#skF_4',A_108)
      | ~ l1_struct_0(A_108)
      | v2_struct_0(A_108)
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_26,c_24,c_93])).

tff(c_98,plain,(
    ! [A_111] :
      ( v1_xboole_0(u1_struct_0(A_111))
      | r1_waybel_0(A_111,'#skF_4',u1_struct_0(A_111))
      | ~ l1_waybel_0('#skF_4',A_111)
      | ~ l1_struct_0(A_111)
      | v2_struct_0(A_111) ) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_28,c_96])).

tff(c_20,plain,(
    ~ r1_waybel_0('#skF_3','#skF_4',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_103,plain,
    ( v1_xboole_0(u1_struct_0('#skF_3'))
    | ~ l1_waybel_0('#skF_4','#skF_3')
    | ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_98,c_20])).

tff(c_108,plain,
    ( v1_xboole_0(u1_struct_0('#skF_3'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_22,c_103])).

tff(c_109,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_108])).

tff(c_4,plain,(
    ! [A_3] :
      ( ~ v1_xboole_0(u1_struct_0(A_3))
      | ~ l1_struct_0(A_3)
      | v2_struct_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_112,plain,
    ( ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_109,c_4])).

tff(c_115,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_112])).

tff(c_117,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_115])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:23:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.14/1.21  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.14/1.22  
% 2.14/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.14/1.22  %$ r1_waybel_0 > r1_orders_2 > r2_hidden > m1_subset_1 > l1_waybel_0 > v7_waybel_0 > v4_orders_2 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > k2_waybel_0 > o_2_2_yellow_6 > #nlpp > u1_struct_0 > #skF_3 > #skF_2 > #skF_4 > #skF_1
% 2.14/1.22  
% 2.14/1.22  %Foreground sorts:
% 2.14/1.22  
% 2.14/1.22  
% 2.14/1.22  %Background operators:
% 2.14/1.22  
% 2.14/1.22  
% 2.14/1.22  %Foreground operators:
% 2.14/1.22  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.14/1.22  tff(o_2_2_yellow_6, type, o_2_2_yellow_6: ($i * $i) > $i).
% 2.14/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.14/1.22  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.14/1.22  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 2.14/1.22  tff(k2_waybel_0, type, k2_waybel_0: ($i * $i * $i) > $i).
% 2.14/1.22  tff(v7_waybel_0, type, v7_waybel_0: $i > $o).
% 2.14/1.22  tff(r1_waybel_0, type, r1_waybel_0: ($i * $i * $i) > $o).
% 2.14/1.22  tff('#skF_3', type, '#skF_3': $i).
% 2.14/1.22  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.14/1.22  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.14/1.22  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.14/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.14/1.22  tff(l1_waybel_0, type, l1_waybel_0: ($i * $i) > $o).
% 2.14/1.22  tff('#skF_4', type, '#skF_4': $i).
% 2.14/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.14/1.22  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 2.14/1.22  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.14/1.22  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.14/1.22  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.14/1.22  
% 2.32/1.23  tff(f_111, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => r1_waybel_0(A, B, u1_struct_0(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_yellow_6)).
% 2.32/1.23  tff(f_93, axiom, (![A, B]: ((((((~v2_struct_0(A) & l1_struct_0(A)) & ~v2_struct_0(B)) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => m1_subset_1(o_2_2_yellow_6(A, B), u1_struct_0(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_o_2_2_yellow_6)).
% 2.32/1.23  tff(f_63, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((~v2_struct_0(B) & l1_waybel_0(B, A)) => (![C]: (r1_waybel_0(A, B, C) <=> (?[D]: (m1_subset_1(D, u1_struct_0(B)) & (![E]: (m1_subset_1(E, u1_struct_0(B)) => (r1_orders_2(B, D, E) => r2_hidden(k2_waybel_0(A, B, E), C)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d11_waybel_0)).
% 2.32/1.23  tff(f_77, axiom, (![A, B, C]: (((((~v2_struct_0(A) & l1_struct_0(A)) & ~v2_struct_0(B)) & l1_waybel_0(B, A)) & m1_subset_1(C, u1_struct_0(B))) => m1_subset_1(k2_waybel_0(A, B, C), u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_waybel_0)).
% 2.32/1.23  tff(f_31, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 2.32/1.23  tff(f_39, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 2.32/1.23  tff(c_32, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.32/1.23  tff(c_30, plain, (l1_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.32/1.23  tff(c_22, plain, (l1_waybel_0('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.32/1.23  tff(c_28, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.32/1.23  tff(c_26, plain, (v4_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.32/1.23  tff(c_24, plain, (v7_waybel_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.32/1.23  tff(c_18, plain, (![A_60, B_61]: (m1_subset_1(o_2_2_yellow_6(A_60, B_61), u1_struct_0(B_61)) | ~l1_waybel_0(B_61, A_60) | ~v7_waybel_0(B_61) | ~v4_orders_2(B_61) | v2_struct_0(B_61) | ~l1_struct_0(A_60) | v2_struct_0(A_60))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.32/1.23  tff(c_14, plain, (![A_4, B_32, C_46, D_53]: (m1_subset_1('#skF_1'(A_4, B_32, C_46, D_53), u1_struct_0(B_32)) | r1_waybel_0(A_4, B_32, C_46) | ~m1_subset_1(D_53, u1_struct_0(B_32)) | ~l1_waybel_0(B_32, A_4) | v2_struct_0(B_32) | ~l1_struct_0(A_4) | v2_struct_0(A_4))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.32/1.23  tff(c_16, plain, (![A_57, B_58, C_59]: (m1_subset_1(k2_waybel_0(A_57, B_58, C_59), u1_struct_0(A_57)) | ~m1_subset_1(C_59, u1_struct_0(B_58)) | ~l1_waybel_0(B_58, A_57) | v2_struct_0(B_58) | ~l1_struct_0(A_57) | v2_struct_0(A_57))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.32/1.23  tff(c_2, plain, (![A_1, B_2]: (r2_hidden(A_1, B_2) | v1_xboole_0(B_2) | ~m1_subset_1(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.32/1.23  tff(c_40, plain, (![A_82, B_83, C_84, D_85]: (~r2_hidden(k2_waybel_0(A_82, B_83, '#skF_1'(A_82, B_83, C_84, D_85)), C_84) | r1_waybel_0(A_82, B_83, C_84) | ~m1_subset_1(D_85, u1_struct_0(B_83)) | ~l1_waybel_0(B_83, A_82) | v2_struct_0(B_83) | ~l1_struct_0(A_82) | v2_struct_0(A_82))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.32/1.23  tff(c_52, plain, (![A_90, B_91, B_92, D_93]: (r1_waybel_0(A_90, B_91, B_92) | ~m1_subset_1(D_93, u1_struct_0(B_91)) | ~l1_waybel_0(B_91, A_90) | v2_struct_0(B_91) | ~l1_struct_0(A_90) | v2_struct_0(A_90) | v1_xboole_0(B_92) | ~m1_subset_1(k2_waybel_0(A_90, B_91, '#skF_1'(A_90, B_91, B_92, D_93)), B_92))), inference(resolution, [status(thm)], [c_2, c_40])).
% 2.32/1.23  tff(c_58, plain, (![A_94, B_95, D_96]: (r1_waybel_0(A_94, B_95, u1_struct_0(A_94)) | ~m1_subset_1(D_96, u1_struct_0(B_95)) | v1_xboole_0(u1_struct_0(A_94)) | ~m1_subset_1('#skF_1'(A_94, B_95, u1_struct_0(A_94), D_96), u1_struct_0(B_95)) | ~l1_waybel_0(B_95, A_94) | v2_struct_0(B_95) | ~l1_struct_0(A_94) | v2_struct_0(A_94))), inference(resolution, [status(thm)], [c_16, c_52])).
% 2.32/1.23  tff(c_64, plain, (![A_97, B_98, D_99]: (v1_xboole_0(u1_struct_0(A_97)) | r1_waybel_0(A_97, B_98, u1_struct_0(A_97)) | ~m1_subset_1(D_99, u1_struct_0(B_98)) | ~l1_waybel_0(B_98, A_97) | v2_struct_0(B_98) | ~l1_struct_0(A_97) | v2_struct_0(A_97))), inference(resolution, [status(thm)], [c_14, c_58])).
% 2.32/1.23  tff(c_91, plain, (![A_108, B_109, A_110]: (v1_xboole_0(u1_struct_0(A_108)) | r1_waybel_0(A_108, B_109, u1_struct_0(A_108)) | ~l1_waybel_0(B_109, A_108) | ~l1_struct_0(A_108) | v2_struct_0(A_108) | ~l1_waybel_0(B_109, A_110) | ~v7_waybel_0(B_109) | ~v4_orders_2(B_109) | v2_struct_0(B_109) | ~l1_struct_0(A_110) | v2_struct_0(A_110))), inference(resolution, [status(thm)], [c_18, c_64])).
% 2.32/1.23  tff(c_93, plain, (![A_108]: (v1_xboole_0(u1_struct_0(A_108)) | r1_waybel_0(A_108, '#skF_4', u1_struct_0(A_108)) | ~l1_waybel_0('#skF_4', A_108) | ~l1_struct_0(A_108) | v2_struct_0(A_108) | ~v7_waybel_0('#skF_4') | ~v4_orders_2('#skF_4') | v2_struct_0('#skF_4') | ~l1_struct_0('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_22, c_91])).
% 2.32/1.23  tff(c_96, plain, (![A_108]: (v1_xboole_0(u1_struct_0(A_108)) | r1_waybel_0(A_108, '#skF_4', u1_struct_0(A_108)) | ~l1_waybel_0('#skF_4', A_108) | ~l1_struct_0(A_108) | v2_struct_0(A_108) | v2_struct_0('#skF_4') | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_26, c_24, c_93])).
% 2.32/1.23  tff(c_98, plain, (![A_111]: (v1_xboole_0(u1_struct_0(A_111)) | r1_waybel_0(A_111, '#skF_4', u1_struct_0(A_111)) | ~l1_waybel_0('#skF_4', A_111) | ~l1_struct_0(A_111) | v2_struct_0(A_111))), inference(negUnitSimplification, [status(thm)], [c_32, c_28, c_96])).
% 2.32/1.23  tff(c_20, plain, (~r1_waybel_0('#skF_3', '#skF_4', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.32/1.23  tff(c_103, plain, (v1_xboole_0(u1_struct_0('#skF_3')) | ~l1_waybel_0('#skF_4', '#skF_3') | ~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_98, c_20])).
% 2.32/1.23  tff(c_108, plain, (v1_xboole_0(u1_struct_0('#skF_3')) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_22, c_103])).
% 2.32/1.23  tff(c_109, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_32, c_108])).
% 2.32/1.23  tff(c_4, plain, (![A_3]: (~v1_xboole_0(u1_struct_0(A_3)) | ~l1_struct_0(A_3) | v2_struct_0(A_3))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.32/1.23  tff(c_112, plain, (~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_109, c_4])).
% 2.32/1.23  tff(c_115, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_112])).
% 2.32/1.23  tff(c_117, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_115])).
% 2.32/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.32/1.23  
% 2.32/1.23  Inference rules
% 2.32/1.23  ----------------------
% 2.32/1.23  #Ref     : 0
% 2.32/1.23  #Sup     : 16
% 2.32/1.23  #Fact    : 0
% 2.32/1.23  #Define  : 0
% 2.32/1.23  #Split   : 0
% 2.32/1.23  #Chain   : 0
% 2.32/1.23  #Close   : 0
% 2.32/1.23  
% 2.32/1.23  Ordering : KBO
% 2.32/1.23  
% 2.32/1.23  Simplification rules
% 2.32/1.23  ----------------------
% 2.32/1.23  #Subsume      : 4
% 2.32/1.23  #Demod        : 6
% 2.32/1.23  #Tautology    : 0
% 2.32/1.23  #SimpNegUnit  : 4
% 2.32/1.23  #BackRed      : 0
% 2.32/1.23  
% 2.32/1.23  #Partial instantiations: 0
% 2.32/1.23  #Strategies tried      : 1
% 2.32/1.23  
% 2.32/1.23  Timing (in seconds)
% 2.32/1.23  ----------------------
% 2.32/1.24  Preprocessing        : 0.27
% 2.32/1.24  Parsing              : 0.15
% 2.32/1.24  CNF conversion       : 0.03
% 2.32/1.24  Main loop            : 0.17
% 2.32/1.24  Inferencing          : 0.08
% 2.32/1.24  Reduction            : 0.04
% 2.32/1.24  Demodulation         : 0.03
% 2.32/1.24  BG Simplification    : 0.02
% 2.32/1.24  Subsumption          : 0.03
% 2.32/1.24  Abstraction          : 0.01
% 2.32/1.24  MUC search           : 0.00
% 2.32/1.24  Cooper               : 0.00
% 2.32/1.24  Total                : 0.48
% 2.32/1.24  Index Insertion      : 0.00
% 2.32/1.24  Index Deletion       : 0.00
% 2.32/1.24  Index Matching       : 0.00
% 2.32/1.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
