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

% Result     : Theorem 2.15s
% Output     : CNFRefutation 2.26s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 105 expanded)
%              Number of leaves         :   31 (  51 expanded)
%              Depth                    :   13
%              Number of atoms          :  142 ( 363 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_waybel_0 > r1_orders_2 > r2_hidden > m1_subset_1 > l1_waybel_0 > v7_waybel_0 > v4_orders_2 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > k2_waybel_0 > k4_yellow_6 > #nlpp > u1_struct_0 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k4_yellow_6,type,(
    k4_yellow_6: ( $i * $i ) > $i )).

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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_waybel_0,type,(
    r1_waybel_0: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

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
    '#skF_3': $i > $i )).

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

tff(f_120,negated_conjecture,(
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

tff(f_88,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ! [B] :
          ( l1_waybel_0(B,A)
         => l1_orders_2(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_waybel_0)).

tff(f_43,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_93,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ? [B] : l1_waybel_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_l1_waybel_0)).

tff(f_102,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A)
        & l1_waybel_0(B,A) )
     => m1_subset_1(k4_yellow_6(A,B),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_yellow_6)).

tff(f_67,axiom,(
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

tff(f_81,axiom,(
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

tff(c_38,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_36,plain,(
    l1_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_28,plain,(
    l1_waybel_0('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_41,plain,(
    ! [B_71,A_72] :
      ( l1_orders_2(B_71)
      | ~ l1_waybel_0(B_71,A_72)
      | ~ l1_struct_0(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_47,plain,
    ( l1_orders_2('#skF_5')
    | ~ l1_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_41])).

tff(c_51,plain,(
    l1_orders_2('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_47])).

tff(c_6,plain,(
    ! [A_4] :
      ( l1_struct_0(A_4)
      | ~ l1_orders_2(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_34,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_22,plain,(
    ! [A_64] :
      ( l1_waybel_0('#skF_3'(A_64),A_64)
      | ~ l1_struct_0(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_24,plain,(
    ! [A_66,B_67] :
      ( m1_subset_1(k4_yellow_6(A_66,B_67),u1_struct_0(A_66))
      | ~ l1_waybel_0(B_67,A_66)
      | ~ l1_struct_0(A_66)
      | v2_struct_0(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_16,plain,(
    ! [A_5,B_33,C_47,D_54] :
      ( m1_subset_1('#skF_1'(A_5,B_33,C_47,D_54),u1_struct_0(B_33))
      | r1_waybel_0(A_5,B_33,C_47)
      | ~ m1_subset_1(D_54,u1_struct_0(B_33))
      | ~ l1_waybel_0(B_33,A_5)
      | v2_struct_0(B_33)
      | ~ l1_struct_0(A_5)
      | v2_struct_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_18,plain,(
    ! [A_58,B_59,C_60] :
      ( m1_subset_1(k2_waybel_0(A_58,B_59,C_60),u1_struct_0(A_58))
      | ~ m1_subset_1(C_60,u1_struct_0(B_59))
      | ~ l1_waybel_0(B_59,A_58)
      | v2_struct_0(B_59)
      | ~ l1_struct_0(A_58)
      | v2_struct_0(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r2_hidden(A_1,B_2)
      | v1_xboole_0(B_2)
      | ~ m1_subset_1(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_60,plain,(
    ! [A_93,B_94,C_95,D_96] :
      ( ~ r2_hidden(k2_waybel_0(A_93,B_94,'#skF_1'(A_93,B_94,C_95,D_96)),C_95)
      | r1_waybel_0(A_93,B_94,C_95)
      | ~ m1_subset_1(D_96,u1_struct_0(B_94))
      | ~ l1_waybel_0(B_94,A_93)
      | v2_struct_0(B_94)
      | ~ l1_struct_0(A_93)
      | v2_struct_0(A_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_66,plain,(
    ! [A_97,B_98,B_99,D_100] :
      ( r1_waybel_0(A_97,B_98,B_99)
      | ~ m1_subset_1(D_100,u1_struct_0(B_98))
      | ~ l1_waybel_0(B_98,A_97)
      | v2_struct_0(B_98)
      | ~ l1_struct_0(A_97)
      | v2_struct_0(A_97)
      | v1_xboole_0(B_99)
      | ~ m1_subset_1(k2_waybel_0(A_97,B_98,'#skF_1'(A_97,B_98,B_99,D_100)),B_99) ) ),
    inference(resolution,[status(thm)],[c_2,c_60])).

tff(c_78,plain,(
    ! [A_105,B_106,D_107] :
      ( r1_waybel_0(A_105,B_106,u1_struct_0(A_105))
      | ~ m1_subset_1(D_107,u1_struct_0(B_106))
      | v1_xboole_0(u1_struct_0(A_105))
      | ~ m1_subset_1('#skF_1'(A_105,B_106,u1_struct_0(A_105),D_107),u1_struct_0(B_106))
      | ~ l1_waybel_0(B_106,A_105)
      | v2_struct_0(B_106)
      | ~ l1_struct_0(A_105)
      | v2_struct_0(A_105) ) ),
    inference(resolution,[status(thm)],[c_18,c_66])).

tff(c_84,plain,(
    ! [A_108,B_109,D_110] :
      ( v1_xboole_0(u1_struct_0(A_108))
      | r1_waybel_0(A_108,B_109,u1_struct_0(A_108))
      | ~ m1_subset_1(D_110,u1_struct_0(B_109))
      | ~ l1_waybel_0(B_109,A_108)
      | v2_struct_0(B_109)
      | ~ l1_struct_0(A_108)
      | v2_struct_0(A_108) ) ),
    inference(resolution,[status(thm)],[c_16,c_78])).

tff(c_97,plain,(
    ! [A_111,A_112,B_113] :
      ( v1_xboole_0(u1_struct_0(A_111))
      | r1_waybel_0(A_111,A_112,u1_struct_0(A_111))
      | ~ l1_waybel_0(A_112,A_111)
      | ~ l1_struct_0(A_111)
      | v2_struct_0(A_111)
      | ~ l1_waybel_0(B_113,A_112)
      | ~ l1_struct_0(A_112)
      | v2_struct_0(A_112) ) ),
    inference(resolution,[status(thm)],[c_24,c_84])).

tff(c_114,plain,(
    ! [A_120,A_121] :
      ( v1_xboole_0(u1_struct_0(A_120))
      | r1_waybel_0(A_120,A_121,u1_struct_0(A_120))
      | ~ l1_waybel_0(A_121,A_120)
      | ~ l1_struct_0(A_120)
      | v2_struct_0(A_120)
      | v2_struct_0(A_121)
      | ~ l1_struct_0(A_121) ) ),
    inference(resolution,[status(thm)],[c_22,c_97])).

tff(c_26,plain,(
    ~ r1_waybel_0('#skF_4','#skF_5',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_117,plain,
    ( v1_xboole_0(u1_struct_0('#skF_4'))
    | ~ l1_waybel_0('#skF_5','#skF_4')
    | ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_5')
    | ~ l1_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_114,c_26])).

tff(c_120,plain,
    ( v1_xboole_0(u1_struct_0('#skF_4'))
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_5')
    | ~ l1_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_28,c_117])).

tff(c_121,plain,
    ( v1_xboole_0(u1_struct_0('#skF_4'))
    | ~ l1_struct_0('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_38,c_120])).

tff(c_122,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_121])).

tff(c_125,plain,(
    ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_6,c_122])).

tff(c_129,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_51,c_125])).

tff(c_130,plain,(
    v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_121])).

tff(c_4,plain,(
    ! [A_3] :
      ( ~ v1_xboole_0(u1_struct_0(A_3))
      | ~ l1_struct_0(A_3)
      | v2_struct_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_134,plain,
    ( ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_130,c_4])).

tff(c_137,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_134])).

tff(c_139,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_137])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:32:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.15/1.24  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.15/1.24  
% 2.15/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.15/1.25  %$ r1_waybel_0 > r1_orders_2 > r2_hidden > m1_subset_1 > l1_waybel_0 > v7_waybel_0 > v4_orders_2 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > k2_waybel_0 > k4_yellow_6 > #nlpp > u1_struct_0 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 2.15/1.25  
% 2.15/1.25  %Foreground sorts:
% 2.15/1.25  
% 2.15/1.25  
% 2.15/1.25  %Background operators:
% 2.15/1.25  
% 2.15/1.25  
% 2.15/1.25  %Foreground operators:
% 2.15/1.25  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.15/1.25  tff(k4_yellow_6, type, k4_yellow_6: ($i * $i) > $i).
% 2.15/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.15/1.25  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.15/1.25  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 2.15/1.25  tff(k2_waybel_0, type, k2_waybel_0: ($i * $i * $i) > $i).
% 2.15/1.25  tff(v7_waybel_0, type, v7_waybel_0: $i > $o).
% 2.15/1.25  tff('#skF_5', type, '#skF_5': $i).
% 2.15/1.25  tff(r1_waybel_0, type, r1_waybel_0: ($i * $i * $i) > $o).
% 2.15/1.25  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.15/1.25  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.15/1.25  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.15/1.25  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.15/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.15/1.25  tff(l1_waybel_0, type, l1_waybel_0: ($i * $i) > $o).
% 2.15/1.25  tff('#skF_4', type, '#skF_4': $i).
% 2.15/1.25  tff('#skF_3', type, '#skF_3': $i > $i).
% 2.15/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.15/1.25  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 2.15/1.25  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.15/1.25  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.15/1.25  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.15/1.25  
% 2.26/1.26  tff(f_120, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => r1_waybel_0(A, B, u1_struct_0(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_yellow_6)).
% 2.26/1.26  tff(f_88, axiom, (![A]: (l1_struct_0(A) => (![B]: (l1_waybel_0(B, A) => l1_orders_2(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_waybel_0)).
% 2.26/1.26  tff(f_43, axiom, (![A]: (l1_orders_2(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 2.26/1.26  tff(f_93, axiom, (![A]: (l1_struct_0(A) => (?[B]: l1_waybel_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', existence_l1_waybel_0)).
% 2.26/1.26  tff(f_102, axiom, (![A, B]: (((~v2_struct_0(A) & l1_struct_0(A)) & l1_waybel_0(B, A)) => m1_subset_1(k4_yellow_6(A, B), u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_yellow_6)).
% 2.26/1.26  tff(f_67, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((~v2_struct_0(B) & l1_waybel_0(B, A)) => (![C]: (r1_waybel_0(A, B, C) <=> (?[D]: (m1_subset_1(D, u1_struct_0(B)) & (![E]: (m1_subset_1(E, u1_struct_0(B)) => (r1_orders_2(B, D, E) => r2_hidden(k2_waybel_0(A, B, E), C)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d11_waybel_0)).
% 2.26/1.26  tff(f_81, axiom, (![A, B, C]: (((((~v2_struct_0(A) & l1_struct_0(A)) & ~v2_struct_0(B)) & l1_waybel_0(B, A)) & m1_subset_1(C, u1_struct_0(B))) => m1_subset_1(k2_waybel_0(A, B, C), u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_waybel_0)).
% 2.26/1.26  tff(f_31, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 2.26/1.26  tff(f_39, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 2.26/1.26  tff(c_38, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_120])).
% 2.26/1.26  tff(c_36, plain, (l1_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_120])).
% 2.26/1.26  tff(c_28, plain, (l1_waybel_0('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_120])).
% 2.26/1.26  tff(c_41, plain, (![B_71, A_72]: (l1_orders_2(B_71) | ~l1_waybel_0(B_71, A_72) | ~l1_struct_0(A_72))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.26/1.26  tff(c_47, plain, (l1_orders_2('#skF_5') | ~l1_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_28, c_41])).
% 2.26/1.26  tff(c_51, plain, (l1_orders_2('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_47])).
% 2.26/1.26  tff(c_6, plain, (![A_4]: (l1_struct_0(A_4) | ~l1_orders_2(A_4))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.26/1.26  tff(c_34, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_120])).
% 2.26/1.26  tff(c_22, plain, (![A_64]: (l1_waybel_0('#skF_3'(A_64), A_64) | ~l1_struct_0(A_64))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.26/1.26  tff(c_24, plain, (![A_66, B_67]: (m1_subset_1(k4_yellow_6(A_66, B_67), u1_struct_0(A_66)) | ~l1_waybel_0(B_67, A_66) | ~l1_struct_0(A_66) | v2_struct_0(A_66))), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.26/1.26  tff(c_16, plain, (![A_5, B_33, C_47, D_54]: (m1_subset_1('#skF_1'(A_5, B_33, C_47, D_54), u1_struct_0(B_33)) | r1_waybel_0(A_5, B_33, C_47) | ~m1_subset_1(D_54, u1_struct_0(B_33)) | ~l1_waybel_0(B_33, A_5) | v2_struct_0(B_33) | ~l1_struct_0(A_5) | v2_struct_0(A_5))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.26/1.26  tff(c_18, plain, (![A_58, B_59, C_60]: (m1_subset_1(k2_waybel_0(A_58, B_59, C_60), u1_struct_0(A_58)) | ~m1_subset_1(C_60, u1_struct_0(B_59)) | ~l1_waybel_0(B_59, A_58) | v2_struct_0(B_59) | ~l1_struct_0(A_58) | v2_struct_0(A_58))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.26/1.26  tff(c_2, plain, (![A_1, B_2]: (r2_hidden(A_1, B_2) | v1_xboole_0(B_2) | ~m1_subset_1(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.26/1.26  tff(c_60, plain, (![A_93, B_94, C_95, D_96]: (~r2_hidden(k2_waybel_0(A_93, B_94, '#skF_1'(A_93, B_94, C_95, D_96)), C_95) | r1_waybel_0(A_93, B_94, C_95) | ~m1_subset_1(D_96, u1_struct_0(B_94)) | ~l1_waybel_0(B_94, A_93) | v2_struct_0(B_94) | ~l1_struct_0(A_93) | v2_struct_0(A_93))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.26/1.26  tff(c_66, plain, (![A_97, B_98, B_99, D_100]: (r1_waybel_0(A_97, B_98, B_99) | ~m1_subset_1(D_100, u1_struct_0(B_98)) | ~l1_waybel_0(B_98, A_97) | v2_struct_0(B_98) | ~l1_struct_0(A_97) | v2_struct_0(A_97) | v1_xboole_0(B_99) | ~m1_subset_1(k2_waybel_0(A_97, B_98, '#skF_1'(A_97, B_98, B_99, D_100)), B_99))), inference(resolution, [status(thm)], [c_2, c_60])).
% 2.26/1.26  tff(c_78, plain, (![A_105, B_106, D_107]: (r1_waybel_0(A_105, B_106, u1_struct_0(A_105)) | ~m1_subset_1(D_107, u1_struct_0(B_106)) | v1_xboole_0(u1_struct_0(A_105)) | ~m1_subset_1('#skF_1'(A_105, B_106, u1_struct_0(A_105), D_107), u1_struct_0(B_106)) | ~l1_waybel_0(B_106, A_105) | v2_struct_0(B_106) | ~l1_struct_0(A_105) | v2_struct_0(A_105))), inference(resolution, [status(thm)], [c_18, c_66])).
% 2.26/1.26  tff(c_84, plain, (![A_108, B_109, D_110]: (v1_xboole_0(u1_struct_0(A_108)) | r1_waybel_0(A_108, B_109, u1_struct_0(A_108)) | ~m1_subset_1(D_110, u1_struct_0(B_109)) | ~l1_waybel_0(B_109, A_108) | v2_struct_0(B_109) | ~l1_struct_0(A_108) | v2_struct_0(A_108))), inference(resolution, [status(thm)], [c_16, c_78])).
% 2.26/1.26  tff(c_97, plain, (![A_111, A_112, B_113]: (v1_xboole_0(u1_struct_0(A_111)) | r1_waybel_0(A_111, A_112, u1_struct_0(A_111)) | ~l1_waybel_0(A_112, A_111) | ~l1_struct_0(A_111) | v2_struct_0(A_111) | ~l1_waybel_0(B_113, A_112) | ~l1_struct_0(A_112) | v2_struct_0(A_112))), inference(resolution, [status(thm)], [c_24, c_84])).
% 2.26/1.26  tff(c_114, plain, (![A_120, A_121]: (v1_xboole_0(u1_struct_0(A_120)) | r1_waybel_0(A_120, A_121, u1_struct_0(A_120)) | ~l1_waybel_0(A_121, A_120) | ~l1_struct_0(A_120) | v2_struct_0(A_120) | v2_struct_0(A_121) | ~l1_struct_0(A_121))), inference(resolution, [status(thm)], [c_22, c_97])).
% 2.26/1.26  tff(c_26, plain, (~r1_waybel_0('#skF_4', '#skF_5', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_120])).
% 2.26/1.26  tff(c_117, plain, (v1_xboole_0(u1_struct_0('#skF_4')) | ~l1_waybel_0('#skF_5', '#skF_4') | ~l1_struct_0('#skF_4') | v2_struct_0('#skF_4') | v2_struct_0('#skF_5') | ~l1_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_114, c_26])).
% 2.26/1.26  tff(c_120, plain, (v1_xboole_0(u1_struct_0('#skF_4')) | v2_struct_0('#skF_4') | v2_struct_0('#skF_5') | ~l1_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_28, c_117])).
% 2.26/1.26  tff(c_121, plain, (v1_xboole_0(u1_struct_0('#skF_4')) | ~l1_struct_0('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_34, c_38, c_120])).
% 2.26/1.26  tff(c_122, plain, (~l1_struct_0('#skF_5')), inference(splitLeft, [status(thm)], [c_121])).
% 2.26/1.26  tff(c_125, plain, (~l1_orders_2('#skF_5')), inference(resolution, [status(thm)], [c_6, c_122])).
% 2.26/1.26  tff(c_129, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_51, c_125])).
% 2.26/1.26  tff(c_130, plain, (v1_xboole_0(u1_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_121])).
% 2.26/1.26  tff(c_4, plain, (![A_3]: (~v1_xboole_0(u1_struct_0(A_3)) | ~l1_struct_0(A_3) | v2_struct_0(A_3))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.26/1.26  tff(c_134, plain, (~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_130, c_4])).
% 2.26/1.26  tff(c_137, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_134])).
% 2.26/1.26  tff(c_139, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_137])).
% 2.26/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.26/1.26  
% 2.26/1.26  Inference rules
% 2.26/1.26  ----------------------
% 2.26/1.26  #Ref     : 0
% 2.26/1.26  #Sup     : 16
% 2.26/1.26  #Fact    : 0
% 2.26/1.26  #Define  : 0
% 2.26/1.26  #Split   : 1
% 2.26/1.26  #Chain   : 0
% 2.26/1.26  #Close   : 0
% 2.26/1.26  
% 2.26/1.26  Ordering : KBO
% 2.26/1.26  
% 2.26/1.26  Simplification rules
% 2.26/1.26  ----------------------
% 2.26/1.26  #Subsume      : 3
% 2.26/1.26  #Demod        : 6
% 2.26/1.26  #Tautology    : 1
% 2.26/1.26  #SimpNegUnit  : 3
% 2.26/1.26  #BackRed      : 0
% 2.26/1.26  
% 2.26/1.26  #Partial instantiations: 0
% 2.26/1.26  #Strategies tried      : 1
% 2.26/1.26  
% 2.26/1.26  Timing (in seconds)
% 2.26/1.26  ----------------------
% 2.26/1.26  Preprocessing        : 0.30
% 2.26/1.26  Parsing              : 0.16
% 2.26/1.26  CNF conversion       : 0.03
% 2.26/1.26  Main loop            : 0.19
% 2.26/1.26  Inferencing          : 0.09
% 2.26/1.26  Reduction            : 0.04
% 2.26/1.26  Demodulation         : 0.03
% 2.26/1.26  BG Simplification    : 0.02
% 2.26/1.27  Subsumption          : 0.04
% 2.26/1.27  Abstraction          : 0.01
% 2.26/1.27  MUC search           : 0.00
% 2.26/1.27  Cooper               : 0.00
% 2.26/1.27  Total                : 0.52
% 2.26/1.27  Index Insertion      : 0.00
% 2.26/1.27  Index Deletion       : 0.00
% 2.26/1.27  Index Matching       : 0.00
% 2.26/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
