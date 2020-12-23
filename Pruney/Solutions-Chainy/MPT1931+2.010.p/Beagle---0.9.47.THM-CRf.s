%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:48 EST 2020

% Result     : Theorem 2.14s
% Output     : CNFRefutation 2.26s
% Verified   : 
% Statistics : Number of formulae       :   47 (  56 expanded)
%              Number of leaves         :   26 (  33 expanded)
%              Depth                    :   11
%              Number of atoms          :  103 ( 156 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_waybel_0 > r1_orders_2 > r2_hidden > m1_subset_1 > l1_waybel_0 > v7_waybel_0 > v4_orders_2 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > k2_waybel_0 > #nlpp > u1_struct_0 > #skF_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3

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

tff(f_28,axiom,(
    ! [A] :
    ? [B] : m1_subset_1(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).

tff(f_66,axiom,(
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

tff(f_80,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A)
        & ~ v2_struct_0(B)
        & l1_waybel_0(B,A)
        & m1_subset_1(C,u1_struct_0(B)) )
     => m1_subset_1(k2_waybel_0(A,B,C),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_waybel_0)).

tff(f_34,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_42,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(c_32,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_30,plain,(
    l1_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_28,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_22,plain,(
    l1_waybel_0('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_2,plain,(
    ! [A_1] : m1_subset_1('#skF_1'(A_1),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_16,plain,(
    ! [A_6,B_34,C_48,D_55] :
      ( m1_subset_1('#skF_2'(A_6,B_34,C_48,D_55),u1_struct_0(B_34))
      | r1_waybel_0(A_6,B_34,C_48)
      | ~ m1_subset_1(D_55,u1_struct_0(B_34))
      | ~ l1_waybel_0(B_34,A_6)
      | v2_struct_0(B_34)
      | ~ l1_struct_0(A_6)
      | v2_struct_0(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_18,plain,(
    ! [A_59,B_60,C_61] :
      ( m1_subset_1(k2_waybel_0(A_59,B_60,C_61),u1_struct_0(A_59))
      | ~ m1_subset_1(C_61,u1_struct_0(B_60))
      | ~ l1_waybel_0(B_60,A_59)
      | v2_struct_0(B_60)
      | ~ l1_struct_0(A_59)
      | v2_struct_0(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( r2_hidden(A_3,B_4)
      | v1_xboole_0(B_4)
      | ~ m1_subset_1(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_40,plain,(
    ! [A_81,B_82,C_83,D_84] :
      ( ~ r2_hidden(k2_waybel_0(A_81,B_82,'#skF_2'(A_81,B_82,C_83,D_84)),C_83)
      | r1_waybel_0(A_81,B_82,C_83)
      | ~ m1_subset_1(D_84,u1_struct_0(B_82))
      | ~ l1_waybel_0(B_82,A_81)
      | v2_struct_0(B_82)
      | ~ l1_struct_0(A_81)
      | v2_struct_0(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_52,plain,(
    ! [A_89,B_90,B_91,D_92] :
      ( r1_waybel_0(A_89,B_90,B_91)
      | ~ m1_subset_1(D_92,u1_struct_0(B_90))
      | ~ l1_waybel_0(B_90,A_89)
      | v2_struct_0(B_90)
      | ~ l1_struct_0(A_89)
      | v2_struct_0(A_89)
      | v1_xboole_0(B_91)
      | ~ m1_subset_1(k2_waybel_0(A_89,B_90,'#skF_2'(A_89,B_90,B_91,D_92)),B_91) ) ),
    inference(resolution,[status(thm)],[c_4,c_40])).

tff(c_58,plain,(
    ! [A_93,B_94,D_95] :
      ( r1_waybel_0(A_93,B_94,u1_struct_0(A_93))
      | ~ m1_subset_1(D_95,u1_struct_0(B_94))
      | v1_xboole_0(u1_struct_0(A_93))
      | ~ m1_subset_1('#skF_2'(A_93,B_94,u1_struct_0(A_93),D_95),u1_struct_0(B_94))
      | ~ l1_waybel_0(B_94,A_93)
      | v2_struct_0(B_94)
      | ~ l1_struct_0(A_93)
      | v2_struct_0(A_93) ) ),
    inference(resolution,[status(thm)],[c_18,c_52])).

tff(c_64,plain,(
    ! [A_96,B_97,D_98] :
      ( v1_xboole_0(u1_struct_0(A_96))
      | r1_waybel_0(A_96,B_97,u1_struct_0(A_96))
      | ~ m1_subset_1(D_98,u1_struct_0(B_97))
      | ~ l1_waybel_0(B_97,A_96)
      | v2_struct_0(B_97)
      | ~ l1_struct_0(A_96)
      | v2_struct_0(A_96) ) ),
    inference(resolution,[status(thm)],[c_16,c_58])).

tff(c_77,plain,(
    ! [A_99,B_100] :
      ( v1_xboole_0(u1_struct_0(A_99))
      | r1_waybel_0(A_99,B_100,u1_struct_0(A_99))
      | ~ l1_waybel_0(B_100,A_99)
      | v2_struct_0(B_100)
      | ~ l1_struct_0(A_99)
      | v2_struct_0(A_99) ) ),
    inference(resolution,[status(thm)],[c_2,c_64])).

tff(c_20,plain,(
    ~ r1_waybel_0('#skF_4','#skF_5',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_80,plain,
    ( v1_xboole_0(u1_struct_0('#skF_4'))
    | ~ l1_waybel_0('#skF_5','#skF_4')
    | v2_struct_0('#skF_5')
    | ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_77,c_20])).

tff(c_83,plain,
    ( v1_xboole_0(u1_struct_0('#skF_4'))
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_22,c_80])).

tff(c_84,plain,(
    v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_28,c_83])).

tff(c_6,plain,(
    ! [A_5] :
      ( ~ v1_xboole_0(u1_struct_0(A_5))
      | ~ l1_struct_0(A_5)
      | v2_struct_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_87,plain,
    ( ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_84,c_6])).

tff(c_90,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_87])).

tff(c_92,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_90])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.32  % Computer   : n017.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % DateTime   : Tue Dec  1 21:03:01 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.14/1.17  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.14/1.18  
% 2.14/1.18  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.14/1.18  %$ r1_waybel_0 > r1_orders_2 > r2_hidden > m1_subset_1 > l1_waybel_0 > v7_waybel_0 > v4_orders_2 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > k2_waybel_0 > #nlpp > u1_struct_0 > #skF_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3
% 2.14/1.18  
% 2.14/1.18  %Foreground sorts:
% 2.14/1.18  
% 2.14/1.18  
% 2.14/1.18  %Background operators:
% 2.14/1.18  
% 2.14/1.18  
% 2.14/1.18  %Foreground operators:
% 2.14/1.18  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.14/1.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.14/1.18  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.14/1.18  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.14/1.18  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 2.14/1.18  tff(k2_waybel_0, type, k2_waybel_0: ($i * $i * $i) > $i).
% 2.14/1.18  tff(v7_waybel_0, type, v7_waybel_0: $i > $o).
% 2.14/1.18  tff('#skF_5', type, '#skF_5': $i).
% 2.14/1.18  tff(r1_waybel_0, type, r1_waybel_0: ($i * $i * $i) > $o).
% 2.14/1.18  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.14/1.18  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.14/1.18  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.14/1.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.14/1.18  tff(l1_waybel_0, type, l1_waybel_0: ($i * $i) > $o).
% 2.14/1.18  tff('#skF_4', type, '#skF_4': $i).
% 2.14/1.18  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.14/1.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.14/1.18  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.14/1.18  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.14/1.18  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.14/1.18  
% 2.26/1.19  tff(f_98, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => r1_waybel_0(A, B, u1_struct_0(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_yellow_6)).
% 2.26/1.19  tff(f_28, axiom, (![A]: (?[B]: m1_subset_1(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', existence_m1_subset_1)).
% 2.26/1.19  tff(f_66, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((~v2_struct_0(B) & l1_waybel_0(B, A)) => (![C]: (r1_waybel_0(A, B, C) <=> (?[D]: (m1_subset_1(D, u1_struct_0(B)) & (![E]: (m1_subset_1(E, u1_struct_0(B)) => (r1_orders_2(B, D, E) => r2_hidden(k2_waybel_0(A, B, E), C)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d11_waybel_0)).
% 2.26/1.19  tff(f_80, axiom, (![A, B, C]: (((((~v2_struct_0(A) & l1_struct_0(A)) & ~v2_struct_0(B)) & l1_waybel_0(B, A)) & m1_subset_1(C, u1_struct_0(B))) => m1_subset_1(k2_waybel_0(A, B, C), u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_waybel_0)).
% 2.26/1.19  tff(f_34, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 2.26/1.19  tff(f_42, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 2.26/1.19  tff(c_32, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.26/1.19  tff(c_30, plain, (l1_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.26/1.19  tff(c_28, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.26/1.19  tff(c_22, plain, (l1_waybel_0('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.26/1.19  tff(c_2, plain, (![A_1]: (m1_subset_1('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_28])).
% 2.26/1.19  tff(c_16, plain, (![A_6, B_34, C_48, D_55]: (m1_subset_1('#skF_2'(A_6, B_34, C_48, D_55), u1_struct_0(B_34)) | r1_waybel_0(A_6, B_34, C_48) | ~m1_subset_1(D_55, u1_struct_0(B_34)) | ~l1_waybel_0(B_34, A_6) | v2_struct_0(B_34) | ~l1_struct_0(A_6) | v2_struct_0(A_6))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.26/1.19  tff(c_18, plain, (![A_59, B_60, C_61]: (m1_subset_1(k2_waybel_0(A_59, B_60, C_61), u1_struct_0(A_59)) | ~m1_subset_1(C_61, u1_struct_0(B_60)) | ~l1_waybel_0(B_60, A_59) | v2_struct_0(B_60) | ~l1_struct_0(A_59) | v2_struct_0(A_59))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.26/1.19  tff(c_4, plain, (![A_3, B_4]: (r2_hidden(A_3, B_4) | v1_xboole_0(B_4) | ~m1_subset_1(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.26/1.19  tff(c_40, plain, (![A_81, B_82, C_83, D_84]: (~r2_hidden(k2_waybel_0(A_81, B_82, '#skF_2'(A_81, B_82, C_83, D_84)), C_83) | r1_waybel_0(A_81, B_82, C_83) | ~m1_subset_1(D_84, u1_struct_0(B_82)) | ~l1_waybel_0(B_82, A_81) | v2_struct_0(B_82) | ~l1_struct_0(A_81) | v2_struct_0(A_81))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.26/1.19  tff(c_52, plain, (![A_89, B_90, B_91, D_92]: (r1_waybel_0(A_89, B_90, B_91) | ~m1_subset_1(D_92, u1_struct_0(B_90)) | ~l1_waybel_0(B_90, A_89) | v2_struct_0(B_90) | ~l1_struct_0(A_89) | v2_struct_0(A_89) | v1_xboole_0(B_91) | ~m1_subset_1(k2_waybel_0(A_89, B_90, '#skF_2'(A_89, B_90, B_91, D_92)), B_91))), inference(resolution, [status(thm)], [c_4, c_40])).
% 2.26/1.19  tff(c_58, plain, (![A_93, B_94, D_95]: (r1_waybel_0(A_93, B_94, u1_struct_0(A_93)) | ~m1_subset_1(D_95, u1_struct_0(B_94)) | v1_xboole_0(u1_struct_0(A_93)) | ~m1_subset_1('#skF_2'(A_93, B_94, u1_struct_0(A_93), D_95), u1_struct_0(B_94)) | ~l1_waybel_0(B_94, A_93) | v2_struct_0(B_94) | ~l1_struct_0(A_93) | v2_struct_0(A_93))), inference(resolution, [status(thm)], [c_18, c_52])).
% 2.26/1.19  tff(c_64, plain, (![A_96, B_97, D_98]: (v1_xboole_0(u1_struct_0(A_96)) | r1_waybel_0(A_96, B_97, u1_struct_0(A_96)) | ~m1_subset_1(D_98, u1_struct_0(B_97)) | ~l1_waybel_0(B_97, A_96) | v2_struct_0(B_97) | ~l1_struct_0(A_96) | v2_struct_0(A_96))), inference(resolution, [status(thm)], [c_16, c_58])).
% 2.26/1.19  tff(c_77, plain, (![A_99, B_100]: (v1_xboole_0(u1_struct_0(A_99)) | r1_waybel_0(A_99, B_100, u1_struct_0(A_99)) | ~l1_waybel_0(B_100, A_99) | v2_struct_0(B_100) | ~l1_struct_0(A_99) | v2_struct_0(A_99))), inference(resolution, [status(thm)], [c_2, c_64])).
% 2.26/1.19  tff(c_20, plain, (~r1_waybel_0('#skF_4', '#skF_5', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.26/1.19  tff(c_80, plain, (v1_xboole_0(u1_struct_0('#skF_4')) | ~l1_waybel_0('#skF_5', '#skF_4') | v2_struct_0('#skF_5') | ~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_77, c_20])).
% 2.26/1.19  tff(c_83, plain, (v1_xboole_0(u1_struct_0('#skF_4')) | v2_struct_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_22, c_80])).
% 2.26/1.19  tff(c_84, plain, (v1_xboole_0(u1_struct_0('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_32, c_28, c_83])).
% 2.26/1.19  tff(c_6, plain, (![A_5]: (~v1_xboole_0(u1_struct_0(A_5)) | ~l1_struct_0(A_5) | v2_struct_0(A_5))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.26/1.19  tff(c_87, plain, (~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_84, c_6])).
% 2.26/1.19  tff(c_90, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_87])).
% 2.26/1.19  tff(c_92, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_90])).
% 2.26/1.19  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.26/1.19  
% 2.26/1.19  Inference rules
% 2.26/1.19  ----------------------
% 2.26/1.20  #Ref     : 0
% 2.26/1.20  #Sup     : 10
% 2.26/1.20  #Fact    : 0
% 2.26/1.20  #Define  : 0
% 2.26/1.20  #Split   : 0
% 2.26/1.20  #Chain   : 0
% 2.26/1.20  #Close   : 0
% 2.26/1.20  
% 2.26/1.20  Ordering : KBO
% 2.26/1.20  
% 2.26/1.20  Simplification rules
% 2.26/1.20  ----------------------
% 2.26/1.20  #Subsume      : 3
% 2.26/1.20  #Demod        : 3
% 2.26/1.20  #Tautology    : 0
% 2.26/1.20  #SimpNegUnit  : 2
% 2.26/1.20  #BackRed      : 0
% 2.26/1.20  
% 2.26/1.20  #Partial instantiations: 0
% 2.26/1.20  #Strategies tried      : 1
% 2.26/1.20  
% 2.26/1.20  Timing (in seconds)
% 2.26/1.20  ----------------------
% 2.26/1.20  Preprocessing        : 0.29
% 2.26/1.20  Parsing              : 0.16
% 2.26/1.20  CNF conversion       : 0.03
% 2.26/1.20  Main loop            : 0.15
% 2.26/1.20  Inferencing          : 0.07
% 2.26/1.20  Reduction            : 0.04
% 2.26/1.20  Demodulation         : 0.03
% 2.26/1.20  BG Simplification    : 0.01
% 2.26/1.20  Subsumption          : 0.03
% 2.26/1.20  Abstraction          : 0.01
% 2.26/1.20  MUC search           : 0.00
% 2.26/1.20  Cooper               : 0.00
% 2.26/1.20  Total                : 0.47
% 2.26/1.20  Index Insertion      : 0.00
% 2.26/1.20  Index Deletion       : 0.00
% 2.26/1.20  Index Matching       : 0.00
% 2.26/1.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
