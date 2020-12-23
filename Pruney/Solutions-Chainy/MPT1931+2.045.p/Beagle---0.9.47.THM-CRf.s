%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:52 EST 2020

% Result     : Theorem 2.38s
% Output     : CNFRefutation 2.38s
% Verified   : 
% Statistics : Number of formulae       :   65 (  82 expanded)
%              Number of leaves         :   36 (  46 expanded)
%              Depth                    :    9
%              Number of atoms          :  105 ( 175 expanded)
%              Number of equality atoms :    5 (   5 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_waybel_0 > r1_waybel_0 > r1_orders_2 > r2_hidden > r1_xboole_0 > m1_subset_1 > l1_waybel_0 > v7_waybel_0 > v4_orders_2 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > k2_waybel_0 > k6_subset_1 > k4_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3

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

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_yellow_6)).

tff(f_28,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_93,axiom,(
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

tff(f_35,axiom,(
    ! [A] :
    ? [B] : m1_subset_1(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).

tff(f_76,axiom,(
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

tff(f_39,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(c_46,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_42,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_44,plain,(
    l1_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_36,plain,(
    l1_waybel_0('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_4,plain,(
    ! [A_1] : r1_xboole_0(A_1,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_61,plain,(
    ! [A_81,B_82] :
      ( k4_xboole_0(A_81,B_82) = A_81
      | ~ r1_xboole_0(A_81,B_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_65,plain,(
    ! [A_1] : k4_xboole_0(A_1,k1_xboole_0) = A_1 ),
    inference(resolution,[status(thm)],[c_4,c_61])).

tff(c_12,plain,(
    ! [A_6,B_7] : k6_subset_1(A_6,B_7) = k4_xboole_0(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_32,plain,(
    ! [A_68,B_72,C_74] :
      ( r2_waybel_0(A_68,B_72,C_74)
      | r1_waybel_0(A_68,B_72,k6_subset_1(u1_struct_0(A_68),C_74))
      | ~ l1_waybel_0(B_72,A_68)
      | v2_struct_0(B_72)
      | ~ l1_struct_0(A_68)
      | v2_struct_0(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_101,plain,(
    ! [A_100,B_101,C_102] :
      ( r2_waybel_0(A_100,B_101,C_102)
      | r1_waybel_0(A_100,B_101,k4_xboole_0(u1_struct_0(A_100),C_102))
      | ~ l1_waybel_0(B_101,A_100)
      | v2_struct_0(B_101)
      | ~ l1_struct_0(A_100)
      | v2_struct_0(A_100) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_32])).

tff(c_106,plain,(
    ! [A_103,B_104] :
      ( r2_waybel_0(A_103,B_104,k1_xboole_0)
      | r1_waybel_0(A_103,B_104,u1_struct_0(A_103))
      | ~ l1_waybel_0(B_104,A_103)
      | v2_struct_0(B_104)
      | ~ l1_struct_0(A_103)
      | v2_struct_0(A_103) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_65,c_101])).

tff(c_34,plain,(
    ~ r1_waybel_0('#skF_4','#skF_5',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_109,plain,
    ( r2_waybel_0('#skF_4','#skF_5',k1_xboole_0)
    | ~ l1_waybel_0('#skF_5','#skF_4')
    | v2_struct_0('#skF_5')
    | ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_106,c_34])).

tff(c_112,plain,
    ( r2_waybel_0('#skF_4','#skF_5',k1_xboole_0)
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_36,c_109])).

tff(c_113,plain,(
    r2_waybel_0('#skF_4','#skF_5',k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_42,c_112])).

tff(c_10,plain,(
    ! [A_4] : m1_subset_1('#skF_1'(A_4),A_4) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_130,plain,(
    ! [A_118,B_119,C_120,D_121] :
      ( r2_hidden(k2_waybel_0(A_118,B_119,'#skF_3'(A_118,B_119,C_120,D_121)),C_120)
      | ~ m1_subset_1(D_121,u1_struct_0(B_119))
      | ~ r2_waybel_0(A_118,B_119,C_120)
      | ~ l1_waybel_0(B_119,A_118)
      | v2_struct_0(B_119)
      | ~ l1_struct_0(A_118)
      | v2_struct_0(A_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_14,plain,(
    ! [A_8] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_80,plain,(
    ! [C_86,B_87,A_88] :
      ( ~ v1_xboole_0(C_86)
      | ~ m1_subset_1(B_87,k1_zfmisc_1(C_86))
      | ~ r2_hidden(A_88,B_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_86,plain,(
    ! [A_8,A_88] :
      ( ~ v1_xboole_0(A_8)
      | ~ r2_hidden(A_88,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_14,c_80])).

tff(c_88,plain,(
    ! [A_88] : ~ r2_hidden(A_88,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_86])).

tff(c_146,plain,(
    ! [D_122,B_123,A_124] :
      ( ~ m1_subset_1(D_122,u1_struct_0(B_123))
      | ~ r2_waybel_0(A_124,B_123,k1_xboole_0)
      | ~ l1_waybel_0(B_123,A_124)
      | v2_struct_0(B_123)
      | ~ l1_struct_0(A_124)
      | v2_struct_0(A_124) ) ),
    inference(resolution,[status(thm)],[c_130,c_88])).

tff(c_156,plain,(
    ! [A_125,B_126] :
      ( ~ r2_waybel_0(A_125,B_126,k1_xboole_0)
      | ~ l1_waybel_0(B_126,A_125)
      | v2_struct_0(B_126)
      | ~ l1_struct_0(A_125)
      | v2_struct_0(A_125) ) ),
    inference(resolution,[status(thm)],[c_10,c_146])).

tff(c_159,plain,
    ( ~ l1_waybel_0('#skF_5','#skF_4')
    | v2_struct_0('#skF_5')
    | ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_113,c_156])).

tff(c_162,plain,
    ( v2_struct_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_36,c_159])).

tff(c_164,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_42,c_162])).

tff(c_165,plain,(
    ! [A_8] : ~ v1_xboole_0(A_8) ),
    inference(splitRight,[status(thm)],[c_86])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_167,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_165,c_2])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n015.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 15:28:53 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.38/1.34  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.38/1.34  
% 2.38/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.38/1.35  %$ r2_waybel_0 > r1_waybel_0 > r1_orders_2 > r2_hidden > r1_xboole_0 > m1_subset_1 > l1_waybel_0 > v7_waybel_0 > v4_orders_2 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > k2_waybel_0 > k6_subset_1 > k4_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3
% 2.38/1.35  
% 2.38/1.35  %Foreground sorts:
% 2.38/1.35  
% 2.38/1.35  
% 2.38/1.35  %Background operators:
% 2.38/1.35  
% 2.38/1.35  
% 2.38/1.35  %Foreground operators:
% 2.38/1.35  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.38/1.35  tff(r2_waybel_0, type, r2_waybel_0: ($i * $i * $i) > $o).
% 2.38/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.38/1.35  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.38/1.35  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.38/1.35  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.38/1.35  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 2.38/1.35  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.38/1.35  tff(k2_waybel_0, type, k2_waybel_0: ($i * $i * $i) > $i).
% 2.38/1.35  tff(v7_waybel_0, type, v7_waybel_0: $i > $o).
% 2.38/1.35  tff('#skF_5', type, '#skF_5': $i).
% 2.38/1.35  tff(r1_waybel_0, type, r1_waybel_0: ($i * $i * $i) > $o).
% 2.38/1.35  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.38/1.35  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 2.38/1.35  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.38/1.35  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.38/1.35  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.38/1.35  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.38/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.38/1.35  tff(l1_waybel_0, type, l1_waybel_0: ($i * $i) > $o).
% 2.38/1.35  tff('#skF_4', type, '#skF_4': $i).
% 2.38/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.38/1.35  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 2.38/1.35  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.38/1.35  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.38/1.35  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.38/1.35  
% 2.38/1.36  tff(f_111, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => r1_waybel_0(A, B, u1_struct_0(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_yellow_6)).
% 2.38/1.36  tff(f_28, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.38/1.36  tff(f_32, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.38/1.36  tff(f_37, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 2.38/1.36  tff(f_93, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((~v2_struct_0(B) & l1_waybel_0(B, A)) => (![C]: (r2_waybel_0(A, B, C) <=> ~r1_waybel_0(A, B, k6_subset_1(u1_struct_0(A), C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_waybel_0)).
% 2.38/1.36  tff(f_35, axiom, (![A]: (?[B]: m1_subset_1(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', existence_m1_subset_1)).
% 2.38/1.36  tff(f_76, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((~v2_struct_0(B) & l1_waybel_0(B, A)) => (![C]: (r2_waybel_0(A, B, C) <=> (![D]: (m1_subset_1(D, u1_struct_0(B)) => (?[E]: ((m1_subset_1(E, u1_struct_0(B)) & r1_orders_2(B, D, E)) & r2_hidden(k2_waybel_0(A, B, E), C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_waybel_0)).
% 2.38/1.36  tff(f_39, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 2.38/1.36  tff(f_52, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 2.38/1.36  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.38/1.36  tff(c_46, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.38/1.36  tff(c_42, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.38/1.36  tff(c_44, plain, (l1_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.38/1.36  tff(c_36, plain, (l1_waybel_0('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.38/1.36  tff(c_4, plain, (![A_1]: (r1_xboole_0(A_1, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_28])).
% 2.38/1.36  tff(c_61, plain, (![A_81, B_82]: (k4_xboole_0(A_81, B_82)=A_81 | ~r1_xboole_0(A_81, B_82))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.38/1.36  tff(c_65, plain, (![A_1]: (k4_xboole_0(A_1, k1_xboole_0)=A_1)), inference(resolution, [status(thm)], [c_4, c_61])).
% 2.38/1.36  tff(c_12, plain, (![A_6, B_7]: (k6_subset_1(A_6, B_7)=k4_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.38/1.36  tff(c_32, plain, (![A_68, B_72, C_74]: (r2_waybel_0(A_68, B_72, C_74) | r1_waybel_0(A_68, B_72, k6_subset_1(u1_struct_0(A_68), C_74)) | ~l1_waybel_0(B_72, A_68) | v2_struct_0(B_72) | ~l1_struct_0(A_68) | v2_struct_0(A_68))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.38/1.36  tff(c_101, plain, (![A_100, B_101, C_102]: (r2_waybel_0(A_100, B_101, C_102) | r1_waybel_0(A_100, B_101, k4_xboole_0(u1_struct_0(A_100), C_102)) | ~l1_waybel_0(B_101, A_100) | v2_struct_0(B_101) | ~l1_struct_0(A_100) | v2_struct_0(A_100))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_32])).
% 2.38/1.36  tff(c_106, plain, (![A_103, B_104]: (r2_waybel_0(A_103, B_104, k1_xboole_0) | r1_waybel_0(A_103, B_104, u1_struct_0(A_103)) | ~l1_waybel_0(B_104, A_103) | v2_struct_0(B_104) | ~l1_struct_0(A_103) | v2_struct_0(A_103))), inference(superposition, [status(thm), theory('equality')], [c_65, c_101])).
% 2.38/1.36  tff(c_34, plain, (~r1_waybel_0('#skF_4', '#skF_5', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.38/1.36  tff(c_109, plain, (r2_waybel_0('#skF_4', '#skF_5', k1_xboole_0) | ~l1_waybel_0('#skF_5', '#skF_4') | v2_struct_0('#skF_5') | ~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_106, c_34])).
% 2.38/1.36  tff(c_112, plain, (r2_waybel_0('#skF_4', '#skF_5', k1_xboole_0) | v2_struct_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_36, c_109])).
% 2.38/1.36  tff(c_113, plain, (r2_waybel_0('#skF_4', '#skF_5', k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_46, c_42, c_112])).
% 2.38/1.36  tff(c_10, plain, (![A_4]: (m1_subset_1('#skF_1'(A_4), A_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.38/1.36  tff(c_130, plain, (![A_118, B_119, C_120, D_121]: (r2_hidden(k2_waybel_0(A_118, B_119, '#skF_3'(A_118, B_119, C_120, D_121)), C_120) | ~m1_subset_1(D_121, u1_struct_0(B_119)) | ~r2_waybel_0(A_118, B_119, C_120) | ~l1_waybel_0(B_119, A_118) | v2_struct_0(B_119) | ~l1_struct_0(A_118) | v2_struct_0(A_118))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.38/1.36  tff(c_14, plain, (![A_8]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.38/1.36  tff(c_80, plain, (![C_86, B_87, A_88]: (~v1_xboole_0(C_86) | ~m1_subset_1(B_87, k1_zfmisc_1(C_86)) | ~r2_hidden(A_88, B_87))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.38/1.36  tff(c_86, plain, (![A_8, A_88]: (~v1_xboole_0(A_8) | ~r2_hidden(A_88, k1_xboole_0))), inference(resolution, [status(thm)], [c_14, c_80])).
% 2.38/1.36  tff(c_88, plain, (![A_88]: (~r2_hidden(A_88, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_86])).
% 2.38/1.36  tff(c_146, plain, (![D_122, B_123, A_124]: (~m1_subset_1(D_122, u1_struct_0(B_123)) | ~r2_waybel_0(A_124, B_123, k1_xboole_0) | ~l1_waybel_0(B_123, A_124) | v2_struct_0(B_123) | ~l1_struct_0(A_124) | v2_struct_0(A_124))), inference(resolution, [status(thm)], [c_130, c_88])).
% 2.38/1.36  tff(c_156, plain, (![A_125, B_126]: (~r2_waybel_0(A_125, B_126, k1_xboole_0) | ~l1_waybel_0(B_126, A_125) | v2_struct_0(B_126) | ~l1_struct_0(A_125) | v2_struct_0(A_125))), inference(resolution, [status(thm)], [c_10, c_146])).
% 2.38/1.36  tff(c_159, plain, (~l1_waybel_0('#skF_5', '#skF_4') | v2_struct_0('#skF_5') | ~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_113, c_156])).
% 2.38/1.36  tff(c_162, plain, (v2_struct_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_36, c_159])).
% 2.38/1.36  tff(c_164, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_42, c_162])).
% 2.38/1.36  tff(c_165, plain, (![A_8]: (~v1_xboole_0(A_8))), inference(splitRight, [status(thm)], [c_86])).
% 2.38/1.36  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.38/1.36  tff(c_167, plain, $false, inference(negUnitSimplification, [status(thm)], [c_165, c_2])).
% 2.38/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.38/1.36  
% 2.38/1.36  Inference rules
% 2.38/1.36  ----------------------
% 2.38/1.36  #Ref     : 0
% 2.38/1.36  #Sup     : 22
% 2.38/1.36  #Fact    : 0
% 2.38/1.36  #Define  : 0
% 2.38/1.36  #Split   : 1
% 2.38/1.36  #Chain   : 0
% 2.38/1.36  #Close   : 0
% 2.38/1.36  
% 2.38/1.36  Ordering : KBO
% 2.38/1.36  
% 2.38/1.36  Simplification rules
% 2.38/1.36  ----------------------
% 2.38/1.36  #Subsume      : 5
% 2.38/1.36  #Demod        : 6
% 2.38/1.36  #Tautology    : 7
% 2.38/1.36  #SimpNegUnit  : 3
% 2.38/1.36  #BackRed      : 1
% 2.38/1.36  
% 2.38/1.36  #Partial instantiations: 0
% 2.38/1.36  #Strategies tried      : 1
% 2.38/1.36  
% 2.38/1.36  Timing (in seconds)
% 2.38/1.36  ----------------------
% 2.38/1.36  Preprocessing        : 0.34
% 2.38/1.37  Parsing              : 0.18
% 2.38/1.37  CNF conversion       : 0.03
% 2.38/1.37  Main loop            : 0.19
% 2.38/1.37  Inferencing          : 0.08
% 2.38/1.37  Reduction            : 0.05
% 2.38/1.37  Demodulation         : 0.04
% 2.38/1.37  BG Simplification    : 0.01
% 2.38/1.37  Subsumption          : 0.03
% 2.38/1.37  Abstraction          : 0.01
% 2.38/1.37  MUC search           : 0.00
% 2.38/1.37  Cooper               : 0.00
% 2.48/1.37  Total                : 0.56
% 2.48/1.37  Index Insertion      : 0.00
% 2.48/1.37  Index Deletion       : 0.00
% 2.48/1.37  Index Matching       : 0.00
% 2.48/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
