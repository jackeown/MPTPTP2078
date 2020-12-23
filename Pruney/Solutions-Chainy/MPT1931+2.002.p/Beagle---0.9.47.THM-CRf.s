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
% DateTime   : Thu Dec  3 10:30:47 EST 2020

% Result     : Theorem 2.52s
% Output     : CNFRefutation 2.52s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 175 expanded)
%              Number of leaves         :   26 (  74 expanded)
%              Depth                    :   14
%              Number of atoms          :  153 ( 750 expanded)
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

tff(f_108,negated_conjecture,(
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

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_44,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_76,axiom,(
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

tff(f_90,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A)
        & ~ v2_struct_0(B)
        & l1_waybel_0(B,A)
        & m1_subset_1(C,u1_struct_0(B)) )
     => m1_subset_1(k2_waybel_0(A,B,C),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_waybel_0)).

tff(f_52,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(c_40,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_38,plain,(
    l1_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_36,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_30,plain,(
    l1_waybel_0('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_54,plain,(
    ! [B_73,A_74] :
      ( m1_subset_1(B_73,A_74)
      | ~ r2_hidden(B_73,A_74)
      | v1_xboole_0(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_58,plain,(
    ! [A_1] :
      ( m1_subset_1('#skF_1'(A_1),A_1)
      | v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_4,c_54])).

tff(c_24,plain,(
    ! [A_8,B_36,C_50,D_57] :
      ( m1_subset_1('#skF_2'(A_8,B_36,C_50,D_57),u1_struct_0(B_36))
      | r1_waybel_0(A_8,B_36,C_50)
      | ~ m1_subset_1(D_57,u1_struct_0(B_36))
      | ~ l1_waybel_0(B_36,A_8)
      | v2_struct_0(B_36)
      | ~ l1_struct_0(A_8)
      | v2_struct_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_26,plain,(
    ! [A_61,B_62,C_63] :
      ( m1_subset_1(k2_waybel_0(A_61,B_62,C_63),u1_struct_0(A_61))
      | ~ m1_subset_1(C_63,u1_struct_0(B_62))
      | ~ l1_waybel_0(B_62,A_61)
      | v2_struct_0(B_62)
      | ~ l1_struct_0(A_61)
      | v2_struct_0(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_8,plain,(
    ! [B_6,A_5] :
      ( r2_hidden(B_6,A_5)
      | ~ m1_subset_1(B_6,A_5)
      | v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_109,plain,(
    ! [A_103,B_104,C_105,D_106] :
      ( ~ r2_hidden(k2_waybel_0(A_103,B_104,'#skF_2'(A_103,B_104,C_105,D_106)),C_105)
      | r1_waybel_0(A_103,B_104,C_105)
      | ~ m1_subset_1(D_106,u1_struct_0(B_104))
      | ~ l1_waybel_0(B_104,A_103)
      | v2_struct_0(B_104)
      | ~ l1_struct_0(A_103)
      | v2_struct_0(A_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_115,plain,(
    ! [A_107,B_108,A_109,D_110] :
      ( r1_waybel_0(A_107,B_108,A_109)
      | ~ m1_subset_1(D_110,u1_struct_0(B_108))
      | ~ l1_waybel_0(B_108,A_107)
      | v2_struct_0(B_108)
      | ~ l1_struct_0(A_107)
      | v2_struct_0(A_107)
      | ~ m1_subset_1(k2_waybel_0(A_107,B_108,'#skF_2'(A_107,B_108,A_109,D_110)),A_109)
      | v1_xboole_0(A_109) ) ),
    inference(resolution,[status(thm)],[c_8,c_109])).

tff(c_146,plain,(
    ! [A_120,B_121,D_122] :
      ( r1_waybel_0(A_120,B_121,u1_struct_0(A_120))
      | ~ m1_subset_1(D_122,u1_struct_0(B_121))
      | v1_xboole_0(u1_struct_0(A_120))
      | ~ m1_subset_1('#skF_2'(A_120,B_121,u1_struct_0(A_120),D_122),u1_struct_0(B_121))
      | ~ l1_waybel_0(B_121,A_120)
      | v2_struct_0(B_121)
      | ~ l1_struct_0(A_120)
      | v2_struct_0(A_120) ) ),
    inference(resolution,[status(thm)],[c_26,c_115])).

tff(c_156,plain,(
    ! [A_123,B_124,D_125] :
      ( v1_xboole_0(u1_struct_0(A_123))
      | r1_waybel_0(A_123,B_124,u1_struct_0(A_123))
      | ~ m1_subset_1(D_125,u1_struct_0(B_124))
      | ~ l1_waybel_0(B_124,A_123)
      | v2_struct_0(B_124)
      | ~ l1_struct_0(A_123)
      | v2_struct_0(A_123) ) ),
    inference(resolution,[status(thm)],[c_24,c_146])).

tff(c_174,plain,(
    ! [A_126,B_127] :
      ( v1_xboole_0(u1_struct_0(A_126))
      | r1_waybel_0(A_126,B_127,u1_struct_0(A_126))
      | ~ l1_waybel_0(B_127,A_126)
      | v2_struct_0(B_127)
      | ~ l1_struct_0(A_126)
      | v2_struct_0(A_126)
      | v1_xboole_0(u1_struct_0(B_127)) ) ),
    inference(resolution,[status(thm)],[c_58,c_156])).

tff(c_28,plain,(
    ~ r1_waybel_0('#skF_4','#skF_5',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_177,plain,
    ( v1_xboole_0(u1_struct_0('#skF_4'))
    | ~ l1_waybel_0('#skF_5','#skF_4')
    | v2_struct_0('#skF_5')
    | ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4')
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_174,c_28])).

tff(c_180,plain,
    ( v1_xboole_0(u1_struct_0('#skF_4'))
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_4')
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_30,c_177])).

tff(c_181,plain,
    ( v1_xboole_0(u1_struct_0('#skF_4'))
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_36,c_180])).

tff(c_182,plain,(
    v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_181])).

tff(c_10,plain,(
    ! [B_6,A_5] :
      ( m1_subset_1(B_6,A_5)
      | ~ v1_xboole_0(B_6)
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_173,plain,(
    ! [A_123,B_124,B_6] :
      ( v1_xboole_0(u1_struct_0(A_123))
      | r1_waybel_0(A_123,B_124,u1_struct_0(A_123))
      | ~ l1_waybel_0(B_124,A_123)
      | v2_struct_0(B_124)
      | ~ l1_struct_0(A_123)
      | v2_struct_0(A_123)
      | ~ v1_xboole_0(B_6)
      | ~ v1_xboole_0(u1_struct_0(B_124)) ) ),
    inference(resolution,[status(thm)],[c_10,c_156])).

tff(c_201,plain,(
    ! [B_6] : ~ v1_xboole_0(B_6) ),
    inference(splitLeft,[status(thm)],[c_173])).

tff(c_218,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_201,c_182])).

tff(c_220,plain,(
    ! [A_138,B_139] :
      ( v1_xboole_0(u1_struct_0(A_138))
      | r1_waybel_0(A_138,B_139,u1_struct_0(A_138))
      | ~ l1_waybel_0(B_139,A_138)
      | v2_struct_0(B_139)
      | ~ l1_struct_0(A_138)
      | v2_struct_0(A_138)
      | ~ v1_xboole_0(u1_struct_0(B_139)) ) ),
    inference(splitRight,[status(thm)],[c_173])).

tff(c_223,plain,
    ( v1_xboole_0(u1_struct_0('#skF_4'))
    | ~ l1_waybel_0('#skF_5','#skF_4')
    | v2_struct_0('#skF_5')
    | ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4')
    | ~ v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_220,c_28])).

tff(c_226,plain,
    ( v1_xboole_0(u1_struct_0('#skF_4'))
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_182,c_38,c_30,c_223])).

tff(c_227,plain,(
    v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_36,c_226])).

tff(c_14,plain,(
    ! [A_7] :
      ( ~ v1_xboole_0(u1_struct_0(A_7))
      | ~ l1_struct_0(A_7)
      | v2_struct_0(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_234,plain,
    ( ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_227,c_14])).

tff(c_243,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_234])).

tff(c_245,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_243])).

tff(c_246,plain,(
    v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_181])).

tff(c_254,plain,
    ( ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_246,c_14])).

tff(c_263,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_254])).

tff(c_265,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_263])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:54:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.52/1.41  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.52/1.42  
% 2.52/1.42  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.52/1.42  %$ r1_waybel_0 > r1_orders_2 > r2_hidden > m1_subset_1 > l1_waybel_0 > v7_waybel_0 > v4_orders_2 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > k2_waybel_0 > #nlpp > u1_struct_0 > #skF_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3
% 2.52/1.42  
% 2.52/1.42  %Foreground sorts:
% 2.52/1.42  
% 2.52/1.42  
% 2.52/1.42  %Background operators:
% 2.52/1.42  
% 2.52/1.42  
% 2.52/1.42  %Foreground operators:
% 2.52/1.42  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.52/1.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.52/1.42  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.52/1.42  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.52/1.42  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 2.52/1.42  tff(k2_waybel_0, type, k2_waybel_0: ($i * $i * $i) > $i).
% 2.52/1.42  tff(v7_waybel_0, type, v7_waybel_0: $i > $o).
% 2.52/1.42  tff('#skF_5', type, '#skF_5': $i).
% 2.52/1.42  tff(r1_waybel_0, type, r1_waybel_0: ($i * $i * $i) > $o).
% 2.52/1.42  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.52/1.42  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.52/1.42  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.52/1.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.52/1.42  tff(l1_waybel_0, type, l1_waybel_0: ($i * $i) > $o).
% 2.52/1.42  tff('#skF_4', type, '#skF_4': $i).
% 2.52/1.42  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.52/1.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.52/1.42  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.52/1.42  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.52/1.42  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.52/1.42  
% 2.52/1.44  tff(f_108, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => r1_waybel_0(A, B, u1_struct_0(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_yellow_6)).
% 2.52/1.44  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.52/1.44  tff(f_44, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 2.52/1.44  tff(f_76, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((~v2_struct_0(B) & l1_waybel_0(B, A)) => (![C]: (r1_waybel_0(A, B, C) <=> (?[D]: (m1_subset_1(D, u1_struct_0(B)) & (![E]: (m1_subset_1(E, u1_struct_0(B)) => (r1_orders_2(B, D, E) => r2_hidden(k2_waybel_0(A, B, E), C)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d11_waybel_0)).
% 2.52/1.44  tff(f_90, axiom, (![A, B, C]: (((((~v2_struct_0(A) & l1_struct_0(A)) & ~v2_struct_0(B)) & l1_waybel_0(B, A)) & m1_subset_1(C, u1_struct_0(B))) => m1_subset_1(k2_waybel_0(A, B, C), u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_waybel_0)).
% 2.52/1.44  tff(f_52, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 2.52/1.44  tff(c_40, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.52/1.44  tff(c_38, plain, (l1_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.52/1.44  tff(c_36, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.52/1.44  tff(c_30, plain, (l1_waybel_0('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.52/1.44  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.52/1.44  tff(c_54, plain, (![B_73, A_74]: (m1_subset_1(B_73, A_74) | ~r2_hidden(B_73, A_74) | v1_xboole_0(A_74))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.52/1.44  tff(c_58, plain, (![A_1]: (m1_subset_1('#skF_1'(A_1), A_1) | v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_4, c_54])).
% 2.52/1.44  tff(c_24, plain, (![A_8, B_36, C_50, D_57]: (m1_subset_1('#skF_2'(A_8, B_36, C_50, D_57), u1_struct_0(B_36)) | r1_waybel_0(A_8, B_36, C_50) | ~m1_subset_1(D_57, u1_struct_0(B_36)) | ~l1_waybel_0(B_36, A_8) | v2_struct_0(B_36) | ~l1_struct_0(A_8) | v2_struct_0(A_8))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.52/1.44  tff(c_26, plain, (![A_61, B_62, C_63]: (m1_subset_1(k2_waybel_0(A_61, B_62, C_63), u1_struct_0(A_61)) | ~m1_subset_1(C_63, u1_struct_0(B_62)) | ~l1_waybel_0(B_62, A_61) | v2_struct_0(B_62) | ~l1_struct_0(A_61) | v2_struct_0(A_61))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.52/1.44  tff(c_8, plain, (![B_6, A_5]: (r2_hidden(B_6, A_5) | ~m1_subset_1(B_6, A_5) | v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.52/1.44  tff(c_109, plain, (![A_103, B_104, C_105, D_106]: (~r2_hidden(k2_waybel_0(A_103, B_104, '#skF_2'(A_103, B_104, C_105, D_106)), C_105) | r1_waybel_0(A_103, B_104, C_105) | ~m1_subset_1(D_106, u1_struct_0(B_104)) | ~l1_waybel_0(B_104, A_103) | v2_struct_0(B_104) | ~l1_struct_0(A_103) | v2_struct_0(A_103))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.52/1.44  tff(c_115, plain, (![A_107, B_108, A_109, D_110]: (r1_waybel_0(A_107, B_108, A_109) | ~m1_subset_1(D_110, u1_struct_0(B_108)) | ~l1_waybel_0(B_108, A_107) | v2_struct_0(B_108) | ~l1_struct_0(A_107) | v2_struct_0(A_107) | ~m1_subset_1(k2_waybel_0(A_107, B_108, '#skF_2'(A_107, B_108, A_109, D_110)), A_109) | v1_xboole_0(A_109))), inference(resolution, [status(thm)], [c_8, c_109])).
% 2.52/1.44  tff(c_146, plain, (![A_120, B_121, D_122]: (r1_waybel_0(A_120, B_121, u1_struct_0(A_120)) | ~m1_subset_1(D_122, u1_struct_0(B_121)) | v1_xboole_0(u1_struct_0(A_120)) | ~m1_subset_1('#skF_2'(A_120, B_121, u1_struct_0(A_120), D_122), u1_struct_0(B_121)) | ~l1_waybel_0(B_121, A_120) | v2_struct_0(B_121) | ~l1_struct_0(A_120) | v2_struct_0(A_120))), inference(resolution, [status(thm)], [c_26, c_115])).
% 2.52/1.44  tff(c_156, plain, (![A_123, B_124, D_125]: (v1_xboole_0(u1_struct_0(A_123)) | r1_waybel_0(A_123, B_124, u1_struct_0(A_123)) | ~m1_subset_1(D_125, u1_struct_0(B_124)) | ~l1_waybel_0(B_124, A_123) | v2_struct_0(B_124) | ~l1_struct_0(A_123) | v2_struct_0(A_123))), inference(resolution, [status(thm)], [c_24, c_146])).
% 2.52/1.44  tff(c_174, plain, (![A_126, B_127]: (v1_xboole_0(u1_struct_0(A_126)) | r1_waybel_0(A_126, B_127, u1_struct_0(A_126)) | ~l1_waybel_0(B_127, A_126) | v2_struct_0(B_127) | ~l1_struct_0(A_126) | v2_struct_0(A_126) | v1_xboole_0(u1_struct_0(B_127)))), inference(resolution, [status(thm)], [c_58, c_156])).
% 2.52/1.44  tff(c_28, plain, (~r1_waybel_0('#skF_4', '#skF_5', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.52/1.44  tff(c_177, plain, (v1_xboole_0(u1_struct_0('#skF_4')) | ~l1_waybel_0('#skF_5', '#skF_4') | v2_struct_0('#skF_5') | ~l1_struct_0('#skF_4') | v2_struct_0('#skF_4') | v1_xboole_0(u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_174, c_28])).
% 2.52/1.44  tff(c_180, plain, (v1_xboole_0(u1_struct_0('#skF_4')) | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | v1_xboole_0(u1_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_30, c_177])).
% 2.52/1.44  tff(c_181, plain, (v1_xboole_0(u1_struct_0('#skF_4')) | v1_xboole_0(u1_struct_0('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_40, c_36, c_180])).
% 2.52/1.44  tff(c_182, plain, (v1_xboole_0(u1_struct_0('#skF_5'))), inference(splitLeft, [status(thm)], [c_181])).
% 2.52/1.44  tff(c_10, plain, (![B_6, A_5]: (m1_subset_1(B_6, A_5) | ~v1_xboole_0(B_6) | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.52/1.44  tff(c_173, plain, (![A_123, B_124, B_6]: (v1_xboole_0(u1_struct_0(A_123)) | r1_waybel_0(A_123, B_124, u1_struct_0(A_123)) | ~l1_waybel_0(B_124, A_123) | v2_struct_0(B_124) | ~l1_struct_0(A_123) | v2_struct_0(A_123) | ~v1_xboole_0(B_6) | ~v1_xboole_0(u1_struct_0(B_124)))), inference(resolution, [status(thm)], [c_10, c_156])).
% 2.52/1.44  tff(c_201, plain, (![B_6]: (~v1_xboole_0(B_6))), inference(splitLeft, [status(thm)], [c_173])).
% 2.52/1.44  tff(c_218, plain, $false, inference(negUnitSimplification, [status(thm)], [c_201, c_182])).
% 2.52/1.44  tff(c_220, plain, (![A_138, B_139]: (v1_xboole_0(u1_struct_0(A_138)) | r1_waybel_0(A_138, B_139, u1_struct_0(A_138)) | ~l1_waybel_0(B_139, A_138) | v2_struct_0(B_139) | ~l1_struct_0(A_138) | v2_struct_0(A_138) | ~v1_xboole_0(u1_struct_0(B_139)))), inference(splitRight, [status(thm)], [c_173])).
% 2.52/1.44  tff(c_223, plain, (v1_xboole_0(u1_struct_0('#skF_4')) | ~l1_waybel_0('#skF_5', '#skF_4') | v2_struct_0('#skF_5') | ~l1_struct_0('#skF_4') | v2_struct_0('#skF_4') | ~v1_xboole_0(u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_220, c_28])).
% 2.52/1.44  tff(c_226, plain, (v1_xboole_0(u1_struct_0('#skF_4')) | v2_struct_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_182, c_38, c_30, c_223])).
% 2.52/1.44  tff(c_227, plain, (v1_xboole_0(u1_struct_0('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_40, c_36, c_226])).
% 2.52/1.44  tff(c_14, plain, (![A_7]: (~v1_xboole_0(u1_struct_0(A_7)) | ~l1_struct_0(A_7) | v2_struct_0(A_7))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.52/1.44  tff(c_234, plain, (~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_227, c_14])).
% 2.52/1.44  tff(c_243, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_234])).
% 2.52/1.44  tff(c_245, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_243])).
% 2.52/1.44  tff(c_246, plain, (v1_xboole_0(u1_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_181])).
% 2.52/1.44  tff(c_254, plain, (~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_246, c_14])).
% 2.52/1.44  tff(c_263, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_254])).
% 2.52/1.44  tff(c_265, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_263])).
% 2.52/1.44  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.52/1.44  
% 2.52/1.44  Inference rules
% 2.52/1.44  ----------------------
% 2.52/1.44  #Ref     : 0
% 2.52/1.44  #Sup     : 39
% 2.52/1.44  #Fact    : 0
% 2.52/1.44  #Define  : 0
% 2.52/1.44  #Split   : 2
% 2.52/1.44  #Chain   : 0
% 2.52/1.44  #Close   : 0
% 2.52/1.44  
% 2.52/1.44  Ordering : KBO
% 2.52/1.44  
% 2.52/1.44  Simplification rules
% 2.52/1.44  ----------------------
% 2.52/1.44  #Subsume      : 13
% 2.52/1.44  #Demod        : 7
% 2.52/1.44  #Tautology    : 8
% 2.52/1.44  #SimpNegUnit  : 26
% 2.52/1.44  #BackRed      : 9
% 2.52/1.44  
% 2.52/1.44  #Partial instantiations: 0
% 2.52/1.44  #Strategies tried      : 1
% 2.52/1.44  
% 2.52/1.44  Timing (in seconds)
% 2.52/1.44  ----------------------
% 2.52/1.44  Preprocessing        : 0.28
% 2.52/1.44  Parsing              : 0.15
% 2.52/1.44  CNF conversion       : 0.03
% 2.52/1.44  Main loop            : 0.34
% 2.52/1.44  Inferencing          : 0.14
% 2.52/1.44  Reduction            : 0.08
% 2.52/1.44  Demodulation         : 0.06
% 2.52/1.44  BG Simplification    : 0.02
% 2.52/1.44  Subsumption          : 0.07
% 2.52/1.44  Abstraction          : 0.01
% 2.52/1.44  MUC search           : 0.00
% 2.52/1.44  Cooper               : 0.00
% 2.52/1.44  Total                : 0.66
% 2.52/1.44  Index Insertion      : 0.00
% 2.52/1.44  Index Deletion       : 0.00
% 2.52/1.44  Index Matching       : 0.00
% 2.52/1.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
