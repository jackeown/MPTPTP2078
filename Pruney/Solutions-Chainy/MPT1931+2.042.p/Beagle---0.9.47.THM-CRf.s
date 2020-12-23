%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:51 EST 2020

% Result     : Theorem 2.04s
% Output     : CNFRefutation 2.37s
% Verified   : 
% Statistics : Number of formulae       :   65 (  87 expanded)
%              Number of leaves         :   36 (  49 expanded)
%              Depth                    :   13
%              Number of atoms          :  128 ( 222 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_waybel_0 > r1_waybel_0 > r1_orders_2 > r2_hidden > r1_tarski > m1_subset_1 > l1_waybel_0 > v7_waybel_0 > v4_orders_2 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > k2_waybel_0 > k6_subset_1 > k4_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3

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

tff(f_123,negated_conjecture,(
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
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_30,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_35,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_83,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & l1_waybel_0(B,A) )
         => ! [C] :
              ( r2_waybel_0(A,B,C)
            <=> ~ r1_waybel_0(A,B,k6_subset_1(u1_struct_0(A),C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_waybel_0)).

tff(f_105,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & l1_waybel_0(B,A) )
         => ! [C,D] :
              ( r1_tarski(C,D)
             => ( ( r1_waybel_0(A,B,C)
                 => r1_waybel_0(A,B,D) )
                & ( r2_waybel_0(A,B,C)
                 => r2_waybel_0(A,B,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_waybel_0)).

tff(f_33,axiom,(
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
              ( r2_waybel_0(A,B,C)
            <=> ! [D] :
                  ( m1_subset_1(D,u1_struct_0(B))
                 => ? [E] :
                      ( m1_subset_1(E,u1_struct_0(B))
                      & r1_orders_2(B,D,E)
                      & r2_hidden(k2_waybel_0(A,B,E),C) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_waybel_0)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(c_44,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_40,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_42,plain,(
    l1_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_34,plain,(
    l1_waybel_0('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_4,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_6,plain,(
    ! [A_2] : k4_xboole_0(A_2,k1_xboole_0) = A_2 ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_10,plain,(
    ! [A_5,B_6] : k6_subset_1(A_5,B_6) = k4_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_26,plain,(
    ! [A_63,B_67,C_69] :
      ( r2_waybel_0(A_63,B_67,C_69)
      | r1_waybel_0(A_63,B_67,k6_subset_1(u1_struct_0(A_63),C_69))
      | ~ l1_waybel_0(B_67,A_63)
      | v2_struct_0(B_67)
      | ~ l1_struct_0(A_63)
      | v2_struct_0(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_81,plain,(
    ! [A_104,B_105,C_106] :
      ( r2_waybel_0(A_104,B_105,C_106)
      | r1_waybel_0(A_104,B_105,k4_xboole_0(u1_struct_0(A_104),C_106))
      | ~ l1_waybel_0(B_105,A_104)
      | v2_struct_0(B_105)
      | ~ l1_struct_0(A_104)
      | v2_struct_0(A_104) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_26])).

tff(c_94,plain,(
    ! [A_111,B_112] :
      ( r2_waybel_0(A_111,B_112,k1_xboole_0)
      | r1_waybel_0(A_111,B_112,u1_struct_0(A_111))
      | ~ l1_waybel_0(B_112,A_111)
      | v2_struct_0(B_112)
      | ~ l1_struct_0(A_111)
      | v2_struct_0(A_111) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_81])).

tff(c_32,plain,(
    ~ r1_waybel_0('#skF_4','#skF_5',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_102,plain,
    ( r2_waybel_0('#skF_4','#skF_5',k1_xboole_0)
    | ~ l1_waybel_0('#skF_5','#skF_4')
    | v2_struct_0('#skF_5')
    | ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_94,c_32])).

tff(c_107,plain,
    ( r2_waybel_0('#skF_4','#skF_5',k1_xboole_0)
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_34,c_102])).

tff(c_108,plain,(
    r2_waybel_0('#skF_4','#skF_5',k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_40,c_107])).

tff(c_28,plain,(
    ! [A_70,B_76,D_80,C_79] :
      ( r2_waybel_0(A_70,B_76,D_80)
      | ~ r2_waybel_0(A_70,B_76,C_79)
      | ~ r1_tarski(C_79,D_80)
      | ~ l1_waybel_0(B_76,A_70)
      | v2_struct_0(B_76)
      | ~ l1_struct_0(A_70)
      | v2_struct_0(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_110,plain,(
    ! [D_80] :
      ( r2_waybel_0('#skF_4','#skF_5',D_80)
      | ~ r1_tarski(k1_xboole_0,D_80)
      | ~ l1_waybel_0('#skF_5','#skF_4')
      | v2_struct_0('#skF_5')
      | ~ l1_struct_0('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_108,c_28])).

tff(c_113,plain,(
    ! [D_80] :
      ( r2_waybel_0('#skF_4','#skF_5',D_80)
      | v2_struct_0('#skF_5')
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_34,c_4,c_110])).

tff(c_114,plain,(
    ! [D_80] : r2_waybel_0('#skF_4','#skF_5',D_80) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_40,c_113])).

tff(c_8,plain,(
    ! [A_3] : m1_subset_1('#skF_1'(A_3),A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_130,plain,(
    ! [A_129,B_130,C_131,D_132] :
      ( r2_hidden(k2_waybel_0(A_129,B_130,'#skF_3'(A_129,B_130,C_131,D_132)),C_131)
      | ~ m1_subset_1(D_132,u1_struct_0(B_130))
      | ~ r2_waybel_0(A_129,B_130,C_131)
      | ~ l1_waybel_0(B_130,A_129)
      | v2_struct_0(B_130)
      | ~ l1_struct_0(A_129)
      | v2_struct_0(A_129) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_67,plain,(
    ! [C_87,B_88,A_89] :
      ( ~ v1_xboole_0(C_87)
      | ~ m1_subset_1(B_88,k1_zfmisc_1(C_87))
      | ~ r2_hidden(A_89,B_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_71,plain,(
    ! [C_87,A_89] :
      ( ~ v1_xboole_0(C_87)
      | ~ r2_hidden(A_89,'#skF_1'(k1_zfmisc_1(C_87))) ) ),
    inference(resolution,[status(thm)],[c_8,c_67])).

tff(c_136,plain,(
    ! [C_133,D_134,B_135,A_136] :
      ( ~ v1_xboole_0(C_133)
      | ~ m1_subset_1(D_134,u1_struct_0(B_135))
      | ~ r2_waybel_0(A_136,B_135,'#skF_1'(k1_zfmisc_1(C_133)))
      | ~ l1_waybel_0(B_135,A_136)
      | v2_struct_0(B_135)
      | ~ l1_struct_0(A_136)
      | v2_struct_0(A_136) ) ),
    inference(resolution,[status(thm)],[c_130,c_71])).

tff(c_152,plain,(
    ! [C_141,A_142,B_143] :
      ( ~ v1_xboole_0(C_141)
      | ~ r2_waybel_0(A_142,B_143,'#skF_1'(k1_zfmisc_1(C_141)))
      | ~ l1_waybel_0(B_143,A_142)
      | v2_struct_0(B_143)
      | ~ l1_struct_0(A_142)
      | v2_struct_0(A_142) ) ),
    inference(resolution,[status(thm)],[c_8,c_136])).

tff(c_156,plain,(
    ! [C_141] :
      ( ~ v1_xboole_0(C_141)
      | ~ l1_waybel_0('#skF_5','#skF_4')
      | v2_struct_0('#skF_5')
      | ~ l1_struct_0('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_114,c_152])).

tff(c_159,plain,(
    ! [C_141] :
      ( ~ v1_xboole_0(C_141)
      | v2_struct_0('#skF_5')
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_34,c_156])).

tff(c_160,plain,(
    ! [C_141] : ~ v1_xboole_0(C_141) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_40,c_159])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_162,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_160,c_2])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:15:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.04/1.31  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.04/1.31  
% 2.04/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.04/1.32  %$ r2_waybel_0 > r1_waybel_0 > r1_orders_2 > r2_hidden > r1_tarski > m1_subset_1 > l1_waybel_0 > v7_waybel_0 > v4_orders_2 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > k2_waybel_0 > k6_subset_1 > k4_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3
% 2.04/1.32  
% 2.04/1.32  %Foreground sorts:
% 2.04/1.32  
% 2.04/1.32  
% 2.04/1.32  %Background operators:
% 2.04/1.32  
% 2.04/1.32  
% 2.04/1.32  %Foreground operators:
% 2.04/1.32  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.04/1.32  tff(r2_waybel_0, type, r2_waybel_0: ($i * $i * $i) > $o).
% 2.04/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.04/1.32  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.04/1.32  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.04/1.32  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.04/1.32  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 2.04/1.32  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.04/1.32  tff(k2_waybel_0, type, k2_waybel_0: ($i * $i * $i) > $i).
% 2.04/1.32  tff(v7_waybel_0, type, v7_waybel_0: $i > $o).
% 2.04/1.32  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.04/1.32  tff('#skF_5', type, '#skF_5': $i).
% 2.04/1.32  tff(r1_waybel_0, type, r1_waybel_0: ($i * $i * $i) > $o).
% 2.04/1.32  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 2.04/1.32  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.04/1.32  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.04/1.32  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.04/1.32  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.04/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.04/1.32  tff(l1_waybel_0, type, l1_waybel_0: ($i * $i) > $o).
% 2.04/1.32  tff('#skF_4', type, '#skF_4': $i).
% 2.04/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.04/1.32  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 2.04/1.32  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.04/1.32  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.04/1.32  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.04/1.32  
% 2.37/1.33  tff(f_123, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => r1_waybel_0(A, B, u1_struct_0(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_yellow_6)).
% 2.37/1.33  tff(f_28, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.37/1.33  tff(f_30, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 2.37/1.33  tff(f_35, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 2.37/1.33  tff(f_83, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((~v2_struct_0(B) & l1_waybel_0(B, A)) => (![C]: (r2_waybel_0(A, B, C) <=> ~r1_waybel_0(A, B, k6_subset_1(u1_struct_0(A), C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_waybel_0)).
% 2.37/1.33  tff(f_105, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((~v2_struct_0(B) & l1_waybel_0(B, A)) => (![C, D]: (r1_tarski(C, D) => ((r1_waybel_0(A, B, C) => r1_waybel_0(A, B, D)) & (r2_waybel_0(A, B, C) => r2_waybel_0(A, B, D))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_waybel_0)).
% 2.37/1.33  tff(f_33, axiom, (![A]: (?[B]: m1_subset_1(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', existence_m1_subset_1)).
% 2.37/1.33  tff(f_66, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((~v2_struct_0(B) & l1_waybel_0(B, A)) => (![C]: (r2_waybel_0(A, B, C) <=> (![D]: (m1_subset_1(D, u1_struct_0(B)) => (?[E]: ((m1_subset_1(E, u1_struct_0(B)) & r1_orders_2(B, D, E)) & r2_hidden(k2_waybel_0(A, B, E), C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d12_waybel_0)).
% 2.37/1.33  tff(f_42, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 2.37/1.33  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.37/1.33  tff(c_44, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_123])).
% 2.37/1.33  tff(c_40, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_123])).
% 2.37/1.33  tff(c_42, plain, (l1_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_123])).
% 2.37/1.33  tff(c_34, plain, (l1_waybel_0('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_123])).
% 2.37/1.33  tff(c_4, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_28])).
% 2.37/1.33  tff(c_6, plain, (![A_2]: (k4_xboole_0(A_2, k1_xboole_0)=A_2)), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.37/1.33  tff(c_10, plain, (![A_5, B_6]: (k6_subset_1(A_5, B_6)=k4_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.37/1.33  tff(c_26, plain, (![A_63, B_67, C_69]: (r2_waybel_0(A_63, B_67, C_69) | r1_waybel_0(A_63, B_67, k6_subset_1(u1_struct_0(A_63), C_69)) | ~l1_waybel_0(B_67, A_63) | v2_struct_0(B_67) | ~l1_struct_0(A_63) | v2_struct_0(A_63))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.37/1.33  tff(c_81, plain, (![A_104, B_105, C_106]: (r2_waybel_0(A_104, B_105, C_106) | r1_waybel_0(A_104, B_105, k4_xboole_0(u1_struct_0(A_104), C_106)) | ~l1_waybel_0(B_105, A_104) | v2_struct_0(B_105) | ~l1_struct_0(A_104) | v2_struct_0(A_104))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_26])).
% 2.37/1.33  tff(c_94, plain, (![A_111, B_112]: (r2_waybel_0(A_111, B_112, k1_xboole_0) | r1_waybel_0(A_111, B_112, u1_struct_0(A_111)) | ~l1_waybel_0(B_112, A_111) | v2_struct_0(B_112) | ~l1_struct_0(A_111) | v2_struct_0(A_111))), inference(superposition, [status(thm), theory('equality')], [c_6, c_81])).
% 2.37/1.33  tff(c_32, plain, (~r1_waybel_0('#skF_4', '#skF_5', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_123])).
% 2.37/1.33  tff(c_102, plain, (r2_waybel_0('#skF_4', '#skF_5', k1_xboole_0) | ~l1_waybel_0('#skF_5', '#skF_4') | v2_struct_0('#skF_5') | ~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_94, c_32])).
% 2.37/1.33  tff(c_107, plain, (r2_waybel_0('#skF_4', '#skF_5', k1_xboole_0) | v2_struct_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_34, c_102])).
% 2.37/1.33  tff(c_108, plain, (r2_waybel_0('#skF_4', '#skF_5', k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_44, c_40, c_107])).
% 2.37/1.33  tff(c_28, plain, (![A_70, B_76, D_80, C_79]: (r2_waybel_0(A_70, B_76, D_80) | ~r2_waybel_0(A_70, B_76, C_79) | ~r1_tarski(C_79, D_80) | ~l1_waybel_0(B_76, A_70) | v2_struct_0(B_76) | ~l1_struct_0(A_70) | v2_struct_0(A_70))), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.37/1.33  tff(c_110, plain, (![D_80]: (r2_waybel_0('#skF_4', '#skF_5', D_80) | ~r1_tarski(k1_xboole_0, D_80) | ~l1_waybel_0('#skF_5', '#skF_4') | v2_struct_0('#skF_5') | ~l1_struct_0('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_108, c_28])).
% 2.37/1.33  tff(c_113, plain, (![D_80]: (r2_waybel_0('#skF_4', '#skF_5', D_80) | v2_struct_0('#skF_5') | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_34, c_4, c_110])).
% 2.37/1.33  tff(c_114, plain, (![D_80]: (r2_waybel_0('#skF_4', '#skF_5', D_80))), inference(negUnitSimplification, [status(thm)], [c_44, c_40, c_113])).
% 2.37/1.33  tff(c_8, plain, (![A_3]: (m1_subset_1('#skF_1'(A_3), A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.37/1.33  tff(c_130, plain, (![A_129, B_130, C_131, D_132]: (r2_hidden(k2_waybel_0(A_129, B_130, '#skF_3'(A_129, B_130, C_131, D_132)), C_131) | ~m1_subset_1(D_132, u1_struct_0(B_130)) | ~r2_waybel_0(A_129, B_130, C_131) | ~l1_waybel_0(B_130, A_129) | v2_struct_0(B_130) | ~l1_struct_0(A_129) | v2_struct_0(A_129))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.37/1.33  tff(c_67, plain, (![C_87, B_88, A_89]: (~v1_xboole_0(C_87) | ~m1_subset_1(B_88, k1_zfmisc_1(C_87)) | ~r2_hidden(A_89, B_88))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.37/1.33  tff(c_71, plain, (![C_87, A_89]: (~v1_xboole_0(C_87) | ~r2_hidden(A_89, '#skF_1'(k1_zfmisc_1(C_87))))), inference(resolution, [status(thm)], [c_8, c_67])).
% 2.37/1.33  tff(c_136, plain, (![C_133, D_134, B_135, A_136]: (~v1_xboole_0(C_133) | ~m1_subset_1(D_134, u1_struct_0(B_135)) | ~r2_waybel_0(A_136, B_135, '#skF_1'(k1_zfmisc_1(C_133))) | ~l1_waybel_0(B_135, A_136) | v2_struct_0(B_135) | ~l1_struct_0(A_136) | v2_struct_0(A_136))), inference(resolution, [status(thm)], [c_130, c_71])).
% 2.37/1.33  tff(c_152, plain, (![C_141, A_142, B_143]: (~v1_xboole_0(C_141) | ~r2_waybel_0(A_142, B_143, '#skF_1'(k1_zfmisc_1(C_141))) | ~l1_waybel_0(B_143, A_142) | v2_struct_0(B_143) | ~l1_struct_0(A_142) | v2_struct_0(A_142))), inference(resolution, [status(thm)], [c_8, c_136])).
% 2.37/1.33  tff(c_156, plain, (![C_141]: (~v1_xboole_0(C_141) | ~l1_waybel_0('#skF_5', '#skF_4') | v2_struct_0('#skF_5') | ~l1_struct_0('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_114, c_152])).
% 2.37/1.33  tff(c_159, plain, (![C_141]: (~v1_xboole_0(C_141) | v2_struct_0('#skF_5') | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_34, c_156])).
% 2.37/1.33  tff(c_160, plain, (![C_141]: (~v1_xboole_0(C_141))), inference(negUnitSimplification, [status(thm)], [c_44, c_40, c_159])).
% 2.37/1.33  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.37/1.33  tff(c_162, plain, $false, inference(negUnitSimplification, [status(thm)], [c_160, c_2])).
% 2.37/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.37/1.33  
% 2.37/1.33  Inference rules
% 2.37/1.33  ----------------------
% 2.37/1.33  #Ref     : 0
% 2.37/1.33  #Sup     : 21
% 2.37/1.33  #Fact    : 0
% 2.37/1.33  #Define  : 0
% 2.37/1.33  #Split   : 0
% 2.37/1.33  #Chain   : 0
% 2.37/1.33  #Close   : 0
% 2.37/1.33  
% 2.37/1.33  Ordering : KBO
% 2.37/1.33  
% 2.37/1.33  Simplification rules
% 2.37/1.33  ----------------------
% 2.37/1.33  #Subsume      : 6
% 2.37/1.33  #Demod        : 13
% 2.37/1.33  #Tautology    : 8
% 2.37/1.33  #SimpNegUnit  : 5
% 2.37/1.33  #BackRed      : 1
% 2.37/1.33  
% 2.37/1.33  #Partial instantiations: 0
% 2.37/1.33  #Strategies tried      : 1
% 2.37/1.33  
% 2.37/1.33  Timing (in seconds)
% 2.37/1.33  ----------------------
% 2.37/1.33  Preprocessing        : 0.34
% 2.37/1.33  Parsing              : 0.18
% 2.37/1.33  CNF conversion       : 0.03
% 2.37/1.33  Main loop            : 0.17
% 2.37/1.33  Inferencing          : 0.07
% 2.37/1.33  Reduction            : 0.05
% 2.37/1.33  Demodulation         : 0.03
% 2.37/1.33  BG Simplification    : 0.01
% 2.37/1.33  Subsumption          : 0.03
% 2.37/1.33  Abstraction          : 0.01
% 2.37/1.33  MUC search           : 0.00
% 2.37/1.33  Cooper               : 0.00
% 2.37/1.33  Total                : 0.54
% 2.37/1.33  Index Insertion      : 0.00
% 2.37/1.33  Index Deletion       : 0.00
% 2.37/1.33  Index Matching       : 0.00
% 2.37/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
