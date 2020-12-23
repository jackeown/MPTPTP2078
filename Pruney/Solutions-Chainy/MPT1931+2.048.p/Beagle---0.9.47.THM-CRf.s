%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:52 EST 2020

% Result     : Theorem 2.30s
% Output     : CNFRefutation 2.30s
% Verified   : 
% Statistics : Number of formulae       :   65 (  85 expanded)
%              Number of leaves         :   37 (  49 expanded)
%              Depth                    :   13
%              Number of atoms          :  126 ( 218 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_waybel_0 > r1_waybel_0 > r1_orders_2 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > l1_waybel_0 > v7_waybel_0 > v4_orders_2 > v2_struct_0 > l1_struct_0 > k2_waybel_0 > k6_subset_1 > k4_xboole_0 > k3_xboole_0 > #nlpp > u1_struct_0 > k1_xboole_0 > #skF_2 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(r2_waybel_0,type,(
    r2_waybel_0: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_waybel_0,type,(
    r1_waybel_0: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(l1_waybel_0,type,(
    l1_waybel_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_131,negated_conjecture,(
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

tff(f_41,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_43,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_50,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_91,axiom,(
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

tff(f_113,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_waybel_0)).

tff(f_48,axiom,(
    ! [A] :
    ? [B] : m1_subset_1(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).

tff(f_74,axiom,(
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
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_45,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(c_46,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_42,plain,(
    ~ v2_struct_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_44,plain,(
    l1_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_36,plain,(
    l1_waybel_0('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_6,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_8,plain,(
    ! [A_7] : k4_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_14,plain,(
    ! [A_11,B_12] : k6_subset_1(A_11,B_12) = k4_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_28,plain,(
    ! [A_66,B_70,C_72] :
      ( r2_waybel_0(A_66,B_70,C_72)
      | r1_waybel_0(A_66,B_70,k6_subset_1(u1_struct_0(A_66),C_72))
      | ~ l1_waybel_0(B_70,A_66)
      | v2_struct_0(B_70)
      | ~ l1_struct_0(A_66)
      | v2_struct_0(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_76,plain,(
    ! [A_96,B_97,C_98] :
      ( r2_waybel_0(A_96,B_97,C_98)
      | r1_waybel_0(A_96,B_97,k4_xboole_0(u1_struct_0(A_96),C_98))
      | ~ l1_waybel_0(B_97,A_96)
      | v2_struct_0(B_97)
      | ~ l1_struct_0(A_96)
      | v2_struct_0(A_96) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_28])).

tff(c_85,plain,(
    ! [A_103,B_104] :
      ( r2_waybel_0(A_103,B_104,k1_xboole_0)
      | r1_waybel_0(A_103,B_104,u1_struct_0(A_103))
      | ~ l1_waybel_0(B_104,A_103)
      | v2_struct_0(B_104)
      | ~ l1_struct_0(A_103)
      | v2_struct_0(A_103) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_76])).

tff(c_34,plain,(
    ~ r1_waybel_0('#skF_5','#skF_6',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_90,plain,
    ( r2_waybel_0('#skF_5','#skF_6',k1_xboole_0)
    | ~ l1_waybel_0('#skF_6','#skF_5')
    | v2_struct_0('#skF_6')
    | ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_85,c_34])).

tff(c_94,plain,
    ( r2_waybel_0('#skF_5','#skF_6',k1_xboole_0)
    | v2_struct_0('#skF_6')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_36,c_90])).

tff(c_95,plain,(
    r2_waybel_0('#skF_5','#skF_6',k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_42,c_94])).

tff(c_96,plain,(
    ! [A_105,B_106,D_107,C_108] :
      ( r2_waybel_0(A_105,B_106,D_107)
      | ~ r2_waybel_0(A_105,B_106,C_108)
      | ~ r1_tarski(C_108,D_107)
      | ~ l1_waybel_0(B_106,A_105)
      | v2_struct_0(B_106)
      | ~ l1_struct_0(A_105)
      | v2_struct_0(A_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_98,plain,(
    ! [D_107] :
      ( r2_waybel_0('#skF_5','#skF_6',D_107)
      | ~ r1_tarski(k1_xboole_0,D_107)
      | ~ l1_waybel_0('#skF_6','#skF_5')
      | v2_struct_0('#skF_6')
      | ~ l1_struct_0('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_95,c_96])).

tff(c_101,plain,(
    ! [D_107] :
      ( r2_waybel_0('#skF_5','#skF_6',D_107)
      | v2_struct_0('#skF_6')
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_36,c_6,c_98])).

tff(c_102,plain,(
    ! [D_107] : r2_waybel_0('#skF_5','#skF_6',D_107) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_42,c_101])).

tff(c_12,plain,(
    ! [A_9] : m1_subset_1('#skF_2'(A_9),A_9) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_133,plain,(
    ! [A_133,B_134,C_135,D_136] :
      ( r2_hidden(k2_waybel_0(A_133,B_134,'#skF_4'(A_133,B_134,C_135,D_136)),C_135)
      | ~ m1_subset_1(D_136,u1_struct_0(B_134))
      | ~ r2_waybel_0(A_133,B_134,C_135)
      | ~ l1_waybel_0(B_134,A_133)
      | v2_struct_0(B_134)
      | ~ l1_struct_0(A_133)
      | v2_struct_0(A_133) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_4,plain,(
    ! [A_1,B_2,C_5] :
      ( ~ r1_xboole_0(A_1,B_2)
      | ~ r2_hidden(C_5,k3_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_139,plain,(
    ! [D_141,A_137,B_138,B_139,A_140] :
      ( ~ r1_xboole_0(A_140,B_139)
      | ~ m1_subset_1(D_141,u1_struct_0(B_138))
      | ~ r2_waybel_0(A_137,B_138,k3_xboole_0(A_140,B_139))
      | ~ l1_waybel_0(B_138,A_137)
      | v2_struct_0(B_138)
      | ~ l1_struct_0(A_137)
      | v2_struct_0(A_137) ) ),
    inference(resolution,[status(thm)],[c_133,c_4])).

tff(c_155,plain,(
    ! [A_146,B_147,A_148,B_149] :
      ( ~ r1_xboole_0(A_146,B_147)
      | ~ r2_waybel_0(A_148,B_149,k3_xboole_0(A_146,B_147))
      | ~ l1_waybel_0(B_149,A_148)
      | v2_struct_0(B_149)
      | ~ l1_struct_0(A_148)
      | v2_struct_0(A_148) ) ),
    inference(resolution,[status(thm)],[c_12,c_139])).

tff(c_159,plain,(
    ! [A_146,B_147] :
      ( ~ r1_xboole_0(A_146,B_147)
      | ~ l1_waybel_0('#skF_6','#skF_5')
      | v2_struct_0('#skF_6')
      | ~ l1_struct_0('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_102,c_155])).

tff(c_162,plain,(
    ! [A_146,B_147] :
      ( ~ r1_xboole_0(A_146,B_147)
      | v2_struct_0('#skF_6')
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_36,c_159])).

tff(c_163,plain,(
    ! [A_146,B_147] : ~ r1_xboole_0(A_146,B_147) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_42,c_162])).

tff(c_10,plain,(
    ! [A_8] : r1_xboole_0(A_8,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_166,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_163,c_10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n016.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:43:49 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.30/1.25  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.30/1.25  
% 2.30/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.30/1.25  %$ r2_waybel_0 > r1_waybel_0 > r1_orders_2 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > l1_waybel_0 > v7_waybel_0 > v4_orders_2 > v2_struct_0 > l1_struct_0 > k2_waybel_0 > k6_subset_1 > k4_xboole_0 > k3_xboole_0 > #nlpp > u1_struct_0 > k1_xboole_0 > #skF_2 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_1
% 2.30/1.25  
% 2.30/1.25  %Foreground sorts:
% 2.30/1.25  
% 2.30/1.25  
% 2.30/1.25  %Background operators:
% 2.30/1.25  
% 2.30/1.25  
% 2.30/1.25  %Foreground operators:
% 2.30/1.25  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.30/1.25  tff(r2_waybel_0, type, r2_waybel_0: ($i * $i * $i) > $o).
% 2.30/1.25  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.30/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.30/1.25  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.30/1.25  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.30/1.25  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 2.30/1.25  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.30/1.25  tff(k2_waybel_0, type, k2_waybel_0: ($i * $i * $i) > $i).
% 2.30/1.25  tff(v7_waybel_0, type, v7_waybel_0: $i > $o).
% 2.30/1.25  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.30/1.25  tff('#skF_5', type, '#skF_5': $i).
% 2.30/1.25  tff(r1_waybel_0, type, r1_waybel_0: ($i * $i * $i) > $o).
% 2.30/1.25  tff('#skF_6', type, '#skF_6': $i).
% 2.30/1.25  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.30/1.25  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 2.30/1.25  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.30/1.25  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.30/1.25  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 2.30/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.30/1.25  tff(l1_waybel_0, type, l1_waybel_0: ($i * $i) > $o).
% 2.30/1.25  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.30/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.30/1.25  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.30/1.25  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.30/1.25  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.30/1.25  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.30/1.25  
% 2.30/1.27  tff(f_131, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => r1_waybel_0(A, B, u1_struct_0(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_yellow_6)).
% 2.30/1.27  tff(f_41, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.30/1.27  tff(f_43, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 2.30/1.27  tff(f_50, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 2.30/1.27  tff(f_91, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((~v2_struct_0(B) & l1_waybel_0(B, A)) => (![C]: (r2_waybel_0(A, B, C) <=> ~r1_waybel_0(A, B, k6_subset_1(u1_struct_0(A), C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_waybel_0)).
% 2.30/1.27  tff(f_113, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((~v2_struct_0(B) & l1_waybel_0(B, A)) => (![C, D]: (r1_tarski(C, D) => ((r1_waybel_0(A, B, C) => r1_waybel_0(A, B, D)) & (r2_waybel_0(A, B, C) => r2_waybel_0(A, B, D))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_waybel_0)).
% 2.30/1.27  tff(f_48, axiom, (![A]: (?[B]: m1_subset_1(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', existence_m1_subset_1)).
% 2.30/1.27  tff(f_74, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((~v2_struct_0(B) & l1_waybel_0(B, A)) => (![C]: (r2_waybel_0(A, B, C) <=> (![D]: (m1_subset_1(D, u1_struct_0(B)) => (?[E]: ((m1_subset_1(E, u1_struct_0(B)) & r1_orders_2(B, D, E)) & r2_hidden(k2_waybel_0(A, B, E), C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_waybel_0)).
% 2.30/1.27  tff(f_39, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.30/1.27  tff(f_45, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.30/1.27  tff(c_46, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_131])).
% 2.30/1.27  tff(c_42, plain, (~v2_struct_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_131])).
% 2.30/1.27  tff(c_44, plain, (l1_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_131])).
% 2.30/1.27  tff(c_36, plain, (l1_waybel_0('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_131])).
% 2.30/1.27  tff(c_6, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.30/1.27  tff(c_8, plain, (![A_7]: (k4_xboole_0(A_7, k1_xboole_0)=A_7)), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.30/1.27  tff(c_14, plain, (![A_11, B_12]: (k6_subset_1(A_11, B_12)=k4_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.30/1.27  tff(c_28, plain, (![A_66, B_70, C_72]: (r2_waybel_0(A_66, B_70, C_72) | r1_waybel_0(A_66, B_70, k6_subset_1(u1_struct_0(A_66), C_72)) | ~l1_waybel_0(B_70, A_66) | v2_struct_0(B_70) | ~l1_struct_0(A_66) | v2_struct_0(A_66))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.30/1.27  tff(c_76, plain, (![A_96, B_97, C_98]: (r2_waybel_0(A_96, B_97, C_98) | r1_waybel_0(A_96, B_97, k4_xboole_0(u1_struct_0(A_96), C_98)) | ~l1_waybel_0(B_97, A_96) | v2_struct_0(B_97) | ~l1_struct_0(A_96) | v2_struct_0(A_96))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_28])).
% 2.30/1.27  tff(c_85, plain, (![A_103, B_104]: (r2_waybel_0(A_103, B_104, k1_xboole_0) | r1_waybel_0(A_103, B_104, u1_struct_0(A_103)) | ~l1_waybel_0(B_104, A_103) | v2_struct_0(B_104) | ~l1_struct_0(A_103) | v2_struct_0(A_103))), inference(superposition, [status(thm), theory('equality')], [c_8, c_76])).
% 2.30/1.27  tff(c_34, plain, (~r1_waybel_0('#skF_5', '#skF_6', u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_131])).
% 2.30/1.27  tff(c_90, plain, (r2_waybel_0('#skF_5', '#skF_6', k1_xboole_0) | ~l1_waybel_0('#skF_6', '#skF_5') | v2_struct_0('#skF_6') | ~l1_struct_0('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_85, c_34])).
% 2.30/1.27  tff(c_94, plain, (r2_waybel_0('#skF_5', '#skF_6', k1_xboole_0) | v2_struct_0('#skF_6') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_36, c_90])).
% 2.30/1.27  tff(c_95, plain, (r2_waybel_0('#skF_5', '#skF_6', k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_46, c_42, c_94])).
% 2.30/1.27  tff(c_96, plain, (![A_105, B_106, D_107, C_108]: (r2_waybel_0(A_105, B_106, D_107) | ~r2_waybel_0(A_105, B_106, C_108) | ~r1_tarski(C_108, D_107) | ~l1_waybel_0(B_106, A_105) | v2_struct_0(B_106) | ~l1_struct_0(A_105) | v2_struct_0(A_105))), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.30/1.27  tff(c_98, plain, (![D_107]: (r2_waybel_0('#skF_5', '#skF_6', D_107) | ~r1_tarski(k1_xboole_0, D_107) | ~l1_waybel_0('#skF_6', '#skF_5') | v2_struct_0('#skF_6') | ~l1_struct_0('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_95, c_96])).
% 2.30/1.27  tff(c_101, plain, (![D_107]: (r2_waybel_0('#skF_5', '#skF_6', D_107) | v2_struct_0('#skF_6') | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_36, c_6, c_98])).
% 2.30/1.27  tff(c_102, plain, (![D_107]: (r2_waybel_0('#skF_5', '#skF_6', D_107))), inference(negUnitSimplification, [status(thm)], [c_46, c_42, c_101])).
% 2.30/1.27  tff(c_12, plain, (![A_9]: (m1_subset_1('#skF_2'(A_9), A_9))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.30/1.27  tff(c_133, plain, (![A_133, B_134, C_135, D_136]: (r2_hidden(k2_waybel_0(A_133, B_134, '#skF_4'(A_133, B_134, C_135, D_136)), C_135) | ~m1_subset_1(D_136, u1_struct_0(B_134)) | ~r2_waybel_0(A_133, B_134, C_135) | ~l1_waybel_0(B_134, A_133) | v2_struct_0(B_134) | ~l1_struct_0(A_133) | v2_struct_0(A_133))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.30/1.27  tff(c_4, plain, (![A_1, B_2, C_5]: (~r1_xboole_0(A_1, B_2) | ~r2_hidden(C_5, k3_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.30/1.27  tff(c_139, plain, (![D_141, A_137, B_138, B_139, A_140]: (~r1_xboole_0(A_140, B_139) | ~m1_subset_1(D_141, u1_struct_0(B_138)) | ~r2_waybel_0(A_137, B_138, k3_xboole_0(A_140, B_139)) | ~l1_waybel_0(B_138, A_137) | v2_struct_0(B_138) | ~l1_struct_0(A_137) | v2_struct_0(A_137))), inference(resolution, [status(thm)], [c_133, c_4])).
% 2.30/1.27  tff(c_155, plain, (![A_146, B_147, A_148, B_149]: (~r1_xboole_0(A_146, B_147) | ~r2_waybel_0(A_148, B_149, k3_xboole_0(A_146, B_147)) | ~l1_waybel_0(B_149, A_148) | v2_struct_0(B_149) | ~l1_struct_0(A_148) | v2_struct_0(A_148))), inference(resolution, [status(thm)], [c_12, c_139])).
% 2.30/1.27  tff(c_159, plain, (![A_146, B_147]: (~r1_xboole_0(A_146, B_147) | ~l1_waybel_0('#skF_6', '#skF_5') | v2_struct_0('#skF_6') | ~l1_struct_0('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_102, c_155])).
% 2.30/1.27  tff(c_162, plain, (![A_146, B_147]: (~r1_xboole_0(A_146, B_147) | v2_struct_0('#skF_6') | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_36, c_159])).
% 2.30/1.27  tff(c_163, plain, (![A_146, B_147]: (~r1_xboole_0(A_146, B_147))), inference(negUnitSimplification, [status(thm)], [c_46, c_42, c_162])).
% 2.30/1.27  tff(c_10, plain, (![A_8]: (r1_xboole_0(A_8, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.30/1.27  tff(c_166, plain, $false, inference(negUnitSimplification, [status(thm)], [c_163, c_10])).
% 2.30/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.30/1.27  
% 2.30/1.27  Inference rules
% 2.30/1.27  ----------------------
% 2.30/1.27  #Ref     : 0
% 2.30/1.27  #Sup     : 21
% 2.30/1.27  #Fact    : 0
% 2.30/1.27  #Define  : 0
% 2.30/1.27  #Split   : 0
% 2.30/1.27  #Chain   : 0
% 2.30/1.27  #Close   : 0
% 2.30/1.27  
% 2.30/1.27  Ordering : KBO
% 2.30/1.27  
% 2.30/1.27  Simplification rules
% 2.30/1.27  ----------------------
% 2.30/1.27  #Subsume      : 5
% 2.30/1.27  #Demod        : 13
% 2.30/1.27  #Tautology    : 9
% 2.30/1.27  #SimpNegUnit  : 6
% 2.30/1.27  #BackRed      : 2
% 2.30/1.27  
% 2.30/1.27  #Partial instantiations: 0
% 2.30/1.27  #Strategies tried      : 1
% 2.30/1.27  
% 2.30/1.27  Timing (in seconds)
% 2.30/1.27  ----------------------
% 2.30/1.27  Preprocessing        : 0.32
% 2.30/1.27  Parsing              : 0.17
% 2.30/1.27  CNF conversion       : 0.03
% 2.30/1.27  Main loop            : 0.19
% 2.30/1.27  Inferencing          : 0.08
% 2.30/1.27  Reduction            : 0.06
% 2.30/1.27  Demodulation         : 0.04
% 2.30/1.27  BG Simplification    : 0.01
% 2.30/1.27  Subsumption          : 0.03
% 2.30/1.27  Abstraction          : 0.01
% 2.30/1.27  MUC search           : 0.00
% 2.30/1.27  Cooper               : 0.00
% 2.30/1.27  Total                : 0.54
% 2.30/1.27  Index Insertion      : 0.00
% 2.30/1.27  Index Deletion       : 0.00
% 2.30/1.27  Index Matching       : 0.00
% 2.30/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
