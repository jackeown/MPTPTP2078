%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:51 EST 2020

% Result     : Theorem 2.21s
% Output     : CNFRefutation 2.21s
% Verified   : 
% Statistics : Number of formulae       :   64 (  84 expanded)
%              Number of leaves         :   34 (  47 expanded)
%              Depth                    :   12
%              Number of atoms          :  136 ( 234 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_waybel_0 > r1_waybel_0 > r1_orders_2 > r2_hidden > r1_tarski > m1_subset_1 > l1_waybel_0 > v7_waybel_0 > v4_orders_2 > v2_struct_0 > l1_struct_0 > k2_waybel_0 > o_2_2_yellow_6 > k6_subset_1 > k4_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(o_2_2_yellow_6,type,(
    o_2_2_yellow_6: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(r2_waybel_0,type,(
    r2_waybel_0: ( $i * $i * $i ) > $o )).

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

tff(r1_waybel_0,type,(
    r1_waybel_0: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_121,negated_conjecture,(
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

tff(f_27,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_29,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_87,axiom,(
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

tff(f_103,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A)
        & ~ v2_struct_0(B)
        & v4_orders_2(B)
        & v7_waybel_0(B)
        & l1_waybel_0(B,A) )
     => m1_subset_1(o_2_2_yellow_6(A,B),u1_struct_0(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_o_2_2_yellow_6)).

tff(f_31,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_70,axiom,(
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

tff(f_46,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_44,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_42,plain,(
    l1_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_34,plain,(
    l1_waybel_0('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_40,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_38,plain,(
    v4_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_36,plain,(
    v7_waybel_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_2,plain,(
    ! [A_1] : k4_xboole_0(A_1,k1_xboole_0) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_2,B_3] : k6_subset_1(A_2,B_3) = k4_xboole_0(A_2,B_3) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_28,plain,(
    ! [A_65,B_69,C_71] :
      ( r2_waybel_0(A_65,B_69,C_71)
      | r1_waybel_0(A_65,B_69,k6_subset_1(u1_struct_0(A_65),C_71))
      | ~ l1_waybel_0(B_69,A_65)
      | v2_struct_0(B_69)
      | ~ l1_struct_0(A_65)
      | v2_struct_0(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_95,plain,(
    ! [A_104,B_105,C_106] :
      ( r2_waybel_0(A_104,B_105,C_106)
      | r1_waybel_0(A_104,B_105,k4_xboole_0(u1_struct_0(A_104),C_106))
      | ~ l1_waybel_0(B_105,A_104)
      | v2_struct_0(B_105)
      | ~ l1_struct_0(A_104)
      | v2_struct_0(A_104) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_28])).

tff(c_104,plain,(
    ! [A_107,B_108] :
      ( r2_waybel_0(A_107,B_108,k1_xboole_0)
      | r1_waybel_0(A_107,B_108,u1_struct_0(A_107))
      | ~ l1_waybel_0(B_108,A_107)
      | v2_struct_0(B_108)
      | ~ l1_struct_0(A_107)
      | v2_struct_0(A_107) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_95])).

tff(c_32,plain,(
    ~ r1_waybel_0('#skF_3','#skF_4',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_110,plain,
    ( r2_waybel_0('#skF_3','#skF_4',k1_xboole_0)
    | ~ l1_waybel_0('#skF_4','#skF_3')
    | v2_struct_0('#skF_4')
    | ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_104,c_32])).

tff(c_114,plain,
    ( r2_waybel_0('#skF_3','#skF_4',k1_xboole_0)
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_34,c_110])).

tff(c_115,plain,(
    r2_waybel_0('#skF_3','#skF_4',k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_40,c_114])).

tff(c_30,plain,(
    ! [A_72,B_73] :
      ( m1_subset_1(o_2_2_yellow_6(A_72,B_73),u1_struct_0(B_73))
      | ~ l1_waybel_0(B_73,A_72)
      | ~ v7_waybel_0(B_73)
      | ~ v4_orders_2(B_73)
      | v2_struct_0(B_73)
      | ~ l1_struct_0(A_72)
      | v2_struct_0(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_6,plain,(
    ! [A_4] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_4)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_68,plain,(
    ! [A_83,B_84] :
      ( r1_tarski(A_83,B_84)
      | ~ m1_subset_1(A_83,k1_zfmisc_1(B_84)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_76,plain,(
    ! [A_4] : r1_tarski(k1_xboole_0,A_4) ),
    inference(resolution,[status(thm)],[c_6,c_68])).

tff(c_118,plain,(
    ! [A_117,B_118,C_119,D_120] :
      ( r2_hidden(k2_waybel_0(A_117,B_118,'#skF_2'(A_117,B_118,C_119,D_120)),C_119)
      | ~ m1_subset_1(D_120,u1_struct_0(B_118))
      | ~ r2_waybel_0(A_117,B_118,C_119)
      | ~ l1_waybel_0(B_118,A_117)
      | v2_struct_0(B_118)
      | ~ l1_struct_0(A_117)
      | v2_struct_0(A_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_14,plain,(
    ! [B_11,A_10] :
      ( ~ r1_tarski(B_11,A_10)
      | ~ r2_hidden(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_130,plain,(
    ! [C_121,A_122,B_123,D_124] :
      ( ~ r1_tarski(C_121,k2_waybel_0(A_122,B_123,'#skF_2'(A_122,B_123,C_121,D_124)))
      | ~ m1_subset_1(D_124,u1_struct_0(B_123))
      | ~ r2_waybel_0(A_122,B_123,C_121)
      | ~ l1_waybel_0(B_123,A_122)
      | v2_struct_0(B_123)
      | ~ l1_struct_0(A_122)
      | v2_struct_0(A_122) ) ),
    inference(resolution,[status(thm)],[c_118,c_14])).

tff(c_136,plain,(
    ! [D_125,B_126,A_127] :
      ( ~ m1_subset_1(D_125,u1_struct_0(B_126))
      | ~ r2_waybel_0(A_127,B_126,k1_xboole_0)
      | ~ l1_waybel_0(B_126,A_127)
      | v2_struct_0(B_126)
      | ~ l1_struct_0(A_127)
      | v2_struct_0(A_127) ) ),
    inference(resolution,[status(thm)],[c_76,c_130])).

tff(c_165,plain,(
    ! [A_138,B_139,A_140] :
      ( ~ r2_waybel_0(A_138,B_139,k1_xboole_0)
      | ~ l1_waybel_0(B_139,A_138)
      | ~ l1_struct_0(A_138)
      | v2_struct_0(A_138)
      | ~ l1_waybel_0(B_139,A_140)
      | ~ v7_waybel_0(B_139)
      | ~ v4_orders_2(B_139)
      | v2_struct_0(B_139)
      | ~ l1_struct_0(A_140)
      | v2_struct_0(A_140) ) ),
    inference(resolution,[status(thm)],[c_30,c_136])).

tff(c_170,plain,(
    ! [A_140] :
      ( ~ l1_waybel_0('#skF_4','#skF_3')
      | ~ l1_struct_0('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ l1_waybel_0('#skF_4',A_140)
      | ~ v7_waybel_0('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ l1_struct_0(A_140)
      | v2_struct_0(A_140) ) ),
    inference(resolution,[status(thm)],[c_115,c_165])).

tff(c_177,plain,(
    ! [A_140] :
      ( v2_struct_0('#skF_3')
      | ~ l1_waybel_0('#skF_4',A_140)
      | v2_struct_0('#skF_4')
      | ~ l1_struct_0(A_140)
      | v2_struct_0(A_140) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_42,c_34,c_170])).

tff(c_179,plain,(
    ! [A_141] :
      ( ~ l1_waybel_0('#skF_4',A_141)
      | ~ l1_struct_0(A_141)
      | v2_struct_0(A_141) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_44,c_177])).

tff(c_182,plain,
    ( ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_179])).

tff(c_185,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_182])).

tff(c_187,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_185])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:39:27 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.21/1.25  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.21/1.25  
% 2.21/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.21/1.25  %$ r2_waybel_0 > r1_waybel_0 > r1_orders_2 > r2_hidden > r1_tarski > m1_subset_1 > l1_waybel_0 > v7_waybel_0 > v4_orders_2 > v2_struct_0 > l1_struct_0 > k2_waybel_0 > o_2_2_yellow_6 > k6_subset_1 > k4_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 2.21/1.25  
% 2.21/1.25  %Foreground sorts:
% 2.21/1.25  
% 2.21/1.25  
% 2.21/1.25  %Background operators:
% 2.21/1.25  
% 2.21/1.25  
% 2.21/1.25  %Foreground operators:
% 2.21/1.25  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.21/1.25  tff(o_2_2_yellow_6, type, o_2_2_yellow_6: ($i * $i) > $i).
% 2.21/1.25  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.21/1.25  tff(r2_waybel_0, type, r2_waybel_0: ($i * $i * $i) > $o).
% 2.21/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.21/1.25  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.21/1.25  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.21/1.25  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 2.21/1.25  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.21/1.25  tff(k2_waybel_0, type, k2_waybel_0: ($i * $i * $i) > $i).
% 2.21/1.25  tff(v7_waybel_0, type, v7_waybel_0: $i > $o).
% 2.21/1.25  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.21/1.25  tff(r1_waybel_0, type, r1_waybel_0: ($i * $i * $i) > $o).
% 2.21/1.25  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.21/1.25  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 2.21/1.25  tff('#skF_3', type, '#skF_3': $i).
% 2.21/1.25  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.21/1.25  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.21/1.25  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.21/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.21/1.25  tff(l1_waybel_0, type, l1_waybel_0: ($i * $i) > $o).
% 2.21/1.25  tff('#skF_4', type, '#skF_4': $i).
% 2.21/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.21/1.25  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.21/1.25  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.21/1.25  
% 2.21/1.27  tff(f_121, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => r1_waybel_0(A, B, u1_struct_0(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_yellow_6)).
% 2.21/1.27  tff(f_27, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 2.21/1.27  tff(f_29, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 2.21/1.27  tff(f_87, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((~v2_struct_0(B) & l1_waybel_0(B, A)) => (![C]: (r2_waybel_0(A, B, C) <=> ~r1_waybel_0(A, B, k6_subset_1(u1_struct_0(A), C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_waybel_0)).
% 2.21/1.27  tff(f_103, axiom, (![A, B]: ((((((~v2_struct_0(A) & l1_struct_0(A)) & ~v2_struct_0(B)) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => m1_subset_1(o_2_2_yellow_6(A, B), u1_struct_0(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_o_2_2_yellow_6)).
% 2.21/1.27  tff(f_31, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 2.21/1.27  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.21/1.27  tff(f_70, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((~v2_struct_0(B) & l1_waybel_0(B, A)) => (![C]: (r2_waybel_0(A, B, C) <=> (![D]: (m1_subset_1(D, u1_struct_0(B)) => (?[E]: ((m1_subset_1(E, u1_struct_0(B)) & r1_orders_2(B, D, E)) & r2_hidden(k2_waybel_0(A, B, E), C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_waybel_0)).
% 2.21/1.27  tff(f_46, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 2.21/1.27  tff(c_44, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_121])).
% 2.21/1.27  tff(c_42, plain, (l1_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_121])).
% 2.21/1.27  tff(c_34, plain, (l1_waybel_0('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_121])).
% 2.21/1.27  tff(c_40, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_121])).
% 2.21/1.27  tff(c_38, plain, (v4_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_121])).
% 2.21/1.27  tff(c_36, plain, (v7_waybel_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_121])).
% 2.21/1.27  tff(c_2, plain, (![A_1]: (k4_xboole_0(A_1, k1_xboole_0)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.21/1.27  tff(c_4, plain, (![A_2, B_3]: (k6_subset_1(A_2, B_3)=k4_xboole_0(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.21/1.27  tff(c_28, plain, (![A_65, B_69, C_71]: (r2_waybel_0(A_65, B_69, C_71) | r1_waybel_0(A_65, B_69, k6_subset_1(u1_struct_0(A_65), C_71)) | ~l1_waybel_0(B_69, A_65) | v2_struct_0(B_69) | ~l1_struct_0(A_65) | v2_struct_0(A_65))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.21/1.27  tff(c_95, plain, (![A_104, B_105, C_106]: (r2_waybel_0(A_104, B_105, C_106) | r1_waybel_0(A_104, B_105, k4_xboole_0(u1_struct_0(A_104), C_106)) | ~l1_waybel_0(B_105, A_104) | v2_struct_0(B_105) | ~l1_struct_0(A_104) | v2_struct_0(A_104))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_28])).
% 2.21/1.27  tff(c_104, plain, (![A_107, B_108]: (r2_waybel_0(A_107, B_108, k1_xboole_0) | r1_waybel_0(A_107, B_108, u1_struct_0(A_107)) | ~l1_waybel_0(B_108, A_107) | v2_struct_0(B_108) | ~l1_struct_0(A_107) | v2_struct_0(A_107))), inference(superposition, [status(thm), theory('equality')], [c_2, c_95])).
% 2.21/1.27  tff(c_32, plain, (~r1_waybel_0('#skF_3', '#skF_4', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_121])).
% 2.21/1.27  tff(c_110, plain, (r2_waybel_0('#skF_3', '#skF_4', k1_xboole_0) | ~l1_waybel_0('#skF_4', '#skF_3') | v2_struct_0('#skF_4') | ~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_104, c_32])).
% 2.21/1.27  tff(c_114, plain, (r2_waybel_0('#skF_3', '#skF_4', k1_xboole_0) | v2_struct_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_34, c_110])).
% 2.21/1.27  tff(c_115, plain, (r2_waybel_0('#skF_3', '#skF_4', k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_44, c_40, c_114])).
% 2.21/1.27  tff(c_30, plain, (![A_72, B_73]: (m1_subset_1(o_2_2_yellow_6(A_72, B_73), u1_struct_0(B_73)) | ~l1_waybel_0(B_73, A_72) | ~v7_waybel_0(B_73) | ~v4_orders_2(B_73) | v2_struct_0(B_73) | ~l1_struct_0(A_72) | v2_struct_0(A_72))), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.21/1.27  tff(c_6, plain, (![A_4]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.21/1.27  tff(c_68, plain, (![A_83, B_84]: (r1_tarski(A_83, B_84) | ~m1_subset_1(A_83, k1_zfmisc_1(B_84)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.21/1.27  tff(c_76, plain, (![A_4]: (r1_tarski(k1_xboole_0, A_4))), inference(resolution, [status(thm)], [c_6, c_68])).
% 2.21/1.27  tff(c_118, plain, (![A_117, B_118, C_119, D_120]: (r2_hidden(k2_waybel_0(A_117, B_118, '#skF_2'(A_117, B_118, C_119, D_120)), C_119) | ~m1_subset_1(D_120, u1_struct_0(B_118)) | ~r2_waybel_0(A_117, B_118, C_119) | ~l1_waybel_0(B_118, A_117) | v2_struct_0(B_118) | ~l1_struct_0(A_117) | v2_struct_0(A_117))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.21/1.27  tff(c_14, plain, (![B_11, A_10]: (~r1_tarski(B_11, A_10) | ~r2_hidden(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.21/1.27  tff(c_130, plain, (![C_121, A_122, B_123, D_124]: (~r1_tarski(C_121, k2_waybel_0(A_122, B_123, '#skF_2'(A_122, B_123, C_121, D_124))) | ~m1_subset_1(D_124, u1_struct_0(B_123)) | ~r2_waybel_0(A_122, B_123, C_121) | ~l1_waybel_0(B_123, A_122) | v2_struct_0(B_123) | ~l1_struct_0(A_122) | v2_struct_0(A_122))), inference(resolution, [status(thm)], [c_118, c_14])).
% 2.21/1.27  tff(c_136, plain, (![D_125, B_126, A_127]: (~m1_subset_1(D_125, u1_struct_0(B_126)) | ~r2_waybel_0(A_127, B_126, k1_xboole_0) | ~l1_waybel_0(B_126, A_127) | v2_struct_0(B_126) | ~l1_struct_0(A_127) | v2_struct_0(A_127))), inference(resolution, [status(thm)], [c_76, c_130])).
% 2.21/1.27  tff(c_165, plain, (![A_138, B_139, A_140]: (~r2_waybel_0(A_138, B_139, k1_xboole_0) | ~l1_waybel_0(B_139, A_138) | ~l1_struct_0(A_138) | v2_struct_0(A_138) | ~l1_waybel_0(B_139, A_140) | ~v7_waybel_0(B_139) | ~v4_orders_2(B_139) | v2_struct_0(B_139) | ~l1_struct_0(A_140) | v2_struct_0(A_140))), inference(resolution, [status(thm)], [c_30, c_136])).
% 2.21/1.27  tff(c_170, plain, (![A_140]: (~l1_waybel_0('#skF_4', '#skF_3') | ~l1_struct_0('#skF_3') | v2_struct_0('#skF_3') | ~l1_waybel_0('#skF_4', A_140) | ~v7_waybel_0('#skF_4') | ~v4_orders_2('#skF_4') | v2_struct_0('#skF_4') | ~l1_struct_0(A_140) | v2_struct_0(A_140))), inference(resolution, [status(thm)], [c_115, c_165])).
% 2.21/1.27  tff(c_177, plain, (![A_140]: (v2_struct_0('#skF_3') | ~l1_waybel_0('#skF_4', A_140) | v2_struct_0('#skF_4') | ~l1_struct_0(A_140) | v2_struct_0(A_140))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_42, c_34, c_170])).
% 2.21/1.27  tff(c_179, plain, (![A_141]: (~l1_waybel_0('#skF_4', A_141) | ~l1_struct_0(A_141) | v2_struct_0(A_141))), inference(negUnitSimplification, [status(thm)], [c_40, c_44, c_177])).
% 2.21/1.27  tff(c_182, plain, (~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_34, c_179])).
% 2.21/1.27  tff(c_185, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_182])).
% 2.21/1.27  tff(c_187, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_185])).
% 2.21/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.21/1.27  
% 2.21/1.27  Inference rules
% 2.21/1.27  ----------------------
% 2.21/1.27  #Ref     : 0
% 2.21/1.27  #Sup     : 26
% 2.21/1.27  #Fact    : 0
% 2.21/1.27  #Define  : 0
% 2.21/1.27  #Split   : 0
% 2.21/1.27  #Chain   : 0
% 2.21/1.27  #Close   : 0
% 2.21/1.27  
% 2.21/1.27  Ordering : KBO
% 2.21/1.27  
% 2.21/1.27  Simplification rules
% 2.21/1.27  ----------------------
% 2.21/1.27  #Subsume      : 3
% 2.21/1.27  #Demod        : 13
% 2.21/1.27  #Tautology    : 7
% 2.21/1.27  #SimpNegUnit  : 6
% 2.21/1.27  #BackRed      : 0
% 2.21/1.27  
% 2.21/1.27  #Partial instantiations: 0
% 2.21/1.27  #Strategies tried      : 1
% 2.21/1.27  
% 2.21/1.27  Timing (in seconds)
% 2.21/1.27  ----------------------
% 2.21/1.27  Preprocessing        : 0.32
% 2.21/1.27  Parsing              : 0.17
% 2.21/1.27  CNF conversion       : 0.02
% 2.21/1.27  Main loop            : 0.18
% 2.21/1.27  Inferencing          : 0.08
% 2.21/1.27  Reduction            : 0.05
% 2.21/1.27  Demodulation         : 0.03
% 2.21/1.27  BG Simplification    : 0.01
% 2.21/1.27  Subsumption          : 0.03
% 2.21/1.27  Abstraction          : 0.01
% 2.21/1.27  MUC search           : 0.00
% 2.21/1.27  Cooper               : 0.00
% 2.21/1.27  Total                : 0.53
% 2.21/1.27  Index Insertion      : 0.00
% 2.21/1.27  Index Deletion       : 0.00
% 2.21/1.27  Index Matching       : 0.00
% 2.21/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
