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
% DateTime   : Thu Dec  3 10:30:51 EST 2020

% Result     : Theorem 2.21s
% Output     : CNFRefutation 2.34s
% Verified   : 
% Statistics : Number of formulae       :   71 (  91 expanded)
%              Number of leaves         :   37 (  50 expanded)
%              Depth                    :   14
%              Number of atoms          :  147 ( 245 expanded)
%              Number of equality atoms :    5 (   5 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_waybel_0 > r1_waybel_0 > r1_orders_2 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > l1_waybel_0 > v7_waybel_0 > v4_orders_2 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > k2_waybel_0 > o_2_2_yellow_6 > k6_subset_1 > k4_xboole_0 > #nlpp > u1_struct_0 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_125,negated_conjecture,(
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

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ ( r1_tarski(B,A)
          & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_91,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & l1_waybel_0(B,A) )
         => ! [C] :
              ( r1_waybel_0(A,B,C)
            <=> ~ r2_waybel_0(A,B,k6_subset_1(u1_struct_0(A),C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_waybel_0)).

tff(f_107,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A)
        & ~ v2_struct_0(B)
        & v4_orders_2(B)
        & v7_waybel_0(B)
        & l1_waybel_0(B,A) )
     => m1_subset_1(o_2_2_yellow_6(A,B),u1_struct_0(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_o_2_2_yellow_6)).

tff(f_31,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_waybel_0)).

tff(f_50,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_44,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_42,plain,(
    l1_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_34,plain,(
    l1_waybel_0('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_40,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_38,plain,(
    v4_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_36,plain,(
    v7_waybel_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_6,plain,(
    ! [A_3,B_4] : r1_tarski(k4_xboole_0(A_3,B_4),A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_10,plain,(
    ! [A_7,B_8] : r1_xboole_0(k4_xboole_0(A_7,B_8),B_8) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_61,plain,(
    ! [B_86,A_87] :
      ( ~ r1_xboole_0(B_86,A_87)
      | ~ r1_tarski(B_86,A_87)
      | v1_xboole_0(B_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_66,plain,(
    ! [A_88,B_89] :
      ( ~ r1_tarski(k4_xboole_0(A_88,B_89),B_89)
      | v1_xboole_0(k4_xboole_0(A_88,B_89)) ) ),
    inference(resolution,[status(thm)],[c_10,c_61])).

tff(c_73,plain,(
    ! [A_92] : v1_xboole_0(k4_xboole_0(A_92,A_92)) ),
    inference(resolution,[status(thm)],[c_6,c_66])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_77,plain,(
    ! [A_92] : k4_xboole_0(A_92,A_92) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_73,c_2])).

tff(c_12,plain,(
    ! [A_9,B_10] : k6_subset_1(A_9,B_10) = k4_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_28,plain,(
    ! [A_66,B_70,C_72] :
      ( r1_waybel_0(A_66,B_70,C_72)
      | r2_waybel_0(A_66,B_70,k6_subset_1(u1_struct_0(A_66),C_72))
      | ~ l1_waybel_0(B_70,A_66)
      | v2_struct_0(B_70)
      | ~ l1_struct_0(A_66)
      | v2_struct_0(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_112,plain,(
    ! [A_98,B_99,C_100] :
      ( r1_waybel_0(A_98,B_99,C_100)
      | r2_waybel_0(A_98,B_99,k4_xboole_0(u1_struct_0(A_98),C_100))
      | ~ l1_waybel_0(B_99,A_98)
      | v2_struct_0(B_99)
      | ~ l1_struct_0(A_98)
      | v2_struct_0(A_98) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_28])).

tff(c_117,plain,(
    ! [A_101,B_102] :
      ( r1_waybel_0(A_101,B_102,u1_struct_0(A_101))
      | r2_waybel_0(A_101,B_102,k1_xboole_0)
      | ~ l1_waybel_0(B_102,A_101)
      | v2_struct_0(B_102)
      | ~ l1_struct_0(A_101)
      | v2_struct_0(A_101) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_77,c_112])).

tff(c_32,plain,(
    ~ r1_waybel_0('#skF_3','#skF_4',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_120,plain,
    ( r2_waybel_0('#skF_3','#skF_4',k1_xboole_0)
    | ~ l1_waybel_0('#skF_4','#skF_3')
    | v2_struct_0('#skF_4')
    | ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_117,c_32])).

tff(c_123,plain,
    ( r2_waybel_0('#skF_3','#skF_4',k1_xboole_0)
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_34,c_120])).

tff(c_124,plain,(
    r2_waybel_0('#skF_3','#skF_4',k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_40,c_123])).

tff(c_30,plain,(
    ! [A_73,B_74] :
      ( m1_subset_1(o_2_2_yellow_6(A_73,B_74),u1_struct_0(B_74))
      | ~ l1_waybel_0(B_74,A_73)
      | ~ v7_waybel_0(B_74)
      | ~ v4_orders_2(B_74)
      | v2_struct_0(B_74)
      | ~ l1_struct_0(A_73)
      | v2_struct_0(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_4,plain,(
    ! [A_2] : r1_tarski(k1_xboole_0,A_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_141,plain,(
    ! [A_116,B_117,C_118,D_119] :
      ( r2_hidden(k2_waybel_0(A_116,B_117,'#skF_2'(A_116,B_117,C_118,D_119)),C_118)
      | ~ m1_subset_1(D_119,u1_struct_0(B_117))
      | ~ r2_waybel_0(A_116,B_117,C_118)
      | ~ l1_waybel_0(B_117,A_116)
      | v2_struct_0(B_117)
      | ~ l1_struct_0(A_116)
      | v2_struct_0(A_116) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_14,plain,(
    ! [B_12,A_11] :
      ( ~ r1_tarski(B_12,A_11)
      | ~ r2_hidden(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_146,plain,(
    ! [C_120,A_121,B_122,D_123] :
      ( ~ r1_tarski(C_120,k2_waybel_0(A_121,B_122,'#skF_2'(A_121,B_122,C_120,D_123)))
      | ~ m1_subset_1(D_123,u1_struct_0(B_122))
      | ~ r2_waybel_0(A_121,B_122,C_120)
      | ~ l1_waybel_0(B_122,A_121)
      | v2_struct_0(B_122)
      | ~ l1_struct_0(A_121)
      | v2_struct_0(A_121) ) ),
    inference(resolution,[status(thm)],[c_141,c_14])).

tff(c_152,plain,(
    ! [D_124,B_125,A_126] :
      ( ~ m1_subset_1(D_124,u1_struct_0(B_125))
      | ~ r2_waybel_0(A_126,B_125,k1_xboole_0)
      | ~ l1_waybel_0(B_125,A_126)
      | v2_struct_0(B_125)
      | ~ l1_struct_0(A_126)
      | v2_struct_0(A_126) ) ),
    inference(resolution,[status(thm)],[c_4,c_146])).

tff(c_195,plain,(
    ! [A_139,B_140,A_141] :
      ( ~ r2_waybel_0(A_139,B_140,k1_xboole_0)
      | ~ l1_waybel_0(B_140,A_139)
      | ~ l1_struct_0(A_139)
      | v2_struct_0(A_139)
      | ~ l1_waybel_0(B_140,A_141)
      | ~ v7_waybel_0(B_140)
      | ~ v4_orders_2(B_140)
      | v2_struct_0(B_140)
      | ~ l1_struct_0(A_141)
      | v2_struct_0(A_141) ) ),
    inference(resolution,[status(thm)],[c_30,c_152])).

tff(c_200,plain,(
    ! [A_141] :
      ( ~ l1_waybel_0('#skF_4','#skF_3')
      | ~ l1_struct_0('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ l1_waybel_0('#skF_4',A_141)
      | ~ v7_waybel_0('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ l1_struct_0(A_141)
      | v2_struct_0(A_141) ) ),
    inference(resolution,[status(thm)],[c_124,c_195])).

tff(c_207,plain,(
    ! [A_141] :
      ( v2_struct_0('#skF_3')
      | ~ l1_waybel_0('#skF_4',A_141)
      | v2_struct_0('#skF_4')
      | ~ l1_struct_0(A_141)
      | v2_struct_0(A_141) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_42,c_34,c_200])).

tff(c_209,plain,(
    ! [A_142] :
      ( ~ l1_waybel_0('#skF_4',A_142)
      | ~ l1_struct_0(A_142)
      | v2_struct_0(A_142) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_44,c_207])).

tff(c_212,plain,
    ( ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_209])).

tff(c_215,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_212])).

tff(c_217,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_215])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n017.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 09:38:16 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.21/1.26  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.21/1.26  
% 2.21/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.21/1.27  %$ r2_waybel_0 > r1_waybel_0 > r1_orders_2 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > l1_waybel_0 > v7_waybel_0 > v4_orders_2 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > k2_waybel_0 > o_2_2_yellow_6 > k6_subset_1 > k4_xboole_0 > #nlpp > u1_struct_0 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 2.21/1.27  
% 2.21/1.27  %Foreground sorts:
% 2.21/1.27  
% 2.21/1.27  
% 2.21/1.27  %Background operators:
% 2.21/1.27  
% 2.21/1.27  
% 2.21/1.27  %Foreground operators:
% 2.21/1.27  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.21/1.27  tff(o_2_2_yellow_6, type, o_2_2_yellow_6: ($i * $i) > $i).
% 2.21/1.27  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.21/1.27  tff(r2_waybel_0, type, r2_waybel_0: ($i * $i * $i) > $o).
% 2.21/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.21/1.27  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.21/1.27  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.21/1.27  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 2.21/1.27  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.21/1.27  tff(k2_waybel_0, type, k2_waybel_0: ($i * $i * $i) > $i).
% 2.21/1.27  tff(v7_waybel_0, type, v7_waybel_0: $i > $o).
% 2.21/1.27  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.21/1.27  tff(r1_waybel_0, type, r1_waybel_0: ($i * $i * $i) > $o).
% 2.21/1.27  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.21/1.27  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.21/1.27  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 2.21/1.27  tff('#skF_3', type, '#skF_3': $i).
% 2.21/1.27  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.21/1.27  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.21/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.21/1.27  tff(l1_waybel_0, type, l1_waybel_0: ($i * $i) > $o).
% 2.21/1.27  tff('#skF_4', type, '#skF_4': $i).
% 2.21/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.21/1.27  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.21/1.27  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.21/1.27  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.21/1.27  
% 2.34/1.28  tff(f_125, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => r1_waybel_0(A, B, u1_struct_0(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_yellow_6)).
% 2.34/1.28  tff(f_33, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 2.34/1.28  tff(f_43, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 2.34/1.28  tff(f_41, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_xboole_1)).
% 2.34/1.28  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.34/1.28  tff(f_45, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 2.34/1.28  tff(f_91, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((~v2_struct_0(B) & l1_waybel_0(B, A)) => (![C]: (r1_waybel_0(A, B, C) <=> ~r2_waybel_0(A, B, k6_subset_1(u1_struct_0(A), C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_waybel_0)).
% 2.34/1.28  tff(f_107, axiom, (![A, B]: ((((((~v2_struct_0(A) & l1_struct_0(A)) & ~v2_struct_0(B)) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => m1_subset_1(o_2_2_yellow_6(A, B), u1_struct_0(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_o_2_2_yellow_6)).
% 2.34/1.28  tff(f_31, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.34/1.28  tff(f_74, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((~v2_struct_0(B) & l1_waybel_0(B, A)) => (![C]: (r2_waybel_0(A, B, C) <=> (![D]: (m1_subset_1(D, u1_struct_0(B)) => (?[E]: ((m1_subset_1(E, u1_struct_0(B)) & r1_orders_2(B, D, E)) & r2_hidden(k2_waybel_0(A, B, E), C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d12_waybel_0)).
% 2.34/1.28  tff(f_50, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 2.34/1.28  tff(c_44, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_125])).
% 2.34/1.28  tff(c_42, plain, (l1_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_125])).
% 2.34/1.28  tff(c_34, plain, (l1_waybel_0('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_125])).
% 2.34/1.28  tff(c_40, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_125])).
% 2.34/1.28  tff(c_38, plain, (v4_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_125])).
% 2.34/1.28  tff(c_36, plain, (v7_waybel_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_125])).
% 2.34/1.28  tff(c_6, plain, (![A_3, B_4]: (r1_tarski(k4_xboole_0(A_3, B_4), A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.34/1.28  tff(c_10, plain, (![A_7, B_8]: (r1_xboole_0(k4_xboole_0(A_7, B_8), B_8))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.34/1.28  tff(c_61, plain, (![B_86, A_87]: (~r1_xboole_0(B_86, A_87) | ~r1_tarski(B_86, A_87) | v1_xboole_0(B_86))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.34/1.28  tff(c_66, plain, (![A_88, B_89]: (~r1_tarski(k4_xboole_0(A_88, B_89), B_89) | v1_xboole_0(k4_xboole_0(A_88, B_89)))), inference(resolution, [status(thm)], [c_10, c_61])).
% 2.34/1.28  tff(c_73, plain, (![A_92]: (v1_xboole_0(k4_xboole_0(A_92, A_92)))), inference(resolution, [status(thm)], [c_6, c_66])).
% 2.34/1.28  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.34/1.28  tff(c_77, plain, (![A_92]: (k4_xboole_0(A_92, A_92)=k1_xboole_0)), inference(resolution, [status(thm)], [c_73, c_2])).
% 2.34/1.28  tff(c_12, plain, (![A_9, B_10]: (k6_subset_1(A_9, B_10)=k4_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.34/1.28  tff(c_28, plain, (![A_66, B_70, C_72]: (r1_waybel_0(A_66, B_70, C_72) | r2_waybel_0(A_66, B_70, k6_subset_1(u1_struct_0(A_66), C_72)) | ~l1_waybel_0(B_70, A_66) | v2_struct_0(B_70) | ~l1_struct_0(A_66) | v2_struct_0(A_66))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.34/1.28  tff(c_112, plain, (![A_98, B_99, C_100]: (r1_waybel_0(A_98, B_99, C_100) | r2_waybel_0(A_98, B_99, k4_xboole_0(u1_struct_0(A_98), C_100)) | ~l1_waybel_0(B_99, A_98) | v2_struct_0(B_99) | ~l1_struct_0(A_98) | v2_struct_0(A_98))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_28])).
% 2.34/1.28  tff(c_117, plain, (![A_101, B_102]: (r1_waybel_0(A_101, B_102, u1_struct_0(A_101)) | r2_waybel_0(A_101, B_102, k1_xboole_0) | ~l1_waybel_0(B_102, A_101) | v2_struct_0(B_102) | ~l1_struct_0(A_101) | v2_struct_0(A_101))), inference(superposition, [status(thm), theory('equality')], [c_77, c_112])).
% 2.34/1.28  tff(c_32, plain, (~r1_waybel_0('#skF_3', '#skF_4', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_125])).
% 2.34/1.28  tff(c_120, plain, (r2_waybel_0('#skF_3', '#skF_4', k1_xboole_0) | ~l1_waybel_0('#skF_4', '#skF_3') | v2_struct_0('#skF_4') | ~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_117, c_32])).
% 2.34/1.28  tff(c_123, plain, (r2_waybel_0('#skF_3', '#skF_4', k1_xboole_0) | v2_struct_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_34, c_120])).
% 2.34/1.28  tff(c_124, plain, (r2_waybel_0('#skF_3', '#skF_4', k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_44, c_40, c_123])).
% 2.34/1.28  tff(c_30, plain, (![A_73, B_74]: (m1_subset_1(o_2_2_yellow_6(A_73, B_74), u1_struct_0(B_74)) | ~l1_waybel_0(B_74, A_73) | ~v7_waybel_0(B_74) | ~v4_orders_2(B_74) | v2_struct_0(B_74) | ~l1_struct_0(A_73) | v2_struct_0(A_73))), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.34/1.28  tff(c_4, plain, (![A_2]: (r1_tarski(k1_xboole_0, A_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.34/1.28  tff(c_141, plain, (![A_116, B_117, C_118, D_119]: (r2_hidden(k2_waybel_0(A_116, B_117, '#skF_2'(A_116, B_117, C_118, D_119)), C_118) | ~m1_subset_1(D_119, u1_struct_0(B_117)) | ~r2_waybel_0(A_116, B_117, C_118) | ~l1_waybel_0(B_117, A_116) | v2_struct_0(B_117) | ~l1_struct_0(A_116) | v2_struct_0(A_116))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.34/1.28  tff(c_14, plain, (![B_12, A_11]: (~r1_tarski(B_12, A_11) | ~r2_hidden(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.34/1.28  tff(c_146, plain, (![C_120, A_121, B_122, D_123]: (~r1_tarski(C_120, k2_waybel_0(A_121, B_122, '#skF_2'(A_121, B_122, C_120, D_123))) | ~m1_subset_1(D_123, u1_struct_0(B_122)) | ~r2_waybel_0(A_121, B_122, C_120) | ~l1_waybel_0(B_122, A_121) | v2_struct_0(B_122) | ~l1_struct_0(A_121) | v2_struct_0(A_121))), inference(resolution, [status(thm)], [c_141, c_14])).
% 2.34/1.28  tff(c_152, plain, (![D_124, B_125, A_126]: (~m1_subset_1(D_124, u1_struct_0(B_125)) | ~r2_waybel_0(A_126, B_125, k1_xboole_0) | ~l1_waybel_0(B_125, A_126) | v2_struct_0(B_125) | ~l1_struct_0(A_126) | v2_struct_0(A_126))), inference(resolution, [status(thm)], [c_4, c_146])).
% 2.34/1.28  tff(c_195, plain, (![A_139, B_140, A_141]: (~r2_waybel_0(A_139, B_140, k1_xboole_0) | ~l1_waybel_0(B_140, A_139) | ~l1_struct_0(A_139) | v2_struct_0(A_139) | ~l1_waybel_0(B_140, A_141) | ~v7_waybel_0(B_140) | ~v4_orders_2(B_140) | v2_struct_0(B_140) | ~l1_struct_0(A_141) | v2_struct_0(A_141))), inference(resolution, [status(thm)], [c_30, c_152])).
% 2.34/1.28  tff(c_200, plain, (![A_141]: (~l1_waybel_0('#skF_4', '#skF_3') | ~l1_struct_0('#skF_3') | v2_struct_0('#skF_3') | ~l1_waybel_0('#skF_4', A_141) | ~v7_waybel_0('#skF_4') | ~v4_orders_2('#skF_4') | v2_struct_0('#skF_4') | ~l1_struct_0(A_141) | v2_struct_0(A_141))), inference(resolution, [status(thm)], [c_124, c_195])).
% 2.34/1.28  tff(c_207, plain, (![A_141]: (v2_struct_0('#skF_3') | ~l1_waybel_0('#skF_4', A_141) | v2_struct_0('#skF_4') | ~l1_struct_0(A_141) | v2_struct_0(A_141))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_42, c_34, c_200])).
% 2.34/1.28  tff(c_209, plain, (![A_142]: (~l1_waybel_0('#skF_4', A_142) | ~l1_struct_0(A_142) | v2_struct_0(A_142))), inference(negUnitSimplification, [status(thm)], [c_40, c_44, c_207])).
% 2.34/1.28  tff(c_212, plain, (~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_34, c_209])).
% 2.34/1.28  tff(c_215, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_212])).
% 2.34/1.28  tff(c_217, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_215])).
% 2.34/1.28  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.34/1.28  
% 2.34/1.28  Inference rules
% 2.34/1.28  ----------------------
% 2.34/1.28  #Ref     : 0
% 2.34/1.28  #Sup     : 30
% 2.34/1.28  #Fact    : 0
% 2.34/1.28  #Define  : 0
% 2.34/1.28  #Split   : 0
% 2.34/1.28  #Chain   : 0
% 2.34/1.28  #Close   : 0
% 2.34/1.28  
% 2.34/1.28  Ordering : KBO
% 2.34/1.28  
% 2.34/1.28  Simplification rules
% 2.34/1.28  ----------------------
% 2.34/1.28  #Subsume      : 5
% 2.34/1.28  #Demod        : 20
% 2.34/1.28  #Tautology    : 10
% 2.34/1.28  #SimpNegUnit  : 8
% 2.34/1.28  #BackRed      : 1
% 2.34/1.28  
% 2.34/1.28  #Partial instantiations: 0
% 2.34/1.28  #Strategies tried      : 1
% 2.34/1.28  
% 2.34/1.28  Timing (in seconds)
% 2.34/1.28  ----------------------
% 2.34/1.28  Preprocessing        : 0.32
% 2.34/1.28  Parsing              : 0.17
% 2.34/1.28  CNF conversion       : 0.03
% 2.34/1.28  Main loop            : 0.20
% 2.34/1.28  Inferencing          : 0.08
% 2.34/1.29  Reduction            : 0.06
% 2.34/1.29  Demodulation         : 0.04
% 2.34/1.29  BG Simplification    : 0.01
% 2.34/1.29  Subsumption          : 0.03
% 2.34/1.29  Abstraction          : 0.01
% 2.34/1.29  MUC search           : 0.00
% 2.34/1.29  Cooper               : 0.00
% 2.34/1.29  Total                : 0.55
% 2.34/1.29  Index Insertion      : 0.00
% 2.34/1.29  Index Deletion       : 0.00
% 2.34/1.29  Index Matching       : 0.00
% 2.34/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
