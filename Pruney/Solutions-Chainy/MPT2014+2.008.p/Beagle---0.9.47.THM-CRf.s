%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:09 EST 2020

% Result     : Theorem 3.45s
% Output     : CNFRefutation 3.45s
% Verified   : 
% Statistics : Number of formulae       :   67 (  96 expanded)
%              Number of leaves         :   28 (  47 expanded)
%              Depth                    :   13
%              Number of atoms          :  164 ( 278 expanded)
%              Number of equality atoms :    7 (   8 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_orders_2 > r2_hidden > r1_tarski > m1_subset_1 > l1_waybel_0 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > k4_waybel_9 > a_3_0_waybel_9 > #nlpp > u1_struct_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff(k4_waybel_9,type,(
    k4_waybel_9: ( $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(a_3_0_waybel_9,type,(
    a_3_0_waybel_9: ( $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

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
              & l1_waybel_0(B,A) )
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(B))
               => r1_tarski(u1_struct_0(k4_waybel_9(A,B,C)),u1_struct_0(B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_waybel_9)).

tff(f_57,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ! [B] :
          ( l1_waybel_0(B,A)
         => l1_orders_2(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_waybel_0)).

tff(f_50,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_78,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v2_struct_0(B)
        & l1_struct_0(B)
        & ~ v2_struct_0(C)
        & l1_waybel_0(C,B)
        & m1_subset_1(D,u1_struct_0(C)) )
     => ( r2_hidden(A,a_3_0_waybel_9(B,C,D))
      <=> ? [E] :
            ( m1_subset_1(E,u1_struct_0(C))
            & A = E
            & r1_orders_2(C,D,E) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fraenkel_a_3_0_waybel_9)).

tff(f_38,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_94,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & l1_waybel_0(B,A) )
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(B))
             => u1_struct_0(k4_waybel_9(A,B,C)) = a_3_0_waybel_9(A,B,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_waybel_9)).

tff(f_46,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(c_34,plain,(
    l1_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_30,plain,(
    l1_waybel_0('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_39,plain,(
    ! [B_33,A_34] :
      ( l1_orders_2(B_33)
      | ~ l1_waybel_0(B_33,A_34)
      | ~ l1_struct_0(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_42,plain,
    ( l1_orders_2('#skF_4')
    | ~ l1_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_39])).

tff(c_45,plain,(
    l1_orders_2('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_42])).

tff(c_12,plain,(
    ! [A_9] :
      ( l1_struct_0(A_9)
      | ~ l1_orders_2(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_32,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_36,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_28,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_47,plain,(
    ! [A_37,B_38] :
      ( r2_hidden('#skF_1'(A_37,B_38),A_37)
      | r1_tarski(A_37,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_52,plain,(
    ! [A_37] : r1_tarski(A_37,A_37) ),
    inference(resolution,[status(thm)],[c_47,c_4])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_60,plain,(
    ! [C_42,B_43,A_44] :
      ( r2_hidden(C_42,B_43)
      | ~ r2_hidden(C_42,A_44)
      | ~ r1_tarski(A_44,B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_66,plain,(
    ! [A_1,B_2,B_43] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_43)
      | ~ r1_tarski(A_1,B_43)
      | r1_tarski(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_60])).

tff(c_112,plain,(
    ! [A_62,B_63,C_64,D_65] :
      ( '#skF_2'(A_62,B_63,C_64,D_65) = A_62
      | ~ r2_hidden(A_62,a_3_0_waybel_9(B_63,C_64,D_65))
      | ~ m1_subset_1(D_65,u1_struct_0(C_64))
      | ~ l1_waybel_0(C_64,B_63)
      | v2_struct_0(C_64)
      | ~ l1_struct_0(B_63)
      | v2_struct_0(B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_194,plain,(
    ! [B_101,C_102,D_103,B_104] :
      ( '#skF_2'('#skF_1'(a_3_0_waybel_9(B_101,C_102,D_103),B_104),B_101,C_102,D_103) = '#skF_1'(a_3_0_waybel_9(B_101,C_102,D_103),B_104)
      | ~ m1_subset_1(D_103,u1_struct_0(C_102))
      | ~ l1_waybel_0(C_102,B_101)
      | v2_struct_0(C_102)
      | ~ l1_struct_0(B_101)
      | v2_struct_0(B_101)
      | r1_tarski(a_3_0_waybel_9(B_101,C_102,D_103),B_104) ) ),
    inference(resolution,[status(thm)],[c_6,c_112])).

tff(c_22,plain,(
    ! [A_13,B_14,C_15,D_16] :
      ( m1_subset_1('#skF_2'(A_13,B_14,C_15,D_16),u1_struct_0(C_15))
      | ~ r2_hidden(A_13,a_3_0_waybel_9(B_14,C_15,D_16))
      | ~ m1_subset_1(D_16,u1_struct_0(C_15))
      | ~ l1_waybel_0(C_15,B_14)
      | v2_struct_0(C_15)
      | ~ l1_struct_0(B_14)
      | v2_struct_0(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_566,plain,(
    ! [B_177,C_178,D_179,B_180] :
      ( m1_subset_1('#skF_1'(a_3_0_waybel_9(B_177,C_178,D_179),B_180),u1_struct_0(C_178))
      | ~ r2_hidden('#skF_1'(a_3_0_waybel_9(B_177,C_178,D_179),B_180),a_3_0_waybel_9(B_177,C_178,D_179))
      | ~ m1_subset_1(D_179,u1_struct_0(C_178))
      | ~ l1_waybel_0(C_178,B_177)
      | v2_struct_0(C_178)
      | ~ l1_struct_0(B_177)
      | v2_struct_0(B_177)
      | ~ m1_subset_1(D_179,u1_struct_0(C_178))
      | ~ l1_waybel_0(C_178,B_177)
      | v2_struct_0(C_178)
      | ~ l1_struct_0(B_177)
      | v2_struct_0(B_177)
      | r1_tarski(a_3_0_waybel_9(B_177,C_178,D_179),B_180) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_194,c_22])).

tff(c_574,plain,(
    ! [B_177,C_178,D_179,B_2] :
      ( m1_subset_1('#skF_1'(a_3_0_waybel_9(B_177,C_178,D_179),B_2),u1_struct_0(C_178))
      | ~ m1_subset_1(D_179,u1_struct_0(C_178))
      | ~ l1_waybel_0(C_178,B_177)
      | v2_struct_0(C_178)
      | ~ l1_struct_0(B_177)
      | v2_struct_0(B_177)
      | ~ r1_tarski(a_3_0_waybel_9(B_177,C_178,D_179),a_3_0_waybel_9(B_177,C_178,D_179))
      | r1_tarski(a_3_0_waybel_9(B_177,C_178,D_179),B_2) ) ),
    inference(resolution,[status(thm)],[c_66,c_566])).

tff(c_588,plain,(
    ! [B_181,C_182,D_183,B_184] :
      ( m1_subset_1('#skF_1'(a_3_0_waybel_9(B_181,C_182,D_183),B_184),u1_struct_0(C_182))
      | ~ m1_subset_1(D_183,u1_struct_0(C_182))
      | ~ l1_waybel_0(C_182,B_181)
      | v2_struct_0(C_182)
      | ~ l1_struct_0(B_181)
      | v2_struct_0(B_181)
      | r1_tarski(a_3_0_waybel_9(B_181,C_182,D_183),B_184) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_574])).

tff(c_54,plain,(
    ! [A_40,B_41] :
      ( r2_hidden(A_40,B_41)
      | v1_xboole_0(B_41)
      | ~ m1_subset_1(A_40,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_59,plain,(
    ! [A_1,B_41] :
      ( r1_tarski(A_1,B_41)
      | v1_xboole_0(B_41)
      | ~ m1_subset_1('#skF_1'(A_1,B_41),B_41) ) ),
    inference(resolution,[status(thm)],[c_54,c_4])).

tff(c_626,plain,(
    ! [C_185,D_186,B_187] :
      ( v1_xboole_0(u1_struct_0(C_185))
      | ~ m1_subset_1(D_186,u1_struct_0(C_185))
      | ~ l1_waybel_0(C_185,B_187)
      | v2_struct_0(C_185)
      | ~ l1_struct_0(B_187)
      | v2_struct_0(B_187)
      | r1_tarski(a_3_0_waybel_9(B_187,C_185,D_186),u1_struct_0(C_185)) ) ),
    inference(resolution,[status(thm)],[c_588,c_59])).

tff(c_67,plain,(
    ! [A_45,B_46,C_47] :
      ( u1_struct_0(k4_waybel_9(A_45,B_46,C_47)) = a_3_0_waybel_9(A_45,B_46,C_47)
      | ~ m1_subset_1(C_47,u1_struct_0(B_46))
      | ~ l1_waybel_0(B_46,A_45)
      | v2_struct_0(B_46)
      | ~ l1_struct_0(A_45)
      | v2_struct_0(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_69,plain,(
    ! [A_45] :
      ( u1_struct_0(k4_waybel_9(A_45,'#skF_4','#skF_5')) = a_3_0_waybel_9(A_45,'#skF_4','#skF_5')
      | ~ l1_waybel_0('#skF_4',A_45)
      | v2_struct_0('#skF_4')
      | ~ l1_struct_0(A_45)
      | v2_struct_0(A_45) ) ),
    inference(resolution,[status(thm)],[c_28,c_67])).

tff(c_87,plain,(
    ! [A_56] :
      ( u1_struct_0(k4_waybel_9(A_56,'#skF_4','#skF_5')) = a_3_0_waybel_9(A_56,'#skF_4','#skF_5')
      | ~ l1_waybel_0('#skF_4',A_56)
      | ~ l1_struct_0(A_56)
      | v2_struct_0(A_56) ) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_69])).

tff(c_26,plain,(
    ~ r1_tarski(u1_struct_0(k4_waybel_9('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_95,plain,
    ( ~ r1_tarski(a_3_0_waybel_9('#skF_3','#skF_4','#skF_5'),u1_struct_0('#skF_4'))
    | ~ l1_waybel_0('#skF_4','#skF_3')
    | ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_87,c_26])).

tff(c_104,plain,
    ( ~ r1_tarski(a_3_0_waybel_9('#skF_3','#skF_4','#skF_5'),u1_struct_0('#skF_4'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30,c_95])).

tff(c_105,plain,(
    ~ r1_tarski(a_3_0_waybel_9('#skF_3','#skF_4','#skF_5'),u1_struct_0('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_104])).

tff(c_633,plain,
    ( v1_xboole_0(u1_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ l1_waybel_0('#skF_4','#skF_3')
    | v2_struct_0('#skF_4')
    | ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_626,c_105])).

tff(c_649,plain,
    ( v1_xboole_0(u1_struct_0('#skF_4'))
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30,c_28,c_633])).

tff(c_650,plain,(
    v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_32,c_649])).

tff(c_10,plain,(
    ! [A_8] :
      ( ~ v1_xboole_0(u1_struct_0(A_8))
      | ~ l1_struct_0(A_8)
      | v2_struct_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_654,plain,
    ( ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_650,c_10])).

tff(c_657,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_654])).

tff(c_660,plain,(
    ~ l1_orders_2('#skF_4') ),
    inference(resolution,[status(thm)],[c_12,c_657])).

tff(c_664,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_45,c_660])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:08:32 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.45/1.57  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.45/1.58  
% 3.45/1.58  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.45/1.58  %$ r1_orders_2 > r2_hidden > r1_tarski > m1_subset_1 > l1_waybel_0 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > k4_waybel_9 > a_3_0_waybel_9 > #nlpp > u1_struct_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 3.45/1.58  
% 3.45/1.58  %Foreground sorts:
% 3.45/1.58  
% 3.45/1.58  
% 3.45/1.58  %Background operators:
% 3.45/1.58  
% 3.45/1.58  
% 3.45/1.58  %Foreground operators:
% 3.45/1.58  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.45/1.58  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.45/1.58  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.45/1.58  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 3.45/1.58  tff(k4_waybel_9, type, k4_waybel_9: ($i * $i * $i) > $i).
% 3.45/1.58  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.45/1.58  tff('#skF_5', type, '#skF_5': $i).
% 3.45/1.58  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 3.45/1.58  tff('#skF_3', type, '#skF_3': $i).
% 3.45/1.58  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.45/1.58  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 3.45/1.58  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.45/1.58  tff(l1_waybel_0, type, l1_waybel_0: ($i * $i) > $o).
% 3.45/1.58  tff('#skF_4', type, '#skF_4': $i).
% 3.45/1.58  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.45/1.58  tff(a_3_0_waybel_9, type, a_3_0_waybel_9: ($i * $i * $i) > $i).
% 3.45/1.58  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.45/1.58  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.45/1.58  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.45/1.58  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.45/1.58  
% 3.45/1.59  tff(f_111, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((~v2_struct_0(B) & l1_waybel_0(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(B)) => r1_tarski(u1_struct_0(k4_waybel_9(A, B, C)), u1_struct_0(B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_waybel_9)).
% 3.45/1.59  tff(f_57, axiom, (![A]: (l1_struct_0(A) => (![B]: (l1_waybel_0(B, A) => l1_orders_2(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_waybel_0)).
% 3.45/1.59  tff(f_50, axiom, (![A]: (l1_orders_2(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 3.45/1.59  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.45/1.59  tff(f_78, axiom, (![A, B, C, D]: (((((~v2_struct_0(B) & l1_struct_0(B)) & ~v2_struct_0(C)) & l1_waybel_0(C, B)) & m1_subset_1(D, u1_struct_0(C))) => (r2_hidden(A, a_3_0_waybel_9(B, C, D)) <=> (?[E]: ((m1_subset_1(E, u1_struct_0(C)) & (A = E)) & r1_orders_2(C, D, E)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fraenkel_a_3_0_waybel_9)).
% 3.45/1.59  tff(f_38, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 3.45/1.59  tff(f_94, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((~v2_struct_0(B) & l1_waybel_0(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(B)) => (u1_struct_0(k4_waybel_9(A, B, C)) = a_3_0_waybel_9(A, B, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_waybel_9)).
% 3.45/1.59  tff(f_46, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 3.45/1.59  tff(c_34, plain, (l1_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.45/1.59  tff(c_30, plain, (l1_waybel_0('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.45/1.59  tff(c_39, plain, (![B_33, A_34]: (l1_orders_2(B_33) | ~l1_waybel_0(B_33, A_34) | ~l1_struct_0(A_34))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.45/1.59  tff(c_42, plain, (l1_orders_2('#skF_4') | ~l1_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_30, c_39])).
% 3.45/1.59  tff(c_45, plain, (l1_orders_2('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_42])).
% 3.45/1.59  tff(c_12, plain, (![A_9]: (l1_struct_0(A_9) | ~l1_orders_2(A_9))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.45/1.59  tff(c_32, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.45/1.59  tff(c_36, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.45/1.59  tff(c_28, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.45/1.59  tff(c_47, plain, (![A_37, B_38]: (r2_hidden('#skF_1'(A_37, B_38), A_37) | r1_tarski(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.45/1.59  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.45/1.59  tff(c_52, plain, (![A_37]: (r1_tarski(A_37, A_37))), inference(resolution, [status(thm)], [c_47, c_4])).
% 3.45/1.59  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.45/1.59  tff(c_60, plain, (![C_42, B_43, A_44]: (r2_hidden(C_42, B_43) | ~r2_hidden(C_42, A_44) | ~r1_tarski(A_44, B_43))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.45/1.59  tff(c_66, plain, (![A_1, B_2, B_43]: (r2_hidden('#skF_1'(A_1, B_2), B_43) | ~r1_tarski(A_1, B_43) | r1_tarski(A_1, B_2))), inference(resolution, [status(thm)], [c_6, c_60])).
% 3.45/1.59  tff(c_112, plain, (![A_62, B_63, C_64, D_65]: ('#skF_2'(A_62, B_63, C_64, D_65)=A_62 | ~r2_hidden(A_62, a_3_0_waybel_9(B_63, C_64, D_65)) | ~m1_subset_1(D_65, u1_struct_0(C_64)) | ~l1_waybel_0(C_64, B_63) | v2_struct_0(C_64) | ~l1_struct_0(B_63) | v2_struct_0(B_63))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.45/1.59  tff(c_194, plain, (![B_101, C_102, D_103, B_104]: ('#skF_2'('#skF_1'(a_3_0_waybel_9(B_101, C_102, D_103), B_104), B_101, C_102, D_103)='#skF_1'(a_3_0_waybel_9(B_101, C_102, D_103), B_104) | ~m1_subset_1(D_103, u1_struct_0(C_102)) | ~l1_waybel_0(C_102, B_101) | v2_struct_0(C_102) | ~l1_struct_0(B_101) | v2_struct_0(B_101) | r1_tarski(a_3_0_waybel_9(B_101, C_102, D_103), B_104))), inference(resolution, [status(thm)], [c_6, c_112])).
% 3.45/1.59  tff(c_22, plain, (![A_13, B_14, C_15, D_16]: (m1_subset_1('#skF_2'(A_13, B_14, C_15, D_16), u1_struct_0(C_15)) | ~r2_hidden(A_13, a_3_0_waybel_9(B_14, C_15, D_16)) | ~m1_subset_1(D_16, u1_struct_0(C_15)) | ~l1_waybel_0(C_15, B_14) | v2_struct_0(C_15) | ~l1_struct_0(B_14) | v2_struct_0(B_14))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.45/1.59  tff(c_566, plain, (![B_177, C_178, D_179, B_180]: (m1_subset_1('#skF_1'(a_3_0_waybel_9(B_177, C_178, D_179), B_180), u1_struct_0(C_178)) | ~r2_hidden('#skF_1'(a_3_0_waybel_9(B_177, C_178, D_179), B_180), a_3_0_waybel_9(B_177, C_178, D_179)) | ~m1_subset_1(D_179, u1_struct_0(C_178)) | ~l1_waybel_0(C_178, B_177) | v2_struct_0(C_178) | ~l1_struct_0(B_177) | v2_struct_0(B_177) | ~m1_subset_1(D_179, u1_struct_0(C_178)) | ~l1_waybel_0(C_178, B_177) | v2_struct_0(C_178) | ~l1_struct_0(B_177) | v2_struct_0(B_177) | r1_tarski(a_3_0_waybel_9(B_177, C_178, D_179), B_180))), inference(superposition, [status(thm), theory('equality')], [c_194, c_22])).
% 3.45/1.59  tff(c_574, plain, (![B_177, C_178, D_179, B_2]: (m1_subset_1('#skF_1'(a_3_0_waybel_9(B_177, C_178, D_179), B_2), u1_struct_0(C_178)) | ~m1_subset_1(D_179, u1_struct_0(C_178)) | ~l1_waybel_0(C_178, B_177) | v2_struct_0(C_178) | ~l1_struct_0(B_177) | v2_struct_0(B_177) | ~r1_tarski(a_3_0_waybel_9(B_177, C_178, D_179), a_3_0_waybel_9(B_177, C_178, D_179)) | r1_tarski(a_3_0_waybel_9(B_177, C_178, D_179), B_2))), inference(resolution, [status(thm)], [c_66, c_566])).
% 3.45/1.59  tff(c_588, plain, (![B_181, C_182, D_183, B_184]: (m1_subset_1('#skF_1'(a_3_0_waybel_9(B_181, C_182, D_183), B_184), u1_struct_0(C_182)) | ~m1_subset_1(D_183, u1_struct_0(C_182)) | ~l1_waybel_0(C_182, B_181) | v2_struct_0(C_182) | ~l1_struct_0(B_181) | v2_struct_0(B_181) | r1_tarski(a_3_0_waybel_9(B_181, C_182, D_183), B_184))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_574])).
% 3.45/1.59  tff(c_54, plain, (![A_40, B_41]: (r2_hidden(A_40, B_41) | v1_xboole_0(B_41) | ~m1_subset_1(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.45/1.59  tff(c_59, plain, (![A_1, B_41]: (r1_tarski(A_1, B_41) | v1_xboole_0(B_41) | ~m1_subset_1('#skF_1'(A_1, B_41), B_41))), inference(resolution, [status(thm)], [c_54, c_4])).
% 3.45/1.59  tff(c_626, plain, (![C_185, D_186, B_187]: (v1_xboole_0(u1_struct_0(C_185)) | ~m1_subset_1(D_186, u1_struct_0(C_185)) | ~l1_waybel_0(C_185, B_187) | v2_struct_0(C_185) | ~l1_struct_0(B_187) | v2_struct_0(B_187) | r1_tarski(a_3_0_waybel_9(B_187, C_185, D_186), u1_struct_0(C_185)))), inference(resolution, [status(thm)], [c_588, c_59])).
% 3.45/1.59  tff(c_67, plain, (![A_45, B_46, C_47]: (u1_struct_0(k4_waybel_9(A_45, B_46, C_47))=a_3_0_waybel_9(A_45, B_46, C_47) | ~m1_subset_1(C_47, u1_struct_0(B_46)) | ~l1_waybel_0(B_46, A_45) | v2_struct_0(B_46) | ~l1_struct_0(A_45) | v2_struct_0(A_45))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.45/1.59  tff(c_69, plain, (![A_45]: (u1_struct_0(k4_waybel_9(A_45, '#skF_4', '#skF_5'))=a_3_0_waybel_9(A_45, '#skF_4', '#skF_5') | ~l1_waybel_0('#skF_4', A_45) | v2_struct_0('#skF_4') | ~l1_struct_0(A_45) | v2_struct_0(A_45))), inference(resolution, [status(thm)], [c_28, c_67])).
% 3.45/1.59  tff(c_87, plain, (![A_56]: (u1_struct_0(k4_waybel_9(A_56, '#skF_4', '#skF_5'))=a_3_0_waybel_9(A_56, '#skF_4', '#skF_5') | ~l1_waybel_0('#skF_4', A_56) | ~l1_struct_0(A_56) | v2_struct_0(A_56))), inference(negUnitSimplification, [status(thm)], [c_32, c_69])).
% 3.45/1.59  tff(c_26, plain, (~r1_tarski(u1_struct_0(k4_waybel_9('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.45/1.59  tff(c_95, plain, (~r1_tarski(a_3_0_waybel_9('#skF_3', '#skF_4', '#skF_5'), u1_struct_0('#skF_4')) | ~l1_waybel_0('#skF_4', '#skF_3') | ~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_87, c_26])).
% 3.45/1.59  tff(c_104, plain, (~r1_tarski(a_3_0_waybel_9('#skF_3', '#skF_4', '#skF_5'), u1_struct_0('#skF_4')) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_30, c_95])).
% 3.45/1.59  tff(c_105, plain, (~r1_tarski(a_3_0_waybel_9('#skF_3', '#skF_4', '#skF_5'), u1_struct_0('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_36, c_104])).
% 3.45/1.59  tff(c_633, plain, (v1_xboole_0(u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~l1_waybel_0('#skF_4', '#skF_3') | v2_struct_0('#skF_4') | ~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_626, c_105])).
% 3.45/1.59  tff(c_649, plain, (v1_xboole_0(u1_struct_0('#skF_4')) | v2_struct_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_30, c_28, c_633])).
% 3.45/1.59  tff(c_650, plain, (v1_xboole_0(u1_struct_0('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_36, c_32, c_649])).
% 3.45/1.59  tff(c_10, plain, (![A_8]: (~v1_xboole_0(u1_struct_0(A_8)) | ~l1_struct_0(A_8) | v2_struct_0(A_8))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.45/1.59  tff(c_654, plain, (~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_650, c_10])).
% 3.45/1.59  tff(c_657, plain, (~l1_struct_0('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_32, c_654])).
% 3.45/1.59  tff(c_660, plain, (~l1_orders_2('#skF_4')), inference(resolution, [status(thm)], [c_12, c_657])).
% 3.45/1.59  tff(c_664, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_45, c_660])).
% 3.45/1.59  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.45/1.59  
% 3.45/1.59  Inference rules
% 3.45/1.59  ----------------------
% 3.45/1.59  #Ref     : 0
% 3.45/1.59  #Sup     : 156
% 3.45/1.59  #Fact    : 0
% 3.45/1.59  #Define  : 0
% 3.45/1.59  #Split   : 1
% 3.45/1.59  #Chain   : 0
% 3.45/1.59  #Close   : 0
% 3.45/1.59  
% 3.45/1.59  Ordering : KBO
% 3.45/1.59  
% 3.45/1.59  Simplification rules
% 3.45/1.59  ----------------------
% 3.45/1.59  #Subsume      : 15
% 3.45/1.59  #Demod        : 13
% 3.45/1.59  #Tautology    : 19
% 3.45/1.59  #SimpNegUnit  : 22
% 3.45/1.59  #BackRed      : 0
% 3.45/1.59  
% 3.45/1.59  #Partial instantiations: 0
% 3.45/1.59  #Strategies tried      : 1
% 3.45/1.59  
% 3.45/1.59  Timing (in seconds)
% 3.45/1.59  ----------------------
% 3.45/1.60  Preprocessing        : 0.30
% 3.45/1.60  Parsing              : 0.17
% 3.45/1.60  CNF conversion       : 0.02
% 3.45/1.60  Main loop            : 0.52
% 3.45/1.60  Inferencing          : 0.21
% 3.45/1.60  Reduction            : 0.12
% 3.45/1.60  Demodulation         : 0.08
% 3.45/1.60  BG Simplification    : 0.03
% 3.45/1.60  Subsumption          : 0.13
% 3.45/1.60  Abstraction          : 0.04
% 3.45/1.60  MUC search           : 0.00
% 3.45/1.60  Cooper               : 0.00
% 3.45/1.60  Total                : 0.86
% 3.45/1.60  Index Insertion      : 0.00
% 3.45/1.60  Index Deletion       : 0.00
% 3.45/1.60  Index Matching       : 0.00
% 3.45/1.60  BG Taut test         : 0.00
%------------------------------------------------------------------------------
