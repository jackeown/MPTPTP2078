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
% DateTime   : Thu Dec  3 10:31:09 EST 2020

% Result     : Theorem 8.44s
% Output     : CNFRefutation 8.44s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 114 expanded)
%              Number of leaves         :   36 (  57 expanded)
%              Depth                    :   14
%              Number of atoms          :  218 ( 352 expanded)
%              Number of equality atoms :    5 (   8 expanded)
%              Maximal formula depth    :   21 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > r1_orders_2 > v6_waybel_0 > r2_hidden > r1_tarski > m1_subset_1 > l1_waybel_0 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > k2_partfun1 > k4_waybel_9 > u1_waybel_0 > k1_toler_1 > #nlpp > u1_struct_0 > u1_orders_2 > #skF_2 > #skF_7 > #skF_6 > #skF_4 > #skF_8 > #skF_5 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(v6_waybel_0,type,(
    v6_waybel_0: ( $i * $i ) > $o )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff(k4_waybel_9,type,(
    k4_waybel_9: ( $i * $i * $i ) > $i )).

tff(k1_toler_1,type,(
    k1_toler_1: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff(u1_waybel_0,type,(
    u1_waybel_0: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(l1_waybel_0,type,(
    l1_waybel_0: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_partfun1,type,(
    k2_partfun1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(u1_orders_2,type,(
    u1_orders_2: $i > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_130,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & l1_struct_0(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & l1_waybel_0(B,A) )
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(B))
               => r1_tarski(u1_struct_0(k4_waybel_9(A,B,C)),u1_struct_0(B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_waybel_9)).

tff(f_56,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ! [B] :
          ( l1_waybel_0(B,A)
         => l1_orders_2(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_waybel_0)).

tff(f_49,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_45,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_113,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A)
        & ~ v2_struct_0(B)
        & l1_waybel_0(B,A)
        & m1_subset_1(C,u1_struct_0(B)) )
     => ( v6_waybel_0(k4_waybel_9(A,B,C),A)
        & l1_waybel_0(k4_waybel_9(A,B,C),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_waybel_9)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_97,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & l1_waybel_0(B,A) )
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(B))
             => ! [D] :
                  ( ( v6_waybel_0(D,A)
                    & l1_waybel_0(D,A) )
                 => ( D = k4_waybel_9(A,B,C)
                  <=> ( ! [E] :
                          ( r2_hidden(E,u1_struct_0(D))
                        <=> ? [F] :
                              ( m1_subset_1(F,u1_struct_0(B))
                              & F = E
                              & r1_orders_2(B,C,F) ) )
                      & r2_relset_1(u1_struct_0(D),u1_struct_0(D),u1_orders_2(D),k1_toler_1(u1_orders_2(B),u1_struct_0(D)))
                      & u1_waybel_0(A,D) = k2_partfun1(u1_struct_0(B),u1_struct_0(A),u1_waybel_0(A,B),u1_struct_0(D)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_waybel_9)).

tff(f_62,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ( v2_struct_0(A)
      <=> v1_xboole_0(u1_struct_0(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_struct_0)).

tff(c_64,plain,(
    l1_struct_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_60,plain,(
    l1_waybel_0('#skF_7','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_4779,plain,(
    ! [B_847,A_848] :
      ( l1_orders_2(B_847)
      | ~ l1_waybel_0(B_847,A_848)
      | ~ l1_struct_0(A_848) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_4782,plain,
    ( l1_orders_2('#skF_7')
    | ~ l1_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_60,c_4779])).

tff(c_4785,plain,(
    l1_orders_2('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_4782])).

tff(c_16,plain,(
    ! [A_8] :
      ( l1_struct_0(A_8)
      | ~ l1_orders_2(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_62,plain,(
    ~ v2_struct_0('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_66,plain,(
    ~ v2_struct_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_58,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_70,plain,(
    ! [B_196,A_197] :
      ( v1_xboole_0(B_196)
      | ~ m1_subset_1(B_196,A_197)
      | ~ v1_xboole_0(A_197) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_78,plain,
    ( v1_xboole_0('#skF_8')
    | ~ v1_xboole_0(u1_struct_0('#skF_7')) ),
    inference(resolution,[status(thm)],[c_58,c_70])).

tff(c_79,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_78])).

tff(c_160,plain,(
    ! [A_223,B_224,C_225] :
      ( l1_waybel_0(k4_waybel_9(A_223,B_224,C_225),A_223)
      | ~ m1_subset_1(C_225,u1_struct_0(B_224))
      | ~ l1_waybel_0(B_224,A_223)
      | v2_struct_0(B_224)
      | ~ l1_struct_0(A_223)
      | v2_struct_0(A_223) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_168,plain,(
    ! [A_223] :
      ( l1_waybel_0(k4_waybel_9(A_223,'#skF_7','#skF_8'),A_223)
      | ~ l1_waybel_0('#skF_7',A_223)
      | v2_struct_0('#skF_7')
      | ~ l1_struct_0(A_223)
      | v2_struct_0(A_223) ) ),
    inference(resolution,[status(thm)],[c_58,c_160])).

tff(c_173,plain,(
    ! [A_223] :
      ( l1_waybel_0(k4_waybel_9(A_223,'#skF_7','#skF_8'),A_223)
      | ~ l1_waybel_0('#skF_7',A_223)
      | ~ l1_struct_0(A_223)
      | v2_struct_0(A_223) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_168])).

tff(c_54,plain,(
    ! [A_185,B_186,C_187] :
      ( v6_waybel_0(k4_waybel_9(A_185,B_186,C_187),A_185)
      | ~ m1_subset_1(C_187,u1_struct_0(B_186))
      | ~ l1_waybel_0(B_186,A_185)
      | v2_struct_0(B_186)
      | ~ l1_struct_0(A_185)
      | v2_struct_0(A_185) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_108,plain,(
    ! [A_207,B_208] :
      ( r2_hidden('#skF_1'(A_207,B_208),A_207)
      | r1_tarski(A_207,B_208) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_117,plain,(
    ! [A_207] : r1_tarski(A_207,A_207) ),
    inference(resolution,[status(thm)],[c_108,c_4])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_118,plain,(
    ! [C_209,B_210,A_211] :
      ( r2_hidden(C_209,B_210)
      | ~ r2_hidden(C_209,A_211)
      | ~ r1_tarski(A_211,B_210) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_123,plain,(
    ! [A_1,B_2,B_210] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_210)
      | ~ r1_tarski(A_1,B_210)
      | r1_tarski(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_118])).

tff(c_304,plain,(
    ! [A_280,B_281,C_282,E_283] :
      ( '#skF_2'(k4_waybel_9(A_280,B_281,C_282),B_281,A_280,E_283,C_282) = E_283
      | ~ r2_hidden(E_283,u1_struct_0(k4_waybel_9(A_280,B_281,C_282)))
      | ~ l1_waybel_0(k4_waybel_9(A_280,B_281,C_282),A_280)
      | ~ v6_waybel_0(k4_waybel_9(A_280,B_281,C_282),A_280)
      | ~ m1_subset_1(C_282,u1_struct_0(B_281))
      | ~ l1_waybel_0(B_281,A_280)
      | v2_struct_0(B_281)
      | ~ l1_struct_0(A_280)
      | v2_struct_0(A_280) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_1677,plain,(
    ! [A_554,B_555,C_556,B_557] :
      ( '#skF_2'(k4_waybel_9(A_554,B_555,C_556),B_555,A_554,'#skF_1'(u1_struct_0(k4_waybel_9(A_554,B_555,C_556)),B_557),C_556) = '#skF_1'(u1_struct_0(k4_waybel_9(A_554,B_555,C_556)),B_557)
      | ~ l1_waybel_0(k4_waybel_9(A_554,B_555,C_556),A_554)
      | ~ v6_waybel_0(k4_waybel_9(A_554,B_555,C_556),A_554)
      | ~ m1_subset_1(C_556,u1_struct_0(B_555))
      | ~ l1_waybel_0(B_555,A_554)
      | v2_struct_0(B_555)
      | ~ l1_struct_0(A_554)
      | v2_struct_0(A_554)
      | r1_tarski(u1_struct_0(k4_waybel_9(A_554,B_555,C_556)),B_557) ) ),
    inference(resolution,[status(thm)],[c_6,c_304])).

tff(c_50,plain,(
    ! [A_13,B_101,C_145,E_178] :
      ( m1_subset_1('#skF_2'(k4_waybel_9(A_13,B_101,C_145),B_101,A_13,E_178,C_145),u1_struct_0(B_101))
      | ~ r2_hidden(E_178,u1_struct_0(k4_waybel_9(A_13,B_101,C_145)))
      | ~ l1_waybel_0(k4_waybel_9(A_13,B_101,C_145),A_13)
      | ~ v6_waybel_0(k4_waybel_9(A_13,B_101,C_145),A_13)
      | ~ m1_subset_1(C_145,u1_struct_0(B_101))
      | ~ l1_waybel_0(B_101,A_13)
      | v2_struct_0(B_101)
      | ~ l1_struct_0(A_13)
      | v2_struct_0(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_4585,plain,(
    ! [A_829,B_830,C_831,B_832] :
      ( m1_subset_1('#skF_1'(u1_struct_0(k4_waybel_9(A_829,B_830,C_831)),B_832),u1_struct_0(B_830))
      | ~ r2_hidden('#skF_1'(u1_struct_0(k4_waybel_9(A_829,B_830,C_831)),B_832),u1_struct_0(k4_waybel_9(A_829,B_830,C_831)))
      | ~ l1_waybel_0(k4_waybel_9(A_829,B_830,C_831),A_829)
      | ~ v6_waybel_0(k4_waybel_9(A_829,B_830,C_831),A_829)
      | ~ m1_subset_1(C_831,u1_struct_0(B_830))
      | ~ l1_waybel_0(B_830,A_829)
      | v2_struct_0(B_830)
      | ~ l1_struct_0(A_829)
      | v2_struct_0(A_829)
      | ~ l1_waybel_0(k4_waybel_9(A_829,B_830,C_831),A_829)
      | ~ v6_waybel_0(k4_waybel_9(A_829,B_830,C_831),A_829)
      | ~ m1_subset_1(C_831,u1_struct_0(B_830))
      | ~ l1_waybel_0(B_830,A_829)
      | v2_struct_0(B_830)
      | ~ l1_struct_0(A_829)
      | v2_struct_0(A_829)
      | r1_tarski(u1_struct_0(k4_waybel_9(A_829,B_830,C_831)),B_832) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1677,c_50])).

tff(c_4617,plain,(
    ! [A_829,B_830,C_831,B_2] :
      ( m1_subset_1('#skF_1'(u1_struct_0(k4_waybel_9(A_829,B_830,C_831)),B_2),u1_struct_0(B_830))
      | ~ l1_waybel_0(k4_waybel_9(A_829,B_830,C_831),A_829)
      | ~ v6_waybel_0(k4_waybel_9(A_829,B_830,C_831),A_829)
      | ~ m1_subset_1(C_831,u1_struct_0(B_830))
      | ~ l1_waybel_0(B_830,A_829)
      | v2_struct_0(B_830)
      | ~ l1_struct_0(A_829)
      | v2_struct_0(A_829)
      | ~ r1_tarski(u1_struct_0(k4_waybel_9(A_829,B_830,C_831)),u1_struct_0(k4_waybel_9(A_829,B_830,C_831)))
      | r1_tarski(u1_struct_0(k4_waybel_9(A_829,B_830,C_831)),B_2) ) ),
    inference(resolution,[status(thm)],[c_123,c_4585])).

tff(c_4647,plain,(
    ! [A_833,B_834,C_835,B_836] :
      ( m1_subset_1('#skF_1'(u1_struct_0(k4_waybel_9(A_833,B_834,C_835)),B_836),u1_struct_0(B_834))
      | ~ l1_waybel_0(k4_waybel_9(A_833,B_834,C_835),A_833)
      | ~ v6_waybel_0(k4_waybel_9(A_833,B_834,C_835),A_833)
      | ~ m1_subset_1(C_835,u1_struct_0(B_834))
      | ~ l1_waybel_0(B_834,A_833)
      | v2_struct_0(B_834)
      | ~ l1_struct_0(A_833)
      | v2_struct_0(A_833)
      | r1_tarski(u1_struct_0(k4_waybel_9(A_833,B_834,C_835)),B_836) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_4617])).

tff(c_4651,plain,(
    ! [A_837,B_838,C_839,B_840] :
      ( m1_subset_1('#skF_1'(u1_struct_0(k4_waybel_9(A_837,B_838,C_839)),B_840),u1_struct_0(B_838))
      | ~ l1_waybel_0(k4_waybel_9(A_837,B_838,C_839),A_837)
      | r1_tarski(u1_struct_0(k4_waybel_9(A_837,B_838,C_839)),B_840)
      | ~ m1_subset_1(C_839,u1_struct_0(B_838))
      | ~ l1_waybel_0(B_838,A_837)
      | v2_struct_0(B_838)
      | ~ l1_struct_0(A_837)
      | v2_struct_0(A_837) ) ),
    inference(resolution,[status(thm)],[c_54,c_4647])).

tff(c_4667,plain,(
    ! [A_223,B_840] :
      ( m1_subset_1('#skF_1'(u1_struct_0(k4_waybel_9(A_223,'#skF_7','#skF_8')),B_840),u1_struct_0('#skF_7'))
      | r1_tarski(u1_struct_0(k4_waybel_9(A_223,'#skF_7','#skF_8')),B_840)
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_7'))
      | v2_struct_0('#skF_7')
      | ~ l1_waybel_0('#skF_7',A_223)
      | ~ l1_struct_0(A_223)
      | v2_struct_0(A_223) ) ),
    inference(resolution,[status(thm)],[c_173,c_4651])).

tff(c_4681,plain,(
    ! [A_223,B_840] :
      ( m1_subset_1('#skF_1'(u1_struct_0(k4_waybel_9(A_223,'#skF_7','#skF_8')),B_840),u1_struct_0('#skF_7'))
      | r1_tarski(u1_struct_0(k4_waybel_9(A_223,'#skF_7','#skF_8')),B_840)
      | v2_struct_0('#skF_7')
      | ~ l1_waybel_0('#skF_7',A_223)
      | ~ l1_struct_0(A_223)
      | v2_struct_0(A_223) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_4667])).

tff(c_4683,plain,(
    ! [A_841,B_842] :
      ( m1_subset_1('#skF_1'(u1_struct_0(k4_waybel_9(A_841,'#skF_7','#skF_8')),B_842),u1_struct_0('#skF_7'))
      | r1_tarski(u1_struct_0(k4_waybel_9(A_841,'#skF_7','#skF_8')),B_842)
      | ~ l1_waybel_0('#skF_7',A_841)
      | ~ l1_struct_0(A_841)
      | v2_struct_0(A_841) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_4681])).

tff(c_10,plain,(
    ! [B_7,A_6] :
      ( r2_hidden(B_7,A_6)
      | ~ m1_subset_1(B_7,A_6)
      | v1_xboole_0(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_97,plain,(
    ! [A_203,B_204] :
      ( ~ r2_hidden('#skF_1'(A_203,B_204),B_204)
      | r1_tarski(A_203,B_204) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_102,plain,(
    ! [A_203,A_6] :
      ( r1_tarski(A_203,A_6)
      | ~ m1_subset_1('#skF_1'(A_203,A_6),A_6)
      | v1_xboole_0(A_6) ) ),
    inference(resolution,[status(thm)],[c_10,c_97])).

tff(c_4697,plain,(
    ! [A_841] :
      ( v1_xboole_0(u1_struct_0('#skF_7'))
      | r1_tarski(u1_struct_0(k4_waybel_9(A_841,'#skF_7','#skF_8')),u1_struct_0('#skF_7'))
      | ~ l1_waybel_0('#skF_7',A_841)
      | ~ l1_struct_0(A_841)
      | v2_struct_0(A_841) ) ),
    inference(resolution,[status(thm)],[c_4683,c_102])).

tff(c_4741,plain,(
    ! [A_846] :
      ( r1_tarski(u1_struct_0(k4_waybel_9(A_846,'#skF_7','#skF_8')),u1_struct_0('#skF_7'))
      | ~ l1_waybel_0('#skF_7',A_846)
      | ~ l1_struct_0(A_846)
      | v2_struct_0(A_846) ) ),
    inference(negUnitSimplification,[status(thm)],[c_79,c_4697])).

tff(c_56,plain,(
    ~ r1_tarski(u1_struct_0(k4_waybel_9('#skF_6','#skF_7','#skF_8')),u1_struct_0('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_4756,plain,
    ( ~ l1_waybel_0('#skF_7','#skF_6')
    | ~ l1_struct_0('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_4741,c_56])).

tff(c_4774,plain,(
    v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_60,c_4756])).

tff(c_4776,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_4774])).

tff(c_4778,plain,(
    v1_xboole_0(u1_struct_0('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_4786,plain,(
    ! [A_849] :
      ( v2_struct_0(A_849)
      | ~ v1_xboole_0(u1_struct_0(A_849))
      | ~ l1_struct_0(A_849) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_4789,plain,
    ( v2_struct_0('#skF_7')
    | ~ l1_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_4778,c_4786])).

tff(c_4795,plain,(
    ~ l1_struct_0('#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_4789])).

tff(c_4799,plain,(
    ~ l1_orders_2('#skF_7') ),
    inference(resolution,[status(thm)],[c_16,c_4795])).

tff(c_4803,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4785,c_4799])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:10:12 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.44/3.14  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.44/3.15  
% 8.44/3.15  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.44/3.15  %$ r2_relset_1 > r1_orders_2 > v6_waybel_0 > r2_hidden > r1_tarski > m1_subset_1 > l1_waybel_0 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > k2_partfun1 > k4_waybel_9 > u1_waybel_0 > k1_toler_1 > #nlpp > u1_struct_0 > u1_orders_2 > #skF_2 > #skF_7 > #skF_6 > #skF_4 > #skF_8 > #skF_5 > #skF_3 > #skF_1
% 8.44/3.15  
% 8.44/3.15  %Foreground sorts:
% 8.44/3.15  
% 8.44/3.15  
% 8.44/3.15  %Background operators:
% 8.44/3.15  
% 8.44/3.15  
% 8.44/3.15  %Foreground operators:
% 8.44/3.15  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 8.44/3.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.44/3.15  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 8.44/3.15  tff(v6_waybel_0, type, v6_waybel_0: ($i * $i) > $o).
% 8.44/3.15  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.44/3.15  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i) > $i).
% 8.44/3.15  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 8.44/3.15  tff(k4_waybel_9, type, k4_waybel_9: ($i * $i * $i) > $i).
% 8.44/3.15  tff(k1_toler_1, type, k1_toler_1: ($i * $i) > $i).
% 8.44/3.15  tff('#skF_7', type, '#skF_7': $i).
% 8.44/3.15  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.44/3.15  tff('#skF_6', type, '#skF_6': $i).
% 8.44/3.15  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 8.44/3.15  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 8.44/3.15  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 8.44/3.15  tff(u1_waybel_0, type, u1_waybel_0: ($i * $i) > $i).
% 8.44/3.15  tff('#skF_8', type, '#skF_8': $i).
% 8.44/3.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.44/3.15  tff(l1_waybel_0, type, l1_waybel_0: ($i * $i) > $o).
% 8.44/3.15  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i) > $i).
% 8.44/3.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.44/3.15  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 8.44/3.15  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 8.44/3.15  tff(u1_orders_2, type, u1_orders_2: $i > $i).
% 8.44/3.15  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 8.44/3.15  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 8.44/3.15  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 8.44/3.15  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.44/3.15  
% 8.44/3.16  tff(f_130, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((~v2_struct_0(B) & l1_waybel_0(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(B)) => r1_tarski(u1_struct_0(k4_waybel_9(A, B, C)), u1_struct_0(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_waybel_9)).
% 8.44/3.16  tff(f_56, axiom, (![A]: (l1_struct_0(A) => (![B]: (l1_waybel_0(B, A) => l1_orders_2(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_waybel_0)).
% 8.44/3.16  tff(f_49, axiom, (![A]: (l1_orders_2(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 8.44/3.16  tff(f_45, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 8.44/3.16  tff(f_113, axiom, (![A, B, C]: (((((~v2_struct_0(A) & l1_struct_0(A)) & ~v2_struct_0(B)) & l1_waybel_0(B, A)) & m1_subset_1(C, u1_struct_0(B))) => (v6_waybel_0(k4_waybel_9(A, B, C), A) & l1_waybel_0(k4_waybel_9(A, B, C), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_waybel_9)).
% 8.44/3.16  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 8.44/3.16  tff(f_97, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((~v2_struct_0(B) & l1_waybel_0(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(B)) => (![D]: ((v6_waybel_0(D, A) & l1_waybel_0(D, A)) => ((D = k4_waybel_9(A, B, C)) <=> (((![E]: (r2_hidden(E, u1_struct_0(D)) <=> (?[F]: ((m1_subset_1(F, u1_struct_0(B)) & (F = E)) & r1_orders_2(B, C, F))))) & r2_relset_1(u1_struct_0(D), u1_struct_0(D), u1_orders_2(D), k1_toler_1(u1_orders_2(B), u1_struct_0(D)))) & (u1_waybel_0(A, D) = k2_partfun1(u1_struct_0(B), u1_struct_0(A), u1_waybel_0(A, B), u1_struct_0(D))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_waybel_9)).
% 8.44/3.16  tff(f_62, axiom, (![A]: (l1_struct_0(A) => (v2_struct_0(A) <=> v1_xboole_0(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_struct_0)).
% 8.44/3.16  tff(c_64, plain, (l1_struct_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_130])).
% 8.44/3.16  tff(c_60, plain, (l1_waybel_0('#skF_7', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_130])).
% 8.44/3.16  tff(c_4779, plain, (![B_847, A_848]: (l1_orders_2(B_847) | ~l1_waybel_0(B_847, A_848) | ~l1_struct_0(A_848))), inference(cnfTransformation, [status(thm)], [f_56])).
% 8.44/3.16  tff(c_4782, plain, (l1_orders_2('#skF_7') | ~l1_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_60, c_4779])).
% 8.44/3.16  tff(c_4785, plain, (l1_orders_2('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_4782])).
% 8.44/3.16  tff(c_16, plain, (![A_8]: (l1_struct_0(A_8) | ~l1_orders_2(A_8))), inference(cnfTransformation, [status(thm)], [f_49])).
% 8.44/3.16  tff(c_62, plain, (~v2_struct_0('#skF_7')), inference(cnfTransformation, [status(thm)], [f_130])).
% 8.44/3.16  tff(c_66, plain, (~v2_struct_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_130])).
% 8.44/3.16  tff(c_58, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_130])).
% 8.44/3.16  tff(c_70, plain, (![B_196, A_197]: (v1_xboole_0(B_196) | ~m1_subset_1(B_196, A_197) | ~v1_xboole_0(A_197))), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.44/3.16  tff(c_78, plain, (v1_xboole_0('#skF_8') | ~v1_xboole_0(u1_struct_0('#skF_7'))), inference(resolution, [status(thm)], [c_58, c_70])).
% 8.44/3.16  tff(c_79, plain, (~v1_xboole_0(u1_struct_0('#skF_7'))), inference(splitLeft, [status(thm)], [c_78])).
% 8.44/3.16  tff(c_160, plain, (![A_223, B_224, C_225]: (l1_waybel_0(k4_waybel_9(A_223, B_224, C_225), A_223) | ~m1_subset_1(C_225, u1_struct_0(B_224)) | ~l1_waybel_0(B_224, A_223) | v2_struct_0(B_224) | ~l1_struct_0(A_223) | v2_struct_0(A_223))), inference(cnfTransformation, [status(thm)], [f_113])).
% 8.44/3.16  tff(c_168, plain, (![A_223]: (l1_waybel_0(k4_waybel_9(A_223, '#skF_7', '#skF_8'), A_223) | ~l1_waybel_0('#skF_7', A_223) | v2_struct_0('#skF_7') | ~l1_struct_0(A_223) | v2_struct_0(A_223))), inference(resolution, [status(thm)], [c_58, c_160])).
% 8.44/3.16  tff(c_173, plain, (![A_223]: (l1_waybel_0(k4_waybel_9(A_223, '#skF_7', '#skF_8'), A_223) | ~l1_waybel_0('#skF_7', A_223) | ~l1_struct_0(A_223) | v2_struct_0(A_223))), inference(negUnitSimplification, [status(thm)], [c_62, c_168])).
% 8.44/3.16  tff(c_54, plain, (![A_185, B_186, C_187]: (v6_waybel_0(k4_waybel_9(A_185, B_186, C_187), A_185) | ~m1_subset_1(C_187, u1_struct_0(B_186)) | ~l1_waybel_0(B_186, A_185) | v2_struct_0(B_186) | ~l1_struct_0(A_185) | v2_struct_0(A_185))), inference(cnfTransformation, [status(thm)], [f_113])).
% 8.44/3.16  tff(c_108, plain, (![A_207, B_208]: (r2_hidden('#skF_1'(A_207, B_208), A_207) | r1_tarski(A_207, B_208))), inference(cnfTransformation, [status(thm)], [f_32])).
% 8.44/3.16  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 8.44/3.16  tff(c_117, plain, (![A_207]: (r1_tarski(A_207, A_207))), inference(resolution, [status(thm)], [c_108, c_4])).
% 8.44/3.16  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 8.44/3.17  tff(c_118, plain, (![C_209, B_210, A_211]: (r2_hidden(C_209, B_210) | ~r2_hidden(C_209, A_211) | ~r1_tarski(A_211, B_210))), inference(cnfTransformation, [status(thm)], [f_32])).
% 8.44/3.17  tff(c_123, plain, (![A_1, B_2, B_210]: (r2_hidden('#skF_1'(A_1, B_2), B_210) | ~r1_tarski(A_1, B_210) | r1_tarski(A_1, B_2))), inference(resolution, [status(thm)], [c_6, c_118])).
% 8.44/3.17  tff(c_304, plain, (![A_280, B_281, C_282, E_283]: ('#skF_2'(k4_waybel_9(A_280, B_281, C_282), B_281, A_280, E_283, C_282)=E_283 | ~r2_hidden(E_283, u1_struct_0(k4_waybel_9(A_280, B_281, C_282))) | ~l1_waybel_0(k4_waybel_9(A_280, B_281, C_282), A_280) | ~v6_waybel_0(k4_waybel_9(A_280, B_281, C_282), A_280) | ~m1_subset_1(C_282, u1_struct_0(B_281)) | ~l1_waybel_0(B_281, A_280) | v2_struct_0(B_281) | ~l1_struct_0(A_280) | v2_struct_0(A_280))), inference(cnfTransformation, [status(thm)], [f_97])).
% 8.44/3.17  tff(c_1677, plain, (![A_554, B_555, C_556, B_557]: ('#skF_2'(k4_waybel_9(A_554, B_555, C_556), B_555, A_554, '#skF_1'(u1_struct_0(k4_waybel_9(A_554, B_555, C_556)), B_557), C_556)='#skF_1'(u1_struct_0(k4_waybel_9(A_554, B_555, C_556)), B_557) | ~l1_waybel_0(k4_waybel_9(A_554, B_555, C_556), A_554) | ~v6_waybel_0(k4_waybel_9(A_554, B_555, C_556), A_554) | ~m1_subset_1(C_556, u1_struct_0(B_555)) | ~l1_waybel_0(B_555, A_554) | v2_struct_0(B_555) | ~l1_struct_0(A_554) | v2_struct_0(A_554) | r1_tarski(u1_struct_0(k4_waybel_9(A_554, B_555, C_556)), B_557))), inference(resolution, [status(thm)], [c_6, c_304])).
% 8.44/3.17  tff(c_50, plain, (![A_13, B_101, C_145, E_178]: (m1_subset_1('#skF_2'(k4_waybel_9(A_13, B_101, C_145), B_101, A_13, E_178, C_145), u1_struct_0(B_101)) | ~r2_hidden(E_178, u1_struct_0(k4_waybel_9(A_13, B_101, C_145))) | ~l1_waybel_0(k4_waybel_9(A_13, B_101, C_145), A_13) | ~v6_waybel_0(k4_waybel_9(A_13, B_101, C_145), A_13) | ~m1_subset_1(C_145, u1_struct_0(B_101)) | ~l1_waybel_0(B_101, A_13) | v2_struct_0(B_101) | ~l1_struct_0(A_13) | v2_struct_0(A_13))), inference(cnfTransformation, [status(thm)], [f_97])).
% 8.44/3.17  tff(c_4585, plain, (![A_829, B_830, C_831, B_832]: (m1_subset_1('#skF_1'(u1_struct_0(k4_waybel_9(A_829, B_830, C_831)), B_832), u1_struct_0(B_830)) | ~r2_hidden('#skF_1'(u1_struct_0(k4_waybel_9(A_829, B_830, C_831)), B_832), u1_struct_0(k4_waybel_9(A_829, B_830, C_831))) | ~l1_waybel_0(k4_waybel_9(A_829, B_830, C_831), A_829) | ~v6_waybel_0(k4_waybel_9(A_829, B_830, C_831), A_829) | ~m1_subset_1(C_831, u1_struct_0(B_830)) | ~l1_waybel_0(B_830, A_829) | v2_struct_0(B_830) | ~l1_struct_0(A_829) | v2_struct_0(A_829) | ~l1_waybel_0(k4_waybel_9(A_829, B_830, C_831), A_829) | ~v6_waybel_0(k4_waybel_9(A_829, B_830, C_831), A_829) | ~m1_subset_1(C_831, u1_struct_0(B_830)) | ~l1_waybel_0(B_830, A_829) | v2_struct_0(B_830) | ~l1_struct_0(A_829) | v2_struct_0(A_829) | r1_tarski(u1_struct_0(k4_waybel_9(A_829, B_830, C_831)), B_832))), inference(superposition, [status(thm), theory('equality')], [c_1677, c_50])).
% 8.44/3.17  tff(c_4617, plain, (![A_829, B_830, C_831, B_2]: (m1_subset_1('#skF_1'(u1_struct_0(k4_waybel_9(A_829, B_830, C_831)), B_2), u1_struct_0(B_830)) | ~l1_waybel_0(k4_waybel_9(A_829, B_830, C_831), A_829) | ~v6_waybel_0(k4_waybel_9(A_829, B_830, C_831), A_829) | ~m1_subset_1(C_831, u1_struct_0(B_830)) | ~l1_waybel_0(B_830, A_829) | v2_struct_0(B_830) | ~l1_struct_0(A_829) | v2_struct_0(A_829) | ~r1_tarski(u1_struct_0(k4_waybel_9(A_829, B_830, C_831)), u1_struct_0(k4_waybel_9(A_829, B_830, C_831))) | r1_tarski(u1_struct_0(k4_waybel_9(A_829, B_830, C_831)), B_2))), inference(resolution, [status(thm)], [c_123, c_4585])).
% 8.44/3.17  tff(c_4647, plain, (![A_833, B_834, C_835, B_836]: (m1_subset_1('#skF_1'(u1_struct_0(k4_waybel_9(A_833, B_834, C_835)), B_836), u1_struct_0(B_834)) | ~l1_waybel_0(k4_waybel_9(A_833, B_834, C_835), A_833) | ~v6_waybel_0(k4_waybel_9(A_833, B_834, C_835), A_833) | ~m1_subset_1(C_835, u1_struct_0(B_834)) | ~l1_waybel_0(B_834, A_833) | v2_struct_0(B_834) | ~l1_struct_0(A_833) | v2_struct_0(A_833) | r1_tarski(u1_struct_0(k4_waybel_9(A_833, B_834, C_835)), B_836))), inference(demodulation, [status(thm), theory('equality')], [c_117, c_4617])).
% 8.44/3.17  tff(c_4651, plain, (![A_837, B_838, C_839, B_840]: (m1_subset_1('#skF_1'(u1_struct_0(k4_waybel_9(A_837, B_838, C_839)), B_840), u1_struct_0(B_838)) | ~l1_waybel_0(k4_waybel_9(A_837, B_838, C_839), A_837) | r1_tarski(u1_struct_0(k4_waybel_9(A_837, B_838, C_839)), B_840) | ~m1_subset_1(C_839, u1_struct_0(B_838)) | ~l1_waybel_0(B_838, A_837) | v2_struct_0(B_838) | ~l1_struct_0(A_837) | v2_struct_0(A_837))), inference(resolution, [status(thm)], [c_54, c_4647])).
% 8.44/3.17  tff(c_4667, plain, (![A_223, B_840]: (m1_subset_1('#skF_1'(u1_struct_0(k4_waybel_9(A_223, '#skF_7', '#skF_8')), B_840), u1_struct_0('#skF_7')) | r1_tarski(u1_struct_0(k4_waybel_9(A_223, '#skF_7', '#skF_8')), B_840) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_7')) | v2_struct_0('#skF_7') | ~l1_waybel_0('#skF_7', A_223) | ~l1_struct_0(A_223) | v2_struct_0(A_223))), inference(resolution, [status(thm)], [c_173, c_4651])).
% 8.44/3.17  tff(c_4681, plain, (![A_223, B_840]: (m1_subset_1('#skF_1'(u1_struct_0(k4_waybel_9(A_223, '#skF_7', '#skF_8')), B_840), u1_struct_0('#skF_7')) | r1_tarski(u1_struct_0(k4_waybel_9(A_223, '#skF_7', '#skF_8')), B_840) | v2_struct_0('#skF_7') | ~l1_waybel_0('#skF_7', A_223) | ~l1_struct_0(A_223) | v2_struct_0(A_223))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_4667])).
% 8.44/3.17  tff(c_4683, plain, (![A_841, B_842]: (m1_subset_1('#skF_1'(u1_struct_0(k4_waybel_9(A_841, '#skF_7', '#skF_8')), B_842), u1_struct_0('#skF_7')) | r1_tarski(u1_struct_0(k4_waybel_9(A_841, '#skF_7', '#skF_8')), B_842) | ~l1_waybel_0('#skF_7', A_841) | ~l1_struct_0(A_841) | v2_struct_0(A_841))), inference(negUnitSimplification, [status(thm)], [c_62, c_4681])).
% 8.44/3.17  tff(c_10, plain, (![B_7, A_6]: (r2_hidden(B_7, A_6) | ~m1_subset_1(B_7, A_6) | v1_xboole_0(A_6))), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.44/3.17  tff(c_97, plain, (![A_203, B_204]: (~r2_hidden('#skF_1'(A_203, B_204), B_204) | r1_tarski(A_203, B_204))), inference(cnfTransformation, [status(thm)], [f_32])).
% 8.44/3.17  tff(c_102, plain, (![A_203, A_6]: (r1_tarski(A_203, A_6) | ~m1_subset_1('#skF_1'(A_203, A_6), A_6) | v1_xboole_0(A_6))), inference(resolution, [status(thm)], [c_10, c_97])).
% 8.44/3.17  tff(c_4697, plain, (![A_841]: (v1_xboole_0(u1_struct_0('#skF_7')) | r1_tarski(u1_struct_0(k4_waybel_9(A_841, '#skF_7', '#skF_8')), u1_struct_0('#skF_7')) | ~l1_waybel_0('#skF_7', A_841) | ~l1_struct_0(A_841) | v2_struct_0(A_841))), inference(resolution, [status(thm)], [c_4683, c_102])).
% 8.44/3.17  tff(c_4741, plain, (![A_846]: (r1_tarski(u1_struct_0(k4_waybel_9(A_846, '#skF_7', '#skF_8')), u1_struct_0('#skF_7')) | ~l1_waybel_0('#skF_7', A_846) | ~l1_struct_0(A_846) | v2_struct_0(A_846))), inference(negUnitSimplification, [status(thm)], [c_79, c_4697])).
% 8.44/3.17  tff(c_56, plain, (~r1_tarski(u1_struct_0(k4_waybel_9('#skF_6', '#skF_7', '#skF_8')), u1_struct_0('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_130])).
% 8.44/3.17  tff(c_4756, plain, (~l1_waybel_0('#skF_7', '#skF_6') | ~l1_struct_0('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_4741, c_56])).
% 8.44/3.17  tff(c_4774, plain, (v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_60, c_4756])).
% 8.44/3.17  tff(c_4776, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_4774])).
% 8.44/3.17  tff(c_4778, plain, (v1_xboole_0(u1_struct_0('#skF_7'))), inference(splitRight, [status(thm)], [c_78])).
% 8.44/3.17  tff(c_4786, plain, (![A_849]: (v2_struct_0(A_849) | ~v1_xboole_0(u1_struct_0(A_849)) | ~l1_struct_0(A_849))), inference(cnfTransformation, [status(thm)], [f_62])).
% 8.44/3.17  tff(c_4789, plain, (v2_struct_0('#skF_7') | ~l1_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_4778, c_4786])).
% 8.44/3.17  tff(c_4795, plain, (~l1_struct_0('#skF_7')), inference(negUnitSimplification, [status(thm)], [c_62, c_4789])).
% 8.44/3.17  tff(c_4799, plain, (~l1_orders_2('#skF_7')), inference(resolution, [status(thm)], [c_16, c_4795])).
% 8.44/3.17  tff(c_4803, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4785, c_4799])).
% 8.44/3.17  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.44/3.17  
% 8.44/3.17  Inference rules
% 8.44/3.17  ----------------------
% 8.44/3.17  #Ref     : 0
% 8.44/3.17  #Sup     : 980
% 8.44/3.17  #Fact    : 0
% 8.44/3.17  #Define  : 0
% 8.44/3.17  #Split   : 6
% 8.44/3.17  #Chain   : 0
% 8.44/3.17  #Close   : 0
% 8.44/3.17  
% 8.44/3.17  Ordering : KBO
% 8.44/3.17  
% 8.44/3.17  Simplification rules
% 8.44/3.17  ----------------------
% 8.44/3.17  #Subsume      : 324
% 8.44/3.17  #Demod        : 196
% 8.44/3.17  #Tautology    : 363
% 8.44/3.17  #SimpNegUnit  : 342
% 8.44/3.17  #BackRed      : 0
% 8.44/3.17  
% 8.44/3.17  #Partial instantiations: 0
% 8.44/3.17  #Strategies tried      : 1
% 8.44/3.17  
% 8.44/3.17  Timing (in seconds)
% 8.44/3.17  ----------------------
% 8.44/3.17  Preprocessing        : 0.35
% 8.44/3.17  Parsing              : 0.17
% 8.44/3.17  CNF conversion       : 0.04
% 8.44/3.17  Main loop            : 2.05
% 8.44/3.17  Inferencing          : 0.66
% 8.44/3.17  Reduction            : 0.45
% 8.44/3.17  Demodulation         : 0.30
% 8.44/3.17  BG Simplification    : 0.08
% 8.44/3.17  Subsumption          : 0.77
% 8.44/3.17  Abstraction          : 0.11
% 8.44/3.17  MUC search           : 0.00
% 8.44/3.17  Cooper               : 0.00
% 8.44/3.17  Total                : 2.44
% 8.44/3.17  Index Insertion      : 0.00
% 8.44/3.17  Index Deletion       : 0.00
% 8.44/3.17  Index Matching       : 0.00
% 8.44/3.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
