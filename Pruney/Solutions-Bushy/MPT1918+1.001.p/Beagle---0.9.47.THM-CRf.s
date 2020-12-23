%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1918+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:41 EST 2020

% Result     : Theorem 1.90s
% Output     : CNFRefutation 1.90s
% Verified   : 
% Statistics : Number of formulae       :   44 (  83 expanded)
%              Number of leaves         :   15 (  36 expanded)
%              Depth                    :   11
%              Number of atoms          :  106 ( 218 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_yellow_0 > l1_orders_2 > #nlpp > u1_struct_0 > u1_orders_2 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(m1_yellow_0,type,(
    m1_yellow_0: ( $i * $i ) > $o )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_orders_2,type,(
    u1_orders_2: $i > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(f_59,negated_conjecture,(
    ~ ! [A] :
        ( l1_orders_2(A)
       => ! [B] :
            ( m1_yellow_0(B,A)
           => ! [C] :
                ( m1_yellow_0(C,B)
               => m1_yellow_0(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_yellow_6)).

tff(f_42,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( m1_yellow_0(B,A)
         => l1_orders_2(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_yellow_0)).

tff(f_35,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( l1_orders_2(B)
         => ( m1_yellow_0(B,A)
          <=> ( r1_tarski(u1_struct_0(B),u1_struct_0(A))
              & r1_tarski(u1_orders_2(B),u1_orders_2(A)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_yellow_0)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(c_12,plain,(
    ~ m1_yellow_0('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_18,plain,(
    l1_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_16,plain,(
    m1_yellow_0('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_19,plain,(
    ! [B_14,A_15] :
      ( l1_orders_2(B_14)
      | ~ m1_yellow_0(B_14,A_15)
      | ~ l1_orders_2(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_25,plain,
    ( l1_orders_2('#skF_2')
    | ~ l1_orders_2('#skF_1') ),
    inference(resolution,[status(thm)],[c_16,c_19])).

tff(c_29,plain,(
    l1_orders_2('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_25])).

tff(c_14,plain,(
    m1_yellow_0('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_26,plain,
    ( l1_orders_2('#skF_3')
    | ~ l1_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_14,c_19])).

tff(c_32,plain,(
    l1_orders_2('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_29,c_26])).

tff(c_4,plain,(
    ! [B_3,A_1] :
      ( r1_tarski(u1_orders_2(B_3),u1_orders_2(A_1))
      | ~ m1_yellow_0(B_3,A_1)
      | ~ l1_orders_2(B_3)
      | ~ l1_orders_2(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_37,plain,(
    ! [B_21,A_22] :
      ( r1_tarski(u1_orders_2(B_21),u1_orders_2(A_22))
      | ~ m1_yellow_0(B_21,A_22)
      | ~ l1_orders_2(B_21)
      | ~ l1_orders_2(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_10,plain,(
    ! [A_7,C_9,B_8] :
      ( r1_tarski(A_7,C_9)
      | ~ r1_tarski(B_8,C_9)
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_45,plain,(
    ! [A_26,A_27,B_28] :
      ( r1_tarski(A_26,u1_orders_2(A_27))
      | ~ r1_tarski(A_26,u1_orders_2(B_28))
      | ~ m1_yellow_0(B_28,A_27)
      | ~ l1_orders_2(B_28)
      | ~ l1_orders_2(A_27) ) ),
    inference(resolution,[status(thm)],[c_37,c_10])).

tff(c_54,plain,(
    ! [B_31,A_32,A_33] :
      ( r1_tarski(u1_orders_2(B_31),u1_orders_2(A_32))
      | ~ m1_yellow_0(A_33,A_32)
      | ~ l1_orders_2(A_32)
      | ~ m1_yellow_0(B_31,A_33)
      | ~ l1_orders_2(B_31)
      | ~ l1_orders_2(A_33) ) ),
    inference(resolution,[status(thm)],[c_4,c_45])).

tff(c_58,plain,(
    ! [B_31] :
      ( r1_tarski(u1_orders_2(B_31),u1_orders_2('#skF_1'))
      | ~ l1_orders_2('#skF_1')
      | ~ m1_yellow_0(B_31,'#skF_2')
      | ~ l1_orders_2(B_31)
      | ~ l1_orders_2('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_16,c_54])).

tff(c_64,plain,(
    ! [B_31] :
      ( r1_tarski(u1_orders_2(B_31),u1_orders_2('#skF_1'))
      | ~ m1_yellow_0(B_31,'#skF_2')
      | ~ l1_orders_2(B_31) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_29,c_18,c_58])).

tff(c_6,plain,(
    ! [B_3,A_1] :
      ( r1_tarski(u1_struct_0(B_3),u1_struct_0(A_1))
      | ~ m1_yellow_0(B_3,A_1)
      | ~ l1_orders_2(B_3)
      | ~ l1_orders_2(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_33,plain,(
    ! [B_19,A_20] :
      ( r1_tarski(u1_struct_0(B_19),u1_struct_0(A_20))
      | ~ m1_yellow_0(B_19,A_20)
      | ~ l1_orders_2(B_19)
      | ~ l1_orders_2(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_41,plain,(
    ! [A_23,A_24,B_25] :
      ( r1_tarski(A_23,u1_struct_0(A_24))
      | ~ r1_tarski(A_23,u1_struct_0(B_25))
      | ~ m1_yellow_0(B_25,A_24)
      | ~ l1_orders_2(B_25)
      | ~ l1_orders_2(A_24) ) ),
    inference(resolution,[status(thm)],[c_33,c_10])).

tff(c_74,plain,(
    ! [B_35,A_36,A_37] :
      ( r1_tarski(u1_struct_0(B_35),u1_struct_0(A_36))
      | ~ m1_yellow_0(A_37,A_36)
      | ~ l1_orders_2(A_36)
      | ~ m1_yellow_0(B_35,A_37)
      | ~ l1_orders_2(B_35)
      | ~ l1_orders_2(A_37) ) ),
    inference(resolution,[status(thm)],[c_6,c_41])).

tff(c_78,plain,(
    ! [B_35] :
      ( r1_tarski(u1_struct_0(B_35),u1_struct_0('#skF_1'))
      | ~ l1_orders_2('#skF_1')
      | ~ m1_yellow_0(B_35,'#skF_2')
      | ~ l1_orders_2(B_35)
      | ~ l1_orders_2('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_16,c_74])).

tff(c_94,plain,(
    ! [B_39] :
      ( r1_tarski(u1_struct_0(B_39),u1_struct_0('#skF_1'))
      | ~ m1_yellow_0(B_39,'#skF_2')
      | ~ l1_orders_2(B_39) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_29,c_18,c_78])).

tff(c_2,plain,(
    ! [B_3,A_1] :
      ( m1_yellow_0(B_3,A_1)
      | ~ r1_tarski(u1_orders_2(B_3),u1_orders_2(A_1))
      | ~ r1_tarski(u1_struct_0(B_3),u1_struct_0(A_1))
      | ~ l1_orders_2(B_3)
      | ~ l1_orders_2(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_97,plain,(
    ! [B_39] :
      ( m1_yellow_0(B_39,'#skF_1')
      | ~ r1_tarski(u1_orders_2(B_39),u1_orders_2('#skF_1'))
      | ~ l1_orders_2('#skF_1')
      | ~ m1_yellow_0(B_39,'#skF_2')
      | ~ l1_orders_2(B_39) ) ),
    inference(resolution,[status(thm)],[c_94,c_2])).

tff(c_138,plain,(
    ! [B_43] :
      ( m1_yellow_0(B_43,'#skF_1')
      | ~ r1_tarski(u1_orders_2(B_43),u1_orders_2('#skF_1'))
      | ~ m1_yellow_0(B_43,'#skF_2')
      | ~ l1_orders_2(B_43) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_97])).

tff(c_150,plain,(
    ! [B_44] :
      ( m1_yellow_0(B_44,'#skF_1')
      | ~ m1_yellow_0(B_44,'#skF_2')
      | ~ l1_orders_2(B_44) ) ),
    inference(resolution,[status(thm)],[c_64,c_138])).

tff(c_153,plain,
    ( m1_yellow_0('#skF_3','#skF_1')
    | ~ l1_orders_2('#skF_3') ),
    inference(resolution,[status(thm)],[c_14,c_150])).

tff(c_156,plain,(
    m1_yellow_0('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_153])).

tff(c_158,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12,c_156])).

%------------------------------------------------------------------------------
