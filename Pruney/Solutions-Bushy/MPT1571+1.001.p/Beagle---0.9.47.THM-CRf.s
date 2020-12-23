%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1571+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:05 EST 2020

% Result     : Theorem 2.97s
% Output     : CNFRefutation 3.34s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 489 expanded)
%              Number of leaves         :   20 ( 175 expanded)
%              Depth                    :   18
%              Number of atoms          :  254 (1873 expanded)
%              Number of equality atoms :   16 ( 168 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_orders_2 > r1_lattice3 > r2_yellow_0 > m1_subset_1 > v2_struct_0 > l1_orders_2 > k2_yellow_0 > #nlpp > u1_struct_0 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r2_yellow_0,type,(
    r2_yellow_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k2_yellow_0,type,(
    k2_yellow_0: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(r1_lattice3,type,(
    r1_lattice3: ( $i * $i * $i ) > $o )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_81,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & l1_orders_2(A) )
       => ! [B,C] :
            ( ( r2_yellow_0(A,B)
              & ! [D] :
                  ( m1_subset_1(D,u1_struct_0(A))
                 => ( r1_lattice3(A,B,D)
                  <=> r1_lattice3(A,C,D) ) ) )
           => k2_yellow_0(A,B) = k2_yellow_0(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_yellow_0)).

tff(f_46,axiom,(
    ! [A,B] :
      ( l1_orders_2(A)
     => m1_subset_1(k2_yellow_0(A,B),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_yellow_0)).

tff(f_42,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B,C] :
          ( m1_subset_1(C,u1_struct_0(A))
         => ( r2_yellow_0(A,B)
           => ( C = k2_yellow_0(A,B)
            <=> ( r1_lattice3(A,B,C)
                & ! [D] :
                    ( m1_subset_1(D,u1_struct_0(A))
                   => ( r1_lattice3(A,B,D)
                     => r1_orders_2(A,D,C) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_yellow_0)).

tff(f_63,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_orders_2(A) )
     => ! [B,C] :
          ( ( ! [D] :
                ( m1_subset_1(D,u1_struct_0(A))
               => ( r1_lattice3(A,B,D)
                <=> r1_lattice3(A,C,D) ) )
            & r2_yellow_0(A,B) )
         => r2_yellow_0(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_yellow_0)).

tff(c_28,plain,(
    l1_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_26,plain,(
    r2_yellow_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_12,plain,(
    ! [A_13,B_14] :
      ( m1_subset_1(k2_yellow_0(A_13,B_14),u1_struct_0(A_13))
      | ~ l1_orders_2(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_58,plain,(
    ! [A_35,B_36] :
      ( r1_lattice3(A_35,B_36,k2_yellow_0(A_35,B_36))
      | ~ r2_yellow_0(A_35,B_36)
      | ~ m1_subset_1(k2_yellow_0(A_35,B_36),u1_struct_0(A_35))
      | ~ l1_orders_2(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_61,plain,(
    ! [A_13,B_14] :
      ( r1_lattice3(A_13,B_14,k2_yellow_0(A_13,B_14))
      | ~ r2_yellow_0(A_13,B_14)
      | ~ l1_orders_2(A_13) ) ),
    inference(resolution,[status(thm)],[c_12,c_58])).

tff(c_44,plain,(
    ! [D_32] :
      ( r1_lattice3('#skF_3','#skF_5',D_32)
      | ~ r1_lattice3('#skF_3','#skF_4',D_32)
      | ~ m1_subset_1(D_32,u1_struct_0('#skF_3')) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_48,plain,(
    ! [B_14] :
      ( r1_lattice3('#skF_3','#skF_5',k2_yellow_0('#skF_3',B_14))
      | ~ r1_lattice3('#skF_3','#skF_4',k2_yellow_0('#skF_3',B_14))
      | ~ l1_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_12,c_44])).

tff(c_51,plain,(
    ! [B_14] :
      ( r1_lattice3('#skF_3','#skF_5',k2_yellow_0('#skF_3',B_14))
      | ~ r1_lattice3('#skF_3','#skF_4',k2_yellow_0('#skF_3',B_14)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_48])).

tff(c_24,plain,(
    k2_yellow_0('#skF_3','#skF_5') != k2_yellow_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_30,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_62,plain,(
    ! [A_37,B_38] :
      ( r1_lattice3(A_37,B_38,k2_yellow_0(A_37,B_38))
      | ~ r2_yellow_0(A_37,B_38)
      | ~ l1_orders_2(A_37) ) ),
    inference(resolution,[status(thm)],[c_12,c_58])).

tff(c_36,plain,(
    ! [D_31] :
      ( r1_lattice3('#skF_3','#skF_4',D_31)
      | ~ r1_lattice3('#skF_3','#skF_5',D_31)
      | ~ m1_subset_1(D_31,u1_struct_0('#skF_3')) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_40,plain,(
    ! [B_14] :
      ( r1_lattice3('#skF_3','#skF_4',k2_yellow_0('#skF_3',B_14))
      | ~ r1_lattice3('#skF_3','#skF_5',k2_yellow_0('#skF_3',B_14))
      | ~ l1_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_12,c_36])).

tff(c_43,plain,(
    ! [B_14] :
      ( r1_lattice3('#skF_3','#skF_4',k2_yellow_0('#skF_3',B_14))
      | ~ r1_lattice3('#skF_3','#skF_5',k2_yellow_0('#skF_3',B_14)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_40])).

tff(c_66,plain,
    ( r1_lattice3('#skF_3','#skF_4',k2_yellow_0('#skF_3','#skF_5'))
    | ~ r2_yellow_0('#skF_3','#skF_5')
    | ~ l1_orders_2('#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_43])).

tff(c_69,plain,
    ( r1_lattice3('#skF_3','#skF_4',k2_yellow_0('#skF_3','#skF_5'))
    | ~ r2_yellow_0('#skF_3','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_66])).

tff(c_70,plain,(
    ~ r2_yellow_0('#skF_3','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_69])).

tff(c_123,plain,(
    ! [A_53,B_54,C_55] :
      ( r1_lattice3(A_53,B_54,'#skF_2'(A_53,B_54,C_55))
      | r1_lattice3(A_53,C_55,'#skF_2'(A_53,B_54,C_55))
      | r2_yellow_0(A_53,C_55)
      | ~ r2_yellow_0(A_53,B_54)
      | ~ l1_orders_2(A_53)
      | v2_struct_0(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_71,plain,(
    ! [A_39,B_40,C_41] :
      ( m1_subset_1('#skF_2'(A_39,B_40,C_41),u1_struct_0(A_39))
      | r2_yellow_0(A_39,C_41)
      | ~ r2_yellow_0(A_39,B_40)
      | ~ l1_orders_2(A_39)
      | v2_struct_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_32,plain,(
    ! [D_28] :
      ( r1_lattice3('#skF_3','#skF_4',D_28)
      | ~ r1_lattice3('#skF_3','#skF_5',D_28)
      | ~ m1_subset_1(D_28,u1_struct_0('#skF_3')) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_79,plain,(
    ! [B_40,C_41] :
      ( r1_lattice3('#skF_3','#skF_4','#skF_2'('#skF_3',B_40,C_41))
      | ~ r1_lattice3('#skF_3','#skF_5','#skF_2'('#skF_3',B_40,C_41))
      | r2_yellow_0('#skF_3',C_41)
      | ~ r2_yellow_0('#skF_3',B_40)
      | ~ l1_orders_2('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_71,c_32])).

tff(c_86,plain,(
    ! [B_40,C_41] :
      ( r1_lattice3('#skF_3','#skF_4','#skF_2'('#skF_3',B_40,C_41))
      | ~ r1_lattice3('#skF_3','#skF_5','#skF_2'('#skF_3',B_40,C_41))
      | r2_yellow_0('#skF_3',C_41)
      | ~ r2_yellow_0('#skF_3',B_40)
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_79])).

tff(c_87,plain,(
    ! [B_40,C_41] :
      ( r1_lattice3('#skF_3','#skF_4','#skF_2'('#skF_3',B_40,C_41))
      | ~ r1_lattice3('#skF_3','#skF_5','#skF_2'('#skF_3',B_40,C_41))
      | r2_yellow_0('#skF_3',C_41)
      | ~ r2_yellow_0('#skF_3',B_40) ) ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_86])).

tff(c_138,plain,(
    ! [B_54] :
      ( r1_lattice3('#skF_3','#skF_4','#skF_2'('#skF_3',B_54,'#skF_5'))
      | r1_lattice3('#skF_3',B_54,'#skF_2'('#skF_3',B_54,'#skF_5'))
      | r2_yellow_0('#skF_3','#skF_5')
      | ~ r2_yellow_0('#skF_3',B_54)
      | ~ l1_orders_2('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_123,c_87])).

tff(c_150,plain,(
    ! [B_54] :
      ( r1_lattice3('#skF_3','#skF_4','#skF_2'('#skF_3',B_54,'#skF_5'))
      | r1_lattice3('#skF_3',B_54,'#skF_2'('#skF_3',B_54,'#skF_5'))
      | r2_yellow_0('#skF_3','#skF_5')
      | ~ r2_yellow_0('#skF_3',B_54)
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_138])).

tff(c_151,plain,(
    ! [B_54] :
      ( r1_lattice3('#skF_3','#skF_4','#skF_2'('#skF_3',B_54,'#skF_5'))
      | r1_lattice3('#skF_3',B_54,'#skF_2'('#skF_3',B_54,'#skF_5'))
      | ~ r2_yellow_0('#skF_3',B_54) ) ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_70,c_150])).

tff(c_163,plain,
    ( ~ r2_yellow_0('#skF_3','#skF_4')
    | r1_lattice3('#skF_3','#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')) ),
    inference(factorization,[status(thm),theory(equality)],[c_151])).

tff(c_166,plain,(
    r1_lattice3('#skF_3','#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_163])).

tff(c_34,plain,(
    ! [D_28] :
      ( r1_lattice3('#skF_3','#skF_5',D_28)
      | ~ r1_lattice3('#skF_3','#skF_4',D_28)
      | ~ m1_subset_1(D_28,u1_struct_0('#skF_3')) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_75,plain,(
    ! [B_40,C_41] :
      ( r1_lattice3('#skF_3','#skF_5','#skF_2'('#skF_3',B_40,C_41))
      | ~ r1_lattice3('#skF_3','#skF_4','#skF_2'('#skF_3',B_40,C_41))
      | r2_yellow_0('#skF_3',C_41)
      | ~ r2_yellow_0('#skF_3',B_40)
      | ~ l1_orders_2('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_71,c_34])).

tff(c_82,plain,(
    ! [B_40,C_41] :
      ( r1_lattice3('#skF_3','#skF_5','#skF_2'('#skF_3',B_40,C_41))
      | ~ r1_lattice3('#skF_3','#skF_4','#skF_2'('#skF_3',B_40,C_41))
      | r2_yellow_0('#skF_3',C_41)
      | ~ r2_yellow_0('#skF_3',B_40)
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_75])).

tff(c_83,plain,(
    ! [B_40,C_41] :
      ( r1_lattice3('#skF_3','#skF_5','#skF_2'('#skF_3',B_40,C_41))
      | ~ r1_lattice3('#skF_3','#skF_4','#skF_2'('#skF_3',B_40,C_41))
      | r2_yellow_0('#skF_3',C_41)
      | ~ r2_yellow_0('#skF_3',B_40) ) ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_82])).

tff(c_95,plain,(
    ! [A_49,C_50,B_51] :
      ( ~ r1_lattice3(A_49,C_50,'#skF_2'(A_49,B_51,C_50))
      | ~ r1_lattice3(A_49,B_51,'#skF_2'(A_49,B_51,C_50))
      | r2_yellow_0(A_49,C_50)
      | ~ r2_yellow_0(A_49,B_51)
      | ~ l1_orders_2(A_49)
      | v2_struct_0(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_98,plain,(
    ! [B_40] :
      ( ~ r1_lattice3('#skF_3',B_40,'#skF_2'('#skF_3',B_40,'#skF_5'))
      | ~ l1_orders_2('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ r1_lattice3('#skF_3','#skF_4','#skF_2'('#skF_3',B_40,'#skF_5'))
      | r2_yellow_0('#skF_3','#skF_5')
      | ~ r2_yellow_0('#skF_3',B_40) ) ),
    inference(resolution,[status(thm)],[c_83,c_95])).

tff(c_101,plain,(
    ! [B_40] :
      ( ~ r1_lattice3('#skF_3',B_40,'#skF_2'('#skF_3',B_40,'#skF_5'))
      | v2_struct_0('#skF_3')
      | ~ r1_lattice3('#skF_3','#skF_4','#skF_2'('#skF_3',B_40,'#skF_5'))
      | r2_yellow_0('#skF_3','#skF_5')
      | ~ r2_yellow_0('#skF_3',B_40) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_98])).

tff(c_102,plain,(
    ! [B_40] :
      ( ~ r1_lattice3('#skF_3',B_40,'#skF_2'('#skF_3',B_40,'#skF_5'))
      | ~ r1_lattice3('#skF_3','#skF_4','#skF_2'('#skF_3',B_40,'#skF_5'))
      | ~ r2_yellow_0('#skF_3',B_40) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_30,c_101])).

tff(c_189,plain,
    ( ~ r1_lattice3('#skF_3','#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5'))
    | ~ r2_yellow_0('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_166,c_102])).

tff(c_193,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_166,c_189])).

tff(c_195,plain,(
    r2_yellow_0('#skF_3','#skF_5') ),
    inference(splitRight,[status(thm)],[c_69])).

tff(c_4,plain,(
    ! [A_1,B_8,C_9] :
      ( r1_lattice3(A_1,B_8,'#skF_1'(A_1,B_8,C_9))
      | k2_yellow_0(A_1,B_8) = C_9
      | ~ r1_lattice3(A_1,B_8,C_9)
      | ~ r2_yellow_0(A_1,B_8)
      | ~ m1_subset_1(C_9,u1_struct_0(A_1))
      | ~ l1_orders_2(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_229,plain,(
    ! [A_73,B_74,C_75] :
      ( m1_subset_1('#skF_1'(A_73,B_74,C_75),u1_struct_0(A_73))
      | k2_yellow_0(A_73,B_74) = C_75
      | ~ r1_lattice3(A_73,B_74,C_75)
      | ~ r2_yellow_0(A_73,B_74)
      | ~ m1_subset_1(C_75,u1_struct_0(A_73))
      | ~ l1_orders_2(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_237,plain,(
    ! [B_74,C_75] :
      ( r1_lattice3('#skF_3','#skF_4','#skF_1'('#skF_3',B_74,C_75))
      | ~ r1_lattice3('#skF_3','#skF_5','#skF_1'('#skF_3',B_74,C_75))
      | k2_yellow_0('#skF_3',B_74) = C_75
      | ~ r1_lattice3('#skF_3',B_74,C_75)
      | ~ r2_yellow_0('#skF_3',B_74)
      | ~ m1_subset_1(C_75,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_229,c_32])).

tff(c_344,plain,(
    ! [B_87,C_88] :
      ( r1_lattice3('#skF_3','#skF_4','#skF_1'('#skF_3',B_87,C_88))
      | ~ r1_lattice3('#skF_3','#skF_5','#skF_1'('#skF_3',B_87,C_88))
      | k2_yellow_0('#skF_3',B_87) = C_88
      | ~ r1_lattice3('#skF_3',B_87,C_88)
      | ~ r2_yellow_0('#skF_3',B_87)
      | ~ m1_subset_1(C_88,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_237])).

tff(c_348,plain,(
    ! [C_9] :
      ( r1_lattice3('#skF_3','#skF_4','#skF_1'('#skF_3','#skF_5',C_9))
      | k2_yellow_0('#skF_3','#skF_5') = C_9
      | ~ r1_lattice3('#skF_3','#skF_5',C_9)
      | ~ r2_yellow_0('#skF_3','#skF_5')
      | ~ m1_subset_1(C_9,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_4,c_344])).

tff(c_351,plain,(
    ! [C_9] :
      ( r1_lattice3('#skF_3','#skF_4','#skF_1'('#skF_3','#skF_5',C_9))
      | k2_yellow_0('#skF_3','#skF_5') = C_9
      | ~ r1_lattice3('#skF_3','#skF_5',C_9)
      | ~ m1_subset_1(C_9,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_195,c_348])).

tff(c_334,plain,(
    ! [A_81,D_82,B_83] :
      ( r1_orders_2(A_81,D_82,k2_yellow_0(A_81,B_83))
      | ~ r1_lattice3(A_81,B_83,D_82)
      | ~ m1_subset_1(D_82,u1_struct_0(A_81))
      | ~ r2_yellow_0(A_81,B_83)
      | ~ m1_subset_1(k2_yellow_0(A_81,B_83),u1_struct_0(A_81))
      | ~ l1_orders_2(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_338,plain,(
    ! [A_84,D_85,B_86] :
      ( r1_orders_2(A_84,D_85,k2_yellow_0(A_84,B_86))
      | ~ r1_lattice3(A_84,B_86,D_85)
      | ~ m1_subset_1(D_85,u1_struct_0(A_84))
      | ~ r2_yellow_0(A_84,B_86)
      | ~ l1_orders_2(A_84) ) ),
    inference(resolution,[status(thm)],[c_12,c_334])).

tff(c_2,plain,(
    ! [A_1,B_8,C_9] :
      ( ~ r1_orders_2(A_1,'#skF_1'(A_1,B_8,C_9),C_9)
      | k2_yellow_0(A_1,B_8) = C_9
      | ~ r1_lattice3(A_1,B_8,C_9)
      | ~ r2_yellow_0(A_1,B_8)
      | ~ m1_subset_1(C_9,u1_struct_0(A_1))
      | ~ l1_orders_2(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_358,plain,(
    ! [A_92,B_94,B_93] :
      ( k2_yellow_0(A_92,B_94) = k2_yellow_0(A_92,B_93)
      | ~ r1_lattice3(A_92,B_94,k2_yellow_0(A_92,B_93))
      | ~ r2_yellow_0(A_92,B_94)
      | ~ m1_subset_1(k2_yellow_0(A_92,B_93),u1_struct_0(A_92))
      | ~ r1_lattice3(A_92,B_93,'#skF_1'(A_92,B_94,k2_yellow_0(A_92,B_93)))
      | ~ m1_subset_1('#skF_1'(A_92,B_94,k2_yellow_0(A_92,B_93)),u1_struct_0(A_92))
      | ~ r2_yellow_0(A_92,B_93)
      | ~ l1_orders_2(A_92) ) ),
    inference(resolution,[status(thm)],[c_338,c_2])).

tff(c_364,plain,
    ( ~ r2_yellow_0('#skF_3','#skF_5')
    | ~ m1_subset_1('#skF_1'('#skF_3','#skF_5',k2_yellow_0('#skF_3','#skF_4')),u1_struct_0('#skF_3'))
    | ~ r2_yellow_0('#skF_3','#skF_4')
    | ~ l1_orders_2('#skF_3')
    | k2_yellow_0('#skF_3','#skF_5') = k2_yellow_0('#skF_3','#skF_4')
    | ~ r1_lattice3('#skF_3','#skF_5',k2_yellow_0('#skF_3','#skF_4'))
    | ~ m1_subset_1(k2_yellow_0('#skF_3','#skF_4'),u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_351,c_358])).

tff(c_373,plain,
    ( ~ m1_subset_1('#skF_1'('#skF_3','#skF_5',k2_yellow_0('#skF_3','#skF_4')),u1_struct_0('#skF_3'))
    | k2_yellow_0('#skF_3','#skF_5') = k2_yellow_0('#skF_3','#skF_4')
    | ~ r1_lattice3('#skF_3','#skF_5',k2_yellow_0('#skF_3','#skF_4'))
    | ~ m1_subset_1(k2_yellow_0('#skF_3','#skF_4'),u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_195,c_364])).

tff(c_374,plain,
    ( ~ m1_subset_1('#skF_1'('#skF_3','#skF_5',k2_yellow_0('#skF_3','#skF_4')),u1_struct_0('#skF_3'))
    | ~ r1_lattice3('#skF_3','#skF_5',k2_yellow_0('#skF_3','#skF_4'))
    | ~ m1_subset_1(k2_yellow_0('#skF_3','#skF_4'),u1_struct_0('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_373])).

tff(c_377,plain,(
    ~ m1_subset_1(k2_yellow_0('#skF_3','#skF_4'),u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_374])).

tff(c_380,plain,(
    ~ l1_orders_2('#skF_3') ),
    inference(resolution,[status(thm)],[c_12,c_377])).

tff(c_384,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_380])).

tff(c_386,plain,(
    m1_subset_1(k2_yellow_0('#skF_3','#skF_4'),u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_374])).

tff(c_6,plain,(
    ! [A_1,B_8,C_9] :
      ( m1_subset_1('#skF_1'(A_1,B_8,C_9),u1_struct_0(A_1))
      | k2_yellow_0(A_1,B_8) = C_9
      | ~ r1_lattice3(A_1,B_8,C_9)
      | ~ r2_yellow_0(A_1,B_8)
      | ~ m1_subset_1(C_9,u1_struct_0(A_1))
      | ~ l1_orders_2(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_385,plain,
    ( ~ r1_lattice3('#skF_3','#skF_5',k2_yellow_0('#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_1'('#skF_3','#skF_5',k2_yellow_0('#skF_3','#skF_4')),u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_374])).

tff(c_395,plain,(
    ~ m1_subset_1('#skF_1'('#skF_3','#skF_5',k2_yellow_0('#skF_3','#skF_4')),u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_385])).

tff(c_398,plain,
    ( k2_yellow_0('#skF_3','#skF_5') = k2_yellow_0('#skF_3','#skF_4')
    | ~ r1_lattice3('#skF_3','#skF_5',k2_yellow_0('#skF_3','#skF_4'))
    | ~ r2_yellow_0('#skF_3','#skF_5')
    | ~ m1_subset_1(k2_yellow_0('#skF_3','#skF_4'),u1_struct_0('#skF_3'))
    | ~ l1_orders_2('#skF_3') ),
    inference(resolution,[status(thm)],[c_6,c_395])).

tff(c_401,plain,
    ( k2_yellow_0('#skF_3','#skF_5') = k2_yellow_0('#skF_3','#skF_4')
    | ~ r1_lattice3('#skF_3','#skF_5',k2_yellow_0('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_386,c_195,c_398])).

tff(c_402,plain,(
    ~ r1_lattice3('#skF_3','#skF_5',k2_yellow_0('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_401])).

tff(c_432,plain,(
    ~ r1_lattice3('#skF_3','#skF_4',k2_yellow_0('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_51,c_402])).

tff(c_435,plain,
    ( ~ r2_yellow_0('#skF_3','#skF_4')
    | ~ l1_orders_2('#skF_3') ),
    inference(resolution,[status(thm)],[c_61,c_432])).

tff(c_439,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_435])).

tff(c_440,plain,(
    ~ r1_lattice3('#skF_3','#skF_5',k2_yellow_0('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_385])).

tff(c_445,plain,(
    ~ r1_lattice3('#skF_3','#skF_4',k2_yellow_0('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_51,c_440])).

tff(c_448,plain,
    ( ~ r2_yellow_0('#skF_3','#skF_4')
    | ~ l1_orders_2('#skF_3') ),
    inference(resolution,[status(thm)],[c_61,c_445])).

tff(c_452,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_448])).

%------------------------------------------------------------------------------
