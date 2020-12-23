%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1579+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:06 EST 2020

% Result     : Theorem 1.87s
% Output     : CNFRefutation 1.87s
% Verified   : 
% Statistics : Number of formulae       :   36 (  58 expanded)
%              Number of leaves         :   15 (  29 expanded)
%              Depth                    :    7
%              Number of atoms          :   67 ( 176 expanded)
%              Number of equality atoms :   15 (  46 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_yellow_0 > m1_yellow_0 > l1_orders_2 > k1_toler_1 > g1_orders_2 > #nlpp > u1_struct_0 > u1_orders_2 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(v4_yellow_0,type,(
    v4_yellow_0: ( $i * $i ) > $o )).

tff(k1_toler_1,type,(
    k1_toler_1: ( $i * $i ) > $i )).

tff(g1_orders_2,type,(
    g1_orders_2: ( $i * $i ) > $i )).

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

tff(f_50,negated_conjecture,(
    ~ ! [A] :
        ( l1_orders_2(A)
       => ! [B] :
            ( ( v4_yellow_0(B,A)
              & m1_yellow_0(B,A) )
           => ! [C] :
                ( ( v4_yellow_0(C,A)
                  & m1_yellow_0(C,A) )
               => ( u1_struct_0(B) = u1_struct_0(C)
                 => g1_orders_2(u1_struct_0(B),u1_orders_2(B)) = g1_orders_2(u1_struct_0(C),u1_orders_2(C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_yellow_0)).

tff(f_33,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( m1_yellow_0(B,A)
         => ( v4_yellow_0(B,A)
          <=> u1_orders_2(B) = k1_toler_1(u1_orders_2(A),u1_struct_0(B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d14_yellow_0)).

tff(c_18,plain,(
    l1_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_14,plain,(
    m1_yellow_0('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_10,plain,(
    m1_yellow_0('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_12,plain,(
    v4_yellow_0('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_16,plain,(
    v4_yellow_0('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_4,plain,(
    ! [A_1,B_3] :
      ( k1_toler_1(u1_orders_2(A_1),u1_struct_0(B_3)) = u1_orders_2(B_3)
      | ~ v4_yellow_0(B_3,A_1)
      | ~ m1_yellow_0(B_3,A_1)
      | ~ l1_orders_2(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_8,plain,(
    u1_struct_0('#skF_2') = u1_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_24,plain,(
    ! [B_8,A_9] :
      ( v4_yellow_0(B_8,A_9)
      | k1_toler_1(u1_orders_2(A_9),u1_struct_0(B_8)) != u1_orders_2(B_8)
      | ~ m1_yellow_0(B_8,A_9)
      | ~ l1_orders_2(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_44,plain,(
    ! [A_12] :
      ( v4_yellow_0('#skF_2',A_12)
      | k1_toler_1(u1_orders_2(A_12),u1_struct_0('#skF_3')) != u1_orders_2('#skF_2')
      | ~ m1_yellow_0('#skF_2',A_12)
      | ~ l1_orders_2(A_12) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_24])).

tff(c_48,plain,(
    ! [A_1] :
      ( v4_yellow_0('#skF_2',A_1)
      | u1_orders_2('#skF_2') != u1_orders_2('#skF_3')
      | ~ m1_yellow_0('#skF_2',A_1)
      | ~ l1_orders_2(A_1)
      | ~ v4_yellow_0('#skF_3',A_1)
      | ~ m1_yellow_0('#skF_3',A_1)
      | ~ l1_orders_2(A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_44])).

tff(c_72,plain,(
    u1_orders_2('#skF_2') != u1_orders_2('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_28,plain,(
    ! [A_10,B_11] :
      ( k1_toler_1(u1_orders_2(A_10),u1_struct_0(B_11)) = u1_orders_2(B_11)
      | ~ v4_yellow_0(B_11,A_10)
      | ~ m1_yellow_0(B_11,A_10)
      | ~ l1_orders_2(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_49,plain,(
    ! [A_13] :
      ( k1_toler_1(u1_orders_2(A_13),u1_struct_0('#skF_3')) = u1_orders_2('#skF_2')
      | ~ v4_yellow_0('#skF_2',A_13)
      | ~ m1_yellow_0('#skF_2',A_13)
      | ~ l1_orders_2(A_13) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_28])).

tff(c_58,plain,(
    ! [A_13] :
      ( u1_orders_2('#skF_2') = u1_orders_2('#skF_3')
      | ~ v4_yellow_0('#skF_3',A_13)
      | ~ m1_yellow_0('#skF_3',A_13)
      | ~ l1_orders_2(A_13)
      | ~ v4_yellow_0('#skF_2',A_13)
      | ~ m1_yellow_0('#skF_2',A_13)
      | ~ l1_orders_2(A_13) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_49,c_4])).

tff(c_74,plain,(
    ! [A_14] :
      ( ~ v4_yellow_0('#skF_3',A_14)
      | ~ m1_yellow_0('#skF_3',A_14)
      | ~ l1_orders_2(A_14)
      | ~ v4_yellow_0('#skF_2',A_14)
      | ~ m1_yellow_0('#skF_2',A_14)
      | ~ l1_orders_2(A_14) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_58])).

tff(c_77,plain,
    ( ~ v4_yellow_0('#skF_3','#skF_1')
    | ~ m1_yellow_0('#skF_3','#skF_1')
    | ~ m1_yellow_0('#skF_2','#skF_1')
    | ~ l1_orders_2('#skF_1') ),
    inference(resolution,[status(thm)],[c_16,c_74])).

tff(c_81,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_14,c_10,c_12,c_77])).

tff(c_83,plain,(
    u1_orders_2('#skF_2') = u1_orders_2('#skF_3') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_6,plain,(
    g1_orders_2(u1_struct_0('#skF_2'),u1_orders_2('#skF_2')) != g1_orders_2(u1_struct_0('#skF_3'),u1_orders_2('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_19,plain,(
    g1_orders_2(u1_struct_0('#skF_3'),u1_orders_2('#skF_2')) != g1_orders_2(u1_struct_0('#skF_3'),u1_orders_2('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_6])).

tff(c_88,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_19])).

%------------------------------------------------------------------------------
