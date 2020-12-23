%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1141+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:29 EST 2020

% Result     : Theorem 1.88s
% Output     : CNFRefutation 1.88s
% Verified   : 
% Statistics : Number of formulae       :   39 (  80 expanded)
%              Number of leaves         :   15 (  37 expanded)
%              Depth                    :    9
%              Number of atoms          :   79 ( 245 expanded)
%              Number of equality atoms :   12 (  20 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_orders_2 > r1_orders_2 > m1_subset_1 > v5_orders_2 > l1_orders_2 > #nlpp > u1_struct_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(r2_orders_2,type,(
    r2_orders_2: ( $i * $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_71,negated_conjecture,(
    ~ ! [A] :
        ( ( v5_orders_2(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => ~ ( r1_orders_2(A,B,C)
                    & r2_orders_2(A,C,B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_orders_2)).

tff(f_39,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( r2_orders_2(A,B,C)
              <=> ( r1_orders_2(A,B,C)
                  & B != C ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_orders_2)).

tff(f_55,axiom,(
    ! [A] :
      ( ( v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( ( r1_orders_2(A,B,C)
                  & r1_orders_2(A,C,B) )
               => B = C ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_orders_2)).

tff(c_18,plain,(
    l1_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_14,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_12,plain,(
    r1_orders_2('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_16,plain,(
    m1_subset_1('#skF_2',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_28,plain,(
    ! [A_24,B_25,C_26] :
      ( r2_orders_2(A_24,B_25,C_26)
      | C_26 = B_25
      | ~ r1_orders_2(A_24,B_25,C_26)
      | ~ m1_subset_1(C_26,u1_struct_0(A_24))
      | ~ m1_subset_1(B_25,u1_struct_0(A_24))
      | ~ l1_orders_2(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_32,plain,(
    ! [B_25] :
      ( r2_orders_2('#skF_1',B_25,'#skF_3')
      | B_25 = '#skF_3'
      | ~ r1_orders_2('#skF_1',B_25,'#skF_3')
      | ~ m1_subset_1(B_25,u1_struct_0('#skF_1'))
      | ~ l1_orders_2('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_14,c_28])).

tff(c_51,plain,(
    ! [B_28] :
      ( r2_orders_2('#skF_1',B_28,'#skF_3')
      | B_28 = '#skF_3'
      | ~ r1_orders_2('#skF_1',B_28,'#skF_3')
      | ~ m1_subset_1(B_28,u1_struct_0('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_32])).

tff(c_54,plain,
    ( r2_orders_2('#skF_1','#skF_2','#skF_3')
    | '#skF_2' = '#skF_3'
    | ~ r1_orders_2('#skF_1','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_16,c_51])).

tff(c_60,plain,
    ( r2_orders_2('#skF_1','#skF_2','#skF_3')
    | '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_54])).

tff(c_63,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_10,plain,(
    r2_orders_2('#skF_1','#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_66,plain,(
    r2_orders_2('#skF_1','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_10])).

tff(c_4,plain,(
    ! [A_1,C_7] :
      ( ~ r2_orders_2(A_1,C_7,C_7)
      | ~ m1_subset_1(C_7,u1_struct_0(A_1))
      | ~ l1_orders_2(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_85,plain,
    ( ~ m1_subset_1('#skF_3',u1_struct_0('#skF_1'))
    | ~ l1_orders_2('#skF_1') ),
    inference(resolution,[status(thm)],[c_66,c_4])).

tff(c_92,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_14,c_85])).

tff(c_94,plain,(
    '#skF_2' != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_20,plain,(
    v5_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_22,plain,(
    ! [A_21,B_22,C_23] :
      ( r1_orders_2(A_21,B_22,C_23)
      | ~ r2_orders_2(A_21,B_22,C_23)
      | ~ m1_subset_1(C_23,u1_struct_0(A_21))
      | ~ m1_subset_1(B_22,u1_struct_0(A_21))
      | ~ l1_orders_2(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_24,plain,
    ( r1_orders_2('#skF_1','#skF_3','#skF_2')
    | ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1'))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_1'))
    | ~ l1_orders_2('#skF_1') ),
    inference(resolution,[status(thm)],[c_10,c_22])).

tff(c_27,plain,(
    r1_orders_2('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_14,c_16,c_24])).

tff(c_100,plain,(
    ! [C_32,B_33,A_34] :
      ( C_32 = B_33
      | ~ r1_orders_2(A_34,C_32,B_33)
      | ~ r1_orders_2(A_34,B_33,C_32)
      | ~ m1_subset_1(C_32,u1_struct_0(A_34))
      | ~ m1_subset_1(B_33,u1_struct_0(A_34))
      | ~ l1_orders_2(A_34)
      | ~ v5_orders_2(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_102,plain,
    ( '#skF_2' = '#skF_3'
    | ~ r1_orders_2('#skF_1','#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_1'))
    | ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1'))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1') ),
    inference(resolution,[status(thm)],[c_27,c_100])).

tff(c_107,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_16,c_14,c_12,c_102])).

tff(c_109,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_107])).

%------------------------------------------------------------------------------
