%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1139+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:28 EST 2020

% Result     : Theorem 1.73s
% Output     : CNFRefutation 1.73s
% Verified   : 
% Statistics : Number of formulae       :   33 (  59 expanded)
%              Number of leaves         :   15 (  31 expanded)
%              Depth                    :    8
%              Number of atoms          :   61 ( 171 expanded)
%              Number of equality atoms :    5 (   7 expanded)
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
               => ~ ( r2_orders_2(A,B,C)
                    & r2_orders_2(A,C,B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_orders_2)).

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

tff(c_20,plain,(
    v5_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_16,plain,(
    m1_subset_1('#skF_2',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_10,plain,(
    r2_orders_2('#skF_1','#skF_3','#skF_2') ),
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

tff(c_29,plain,(
    r1_orders_2('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_14,c_16,c_24])).

tff(c_12,plain,(
    r2_orders_2('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_26,plain,
    ( r1_orders_2('#skF_1','#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_1'))
    | ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1'))
    | ~ l1_orders_2('#skF_1') ),
    inference(resolution,[status(thm)],[c_12,c_22])).

tff(c_32,plain,(
    r1_orders_2('#skF_1','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_16,c_14,c_26])).

tff(c_68,plain,(
    ! [C_29,B_30,A_31] :
      ( C_29 = B_30
      | ~ r1_orders_2(A_31,C_29,B_30)
      | ~ r1_orders_2(A_31,B_30,C_29)
      | ~ m1_subset_1(C_29,u1_struct_0(A_31))
      | ~ m1_subset_1(B_30,u1_struct_0(A_31))
      | ~ l1_orders_2(A_31)
      | ~ v5_orders_2(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_70,plain,
    ( '#skF_2' = '#skF_3'
    | ~ r1_orders_2('#skF_1','#skF_3','#skF_2')
    | ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1'))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_1'))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_68])).

tff(c_75,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_14,c_16,c_29,c_70])).

tff(c_84,plain,(
    r2_orders_2('#skF_1','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_12])).

tff(c_4,plain,(
    ! [A_1,C_7] :
      ( ~ r2_orders_2(A_1,C_7,C_7)
      | ~ m1_subset_1(C_7,u1_struct_0(A_1))
      | ~ l1_orders_2(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_100,plain,
    ( ~ m1_subset_1('#skF_3',u1_struct_0('#skF_1'))
    | ~ l1_orders_2('#skF_1') ),
    inference(resolution,[status(thm)],[c_84,c_4])).

tff(c_107,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_14,c_100])).

%------------------------------------------------------------------------------
