%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1922+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:41 EST 2020

% Result     : Theorem 1.60s
% Output     : CNFRefutation 1.80s
% Verified   : 
% Statistics : Number of formulae       :   54 (  78 expanded)
%              Number of leaves         :   25 (  42 expanded)
%              Depth                    :    7
%              Number of atoms          :   98 ( 292 expanded)
%              Number of equality atoms :    7 (  43 expanded)
%              Maximal formula depth    :   19 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_orders_2 > m1_yellow_6 > m1_yellow_0 > m1_subset_1 > l1_waybel_0 > l1_struct_0 > l1_orders_2 > k2_partfun1 > u1_waybel_0 > #nlpp > u1_struct_0 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(m1_yellow_0,type,(
    m1_yellow_0: ( $i * $i ) > $o )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff(u1_waybel_0,type,(
    u1_waybel_0: ( $i * $i ) > $i )).

tff(m1_yellow_6,type,(
    m1_yellow_6: ( $i * $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(l1_waybel_0,type,(
    l1_waybel_0: ( $i * $i ) > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_partfun1,type,(
    k2_partfun1: ( $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_108,negated_conjecture,(
    ~ ! [A] :
        ( l1_struct_0(A)
       => ! [B] :
            ( l1_waybel_0(B,A)
           => ! [C] :
                ( m1_yellow_6(C,A,B)
               => ! [D] :
                    ( m1_subset_1(D,u1_struct_0(B))
                   => ! [E] :
                        ( m1_subset_1(E,u1_struct_0(B))
                       => ! [F] :
                            ( m1_subset_1(F,u1_struct_0(C))
                           => ! [G] :
                                ( m1_subset_1(G,u1_struct_0(C))
                               => ( ( D = F
                                    & E = G
                                    & r1_orders_2(C,F,G) )
                                 => r1_orders_2(B,D,E) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_yellow_6)).

tff(f_45,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ! [B] :
          ( l1_waybel_0(B,A)
         => l1_orders_2(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_waybel_0)).

tff(f_54,axiom,(
    ! [A,B] :
      ( ( l1_struct_0(A)
        & l1_waybel_0(B,A) )
     => ! [C] :
          ( m1_yellow_6(C,A,B)
         => l1_waybel_0(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_yellow_6)).

tff(f_38,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ! [B] :
          ( l1_waybel_0(B,A)
         => ! [C] :
              ( l1_waybel_0(C,A)
             => ( m1_yellow_6(C,A,B)
              <=> ( m1_yellow_0(C,B)
                  & u1_waybel_0(A,C) = k2_partfun1(u1_struct_0(B),u1_struct_0(A),u1_waybel_0(A,B),u1_struct_0(C)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_yellow_6)).

tff(f_79,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( m1_yellow_0(B,A)
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ! [D] :
                  ( m1_subset_1(D,u1_struct_0(A))
                 => ! [E] :
                      ( m1_subset_1(E,u1_struct_0(B))
                     => ! [F] :
                          ( m1_subset_1(F,u1_struct_0(B))
                         => ( ( E = C
                              & F = D
                              & r1_orders_2(B,E,F) )
                           => r1_orders_2(A,C,D) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_yellow_0)).

tff(c_14,plain,(
    ~ r1_orders_2('#skF_2','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_34,plain,(
    l1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_32,plain,(
    l1_waybel_0('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_46,plain,(
    ! [B_198,A_199] :
      ( l1_orders_2(B_198)
      | ~ l1_waybel_0(B_198,A_199)
      | ~ l1_struct_0(A_199) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_49,plain,
    ( l1_orders_2('#skF_2')
    | ~ l1_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_46])).

tff(c_52,plain,(
    l1_orders_2('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_49])).

tff(c_30,plain,(
    m1_yellow_6('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_53,plain,(
    ! [C_200,A_201,B_202] :
      ( l1_waybel_0(C_200,A_201)
      | ~ m1_yellow_6(C_200,A_201,B_202)
      | ~ l1_waybel_0(B_202,A_201)
      | ~ l1_struct_0(A_201) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_56,plain,
    ( l1_waybel_0('#skF_3','#skF_1')
    | ~ l1_waybel_0('#skF_2','#skF_1')
    | ~ l1_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_53])).

tff(c_59,plain,(
    l1_waybel_0('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_56])).

tff(c_66,plain,(
    ! [C_203,B_204,A_205] :
      ( m1_yellow_0(C_203,B_204)
      | ~ m1_yellow_6(C_203,A_205,B_204)
      | ~ l1_waybel_0(C_203,A_205)
      | ~ l1_waybel_0(B_204,A_205)
      | ~ l1_struct_0(A_205) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_69,plain,
    ( m1_yellow_0('#skF_3','#skF_2')
    | ~ l1_waybel_0('#skF_3','#skF_1')
    | ~ l1_waybel_0('#skF_2','#skF_1')
    | ~ l1_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_66])).

tff(c_72,plain,(
    m1_yellow_0('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_59,c_69])).

tff(c_28,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_26,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_20,plain,(
    '#skF_6' = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_24,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_35,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_24])).

tff(c_18,plain,(
    '#skF_7' = '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_22,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_36,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_22])).

tff(c_16,plain,(
    r1_orders_2('#skF_3','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_37,plain,(
    r1_orders_2('#skF_3','#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_16])).

tff(c_87,plain,(
    ! [A_212,E_213,F_214,B_215] :
      ( r1_orders_2(A_212,E_213,F_214)
      | ~ r1_orders_2(B_215,E_213,F_214)
      | ~ m1_subset_1(F_214,u1_struct_0(B_215))
      | ~ m1_subset_1(E_213,u1_struct_0(B_215))
      | ~ m1_subset_1(F_214,u1_struct_0(A_212))
      | ~ m1_subset_1(E_213,u1_struct_0(A_212))
      | ~ m1_yellow_0(B_215,A_212)
      | ~ l1_orders_2(A_212) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_89,plain,(
    ! [A_212] :
      ( r1_orders_2(A_212,'#skF_4','#skF_5')
      | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
      | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
      | ~ m1_subset_1('#skF_5',u1_struct_0(A_212))
      | ~ m1_subset_1('#skF_4',u1_struct_0(A_212))
      | ~ m1_yellow_0('#skF_3',A_212)
      | ~ l1_orders_2(A_212) ) ),
    inference(resolution,[status(thm)],[c_37,c_87])).

tff(c_93,plain,(
    ! [A_216] :
      ( r1_orders_2(A_216,'#skF_4','#skF_5')
      | ~ m1_subset_1('#skF_5',u1_struct_0(A_216))
      | ~ m1_subset_1('#skF_4',u1_struct_0(A_216))
      | ~ m1_yellow_0('#skF_3',A_216)
      | ~ l1_orders_2(A_216) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_35,c_36,c_89])).

tff(c_96,plain,
    ( r1_orders_2('#skF_2','#skF_4','#skF_5')
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2'))
    | ~ m1_yellow_0('#skF_3','#skF_2')
    | ~ l1_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_93])).

tff(c_102,plain,(
    r1_orders_2('#skF_2','#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_72,c_28,c_96])).

tff(c_104,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14,c_102])).

%------------------------------------------------------------------------------
