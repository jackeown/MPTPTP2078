%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT2000+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:46 EST 2020

% Result     : Theorem 2.43s
% Output     : CNFRefutation 2.43s
% Verified   : 
% Statistics : Number of formulae       :   57 (  72 expanded)
%              Number of leaves         :   29 (  44 expanded)
%              Depth                    :   11
%              Number of atoms          :  220 ( 416 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   21 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_orders_2 > r1_waybel_3 > v5_waybel_7 > v5_waybel_6 > v4_waybel_7 > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_waybel_3 > v3_orders_2 > v2_lattice3 > v1_yellow_0 > v1_lattice3 > l1_orders_2 > k12_lattice3 > #nlpp > u1_struct_0 > k1_waybel_4 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(r3_orders_2,type,(
    r3_orders_2: ( $i * $i * $i ) > $o )).

tff(v5_waybel_6,type,(
    v5_waybel_6: ( $i * $i ) > $o )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(v3_waybel_3,type,(
    v3_waybel_3: $i > $o )).

tff(k1_waybel_4,type,(
    k1_waybel_4: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(v1_lattice3,type,(
    v1_lattice3: $i > $o )).

tff(v5_waybel_7,type,(
    v5_waybel_7: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k12_lattice3,type,(
    k12_lattice3: ( $i * $i * $i ) > $i )).

tff(v4_waybel_7,type,(
    v4_waybel_7: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v2_lattice3,type,(
    v2_lattice3: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(r1_waybel_3,type,(
    r1_waybel_3: ( $i * $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(v1_yellow_0,type,(
    v1_yellow_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_128,negated_conjecture,(
    ~ ! [A] :
        ( ( v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & v1_yellow_0(A)
          & v1_lattice3(A)
          & v2_lattice3(A)
          & v3_waybel_3(A)
          & l1_orders_2(A) )
       => ( v5_waybel_7(k1_waybel_4(A),A)
         => ! [B] :
              ( m1_subset_1(B,u1_struct_0(A))
             => ( v4_waybel_7(B,A)
               => v5_waybel_6(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_waybel_7)).

tff(f_64,axiom,(
    ! [A] :
      ( ( v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & v1_yellow_0(A)
        & v1_lattice3(A)
        & v2_lattice3(A)
        & v3_waybel_3(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ~ ( v5_waybel_7(k1_waybel_4(A),A)
              & ! [C] :
                  ( m1_subset_1(C,u1_struct_0(A))
                 => ! [D] :
                      ( m1_subset_1(D,u1_struct_0(A))
                     => ~ ( r1_waybel_3(A,k12_lattice3(A,C,D),B)
                          & ~ r3_orders_2(A,C,B)
                          & ~ r3_orders_2(A,D,B) ) ) )
              & ~ v5_waybel_6(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l57_waybel_7)).

tff(f_102,axiom,(
    ! [A] :
      ( ( v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & v1_yellow_0(A)
        & v1_lattice3(A)
        & v2_lattice3(A)
        & v3_waybel_3(A)
        & l1_orders_2(A) )
     => ( v5_waybel_7(k1_waybel_4(A),A)
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ( v4_waybel_7(B,A)
            <=> ! [C] :
                  ( m1_subset_1(C,u1_struct_0(A))
                 => ! [D] :
                      ( m1_subset_1(D,u1_struct_0(A))
                     => ~ ( r1_waybel_3(A,k12_lattice3(A,C,D),B)
                          & ~ r3_orders_2(A,C,B)
                          & ~ r3_orders_2(A,D,B) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_waybel_7)).

tff(c_24,plain,(
    ~ v5_waybel_6('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_26,plain,(
    v4_waybel_7('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_28,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_46,plain,(
    v3_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_44,plain,(
    v4_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_42,plain,(
    v5_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_40,plain,(
    v1_yellow_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_38,plain,(
    v1_lattice3('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_36,plain,(
    v2_lattice3('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_34,plain,(
    v3_waybel_3('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_32,plain,(
    l1_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_30,plain,(
    v5_waybel_7(k1_waybel_4('#skF_5'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_10,plain,(
    ! [A_1,B_9] :
      ( m1_subset_1('#skF_1'(A_1,B_9),u1_struct_0(A_1))
      | v5_waybel_6(B_9,A_1)
      | ~ v5_waybel_7(k1_waybel_4(A_1),A_1)
      | ~ m1_subset_1(B_9,u1_struct_0(A_1))
      | ~ l1_orders_2(A_1)
      | ~ v3_waybel_3(A_1)
      | ~ v2_lattice3(A_1)
      | ~ v1_lattice3(A_1)
      | ~ v1_yellow_0(A_1)
      | ~ v5_orders_2(A_1)
      | ~ v4_orders_2(A_1)
      | ~ v3_orders_2(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_8,plain,(
    ! [A_1,B_9] :
      ( m1_subset_1('#skF_2'(A_1,B_9),u1_struct_0(A_1))
      | v5_waybel_6(B_9,A_1)
      | ~ v5_waybel_7(k1_waybel_4(A_1),A_1)
      | ~ m1_subset_1(B_9,u1_struct_0(A_1))
      | ~ l1_orders_2(A_1)
      | ~ v3_waybel_3(A_1)
      | ~ v2_lattice3(A_1)
      | ~ v1_lattice3(A_1)
      | ~ v1_yellow_0(A_1)
      | ~ v5_orders_2(A_1)
      | ~ v4_orders_2(A_1)
      | ~ v3_orders_2(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_6,plain,(
    ! [A_1,B_9] :
      ( r1_waybel_3(A_1,k12_lattice3(A_1,'#skF_1'(A_1,B_9),'#skF_2'(A_1,B_9)),B_9)
      | v5_waybel_6(B_9,A_1)
      | ~ v5_waybel_7(k1_waybel_4(A_1),A_1)
      | ~ m1_subset_1(B_9,u1_struct_0(A_1))
      | ~ l1_orders_2(A_1)
      | ~ v3_waybel_3(A_1)
      | ~ v2_lattice3(A_1)
      | ~ v1_lattice3(A_1)
      | ~ v1_yellow_0(A_1)
      | ~ v5_orders_2(A_1)
      | ~ v4_orders_2(A_1)
      | ~ v3_orders_2(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_57,plain,(
    ! [A_60,D_61,B_62,C_63] :
      ( r3_orders_2(A_60,D_61,B_62)
      | r3_orders_2(A_60,C_63,B_62)
      | ~ r1_waybel_3(A_60,k12_lattice3(A_60,C_63,D_61),B_62)
      | ~ m1_subset_1(D_61,u1_struct_0(A_60))
      | ~ m1_subset_1(C_63,u1_struct_0(A_60))
      | ~ v4_waybel_7(B_62,A_60)
      | ~ m1_subset_1(B_62,u1_struct_0(A_60))
      | ~ v5_waybel_7(k1_waybel_4(A_60),A_60)
      | ~ l1_orders_2(A_60)
      | ~ v3_waybel_3(A_60)
      | ~ v2_lattice3(A_60)
      | ~ v1_lattice3(A_60)
      | ~ v1_yellow_0(A_60)
      | ~ v5_orders_2(A_60)
      | ~ v4_orders_2(A_60)
      | ~ v3_orders_2(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_66,plain,(
    ! [A_64,B_65] :
      ( r3_orders_2(A_64,'#skF_2'(A_64,B_65),B_65)
      | r3_orders_2(A_64,'#skF_1'(A_64,B_65),B_65)
      | ~ m1_subset_1('#skF_2'(A_64,B_65),u1_struct_0(A_64))
      | ~ m1_subset_1('#skF_1'(A_64,B_65),u1_struct_0(A_64))
      | ~ v4_waybel_7(B_65,A_64)
      | v5_waybel_6(B_65,A_64)
      | ~ v5_waybel_7(k1_waybel_4(A_64),A_64)
      | ~ m1_subset_1(B_65,u1_struct_0(A_64))
      | ~ l1_orders_2(A_64)
      | ~ v3_waybel_3(A_64)
      | ~ v2_lattice3(A_64)
      | ~ v1_lattice3(A_64)
      | ~ v1_yellow_0(A_64)
      | ~ v5_orders_2(A_64)
      | ~ v4_orders_2(A_64)
      | ~ v3_orders_2(A_64) ) ),
    inference(resolution,[status(thm)],[c_6,c_57])).

tff(c_70,plain,(
    ! [A_66,B_67] :
      ( r3_orders_2(A_66,'#skF_2'(A_66,B_67),B_67)
      | r3_orders_2(A_66,'#skF_1'(A_66,B_67),B_67)
      | ~ m1_subset_1('#skF_1'(A_66,B_67),u1_struct_0(A_66))
      | ~ v4_waybel_7(B_67,A_66)
      | v5_waybel_6(B_67,A_66)
      | ~ v5_waybel_7(k1_waybel_4(A_66),A_66)
      | ~ m1_subset_1(B_67,u1_struct_0(A_66))
      | ~ l1_orders_2(A_66)
      | ~ v3_waybel_3(A_66)
      | ~ v2_lattice3(A_66)
      | ~ v1_lattice3(A_66)
      | ~ v1_yellow_0(A_66)
      | ~ v5_orders_2(A_66)
      | ~ v4_orders_2(A_66)
      | ~ v3_orders_2(A_66) ) ),
    inference(resolution,[status(thm)],[c_8,c_66])).

tff(c_74,plain,(
    ! [A_68,B_69] :
      ( r3_orders_2(A_68,'#skF_2'(A_68,B_69),B_69)
      | r3_orders_2(A_68,'#skF_1'(A_68,B_69),B_69)
      | ~ v4_waybel_7(B_69,A_68)
      | v5_waybel_6(B_69,A_68)
      | ~ v5_waybel_7(k1_waybel_4(A_68),A_68)
      | ~ m1_subset_1(B_69,u1_struct_0(A_68))
      | ~ l1_orders_2(A_68)
      | ~ v3_waybel_3(A_68)
      | ~ v2_lattice3(A_68)
      | ~ v1_lattice3(A_68)
      | ~ v1_yellow_0(A_68)
      | ~ v5_orders_2(A_68)
      | ~ v4_orders_2(A_68)
      | ~ v3_orders_2(A_68) ) ),
    inference(resolution,[status(thm)],[c_10,c_70])).

tff(c_2,plain,(
    ! [A_1,B_9] :
      ( ~ r3_orders_2(A_1,'#skF_2'(A_1,B_9),B_9)
      | v5_waybel_6(B_9,A_1)
      | ~ v5_waybel_7(k1_waybel_4(A_1),A_1)
      | ~ m1_subset_1(B_9,u1_struct_0(A_1))
      | ~ l1_orders_2(A_1)
      | ~ v3_waybel_3(A_1)
      | ~ v2_lattice3(A_1)
      | ~ v1_lattice3(A_1)
      | ~ v1_yellow_0(A_1)
      | ~ v5_orders_2(A_1)
      | ~ v4_orders_2(A_1)
      | ~ v3_orders_2(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_79,plain,(
    ! [A_70,B_71] :
      ( r3_orders_2(A_70,'#skF_1'(A_70,B_71),B_71)
      | ~ v4_waybel_7(B_71,A_70)
      | v5_waybel_6(B_71,A_70)
      | ~ v5_waybel_7(k1_waybel_4(A_70),A_70)
      | ~ m1_subset_1(B_71,u1_struct_0(A_70))
      | ~ l1_orders_2(A_70)
      | ~ v3_waybel_3(A_70)
      | ~ v2_lattice3(A_70)
      | ~ v1_lattice3(A_70)
      | ~ v1_yellow_0(A_70)
      | ~ v5_orders_2(A_70)
      | ~ v4_orders_2(A_70)
      | ~ v3_orders_2(A_70) ) ),
    inference(resolution,[status(thm)],[c_74,c_2])).

tff(c_4,plain,(
    ! [A_1,B_9] :
      ( ~ r3_orders_2(A_1,'#skF_1'(A_1,B_9),B_9)
      | v5_waybel_6(B_9,A_1)
      | ~ v5_waybel_7(k1_waybel_4(A_1),A_1)
      | ~ m1_subset_1(B_9,u1_struct_0(A_1))
      | ~ l1_orders_2(A_1)
      | ~ v3_waybel_3(A_1)
      | ~ v2_lattice3(A_1)
      | ~ v1_lattice3(A_1)
      | ~ v1_yellow_0(A_1)
      | ~ v5_orders_2(A_1)
      | ~ v4_orders_2(A_1)
      | ~ v3_orders_2(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_84,plain,(
    ! [B_72,A_73] :
      ( ~ v4_waybel_7(B_72,A_73)
      | v5_waybel_6(B_72,A_73)
      | ~ v5_waybel_7(k1_waybel_4(A_73),A_73)
      | ~ m1_subset_1(B_72,u1_struct_0(A_73))
      | ~ l1_orders_2(A_73)
      | ~ v3_waybel_3(A_73)
      | ~ v2_lattice3(A_73)
      | ~ v1_lattice3(A_73)
      | ~ v1_yellow_0(A_73)
      | ~ v5_orders_2(A_73)
      | ~ v4_orders_2(A_73)
      | ~ v3_orders_2(A_73) ) ),
    inference(resolution,[status(thm)],[c_79,c_4])).

tff(c_86,plain,(
    ! [B_72] :
      ( ~ v4_waybel_7(B_72,'#skF_5')
      | v5_waybel_6(B_72,'#skF_5')
      | ~ m1_subset_1(B_72,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5')
      | ~ v3_waybel_3('#skF_5')
      | ~ v2_lattice3('#skF_5')
      | ~ v1_lattice3('#skF_5')
      | ~ v1_yellow_0('#skF_5')
      | ~ v5_orders_2('#skF_5')
      | ~ v4_orders_2('#skF_5')
      | ~ v3_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_30,c_84])).

tff(c_90,plain,(
    ! [B_74] :
      ( ~ v4_waybel_7(B_74,'#skF_5')
      | v5_waybel_6(B_74,'#skF_5')
      | ~ m1_subset_1(B_74,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_40,c_38,c_36,c_34,c_32,c_86])).

tff(c_109,plain,
    ( ~ v4_waybel_7('#skF_6','#skF_5')
    | v5_waybel_6('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_28,c_90])).

tff(c_124,plain,(
    v5_waybel_6('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_109])).

tff(c_126,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_124])).

%------------------------------------------------------------------------------
