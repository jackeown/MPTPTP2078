%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1639+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:10 EST 2020

% Result     : Theorem 2.20s
% Output     : CNFRefutation 2.46s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 229 expanded)
%              Number of leaves         :   21 (  94 expanded)
%              Depth                    :   12
%              Number of atoms          :  186 ( 944 expanded)
%              Number of equality atoms :    8 ( 136 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_orders_2 > r1_orders_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > k5_waybel_0 > #nlpp > u1_struct_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(r3_orders_2,type,(
    r3_orders_2: ( $i * $i * $i ) > $o )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k5_waybel_0,type,(
    k5_waybel_0: ( $i * $i ) > $i )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_103,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v5_orders_2(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => ( k5_waybel_0(A,B) = k5_waybel_0(A,C)
                 => B = C ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_waybel_0)).

tff(f_67,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( r2_hidden(C,k5_waybel_0(A,B))
              <=> r1_orders_2(A,C,B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_waybel_0)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => r3_orders_2(A,B,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r3_orders_2)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => ( r3_orders_2(A,B,C)
      <=> r1_orders_2(A,B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r3_orders_2)).

tff(f_83,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_orders_2)).

tff(c_14,plain,(
    '#skF_2' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_24,plain,(
    v5_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_22,plain,(
    l1_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_18,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_20,plain,(
    m1_subset_1('#skF_2',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_28,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_16,plain,(
    k5_waybel_0('#skF_1','#skF_2') = k5_waybel_0('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_53,plain,(
    ! [C_29,A_30,B_31] :
      ( r2_hidden(C_29,k5_waybel_0(A_30,B_31))
      | ~ r1_orders_2(A_30,C_29,B_31)
      | ~ m1_subset_1(C_29,u1_struct_0(A_30))
      | ~ m1_subset_1(B_31,u1_struct_0(A_30))
      | ~ l1_orders_2(A_30)
      | v2_struct_0(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_56,plain,(
    ! [C_29] :
      ( r2_hidden(C_29,k5_waybel_0('#skF_1','#skF_3'))
      | ~ r1_orders_2('#skF_1',C_29,'#skF_2')
      | ~ m1_subset_1(C_29,u1_struct_0('#skF_1'))
      | ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1'))
      | ~ l1_orders_2('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_53])).

tff(c_58,plain,(
    ! [C_29] :
      ( r2_hidden(C_29,k5_waybel_0('#skF_1','#skF_3'))
      | ~ r1_orders_2('#skF_1',C_29,'#skF_2')
      | ~ m1_subset_1(C_29,u1_struct_0('#skF_1'))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_56])).

tff(c_59,plain,(
    ! [C_29] :
      ( r2_hidden(C_29,k5_waybel_0('#skF_1','#skF_3'))
      | ~ r1_orders_2('#skF_1',C_29,'#skF_2')
      | ~ m1_subset_1(C_29,u1_struct_0('#skF_1')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_58])).

tff(c_61,plain,(
    ! [A_33,C_34,B_35] :
      ( r1_orders_2(A_33,C_34,B_35)
      | ~ r2_hidden(C_34,k5_waybel_0(A_33,B_35))
      | ~ m1_subset_1(C_34,u1_struct_0(A_33))
      | ~ m1_subset_1(B_35,u1_struct_0(A_33))
      | ~ l1_orders_2(A_33)
      | v2_struct_0(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_64,plain,(
    ! [C_29] :
      ( r1_orders_2('#skF_1',C_29,'#skF_3')
      | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_1'))
      | ~ l1_orders_2('#skF_1')
      | v2_struct_0('#skF_1')
      | ~ r1_orders_2('#skF_1',C_29,'#skF_2')
      | ~ m1_subset_1(C_29,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_59,c_61])).

tff(c_73,plain,(
    ! [C_29] :
      ( r1_orders_2('#skF_1',C_29,'#skF_3')
      | v2_struct_0('#skF_1')
      | ~ r1_orders_2('#skF_1',C_29,'#skF_2')
      | ~ m1_subset_1(C_29,u1_struct_0('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_18,c_64])).

tff(c_79,plain,(
    ! [C_36] :
      ( r1_orders_2('#skF_1',C_36,'#skF_3')
      | ~ r1_orders_2('#skF_1',C_36,'#skF_2')
      | ~ m1_subset_1(C_36,u1_struct_0('#skF_1')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_73])).

tff(c_86,plain,
    ( r1_orders_2('#skF_1','#skF_3','#skF_3')
    | ~ r1_orders_2('#skF_1','#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_18,c_79])).

tff(c_88,plain,(
    ~ r1_orders_2('#skF_1','#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_86])).

tff(c_8,plain,(
    ! [C_13,A_7,B_11] :
      ( r2_hidden(C_13,k5_waybel_0(A_7,B_11))
      | ~ r1_orders_2(A_7,C_13,B_11)
      | ~ m1_subset_1(C_13,u1_struct_0(A_7))
      | ~ m1_subset_1(B_11,u1_struct_0(A_7))
      | ~ l1_orders_2(A_7)
      | v2_struct_0(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_70,plain,(
    ! [C_34] :
      ( r1_orders_2('#skF_1',C_34,'#skF_2')
      | ~ r2_hidden(C_34,k5_waybel_0('#skF_1','#skF_3'))
      | ~ m1_subset_1(C_34,u1_struct_0('#skF_1'))
      | ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1'))
      | ~ l1_orders_2('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_61])).

tff(c_77,plain,(
    ! [C_34] :
      ( r1_orders_2('#skF_1',C_34,'#skF_2')
      | ~ r2_hidden(C_34,k5_waybel_0('#skF_1','#skF_3'))
      | ~ m1_subset_1(C_34,u1_struct_0('#skF_1'))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_70])).

tff(c_162,plain,(
    ! [C_50] :
      ( r1_orders_2('#skF_1',C_50,'#skF_2')
      | ~ r2_hidden(C_50,k5_waybel_0('#skF_1','#skF_3'))
      | ~ m1_subset_1(C_50,u1_struct_0('#skF_1')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_77])).

tff(c_169,plain,(
    ! [C_13] :
      ( r1_orders_2('#skF_1',C_13,'#skF_2')
      | ~ r1_orders_2('#skF_1',C_13,'#skF_3')
      | ~ m1_subset_1(C_13,u1_struct_0('#skF_1'))
      | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_1'))
      | ~ l1_orders_2('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_8,c_162])).

tff(c_173,plain,(
    ! [C_13] :
      ( r1_orders_2('#skF_1',C_13,'#skF_2')
      | ~ r1_orders_2('#skF_1',C_13,'#skF_3')
      | ~ m1_subset_1(C_13,u1_struct_0('#skF_1'))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_18,c_169])).

tff(c_175,plain,(
    ! [C_51] :
      ( r1_orders_2('#skF_1',C_51,'#skF_2')
      | ~ r1_orders_2('#skF_1',C_51,'#skF_3')
      | ~ m1_subset_1(C_51,u1_struct_0('#skF_1')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_173])).

tff(c_178,plain,
    ( r1_orders_2('#skF_1','#skF_3','#skF_2')
    | ~ r1_orders_2('#skF_1','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_18,c_175])).

tff(c_184,plain,(
    ~ r1_orders_2('#skF_1','#skF_3','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_178])).

tff(c_26,plain,(
    v3_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_33,plain,(
    ! [A_25,B_26,C_27] :
      ( r3_orders_2(A_25,B_26,B_26)
      | ~ m1_subset_1(C_27,u1_struct_0(A_25))
      | ~ m1_subset_1(B_26,u1_struct_0(A_25))
      | ~ l1_orders_2(A_25)
      | ~ v3_orders_2(A_25)
      | v2_struct_0(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_35,plain,(
    ! [B_26] :
      ( r3_orders_2('#skF_1',B_26,B_26)
      | ~ m1_subset_1(B_26,u1_struct_0('#skF_1'))
      | ~ l1_orders_2('#skF_1')
      | ~ v3_orders_2('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_18,c_33])).

tff(c_40,plain,(
    ! [B_26] :
      ( r3_orders_2('#skF_1',B_26,B_26)
      | ~ m1_subset_1(B_26,u1_struct_0('#skF_1'))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_22,c_35])).

tff(c_46,plain,(
    ! [B_28] :
      ( r3_orders_2('#skF_1',B_28,B_28)
      | ~ m1_subset_1(B_28,u1_struct_0('#skF_1')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_40])).

tff(c_51,plain,(
    r3_orders_2('#skF_1','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_18,c_46])).

tff(c_237,plain,(
    ! [A_60,B_61,C_62] :
      ( r1_orders_2(A_60,B_61,C_62)
      | ~ r3_orders_2(A_60,B_61,C_62)
      | ~ m1_subset_1(C_62,u1_struct_0(A_60))
      | ~ m1_subset_1(B_61,u1_struct_0(A_60))
      | ~ l1_orders_2(A_60)
      | ~ v3_orders_2(A_60)
      | v2_struct_0(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_243,plain,
    ( r1_orders_2('#skF_1','#skF_3','#skF_3')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_1'))
    | ~ l1_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_51,c_237])).

tff(c_254,plain,
    ( r1_orders_2('#skF_1','#skF_3','#skF_3')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_22,c_18,c_243])).

tff(c_256,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_184,c_254])).

tff(c_258,plain,(
    r1_orders_2('#skF_1','#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_86])).

tff(c_87,plain,
    ( r1_orders_2('#skF_1','#skF_2','#skF_3')
    | ~ r1_orders_2('#skF_1','#skF_2','#skF_2') ),
    inference(resolution,[status(thm)],[c_20,c_79])).

tff(c_259,plain,(
    ~ r1_orders_2('#skF_1','#skF_2','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_87])).

tff(c_52,plain,(
    r3_orders_2('#skF_1','#skF_2','#skF_2') ),
    inference(resolution,[status(thm)],[c_20,c_46])).

tff(c_260,plain,(
    ! [A_63,B_64,C_65] :
      ( r1_orders_2(A_63,B_64,C_65)
      | ~ r3_orders_2(A_63,B_64,C_65)
      | ~ m1_subset_1(C_65,u1_struct_0(A_63))
      | ~ m1_subset_1(B_64,u1_struct_0(A_63))
      | ~ l1_orders_2(A_63)
      | ~ v3_orders_2(A_63)
      | v2_struct_0(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_262,plain,
    ( r1_orders_2('#skF_1','#skF_2','#skF_2')
    | ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1'))
    | ~ l1_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_52,c_260])).

tff(c_267,plain,
    ( r1_orders_2('#skF_1','#skF_2','#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_22,c_20,c_262])).

tff(c_269,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_259,c_267])).

tff(c_270,plain,(
    r1_orders_2('#skF_1','#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_87])).

tff(c_311,plain,(
    ! [C_71,B_72,A_73] :
      ( C_71 = B_72
      | ~ r1_orders_2(A_73,C_71,B_72)
      | ~ r1_orders_2(A_73,B_72,C_71)
      | ~ m1_subset_1(C_71,u1_struct_0(A_73))
      | ~ m1_subset_1(B_72,u1_struct_0(A_73))
      | ~ l1_orders_2(A_73)
      | ~ v5_orders_2(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_315,plain,
    ( '#skF_2' = '#skF_3'
    | ~ r1_orders_2('#skF_1','#skF_3','#skF_2')
    | ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1'))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_1'))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1') ),
    inference(resolution,[status(thm)],[c_270,c_311])).

tff(c_326,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_18,c_20,c_258,c_315])).

tff(c_328,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14,c_326])).

%------------------------------------------------------------------------------
