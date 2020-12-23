%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1989+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:45 EST 2020

% Result     : Theorem 2.24s
% Output     : CNFRefutation 2.24s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 420 expanded)
%              Number of leaves         :   33 ( 179 expanded)
%              Depth                    :   13
%              Number of atoms          :  201 (1956 expanded)
%              Number of equality atoms :    6 (  60 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_waybel_6 > v4_waybel_7 > v1_waybel_7 > v1_waybel_0 > v12_waybel_0 > r1_yellow_0 > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v2_lattice3 > v1_xboole_0 > v1_lattice3 > l1_orders_2 > k5_waybel_0 > k1_yellow_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_waybel_7,type,(
    v1_waybel_7: ( $i * $i ) > $o )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k1_yellow_0,type,(
    k1_yellow_0: ( $i * $i ) > $i )).

tff(v5_waybel_6,type,(
    v5_waybel_6: ( $i * $i ) > $o )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(v12_waybel_0,type,(
    v12_waybel_0: ( $i * $i ) > $o )).

tff(v1_lattice3,type,(
    v1_lattice3: $i > $o )).

tff(v4_waybel_7,type,(
    v4_waybel_7: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(r1_yellow_0,type,(
    r1_yellow_0: ( $i * $i ) > $o )).

tff(k5_waybel_0,type,(
    k5_waybel_0: ( $i * $i ) > $i )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff(v1_waybel_0,type,(
    v1_waybel_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_lattice3,type,(
    v2_lattice3: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_157,negated_conjecture,(
    ~ ! [A] :
        ( ( v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & v1_lattice3(A)
          & v2_lattice3(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ( v5_waybel_6(B,A)
             => v4_waybel_7(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_waybel_7)).

tff(f_137,axiom,(
    ! [A] :
      ( ( v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & v1_lattice3(A)
        & v2_lattice3(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ( v5_waybel_6(B,A)
           => v1_waybel_7(k5_waybel_0(A,B),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_waybel_7)).

tff(f_118,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ( r1_yellow_0(A,k5_waybel_0(A,B))
            & k1_yellow_0(A,k5_waybel_0(A,B)) = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_waybel_0)).

tff(f_31,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v2_lattice3(A)
       => ~ v2_struct_0(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_lattice3)).

tff(f_86,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v4_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => v12_waybel_0(k5_waybel_0(A,B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc12_waybel_0)).

tff(f_75,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => m1_subset_1(k5_waybel_0(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_waybel_0)).

tff(f_100,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ( ~ v1_xboole_0(k5_waybel_0(A,B))
        & v1_waybel_0(k5_waybel_0(A,B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_waybel_0)).

tff(f_62,axiom,(
    ! [A] :
      ( ( v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & v1_lattice3(A)
        & v2_lattice3(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ( v4_waybel_7(B,A)
          <=> ? [C] :
                ( ~ v1_xboole_0(C)
                & v1_waybel_0(C,A)
                & v12_waybel_0(C,A)
                & v1_waybel_7(C,A)
                & m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
                & B = k1_yellow_0(A,C) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_waybel_7)).

tff(c_40,plain,(
    l1_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_42,plain,(
    v2_lattice3('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_50,plain,(
    v3_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_48,plain,(
    v4_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_46,plain,(
    v5_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_44,plain,(
    v1_lattice3('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_38,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_36,plain,(
    v5_waybel_6('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_32,plain,(
    ! [A_23,B_25] :
      ( v1_waybel_7(k5_waybel_0(A_23,B_25),A_23)
      | ~ v5_waybel_6(B_25,A_23)
      | ~ m1_subset_1(B_25,u1_struct_0(A_23))
      | ~ l1_orders_2(A_23)
      | ~ v2_lattice3(A_23)
      | ~ v1_lattice3(A_23)
      | ~ v5_orders_2(A_23)
      | ~ v4_orders_2(A_23)
      | ~ v3_orders_2(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_70,plain,(
    ! [A_42,B_43] :
      ( k1_yellow_0(A_42,k5_waybel_0(A_42,B_43)) = B_43
      | ~ m1_subset_1(B_43,u1_struct_0(A_42))
      | ~ l1_orders_2(A_42)
      | ~ v5_orders_2(A_42)
      | ~ v4_orders_2(A_42)
      | ~ v3_orders_2(A_42)
      | v2_struct_0(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_74,plain,
    ( k1_yellow_0('#skF_2',k5_waybel_0('#skF_2','#skF_3')) = '#skF_3'
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_70])).

tff(c_78,plain,
    ( k1_yellow_0('#skF_2',k5_waybel_0('#skF_2','#skF_3')) = '#skF_3'
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_40,c_74])).

tff(c_79,plain,(
    v2_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_78])).

tff(c_2,plain,(
    ! [A_1] :
      ( ~ v2_struct_0(A_1)
      | ~ v2_lattice3(A_1)
      | ~ l1_orders_2(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_82,plain,
    ( ~ v2_lattice3('#skF_2')
    | ~ l1_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_79,c_2])).

tff(c_86,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_42,c_82])).

tff(c_88,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_22,plain,(
    ! [A_16,B_17] :
      ( v12_waybel_0(k5_waybel_0(A_16,B_17),A_16)
      | ~ m1_subset_1(B_17,u1_struct_0(A_16))
      | ~ l1_orders_2(A_16)
      | ~ v4_orders_2(A_16)
      | v2_struct_0(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_20,plain,(
    ! [A_14,B_15] :
      ( m1_subset_1(k5_waybel_0(A_14,B_15),k1_zfmisc_1(u1_struct_0(A_14)))
      | ~ m1_subset_1(B_15,u1_struct_0(A_14))
      | ~ l1_orders_2(A_14)
      | v2_struct_0(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_24,plain,(
    ! [A_18,B_19] :
      ( v1_waybel_0(k5_waybel_0(A_18,B_19),A_18)
      | ~ m1_subset_1(B_19,u1_struct_0(A_18))
      | ~ l1_orders_2(A_18)
      | ~ v3_orders_2(A_18)
      | v2_struct_0(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_53,plain,(
    ! [A_30,B_31] :
      ( ~ v1_xboole_0(k5_waybel_0(A_30,B_31))
      | ~ m1_subset_1(B_31,u1_struct_0(A_30))
      | ~ l1_orders_2(A_30)
      | ~ v3_orders_2(A_30)
      | v2_struct_0(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_59,plain,
    ( ~ v1_xboole_0(k5_waybel_0('#skF_2','#skF_3'))
    | ~ l1_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_53])).

tff(c_63,plain,
    ( ~ v1_xboole_0(k5_waybel_0('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_40,c_59])).

tff(c_64,plain,(
    ~ v1_xboole_0(k5_waybel_0('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_63])).

tff(c_34,plain,(
    ~ v4_waybel_7('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_87,plain,(
    k1_yellow_0('#skF_2',k5_waybel_0('#skF_2','#skF_3')) = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_220,plain,(
    ! [A_66,C_67] :
      ( v4_waybel_7(k1_yellow_0(A_66,C_67),A_66)
      | ~ m1_subset_1(C_67,k1_zfmisc_1(u1_struct_0(A_66)))
      | ~ v1_waybel_7(C_67,A_66)
      | ~ v12_waybel_0(C_67,A_66)
      | ~ v1_waybel_0(C_67,A_66)
      | v1_xboole_0(C_67)
      | ~ m1_subset_1(k1_yellow_0(A_66,C_67),u1_struct_0(A_66))
      | ~ l1_orders_2(A_66)
      | ~ v2_lattice3(A_66)
      | ~ v1_lattice3(A_66)
      | ~ v5_orders_2(A_66)
      | ~ v4_orders_2(A_66)
      | ~ v3_orders_2(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_229,plain,
    ( v4_waybel_7(k1_yellow_0('#skF_2',k5_waybel_0('#skF_2','#skF_3')),'#skF_2')
    | ~ m1_subset_1(k5_waybel_0('#skF_2','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ v1_waybel_7(k5_waybel_0('#skF_2','#skF_3'),'#skF_2')
    | ~ v12_waybel_0(k5_waybel_0('#skF_2','#skF_3'),'#skF_2')
    | ~ v1_waybel_0(k5_waybel_0('#skF_2','#skF_3'),'#skF_2')
    | v1_xboole_0(k5_waybel_0('#skF_2','#skF_3'))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_orders_2('#skF_2')
    | ~ v2_lattice3('#skF_2')
    | ~ v1_lattice3('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_87,c_220])).

tff(c_234,plain,
    ( v4_waybel_7('#skF_3','#skF_2')
    | ~ m1_subset_1(k5_waybel_0('#skF_2','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ v1_waybel_7(k5_waybel_0('#skF_2','#skF_3'),'#skF_2')
    | ~ v12_waybel_0(k5_waybel_0('#skF_2','#skF_3'),'#skF_2')
    | ~ v1_waybel_0(k5_waybel_0('#skF_2','#skF_3'),'#skF_2')
    | v1_xboole_0(k5_waybel_0('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_44,c_42,c_40,c_38,c_87,c_229])).

tff(c_235,plain,
    ( ~ m1_subset_1(k5_waybel_0('#skF_2','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ v1_waybel_7(k5_waybel_0('#skF_2','#skF_3'),'#skF_2')
    | ~ v12_waybel_0(k5_waybel_0('#skF_2','#skF_3'),'#skF_2')
    | ~ v1_waybel_0(k5_waybel_0('#skF_2','#skF_3'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_34,c_234])).

tff(c_237,plain,(
    ~ v1_waybel_0(k5_waybel_0('#skF_2','#skF_3'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_235])).

tff(c_240,plain,
    ( ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_237])).

tff(c_243,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_40,c_38,c_240])).

tff(c_245,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_243])).

tff(c_246,plain,
    ( ~ v12_waybel_0(k5_waybel_0('#skF_2','#skF_3'),'#skF_2')
    | ~ v1_waybel_7(k5_waybel_0('#skF_2','#skF_3'),'#skF_2')
    | ~ m1_subset_1(k5_waybel_0('#skF_2','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_235])).

tff(c_248,plain,(
    ~ m1_subset_1(k5_waybel_0('#skF_2','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_246])).

tff(c_251,plain,
    ( ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_20,c_248])).

tff(c_254,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_251])).

tff(c_256,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_254])).

tff(c_257,plain,
    ( ~ v1_waybel_7(k5_waybel_0('#skF_2','#skF_3'),'#skF_2')
    | ~ v12_waybel_0(k5_waybel_0('#skF_2','#skF_3'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_246])).

tff(c_259,plain,(
    ~ v12_waybel_0(k5_waybel_0('#skF_2','#skF_3'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_257])).

tff(c_262,plain,
    ( ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_22,c_259])).

tff(c_265,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_40,c_38,c_262])).

tff(c_267,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_265])).

tff(c_268,plain,(
    ~ v1_waybel_7(k5_waybel_0('#skF_2','#skF_3'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_257])).

tff(c_285,plain,
    ( ~ v5_waybel_6('#skF_3','#skF_2')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_orders_2('#skF_2')
    | ~ v2_lattice3('#skF_2')
    | ~ v1_lattice3('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_268])).

tff(c_289,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_44,c_42,c_40,c_38,c_36,c_285])).

tff(c_290,plain,(
    v2_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_63])).

tff(c_294,plain,
    ( ~ v2_lattice3('#skF_2')
    | ~ l1_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_290,c_2])).

tff(c_298,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_42,c_294])).

%------------------------------------------------------------------------------
