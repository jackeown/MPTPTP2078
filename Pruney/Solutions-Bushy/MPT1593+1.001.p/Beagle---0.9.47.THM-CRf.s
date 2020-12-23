%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1593+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:07 EST 2020

% Result     : Theorem 2.97s
% Output     : CNFRefutation 2.97s
% Verified   : 
% Statistics : Number of formulae       :   53 ( 143 expanded)
%              Number of leaves         :   21 (  59 expanded)
%              Depth                    :   11
%              Number of atoms          :   90 ( 283 expanded)
%              Number of equality atoms :   42 ( 110 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_subset_1 > v1_orders_2 > l1_orders_2 > k2_zfmisc_1 > g1_orders_2 > #nlpp > u1_struct_0 > u1_orders_2 > k2_yellow_1 > k1_zfmisc_1 > k1_yellow_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_orders_2,type,(
    v1_orders_2: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k2_yellow_1,type,(
    k2_yellow_1: $i > $i )).

tff(g1_orders_2,type,(
    g1_orders_2: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff(k1_yellow_1,type,(
    k1_yellow_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_orders_2,type,(
    u1_orders_2: $i > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_36,axiom,(
    ! [A] :
      ( v1_orders_2(k2_yellow_1(A))
      & l1_orders_2(k2_yellow_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_yellow_1)).

tff(f_40,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => m1_subset_1(u1_orders_2(A),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_orders_2)).

tff(f_32,axiom,(
    ! [A] : k2_yellow_1(A) = g1_orders_2(A,k1_yellow_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_yellow_1)).

tff(f_30,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v1_orders_2(A)
       => A = g1_orders_2(u1_struct_0(A),u1_orders_2(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',abstractness_v1_orders_2)).

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A)))
     => ! [C,D] :
          ( g1_orders_2(A,B) = g1_orders_2(C,D)
         => ( A = C
            & B = D ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',free_g1_orders_2)).

tff(f_54,negated_conjecture,(
    ~ ! [A] :
        ( u1_struct_0(k2_yellow_1(A)) = A
        & u1_orders_2(k2_yellow_1(A)) = k1_yellow_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_yellow_1)).

tff(c_8,plain,(
    ! [A_3] : l1_orders_2(k2_yellow_1(A_3)) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_10,plain,(
    ! [A_4] :
      ( m1_subset_1(u1_orders_2(A_4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_4),u1_struct_0(A_4))))
      | ~ l1_orders_2(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_6,plain,(
    ! [A_3] : v1_orders_2(k2_yellow_1(A_3)) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_4,plain,(
    ! [A_2] : g1_orders_2(A_2,k1_yellow_1(A_2)) = k2_yellow_1(A_2) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_2,plain,(
    ! [A_1] :
      ( g1_orders_2(u1_struct_0(A_1),u1_orders_2(A_1)) = A_1
      | ~ v1_orders_2(A_1)
      | ~ l1_orders_2(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_530,plain,(
    ! [C_100,A_101,D_102,B_103] :
      ( C_100 = A_101
      | g1_orders_2(C_100,D_102) != g1_orders_2(A_101,B_103)
      | ~ m1_subset_1(B_103,k1_zfmisc_1(k2_zfmisc_1(A_101,A_101))) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_974,plain,(
    ! [A_162,C_163,D_164] :
      ( u1_struct_0(A_162) = C_163
      | g1_orders_2(C_163,D_164) != A_162
      | ~ m1_subset_1(u1_orders_2(A_162),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_162),u1_struct_0(A_162))))
      | ~ v1_orders_2(A_162)
      | ~ l1_orders_2(A_162) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_530])).

tff(c_982,plain,(
    ! [A_162,A_2] :
      ( u1_struct_0(A_162) = A_2
      | k2_yellow_1(A_2) != A_162
      | ~ m1_subset_1(u1_orders_2(A_162),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_162),u1_struct_0(A_162))))
      | ~ v1_orders_2(A_162)
      | ~ l1_orders_2(A_162) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_974])).

tff(c_992,plain,(
    ! [A_2] :
      ( u1_struct_0(k2_yellow_1(A_2)) = A_2
      | ~ m1_subset_1(u1_orders_2(k2_yellow_1(A_2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k2_yellow_1(A_2)),u1_struct_0(k2_yellow_1(A_2)))))
      | ~ v1_orders_2(k2_yellow_1(A_2))
      | ~ l1_orders_2(k2_yellow_1(A_2)) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_982])).

tff(c_1000,plain,(
    ! [A_171] :
      ( u1_struct_0(k2_yellow_1(A_171)) = A_171
      | ~ m1_subset_1(u1_orders_2(k2_yellow_1(A_171)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k2_yellow_1(A_171)),u1_struct_0(k2_yellow_1(A_171))))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_6,c_992])).

tff(c_1018,plain,(
    ! [A_171] :
      ( u1_struct_0(k2_yellow_1(A_171)) = A_171
      | ~ l1_orders_2(k2_yellow_1(A_171)) ) ),
    inference(resolution,[status(thm)],[c_10,c_1000])).

tff(c_1028,plain,(
    ! [A_171] : u1_struct_0(k2_yellow_1(A_171)) = A_171 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_1018])).

tff(c_56,plain,(
    ! [C_20,A_21,D_22,B_23] :
      ( C_20 = A_21
      | g1_orders_2(C_20,D_22) != g1_orders_2(A_21,B_23)
      | ~ m1_subset_1(B_23,k1_zfmisc_1(k2_zfmisc_1(A_21,A_21))) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_65,plain,(
    ! [A_25,A_24,B_26] :
      ( A_25 = A_24
      | k2_yellow_1(A_25) != g1_orders_2(A_24,B_26)
      | ~ m1_subset_1(B_26,k1_zfmisc_1(k2_zfmisc_1(A_24,A_24))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_56])).

tff(c_67,plain,(
    ! [A_1,A_25] :
      ( u1_struct_0(A_1) = A_25
      | k2_yellow_1(A_25) != A_1
      | ~ m1_subset_1(u1_orders_2(A_1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1),u1_struct_0(A_1))))
      | ~ v1_orders_2(A_1)
      | ~ l1_orders_2(A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_65])).

tff(c_152,plain,(
    ! [A_25] :
      ( u1_struct_0(k2_yellow_1(A_25)) = A_25
      | ~ m1_subset_1(u1_orders_2(k2_yellow_1(A_25)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k2_yellow_1(A_25)),u1_struct_0(k2_yellow_1(A_25)))))
      | ~ v1_orders_2(k2_yellow_1(A_25))
      | ~ l1_orders_2(k2_yellow_1(A_25)) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_67])).

tff(c_156,plain,(
    ! [A_59] :
      ( u1_struct_0(k2_yellow_1(A_59)) = A_59
      | ~ m1_subset_1(u1_orders_2(k2_yellow_1(A_59)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k2_yellow_1(A_59)),u1_struct_0(k2_yellow_1(A_59))))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_6,c_152])).

tff(c_159,plain,(
    ! [A_59] :
      ( u1_struct_0(k2_yellow_1(A_59)) = A_59
      | ~ l1_orders_2(k2_yellow_1(A_59)) ) ),
    inference(resolution,[status(thm)],[c_10,c_156])).

tff(c_162,plain,(
    ! [A_59] : u1_struct_0(k2_yellow_1(A_59)) = A_59 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_159])).

tff(c_165,plain,(
    ! [A_60] : u1_struct_0(k2_yellow_1(A_60)) = A_60 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_159])).

tff(c_171,plain,(
    ! [A_60] :
      ( m1_subset_1(u1_orders_2(k2_yellow_1(A_60)),k1_zfmisc_1(k2_zfmisc_1(A_60,u1_struct_0(k2_yellow_1(A_60)))))
      | ~ l1_orders_2(k2_yellow_1(A_60)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_165,c_10])).

tff(c_183,plain,(
    ! [A_60] : m1_subset_1(u1_orders_2(k2_yellow_1(A_60)),k1_zfmisc_1(k2_zfmisc_1(A_60,A_60))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_162,c_171])).

tff(c_43,plain,(
    ! [D_16,B_17,C_18,A_19] :
      ( D_16 = B_17
      | g1_orders_2(C_18,D_16) != g1_orders_2(A_19,B_17)
      | ~ m1_subset_1(B_17,k1_zfmisc_1(k2_zfmisc_1(A_19,A_19))) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_75,plain,(
    ! [A_29,B_30,A_31] :
      ( k1_yellow_1(A_29) = B_30
      | k2_yellow_1(A_29) != g1_orders_2(A_31,B_30)
      | ~ m1_subset_1(B_30,k1_zfmisc_1(k2_zfmisc_1(A_31,A_31))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_43])).

tff(c_77,plain,(
    ! [A_1,A_29] :
      ( u1_orders_2(A_1) = k1_yellow_1(A_29)
      | k2_yellow_1(A_29) != A_1
      | ~ m1_subset_1(u1_orders_2(A_1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1),u1_struct_0(A_1))))
      | ~ v1_orders_2(A_1)
      | ~ l1_orders_2(A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_75])).

tff(c_447,plain,(
    ! [A_29] :
      ( u1_orders_2(k2_yellow_1(A_29)) = k1_yellow_1(A_29)
      | ~ m1_subset_1(u1_orders_2(k2_yellow_1(A_29)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k2_yellow_1(A_29)),u1_struct_0(k2_yellow_1(A_29)))))
      | ~ v1_orders_2(k2_yellow_1(A_29))
      | ~ l1_orders_2(k2_yellow_1(A_29)) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_77])).

tff(c_449,plain,(
    ! [A_29] : u1_orders_2(k2_yellow_1(A_29)) = k1_yellow_1(A_29) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_6,c_183,c_162,c_162,c_447])).

tff(c_16,plain,
    ( u1_struct_0(k2_yellow_1('#skF_2')) != '#skF_2'
    | u1_orders_2(k2_yellow_1('#skF_1')) != k1_yellow_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_28,plain,(
    u1_orders_2(k2_yellow_1('#skF_1')) != k1_yellow_1('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_16])).

tff(c_464,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_449,c_28])).

tff(c_465,plain,(
    u1_struct_0(k2_yellow_1('#skF_2')) != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_16])).

tff(c_1043,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1028,c_465])).

%------------------------------------------------------------------------------
