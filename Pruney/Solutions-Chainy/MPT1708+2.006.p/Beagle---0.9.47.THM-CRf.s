%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:28 EST 2020

% Result     : Theorem 5.26s
% Output     : CNFRefutation 5.26s
% Verified   : 
% Statistics : Number of formulae       :  118 ( 213 expanded)
%              Number of leaves         :   41 (  95 expanded)
%              Depth                    :   12
%              Number of atoms          :  368 (1092 expanded)
%              Number of equality atoms :   29 ( 109 expanded)
%              Maximal formula depth    :   18 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tsep_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > l1_pre_topc > k4_enumset1 > k3_enumset1 > k2_enumset1 > k2_tsep_1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k1_setfam_1 > #skF_2 > #skF_5 > #skF_6 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(k2_tsep_1,type,(
    k2_tsep_1: ( $i * $i * $i ) > $i )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(r1_tsep_1,type,(
    r1_tsep_1: ( $i * $i ) > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_192,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & m1_pre_topc(B,A) )
           => ! [C] :
                ( ( ~ v2_struct_0(C)
                  & m1_pre_topc(C,A) )
               => ( ~ r1_tsep_1(B,C)
                 => ! [D] :
                      ( m1_subset_1(D,u1_struct_0(k2_tsep_1(A,B,C)))
                     => ( ? [E] :
                            ( m1_subset_1(E,u1_struct_0(B))
                            & E = D )
                        & ? [E] :
                            ( m1_subset_1(E,u1_struct_0(C))
                            & E = D ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_tmap_1)).

tff(f_142,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A)
        & ~ v2_struct_0(B)
        & m1_pre_topc(B,A)
        & ~ v2_struct_0(C)
        & m1_pre_topc(C,A) )
     => ( ~ v2_struct_0(k2_tsep_1(A,B,C))
        & v1_pre_topc(k2_tsep_1(A,B,C))
        & m1_pre_topc(k2_tsep_1(A,B,C),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tsep_1)).

tff(f_120,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & m1_pre_topc(B,A) )
         => ! [C] :
              ( ( ~ v2_struct_0(C)
                & m1_pre_topc(C,A) )
             => ( ~ r1_tsep_1(B,C)
               => ! [D] :
                    ( ( ~ v2_struct_0(D)
                      & v1_pre_topc(D)
                      & m1_pre_topc(D,A) )
                   => ( D = k2_tsep_1(A,B,C)
                    <=> u1_struct_0(D) = k3_xboole_0(u1_struct_0(B),u1_struct_0(C)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tsep_1)).

tff(f_29,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_59,axiom,(
    ! [A,B,C,D,E,F,G] :
      ( G = k4_enumset1(A,B,C,D,E,F)
    <=> ! [H] :
          ( r2_hidden(H,G)
        <=> ~ ( H != A
              & H != B
              & H != C
              & H != D
              & H != E
              & H != F ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_enumset1)).

tff(f_61,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(k1_setfam_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_setfam_1)).

tff(f_156,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_pre_topc(C,A)
             => ( r1_tarski(u1_struct_0(B),u1_struct_0(C))
              <=> m1_pre_topc(B,C) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_tsep_1)).

tff(f_72,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_88,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & m1_pre_topc(B,A) )
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(B))
             => m1_subset_1(C,u1_struct_0(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_pre_topc)).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(c_94,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_88,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_84,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_80,plain,(
    ~ r1_tsep_1('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_90,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_86,plain,(
    m1_pre_topc('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_82,plain,(
    m1_pre_topc('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_92,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_66,plain,(
    ! [A_56,B_57,C_58] :
      ( m1_pre_topc(k2_tsep_1(A_56,B_57,C_58),A_56)
      | ~ m1_pre_topc(C_58,A_56)
      | v2_struct_0(C_58)
      | ~ m1_pre_topc(B_57,A_56)
      | v2_struct_0(B_57)
      | ~ l1_pre_topc(A_56)
      | v2_struct_0(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_68,plain,(
    ! [A_56,B_57,C_58] :
      ( v1_pre_topc(k2_tsep_1(A_56,B_57,C_58))
      | ~ m1_pre_topc(C_58,A_56)
      | v2_struct_0(C_58)
      | ~ m1_pre_topc(B_57,A_56)
      | v2_struct_0(B_57)
      | ~ l1_pre_topc(A_56)
      | v2_struct_0(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_1586,plain,(
    ! [A_806,B_807,C_808] :
      ( u1_struct_0(k2_tsep_1(A_806,B_807,C_808)) = k3_xboole_0(u1_struct_0(B_807),u1_struct_0(C_808))
      | ~ m1_pre_topc(k2_tsep_1(A_806,B_807,C_808),A_806)
      | ~ v1_pre_topc(k2_tsep_1(A_806,B_807,C_808))
      | v2_struct_0(k2_tsep_1(A_806,B_807,C_808))
      | r1_tsep_1(B_807,C_808)
      | ~ m1_pre_topc(C_808,A_806)
      | v2_struct_0(C_808)
      | ~ m1_pre_topc(B_807,A_806)
      | v2_struct_0(B_807)
      | ~ l1_pre_topc(A_806)
      | v2_struct_0(A_806) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_1590,plain,(
    ! [A_809,B_810,C_811] :
      ( u1_struct_0(k2_tsep_1(A_809,B_810,C_811)) = k3_xboole_0(u1_struct_0(B_810),u1_struct_0(C_811))
      | ~ v1_pre_topc(k2_tsep_1(A_809,B_810,C_811))
      | v2_struct_0(k2_tsep_1(A_809,B_810,C_811))
      | r1_tsep_1(B_810,C_811)
      | ~ m1_pre_topc(C_811,A_809)
      | v2_struct_0(C_811)
      | ~ m1_pre_topc(B_810,A_809)
      | v2_struct_0(B_810)
      | ~ l1_pre_topc(A_809)
      | v2_struct_0(A_809) ) ),
    inference(resolution,[status(thm)],[c_66,c_1586])).

tff(c_70,plain,(
    ! [A_56,B_57,C_58] :
      ( ~ v2_struct_0(k2_tsep_1(A_56,B_57,C_58))
      | ~ m1_pre_topc(C_58,A_56)
      | v2_struct_0(C_58)
      | ~ m1_pre_topc(B_57,A_56)
      | v2_struct_0(B_57)
      | ~ l1_pre_topc(A_56)
      | v2_struct_0(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_1663,plain,(
    ! [A_812,B_813,C_814] :
      ( u1_struct_0(k2_tsep_1(A_812,B_813,C_814)) = k3_xboole_0(u1_struct_0(B_813),u1_struct_0(C_814))
      | ~ v1_pre_topc(k2_tsep_1(A_812,B_813,C_814))
      | r1_tsep_1(B_813,C_814)
      | ~ m1_pre_topc(C_814,A_812)
      | v2_struct_0(C_814)
      | ~ m1_pre_topc(B_813,A_812)
      | v2_struct_0(B_813)
      | ~ l1_pre_topc(A_812)
      | v2_struct_0(A_812) ) ),
    inference(resolution,[status(thm)],[c_1590,c_70])).

tff(c_1667,plain,(
    ! [A_815,B_816,C_817] :
      ( u1_struct_0(k2_tsep_1(A_815,B_816,C_817)) = k3_xboole_0(u1_struct_0(B_816),u1_struct_0(C_817))
      | r1_tsep_1(B_816,C_817)
      | ~ m1_pre_topc(C_817,A_815)
      | v2_struct_0(C_817)
      | ~ m1_pre_topc(B_816,A_815)
      | v2_struct_0(B_816)
      | ~ l1_pre_topc(A_815)
      | v2_struct_0(A_815) ) ),
    inference(resolution,[status(thm)],[c_68,c_1663])).

tff(c_4,plain,(
    ! [A_3,B_4] : k1_enumset1(A_3,A_3,B_4) = k2_tarski(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6,plain,(
    ! [A_5,B_6,C_7] : k2_enumset1(A_5,A_5,B_6,C_7) = k1_enumset1(A_5,B_6,C_7) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,(
    ! [A_8,B_9,C_10,D_11] : k3_enumset1(A_8,A_8,B_9,C_10,D_11) = k2_enumset1(A_8,B_9,C_10,D_11) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_757,plain,(
    ! [C_471,B_467,D_470,E_469,A_468] : k4_enumset1(A_468,A_468,B_467,C_471,D_470,E_469) = k3_enumset1(A_468,B_467,C_471,D_470,E_469) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_14,plain,(
    ! [E_21,D_20,C_19,H_26,B_18,A_17] : r2_hidden(H_26,k4_enumset1(A_17,B_18,C_19,D_20,E_21,H_26)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_784,plain,(
    ! [E_472,A_476,D_475,C_473,B_474] : r2_hidden(E_472,k3_enumset1(A_476,B_474,C_473,D_475,E_472)) ),
    inference(superposition,[status(thm),theory(equality)],[c_757,c_14])).

tff(c_788,plain,(
    ! [D_477,A_478,B_479,C_480] : r2_hidden(D_477,k2_enumset1(A_478,B_479,C_480,D_477)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_784])).

tff(c_801,plain,(
    ! [C_484,A_485,B_486] : r2_hidden(C_484,k1_enumset1(A_485,B_486,C_484)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_788])).

tff(c_805,plain,(
    ! [B_487,A_488] : r2_hidden(B_487,k2_tarski(A_488,B_487)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_801])).

tff(c_54,plain,(
    ! [A_27,B_28] : k1_setfam_1(k2_tarski(A_27,B_28)) = k3_xboole_0(A_27,B_28) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_127,plain,(
    ! [B_117,A_118] :
      ( r1_tarski(k1_setfam_1(B_117),A_118)
      | ~ r2_hidden(A_118,B_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_130,plain,(
    ! [A_27,B_28,A_118] :
      ( r1_tarski(k3_xboole_0(A_27,B_28),A_118)
      | ~ r2_hidden(A_118,k2_tarski(A_27,B_28)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_127])).

tff(c_809,plain,(
    ! [A_488,B_487] : r1_tarski(k3_xboole_0(A_488,B_487),B_487) ),
    inference(resolution,[status(thm)],[c_805,c_130])).

tff(c_1747,plain,(
    ! [A_824,B_825,C_826] :
      ( r1_tarski(u1_struct_0(k2_tsep_1(A_824,B_825,C_826)),u1_struct_0(C_826))
      | r1_tsep_1(B_825,C_826)
      | ~ m1_pre_topc(C_826,A_824)
      | v2_struct_0(C_826)
      | ~ m1_pre_topc(B_825,A_824)
      | v2_struct_0(B_825)
      | ~ l1_pre_topc(A_824)
      | v2_struct_0(A_824) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1667,c_809])).

tff(c_74,plain,(
    ! [B_63,C_65,A_59] :
      ( m1_pre_topc(B_63,C_65)
      | ~ r1_tarski(u1_struct_0(B_63),u1_struct_0(C_65))
      | ~ m1_pre_topc(C_65,A_59)
      | ~ m1_pre_topc(B_63,A_59)
      | ~ l1_pre_topc(A_59)
      | ~ v2_pre_topc(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_1789,plain,(
    ! [A_841,B_842,C_843,A_844] :
      ( m1_pre_topc(k2_tsep_1(A_841,B_842,C_843),C_843)
      | ~ m1_pre_topc(C_843,A_844)
      | ~ m1_pre_topc(k2_tsep_1(A_841,B_842,C_843),A_844)
      | ~ l1_pre_topc(A_844)
      | ~ v2_pre_topc(A_844)
      | r1_tsep_1(B_842,C_843)
      | ~ m1_pre_topc(C_843,A_841)
      | v2_struct_0(C_843)
      | ~ m1_pre_topc(B_842,A_841)
      | v2_struct_0(B_842)
      | ~ l1_pre_topc(A_841)
      | v2_struct_0(A_841) ) ),
    inference(resolution,[status(thm)],[c_1747,c_74])).

tff(c_1802,plain,(
    ! [A_845,B_846,C_847] :
      ( m1_pre_topc(k2_tsep_1(A_845,B_846,C_847),C_847)
      | ~ v2_pre_topc(A_845)
      | r1_tsep_1(B_846,C_847)
      | ~ m1_pre_topc(C_847,A_845)
      | v2_struct_0(C_847)
      | ~ m1_pre_topc(B_846,A_845)
      | v2_struct_0(B_846)
      | ~ l1_pre_topc(A_845)
      | v2_struct_0(A_845) ) ),
    inference(resolution,[status(thm)],[c_66,c_1789])).

tff(c_114,plain,(
    ! [B_115,A_116] :
      ( l1_pre_topc(B_115)
      | ~ m1_pre_topc(B_115,A_116)
      | ~ l1_pre_topc(A_116) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_120,plain,
    ( l1_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_82,c_114])).

tff(c_126,plain,(
    l1_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_120])).

tff(c_78,plain,(
    m1_subset_1('#skF_6',u1_struct_0(k2_tsep_1('#skF_3','#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_792,plain,(
    ! [C_481,A_482,B_483] :
      ( m1_subset_1(C_481,u1_struct_0(A_482))
      | ~ m1_subset_1(C_481,u1_struct_0(B_483))
      | ~ m1_pre_topc(B_483,A_482)
      | v2_struct_0(B_483)
      | ~ l1_pre_topc(A_482)
      | v2_struct_0(A_482) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_800,plain,(
    ! [A_482] :
      ( m1_subset_1('#skF_6',u1_struct_0(A_482))
      | ~ m1_pre_topc(k2_tsep_1('#skF_3','#skF_4','#skF_5'),A_482)
      | v2_struct_0(k2_tsep_1('#skF_3','#skF_4','#skF_5'))
      | ~ l1_pre_topc(A_482)
      | v2_struct_0(A_482) ) ),
    inference(resolution,[status(thm)],[c_78,c_792])).

tff(c_851,plain,(
    v2_struct_0(k2_tsep_1('#skF_3','#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_800])).

tff(c_903,plain,(
    ! [A_542,B_543,C_544] :
      ( ~ v2_struct_0(k2_tsep_1(A_542,B_543,C_544))
      | ~ m1_pre_topc(C_544,A_542)
      | v2_struct_0(C_544)
      | ~ m1_pre_topc(B_543,A_542)
      | v2_struct_0(B_543)
      | ~ l1_pre_topc(A_542)
      | v2_struct_0(A_542) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_906,plain,
    ( ~ m1_pre_topc('#skF_5','#skF_3')
    | v2_struct_0('#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_851,c_903])).

tff(c_909,plain,
    ( v2_struct_0('#skF_5')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_86,c_82,c_906])).

tff(c_911,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_88,c_84,c_909])).

tff(c_951,plain,(
    ! [A_567] :
      ( m1_subset_1('#skF_6',u1_struct_0(A_567))
      | ~ m1_pre_topc(k2_tsep_1('#skF_3','#skF_4','#skF_5'),A_567)
      | ~ l1_pre_topc(A_567)
      | v2_struct_0(A_567) ) ),
    inference(splitRight,[status(thm)],[c_800])).

tff(c_531,plain,(
    ! [A_379,B_380,C_381] :
      ( u1_struct_0(k2_tsep_1(A_379,B_380,C_381)) = k3_xboole_0(u1_struct_0(B_380),u1_struct_0(C_381))
      | ~ m1_pre_topc(k2_tsep_1(A_379,B_380,C_381),A_379)
      | ~ v1_pre_topc(k2_tsep_1(A_379,B_380,C_381))
      | v2_struct_0(k2_tsep_1(A_379,B_380,C_381))
      | r1_tsep_1(B_380,C_381)
      | ~ m1_pre_topc(C_381,A_379)
      | v2_struct_0(C_381)
      | ~ m1_pre_topc(B_380,A_379)
      | v2_struct_0(B_380)
      | ~ l1_pre_topc(A_379)
      | v2_struct_0(A_379) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_536,plain,(
    ! [A_389,B_390,C_391] :
      ( u1_struct_0(k2_tsep_1(A_389,B_390,C_391)) = k3_xboole_0(u1_struct_0(B_390),u1_struct_0(C_391))
      | ~ v1_pre_topc(k2_tsep_1(A_389,B_390,C_391))
      | v2_struct_0(k2_tsep_1(A_389,B_390,C_391))
      | r1_tsep_1(B_390,C_391)
      | ~ m1_pre_topc(C_391,A_389)
      | v2_struct_0(C_391)
      | ~ m1_pre_topc(B_390,A_389)
      | v2_struct_0(B_390)
      | ~ l1_pre_topc(A_389)
      | v2_struct_0(A_389) ) ),
    inference(resolution,[status(thm)],[c_66,c_531])).

tff(c_603,plain,(
    ! [A_392,B_393,C_394] :
      ( u1_struct_0(k2_tsep_1(A_392,B_393,C_394)) = k3_xboole_0(u1_struct_0(B_393),u1_struct_0(C_394))
      | ~ v1_pre_topc(k2_tsep_1(A_392,B_393,C_394))
      | r1_tsep_1(B_393,C_394)
      | ~ m1_pre_topc(C_394,A_392)
      | v2_struct_0(C_394)
      | ~ m1_pre_topc(B_393,A_392)
      | v2_struct_0(B_393)
      | ~ l1_pre_topc(A_392)
      | v2_struct_0(A_392) ) ),
    inference(resolution,[status(thm)],[c_536,c_70])).

tff(c_607,plain,(
    ! [A_395,B_396,C_397] :
      ( u1_struct_0(k2_tsep_1(A_395,B_396,C_397)) = k3_xboole_0(u1_struct_0(B_396),u1_struct_0(C_397))
      | r1_tsep_1(B_396,C_397)
      | ~ m1_pre_topc(C_397,A_395)
      | v2_struct_0(C_397)
      | ~ m1_pre_topc(B_396,A_395)
      | v2_struct_0(B_396)
      | ~ l1_pre_topc(A_395)
      | v2_struct_0(A_395) ) ),
    inference(resolution,[status(thm)],[c_68,c_603])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k3_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_669,plain,(
    ! [A_398,B_399,C_400] :
      ( r1_tarski(u1_struct_0(k2_tsep_1(A_398,B_399,C_400)),u1_struct_0(B_399))
      | r1_tsep_1(B_399,C_400)
      | ~ m1_pre_topc(C_400,A_398)
      | v2_struct_0(C_400)
      | ~ m1_pre_topc(B_399,A_398)
      | v2_struct_0(B_399)
      | ~ l1_pre_topc(A_398)
      | v2_struct_0(A_398) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_607,c_2])).

tff(c_692,plain,(
    ! [A_411,B_412,C_413,A_414] :
      ( m1_pre_topc(k2_tsep_1(A_411,B_412,C_413),B_412)
      | ~ m1_pre_topc(B_412,A_414)
      | ~ m1_pre_topc(k2_tsep_1(A_411,B_412,C_413),A_414)
      | ~ l1_pre_topc(A_414)
      | ~ v2_pre_topc(A_414)
      | r1_tsep_1(B_412,C_413)
      | ~ m1_pre_topc(C_413,A_411)
      | v2_struct_0(C_413)
      | ~ m1_pre_topc(B_412,A_411)
      | v2_struct_0(B_412)
      | ~ l1_pre_topc(A_411)
      | v2_struct_0(A_411) ) ),
    inference(resolution,[status(thm)],[c_669,c_74])).

tff(c_704,plain,(
    ! [A_418,B_419,C_420] :
      ( m1_pre_topc(k2_tsep_1(A_418,B_419,C_420),B_419)
      | ~ v2_pre_topc(A_418)
      | r1_tsep_1(B_419,C_420)
      | ~ m1_pre_topc(C_420,A_418)
      | v2_struct_0(C_420)
      | ~ m1_pre_topc(B_419,A_418)
      | v2_struct_0(B_419)
      | ~ l1_pre_topc(A_418)
      | v2_struct_0(A_418) ) ),
    inference(resolution,[status(thm)],[c_66,c_692])).

tff(c_117,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_86,c_114])).

tff(c_123,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_117])).

tff(c_188,plain,(
    ! [C_175,A_176,B_177] :
      ( m1_subset_1(C_175,u1_struct_0(A_176))
      | ~ m1_subset_1(C_175,u1_struct_0(B_177))
      | ~ m1_pre_topc(B_177,A_176)
      | v2_struct_0(B_177)
      | ~ l1_pre_topc(A_176)
      | v2_struct_0(A_176) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_191,plain,(
    ! [A_176] :
      ( m1_subset_1('#skF_6',u1_struct_0(A_176))
      | ~ m1_pre_topc(k2_tsep_1('#skF_3','#skF_4','#skF_5'),A_176)
      | v2_struct_0(k2_tsep_1('#skF_3','#skF_4','#skF_5'))
      | ~ l1_pre_topc(A_176)
      | v2_struct_0(A_176) ) ),
    inference(resolution,[status(thm)],[c_78,c_188])).

tff(c_225,plain,(
    v2_struct_0(k2_tsep_1('#skF_3','#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_191])).

tff(c_273,plain,(
    ! [A_237,B_238,C_239] :
      ( ~ v2_struct_0(k2_tsep_1(A_237,B_238,C_239))
      | ~ m1_pre_topc(C_239,A_237)
      | v2_struct_0(C_239)
      | ~ m1_pre_topc(B_238,A_237)
      | v2_struct_0(B_238)
      | ~ l1_pre_topc(A_237)
      | v2_struct_0(A_237) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_276,plain,
    ( ~ m1_pre_topc('#skF_5','#skF_3')
    | v2_struct_0('#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_225,c_273])).

tff(c_279,plain,
    ( v2_struct_0('#skF_5')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_86,c_82,c_276])).

tff(c_281,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_88,c_84,c_279])).

tff(c_331,plain,(
    ! [A_271] :
      ( m1_subset_1('#skF_6',u1_struct_0(A_271))
      | ~ m1_pre_topc(k2_tsep_1('#skF_3','#skF_4','#skF_5'),A_271)
      | ~ l1_pre_topc(A_271)
      | v2_struct_0(A_271) ) ),
    inference(splitRight,[status(thm)],[c_191])).

tff(c_76,plain,
    ( ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_131,plain,(
    ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_76])).

tff(c_336,plain,
    ( ~ m1_pre_topc(k2_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_331,c_131])).

tff(c_340,plain,
    ( ~ m1_pre_topc(k2_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_336])).

tff(c_341,plain,(
    ~ m1_pre_topc(k2_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_340])).

tff(c_714,plain,
    ( ~ v2_pre_topc('#skF_3')
    | r1_tsep_1('#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | v2_struct_0('#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_704,c_341])).

tff(c_727,plain,
    ( r1_tsep_1('#skF_4','#skF_5')
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_86,c_82,c_92,c_714])).

tff(c_729,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_88,c_84,c_80,c_727])).

tff(c_730,plain,(
    ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_956,plain,
    ( ~ m1_pre_topc(k2_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5')
    | ~ l1_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_951,c_730])).

tff(c_960,plain,
    ( ~ m1_pre_topc(k2_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_956])).

tff(c_961,plain,(
    ~ m1_pre_topc(k2_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_960])).

tff(c_1815,plain,
    ( ~ v2_pre_topc('#skF_3')
    | r1_tsep_1('#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | v2_struct_0('#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_1802,c_961])).

tff(c_1828,plain,
    ( r1_tsep_1('#skF_4','#skF_5')
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_86,c_82,c_92,c_1815])).

tff(c_1830,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_88,c_84,c_80,c_1828])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:47:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.26/1.98  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.26/1.99  
% 5.26/1.99  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.26/1.99  %$ r2_hidden > r1_tsep_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > l1_pre_topc > k4_enumset1 > k3_enumset1 > k2_enumset1 > k2_tsep_1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k1_setfam_1 > #skF_2 > #skF_5 > #skF_6 > #skF_3 > #skF_1 > #skF_4
% 5.26/1.99  
% 5.26/1.99  %Foreground sorts:
% 5.26/1.99  
% 5.26/1.99  
% 5.26/1.99  %Background operators:
% 5.26/1.99  
% 5.26/1.99  
% 5.26/1.99  %Foreground operators:
% 5.26/1.99  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 5.26/1.99  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.26/1.99  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.26/1.99  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i * $i * $i) > $i).
% 5.26/1.99  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 5.26/1.99  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 5.26/1.99  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.26/1.99  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.26/1.99  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.26/1.99  tff('#skF_5', type, '#skF_5': $i).
% 5.26/1.99  tff('#skF_6', type, '#skF_6': $i).
% 5.26/1.99  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.26/1.99  tff('#skF_3', type, '#skF_3': $i).
% 5.26/1.99  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i * $i * $i) > $i).
% 5.26/1.99  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.26/1.99  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 5.26/1.99  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.26/1.99  tff('#skF_4', type, '#skF_4': $i).
% 5.26/1.99  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.26/1.99  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 5.26/1.99  tff(k2_tsep_1, type, k2_tsep_1: ($i * $i * $i) > $i).
% 5.26/1.99  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 5.26/1.99  tff(r1_tsep_1, type, r1_tsep_1: ($i * $i) > $o).
% 5.26/1.99  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.26/1.99  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.26/1.99  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.26/1.99  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 5.26/1.99  
% 5.26/2.01  tff(f_192, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (~r1_tsep_1(B, C) => (![D]: (m1_subset_1(D, u1_struct_0(k2_tsep_1(A, B, C))) => ((?[E]: (m1_subset_1(E, u1_struct_0(B)) & (E = D))) & (?[E]: (m1_subset_1(E, u1_struct_0(C)) & (E = D))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_tmap_1)).
% 5.26/2.01  tff(f_142, axiom, (![A, B, C]: ((((((~v2_struct_0(A) & l1_pre_topc(A)) & ~v2_struct_0(B)) & m1_pre_topc(B, A)) & ~v2_struct_0(C)) & m1_pre_topc(C, A)) => ((~v2_struct_0(k2_tsep_1(A, B, C)) & v1_pre_topc(k2_tsep_1(A, B, C))) & m1_pre_topc(k2_tsep_1(A, B, C), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_tsep_1)).
% 5.26/2.01  tff(f_120, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (~r1_tsep_1(B, C) => (![D]: (((~v2_struct_0(D) & v1_pre_topc(D)) & m1_pre_topc(D, A)) => ((D = k2_tsep_1(A, B, C)) <=> (u1_struct_0(D) = k3_xboole_0(u1_struct_0(B), u1_struct_0(C))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_tsep_1)).
% 5.26/2.01  tff(f_29, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 5.26/2.01  tff(f_31, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 5.26/2.01  tff(f_33, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 5.26/2.01  tff(f_35, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 5.26/2.01  tff(f_59, axiom, (![A, B, C, D, E, F, G]: ((G = k4_enumset1(A, B, C, D, E, F)) <=> (![H]: (r2_hidden(H, G) <=> ~(((((~(H = A) & ~(H = B)) & ~(H = C)) & ~(H = D)) & ~(H = E)) & ~(H = F)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_enumset1)).
% 5.26/2.01  tff(f_61, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 5.26/2.01  tff(f_65, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(k1_setfam_1(B), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_setfam_1)).
% 5.26/2.01  tff(f_156, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_pre_topc(C, A) => (r1_tarski(u1_struct_0(B), u1_struct_0(C)) <=> m1_pre_topc(B, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_tsep_1)).
% 5.26/2.01  tff(f_72, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 5.26/2.01  tff(f_88, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(B)) => m1_subset_1(C, u1_struct_0(A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_pre_topc)).
% 5.26/2.01  tff(f_27, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 5.26/2.01  tff(c_94, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_192])).
% 5.26/2.01  tff(c_88, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_192])).
% 5.26/2.01  tff(c_84, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_192])).
% 5.26/2.01  tff(c_80, plain, (~r1_tsep_1('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_192])).
% 5.26/2.01  tff(c_90, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_192])).
% 5.26/2.01  tff(c_86, plain, (m1_pre_topc('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_192])).
% 5.26/2.01  tff(c_82, plain, (m1_pre_topc('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_192])).
% 5.26/2.01  tff(c_92, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_192])).
% 5.26/2.01  tff(c_66, plain, (![A_56, B_57, C_58]: (m1_pre_topc(k2_tsep_1(A_56, B_57, C_58), A_56) | ~m1_pre_topc(C_58, A_56) | v2_struct_0(C_58) | ~m1_pre_topc(B_57, A_56) | v2_struct_0(B_57) | ~l1_pre_topc(A_56) | v2_struct_0(A_56))), inference(cnfTransformation, [status(thm)], [f_142])).
% 5.26/2.01  tff(c_68, plain, (![A_56, B_57, C_58]: (v1_pre_topc(k2_tsep_1(A_56, B_57, C_58)) | ~m1_pre_topc(C_58, A_56) | v2_struct_0(C_58) | ~m1_pre_topc(B_57, A_56) | v2_struct_0(B_57) | ~l1_pre_topc(A_56) | v2_struct_0(A_56))), inference(cnfTransformation, [status(thm)], [f_142])).
% 5.26/2.01  tff(c_1586, plain, (![A_806, B_807, C_808]: (u1_struct_0(k2_tsep_1(A_806, B_807, C_808))=k3_xboole_0(u1_struct_0(B_807), u1_struct_0(C_808)) | ~m1_pre_topc(k2_tsep_1(A_806, B_807, C_808), A_806) | ~v1_pre_topc(k2_tsep_1(A_806, B_807, C_808)) | v2_struct_0(k2_tsep_1(A_806, B_807, C_808)) | r1_tsep_1(B_807, C_808) | ~m1_pre_topc(C_808, A_806) | v2_struct_0(C_808) | ~m1_pre_topc(B_807, A_806) | v2_struct_0(B_807) | ~l1_pre_topc(A_806) | v2_struct_0(A_806))), inference(cnfTransformation, [status(thm)], [f_120])).
% 5.26/2.01  tff(c_1590, plain, (![A_809, B_810, C_811]: (u1_struct_0(k2_tsep_1(A_809, B_810, C_811))=k3_xboole_0(u1_struct_0(B_810), u1_struct_0(C_811)) | ~v1_pre_topc(k2_tsep_1(A_809, B_810, C_811)) | v2_struct_0(k2_tsep_1(A_809, B_810, C_811)) | r1_tsep_1(B_810, C_811) | ~m1_pre_topc(C_811, A_809) | v2_struct_0(C_811) | ~m1_pre_topc(B_810, A_809) | v2_struct_0(B_810) | ~l1_pre_topc(A_809) | v2_struct_0(A_809))), inference(resolution, [status(thm)], [c_66, c_1586])).
% 5.26/2.01  tff(c_70, plain, (![A_56, B_57, C_58]: (~v2_struct_0(k2_tsep_1(A_56, B_57, C_58)) | ~m1_pre_topc(C_58, A_56) | v2_struct_0(C_58) | ~m1_pre_topc(B_57, A_56) | v2_struct_0(B_57) | ~l1_pre_topc(A_56) | v2_struct_0(A_56))), inference(cnfTransformation, [status(thm)], [f_142])).
% 5.26/2.01  tff(c_1663, plain, (![A_812, B_813, C_814]: (u1_struct_0(k2_tsep_1(A_812, B_813, C_814))=k3_xboole_0(u1_struct_0(B_813), u1_struct_0(C_814)) | ~v1_pre_topc(k2_tsep_1(A_812, B_813, C_814)) | r1_tsep_1(B_813, C_814) | ~m1_pre_topc(C_814, A_812) | v2_struct_0(C_814) | ~m1_pre_topc(B_813, A_812) | v2_struct_0(B_813) | ~l1_pre_topc(A_812) | v2_struct_0(A_812))), inference(resolution, [status(thm)], [c_1590, c_70])).
% 5.26/2.01  tff(c_1667, plain, (![A_815, B_816, C_817]: (u1_struct_0(k2_tsep_1(A_815, B_816, C_817))=k3_xboole_0(u1_struct_0(B_816), u1_struct_0(C_817)) | r1_tsep_1(B_816, C_817) | ~m1_pre_topc(C_817, A_815) | v2_struct_0(C_817) | ~m1_pre_topc(B_816, A_815) | v2_struct_0(B_816) | ~l1_pre_topc(A_815) | v2_struct_0(A_815))), inference(resolution, [status(thm)], [c_68, c_1663])).
% 5.26/2.01  tff(c_4, plain, (![A_3, B_4]: (k1_enumset1(A_3, A_3, B_4)=k2_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.26/2.01  tff(c_6, plain, (![A_5, B_6, C_7]: (k2_enumset1(A_5, A_5, B_6, C_7)=k1_enumset1(A_5, B_6, C_7))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.26/2.01  tff(c_8, plain, (![A_8, B_9, C_10, D_11]: (k3_enumset1(A_8, A_8, B_9, C_10, D_11)=k2_enumset1(A_8, B_9, C_10, D_11))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.26/2.01  tff(c_757, plain, (![C_471, B_467, D_470, E_469, A_468]: (k4_enumset1(A_468, A_468, B_467, C_471, D_470, E_469)=k3_enumset1(A_468, B_467, C_471, D_470, E_469))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.26/2.01  tff(c_14, plain, (![E_21, D_20, C_19, H_26, B_18, A_17]: (r2_hidden(H_26, k4_enumset1(A_17, B_18, C_19, D_20, E_21, H_26)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.26/2.01  tff(c_784, plain, (![E_472, A_476, D_475, C_473, B_474]: (r2_hidden(E_472, k3_enumset1(A_476, B_474, C_473, D_475, E_472)))), inference(superposition, [status(thm), theory('equality')], [c_757, c_14])).
% 5.26/2.01  tff(c_788, plain, (![D_477, A_478, B_479, C_480]: (r2_hidden(D_477, k2_enumset1(A_478, B_479, C_480, D_477)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_784])).
% 5.26/2.01  tff(c_801, plain, (![C_484, A_485, B_486]: (r2_hidden(C_484, k1_enumset1(A_485, B_486, C_484)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_788])).
% 5.26/2.01  tff(c_805, plain, (![B_487, A_488]: (r2_hidden(B_487, k2_tarski(A_488, B_487)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_801])).
% 5.26/2.01  tff(c_54, plain, (![A_27, B_28]: (k1_setfam_1(k2_tarski(A_27, B_28))=k3_xboole_0(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.26/2.01  tff(c_127, plain, (![B_117, A_118]: (r1_tarski(k1_setfam_1(B_117), A_118) | ~r2_hidden(A_118, B_117))), inference(cnfTransformation, [status(thm)], [f_65])).
% 5.26/2.01  tff(c_130, plain, (![A_27, B_28, A_118]: (r1_tarski(k3_xboole_0(A_27, B_28), A_118) | ~r2_hidden(A_118, k2_tarski(A_27, B_28)))), inference(superposition, [status(thm), theory('equality')], [c_54, c_127])).
% 5.26/2.01  tff(c_809, plain, (![A_488, B_487]: (r1_tarski(k3_xboole_0(A_488, B_487), B_487))), inference(resolution, [status(thm)], [c_805, c_130])).
% 5.26/2.01  tff(c_1747, plain, (![A_824, B_825, C_826]: (r1_tarski(u1_struct_0(k2_tsep_1(A_824, B_825, C_826)), u1_struct_0(C_826)) | r1_tsep_1(B_825, C_826) | ~m1_pre_topc(C_826, A_824) | v2_struct_0(C_826) | ~m1_pre_topc(B_825, A_824) | v2_struct_0(B_825) | ~l1_pre_topc(A_824) | v2_struct_0(A_824))), inference(superposition, [status(thm), theory('equality')], [c_1667, c_809])).
% 5.26/2.01  tff(c_74, plain, (![B_63, C_65, A_59]: (m1_pre_topc(B_63, C_65) | ~r1_tarski(u1_struct_0(B_63), u1_struct_0(C_65)) | ~m1_pre_topc(C_65, A_59) | ~m1_pre_topc(B_63, A_59) | ~l1_pre_topc(A_59) | ~v2_pre_topc(A_59))), inference(cnfTransformation, [status(thm)], [f_156])).
% 5.26/2.01  tff(c_1789, plain, (![A_841, B_842, C_843, A_844]: (m1_pre_topc(k2_tsep_1(A_841, B_842, C_843), C_843) | ~m1_pre_topc(C_843, A_844) | ~m1_pre_topc(k2_tsep_1(A_841, B_842, C_843), A_844) | ~l1_pre_topc(A_844) | ~v2_pre_topc(A_844) | r1_tsep_1(B_842, C_843) | ~m1_pre_topc(C_843, A_841) | v2_struct_0(C_843) | ~m1_pre_topc(B_842, A_841) | v2_struct_0(B_842) | ~l1_pre_topc(A_841) | v2_struct_0(A_841))), inference(resolution, [status(thm)], [c_1747, c_74])).
% 5.26/2.01  tff(c_1802, plain, (![A_845, B_846, C_847]: (m1_pre_topc(k2_tsep_1(A_845, B_846, C_847), C_847) | ~v2_pre_topc(A_845) | r1_tsep_1(B_846, C_847) | ~m1_pre_topc(C_847, A_845) | v2_struct_0(C_847) | ~m1_pre_topc(B_846, A_845) | v2_struct_0(B_846) | ~l1_pre_topc(A_845) | v2_struct_0(A_845))), inference(resolution, [status(thm)], [c_66, c_1789])).
% 5.26/2.01  tff(c_114, plain, (![B_115, A_116]: (l1_pre_topc(B_115) | ~m1_pre_topc(B_115, A_116) | ~l1_pre_topc(A_116))), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.26/2.01  tff(c_120, plain, (l1_pre_topc('#skF_5') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_82, c_114])).
% 5.26/2.01  tff(c_126, plain, (l1_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_120])).
% 5.26/2.01  tff(c_78, plain, (m1_subset_1('#skF_6', u1_struct_0(k2_tsep_1('#skF_3', '#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_192])).
% 5.26/2.01  tff(c_792, plain, (![C_481, A_482, B_483]: (m1_subset_1(C_481, u1_struct_0(A_482)) | ~m1_subset_1(C_481, u1_struct_0(B_483)) | ~m1_pre_topc(B_483, A_482) | v2_struct_0(B_483) | ~l1_pre_topc(A_482) | v2_struct_0(A_482))), inference(cnfTransformation, [status(thm)], [f_88])).
% 5.26/2.01  tff(c_800, plain, (![A_482]: (m1_subset_1('#skF_6', u1_struct_0(A_482)) | ~m1_pre_topc(k2_tsep_1('#skF_3', '#skF_4', '#skF_5'), A_482) | v2_struct_0(k2_tsep_1('#skF_3', '#skF_4', '#skF_5')) | ~l1_pre_topc(A_482) | v2_struct_0(A_482))), inference(resolution, [status(thm)], [c_78, c_792])).
% 5.26/2.01  tff(c_851, plain, (v2_struct_0(k2_tsep_1('#skF_3', '#skF_4', '#skF_5'))), inference(splitLeft, [status(thm)], [c_800])).
% 5.26/2.01  tff(c_903, plain, (![A_542, B_543, C_544]: (~v2_struct_0(k2_tsep_1(A_542, B_543, C_544)) | ~m1_pre_topc(C_544, A_542) | v2_struct_0(C_544) | ~m1_pre_topc(B_543, A_542) | v2_struct_0(B_543) | ~l1_pre_topc(A_542) | v2_struct_0(A_542))), inference(cnfTransformation, [status(thm)], [f_142])).
% 5.26/2.01  tff(c_906, plain, (~m1_pre_topc('#skF_5', '#skF_3') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_3') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_851, c_903])).
% 5.26/2.01  tff(c_909, plain, (v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_86, c_82, c_906])).
% 5.26/2.01  tff(c_911, plain, $false, inference(negUnitSimplification, [status(thm)], [c_94, c_88, c_84, c_909])).
% 5.26/2.01  tff(c_951, plain, (![A_567]: (m1_subset_1('#skF_6', u1_struct_0(A_567)) | ~m1_pre_topc(k2_tsep_1('#skF_3', '#skF_4', '#skF_5'), A_567) | ~l1_pre_topc(A_567) | v2_struct_0(A_567))), inference(splitRight, [status(thm)], [c_800])).
% 5.26/2.01  tff(c_531, plain, (![A_379, B_380, C_381]: (u1_struct_0(k2_tsep_1(A_379, B_380, C_381))=k3_xboole_0(u1_struct_0(B_380), u1_struct_0(C_381)) | ~m1_pre_topc(k2_tsep_1(A_379, B_380, C_381), A_379) | ~v1_pre_topc(k2_tsep_1(A_379, B_380, C_381)) | v2_struct_0(k2_tsep_1(A_379, B_380, C_381)) | r1_tsep_1(B_380, C_381) | ~m1_pre_topc(C_381, A_379) | v2_struct_0(C_381) | ~m1_pre_topc(B_380, A_379) | v2_struct_0(B_380) | ~l1_pre_topc(A_379) | v2_struct_0(A_379))), inference(cnfTransformation, [status(thm)], [f_120])).
% 5.26/2.01  tff(c_536, plain, (![A_389, B_390, C_391]: (u1_struct_0(k2_tsep_1(A_389, B_390, C_391))=k3_xboole_0(u1_struct_0(B_390), u1_struct_0(C_391)) | ~v1_pre_topc(k2_tsep_1(A_389, B_390, C_391)) | v2_struct_0(k2_tsep_1(A_389, B_390, C_391)) | r1_tsep_1(B_390, C_391) | ~m1_pre_topc(C_391, A_389) | v2_struct_0(C_391) | ~m1_pre_topc(B_390, A_389) | v2_struct_0(B_390) | ~l1_pre_topc(A_389) | v2_struct_0(A_389))), inference(resolution, [status(thm)], [c_66, c_531])).
% 5.26/2.01  tff(c_603, plain, (![A_392, B_393, C_394]: (u1_struct_0(k2_tsep_1(A_392, B_393, C_394))=k3_xboole_0(u1_struct_0(B_393), u1_struct_0(C_394)) | ~v1_pre_topc(k2_tsep_1(A_392, B_393, C_394)) | r1_tsep_1(B_393, C_394) | ~m1_pre_topc(C_394, A_392) | v2_struct_0(C_394) | ~m1_pre_topc(B_393, A_392) | v2_struct_0(B_393) | ~l1_pre_topc(A_392) | v2_struct_0(A_392))), inference(resolution, [status(thm)], [c_536, c_70])).
% 5.26/2.01  tff(c_607, plain, (![A_395, B_396, C_397]: (u1_struct_0(k2_tsep_1(A_395, B_396, C_397))=k3_xboole_0(u1_struct_0(B_396), u1_struct_0(C_397)) | r1_tsep_1(B_396, C_397) | ~m1_pre_topc(C_397, A_395) | v2_struct_0(C_397) | ~m1_pre_topc(B_396, A_395) | v2_struct_0(B_396) | ~l1_pre_topc(A_395) | v2_struct_0(A_395))), inference(resolution, [status(thm)], [c_68, c_603])).
% 5.26/2.01  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k3_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.26/2.01  tff(c_669, plain, (![A_398, B_399, C_400]: (r1_tarski(u1_struct_0(k2_tsep_1(A_398, B_399, C_400)), u1_struct_0(B_399)) | r1_tsep_1(B_399, C_400) | ~m1_pre_topc(C_400, A_398) | v2_struct_0(C_400) | ~m1_pre_topc(B_399, A_398) | v2_struct_0(B_399) | ~l1_pre_topc(A_398) | v2_struct_0(A_398))), inference(superposition, [status(thm), theory('equality')], [c_607, c_2])).
% 5.26/2.01  tff(c_692, plain, (![A_411, B_412, C_413, A_414]: (m1_pre_topc(k2_tsep_1(A_411, B_412, C_413), B_412) | ~m1_pre_topc(B_412, A_414) | ~m1_pre_topc(k2_tsep_1(A_411, B_412, C_413), A_414) | ~l1_pre_topc(A_414) | ~v2_pre_topc(A_414) | r1_tsep_1(B_412, C_413) | ~m1_pre_topc(C_413, A_411) | v2_struct_0(C_413) | ~m1_pre_topc(B_412, A_411) | v2_struct_0(B_412) | ~l1_pre_topc(A_411) | v2_struct_0(A_411))), inference(resolution, [status(thm)], [c_669, c_74])).
% 5.26/2.01  tff(c_704, plain, (![A_418, B_419, C_420]: (m1_pre_topc(k2_tsep_1(A_418, B_419, C_420), B_419) | ~v2_pre_topc(A_418) | r1_tsep_1(B_419, C_420) | ~m1_pre_topc(C_420, A_418) | v2_struct_0(C_420) | ~m1_pre_topc(B_419, A_418) | v2_struct_0(B_419) | ~l1_pre_topc(A_418) | v2_struct_0(A_418))), inference(resolution, [status(thm)], [c_66, c_692])).
% 5.26/2.01  tff(c_117, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_86, c_114])).
% 5.26/2.01  tff(c_123, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_117])).
% 5.26/2.01  tff(c_188, plain, (![C_175, A_176, B_177]: (m1_subset_1(C_175, u1_struct_0(A_176)) | ~m1_subset_1(C_175, u1_struct_0(B_177)) | ~m1_pre_topc(B_177, A_176) | v2_struct_0(B_177) | ~l1_pre_topc(A_176) | v2_struct_0(A_176))), inference(cnfTransformation, [status(thm)], [f_88])).
% 5.26/2.01  tff(c_191, plain, (![A_176]: (m1_subset_1('#skF_6', u1_struct_0(A_176)) | ~m1_pre_topc(k2_tsep_1('#skF_3', '#skF_4', '#skF_5'), A_176) | v2_struct_0(k2_tsep_1('#skF_3', '#skF_4', '#skF_5')) | ~l1_pre_topc(A_176) | v2_struct_0(A_176))), inference(resolution, [status(thm)], [c_78, c_188])).
% 5.26/2.01  tff(c_225, plain, (v2_struct_0(k2_tsep_1('#skF_3', '#skF_4', '#skF_5'))), inference(splitLeft, [status(thm)], [c_191])).
% 5.26/2.01  tff(c_273, plain, (![A_237, B_238, C_239]: (~v2_struct_0(k2_tsep_1(A_237, B_238, C_239)) | ~m1_pre_topc(C_239, A_237) | v2_struct_0(C_239) | ~m1_pre_topc(B_238, A_237) | v2_struct_0(B_238) | ~l1_pre_topc(A_237) | v2_struct_0(A_237))), inference(cnfTransformation, [status(thm)], [f_142])).
% 5.26/2.01  tff(c_276, plain, (~m1_pre_topc('#skF_5', '#skF_3') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_3') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_225, c_273])).
% 5.26/2.01  tff(c_279, plain, (v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_86, c_82, c_276])).
% 5.26/2.01  tff(c_281, plain, $false, inference(negUnitSimplification, [status(thm)], [c_94, c_88, c_84, c_279])).
% 5.26/2.01  tff(c_331, plain, (![A_271]: (m1_subset_1('#skF_6', u1_struct_0(A_271)) | ~m1_pre_topc(k2_tsep_1('#skF_3', '#skF_4', '#skF_5'), A_271) | ~l1_pre_topc(A_271) | v2_struct_0(A_271))), inference(splitRight, [status(thm)], [c_191])).
% 5.26/2.01  tff(c_76, plain, (~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_192])).
% 5.26/2.01  tff(c_131, plain, (~m1_subset_1('#skF_6', u1_struct_0('#skF_4'))), inference(splitLeft, [status(thm)], [c_76])).
% 5.26/2.01  tff(c_336, plain, (~m1_pre_topc(k2_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4') | ~l1_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_331, c_131])).
% 5.26/2.01  tff(c_340, plain, (~m1_pre_topc(k2_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_123, c_336])).
% 5.26/2.01  tff(c_341, plain, (~m1_pre_topc(k2_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_88, c_340])).
% 5.26/2.01  tff(c_714, plain, (~v2_pre_topc('#skF_3') | r1_tsep_1('#skF_4', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_3') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_3') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_704, c_341])).
% 5.26/2.01  tff(c_727, plain, (r1_tsep_1('#skF_4', '#skF_5') | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_86, c_82, c_92, c_714])).
% 5.26/2.01  tff(c_729, plain, $false, inference(negUnitSimplification, [status(thm)], [c_94, c_88, c_84, c_80, c_727])).
% 5.26/2.01  tff(c_730, plain, (~m1_subset_1('#skF_6', u1_struct_0('#skF_5'))), inference(splitRight, [status(thm)], [c_76])).
% 5.26/2.01  tff(c_956, plain, (~m1_pre_topc(k2_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5') | ~l1_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_951, c_730])).
% 5.26/2.01  tff(c_960, plain, (~m1_pre_topc(k2_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_126, c_956])).
% 5.26/2.01  tff(c_961, plain, (~m1_pre_topc(k2_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_84, c_960])).
% 5.26/2.01  tff(c_1815, plain, (~v2_pre_topc('#skF_3') | r1_tsep_1('#skF_4', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_3') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_3') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_1802, c_961])).
% 5.26/2.01  tff(c_1828, plain, (r1_tsep_1('#skF_4', '#skF_5') | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_86, c_82, c_92, c_1815])).
% 5.26/2.01  tff(c_1830, plain, $false, inference(negUnitSimplification, [status(thm)], [c_94, c_88, c_84, c_80, c_1828])).
% 5.26/2.01  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.26/2.01  
% 5.26/2.01  Inference rules
% 5.26/2.01  ----------------------
% 5.26/2.01  #Ref     : 0
% 5.26/2.01  #Sup     : 414
% 5.26/2.01  #Fact    : 0
% 5.26/2.01  #Define  : 0
% 5.26/2.01  #Split   : 8
% 5.26/2.01  #Chain   : 0
% 5.26/2.01  #Close   : 0
% 5.26/2.01  
% 5.26/2.01  Ordering : KBO
% 5.26/2.01  
% 5.26/2.01  Simplification rules
% 5.26/2.01  ----------------------
% 5.26/2.01  #Subsume      : 28
% 5.26/2.01  #Demod        : 103
% 5.26/2.01  #Tautology    : 125
% 5.26/2.01  #SimpNegUnit  : 28
% 5.26/2.01  #BackRed      : 0
% 5.26/2.01  
% 5.26/2.01  #Partial instantiations: 0
% 5.26/2.01  #Strategies tried      : 1
% 5.26/2.01  
% 5.26/2.01  Timing (in seconds)
% 5.26/2.01  ----------------------
% 5.26/2.01  Preprocessing        : 0.36
% 5.26/2.01  Parsing              : 0.17
% 5.26/2.01  CNF conversion       : 0.03
% 5.26/2.01  Main loop            : 0.81
% 5.26/2.01  Inferencing          : 0.30
% 5.26/2.01  Reduction            : 0.21
% 5.26/2.01  Demodulation         : 0.15
% 5.26/2.01  BG Simplification    : 0.04
% 5.26/2.01  Subsumption          : 0.20
% 5.26/2.01  Abstraction          : 0.04
% 5.26/2.01  MUC search           : 0.00
% 5.26/2.01  Cooper               : 0.00
% 5.26/2.01  Total                : 1.21
% 5.26/2.01  Index Insertion      : 0.00
% 5.26/2.01  Index Deletion       : 0.00
% 5.26/2.01  Index Matching       : 0.00
% 5.26/2.01  BG Taut test         : 0.00
%------------------------------------------------------------------------------
