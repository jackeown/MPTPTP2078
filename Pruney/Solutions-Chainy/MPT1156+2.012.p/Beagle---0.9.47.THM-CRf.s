%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:39 EST 2020

% Result     : Theorem 3.79s
% Output     : CNFRefutation 3.96s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 162 expanded)
%              Number of leaves         :   44 (  78 expanded)
%              Depth                    :   10
%              Number of atoms          :  157 ( 440 expanded)
%              Number of equality atoms :   27 (  34 expanded)
%              Maximal formula depth    :   22 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v6_orders_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_orders_2 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k6_domain_1 > k2_tarski > k2_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_3 > #skF_1 > #skF_5 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k2_orders_2,type,(
    k2_orders_2: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v6_orders_2,type,(
    v6_orders_2: ( $i * $i ) > $o )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_164,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ~ r2_hidden(B,k2_orders_2(A,k6_domain_1(u1_struct_0(A),B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_orders_2)).

tff(f_110,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_124,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ( v6_orders_2(k6_domain_1(u1_struct_0(A),B),A)
            & m1_subset_1(k6_domain_1(u1_struct_0(A),B),k1_zfmisc_1(u1_struct_0(A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_orders_2)).

tff(f_103,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_orders_2(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_orders_2)).

tff(f_82,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_33,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_35,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_41,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_43,axiom,(
    ! [A,B,C,D,E,F] : k5_enumset1(A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

tff(f_45,axiom,(
    ! [A,B,C,D,E,F,G] : k6_enumset1(A,A,B,C,D,E,F,G) = k5_enumset1(A,B,C,D,E,F,G) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

tff(f_75,axiom,(
    ! [A,B,C,D,E,F,G,H,I] :
      ( I = k6_enumset1(A,B,C,D,E,F,G,H)
    <=> ! [J] :
          ( r2_hidden(J,I)
        <=> ~ ( J != A
              & J != B
              & J != C
              & J != D
              & J != E
              & J != F
              & J != G
              & J != H ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_enumset1)).

tff(f_146,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ~ ( r2_hidden(B,C)
                  & r2_hidden(B,k2_orders_2(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_orders_2)).

tff(c_100,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_98,plain,(
    v3_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_96,plain,(
    v4_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_94,plain,(
    v5_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_92,plain,(
    l1_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_90,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_138,plain,(
    ! [A_76,B_77] :
      ( k6_domain_1(A_76,B_77) = k1_tarski(B_77)
      | ~ m1_subset_1(B_77,A_76)
      | v1_xboole_0(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_142,plain,
    ( k6_domain_1(u1_struct_0('#skF_4'),'#skF_5') = k1_tarski('#skF_5')
    | v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_90,c_138])).

tff(c_143,plain,(
    v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_142])).

tff(c_82,plain,(
    ! [A_56,B_58] :
      ( m1_subset_1(k6_domain_1(u1_struct_0(A_56),B_58),k1_zfmisc_1(u1_struct_0(A_56)))
      | ~ m1_subset_1(B_58,u1_struct_0(A_56))
      | ~ l1_orders_2(A_56)
      | ~ v3_orders_2(A_56)
      | v2_struct_0(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_352,plain,(
    ! [A_261,B_262] :
      ( m1_subset_1(k2_orders_2(A_261,B_262),k1_zfmisc_1(u1_struct_0(A_261)))
      | ~ m1_subset_1(B_262,k1_zfmisc_1(u1_struct_0(A_261)))
      | ~ l1_orders_2(A_261)
      | ~ v5_orders_2(A_261)
      | ~ v4_orders_2(A_261)
      | ~ v3_orders_2(A_261)
      | v2_struct_0(A_261) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_88,plain,(
    r2_hidden('#skF_5',k2_orders_2('#skF_4',k6_domain_1(u1_struct_0('#skF_4'),'#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_145,plain,(
    ! [C_81,A_82,B_83] :
      ( r2_hidden(C_81,A_82)
      | ~ r2_hidden(C_81,B_83)
      | ~ m1_subset_1(B_83,k1_zfmisc_1(A_82)) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_150,plain,(
    ! [A_82] :
      ( r2_hidden('#skF_5',A_82)
      | ~ m1_subset_1(k2_orders_2('#skF_4',k6_domain_1(u1_struct_0('#skF_4'),'#skF_5')),k1_zfmisc_1(A_82)) ) ),
    inference(resolution,[status(thm)],[c_88,c_145])).

tff(c_361,plain,
    ( r2_hidden('#skF_5',u1_struct_0('#skF_4'))
    | ~ m1_subset_1(k6_domain_1(u1_struct_0('#skF_4'),'#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ l1_orders_2('#skF_4')
    | ~ v5_orders_2('#skF_4')
    | ~ v4_orders_2('#skF_4')
    | ~ v3_orders_2('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_352,c_150])).

tff(c_371,plain,
    ( r2_hidden('#skF_5',u1_struct_0('#skF_4'))
    | ~ m1_subset_1(k6_domain_1(u1_struct_0('#skF_4'),'#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_96,c_94,c_92,c_361])).

tff(c_372,plain,
    ( r2_hidden('#skF_5',u1_struct_0('#skF_4'))
    | ~ m1_subset_1(k6_domain_1(u1_struct_0('#skF_4'),'#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_100,c_371])).

tff(c_458,plain,(
    ~ m1_subset_1(k6_domain_1(u1_struct_0('#skF_4'),'#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_372])).

tff(c_461,plain,
    ( ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ l1_orders_2('#skF_4')
    | ~ v3_orders_2('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_82,c_458])).

tff(c_464,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_92,c_90,c_461])).

tff(c_466,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_100,c_464])).

tff(c_467,plain,(
    r2_hidden('#skF_5',u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_372])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_473,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_467,c_2])).

tff(c_478,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_143,c_473])).

tff(c_479,plain,(
    k6_domain_1(u1_struct_0('#skF_4'),'#skF_5') = k1_tarski('#skF_5') ),
    inference(splitRight,[status(thm)],[c_142])).

tff(c_671,plain,(
    ! [A_454,B_455] :
      ( m1_subset_1(k6_domain_1(u1_struct_0(A_454),B_455),k1_zfmisc_1(u1_struct_0(A_454)))
      | ~ m1_subset_1(B_455,u1_struct_0(A_454))
      | ~ l1_orders_2(A_454)
      | ~ v3_orders_2(A_454)
      | v2_struct_0(A_454) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_684,plain,
    ( m1_subset_1(k1_tarski('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ l1_orders_2('#skF_4')
    | ~ v3_orders_2('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_479,c_671])).

tff(c_690,plain,
    ( m1_subset_1(k1_tarski('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_92,c_90,c_684])).

tff(c_691,plain,(
    m1_subset_1(k1_tarski('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_100,c_690])).

tff(c_6,plain,(
    ! [A_5] : k2_tarski(A_5,A_5) = k1_tarski(A_5) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_8,plain,(
    ! [A_6,B_7] : k1_enumset1(A_6,A_6,B_7) = k2_tarski(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_10,plain,(
    ! [A_8,B_9,C_10] : k2_enumset1(A_8,A_8,B_9,C_10) = k1_enumset1(A_8,B_9,C_10) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_12,plain,(
    ! [A_11,B_12,C_13,D_14] : k3_enumset1(A_11,A_11,B_12,C_13,D_14) = k2_enumset1(A_11,B_12,C_13,D_14) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_14,plain,(
    ! [B_16,A_15,D_18,E_19,C_17] : k4_enumset1(A_15,A_15,B_16,C_17,D_18,E_19) = k3_enumset1(A_15,B_16,C_17,D_18,E_19) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_16,plain,(
    ! [C_22,D_23,A_20,B_21,F_25,E_24] : k5_enumset1(A_20,A_20,B_21,C_22,D_23,E_24,F_25) = k4_enumset1(A_20,B_21,C_22,D_23,E_24,F_25) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_612,plain,(
    ! [A_424,F_425,E_427,C_426,G_428,B_423,D_422] : k6_enumset1(A_424,A_424,B_423,C_426,D_422,E_427,F_425,G_428) = k5_enumset1(A_424,B_423,C_426,D_422,E_427,F_425,G_428) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_36,plain,(
    ! [D_36,G_39,J_44,F_38,E_37,B_34,H_40,C_35] : r2_hidden(J_44,k6_enumset1(J_44,B_34,C_35,D_36,E_37,F_38,G_39,H_40)) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_730,plain,(
    ! [D_463,E_460,G_464,A_466,F_461,B_465,C_462] : r2_hidden(A_466,k5_enumset1(A_466,B_465,C_462,D_463,E_460,F_461,G_464)) ),
    inference(superposition,[status(thm),theory(equality)],[c_612,c_36])).

tff(c_741,plain,(
    ! [C_467,B_468,A_471,D_469,E_470,F_472] : r2_hidden(A_471,k4_enumset1(A_471,B_468,C_467,D_469,E_470,F_472)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_730])).

tff(c_752,plain,(
    ! [E_476,B_475,D_474,C_473,A_477] : r2_hidden(A_477,k3_enumset1(A_477,B_475,C_473,D_474,E_476)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_741])).

tff(c_763,plain,(
    ! [A_478,B_479,C_480,D_481] : r2_hidden(A_478,k2_enumset1(A_478,B_479,C_480,D_481)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_752])).

tff(c_804,plain,(
    ! [A_484,B_485,C_486] : r2_hidden(A_484,k1_enumset1(A_484,B_485,C_486)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_763])).

tff(c_815,plain,(
    ! [A_487,B_488] : r2_hidden(A_487,k2_tarski(A_487,B_488)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_804])).

tff(c_823,plain,(
    ! [A_5] : r2_hidden(A_5,k1_tarski(A_5)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_815])).

tff(c_482,plain,(
    r2_hidden('#skF_5',k2_orders_2('#skF_4',k1_tarski('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_479,c_88])).

tff(c_873,plain,(
    ! [B_509,A_510,C_511] :
      ( ~ r2_hidden(B_509,k2_orders_2(A_510,C_511))
      | ~ r2_hidden(B_509,C_511)
      | ~ m1_subset_1(C_511,k1_zfmisc_1(u1_struct_0(A_510)))
      | ~ m1_subset_1(B_509,u1_struct_0(A_510))
      | ~ l1_orders_2(A_510)
      | ~ v5_orders_2(A_510)
      | ~ v4_orders_2(A_510)
      | ~ v3_orders_2(A_510)
      | v2_struct_0(A_510) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_878,plain,
    ( ~ r2_hidden('#skF_5',k1_tarski('#skF_5'))
    | ~ m1_subset_1(k1_tarski('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ l1_orders_2('#skF_4')
    | ~ v5_orders_2('#skF_4')
    | ~ v4_orders_2('#skF_4')
    | ~ v3_orders_2('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_482,c_873])).

tff(c_885,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_96,c_94,c_92,c_90,c_691,c_823,c_878])).

tff(c_887,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_100,c_885])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:41:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.79/1.55  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.79/1.55  
% 3.79/1.55  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.79/1.55  %$ v6_orders_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_orders_2 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k6_domain_1 > k2_tarski > k2_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_3 > #skF_1 > #skF_5 > #skF_2 > #skF_4
% 3.79/1.55  
% 3.79/1.55  %Foreground sorts:
% 3.79/1.55  
% 3.79/1.55  
% 3.79/1.55  %Background operators:
% 3.79/1.55  
% 3.79/1.55  
% 3.79/1.55  %Foreground operators:
% 3.79/1.55  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.79/1.55  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 3.79/1.55  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.79/1.55  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.79/1.55  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.79/1.55  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.79/1.55  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.79/1.55  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.79/1.55  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 3.79/1.55  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.79/1.55  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.79/1.55  tff(k2_orders_2, type, k2_orders_2: ($i * $i) > $i).
% 3.79/1.55  tff('#skF_5', type, '#skF_5': $i).
% 3.79/1.55  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.79/1.55  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.79/1.55  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 3.79/1.55  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.79/1.55  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 3.79/1.55  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.79/1.55  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.79/1.55  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 3.79/1.55  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.79/1.55  tff('#skF_4', type, '#skF_4': $i).
% 3.79/1.55  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.79/1.55  tff(v6_orders_2, type, v6_orders_2: ($i * $i) > $o).
% 3.79/1.55  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.79/1.55  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.79/1.55  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.79/1.55  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.79/1.55  
% 3.96/1.57  tff(f_164, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => ~r2_hidden(B, k2_orders_2(A, k6_domain_1(u1_struct_0(A), B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_orders_2)).
% 3.96/1.57  tff(f_110, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 3.96/1.57  tff(f_124, axiom, (![A]: (((~v2_struct_0(A) & v3_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (v6_orders_2(k6_domain_1(u1_struct_0(A), B), A) & m1_subset_1(k6_domain_1(u1_struct_0(A), B), k1_zfmisc_1(u1_struct_0(A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_orders_2)).
% 3.96/1.57  tff(f_103, axiom, (![A, B]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_orders_2(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_orders_2)).
% 3.96/1.57  tff(f_82, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 3.96/1.57  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.96/1.57  tff(f_33, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 3.96/1.57  tff(f_35, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 3.96/1.57  tff(f_37, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 3.96/1.57  tff(f_39, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 3.96/1.57  tff(f_41, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 3.96/1.57  tff(f_43, axiom, (![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 3.96/1.57  tff(f_45, axiom, (![A, B, C, D, E, F, G]: (k6_enumset1(A, A, B, C, D, E, F, G) = k5_enumset1(A, B, C, D, E, F, G))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_enumset1)).
% 3.96/1.57  tff(f_75, axiom, (![A, B, C, D, E, F, G, H, I]: ((I = k6_enumset1(A, B, C, D, E, F, G, H)) <=> (![J]: (r2_hidden(J, I) <=> ~(((((((~(J = A) & ~(J = B)) & ~(J = C)) & ~(J = D)) & ~(J = E)) & ~(J = F)) & ~(J = G)) & ~(J = H)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_enumset1)).
% 3.96/1.57  tff(f_146, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r2_hidden(B, C) & r2_hidden(B, k2_orders_2(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_orders_2)).
% 3.96/1.57  tff(c_100, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_164])).
% 3.96/1.57  tff(c_98, plain, (v3_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_164])).
% 3.96/1.57  tff(c_96, plain, (v4_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_164])).
% 3.96/1.57  tff(c_94, plain, (v5_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_164])).
% 3.96/1.57  tff(c_92, plain, (l1_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_164])).
% 3.96/1.57  tff(c_90, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_164])).
% 3.96/1.57  tff(c_138, plain, (![A_76, B_77]: (k6_domain_1(A_76, B_77)=k1_tarski(B_77) | ~m1_subset_1(B_77, A_76) | v1_xboole_0(A_76))), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.96/1.57  tff(c_142, plain, (k6_domain_1(u1_struct_0('#skF_4'), '#skF_5')=k1_tarski('#skF_5') | v1_xboole_0(u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_90, c_138])).
% 3.96/1.57  tff(c_143, plain, (v1_xboole_0(u1_struct_0('#skF_4'))), inference(splitLeft, [status(thm)], [c_142])).
% 3.96/1.57  tff(c_82, plain, (![A_56, B_58]: (m1_subset_1(k6_domain_1(u1_struct_0(A_56), B_58), k1_zfmisc_1(u1_struct_0(A_56))) | ~m1_subset_1(B_58, u1_struct_0(A_56)) | ~l1_orders_2(A_56) | ~v3_orders_2(A_56) | v2_struct_0(A_56))), inference(cnfTransformation, [status(thm)], [f_124])).
% 3.96/1.57  tff(c_352, plain, (![A_261, B_262]: (m1_subset_1(k2_orders_2(A_261, B_262), k1_zfmisc_1(u1_struct_0(A_261))) | ~m1_subset_1(B_262, k1_zfmisc_1(u1_struct_0(A_261))) | ~l1_orders_2(A_261) | ~v5_orders_2(A_261) | ~v4_orders_2(A_261) | ~v3_orders_2(A_261) | v2_struct_0(A_261))), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.96/1.57  tff(c_88, plain, (r2_hidden('#skF_5', k2_orders_2('#skF_4', k6_domain_1(u1_struct_0('#skF_4'), '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_164])).
% 3.96/1.57  tff(c_145, plain, (![C_81, A_82, B_83]: (r2_hidden(C_81, A_82) | ~r2_hidden(C_81, B_83) | ~m1_subset_1(B_83, k1_zfmisc_1(A_82)))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.96/1.57  tff(c_150, plain, (![A_82]: (r2_hidden('#skF_5', A_82) | ~m1_subset_1(k2_orders_2('#skF_4', k6_domain_1(u1_struct_0('#skF_4'), '#skF_5')), k1_zfmisc_1(A_82)))), inference(resolution, [status(thm)], [c_88, c_145])).
% 3.96/1.57  tff(c_361, plain, (r2_hidden('#skF_5', u1_struct_0('#skF_4')) | ~m1_subset_1(k6_domain_1(u1_struct_0('#skF_4'), '#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_352, c_150])).
% 3.96/1.57  tff(c_371, plain, (r2_hidden('#skF_5', u1_struct_0('#skF_4')) | ~m1_subset_1(k6_domain_1(u1_struct_0('#skF_4'), '#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_98, c_96, c_94, c_92, c_361])).
% 3.96/1.57  tff(c_372, plain, (r2_hidden('#skF_5', u1_struct_0('#skF_4')) | ~m1_subset_1(k6_domain_1(u1_struct_0('#skF_4'), '#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_100, c_371])).
% 3.96/1.57  tff(c_458, plain, (~m1_subset_1(k6_domain_1(u1_struct_0('#skF_4'), '#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(splitLeft, [status(thm)], [c_372])).
% 3.96/1.57  tff(c_461, plain, (~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~l1_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_82, c_458])).
% 3.96/1.57  tff(c_464, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_98, c_92, c_90, c_461])).
% 3.96/1.57  tff(c_466, plain, $false, inference(negUnitSimplification, [status(thm)], [c_100, c_464])).
% 3.96/1.57  tff(c_467, plain, (r2_hidden('#skF_5', u1_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_372])).
% 3.96/1.57  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.96/1.57  tff(c_473, plain, (~v1_xboole_0(u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_467, c_2])).
% 3.96/1.57  tff(c_478, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_143, c_473])).
% 3.96/1.57  tff(c_479, plain, (k6_domain_1(u1_struct_0('#skF_4'), '#skF_5')=k1_tarski('#skF_5')), inference(splitRight, [status(thm)], [c_142])).
% 3.96/1.57  tff(c_671, plain, (![A_454, B_455]: (m1_subset_1(k6_domain_1(u1_struct_0(A_454), B_455), k1_zfmisc_1(u1_struct_0(A_454))) | ~m1_subset_1(B_455, u1_struct_0(A_454)) | ~l1_orders_2(A_454) | ~v3_orders_2(A_454) | v2_struct_0(A_454))), inference(cnfTransformation, [status(thm)], [f_124])).
% 3.96/1.57  tff(c_684, plain, (m1_subset_1(k1_tarski('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~l1_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_479, c_671])).
% 3.96/1.57  tff(c_690, plain, (m1_subset_1(k1_tarski('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_98, c_92, c_90, c_684])).
% 3.96/1.57  tff(c_691, plain, (m1_subset_1(k1_tarski('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_100, c_690])).
% 3.96/1.57  tff(c_6, plain, (![A_5]: (k2_tarski(A_5, A_5)=k1_tarski(A_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.96/1.57  tff(c_8, plain, (![A_6, B_7]: (k1_enumset1(A_6, A_6, B_7)=k2_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.96/1.57  tff(c_10, plain, (![A_8, B_9, C_10]: (k2_enumset1(A_8, A_8, B_9, C_10)=k1_enumset1(A_8, B_9, C_10))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.96/1.57  tff(c_12, plain, (![A_11, B_12, C_13, D_14]: (k3_enumset1(A_11, A_11, B_12, C_13, D_14)=k2_enumset1(A_11, B_12, C_13, D_14))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.96/1.57  tff(c_14, plain, (![B_16, A_15, D_18, E_19, C_17]: (k4_enumset1(A_15, A_15, B_16, C_17, D_18, E_19)=k3_enumset1(A_15, B_16, C_17, D_18, E_19))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.96/1.57  tff(c_16, plain, (![C_22, D_23, A_20, B_21, F_25, E_24]: (k5_enumset1(A_20, A_20, B_21, C_22, D_23, E_24, F_25)=k4_enumset1(A_20, B_21, C_22, D_23, E_24, F_25))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.96/1.57  tff(c_612, plain, (![A_424, F_425, E_427, C_426, G_428, B_423, D_422]: (k6_enumset1(A_424, A_424, B_423, C_426, D_422, E_427, F_425, G_428)=k5_enumset1(A_424, B_423, C_426, D_422, E_427, F_425, G_428))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.96/1.57  tff(c_36, plain, (![D_36, G_39, J_44, F_38, E_37, B_34, H_40, C_35]: (r2_hidden(J_44, k6_enumset1(J_44, B_34, C_35, D_36, E_37, F_38, G_39, H_40)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.96/1.57  tff(c_730, plain, (![D_463, E_460, G_464, A_466, F_461, B_465, C_462]: (r2_hidden(A_466, k5_enumset1(A_466, B_465, C_462, D_463, E_460, F_461, G_464)))), inference(superposition, [status(thm), theory('equality')], [c_612, c_36])).
% 3.96/1.57  tff(c_741, plain, (![C_467, B_468, A_471, D_469, E_470, F_472]: (r2_hidden(A_471, k4_enumset1(A_471, B_468, C_467, D_469, E_470, F_472)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_730])).
% 3.96/1.57  tff(c_752, plain, (![E_476, B_475, D_474, C_473, A_477]: (r2_hidden(A_477, k3_enumset1(A_477, B_475, C_473, D_474, E_476)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_741])).
% 3.96/1.57  tff(c_763, plain, (![A_478, B_479, C_480, D_481]: (r2_hidden(A_478, k2_enumset1(A_478, B_479, C_480, D_481)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_752])).
% 3.96/1.57  tff(c_804, plain, (![A_484, B_485, C_486]: (r2_hidden(A_484, k1_enumset1(A_484, B_485, C_486)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_763])).
% 3.96/1.57  tff(c_815, plain, (![A_487, B_488]: (r2_hidden(A_487, k2_tarski(A_487, B_488)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_804])).
% 3.96/1.57  tff(c_823, plain, (![A_5]: (r2_hidden(A_5, k1_tarski(A_5)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_815])).
% 3.96/1.57  tff(c_482, plain, (r2_hidden('#skF_5', k2_orders_2('#skF_4', k1_tarski('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_479, c_88])).
% 3.96/1.57  tff(c_873, plain, (![B_509, A_510, C_511]: (~r2_hidden(B_509, k2_orders_2(A_510, C_511)) | ~r2_hidden(B_509, C_511) | ~m1_subset_1(C_511, k1_zfmisc_1(u1_struct_0(A_510))) | ~m1_subset_1(B_509, u1_struct_0(A_510)) | ~l1_orders_2(A_510) | ~v5_orders_2(A_510) | ~v4_orders_2(A_510) | ~v3_orders_2(A_510) | v2_struct_0(A_510))), inference(cnfTransformation, [status(thm)], [f_146])).
% 3.96/1.57  tff(c_878, plain, (~r2_hidden('#skF_5', k1_tarski('#skF_5')) | ~m1_subset_1(k1_tarski('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_482, c_873])).
% 3.96/1.57  tff(c_885, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_98, c_96, c_94, c_92, c_90, c_691, c_823, c_878])).
% 3.96/1.57  tff(c_887, plain, $false, inference(negUnitSimplification, [status(thm)], [c_100, c_885])).
% 3.96/1.57  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.96/1.57  
% 3.96/1.57  Inference rules
% 3.96/1.57  ----------------------
% 3.96/1.57  #Ref     : 0
% 3.96/1.57  #Sup     : 193
% 3.96/1.57  #Fact    : 0
% 3.96/1.57  #Define  : 0
% 3.96/1.57  #Split   : 2
% 3.96/1.57  #Chain   : 0
% 3.96/1.57  #Close   : 0
% 3.96/1.57  
% 3.96/1.57  Ordering : KBO
% 3.96/1.57  
% 3.96/1.57  Simplification rules
% 3.96/1.57  ----------------------
% 3.96/1.57  #Subsume      : 35
% 3.96/1.57  #Demod        : 35
% 3.96/1.57  #Tautology    : 27
% 3.96/1.57  #SimpNegUnit  : 10
% 3.96/1.57  #BackRed      : 2
% 3.96/1.57  
% 3.96/1.57  #Partial instantiations: 0
% 3.96/1.57  #Strategies tried      : 1
% 3.96/1.57  
% 3.96/1.57  Timing (in seconds)
% 3.96/1.57  ----------------------
% 3.96/1.57  Preprocessing        : 0.38
% 3.96/1.57  Parsing              : 0.18
% 3.96/1.58  CNF conversion       : 0.03
% 3.96/1.58  Main loop            : 0.42
% 3.96/1.58  Inferencing          : 0.14
% 3.96/1.58  Reduction            : 0.12
% 3.96/1.58  Demodulation         : 0.08
% 3.96/1.58  BG Simplification    : 0.03
% 3.96/1.58  Subsumption          : 0.11
% 3.96/1.58  Abstraction          : 0.03
% 3.96/1.58  MUC search           : 0.00
% 3.96/1.58  Cooper               : 0.00
% 3.96/1.58  Total                : 0.84
% 3.96/1.58  Index Insertion      : 0.00
% 3.96/1.58  Index Deletion       : 0.00
% 3.96/1.58  Index Matching       : 0.00
% 3.96/1.58  BG Taut test         : 0.00
%------------------------------------------------------------------------------
