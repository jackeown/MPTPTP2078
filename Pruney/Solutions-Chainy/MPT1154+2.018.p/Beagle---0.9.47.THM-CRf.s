%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:34 EST 2020

% Result     : Theorem 3.81s
% Output     : CNFRefutation 4.29s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 117 expanded)
%              Number of leaves         :   43 (  59 expanded)
%              Depth                    :   14
%              Number of atoms          :  125 ( 252 expanded)
%              Number of equality atoms :   27 (  27 expanded)
%              Maximal formula depth    :   22 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k6_domain_1 > k2_tarski > k1_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff(k1_orders_2,type,(
    k1_orders_2: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_158,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ~ r2_hidden(B,k1_orders_2(A,k6_domain_1(u1_struct_0(A),B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_orders_2)).

tff(f_111,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_52,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_86,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(k1_tarski(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_subset_1)).

tff(f_27,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

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

tff(f_37,axiom,(
    ! [A,B,C,D,E,F] : k5_enumset1(A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C,D,E,F,G] : k6_enumset1(A,A,B,C,D,E,F,G) = k5_enumset1(A,B,C,D,E,F,G) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

tff(f_82,axiom,(
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

tff(f_118,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_140,axiom,(
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
                  & r2_hidden(B,k1_orders_2(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_orders_2)).

tff(f_107,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(c_96,plain,(
    l1_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_86,plain,(
    ! [A_52] :
      ( l1_struct_0(A_52)
      | ~ l1_orders_2(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_104,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_94,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_126,plain,(
    ! [B_70,A_71] :
      ( v1_xboole_0(B_70)
      | ~ m1_subset_1(B_70,A_71)
      | ~ v1_xboole_0(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_134,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_94,c_126])).

tff(c_135,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_134])).

tff(c_18,plain,(
    ! [B_30,A_29] :
      ( r2_hidden(B_30,A_29)
      | ~ m1_subset_1(B_30,A_29)
      | v1_xboole_0(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_78,plain,(
    ! [A_43,B_44] :
      ( m1_subset_1(k1_tarski(A_43),k1_zfmisc_1(B_44))
      | ~ r2_hidden(A_43,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_102,plain,(
    v3_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_100,plain,(
    v4_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_98,plain,(
    v5_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_2,plain,(
    ! [A_1] : k2_tarski(A_1,A_1) = k1_tarski(A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_2,B_3] : k1_enumset1(A_2,A_2,B_3) = k2_tarski(A_2,B_3) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6,plain,(
    ! [A_4,B_5,C_6] : k2_enumset1(A_4,A_4,B_5,C_6) = k1_enumset1(A_4,B_5,C_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,(
    ! [A_7,B_8,C_9,D_10] : k3_enumset1(A_7,A_7,B_8,C_9,D_10) = k2_enumset1(A_7,B_8,C_9,D_10) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_10,plain,(
    ! [D_14,E_15,B_12,A_11,C_13] : k4_enumset1(A_11,A_11,B_12,C_13,D_14,E_15) = k3_enumset1(A_11,B_12,C_13,D_14,E_15) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_12,plain,(
    ! [C_18,B_17,A_16,D_19,E_20,F_21] : k5_enumset1(A_16,A_16,B_17,C_18,D_19,E_20,F_21) = k4_enumset1(A_16,B_17,C_18,D_19,E_20,F_21) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1289,plain,(
    ! [B_453,D_452,C_448,A_447,F_450,G_451,E_449] : k6_enumset1(A_447,A_447,B_453,C_448,D_452,E_449,F_450,G_451) = k5_enumset1(A_447,B_453,C_448,D_452,E_449,F_450,G_451) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_34,plain,(
    ! [A_31,C_33,B_32,H_38,F_36,E_35,G_37,J_42] : r2_hidden(J_42,k6_enumset1(A_31,B_32,C_33,J_42,E_35,F_36,G_37,H_38)) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_1326,plain,(
    ! [F_460,E_458,D_456,A_455,C_459,B_454,G_457] : r2_hidden(C_459,k5_enumset1(A_455,B_454,C_459,D_456,E_458,F_460,G_457)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1289,c_34])).

tff(c_1343,plain,(
    ! [B_462,E_463,C_466,F_461,D_465,A_464] : r2_hidden(B_462,k4_enumset1(A_464,B_462,C_466,D_465,E_463,F_461)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_1326])).

tff(c_1360,plain,(
    ! [C_467,D_470,E_471,B_469,A_468] : r2_hidden(A_468,k3_enumset1(A_468,B_469,C_467,D_470,E_471)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_1343])).

tff(c_1377,plain,(
    ! [A_472,B_473,C_474,D_475] : r2_hidden(A_472,k2_enumset1(A_472,B_473,C_474,D_475)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_1360])).

tff(c_1394,plain,(
    ! [A_476,B_477,C_478] : r2_hidden(A_476,k1_enumset1(A_476,B_477,C_478)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_1377])).

tff(c_1460,plain,(
    ! [A_488,B_489] : r2_hidden(A_488,k2_tarski(A_488,B_489)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_1394])).

tff(c_1472,plain,(
    ! [A_1] : r2_hidden(A_1,k1_tarski(A_1)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1460])).

tff(c_701,plain,(
    ! [A_262,B_263] :
      ( k6_domain_1(A_262,B_263) = k1_tarski(B_263)
      | ~ m1_subset_1(B_263,A_262)
      | v1_xboole_0(A_262) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_713,plain,
    ( k6_domain_1(u1_struct_0('#skF_3'),'#skF_4') = k1_tarski('#skF_4')
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_94,c_701])).

tff(c_721,plain,(
    k6_domain_1(u1_struct_0('#skF_3'),'#skF_4') = k1_tarski('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_135,c_713])).

tff(c_92,plain,(
    r2_hidden('#skF_4',k1_orders_2('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),'#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_724,plain,(
    r2_hidden('#skF_4',k1_orders_2('#skF_3',k1_tarski('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_721,c_92])).

tff(c_1566,plain,(
    ! [B_493,A_494,C_495] :
      ( ~ r2_hidden(B_493,k1_orders_2(A_494,C_495))
      | ~ r2_hidden(B_493,C_495)
      | ~ m1_subset_1(C_495,k1_zfmisc_1(u1_struct_0(A_494)))
      | ~ m1_subset_1(B_493,u1_struct_0(A_494))
      | ~ l1_orders_2(A_494)
      | ~ v5_orders_2(A_494)
      | ~ v4_orders_2(A_494)
      | ~ v3_orders_2(A_494)
      | v2_struct_0(A_494) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_1568,plain,
    ( ~ r2_hidden('#skF_4',k1_tarski('#skF_4'))
    | ~ m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ l1_orders_2('#skF_3')
    | ~ v5_orders_2('#skF_3')
    | ~ v4_orders_2('#skF_3')
    | ~ v3_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_724,c_1566])).

tff(c_1574,plain,
    ( ~ m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_100,c_98,c_96,c_94,c_1472,c_1568])).

tff(c_1575,plain,(
    ~ m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_104,c_1574])).

tff(c_1594,plain,(
    ~ r2_hidden('#skF_4',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_78,c_1575])).

tff(c_1604,plain,
    ( ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_18,c_1594])).

tff(c_1607,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_1604])).

tff(c_1609,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_135,c_1607])).

tff(c_1611,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_134])).

tff(c_84,plain,(
    ! [A_51] :
      ( ~ v1_xboole_0(u1_struct_0(A_51))
      | ~ l1_struct_0(A_51)
      | v2_struct_0(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_1614,plain,
    ( ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_1611,c_84])).

tff(c_1617,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_104,c_1614])).

tff(c_1620,plain,(
    ~ l1_orders_2('#skF_3') ),
    inference(resolution,[status(thm)],[c_86,c_1617])).

tff(c_1624,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_1620])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:48:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.81/1.76  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.20/1.77  
% 4.20/1.77  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.20/1.77  %$ r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k6_domain_1 > k2_tarski > k1_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 4.20/1.77  
% 4.20/1.77  %Foreground sorts:
% 4.20/1.77  
% 4.20/1.77  
% 4.20/1.77  %Background operators:
% 4.20/1.77  
% 4.20/1.77  
% 4.20/1.77  %Foreground operators:
% 4.20/1.77  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.20/1.77  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 4.20/1.77  tff(k1_orders_2, type, k1_orders_2: ($i * $i) > $i).
% 4.20/1.77  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.20/1.77  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.20/1.77  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.20/1.77  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.20/1.77  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 4.20/1.77  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.20/1.77  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.20/1.77  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 4.20/1.77  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.20/1.77  tff('#skF_3', type, '#skF_3': $i).
% 4.20/1.77  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 4.20/1.77  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.20/1.77  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 4.20/1.77  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.20/1.77  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 4.20/1.77  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 4.20/1.77  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 4.20/1.77  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.20/1.77  tff('#skF_4', type, '#skF_4': $i).
% 4.20/1.77  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.20/1.77  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 4.20/1.77  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 4.20/1.77  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.20/1.77  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.20/1.77  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.20/1.77  
% 4.29/1.79  tff(f_158, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => ~r2_hidden(B, k1_orders_2(A, k6_domain_1(u1_struct_0(A), B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_orders_2)).
% 4.29/1.79  tff(f_111, axiom, (![A]: (l1_orders_2(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 4.29/1.79  tff(f_52, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 4.29/1.79  tff(f_86, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(k1_tarski(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_subset_1)).
% 4.29/1.79  tff(f_27, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 4.29/1.79  tff(f_29, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 4.29/1.79  tff(f_31, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 4.29/1.79  tff(f_33, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 4.29/1.79  tff(f_35, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 4.29/1.79  tff(f_37, axiom, (![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 4.29/1.79  tff(f_39, axiom, (![A, B, C, D, E, F, G]: (k6_enumset1(A, A, B, C, D, E, F, G) = k5_enumset1(A, B, C, D, E, F, G))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_enumset1)).
% 4.29/1.79  tff(f_82, axiom, (![A, B, C, D, E, F, G, H, I]: ((I = k6_enumset1(A, B, C, D, E, F, G, H)) <=> (![J]: (r2_hidden(J, I) <=> ~(((((((~(J = A) & ~(J = B)) & ~(J = C)) & ~(J = D)) & ~(J = E)) & ~(J = F)) & ~(J = G)) & ~(J = H)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_enumset1)).
% 4.29/1.79  tff(f_118, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 4.29/1.79  tff(f_140, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r2_hidden(B, C) & r2_hidden(B, k1_orders_2(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_orders_2)).
% 4.29/1.79  tff(f_107, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 4.29/1.79  tff(c_96, plain, (l1_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_158])).
% 4.29/1.79  tff(c_86, plain, (![A_52]: (l1_struct_0(A_52) | ~l1_orders_2(A_52))), inference(cnfTransformation, [status(thm)], [f_111])).
% 4.29/1.79  tff(c_104, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_158])).
% 4.29/1.79  tff(c_94, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_158])).
% 4.29/1.79  tff(c_126, plain, (![B_70, A_71]: (v1_xboole_0(B_70) | ~m1_subset_1(B_70, A_71) | ~v1_xboole_0(A_71))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.29/1.79  tff(c_134, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_94, c_126])).
% 4.29/1.79  tff(c_135, plain, (~v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_134])).
% 4.29/1.79  tff(c_18, plain, (![B_30, A_29]: (r2_hidden(B_30, A_29) | ~m1_subset_1(B_30, A_29) | v1_xboole_0(A_29))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.29/1.79  tff(c_78, plain, (![A_43, B_44]: (m1_subset_1(k1_tarski(A_43), k1_zfmisc_1(B_44)) | ~r2_hidden(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.29/1.79  tff(c_102, plain, (v3_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_158])).
% 4.29/1.79  tff(c_100, plain, (v4_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_158])).
% 4.29/1.79  tff(c_98, plain, (v5_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_158])).
% 4.29/1.79  tff(c_2, plain, (![A_1]: (k2_tarski(A_1, A_1)=k1_tarski(A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.29/1.79  tff(c_4, plain, (![A_2, B_3]: (k1_enumset1(A_2, A_2, B_3)=k2_tarski(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.29/1.79  tff(c_6, plain, (![A_4, B_5, C_6]: (k2_enumset1(A_4, A_4, B_5, C_6)=k1_enumset1(A_4, B_5, C_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.29/1.79  tff(c_8, plain, (![A_7, B_8, C_9, D_10]: (k3_enumset1(A_7, A_7, B_8, C_9, D_10)=k2_enumset1(A_7, B_8, C_9, D_10))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.29/1.79  tff(c_10, plain, (![D_14, E_15, B_12, A_11, C_13]: (k4_enumset1(A_11, A_11, B_12, C_13, D_14, E_15)=k3_enumset1(A_11, B_12, C_13, D_14, E_15))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.29/1.79  tff(c_12, plain, (![C_18, B_17, A_16, D_19, E_20, F_21]: (k5_enumset1(A_16, A_16, B_17, C_18, D_19, E_20, F_21)=k4_enumset1(A_16, B_17, C_18, D_19, E_20, F_21))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.29/1.79  tff(c_1289, plain, (![B_453, D_452, C_448, A_447, F_450, G_451, E_449]: (k6_enumset1(A_447, A_447, B_453, C_448, D_452, E_449, F_450, G_451)=k5_enumset1(A_447, B_453, C_448, D_452, E_449, F_450, G_451))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.29/1.79  tff(c_34, plain, (![A_31, C_33, B_32, H_38, F_36, E_35, G_37, J_42]: (r2_hidden(J_42, k6_enumset1(A_31, B_32, C_33, J_42, E_35, F_36, G_37, H_38)))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.29/1.79  tff(c_1326, plain, (![F_460, E_458, D_456, A_455, C_459, B_454, G_457]: (r2_hidden(C_459, k5_enumset1(A_455, B_454, C_459, D_456, E_458, F_460, G_457)))), inference(superposition, [status(thm), theory('equality')], [c_1289, c_34])).
% 4.29/1.79  tff(c_1343, plain, (![B_462, E_463, C_466, F_461, D_465, A_464]: (r2_hidden(B_462, k4_enumset1(A_464, B_462, C_466, D_465, E_463, F_461)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_1326])).
% 4.29/1.79  tff(c_1360, plain, (![C_467, D_470, E_471, B_469, A_468]: (r2_hidden(A_468, k3_enumset1(A_468, B_469, C_467, D_470, E_471)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_1343])).
% 4.29/1.79  tff(c_1377, plain, (![A_472, B_473, C_474, D_475]: (r2_hidden(A_472, k2_enumset1(A_472, B_473, C_474, D_475)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_1360])).
% 4.29/1.79  tff(c_1394, plain, (![A_476, B_477, C_478]: (r2_hidden(A_476, k1_enumset1(A_476, B_477, C_478)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_1377])).
% 4.29/1.79  tff(c_1460, plain, (![A_488, B_489]: (r2_hidden(A_488, k2_tarski(A_488, B_489)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_1394])).
% 4.29/1.79  tff(c_1472, plain, (![A_1]: (r2_hidden(A_1, k1_tarski(A_1)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1460])).
% 4.29/1.79  tff(c_701, plain, (![A_262, B_263]: (k6_domain_1(A_262, B_263)=k1_tarski(B_263) | ~m1_subset_1(B_263, A_262) | v1_xboole_0(A_262))), inference(cnfTransformation, [status(thm)], [f_118])).
% 4.29/1.79  tff(c_713, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_4')=k1_tarski('#skF_4') | v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_94, c_701])).
% 4.29/1.79  tff(c_721, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_4')=k1_tarski('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_135, c_713])).
% 4.29/1.79  tff(c_92, plain, (r2_hidden('#skF_4', k1_orders_2('#skF_3', k6_domain_1(u1_struct_0('#skF_3'), '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_158])).
% 4.29/1.79  tff(c_724, plain, (r2_hidden('#skF_4', k1_orders_2('#skF_3', k1_tarski('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_721, c_92])).
% 4.29/1.79  tff(c_1566, plain, (![B_493, A_494, C_495]: (~r2_hidden(B_493, k1_orders_2(A_494, C_495)) | ~r2_hidden(B_493, C_495) | ~m1_subset_1(C_495, k1_zfmisc_1(u1_struct_0(A_494))) | ~m1_subset_1(B_493, u1_struct_0(A_494)) | ~l1_orders_2(A_494) | ~v5_orders_2(A_494) | ~v4_orders_2(A_494) | ~v3_orders_2(A_494) | v2_struct_0(A_494))), inference(cnfTransformation, [status(thm)], [f_140])).
% 4.29/1.79  tff(c_1568, plain, (~r2_hidden('#skF_4', k1_tarski('#skF_4')) | ~m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v5_orders_2('#skF_3') | ~v4_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_724, c_1566])).
% 4.29/1.79  tff(c_1574, plain, (~m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_102, c_100, c_98, c_96, c_94, c_1472, c_1568])).
% 4.29/1.79  tff(c_1575, plain, (~m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_104, c_1574])).
% 4.29/1.79  tff(c_1594, plain, (~r2_hidden('#skF_4', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_78, c_1575])).
% 4.29/1.79  tff(c_1604, plain, (~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_18, c_1594])).
% 4.29/1.79  tff(c_1607, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_1604])).
% 4.29/1.79  tff(c_1609, plain, $false, inference(negUnitSimplification, [status(thm)], [c_135, c_1607])).
% 4.29/1.79  tff(c_1611, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_134])).
% 4.29/1.79  tff(c_84, plain, (![A_51]: (~v1_xboole_0(u1_struct_0(A_51)) | ~l1_struct_0(A_51) | v2_struct_0(A_51))), inference(cnfTransformation, [status(thm)], [f_107])).
% 4.29/1.79  tff(c_1614, plain, (~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_1611, c_84])).
% 4.29/1.79  tff(c_1617, plain, (~l1_struct_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_104, c_1614])).
% 4.29/1.79  tff(c_1620, plain, (~l1_orders_2('#skF_3')), inference(resolution, [status(thm)], [c_86, c_1617])).
% 4.29/1.79  tff(c_1624, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_96, c_1620])).
% 4.29/1.79  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.29/1.79  
% 4.29/1.79  Inference rules
% 4.29/1.79  ----------------------
% 4.29/1.79  #Ref     : 0
% 4.29/1.79  #Sup     : 382
% 4.29/1.79  #Fact    : 0
% 4.29/1.79  #Define  : 0
% 4.29/1.79  #Split   : 7
% 4.29/1.79  #Chain   : 0
% 4.29/1.79  #Close   : 0
% 4.29/1.79  
% 4.29/1.79  Ordering : KBO
% 4.29/1.79  
% 4.29/1.79  Simplification rules
% 4.29/1.79  ----------------------
% 4.29/1.79  #Subsume      : 21
% 4.29/1.79  #Demod        : 26
% 4.29/1.79  #Tautology    : 90
% 4.29/1.79  #SimpNegUnit  : 18
% 4.29/1.79  #BackRed      : 12
% 4.29/1.79  
% 4.29/1.79  #Partial instantiations: 0
% 4.29/1.79  #Strategies tried      : 1
% 4.29/1.79  
% 4.29/1.79  Timing (in seconds)
% 4.29/1.79  ----------------------
% 4.29/1.79  Preprocessing        : 0.46
% 4.29/1.79  Parsing              : 0.23
% 4.29/1.79  CNF conversion       : 0.03
% 4.29/1.79  Main loop            : 0.52
% 4.29/1.79  Inferencing          : 0.17
% 4.29/1.79  Reduction            : 0.15
% 4.29/1.79  Demodulation         : 0.10
% 4.29/1.79  BG Simplification    : 0.04
% 4.29/1.79  Subsumption          : 0.12
% 4.29/1.79  Abstraction          : 0.04
% 4.29/1.79  MUC search           : 0.00
% 4.29/1.79  Cooper               : 0.00
% 4.29/1.79  Total                : 1.01
% 4.29/1.79  Index Insertion      : 0.00
% 4.29/1.79  Index Deletion       : 0.00
% 4.29/1.79  Index Matching       : 0.00
% 4.29/1.79  BG Taut test         : 0.00
%------------------------------------------------------------------------------
