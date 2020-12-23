%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:25:28 EST 2020

% Result     : Theorem 5.92s
% Output     : CNFRefutation 6.08s
% Verified   : 
% Statistics : Number of formulae       :  266 (1545 expanded)
%              Number of leaves         :   50 ( 546 expanded)
%              Depth                    :   24
%              Number of atoms          :  649 (3279 expanded)
%              Number of equality atoms :   98 (1021 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v2_lattice3 > v1_xboole_0 > v1_orders_2 > v1_lattice3 > l1_orders_2 > k13_lattice3 > k12_lattice3 > k11_lattice3 > k10_lattice3 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > u1_orders_2 > k9_setfam_1 > k3_yellow_1 > k2_yellow_1 > k1_yellow_1 > k1_setfam_1 > #skF_5 > #skF_2 > #skF_4 > #skF_1 > #skF_7 > #skF_6 > #skF_8 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_orders_2,type,(
    v1_orders_2: $i > $o )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': $i > $i )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k13_lattice3,type,(
    k13_lattice3: ( $i * $i * $i ) > $i )).

tff(k3_yellow_1,type,(
    k3_yellow_1: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k10_lattice3,type,(
    k10_lattice3: ( $i * $i * $i ) > $i )).

tff(k2_yellow_1,type,(
    k2_yellow_1: $i > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k11_lattice3,type,(
    k11_lattice3: ( $i * $i * $i ) > $i )).

tff(k9_setfam_1,type,(
    k9_setfam_1: $i > $i )).

tff(v1_lattice3,type,(
    v1_lattice3: $i > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k12_lattice3,type,(
    k12_lattice3: ( $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k1_yellow_1,type,(
    k1_yellow_1: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(v2_lattice3,type,(
    v2_lattice3: $i > $o )).

tff(u1_orders_2,type,(
    u1_orders_2: $i > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_160,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,u1_struct_0(k3_yellow_1(A)))
       => ! [C] :
            ( m1_subset_1(C,u1_struct_0(k3_yellow_1(A)))
           => ( k13_lattice3(k3_yellow_1(A),B,C) = k2_xboole_0(B,C)
              & k12_lattice3(k3_yellow_1(A),B,C) = k3_xboole_0(B,C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_yellow_1)).

tff(f_124,axiom,(
    ! [A] : k3_yellow_1(A) = k2_yellow_1(k9_setfam_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_yellow_1)).

tff(f_122,axiom,(
    ! [A] :
      ( u1_struct_0(k2_yellow_1(A)) = A
      & u1_orders_2(k2_yellow_1(A)) = k1_yellow_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_yellow_1)).

tff(f_94,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,u1_struct_0(k3_yellow_1(A)))
     => ! [C] :
          ( m1_subset_1(C,u1_struct_0(k3_yellow_1(A)))
         => ( r2_hidden(k3_xboole_0(B,C),k9_setfam_1(A))
            & r2_hidden(k2_xboole_0(B,C),k9_setfam_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l19_yellow_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_137,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(k2_yellow_1(A)))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(k2_yellow_1(A)))
             => ( r2_hidden(k2_xboole_0(B,C),A)
               => k10_lattice3(k2_yellow_1(A),B,C) = k2_xboole_0(B,C) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_yellow_1)).

tff(f_85,axiom,(
    ! [A] :
      ( ~ v2_struct_0(k3_yellow_1(A))
      & v1_orders_2(k3_yellow_1(A))
      & v3_orders_2(k3_yellow_1(A))
      & v4_orders_2(k3_yellow_1(A))
      & v5_orders_2(k3_yellow_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_yellow_1)).

tff(f_106,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ( ! [B,C] :
            ( ( r2_hidden(B,A)
              & r2_hidden(C,A) )
           => r2_hidden(k2_xboole_0(B,C),A) )
       => v1_lattice3(k2_yellow_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_yellow_1)).

tff(f_74,axiom,(
    ! [A] :
      ( v1_orders_2(k3_yellow_1(A))
      & l1_orders_2(k3_yellow_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_yellow_1)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( ( v5_orders_2(A)
        & v1_lattice3(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => k13_lattice3(A,B,C) = k10_lattice3(A,B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k13_lattice3)).

tff(f_150,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(k2_yellow_1(A)))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(k2_yellow_1(A)))
             => ( r2_hidden(k3_xboole_0(B,C),A)
               => k11_lattice3(k2_yellow_1(A),B,C) = k3_xboole_0(B,C) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_yellow_1)).

tff(f_118,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ( ! [B,C] :
            ( ( r2_hidden(B,A)
              & r2_hidden(C,A) )
           => r2_hidden(k3_xboole_0(B,C),A) )
       => v2_lattice3(k2_yellow_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_yellow_1)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( ( v5_orders_2(A)
        & v2_lattice3(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => k12_lattice3(A,B,C) = k11_lattice3(A,B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k12_lattice3)).

tff(c_60,plain,
    ( k12_lattice3(k3_yellow_1('#skF_6'),'#skF_7','#skF_8') != k3_xboole_0('#skF_7','#skF_8')
    | k13_lattice3(k3_yellow_1('#skF_6'),'#skF_7','#skF_8') != k2_xboole_0('#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_143,plain,(
    k13_lattice3(k3_yellow_1('#skF_6'),'#skF_7','#skF_8') != k2_xboole_0('#skF_7','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_83,plain,(
    ! [A_51] : k2_yellow_1(k9_setfam_1(A_51)) = k3_yellow_1(A_51) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_50,plain,(
    ! [A_27] : u1_struct_0(k2_yellow_1(A_27)) = A_27 ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_89,plain,(
    ! [A_51] : u1_struct_0(k3_yellow_1(A_51)) = k9_setfam_1(A_51) ),
    inference(superposition,[status(thm),theory(equality)],[c_83,c_50])).

tff(c_64,plain,(
    m1_subset_1('#skF_7',u1_struct_0(k3_yellow_1('#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_109,plain,(
    m1_subset_1('#skF_7',k9_setfam_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_64])).

tff(c_62,plain,(
    m1_subset_1('#skF_8',u1_struct_0(k3_yellow_1('#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_108,plain,(
    m1_subset_1('#skF_8',k9_setfam_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_62])).

tff(c_54,plain,(
    ! [A_28] : k2_yellow_1(k9_setfam_1(A_28)) = k3_yellow_1(A_28) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_34,plain,(
    ! [B_18,C_20,A_17] :
      ( r2_hidden(k2_xboole_0(B_18,C_20),k9_setfam_1(A_17))
      | ~ m1_subset_1(C_20,u1_struct_0(k3_yellow_1(A_17)))
      | ~ m1_subset_1(B_18,u1_struct_0(k3_yellow_1(A_17))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_2135,plain,(
    ! [B_18,C_20,A_17] :
      ( r2_hidden(k2_xboole_0(B_18,C_20),k9_setfam_1(A_17))
      | ~ m1_subset_1(C_20,k9_setfam_1(A_17))
      | ~ m1_subset_1(B_18,k9_setfam_1(A_17)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_89,c_34])).

tff(c_1242,plain,(
    ! [B_18,C_20,A_17] :
      ( r2_hidden(k2_xboole_0(B_18,C_20),k9_setfam_1(A_17))
      | ~ m1_subset_1(C_20,k9_setfam_1(A_17))
      | ~ m1_subset_1(B_18,k9_setfam_1(A_17)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_89,c_34])).

tff(c_10,plain,(
    ! [B_6,A_5] :
      ( m1_subset_1(B_6,A_5)
      | ~ v1_xboole_0(B_6)
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_36,plain,(
    ! [B_18,C_20,A_17] :
      ( r2_hidden(k3_xboole_0(B_18,C_20),k9_setfam_1(A_17))
      | ~ m1_subset_1(C_20,u1_struct_0(k3_yellow_1(A_17)))
      | ~ m1_subset_1(B_18,u1_struct_0(k3_yellow_1(A_17))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_252,plain,(
    ! [B_80,C_81,A_82] :
      ( r2_hidden(k3_xboole_0(B_80,C_81),k9_setfam_1(A_82))
      | ~ m1_subset_1(C_81,k9_setfam_1(A_82))
      | ~ m1_subset_1(B_80,k9_setfam_1(A_82)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_89,c_36])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_267,plain,(
    ! [A_83,C_84,B_85] :
      ( ~ v1_xboole_0(k9_setfam_1(A_83))
      | ~ m1_subset_1(C_84,k9_setfam_1(A_83))
      | ~ m1_subset_1(B_85,k9_setfam_1(A_83)) ) ),
    inference(resolution,[status(thm)],[c_252,c_2])).

tff(c_299,plain,(
    ! [B_85,A_83,B_6] :
      ( ~ m1_subset_1(B_85,k9_setfam_1(A_83))
      | ~ v1_xboole_0(B_6)
      | ~ v1_xboole_0(k9_setfam_1(A_83)) ) ),
    inference(resolution,[status(thm)],[c_10,c_267])).

tff(c_303,plain,(
    ! [B_86,A_87] :
      ( ~ m1_subset_1(B_86,k9_setfam_1(A_87))
      | ~ v1_xboole_0(k9_setfam_1(A_87)) ) ),
    inference(splitLeft,[status(thm)],[c_299])).

tff(c_343,plain,(
    ! [B_6,A_87] :
      ( ~ v1_xboole_0(B_6)
      | ~ v1_xboole_0(k9_setfam_1(A_87)) ) ),
    inference(resolution,[status(thm)],[c_10,c_303])).

tff(c_346,plain,(
    ! [A_87] : ~ v1_xboole_0(k9_setfam_1(A_87)) ),
    inference(splitLeft,[status(thm)],[c_343])).

tff(c_348,plain,(
    ! [B_18,C_20,A_17] :
      ( r2_hidden(k2_xboole_0(B_18,C_20),k9_setfam_1(A_17))
      | ~ m1_subset_1(C_20,k9_setfam_1(A_17))
      | ~ m1_subset_1(B_18,k9_setfam_1(A_17)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_89,c_34])).

tff(c_56,plain,(
    ! [A_29,B_33,C_35] :
      ( k10_lattice3(k2_yellow_1(A_29),B_33,C_35) = k2_xboole_0(B_33,C_35)
      | ~ r2_hidden(k2_xboole_0(B_33,C_35),A_29)
      | ~ m1_subset_1(C_35,u1_struct_0(k2_yellow_1(A_29)))
      | ~ m1_subset_1(B_33,u1_struct_0(k2_yellow_1(A_29)))
      | v1_xboole_0(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_455,plain,(
    ! [A_103,B_104,C_105] :
      ( k10_lattice3(k2_yellow_1(A_103),B_104,C_105) = k2_xboole_0(B_104,C_105)
      | ~ r2_hidden(k2_xboole_0(B_104,C_105),A_103)
      | ~ m1_subset_1(C_105,A_103)
      | ~ m1_subset_1(B_104,A_103)
      | v1_xboole_0(A_103) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_50,c_56])).

tff(c_458,plain,(
    ! [A_17,B_18,C_20] :
      ( k10_lattice3(k2_yellow_1(k9_setfam_1(A_17)),B_18,C_20) = k2_xboole_0(B_18,C_20)
      | v1_xboole_0(k9_setfam_1(A_17))
      | ~ m1_subset_1(C_20,k9_setfam_1(A_17))
      | ~ m1_subset_1(B_18,k9_setfam_1(A_17)) ) ),
    inference(resolution,[status(thm)],[c_348,c_455])).

tff(c_464,plain,(
    ! [A_17,B_18,C_20] :
      ( k10_lattice3(k3_yellow_1(A_17),B_18,C_20) = k2_xboole_0(B_18,C_20)
      | v1_xboole_0(k9_setfam_1(A_17))
      | ~ m1_subset_1(C_20,k9_setfam_1(A_17))
      | ~ m1_subset_1(B_18,k9_setfam_1(A_17)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_458])).

tff(c_467,plain,(
    ! [A_106,B_107,C_108] :
      ( k10_lattice3(k3_yellow_1(A_106),B_107,C_108) = k2_xboole_0(B_107,C_108)
      | ~ m1_subset_1(C_108,k9_setfam_1(A_106))
      | ~ m1_subset_1(B_107,k9_setfam_1(A_106)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_346,c_464])).

tff(c_573,plain,(
    ! [B_110] :
      ( k10_lattice3(k3_yellow_1('#skF_6'),B_110,'#skF_8') = k2_xboole_0(B_110,'#skF_8')
      | ~ m1_subset_1(B_110,k9_setfam_1('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_108,c_467])).

tff(c_625,plain,(
    k10_lattice3(k3_yellow_1('#skF_6'),'#skF_7','#skF_8') = k2_xboole_0('#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_109,c_573])).

tff(c_32,plain,(
    ! [A_16] : v5_orders_2(k3_yellow_1(A_16)) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_204,plain,(
    ! [A_72] :
      ( r2_hidden('#skF_3'(A_72),A_72)
      | v1_lattice3(k2_yellow_1(A_72))
      | v1_xboole_0(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_6,plain,(
    ! [B_6,A_5] :
      ( m1_subset_1(B_6,A_5)
      | ~ r2_hidden(B_6,A_5)
      | v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_211,plain,(
    ! [A_72] :
      ( m1_subset_1('#skF_3'(A_72),A_72)
      | v1_lattice3(k2_yellow_1(A_72))
      | v1_xboole_0(A_72) ) ),
    inference(resolution,[status(thm)],[c_204,c_6])).

tff(c_177,plain,(
    ! [A_69] :
      ( r2_hidden('#skF_2'(A_69),A_69)
      | v1_lattice3(k2_yellow_1(A_69))
      | v1_xboole_0(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_184,plain,(
    ! [A_69] :
      ( m1_subset_1('#skF_2'(A_69),A_69)
      | v1_lattice3(k2_yellow_1(A_69))
      | v1_xboole_0(A_69) ) ),
    inference(resolution,[status(thm)],[c_177,c_6])).

tff(c_349,plain,(
    ! [B_89,C_90,A_91] :
      ( r2_hidden(k2_xboole_0(B_89,C_90),k9_setfam_1(A_91))
      | ~ m1_subset_1(C_90,k9_setfam_1(A_91))
      | ~ m1_subset_1(B_89,k9_setfam_1(A_91)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_89,c_34])).

tff(c_38,plain,(
    ! [A_21] :
      ( ~ r2_hidden(k2_xboole_0('#skF_2'(A_21),'#skF_3'(A_21)),A_21)
      | v1_lattice3(k2_yellow_1(A_21))
      | v1_xboole_0(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_353,plain,(
    ! [A_91] :
      ( v1_lattice3(k2_yellow_1(k9_setfam_1(A_91)))
      | v1_xboole_0(k9_setfam_1(A_91))
      | ~ m1_subset_1('#skF_3'(k9_setfam_1(A_91)),k9_setfam_1(A_91))
      | ~ m1_subset_1('#skF_2'(k9_setfam_1(A_91)),k9_setfam_1(A_91)) ) ),
    inference(resolution,[status(thm)],[c_349,c_38])).

tff(c_361,plain,(
    ! [A_91] :
      ( v1_lattice3(k3_yellow_1(A_91))
      | v1_xboole_0(k9_setfam_1(A_91))
      | ~ m1_subset_1('#skF_3'(k9_setfam_1(A_91)),k9_setfam_1(A_91))
      | ~ m1_subset_1('#skF_2'(k9_setfam_1(A_91)),k9_setfam_1(A_91)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_353])).

tff(c_385,plain,(
    ! [A_96] :
      ( v1_lattice3(k3_yellow_1(A_96))
      | ~ m1_subset_1('#skF_3'(k9_setfam_1(A_96)),k9_setfam_1(A_96))
      | ~ m1_subset_1('#skF_2'(k9_setfam_1(A_96)),k9_setfam_1(A_96)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_346,c_361])).

tff(c_388,plain,(
    ! [A_96] :
      ( v1_lattice3(k3_yellow_1(A_96))
      | ~ m1_subset_1('#skF_3'(k9_setfam_1(A_96)),k9_setfam_1(A_96))
      | v1_lattice3(k2_yellow_1(k9_setfam_1(A_96)))
      | v1_xboole_0(k9_setfam_1(A_96)) ) ),
    inference(resolution,[status(thm)],[c_184,c_385])).

tff(c_393,plain,(
    ! [A_96] :
      ( v1_lattice3(k3_yellow_1(A_96))
      | ~ m1_subset_1('#skF_3'(k9_setfam_1(A_96)),k9_setfam_1(A_96))
      | v1_lattice3(k3_yellow_1(A_96))
      | v1_xboole_0(k9_setfam_1(A_96)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_388])).

tff(c_428,plain,(
    ! [A_100] :
      ( v1_lattice3(k3_yellow_1(A_100))
      | ~ m1_subset_1('#skF_3'(k9_setfam_1(A_100)),k9_setfam_1(A_100))
      | v1_lattice3(k3_yellow_1(A_100)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_346,c_393])).

tff(c_431,plain,(
    ! [A_100] :
      ( v1_lattice3(k3_yellow_1(A_100))
      | v1_lattice3(k2_yellow_1(k9_setfam_1(A_100)))
      | v1_xboole_0(k9_setfam_1(A_100)) ) ),
    inference(resolution,[status(thm)],[c_211,c_428])).

tff(c_436,plain,(
    ! [A_100] :
      ( v1_lattice3(k3_yellow_1(A_100))
      | v1_lattice3(k3_yellow_1(A_100))
      | v1_xboole_0(k9_setfam_1(A_100)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_431])).

tff(c_437,plain,(
    ! [A_100] :
      ( v1_lattice3(k3_yellow_1(A_100))
      | v1_lattice3(k3_yellow_1(A_100)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_346,c_436])).

tff(c_447,plain,(
    ! [A_100] : v1_lattice3(k3_yellow_1(A_100)) ),
    inference(factorization,[status(thm),theory(equality)],[c_437])).

tff(c_22,plain,(
    ! [A_15] : l1_orders_2(k3_yellow_1(A_15)) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_770,plain,(
    ! [A_120,B_121,C_122] :
      ( k13_lattice3(A_120,B_121,C_122) = k10_lattice3(A_120,B_121,C_122)
      | ~ m1_subset_1(C_122,u1_struct_0(A_120))
      | ~ m1_subset_1(B_121,u1_struct_0(A_120))
      | ~ l1_orders_2(A_120)
      | ~ v1_lattice3(A_120)
      | ~ v5_orders_2(A_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_790,plain,(
    ! [A_51,B_121,C_122] :
      ( k13_lattice3(k3_yellow_1(A_51),B_121,C_122) = k10_lattice3(k3_yellow_1(A_51),B_121,C_122)
      | ~ m1_subset_1(C_122,k9_setfam_1(A_51))
      | ~ m1_subset_1(B_121,u1_struct_0(k3_yellow_1(A_51)))
      | ~ l1_orders_2(k3_yellow_1(A_51))
      | ~ v1_lattice3(k3_yellow_1(A_51))
      | ~ v5_orders_2(k3_yellow_1(A_51)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_89,c_770])).

tff(c_994,plain,(
    ! [A_140,B_141,C_142] :
      ( k13_lattice3(k3_yellow_1(A_140),B_141,C_142) = k10_lattice3(k3_yellow_1(A_140),B_141,C_142)
      | ~ m1_subset_1(C_142,k9_setfam_1(A_140))
      | ~ m1_subset_1(B_141,k9_setfam_1(A_140)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_447,c_22,c_89,c_790])).

tff(c_1126,plain,(
    ! [B_147] :
      ( k13_lattice3(k3_yellow_1('#skF_6'),B_147,'#skF_8') = k10_lattice3(k3_yellow_1('#skF_6'),B_147,'#skF_8')
      | ~ m1_subset_1(B_147,k9_setfam_1('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_108,c_994])).

tff(c_1161,plain,(
    k13_lattice3(k3_yellow_1('#skF_6'),'#skF_7','#skF_8') = k10_lattice3(k3_yellow_1('#skF_6'),'#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_109,c_1126])).

tff(c_1184,plain,(
    k13_lattice3(k3_yellow_1('#skF_6'),'#skF_7','#skF_8') = k2_xboole_0('#skF_7','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_625,c_1161])).

tff(c_1186,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_143,c_1184])).

tff(c_1187,plain,(
    ! [B_6] : ~ v1_xboole_0(B_6) ),
    inference(splitRight,[status(thm)],[c_343])).

tff(c_66,plain,(
    ! [A_29,B_33,C_35] :
      ( k10_lattice3(k2_yellow_1(A_29),B_33,C_35) = k2_xboole_0(B_33,C_35)
      | ~ r2_hidden(k2_xboole_0(B_33,C_35),A_29)
      | ~ m1_subset_1(C_35,A_29)
      | ~ m1_subset_1(B_33,A_29)
      | v1_xboole_0(A_29) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_50,c_56])).

tff(c_1395,plain,(
    ! [A_190,B_191,C_192] :
      ( k10_lattice3(k2_yellow_1(A_190),B_191,C_192) = k2_xboole_0(B_191,C_192)
      | ~ r2_hidden(k2_xboole_0(B_191,C_192),A_190)
      | ~ m1_subset_1(C_192,A_190)
      | ~ m1_subset_1(B_191,A_190) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1187,c_66])).

tff(c_1398,plain,(
    ! [A_17,B_18,C_20] :
      ( k10_lattice3(k2_yellow_1(k9_setfam_1(A_17)),B_18,C_20) = k2_xboole_0(B_18,C_20)
      | ~ m1_subset_1(C_20,k9_setfam_1(A_17))
      | ~ m1_subset_1(B_18,k9_setfam_1(A_17)) ) ),
    inference(resolution,[status(thm)],[c_1242,c_1395])).

tff(c_1430,plain,(
    ! [A_196,B_197,C_198] :
      ( k10_lattice3(k3_yellow_1(A_196),B_197,C_198) = k2_xboole_0(B_197,C_198)
      | ~ m1_subset_1(C_198,k9_setfam_1(A_196))
      | ~ m1_subset_1(B_197,k9_setfam_1(A_196)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_1398])).

tff(c_1529,plain,(
    ! [B_203] :
      ( k10_lattice3(k3_yellow_1('#skF_6'),B_203,'#skF_8') = k2_xboole_0(B_203,'#skF_8')
      | ~ m1_subset_1(B_203,k9_setfam_1('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_108,c_1430])).

tff(c_1575,plain,(
    k10_lattice3(k3_yellow_1('#skF_6'),'#skF_7','#skF_8') = k2_xboole_0('#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_109,c_1529])).

tff(c_40,plain,(
    ! [A_21] :
      ( r2_hidden('#skF_3'(A_21),A_21)
      | v1_lattice3(k2_yellow_1(A_21))
      | v1_xboole_0(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_1227,plain,(
    ! [A_156] :
      ( r2_hidden('#skF_3'(A_156),A_156)
      | v1_lattice3(k2_yellow_1(A_156)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1187,c_40])).

tff(c_1200,plain,(
    ! [B_6,A_5] :
      ( m1_subset_1(B_6,A_5)
      | ~ r2_hidden(B_6,A_5) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1187,c_6])).

tff(c_1231,plain,(
    ! [A_156] :
      ( m1_subset_1('#skF_3'(A_156),A_156)
      | v1_lattice3(k2_yellow_1(A_156)) ) ),
    inference(resolution,[status(thm)],[c_1227,c_1200])).

tff(c_1194,plain,(
    ! [A_69] :
      ( m1_subset_1('#skF_2'(A_69),A_69)
      | v1_lattice3(k2_yellow_1(A_69)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1187,c_184])).

tff(c_1292,plain,(
    ! [A_170] :
      ( ~ r2_hidden(k2_xboole_0('#skF_2'(A_170),'#skF_3'(A_170)),A_170)
      | v1_lattice3(k2_yellow_1(A_170)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1187,c_38])).

tff(c_1296,plain,(
    ! [A_17] :
      ( v1_lattice3(k2_yellow_1(k9_setfam_1(A_17)))
      | ~ m1_subset_1('#skF_3'(k9_setfam_1(A_17)),k9_setfam_1(A_17))
      | ~ m1_subset_1('#skF_2'(k9_setfam_1(A_17)),k9_setfam_1(A_17)) ) ),
    inference(resolution,[status(thm)],[c_1242,c_1292])).

tff(c_1388,plain,(
    ! [A_189] :
      ( v1_lattice3(k3_yellow_1(A_189))
      | ~ m1_subset_1('#skF_3'(k9_setfam_1(A_189)),k9_setfam_1(A_189))
      | ~ m1_subset_1('#skF_2'(k9_setfam_1(A_189)),k9_setfam_1(A_189)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_1296])).

tff(c_1391,plain,(
    ! [A_189] :
      ( v1_lattice3(k3_yellow_1(A_189))
      | ~ m1_subset_1('#skF_3'(k9_setfam_1(A_189)),k9_setfam_1(A_189))
      | v1_lattice3(k2_yellow_1(k9_setfam_1(A_189))) ) ),
    inference(resolution,[status(thm)],[c_1194,c_1388])).

tff(c_1406,plain,(
    ! [A_193] :
      ( v1_lattice3(k3_yellow_1(A_193))
      | ~ m1_subset_1('#skF_3'(k9_setfam_1(A_193)),k9_setfam_1(A_193))
      | v1_lattice3(k3_yellow_1(A_193)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_1391])).

tff(c_1409,plain,(
    ! [A_193] :
      ( v1_lattice3(k3_yellow_1(A_193))
      | v1_lattice3(k2_yellow_1(k9_setfam_1(A_193))) ) ),
    inference(resolution,[status(thm)],[c_1231,c_1406])).

tff(c_1411,plain,(
    ! [A_193] :
      ( v1_lattice3(k3_yellow_1(A_193))
      | v1_lattice3(k3_yellow_1(A_193)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_1409])).

tff(c_1420,plain,(
    ! [A_193] : v1_lattice3(k3_yellow_1(A_193)) ),
    inference(factorization,[status(thm),theory(equality)],[c_1411])).

tff(c_1339,plain,(
    ! [A_183,B_184,C_185] :
      ( k13_lattice3(A_183,B_184,C_185) = k10_lattice3(A_183,B_184,C_185)
      | ~ m1_subset_1(C_185,u1_struct_0(A_183))
      | ~ m1_subset_1(B_184,u1_struct_0(A_183))
      | ~ l1_orders_2(A_183)
      | ~ v1_lattice3(A_183)
      | ~ v5_orders_2(A_183) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_1358,plain,(
    ! [A_27,B_184,C_185] :
      ( k13_lattice3(k2_yellow_1(A_27),B_184,C_185) = k10_lattice3(k2_yellow_1(A_27),B_184,C_185)
      | ~ m1_subset_1(C_185,A_27)
      | ~ m1_subset_1(B_184,u1_struct_0(k2_yellow_1(A_27)))
      | ~ l1_orders_2(k2_yellow_1(A_27))
      | ~ v1_lattice3(k2_yellow_1(A_27))
      | ~ v5_orders_2(k2_yellow_1(A_27)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_1339])).

tff(c_1936,plain,(
    ! [A_224,B_225,C_226] :
      ( k13_lattice3(k2_yellow_1(A_224),B_225,C_226) = k10_lattice3(k2_yellow_1(A_224),B_225,C_226)
      | ~ m1_subset_1(C_226,A_224)
      | ~ m1_subset_1(B_225,A_224)
      | ~ l1_orders_2(k2_yellow_1(A_224))
      | ~ v1_lattice3(k2_yellow_1(A_224))
      | ~ v5_orders_2(k2_yellow_1(A_224)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_1358])).

tff(c_1938,plain,(
    ! [A_28,B_225,C_226] :
      ( k13_lattice3(k2_yellow_1(k9_setfam_1(A_28)),B_225,C_226) = k10_lattice3(k2_yellow_1(k9_setfam_1(A_28)),B_225,C_226)
      | ~ m1_subset_1(C_226,k9_setfam_1(A_28))
      | ~ m1_subset_1(B_225,k9_setfam_1(A_28))
      | ~ l1_orders_2(k2_yellow_1(k9_setfam_1(A_28)))
      | ~ v1_lattice3(k2_yellow_1(k9_setfam_1(A_28)))
      | ~ v5_orders_2(k3_yellow_1(A_28)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_1936])).

tff(c_1949,plain,(
    ! [A_227,B_228,C_229] :
      ( k13_lattice3(k3_yellow_1(A_227),B_228,C_229) = k10_lattice3(k3_yellow_1(A_227),B_228,C_229)
      | ~ m1_subset_1(C_229,k9_setfam_1(A_227))
      | ~ m1_subset_1(B_228,k9_setfam_1(A_227)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_1420,c_54,c_22,c_54,c_54,c_54,c_1938])).

tff(c_2049,plain,(
    ! [B_231] :
      ( k13_lattice3(k3_yellow_1('#skF_6'),B_231,'#skF_8') = k10_lattice3(k3_yellow_1('#skF_6'),B_231,'#skF_8')
      | ~ m1_subset_1(B_231,k9_setfam_1('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_108,c_1949])).

tff(c_2080,plain,(
    k13_lattice3(k3_yellow_1('#skF_6'),'#skF_7','#skF_8') = k10_lattice3(k3_yellow_1('#skF_6'),'#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_109,c_2049])).

tff(c_2097,plain,(
    k13_lattice3(k3_yellow_1('#skF_6'),'#skF_7','#skF_8') = k2_xboole_0('#skF_7','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1575,c_2080])).

tff(c_2099,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_143,c_2097])).

tff(c_2100,plain,(
    ! [B_6] : ~ v1_xboole_0(B_6) ),
    inference(splitRight,[status(thm)],[c_299])).

tff(c_2287,plain,(
    ! [A_271,B_272,C_273] :
      ( k10_lattice3(k2_yellow_1(A_271),B_272,C_273) = k2_xboole_0(B_272,C_273)
      | ~ r2_hidden(k2_xboole_0(B_272,C_273),A_271)
      | ~ m1_subset_1(C_273,A_271)
      | ~ m1_subset_1(B_272,A_271) ) ),
    inference(negUnitSimplification,[status(thm)],[c_2100,c_66])).

tff(c_2290,plain,(
    ! [A_17,B_18,C_20] :
      ( k10_lattice3(k2_yellow_1(k9_setfam_1(A_17)),B_18,C_20) = k2_xboole_0(B_18,C_20)
      | ~ m1_subset_1(C_20,k9_setfam_1(A_17))
      | ~ m1_subset_1(B_18,k9_setfam_1(A_17)) ) ),
    inference(resolution,[status(thm)],[c_2135,c_2287])).

tff(c_2512,plain,(
    ! [A_291,B_292,C_293] :
      ( k10_lattice3(k3_yellow_1(A_291),B_292,C_293) = k2_xboole_0(B_292,C_293)
      | ~ m1_subset_1(C_293,k9_setfam_1(A_291))
      | ~ m1_subset_1(B_292,k9_setfam_1(A_291)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_2290])).

tff(c_2605,plain,(
    ! [B_295] :
      ( k10_lattice3(k3_yellow_1('#skF_6'),B_295,'#skF_8') = k2_xboole_0(B_295,'#skF_8')
      | ~ m1_subset_1(B_295,k9_setfam_1('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_108,c_2512])).

tff(c_2651,plain,(
    k10_lattice3(k3_yellow_1('#skF_6'),'#skF_7','#skF_8') = k2_xboole_0('#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_109,c_2605])).

tff(c_2146,plain,(
    ! [A_243] :
      ( r2_hidden('#skF_3'(A_243),A_243)
      | v1_lattice3(k2_yellow_1(A_243)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_2100,c_40])).

tff(c_2113,plain,(
    ! [B_6,A_5] :
      ( m1_subset_1(B_6,A_5)
      | ~ r2_hidden(B_6,A_5) ) ),
    inference(negUnitSimplification,[status(thm)],[c_2100,c_6])).

tff(c_2150,plain,(
    ! [A_243] :
      ( m1_subset_1('#skF_3'(A_243),A_243)
      | v1_lattice3(k2_yellow_1(A_243)) ) ),
    inference(resolution,[status(thm)],[c_2146,c_2113])).

tff(c_42,plain,(
    ! [A_21] :
      ( r2_hidden('#skF_2'(A_21),A_21)
      | v1_lattice3(k2_yellow_1(A_21))
      | v1_xboole_0(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_2141,plain,(
    ! [A_242] :
      ( r2_hidden('#skF_2'(A_242),A_242)
      | v1_lattice3(k2_yellow_1(A_242)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_2100,c_42])).

tff(c_2145,plain,(
    ! [A_242] :
      ( m1_subset_1('#skF_2'(A_242),A_242)
      | v1_lattice3(k2_yellow_1(A_242)) ) ),
    inference(resolution,[status(thm)],[c_2141,c_2113])).

tff(c_2205,plain,(
    ! [A_254] :
      ( ~ r2_hidden(k2_xboole_0('#skF_2'(A_254),'#skF_3'(A_254)),A_254)
      | v1_lattice3(k2_yellow_1(A_254)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_2100,c_38])).

tff(c_2209,plain,(
    ! [A_17] :
      ( v1_lattice3(k2_yellow_1(k9_setfam_1(A_17)))
      | ~ m1_subset_1('#skF_3'(k9_setfam_1(A_17)),k9_setfam_1(A_17))
      | ~ m1_subset_1('#skF_2'(k9_setfam_1(A_17)),k9_setfam_1(A_17)) ) ),
    inference(resolution,[status(thm)],[c_2135,c_2205])).

tff(c_2274,plain,(
    ! [A_269] :
      ( v1_lattice3(k3_yellow_1(A_269))
      | ~ m1_subset_1('#skF_3'(k9_setfam_1(A_269)),k9_setfam_1(A_269))
      | ~ m1_subset_1('#skF_2'(k9_setfam_1(A_269)),k9_setfam_1(A_269)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_2209])).

tff(c_2277,plain,(
    ! [A_269] :
      ( v1_lattice3(k3_yellow_1(A_269))
      | ~ m1_subset_1('#skF_3'(k9_setfam_1(A_269)),k9_setfam_1(A_269))
      | v1_lattice3(k2_yellow_1(k9_setfam_1(A_269))) ) ),
    inference(resolution,[status(thm)],[c_2145,c_2274])).

tff(c_2280,plain,(
    ! [A_270] :
      ( v1_lattice3(k3_yellow_1(A_270))
      | ~ m1_subset_1('#skF_3'(k9_setfam_1(A_270)),k9_setfam_1(A_270))
      | v1_lattice3(k3_yellow_1(A_270)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_2277])).

tff(c_2283,plain,(
    ! [A_270] :
      ( v1_lattice3(k3_yellow_1(A_270))
      | v1_lattice3(k2_yellow_1(k9_setfam_1(A_270))) ) ),
    inference(resolution,[status(thm)],[c_2150,c_2280])).

tff(c_2285,plain,(
    ! [A_270] :
      ( v1_lattice3(k3_yellow_1(A_270))
      | v1_lattice3(k3_yellow_1(A_270)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_2283])).

tff(c_2306,plain,(
    ! [A_270] : v1_lattice3(k3_yellow_1(A_270)) ),
    inference(factorization,[status(thm),theory(equality)],[c_2285])).

tff(c_2231,plain,(
    ! [A_260,B_261,C_262] :
      ( k13_lattice3(A_260,B_261,C_262) = k10_lattice3(A_260,B_261,C_262)
      | ~ m1_subset_1(C_262,u1_struct_0(A_260))
      | ~ m1_subset_1(B_261,u1_struct_0(A_260))
      | ~ l1_orders_2(A_260)
      | ~ v1_lattice3(A_260)
      | ~ v5_orders_2(A_260) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_2250,plain,(
    ! [A_27,B_261,C_262] :
      ( k13_lattice3(k2_yellow_1(A_27),B_261,C_262) = k10_lattice3(k2_yellow_1(A_27),B_261,C_262)
      | ~ m1_subset_1(C_262,A_27)
      | ~ m1_subset_1(B_261,u1_struct_0(k2_yellow_1(A_27)))
      | ~ l1_orders_2(k2_yellow_1(A_27))
      | ~ v1_lattice3(k2_yellow_1(A_27))
      | ~ v5_orders_2(k2_yellow_1(A_27)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_2231])).

tff(c_2661,plain,(
    ! [A_296,B_297,C_298] :
      ( k13_lattice3(k2_yellow_1(A_296),B_297,C_298) = k10_lattice3(k2_yellow_1(A_296),B_297,C_298)
      | ~ m1_subset_1(C_298,A_296)
      | ~ m1_subset_1(B_297,A_296)
      | ~ l1_orders_2(k2_yellow_1(A_296))
      | ~ v1_lattice3(k2_yellow_1(A_296))
      | ~ v5_orders_2(k2_yellow_1(A_296)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_2250])).

tff(c_2663,plain,(
    ! [A_28,B_297,C_298] :
      ( k13_lattice3(k2_yellow_1(k9_setfam_1(A_28)),B_297,C_298) = k10_lattice3(k2_yellow_1(k9_setfam_1(A_28)),B_297,C_298)
      | ~ m1_subset_1(C_298,k9_setfam_1(A_28))
      | ~ m1_subset_1(B_297,k9_setfam_1(A_28))
      | ~ l1_orders_2(k2_yellow_1(k9_setfam_1(A_28)))
      | ~ v1_lattice3(k2_yellow_1(k9_setfam_1(A_28)))
      | ~ v5_orders_2(k3_yellow_1(A_28)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_2661])).

tff(c_2703,plain,(
    ! [A_305,B_306,C_307] :
      ( k13_lattice3(k3_yellow_1(A_305),B_306,C_307) = k10_lattice3(k3_yellow_1(A_305),B_306,C_307)
      | ~ m1_subset_1(C_307,k9_setfam_1(A_305))
      | ~ m1_subset_1(B_306,k9_setfam_1(A_305)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_2306,c_54,c_22,c_54,c_54,c_54,c_2663])).

tff(c_2804,plain,(
    ! [B_312] :
      ( k13_lattice3(k3_yellow_1('#skF_6'),B_312,'#skF_8') = k10_lattice3(k3_yellow_1('#skF_6'),B_312,'#skF_8')
      | ~ m1_subset_1(B_312,k9_setfam_1('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_108,c_2703])).

tff(c_2835,plain,(
    k13_lattice3(k3_yellow_1('#skF_6'),'#skF_7','#skF_8') = k10_lattice3(k3_yellow_1('#skF_6'),'#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_109,c_2804])).

tff(c_2852,plain,(
    k13_lattice3(k3_yellow_1('#skF_6'),'#skF_7','#skF_8') = k2_xboole_0('#skF_7','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2651,c_2835])).

tff(c_2854,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_143,c_2852])).

tff(c_2855,plain,(
    k12_lattice3(k3_yellow_1('#skF_6'),'#skF_7','#skF_8') != k3_xboole_0('#skF_7','#skF_8') ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_2962,plain,(
    ! [B_18,C_20,A_17] :
      ( r2_hidden(k3_xboole_0(B_18,C_20),k9_setfam_1(A_17))
      | ~ m1_subset_1(C_20,k9_setfam_1(A_17))
      | ~ m1_subset_1(B_18,k9_setfam_1(A_17)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_89,c_36])).

tff(c_2963,plain,(
    ! [B_332,C_333,A_334] :
      ( r2_hidden(k3_xboole_0(B_332,C_333),k9_setfam_1(A_334))
      | ~ m1_subset_1(C_333,k9_setfam_1(A_334))
      | ~ m1_subset_1(B_332,k9_setfam_1(A_334)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_89,c_36])).

tff(c_2978,plain,(
    ! [A_335,C_336,B_337] :
      ( ~ v1_xboole_0(k9_setfam_1(A_335))
      | ~ m1_subset_1(C_336,k9_setfam_1(A_335))
      | ~ m1_subset_1(B_337,k9_setfam_1(A_335)) ) ),
    inference(resolution,[status(thm)],[c_2963,c_2])).

tff(c_3010,plain,(
    ! [B_337,A_335,B_6] :
      ( ~ m1_subset_1(B_337,k9_setfam_1(A_335))
      | ~ v1_xboole_0(B_6)
      | ~ v1_xboole_0(k9_setfam_1(A_335)) ) ),
    inference(resolution,[status(thm)],[c_10,c_2978])).

tff(c_3014,plain,(
    ! [B_338,A_339] :
      ( ~ m1_subset_1(B_338,k9_setfam_1(A_339))
      | ~ v1_xboole_0(k9_setfam_1(A_339)) ) ),
    inference(splitLeft,[status(thm)],[c_3010])).

tff(c_3054,plain,(
    ! [B_6,A_339] :
      ( ~ v1_xboole_0(B_6)
      | ~ v1_xboole_0(k9_setfam_1(A_339)) ) ),
    inference(resolution,[status(thm)],[c_10,c_3014])).

tff(c_3057,plain,(
    ! [A_339] : ~ v1_xboole_0(k9_setfam_1(A_339)) ),
    inference(splitLeft,[status(thm)],[c_3054])).

tff(c_58,plain,(
    ! [A_36,B_40,C_42] :
      ( k11_lattice3(k2_yellow_1(A_36),B_40,C_42) = k3_xboole_0(B_40,C_42)
      | ~ r2_hidden(k3_xboole_0(B_40,C_42),A_36)
      | ~ m1_subset_1(C_42,u1_struct_0(k2_yellow_1(A_36)))
      | ~ m1_subset_1(B_40,u1_struct_0(k2_yellow_1(A_36)))
      | v1_xboole_0(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_3356,plain,(
    ! [A_364,B_365,C_366] :
      ( k11_lattice3(k2_yellow_1(A_364),B_365,C_366) = k3_xboole_0(B_365,C_366)
      | ~ r2_hidden(k3_xboole_0(B_365,C_366),A_364)
      | ~ m1_subset_1(C_366,A_364)
      | ~ m1_subset_1(B_365,A_364)
      | v1_xboole_0(A_364) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_50,c_58])).

tff(c_3359,plain,(
    ! [A_17,B_18,C_20] :
      ( k11_lattice3(k2_yellow_1(k9_setfam_1(A_17)),B_18,C_20) = k3_xboole_0(B_18,C_20)
      | v1_xboole_0(k9_setfam_1(A_17))
      | ~ m1_subset_1(C_20,k9_setfam_1(A_17))
      | ~ m1_subset_1(B_18,k9_setfam_1(A_17)) ) ),
    inference(resolution,[status(thm)],[c_2962,c_3356])).

tff(c_3365,plain,(
    ! [A_17,B_18,C_20] :
      ( k11_lattice3(k3_yellow_1(A_17),B_18,C_20) = k3_xboole_0(B_18,C_20)
      | v1_xboole_0(k9_setfam_1(A_17))
      | ~ m1_subset_1(C_20,k9_setfam_1(A_17))
      | ~ m1_subset_1(B_18,k9_setfam_1(A_17)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_3359])).

tff(c_3385,plain,(
    ! [A_369,B_370,C_371] :
      ( k11_lattice3(k3_yellow_1(A_369),B_370,C_371) = k3_xboole_0(B_370,C_371)
      | ~ m1_subset_1(C_371,k9_setfam_1(A_369))
      | ~ m1_subset_1(B_370,k9_setfam_1(A_369)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_3057,c_3365])).

tff(c_3523,plain,(
    ! [B_376] :
      ( k11_lattice3(k3_yellow_1('#skF_6'),B_376,'#skF_8') = k3_xboole_0(B_376,'#skF_8')
      | ~ m1_subset_1(B_376,k9_setfam_1('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_108,c_3385])).

tff(c_3575,plain,(
    k11_lattice3(k3_yellow_1('#skF_6'),'#skF_7','#skF_8') = k3_xboole_0('#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_109,c_3523])).

tff(c_2912,plain,(
    ! [A_324] :
      ( r2_hidden('#skF_4'(A_324),A_324)
      | v2_lattice3(k2_yellow_1(A_324))
      | v1_xboole_0(A_324) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_2919,plain,(
    ! [A_324] :
      ( m1_subset_1('#skF_4'(A_324),A_324)
      | v2_lattice3(k2_yellow_1(A_324))
      | v1_xboole_0(A_324) ) ),
    inference(resolution,[status(thm)],[c_2912,c_6])).

tff(c_2921,plain,(
    ! [A_325] :
      ( r2_hidden('#skF_5'(A_325),A_325)
      | v2_lattice3(k2_yellow_1(A_325))
      | v1_xboole_0(A_325) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_2928,plain,(
    ! [A_325] :
      ( m1_subset_1('#skF_5'(A_325),A_325)
      | v2_lattice3(k2_yellow_1(A_325))
      | v1_xboole_0(A_325) ) ),
    inference(resolution,[status(thm)],[c_2921,c_6])).

tff(c_2976,plain,(
    ! [B_332,C_333,A_334] :
      ( m1_subset_1(k3_xboole_0(B_332,C_333),k9_setfam_1(A_334))
      | v1_xboole_0(k9_setfam_1(A_334))
      | ~ m1_subset_1(C_333,k9_setfam_1(A_334))
      | ~ m1_subset_1(B_332,k9_setfam_1(A_334)) ) ),
    inference(resolution,[status(thm)],[c_2963,c_6])).

tff(c_3618,plain,(
    ! [B_384,C_385,A_386] :
      ( m1_subset_1(k3_xboole_0(B_384,C_385),k9_setfam_1(A_386))
      | ~ m1_subset_1(C_385,k9_setfam_1(A_386))
      | ~ m1_subset_1(B_384,k9_setfam_1(A_386)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_3057,c_2976])).

tff(c_8,plain,(
    ! [B_6,A_5] :
      ( r2_hidden(B_6,A_5)
      | ~ m1_subset_1(B_6,A_5)
      | v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_2940,plain,(
    ! [A_328] :
      ( ~ r2_hidden(k3_xboole_0('#skF_4'(A_328),'#skF_5'(A_328)),A_328)
      | v2_lattice3(k2_yellow_1(A_328))
      | v1_xboole_0(A_328) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_2945,plain,(
    ! [A_5] :
      ( v2_lattice3(k2_yellow_1(A_5))
      | ~ m1_subset_1(k3_xboole_0('#skF_4'(A_5),'#skF_5'(A_5)),A_5)
      | v1_xboole_0(A_5) ) ),
    inference(resolution,[status(thm)],[c_8,c_2940])).

tff(c_3645,plain,(
    ! [A_386] :
      ( v2_lattice3(k2_yellow_1(k9_setfam_1(A_386)))
      | v1_xboole_0(k9_setfam_1(A_386))
      | ~ m1_subset_1('#skF_5'(k9_setfam_1(A_386)),k9_setfam_1(A_386))
      | ~ m1_subset_1('#skF_4'(k9_setfam_1(A_386)),k9_setfam_1(A_386)) ) ),
    inference(resolution,[status(thm)],[c_3618,c_2945])).

tff(c_3659,plain,(
    ! [A_386] :
      ( v2_lattice3(k3_yellow_1(A_386))
      | v1_xboole_0(k9_setfam_1(A_386))
      | ~ m1_subset_1('#skF_5'(k9_setfam_1(A_386)),k9_setfam_1(A_386))
      | ~ m1_subset_1('#skF_4'(k9_setfam_1(A_386)),k9_setfam_1(A_386)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_3645])).

tff(c_3662,plain,(
    ! [A_387] :
      ( v2_lattice3(k3_yellow_1(A_387))
      | ~ m1_subset_1('#skF_5'(k9_setfam_1(A_387)),k9_setfam_1(A_387))
      | ~ m1_subset_1('#skF_4'(k9_setfam_1(A_387)),k9_setfam_1(A_387)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_3057,c_3659])).

tff(c_3665,plain,(
    ! [A_387] :
      ( v2_lattice3(k3_yellow_1(A_387))
      | ~ m1_subset_1('#skF_4'(k9_setfam_1(A_387)),k9_setfam_1(A_387))
      | v2_lattice3(k2_yellow_1(k9_setfam_1(A_387)))
      | v1_xboole_0(k9_setfam_1(A_387)) ) ),
    inference(resolution,[status(thm)],[c_2928,c_3662])).

tff(c_3670,plain,(
    ! [A_387] :
      ( v2_lattice3(k3_yellow_1(A_387))
      | ~ m1_subset_1('#skF_4'(k9_setfam_1(A_387)),k9_setfam_1(A_387))
      | v2_lattice3(k3_yellow_1(A_387))
      | v1_xboole_0(k9_setfam_1(A_387)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_3665])).

tff(c_3673,plain,(
    ! [A_388] :
      ( v2_lattice3(k3_yellow_1(A_388))
      | ~ m1_subset_1('#skF_4'(k9_setfam_1(A_388)),k9_setfam_1(A_388))
      | v2_lattice3(k3_yellow_1(A_388)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_3057,c_3670])).

tff(c_3676,plain,(
    ! [A_388] :
      ( v2_lattice3(k3_yellow_1(A_388))
      | v2_lattice3(k2_yellow_1(k9_setfam_1(A_388)))
      | v1_xboole_0(k9_setfam_1(A_388)) ) ),
    inference(resolution,[status(thm)],[c_2919,c_3673])).

tff(c_3681,plain,(
    ! [A_388] :
      ( v2_lattice3(k3_yellow_1(A_388))
      | v2_lattice3(k3_yellow_1(A_388))
      | v1_xboole_0(k9_setfam_1(A_388)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_3676])).

tff(c_3682,plain,(
    ! [A_388] :
      ( v2_lattice3(k3_yellow_1(A_388))
      | v2_lattice3(k3_yellow_1(A_388)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_3057,c_3681])).

tff(c_3701,plain,(
    ! [A_388] : v2_lattice3(k3_yellow_1(A_388)) ),
    inference(factorization,[status(thm),theory(equality)],[c_3682])).

tff(c_3102,plain,(
    ! [A_349,B_350,C_351] :
      ( k12_lattice3(A_349,B_350,C_351) = k11_lattice3(A_349,B_350,C_351)
      | ~ m1_subset_1(C_351,u1_struct_0(A_349))
      | ~ m1_subset_1(B_350,u1_struct_0(A_349))
      | ~ l1_orders_2(A_349)
      | ~ v2_lattice3(A_349)
      | ~ v5_orders_2(A_349) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_3122,plain,(
    ! [A_51,B_350,C_351] :
      ( k12_lattice3(k3_yellow_1(A_51),B_350,C_351) = k11_lattice3(k3_yellow_1(A_51),B_350,C_351)
      | ~ m1_subset_1(C_351,k9_setfam_1(A_51))
      | ~ m1_subset_1(B_350,u1_struct_0(k3_yellow_1(A_51)))
      | ~ l1_orders_2(k3_yellow_1(A_51))
      | ~ v2_lattice3(k3_yellow_1(A_51))
      | ~ v5_orders_2(k3_yellow_1(A_51)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_89,c_3102])).

tff(c_3132,plain,(
    ! [A_51,B_350,C_351] :
      ( k12_lattice3(k3_yellow_1(A_51),B_350,C_351) = k11_lattice3(k3_yellow_1(A_51),B_350,C_351)
      | ~ m1_subset_1(C_351,k9_setfam_1(A_51))
      | ~ m1_subset_1(B_350,k9_setfam_1(A_51))
      | ~ v2_lattice3(k3_yellow_1(A_51)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_22,c_89,c_3122])).

tff(c_4046,plain,(
    ! [A_424,B_425,C_426] :
      ( k12_lattice3(k3_yellow_1(A_424),B_425,C_426) = k11_lattice3(k3_yellow_1(A_424),B_425,C_426)
      | ~ m1_subset_1(C_426,k9_setfam_1(A_424))
      | ~ m1_subset_1(B_425,k9_setfam_1(A_424)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3701,c_3132])).

tff(c_4154,plain,(
    ! [B_428] :
      ( k12_lattice3(k3_yellow_1('#skF_6'),B_428,'#skF_8') = k11_lattice3(k3_yellow_1('#skF_6'),B_428,'#skF_8')
      | ~ m1_subset_1(B_428,k9_setfam_1('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_108,c_4046])).

tff(c_4189,plain,(
    k12_lattice3(k3_yellow_1('#skF_6'),'#skF_7','#skF_8') = k11_lattice3(k3_yellow_1('#skF_6'),'#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_109,c_4154])).

tff(c_4212,plain,(
    k12_lattice3(k3_yellow_1('#skF_6'),'#skF_7','#skF_8') = k3_xboole_0('#skF_7','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3575,c_4189])).

tff(c_4214,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2855,c_4212])).

tff(c_4215,plain,(
    ! [B_6] : ~ v1_xboole_0(B_6) ),
    inference(splitRight,[status(thm)],[c_3054])).

tff(c_65,plain,(
    ! [A_36,B_40,C_42] :
      ( k11_lattice3(k2_yellow_1(A_36),B_40,C_42) = k3_xboole_0(B_40,C_42)
      | ~ r2_hidden(k3_xboole_0(B_40,C_42),A_36)
      | ~ m1_subset_1(C_42,A_36)
      | ~ m1_subset_1(B_40,A_36)
      | v1_xboole_0(A_36) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_50,c_58])).

tff(c_4336,plain,(
    ! [A_454,B_455,C_456] :
      ( k11_lattice3(k2_yellow_1(A_454),B_455,C_456) = k3_xboole_0(B_455,C_456)
      | ~ r2_hidden(k3_xboole_0(B_455,C_456),A_454)
      | ~ m1_subset_1(C_456,A_454)
      | ~ m1_subset_1(B_455,A_454) ) ),
    inference(negUnitSimplification,[status(thm)],[c_4215,c_65])).

tff(c_4343,plain,(
    ! [A_17,B_18,C_20] :
      ( k11_lattice3(k2_yellow_1(k9_setfam_1(A_17)),B_18,C_20) = k3_xboole_0(B_18,C_20)
      | ~ m1_subset_1(C_20,k9_setfam_1(A_17))
      | ~ m1_subset_1(B_18,k9_setfam_1(A_17)) ) ),
    inference(resolution,[status(thm)],[c_2962,c_4336])).

tff(c_4621,plain,(
    ! [A_485,B_486,C_487] :
      ( k11_lattice3(k3_yellow_1(A_485),B_486,C_487) = k3_xboole_0(B_486,C_487)
      | ~ m1_subset_1(C_487,k9_setfam_1(A_485))
      | ~ m1_subset_1(B_486,k9_setfam_1(A_485)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_4343])).

tff(c_4720,plain,(
    ! [B_492] :
      ( k11_lattice3(k3_yellow_1('#skF_6'),B_492,'#skF_8') = k3_xboole_0(B_492,'#skF_8')
      | ~ m1_subset_1(B_492,k9_setfam_1('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_108,c_4621])).

tff(c_4766,plain,(
    k11_lattice3(k3_yellow_1('#skF_6'),'#skF_7','#skF_8') = k3_xboole_0('#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_109,c_4720])).

tff(c_48,plain,(
    ! [A_24] :
      ( r2_hidden('#skF_4'(A_24),A_24)
      | v2_lattice3(k2_yellow_1(A_24))
      | v1_xboole_0(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_4259,plain,(
    ! [A_438] :
      ( r2_hidden('#skF_4'(A_438),A_438)
      | v2_lattice3(k2_yellow_1(A_438)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_4215,c_48])).

tff(c_4228,plain,(
    ! [B_6,A_5] :
      ( m1_subset_1(B_6,A_5)
      | ~ r2_hidden(B_6,A_5) ) ),
    inference(negUnitSimplification,[status(thm)],[c_4215,c_6])).

tff(c_4263,plain,(
    ! [A_438] :
      ( m1_subset_1('#skF_4'(A_438),A_438)
      | v2_lattice3(k2_yellow_1(A_438)) ) ),
    inference(resolution,[status(thm)],[c_4259,c_4228])).

tff(c_46,plain,(
    ! [A_24] :
      ( r2_hidden('#skF_5'(A_24),A_24)
      | v2_lattice3(k2_yellow_1(A_24))
      | v1_xboole_0(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_4254,plain,(
    ! [A_437] :
      ( r2_hidden('#skF_5'(A_437),A_437)
      | v2_lattice3(k2_yellow_1(A_437)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_4215,c_46])).

tff(c_4258,plain,(
    ! [A_437] :
      ( m1_subset_1('#skF_5'(A_437),A_437)
      | v2_lattice3(k2_yellow_1(A_437)) ) ),
    inference(resolution,[status(thm)],[c_4254,c_4228])).

tff(c_44,plain,(
    ! [A_24] :
      ( ~ r2_hidden(k3_xboole_0('#skF_4'(A_24),'#skF_5'(A_24)),A_24)
      | v2_lattice3(k2_yellow_1(A_24))
      | v1_xboole_0(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_4278,plain,(
    ! [A_446] :
      ( ~ r2_hidden(k3_xboole_0('#skF_4'(A_446),'#skF_5'(A_446)),A_446)
      | v2_lattice3(k2_yellow_1(A_446)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_4215,c_44])).

tff(c_4286,plain,(
    ! [A_17] :
      ( v2_lattice3(k2_yellow_1(k9_setfam_1(A_17)))
      | ~ m1_subset_1('#skF_5'(k9_setfam_1(A_17)),k9_setfam_1(A_17))
      | ~ m1_subset_1('#skF_4'(k9_setfam_1(A_17)),k9_setfam_1(A_17)) ) ),
    inference(resolution,[status(thm)],[c_2962,c_4278])).

tff(c_4361,plain,(
    ! [A_463] :
      ( v2_lattice3(k3_yellow_1(A_463))
      | ~ m1_subset_1('#skF_5'(k9_setfam_1(A_463)),k9_setfam_1(A_463))
      | ~ m1_subset_1('#skF_4'(k9_setfam_1(A_463)),k9_setfam_1(A_463)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_4286])).

tff(c_4364,plain,(
    ! [A_463] :
      ( v2_lattice3(k3_yellow_1(A_463))
      | ~ m1_subset_1('#skF_4'(k9_setfam_1(A_463)),k9_setfam_1(A_463))
      | v2_lattice3(k2_yellow_1(k9_setfam_1(A_463))) ) ),
    inference(resolution,[status(thm)],[c_4258,c_4361])).

tff(c_4395,plain,(
    ! [A_467] :
      ( v2_lattice3(k3_yellow_1(A_467))
      | ~ m1_subset_1('#skF_4'(k9_setfam_1(A_467)),k9_setfam_1(A_467))
      | v2_lattice3(k3_yellow_1(A_467)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_4364])).

tff(c_4398,plain,(
    ! [A_467] :
      ( v2_lattice3(k3_yellow_1(A_467))
      | v2_lattice3(k2_yellow_1(k9_setfam_1(A_467))) ) ),
    inference(resolution,[status(thm)],[c_4263,c_4395])).

tff(c_4400,plain,(
    ! [A_467] :
      ( v2_lattice3(k3_yellow_1(A_467))
      | v2_lattice3(k3_yellow_1(A_467)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_4398])).

tff(c_4409,plain,(
    ! [A_467] : v2_lattice3(k3_yellow_1(A_467)) ),
    inference(factorization,[status(thm),theory(equality)],[c_4400])).

tff(c_4367,plain,(
    ! [A_464,B_465,C_466] :
      ( k12_lattice3(A_464,B_465,C_466) = k11_lattice3(A_464,B_465,C_466)
      | ~ m1_subset_1(C_466,u1_struct_0(A_464))
      | ~ m1_subset_1(B_465,u1_struct_0(A_464))
      | ~ l1_orders_2(A_464)
      | ~ v2_lattice3(A_464)
      | ~ v5_orders_2(A_464) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_4386,plain,(
    ! [A_27,B_465,C_466] :
      ( k12_lattice3(k2_yellow_1(A_27),B_465,C_466) = k11_lattice3(k2_yellow_1(A_27),B_465,C_466)
      | ~ m1_subset_1(C_466,A_27)
      | ~ m1_subset_1(B_465,u1_struct_0(k2_yellow_1(A_27)))
      | ~ l1_orders_2(k2_yellow_1(A_27))
      | ~ v2_lattice3(k2_yellow_1(A_27))
      | ~ v5_orders_2(k2_yellow_1(A_27)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_4367])).

tff(c_4964,plain,(
    ! [A_505,B_506,C_507] :
      ( k12_lattice3(k2_yellow_1(A_505),B_506,C_507) = k11_lattice3(k2_yellow_1(A_505),B_506,C_507)
      | ~ m1_subset_1(C_507,A_505)
      | ~ m1_subset_1(B_506,A_505)
      | ~ l1_orders_2(k2_yellow_1(A_505))
      | ~ v2_lattice3(k2_yellow_1(A_505))
      | ~ v5_orders_2(k2_yellow_1(A_505)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_4386])).

tff(c_4966,plain,(
    ! [A_28,B_506,C_507] :
      ( k12_lattice3(k2_yellow_1(k9_setfam_1(A_28)),B_506,C_507) = k11_lattice3(k2_yellow_1(k9_setfam_1(A_28)),B_506,C_507)
      | ~ m1_subset_1(C_507,k9_setfam_1(A_28))
      | ~ m1_subset_1(B_506,k9_setfam_1(A_28))
      | ~ l1_orders_2(k2_yellow_1(k9_setfam_1(A_28)))
      | ~ v2_lattice3(k2_yellow_1(k9_setfam_1(A_28)))
      | ~ v5_orders_2(k3_yellow_1(A_28)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_4964])).

tff(c_4973,plain,(
    ! [A_508,B_509,C_510] :
      ( k12_lattice3(k3_yellow_1(A_508),B_509,C_510) = k11_lattice3(k3_yellow_1(A_508),B_509,C_510)
      | ~ m1_subset_1(C_510,k9_setfam_1(A_508))
      | ~ m1_subset_1(B_509,k9_setfam_1(A_508)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_4409,c_54,c_22,c_54,c_54,c_54,c_4966])).

tff(c_5061,plain,(
    ! [B_512] :
      ( k12_lattice3(k3_yellow_1('#skF_6'),B_512,'#skF_8') = k11_lattice3(k3_yellow_1('#skF_6'),B_512,'#skF_8')
      | ~ m1_subset_1(B_512,k9_setfam_1('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_108,c_4973])).

tff(c_5092,plain,(
    k12_lattice3(k3_yellow_1('#skF_6'),'#skF_7','#skF_8') = k11_lattice3(k3_yellow_1('#skF_6'),'#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_109,c_5061])).

tff(c_5109,plain,(
    k12_lattice3(k3_yellow_1('#skF_6'),'#skF_7','#skF_8') = k3_xboole_0('#skF_7','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4766,c_5092])).

tff(c_5111,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2855,c_5109])).

tff(c_5112,plain,(
    ! [B_6] : ~ v1_xboole_0(B_6) ),
    inference(splitRight,[status(thm)],[c_3010])).

tff(c_5233,plain,(
    ! [A_538,B_539,C_540] :
      ( k11_lattice3(k2_yellow_1(A_538),B_539,C_540) = k3_xboole_0(B_539,C_540)
      | ~ r2_hidden(k3_xboole_0(B_539,C_540),A_538)
      | ~ m1_subset_1(C_540,A_538)
      | ~ m1_subset_1(B_539,A_538) ) ),
    inference(negUnitSimplification,[status(thm)],[c_5112,c_65])).

tff(c_5240,plain,(
    ! [A_17,B_18,C_20] :
      ( k11_lattice3(k2_yellow_1(k9_setfam_1(A_17)),B_18,C_20) = k3_xboole_0(B_18,C_20)
      | ~ m1_subset_1(C_20,k9_setfam_1(A_17))
      | ~ m1_subset_1(B_18,k9_setfam_1(A_17)) ) ),
    inference(resolution,[status(thm)],[c_2962,c_5233])).

tff(c_5518,plain,(
    ! [A_569,B_570,C_571] :
      ( k11_lattice3(k3_yellow_1(A_569),B_570,C_571) = k3_xboole_0(B_570,C_571)
      | ~ m1_subset_1(C_571,k9_setfam_1(A_569))
      | ~ m1_subset_1(B_570,k9_setfam_1(A_569)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_5240])).

tff(c_5617,plain,(
    ! [B_576] :
      ( k11_lattice3(k3_yellow_1('#skF_6'),B_576,'#skF_8') = k3_xboole_0(B_576,'#skF_8')
      | ~ m1_subset_1(B_576,k9_setfam_1('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_108,c_5518])).

tff(c_5663,plain,(
    k11_lattice3(k3_yellow_1('#skF_6'),'#skF_7','#skF_8') = k3_xboole_0('#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_109,c_5617])).

tff(c_5156,plain,(
    ! [A_522] :
      ( r2_hidden('#skF_4'(A_522),A_522)
      | v2_lattice3(k2_yellow_1(A_522)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_5112,c_48])).

tff(c_5125,plain,(
    ! [B_6,A_5] :
      ( m1_subset_1(B_6,A_5)
      | ~ r2_hidden(B_6,A_5) ) ),
    inference(negUnitSimplification,[status(thm)],[c_5112,c_6])).

tff(c_5160,plain,(
    ! [A_522] :
      ( m1_subset_1('#skF_4'(A_522),A_522)
      | v2_lattice3(k2_yellow_1(A_522)) ) ),
    inference(resolution,[status(thm)],[c_5156,c_5125])).

tff(c_5151,plain,(
    ! [A_521] :
      ( r2_hidden('#skF_5'(A_521),A_521)
      | v2_lattice3(k2_yellow_1(A_521)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_5112,c_46])).

tff(c_5155,plain,(
    ! [A_521] :
      ( m1_subset_1('#skF_5'(A_521),A_521)
      | v2_lattice3(k2_yellow_1(A_521)) ) ),
    inference(resolution,[status(thm)],[c_5151,c_5125])).

tff(c_5175,plain,(
    ! [A_530] :
      ( ~ r2_hidden(k3_xboole_0('#skF_4'(A_530),'#skF_5'(A_530)),A_530)
      | v2_lattice3(k2_yellow_1(A_530)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_5112,c_44])).

tff(c_5183,plain,(
    ! [A_17] :
      ( v2_lattice3(k2_yellow_1(k9_setfam_1(A_17)))
      | ~ m1_subset_1('#skF_5'(k9_setfam_1(A_17)),k9_setfam_1(A_17))
      | ~ m1_subset_1('#skF_4'(k9_setfam_1(A_17)),k9_setfam_1(A_17)) ) ),
    inference(resolution,[status(thm)],[c_2962,c_5175])).

tff(c_5258,plain,(
    ! [A_547] :
      ( v2_lattice3(k3_yellow_1(A_547))
      | ~ m1_subset_1('#skF_5'(k9_setfam_1(A_547)),k9_setfam_1(A_547))
      | ~ m1_subset_1('#skF_4'(k9_setfam_1(A_547)),k9_setfam_1(A_547)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_5183])).

tff(c_5261,plain,(
    ! [A_547] :
      ( v2_lattice3(k3_yellow_1(A_547))
      | ~ m1_subset_1('#skF_4'(k9_setfam_1(A_547)),k9_setfam_1(A_547))
      | v2_lattice3(k2_yellow_1(k9_setfam_1(A_547))) ) ),
    inference(resolution,[status(thm)],[c_5155,c_5258])).

tff(c_5292,plain,(
    ! [A_551] :
      ( v2_lattice3(k3_yellow_1(A_551))
      | ~ m1_subset_1('#skF_4'(k9_setfam_1(A_551)),k9_setfam_1(A_551))
      | v2_lattice3(k3_yellow_1(A_551)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_5261])).

tff(c_5295,plain,(
    ! [A_551] :
      ( v2_lattice3(k3_yellow_1(A_551))
      | v2_lattice3(k2_yellow_1(k9_setfam_1(A_551))) ) ),
    inference(resolution,[status(thm)],[c_5160,c_5292])).

tff(c_5297,plain,(
    ! [A_551] :
      ( v2_lattice3(k3_yellow_1(A_551))
      | v2_lattice3(k3_yellow_1(A_551)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_5295])).

tff(c_5306,plain,(
    ! [A_551] : v2_lattice3(k3_yellow_1(A_551)) ),
    inference(factorization,[status(thm),theory(equality)],[c_5297])).

tff(c_5264,plain,(
    ! [A_548,B_549,C_550] :
      ( k12_lattice3(A_548,B_549,C_550) = k11_lattice3(A_548,B_549,C_550)
      | ~ m1_subset_1(C_550,u1_struct_0(A_548))
      | ~ m1_subset_1(B_549,u1_struct_0(A_548))
      | ~ l1_orders_2(A_548)
      | ~ v2_lattice3(A_548)
      | ~ v5_orders_2(A_548) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_5283,plain,(
    ! [A_27,B_549,C_550] :
      ( k12_lattice3(k2_yellow_1(A_27),B_549,C_550) = k11_lattice3(k2_yellow_1(A_27),B_549,C_550)
      | ~ m1_subset_1(C_550,A_27)
      | ~ m1_subset_1(B_549,u1_struct_0(k2_yellow_1(A_27)))
      | ~ l1_orders_2(k2_yellow_1(A_27))
      | ~ v2_lattice3(k2_yellow_1(A_27))
      | ~ v5_orders_2(k2_yellow_1(A_27)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_5264])).

tff(c_5861,plain,(
    ! [A_589,B_590,C_591] :
      ( k12_lattice3(k2_yellow_1(A_589),B_590,C_591) = k11_lattice3(k2_yellow_1(A_589),B_590,C_591)
      | ~ m1_subset_1(C_591,A_589)
      | ~ m1_subset_1(B_590,A_589)
      | ~ l1_orders_2(k2_yellow_1(A_589))
      | ~ v2_lattice3(k2_yellow_1(A_589))
      | ~ v5_orders_2(k2_yellow_1(A_589)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_5283])).

tff(c_5863,plain,(
    ! [A_28,B_590,C_591] :
      ( k12_lattice3(k2_yellow_1(k9_setfam_1(A_28)),B_590,C_591) = k11_lattice3(k2_yellow_1(k9_setfam_1(A_28)),B_590,C_591)
      | ~ m1_subset_1(C_591,k9_setfam_1(A_28))
      | ~ m1_subset_1(B_590,k9_setfam_1(A_28))
      | ~ l1_orders_2(k2_yellow_1(k9_setfam_1(A_28)))
      | ~ v2_lattice3(k2_yellow_1(k9_setfam_1(A_28)))
      | ~ v5_orders_2(k3_yellow_1(A_28)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_5861])).

tff(c_5870,plain,(
    ! [A_592,B_593,C_594] :
      ( k12_lattice3(k3_yellow_1(A_592),B_593,C_594) = k11_lattice3(k3_yellow_1(A_592),B_593,C_594)
      | ~ m1_subset_1(C_594,k9_setfam_1(A_592))
      | ~ m1_subset_1(B_593,k9_setfam_1(A_592)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_5306,c_54,c_22,c_54,c_54,c_54,c_5863])).

tff(c_5958,plain,(
    ! [B_596] :
      ( k12_lattice3(k3_yellow_1('#skF_6'),B_596,'#skF_8') = k11_lattice3(k3_yellow_1('#skF_6'),B_596,'#skF_8')
      | ~ m1_subset_1(B_596,k9_setfam_1('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_108,c_5870])).

tff(c_5989,plain,(
    k12_lattice3(k3_yellow_1('#skF_6'),'#skF_7','#skF_8') = k11_lattice3(k3_yellow_1('#skF_6'),'#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_109,c_5958])).

tff(c_6006,plain,(
    k12_lattice3(k3_yellow_1('#skF_6'),'#skF_7','#skF_8') = k3_xboole_0('#skF_7','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5663,c_5989])).

tff(c_6008,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2855,c_6006])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:54:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.92/2.12  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.92/2.15  
% 5.92/2.15  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.92/2.16  %$ r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v2_lattice3 > v1_xboole_0 > v1_orders_2 > v1_lattice3 > l1_orders_2 > k13_lattice3 > k12_lattice3 > k11_lattice3 > k10_lattice3 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > u1_orders_2 > k9_setfam_1 > k3_yellow_1 > k2_yellow_1 > k1_yellow_1 > k1_setfam_1 > #skF_5 > #skF_2 > #skF_4 > #skF_1 > #skF_7 > #skF_6 > #skF_8 > #skF_3
% 5.92/2.16  
% 5.92/2.16  %Foreground sorts:
% 5.92/2.16  
% 5.92/2.16  
% 5.92/2.16  %Background operators:
% 5.92/2.16  
% 5.92/2.16  
% 5.92/2.16  %Foreground operators:
% 5.92/2.16  tff(v1_orders_2, type, v1_orders_2: $i > $o).
% 5.92/2.16  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 5.92/2.16  tff('#skF_5', type, '#skF_5': $i > $i).
% 5.92/2.16  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 5.92/2.16  tff('#skF_2', type, '#skF_2': $i > $i).
% 5.92/2.16  tff('#skF_4', type, '#skF_4': $i > $i).
% 5.92/2.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.92/2.16  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.92/2.16  tff(k13_lattice3, type, k13_lattice3: ($i * $i * $i) > $i).
% 5.92/2.16  tff(k3_yellow_1, type, k3_yellow_1: $i > $i).
% 5.92/2.16  tff('#skF_1', type, '#skF_1': $i > $i).
% 5.92/2.16  tff(k10_lattice3, type, k10_lattice3: ($i * $i * $i) > $i).
% 5.92/2.16  tff(k2_yellow_1, type, k2_yellow_1: $i > $i).
% 5.92/2.16  tff('#skF_7', type, '#skF_7': $i).
% 5.92/2.16  tff(k11_lattice3, type, k11_lattice3: ($i * $i * $i) > $i).
% 5.92/2.16  tff(k9_setfam_1, type, k9_setfam_1: $i > $i).
% 5.92/2.16  tff(v1_lattice3, type, v1_lattice3: $i > $o).
% 5.92/2.16  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.92/2.16  tff(k12_lattice3, type, k12_lattice3: ($i * $i * $i) > $i).
% 5.92/2.16  tff('#skF_6', type, '#skF_6': $i).
% 5.92/2.16  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 5.92/2.16  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 5.92/2.16  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 5.92/2.16  tff('#skF_8', type, '#skF_8': $i).
% 5.92/2.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.92/2.16  tff(k1_yellow_1, type, k1_yellow_1: $i > $i).
% 5.92/2.16  tff('#skF_3', type, '#skF_3': $i > $i).
% 5.92/2.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.92/2.16  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.92/2.16  tff(v2_lattice3, type, v2_lattice3: $i > $o).
% 5.92/2.16  tff(u1_orders_2, type, u1_orders_2: $i > $i).
% 5.92/2.16  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.92/2.16  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.92/2.16  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.92/2.16  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.92/2.16  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 5.92/2.16  
% 6.08/2.19  tff(f_160, negated_conjecture, ~(![A, B]: (m1_subset_1(B, u1_struct_0(k3_yellow_1(A))) => (![C]: (m1_subset_1(C, u1_struct_0(k3_yellow_1(A))) => ((k13_lattice3(k3_yellow_1(A), B, C) = k2_xboole_0(B, C)) & (k12_lattice3(k3_yellow_1(A), B, C) = k3_xboole_0(B, C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_yellow_1)).
% 6.08/2.19  tff(f_124, axiom, (![A]: (k3_yellow_1(A) = k2_yellow_1(k9_setfam_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_yellow_1)).
% 6.08/2.19  tff(f_122, axiom, (![A]: ((u1_struct_0(k2_yellow_1(A)) = A) & (u1_orders_2(k2_yellow_1(A)) = k1_yellow_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_yellow_1)).
% 6.08/2.19  tff(f_94, axiom, (![A, B]: (m1_subset_1(B, u1_struct_0(k3_yellow_1(A))) => (![C]: (m1_subset_1(C, u1_struct_0(k3_yellow_1(A))) => (r2_hidden(k3_xboole_0(B, C), k9_setfam_1(A)) & r2_hidden(k2_xboole_0(B, C), k9_setfam_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l19_yellow_1)).
% 6.08/2.19  tff(f_44, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 6.08/2.19  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 6.08/2.19  tff(f_137, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, u1_struct_0(k2_yellow_1(A))) => (![C]: (m1_subset_1(C, u1_struct_0(k2_yellow_1(A))) => (r2_hidden(k2_xboole_0(B, C), A) => (k10_lattice3(k2_yellow_1(A), B, C) = k2_xboole_0(B, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_yellow_1)).
% 6.08/2.19  tff(f_85, axiom, (![A]: ((((~v2_struct_0(k3_yellow_1(A)) & v1_orders_2(k3_yellow_1(A))) & v3_orders_2(k3_yellow_1(A))) & v4_orders_2(k3_yellow_1(A))) & v5_orders_2(k3_yellow_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc7_yellow_1)).
% 6.08/2.19  tff(f_106, axiom, (![A]: (~v1_xboole_0(A) => ((![B, C]: ((r2_hidden(B, A) & r2_hidden(C, A)) => r2_hidden(k2_xboole_0(B, C), A))) => v1_lattice3(k2_yellow_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_yellow_1)).
% 6.08/2.19  tff(f_74, axiom, (![A]: (v1_orders_2(k3_yellow_1(A)) & l1_orders_2(k3_yellow_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_yellow_1)).
% 6.08/2.19  tff(f_70, axiom, (![A, B, C]: (((((v5_orders_2(A) & v1_lattice3(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (k13_lattice3(A, B, C) = k10_lattice3(A, B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k13_lattice3)).
% 6.08/2.19  tff(f_150, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, u1_struct_0(k2_yellow_1(A))) => (![C]: (m1_subset_1(C, u1_struct_0(k2_yellow_1(A))) => (r2_hidden(k3_xboole_0(B, C), A) => (k11_lattice3(k2_yellow_1(A), B, C) = k3_xboole_0(B, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_yellow_1)).
% 6.08/2.19  tff(f_118, axiom, (![A]: (~v1_xboole_0(A) => ((![B, C]: ((r2_hidden(B, A) & r2_hidden(C, A)) => r2_hidden(k3_xboole_0(B, C), A))) => v2_lattice3(k2_yellow_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_yellow_1)).
% 6.08/2.19  tff(f_58, axiom, (![A, B, C]: (((((v5_orders_2(A) & v2_lattice3(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (k12_lattice3(A, B, C) = k11_lattice3(A, B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k12_lattice3)).
% 6.08/2.19  tff(c_60, plain, (k12_lattice3(k3_yellow_1('#skF_6'), '#skF_7', '#skF_8')!=k3_xboole_0('#skF_7', '#skF_8') | k13_lattice3(k3_yellow_1('#skF_6'), '#skF_7', '#skF_8')!=k2_xboole_0('#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_160])).
% 6.08/2.19  tff(c_143, plain, (k13_lattice3(k3_yellow_1('#skF_6'), '#skF_7', '#skF_8')!=k2_xboole_0('#skF_7', '#skF_8')), inference(splitLeft, [status(thm)], [c_60])).
% 6.08/2.19  tff(c_83, plain, (![A_51]: (k2_yellow_1(k9_setfam_1(A_51))=k3_yellow_1(A_51))), inference(cnfTransformation, [status(thm)], [f_124])).
% 6.08/2.19  tff(c_50, plain, (![A_27]: (u1_struct_0(k2_yellow_1(A_27))=A_27)), inference(cnfTransformation, [status(thm)], [f_122])).
% 6.08/2.19  tff(c_89, plain, (![A_51]: (u1_struct_0(k3_yellow_1(A_51))=k9_setfam_1(A_51))), inference(superposition, [status(thm), theory('equality')], [c_83, c_50])).
% 6.08/2.19  tff(c_64, plain, (m1_subset_1('#skF_7', u1_struct_0(k3_yellow_1('#skF_6')))), inference(cnfTransformation, [status(thm)], [f_160])).
% 6.08/2.19  tff(c_109, plain, (m1_subset_1('#skF_7', k9_setfam_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_89, c_64])).
% 6.08/2.19  tff(c_62, plain, (m1_subset_1('#skF_8', u1_struct_0(k3_yellow_1('#skF_6')))), inference(cnfTransformation, [status(thm)], [f_160])).
% 6.08/2.19  tff(c_108, plain, (m1_subset_1('#skF_8', k9_setfam_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_89, c_62])).
% 6.08/2.19  tff(c_54, plain, (![A_28]: (k2_yellow_1(k9_setfam_1(A_28))=k3_yellow_1(A_28))), inference(cnfTransformation, [status(thm)], [f_124])).
% 6.08/2.19  tff(c_34, plain, (![B_18, C_20, A_17]: (r2_hidden(k2_xboole_0(B_18, C_20), k9_setfam_1(A_17)) | ~m1_subset_1(C_20, u1_struct_0(k3_yellow_1(A_17))) | ~m1_subset_1(B_18, u1_struct_0(k3_yellow_1(A_17))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 6.08/2.19  tff(c_2135, plain, (![B_18, C_20, A_17]: (r2_hidden(k2_xboole_0(B_18, C_20), k9_setfam_1(A_17)) | ~m1_subset_1(C_20, k9_setfam_1(A_17)) | ~m1_subset_1(B_18, k9_setfam_1(A_17)))), inference(demodulation, [status(thm), theory('equality')], [c_89, c_89, c_34])).
% 6.08/2.19  tff(c_1242, plain, (![B_18, C_20, A_17]: (r2_hidden(k2_xboole_0(B_18, C_20), k9_setfam_1(A_17)) | ~m1_subset_1(C_20, k9_setfam_1(A_17)) | ~m1_subset_1(B_18, k9_setfam_1(A_17)))), inference(demodulation, [status(thm), theory('equality')], [c_89, c_89, c_34])).
% 6.08/2.19  tff(c_10, plain, (![B_6, A_5]: (m1_subset_1(B_6, A_5) | ~v1_xboole_0(B_6) | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_44])).
% 6.08/2.19  tff(c_36, plain, (![B_18, C_20, A_17]: (r2_hidden(k3_xboole_0(B_18, C_20), k9_setfam_1(A_17)) | ~m1_subset_1(C_20, u1_struct_0(k3_yellow_1(A_17))) | ~m1_subset_1(B_18, u1_struct_0(k3_yellow_1(A_17))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 6.08/2.19  tff(c_252, plain, (![B_80, C_81, A_82]: (r2_hidden(k3_xboole_0(B_80, C_81), k9_setfam_1(A_82)) | ~m1_subset_1(C_81, k9_setfam_1(A_82)) | ~m1_subset_1(B_80, k9_setfam_1(A_82)))), inference(demodulation, [status(thm), theory('equality')], [c_89, c_89, c_36])).
% 6.08/2.19  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.08/2.19  tff(c_267, plain, (![A_83, C_84, B_85]: (~v1_xboole_0(k9_setfam_1(A_83)) | ~m1_subset_1(C_84, k9_setfam_1(A_83)) | ~m1_subset_1(B_85, k9_setfam_1(A_83)))), inference(resolution, [status(thm)], [c_252, c_2])).
% 6.08/2.19  tff(c_299, plain, (![B_85, A_83, B_6]: (~m1_subset_1(B_85, k9_setfam_1(A_83)) | ~v1_xboole_0(B_6) | ~v1_xboole_0(k9_setfam_1(A_83)))), inference(resolution, [status(thm)], [c_10, c_267])).
% 6.08/2.19  tff(c_303, plain, (![B_86, A_87]: (~m1_subset_1(B_86, k9_setfam_1(A_87)) | ~v1_xboole_0(k9_setfam_1(A_87)))), inference(splitLeft, [status(thm)], [c_299])).
% 6.08/2.19  tff(c_343, plain, (![B_6, A_87]: (~v1_xboole_0(B_6) | ~v1_xboole_0(k9_setfam_1(A_87)))), inference(resolution, [status(thm)], [c_10, c_303])).
% 6.08/2.19  tff(c_346, plain, (![A_87]: (~v1_xboole_0(k9_setfam_1(A_87)))), inference(splitLeft, [status(thm)], [c_343])).
% 6.08/2.19  tff(c_348, plain, (![B_18, C_20, A_17]: (r2_hidden(k2_xboole_0(B_18, C_20), k9_setfam_1(A_17)) | ~m1_subset_1(C_20, k9_setfam_1(A_17)) | ~m1_subset_1(B_18, k9_setfam_1(A_17)))), inference(demodulation, [status(thm), theory('equality')], [c_89, c_89, c_34])).
% 6.08/2.19  tff(c_56, plain, (![A_29, B_33, C_35]: (k10_lattice3(k2_yellow_1(A_29), B_33, C_35)=k2_xboole_0(B_33, C_35) | ~r2_hidden(k2_xboole_0(B_33, C_35), A_29) | ~m1_subset_1(C_35, u1_struct_0(k2_yellow_1(A_29))) | ~m1_subset_1(B_33, u1_struct_0(k2_yellow_1(A_29))) | v1_xboole_0(A_29))), inference(cnfTransformation, [status(thm)], [f_137])).
% 6.08/2.19  tff(c_455, plain, (![A_103, B_104, C_105]: (k10_lattice3(k2_yellow_1(A_103), B_104, C_105)=k2_xboole_0(B_104, C_105) | ~r2_hidden(k2_xboole_0(B_104, C_105), A_103) | ~m1_subset_1(C_105, A_103) | ~m1_subset_1(B_104, A_103) | v1_xboole_0(A_103))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_50, c_56])).
% 6.08/2.19  tff(c_458, plain, (![A_17, B_18, C_20]: (k10_lattice3(k2_yellow_1(k9_setfam_1(A_17)), B_18, C_20)=k2_xboole_0(B_18, C_20) | v1_xboole_0(k9_setfam_1(A_17)) | ~m1_subset_1(C_20, k9_setfam_1(A_17)) | ~m1_subset_1(B_18, k9_setfam_1(A_17)))), inference(resolution, [status(thm)], [c_348, c_455])).
% 6.08/2.19  tff(c_464, plain, (![A_17, B_18, C_20]: (k10_lattice3(k3_yellow_1(A_17), B_18, C_20)=k2_xboole_0(B_18, C_20) | v1_xboole_0(k9_setfam_1(A_17)) | ~m1_subset_1(C_20, k9_setfam_1(A_17)) | ~m1_subset_1(B_18, k9_setfam_1(A_17)))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_458])).
% 6.08/2.19  tff(c_467, plain, (![A_106, B_107, C_108]: (k10_lattice3(k3_yellow_1(A_106), B_107, C_108)=k2_xboole_0(B_107, C_108) | ~m1_subset_1(C_108, k9_setfam_1(A_106)) | ~m1_subset_1(B_107, k9_setfam_1(A_106)))), inference(negUnitSimplification, [status(thm)], [c_346, c_464])).
% 6.08/2.19  tff(c_573, plain, (![B_110]: (k10_lattice3(k3_yellow_1('#skF_6'), B_110, '#skF_8')=k2_xboole_0(B_110, '#skF_8') | ~m1_subset_1(B_110, k9_setfam_1('#skF_6')))), inference(resolution, [status(thm)], [c_108, c_467])).
% 6.08/2.19  tff(c_625, plain, (k10_lattice3(k3_yellow_1('#skF_6'), '#skF_7', '#skF_8')=k2_xboole_0('#skF_7', '#skF_8')), inference(resolution, [status(thm)], [c_109, c_573])).
% 6.08/2.19  tff(c_32, plain, (![A_16]: (v5_orders_2(k3_yellow_1(A_16)))), inference(cnfTransformation, [status(thm)], [f_85])).
% 6.08/2.19  tff(c_204, plain, (![A_72]: (r2_hidden('#skF_3'(A_72), A_72) | v1_lattice3(k2_yellow_1(A_72)) | v1_xboole_0(A_72))), inference(cnfTransformation, [status(thm)], [f_106])).
% 6.08/2.19  tff(c_6, plain, (![B_6, A_5]: (m1_subset_1(B_6, A_5) | ~r2_hidden(B_6, A_5) | v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_44])).
% 6.08/2.19  tff(c_211, plain, (![A_72]: (m1_subset_1('#skF_3'(A_72), A_72) | v1_lattice3(k2_yellow_1(A_72)) | v1_xboole_0(A_72))), inference(resolution, [status(thm)], [c_204, c_6])).
% 6.08/2.19  tff(c_177, plain, (![A_69]: (r2_hidden('#skF_2'(A_69), A_69) | v1_lattice3(k2_yellow_1(A_69)) | v1_xboole_0(A_69))), inference(cnfTransformation, [status(thm)], [f_106])).
% 6.08/2.20  tff(c_184, plain, (![A_69]: (m1_subset_1('#skF_2'(A_69), A_69) | v1_lattice3(k2_yellow_1(A_69)) | v1_xboole_0(A_69))), inference(resolution, [status(thm)], [c_177, c_6])).
% 6.08/2.20  tff(c_349, plain, (![B_89, C_90, A_91]: (r2_hidden(k2_xboole_0(B_89, C_90), k9_setfam_1(A_91)) | ~m1_subset_1(C_90, k9_setfam_1(A_91)) | ~m1_subset_1(B_89, k9_setfam_1(A_91)))), inference(demodulation, [status(thm), theory('equality')], [c_89, c_89, c_34])).
% 6.08/2.20  tff(c_38, plain, (![A_21]: (~r2_hidden(k2_xboole_0('#skF_2'(A_21), '#skF_3'(A_21)), A_21) | v1_lattice3(k2_yellow_1(A_21)) | v1_xboole_0(A_21))), inference(cnfTransformation, [status(thm)], [f_106])).
% 6.08/2.20  tff(c_353, plain, (![A_91]: (v1_lattice3(k2_yellow_1(k9_setfam_1(A_91))) | v1_xboole_0(k9_setfam_1(A_91)) | ~m1_subset_1('#skF_3'(k9_setfam_1(A_91)), k9_setfam_1(A_91)) | ~m1_subset_1('#skF_2'(k9_setfam_1(A_91)), k9_setfam_1(A_91)))), inference(resolution, [status(thm)], [c_349, c_38])).
% 6.08/2.20  tff(c_361, plain, (![A_91]: (v1_lattice3(k3_yellow_1(A_91)) | v1_xboole_0(k9_setfam_1(A_91)) | ~m1_subset_1('#skF_3'(k9_setfam_1(A_91)), k9_setfam_1(A_91)) | ~m1_subset_1('#skF_2'(k9_setfam_1(A_91)), k9_setfam_1(A_91)))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_353])).
% 6.08/2.20  tff(c_385, plain, (![A_96]: (v1_lattice3(k3_yellow_1(A_96)) | ~m1_subset_1('#skF_3'(k9_setfam_1(A_96)), k9_setfam_1(A_96)) | ~m1_subset_1('#skF_2'(k9_setfam_1(A_96)), k9_setfam_1(A_96)))), inference(negUnitSimplification, [status(thm)], [c_346, c_361])).
% 6.08/2.20  tff(c_388, plain, (![A_96]: (v1_lattice3(k3_yellow_1(A_96)) | ~m1_subset_1('#skF_3'(k9_setfam_1(A_96)), k9_setfam_1(A_96)) | v1_lattice3(k2_yellow_1(k9_setfam_1(A_96))) | v1_xboole_0(k9_setfam_1(A_96)))), inference(resolution, [status(thm)], [c_184, c_385])).
% 6.08/2.20  tff(c_393, plain, (![A_96]: (v1_lattice3(k3_yellow_1(A_96)) | ~m1_subset_1('#skF_3'(k9_setfam_1(A_96)), k9_setfam_1(A_96)) | v1_lattice3(k3_yellow_1(A_96)) | v1_xboole_0(k9_setfam_1(A_96)))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_388])).
% 6.08/2.20  tff(c_428, plain, (![A_100]: (v1_lattice3(k3_yellow_1(A_100)) | ~m1_subset_1('#skF_3'(k9_setfam_1(A_100)), k9_setfam_1(A_100)) | v1_lattice3(k3_yellow_1(A_100)))), inference(negUnitSimplification, [status(thm)], [c_346, c_393])).
% 6.08/2.20  tff(c_431, plain, (![A_100]: (v1_lattice3(k3_yellow_1(A_100)) | v1_lattice3(k2_yellow_1(k9_setfam_1(A_100))) | v1_xboole_0(k9_setfam_1(A_100)))), inference(resolution, [status(thm)], [c_211, c_428])).
% 6.08/2.20  tff(c_436, plain, (![A_100]: (v1_lattice3(k3_yellow_1(A_100)) | v1_lattice3(k3_yellow_1(A_100)) | v1_xboole_0(k9_setfam_1(A_100)))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_431])).
% 6.08/2.20  tff(c_437, plain, (![A_100]: (v1_lattice3(k3_yellow_1(A_100)) | v1_lattice3(k3_yellow_1(A_100)))), inference(negUnitSimplification, [status(thm)], [c_346, c_436])).
% 6.08/2.20  tff(c_447, plain, (![A_100]: (v1_lattice3(k3_yellow_1(A_100)))), inference(factorization, [status(thm), theory('equality')], [c_437])).
% 6.08/2.20  tff(c_22, plain, (![A_15]: (l1_orders_2(k3_yellow_1(A_15)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 6.08/2.20  tff(c_770, plain, (![A_120, B_121, C_122]: (k13_lattice3(A_120, B_121, C_122)=k10_lattice3(A_120, B_121, C_122) | ~m1_subset_1(C_122, u1_struct_0(A_120)) | ~m1_subset_1(B_121, u1_struct_0(A_120)) | ~l1_orders_2(A_120) | ~v1_lattice3(A_120) | ~v5_orders_2(A_120))), inference(cnfTransformation, [status(thm)], [f_70])).
% 6.08/2.20  tff(c_790, plain, (![A_51, B_121, C_122]: (k13_lattice3(k3_yellow_1(A_51), B_121, C_122)=k10_lattice3(k3_yellow_1(A_51), B_121, C_122) | ~m1_subset_1(C_122, k9_setfam_1(A_51)) | ~m1_subset_1(B_121, u1_struct_0(k3_yellow_1(A_51))) | ~l1_orders_2(k3_yellow_1(A_51)) | ~v1_lattice3(k3_yellow_1(A_51)) | ~v5_orders_2(k3_yellow_1(A_51)))), inference(superposition, [status(thm), theory('equality')], [c_89, c_770])).
% 6.08/2.20  tff(c_994, plain, (![A_140, B_141, C_142]: (k13_lattice3(k3_yellow_1(A_140), B_141, C_142)=k10_lattice3(k3_yellow_1(A_140), B_141, C_142) | ~m1_subset_1(C_142, k9_setfam_1(A_140)) | ~m1_subset_1(B_141, k9_setfam_1(A_140)))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_447, c_22, c_89, c_790])).
% 6.08/2.20  tff(c_1126, plain, (![B_147]: (k13_lattice3(k3_yellow_1('#skF_6'), B_147, '#skF_8')=k10_lattice3(k3_yellow_1('#skF_6'), B_147, '#skF_8') | ~m1_subset_1(B_147, k9_setfam_1('#skF_6')))), inference(resolution, [status(thm)], [c_108, c_994])).
% 6.08/2.20  tff(c_1161, plain, (k13_lattice3(k3_yellow_1('#skF_6'), '#skF_7', '#skF_8')=k10_lattice3(k3_yellow_1('#skF_6'), '#skF_7', '#skF_8')), inference(resolution, [status(thm)], [c_109, c_1126])).
% 6.08/2.20  tff(c_1184, plain, (k13_lattice3(k3_yellow_1('#skF_6'), '#skF_7', '#skF_8')=k2_xboole_0('#skF_7', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_625, c_1161])).
% 6.08/2.20  tff(c_1186, plain, $false, inference(negUnitSimplification, [status(thm)], [c_143, c_1184])).
% 6.08/2.20  tff(c_1187, plain, (![B_6]: (~v1_xboole_0(B_6))), inference(splitRight, [status(thm)], [c_343])).
% 6.08/2.20  tff(c_66, plain, (![A_29, B_33, C_35]: (k10_lattice3(k2_yellow_1(A_29), B_33, C_35)=k2_xboole_0(B_33, C_35) | ~r2_hidden(k2_xboole_0(B_33, C_35), A_29) | ~m1_subset_1(C_35, A_29) | ~m1_subset_1(B_33, A_29) | v1_xboole_0(A_29))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_50, c_56])).
% 6.08/2.20  tff(c_1395, plain, (![A_190, B_191, C_192]: (k10_lattice3(k2_yellow_1(A_190), B_191, C_192)=k2_xboole_0(B_191, C_192) | ~r2_hidden(k2_xboole_0(B_191, C_192), A_190) | ~m1_subset_1(C_192, A_190) | ~m1_subset_1(B_191, A_190))), inference(negUnitSimplification, [status(thm)], [c_1187, c_66])).
% 6.08/2.20  tff(c_1398, plain, (![A_17, B_18, C_20]: (k10_lattice3(k2_yellow_1(k9_setfam_1(A_17)), B_18, C_20)=k2_xboole_0(B_18, C_20) | ~m1_subset_1(C_20, k9_setfam_1(A_17)) | ~m1_subset_1(B_18, k9_setfam_1(A_17)))), inference(resolution, [status(thm)], [c_1242, c_1395])).
% 6.08/2.20  tff(c_1430, plain, (![A_196, B_197, C_198]: (k10_lattice3(k3_yellow_1(A_196), B_197, C_198)=k2_xboole_0(B_197, C_198) | ~m1_subset_1(C_198, k9_setfam_1(A_196)) | ~m1_subset_1(B_197, k9_setfam_1(A_196)))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_1398])).
% 6.08/2.20  tff(c_1529, plain, (![B_203]: (k10_lattice3(k3_yellow_1('#skF_6'), B_203, '#skF_8')=k2_xboole_0(B_203, '#skF_8') | ~m1_subset_1(B_203, k9_setfam_1('#skF_6')))), inference(resolution, [status(thm)], [c_108, c_1430])).
% 6.08/2.20  tff(c_1575, plain, (k10_lattice3(k3_yellow_1('#skF_6'), '#skF_7', '#skF_8')=k2_xboole_0('#skF_7', '#skF_8')), inference(resolution, [status(thm)], [c_109, c_1529])).
% 6.08/2.20  tff(c_40, plain, (![A_21]: (r2_hidden('#skF_3'(A_21), A_21) | v1_lattice3(k2_yellow_1(A_21)) | v1_xboole_0(A_21))), inference(cnfTransformation, [status(thm)], [f_106])).
% 6.08/2.20  tff(c_1227, plain, (![A_156]: (r2_hidden('#skF_3'(A_156), A_156) | v1_lattice3(k2_yellow_1(A_156)))), inference(negUnitSimplification, [status(thm)], [c_1187, c_40])).
% 6.08/2.20  tff(c_1200, plain, (![B_6, A_5]: (m1_subset_1(B_6, A_5) | ~r2_hidden(B_6, A_5))), inference(negUnitSimplification, [status(thm)], [c_1187, c_6])).
% 6.08/2.20  tff(c_1231, plain, (![A_156]: (m1_subset_1('#skF_3'(A_156), A_156) | v1_lattice3(k2_yellow_1(A_156)))), inference(resolution, [status(thm)], [c_1227, c_1200])).
% 6.08/2.20  tff(c_1194, plain, (![A_69]: (m1_subset_1('#skF_2'(A_69), A_69) | v1_lattice3(k2_yellow_1(A_69)))), inference(negUnitSimplification, [status(thm)], [c_1187, c_184])).
% 6.08/2.20  tff(c_1292, plain, (![A_170]: (~r2_hidden(k2_xboole_0('#skF_2'(A_170), '#skF_3'(A_170)), A_170) | v1_lattice3(k2_yellow_1(A_170)))), inference(negUnitSimplification, [status(thm)], [c_1187, c_38])).
% 6.08/2.20  tff(c_1296, plain, (![A_17]: (v1_lattice3(k2_yellow_1(k9_setfam_1(A_17))) | ~m1_subset_1('#skF_3'(k9_setfam_1(A_17)), k9_setfam_1(A_17)) | ~m1_subset_1('#skF_2'(k9_setfam_1(A_17)), k9_setfam_1(A_17)))), inference(resolution, [status(thm)], [c_1242, c_1292])).
% 6.08/2.20  tff(c_1388, plain, (![A_189]: (v1_lattice3(k3_yellow_1(A_189)) | ~m1_subset_1('#skF_3'(k9_setfam_1(A_189)), k9_setfam_1(A_189)) | ~m1_subset_1('#skF_2'(k9_setfam_1(A_189)), k9_setfam_1(A_189)))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_1296])).
% 6.08/2.20  tff(c_1391, plain, (![A_189]: (v1_lattice3(k3_yellow_1(A_189)) | ~m1_subset_1('#skF_3'(k9_setfam_1(A_189)), k9_setfam_1(A_189)) | v1_lattice3(k2_yellow_1(k9_setfam_1(A_189))))), inference(resolution, [status(thm)], [c_1194, c_1388])).
% 6.08/2.20  tff(c_1406, plain, (![A_193]: (v1_lattice3(k3_yellow_1(A_193)) | ~m1_subset_1('#skF_3'(k9_setfam_1(A_193)), k9_setfam_1(A_193)) | v1_lattice3(k3_yellow_1(A_193)))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_1391])).
% 6.08/2.20  tff(c_1409, plain, (![A_193]: (v1_lattice3(k3_yellow_1(A_193)) | v1_lattice3(k2_yellow_1(k9_setfam_1(A_193))))), inference(resolution, [status(thm)], [c_1231, c_1406])).
% 6.08/2.20  tff(c_1411, plain, (![A_193]: (v1_lattice3(k3_yellow_1(A_193)) | v1_lattice3(k3_yellow_1(A_193)))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_1409])).
% 6.08/2.20  tff(c_1420, plain, (![A_193]: (v1_lattice3(k3_yellow_1(A_193)))), inference(factorization, [status(thm), theory('equality')], [c_1411])).
% 6.08/2.20  tff(c_1339, plain, (![A_183, B_184, C_185]: (k13_lattice3(A_183, B_184, C_185)=k10_lattice3(A_183, B_184, C_185) | ~m1_subset_1(C_185, u1_struct_0(A_183)) | ~m1_subset_1(B_184, u1_struct_0(A_183)) | ~l1_orders_2(A_183) | ~v1_lattice3(A_183) | ~v5_orders_2(A_183))), inference(cnfTransformation, [status(thm)], [f_70])).
% 6.08/2.20  tff(c_1358, plain, (![A_27, B_184, C_185]: (k13_lattice3(k2_yellow_1(A_27), B_184, C_185)=k10_lattice3(k2_yellow_1(A_27), B_184, C_185) | ~m1_subset_1(C_185, A_27) | ~m1_subset_1(B_184, u1_struct_0(k2_yellow_1(A_27))) | ~l1_orders_2(k2_yellow_1(A_27)) | ~v1_lattice3(k2_yellow_1(A_27)) | ~v5_orders_2(k2_yellow_1(A_27)))), inference(superposition, [status(thm), theory('equality')], [c_50, c_1339])).
% 6.08/2.20  tff(c_1936, plain, (![A_224, B_225, C_226]: (k13_lattice3(k2_yellow_1(A_224), B_225, C_226)=k10_lattice3(k2_yellow_1(A_224), B_225, C_226) | ~m1_subset_1(C_226, A_224) | ~m1_subset_1(B_225, A_224) | ~l1_orders_2(k2_yellow_1(A_224)) | ~v1_lattice3(k2_yellow_1(A_224)) | ~v5_orders_2(k2_yellow_1(A_224)))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_1358])).
% 6.08/2.20  tff(c_1938, plain, (![A_28, B_225, C_226]: (k13_lattice3(k2_yellow_1(k9_setfam_1(A_28)), B_225, C_226)=k10_lattice3(k2_yellow_1(k9_setfam_1(A_28)), B_225, C_226) | ~m1_subset_1(C_226, k9_setfam_1(A_28)) | ~m1_subset_1(B_225, k9_setfam_1(A_28)) | ~l1_orders_2(k2_yellow_1(k9_setfam_1(A_28))) | ~v1_lattice3(k2_yellow_1(k9_setfam_1(A_28))) | ~v5_orders_2(k3_yellow_1(A_28)))), inference(superposition, [status(thm), theory('equality')], [c_54, c_1936])).
% 6.08/2.20  tff(c_1949, plain, (![A_227, B_228, C_229]: (k13_lattice3(k3_yellow_1(A_227), B_228, C_229)=k10_lattice3(k3_yellow_1(A_227), B_228, C_229) | ~m1_subset_1(C_229, k9_setfam_1(A_227)) | ~m1_subset_1(B_228, k9_setfam_1(A_227)))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_1420, c_54, c_22, c_54, c_54, c_54, c_1938])).
% 6.08/2.20  tff(c_2049, plain, (![B_231]: (k13_lattice3(k3_yellow_1('#skF_6'), B_231, '#skF_8')=k10_lattice3(k3_yellow_1('#skF_6'), B_231, '#skF_8') | ~m1_subset_1(B_231, k9_setfam_1('#skF_6')))), inference(resolution, [status(thm)], [c_108, c_1949])).
% 6.08/2.20  tff(c_2080, plain, (k13_lattice3(k3_yellow_1('#skF_6'), '#skF_7', '#skF_8')=k10_lattice3(k3_yellow_1('#skF_6'), '#skF_7', '#skF_8')), inference(resolution, [status(thm)], [c_109, c_2049])).
% 6.08/2.20  tff(c_2097, plain, (k13_lattice3(k3_yellow_1('#skF_6'), '#skF_7', '#skF_8')=k2_xboole_0('#skF_7', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_1575, c_2080])).
% 6.08/2.20  tff(c_2099, plain, $false, inference(negUnitSimplification, [status(thm)], [c_143, c_2097])).
% 6.08/2.20  tff(c_2100, plain, (![B_6]: (~v1_xboole_0(B_6))), inference(splitRight, [status(thm)], [c_299])).
% 6.08/2.20  tff(c_2287, plain, (![A_271, B_272, C_273]: (k10_lattice3(k2_yellow_1(A_271), B_272, C_273)=k2_xboole_0(B_272, C_273) | ~r2_hidden(k2_xboole_0(B_272, C_273), A_271) | ~m1_subset_1(C_273, A_271) | ~m1_subset_1(B_272, A_271))), inference(negUnitSimplification, [status(thm)], [c_2100, c_66])).
% 6.08/2.20  tff(c_2290, plain, (![A_17, B_18, C_20]: (k10_lattice3(k2_yellow_1(k9_setfam_1(A_17)), B_18, C_20)=k2_xboole_0(B_18, C_20) | ~m1_subset_1(C_20, k9_setfam_1(A_17)) | ~m1_subset_1(B_18, k9_setfam_1(A_17)))), inference(resolution, [status(thm)], [c_2135, c_2287])).
% 6.08/2.20  tff(c_2512, plain, (![A_291, B_292, C_293]: (k10_lattice3(k3_yellow_1(A_291), B_292, C_293)=k2_xboole_0(B_292, C_293) | ~m1_subset_1(C_293, k9_setfam_1(A_291)) | ~m1_subset_1(B_292, k9_setfam_1(A_291)))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_2290])).
% 6.08/2.20  tff(c_2605, plain, (![B_295]: (k10_lattice3(k3_yellow_1('#skF_6'), B_295, '#skF_8')=k2_xboole_0(B_295, '#skF_8') | ~m1_subset_1(B_295, k9_setfam_1('#skF_6')))), inference(resolution, [status(thm)], [c_108, c_2512])).
% 6.08/2.20  tff(c_2651, plain, (k10_lattice3(k3_yellow_1('#skF_6'), '#skF_7', '#skF_8')=k2_xboole_0('#skF_7', '#skF_8')), inference(resolution, [status(thm)], [c_109, c_2605])).
% 6.08/2.20  tff(c_2146, plain, (![A_243]: (r2_hidden('#skF_3'(A_243), A_243) | v1_lattice3(k2_yellow_1(A_243)))), inference(negUnitSimplification, [status(thm)], [c_2100, c_40])).
% 6.08/2.20  tff(c_2113, plain, (![B_6, A_5]: (m1_subset_1(B_6, A_5) | ~r2_hidden(B_6, A_5))), inference(negUnitSimplification, [status(thm)], [c_2100, c_6])).
% 6.08/2.20  tff(c_2150, plain, (![A_243]: (m1_subset_1('#skF_3'(A_243), A_243) | v1_lattice3(k2_yellow_1(A_243)))), inference(resolution, [status(thm)], [c_2146, c_2113])).
% 6.08/2.20  tff(c_42, plain, (![A_21]: (r2_hidden('#skF_2'(A_21), A_21) | v1_lattice3(k2_yellow_1(A_21)) | v1_xboole_0(A_21))), inference(cnfTransformation, [status(thm)], [f_106])).
% 6.08/2.20  tff(c_2141, plain, (![A_242]: (r2_hidden('#skF_2'(A_242), A_242) | v1_lattice3(k2_yellow_1(A_242)))), inference(negUnitSimplification, [status(thm)], [c_2100, c_42])).
% 6.08/2.20  tff(c_2145, plain, (![A_242]: (m1_subset_1('#skF_2'(A_242), A_242) | v1_lattice3(k2_yellow_1(A_242)))), inference(resolution, [status(thm)], [c_2141, c_2113])).
% 6.08/2.20  tff(c_2205, plain, (![A_254]: (~r2_hidden(k2_xboole_0('#skF_2'(A_254), '#skF_3'(A_254)), A_254) | v1_lattice3(k2_yellow_1(A_254)))), inference(negUnitSimplification, [status(thm)], [c_2100, c_38])).
% 6.08/2.20  tff(c_2209, plain, (![A_17]: (v1_lattice3(k2_yellow_1(k9_setfam_1(A_17))) | ~m1_subset_1('#skF_3'(k9_setfam_1(A_17)), k9_setfam_1(A_17)) | ~m1_subset_1('#skF_2'(k9_setfam_1(A_17)), k9_setfam_1(A_17)))), inference(resolution, [status(thm)], [c_2135, c_2205])).
% 6.08/2.20  tff(c_2274, plain, (![A_269]: (v1_lattice3(k3_yellow_1(A_269)) | ~m1_subset_1('#skF_3'(k9_setfam_1(A_269)), k9_setfam_1(A_269)) | ~m1_subset_1('#skF_2'(k9_setfam_1(A_269)), k9_setfam_1(A_269)))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_2209])).
% 6.08/2.20  tff(c_2277, plain, (![A_269]: (v1_lattice3(k3_yellow_1(A_269)) | ~m1_subset_1('#skF_3'(k9_setfam_1(A_269)), k9_setfam_1(A_269)) | v1_lattice3(k2_yellow_1(k9_setfam_1(A_269))))), inference(resolution, [status(thm)], [c_2145, c_2274])).
% 6.08/2.20  tff(c_2280, plain, (![A_270]: (v1_lattice3(k3_yellow_1(A_270)) | ~m1_subset_1('#skF_3'(k9_setfam_1(A_270)), k9_setfam_1(A_270)) | v1_lattice3(k3_yellow_1(A_270)))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_2277])).
% 6.08/2.20  tff(c_2283, plain, (![A_270]: (v1_lattice3(k3_yellow_1(A_270)) | v1_lattice3(k2_yellow_1(k9_setfam_1(A_270))))), inference(resolution, [status(thm)], [c_2150, c_2280])).
% 6.08/2.20  tff(c_2285, plain, (![A_270]: (v1_lattice3(k3_yellow_1(A_270)) | v1_lattice3(k3_yellow_1(A_270)))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_2283])).
% 6.08/2.20  tff(c_2306, plain, (![A_270]: (v1_lattice3(k3_yellow_1(A_270)))), inference(factorization, [status(thm), theory('equality')], [c_2285])).
% 6.08/2.20  tff(c_2231, plain, (![A_260, B_261, C_262]: (k13_lattice3(A_260, B_261, C_262)=k10_lattice3(A_260, B_261, C_262) | ~m1_subset_1(C_262, u1_struct_0(A_260)) | ~m1_subset_1(B_261, u1_struct_0(A_260)) | ~l1_orders_2(A_260) | ~v1_lattice3(A_260) | ~v5_orders_2(A_260))), inference(cnfTransformation, [status(thm)], [f_70])).
% 6.08/2.20  tff(c_2250, plain, (![A_27, B_261, C_262]: (k13_lattice3(k2_yellow_1(A_27), B_261, C_262)=k10_lattice3(k2_yellow_1(A_27), B_261, C_262) | ~m1_subset_1(C_262, A_27) | ~m1_subset_1(B_261, u1_struct_0(k2_yellow_1(A_27))) | ~l1_orders_2(k2_yellow_1(A_27)) | ~v1_lattice3(k2_yellow_1(A_27)) | ~v5_orders_2(k2_yellow_1(A_27)))), inference(superposition, [status(thm), theory('equality')], [c_50, c_2231])).
% 6.08/2.20  tff(c_2661, plain, (![A_296, B_297, C_298]: (k13_lattice3(k2_yellow_1(A_296), B_297, C_298)=k10_lattice3(k2_yellow_1(A_296), B_297, C_298) | ~m1_subset_1(C_298, A_296) | ~m1_subset_1(B_297, A_296) | ~l1_orders_2(k2_yellow_1(A_296)) | ~v1_lattice3(k2_yellow_1(A_296)) | ~v5_orders_2(k2_yellow_1(A_296)))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_2250])).
% 6.08/2.20  tff(c_2663, plain, (![A_28, B_297, C_298]: (k13_lattice3(k2_yellow_1(k9_setfam_1(A_28)), B_297, C_298)=k10_lattice3(k2_yellow_1(k9_setfam_1(A_28)), B_297, C_298) | ~m1_subset_1(C_298, k9_setfam_1(A_28)) | ~m1_subset_1(B_297, k9_setfam_1(A_28)) | ~l1_orders_2(k2_yellow_1(k9_setfam_1(A_28))) | ~v1_lattice3(k2_yellow_1(k9_setfam_1(A_28))) | ~v5_orders_2(k3_yellow_1(A_28)))), inference(superposition, [status(thm), theory('equality')], [c_54, c_2661])).
% 6.08/2.20  tff(c_2703, plain, (![A_305, B_306, C_307]: (k13_lattice3(k3_yellow_1(A_305), B_306, C_307)=k10_lattice3(k3_yellow_1(A_305), B_306, C_307) | ~m1_subset_1(C_307, k9_setfam_1(A_305)) | ~m1_subset_1(B_306, k9_setfam_1(A_305)))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_2306, c_54, c_22, c_54, c_54, c_54, c_2663])).
% 6.08/2.20  tff(c_2804, plain, (![B_312]: (k13_lattice3(k3_yellow_1('#skF_6'), B_312, '#skF_8')=k10_lattice3(k3_yellow_1('#skF_6'), B_312, '#skF_8') | ~m1_subset_1(B_312, k9_setfam_1('#skF_6')))), inference(resolution, [status(thm)], [c_108, c_2703])).
% 6.08/2.20  tff(c_2835, plain, (k13_lattice3(k3_yellow_1('#skF_6'), '#skF_7', '#skF_8')=k10_lattice3(k3_yellow_1('#skF_6'), '#skF_7', '#skF_8')), inference(resolution, [status(thm)], [c_109, c_2804])).
% 6.08/2.20  tff(c_2852, plain, (k13_lattice3(k3_yellow_1('#skF_6'), '#skF_7', '#skF_8')=k2_xboole_0('#skF_7', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_2651, c_2835])).
% 6.08/2.20  tff(c_2854, plain, $false, inference(negUnitSimplification, [status(thm)], [c_143, c_2852])).
% 6.08/2.20  tff(c_2855, plain, (k12_lattice3(k3_yellow_1('#skF_6'), '#skF_7', '#skF_8')!=k3_xboole_0('#skF_7', '#skF_8')), inference(splitRight, [status(thm)], [c_60])).
% 6.08/2.20  tff(c_2962, plain, (![B_18, C_20, A_17]: (r2_hidden(k3_xboole_0(B_18, C_20), k9_setfam_1(A_17)) | ~m1_subset_1(C_20, k9_setfam_1(A_17)) | ~m1_subset_1(B_18, k9_setfam_1(A_17)))), inference(demodulation, [status(thm), theory('equality')], [c_89, c_89, c_36])).
% 6.08/2.20  tff(c_2963, plain, (![B_332, C_333, A_334]: (r2_hidden(k3_xboole_0(B_332, C_333), k9_setfam_1(A_334)) | ~m1_subset_1(C_333, k9_setfam_1(A_334)) | ~m1_subset_1(B_332, k9_setfam_1(A_334)))), inference(demodulation, [status(thm), theory('equality')], [c_89, c_89, c_36])).
% 6.08/2.20  tff(c_2978, plain, (![A_335, C_336, B_337]: (~v1_xboole_0(k9_setfam_1(A_335)) | ~m1_subset_1(C_336, k9_setfam_1(A_335)) | ~m1_subset_1(B_337, k9_setfam_1(A_335)))), inference(resolution, [status(thm)], [c_2963, c_2])).
% 6.08/2.20  tff(c_3010, plain, (![B_337, A_335, B_6]: (~m1_subset_1(B_337, k9_setfam_1(A_335)) | ~v1_xboole_0(B_6) | ~v1_xboole_0(k9_setfam_1(A_335)))), inference(resolution, [status(thm)], [c_10, c_2978])).
% 6.08/2.20  tff(c_3014, plain, (![B_338, A_339]: (~m1_subset_1(B_338, k9_setfam_1(A_339)) | ~v1_xboole_0(k9_setfam_1(A_339)))), inference(splitLeft, [status(thm)], [c_3010])).
% 6.08/2.20  tff(c_3054, plain, (![B_6, A_339]: (~v1_xboole_0(B_6) | ~v1_xboole_0(k9_setfam_1(A_339)))), inference(resolution, [status(thm)], [c_10, c_3014])).
% 6.08/2.20  tff(c_3057, plain, (![A_339]: (~v1_xboole_0(k9_setfam_1(A_339)))), inference(splitLeft, [status(thm)], [c_3054])).
% 6.08/2.20  tff(c_58, plain, (![A_36, B_40, C_42]: (k11_lattice3(k2_yellow_1(A_36), B_40, C_42)=k3_xboole_0(B_40, C_42) | ~r2_hidden(k3_xboole_0(B_40, C_42), A_36) | ~m1_subset_1(C_42, u1_struct_0(k2_yellow_1(A_36))) | ~m1_subset_1(B_40, u1_struct_0(k2_yellow_1(A_36))) | v1_xboole_0(A_36))), inference(cnfTransformation, [status(thm)], [f_150])).
% 6.08/2.20  tff(c_3356, plain, (![A_364, B_365, C_366]: (k11_lattice3(k2_yellow_1(A_364), B_365, C_366)=k3_xboole_0(B_365, C_366) | ~r2_hidden(k3_xboole_0(B_365, C_366), A_364) | ~m1_subset_1(C_366, A_364) | ~m1_subset_1(B_365, A_364) | v1_xboole_0(A_364))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_50, c_58])).
% 6.08/2.20  tff(c_3359, plain, (![A_17, B_18, C_20]: (k11_lattice3(k2_yellow_1(k9_setfam_1(A_17)), B_18, C_20)=k3_xboole_0(B_18, C_20) | v1_xboole_0(k9_setfam_1(A_17)) | ~m1_subset_1(C_20, k9_setfam_1(A_17)) | ~m1_subset_1(B_18, k9_setfam_1(A_17)))), inference(resolution, [status(thm)], [c_2962, c_3356])).
% 6.08/2.20  tff(c_3365, plain, (![A_17, B_18, C_20]: (k11_lattice3(k3_yellow_1(A_17), B_18, C_20)=k3_xboole_0(B_18, C_20) | v1_xboole_0(k9_setfam_1(A_17)) | ~m1_subset_1(C_20, k9_setfam_1(A_17)) | ~m1_subset_1(B_18, k9_setfam_1(A_17)))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_3359])).
% 6.08/2.20  tff(c_3385, plain, (![A_369, B_370, C_371]: (k11_lattice3(k3_yellow_1(A_369), B_370, C_371)=k3_xboole_0(B_370, C_371) | ~m1_subset_1(C_371, k9_setfam_1(A_369)) | ~m1_subset_1(B_370, k9_setfam_1(A_369)))), inference(negUnitSimplification, [status(thm)], [c_3057, c_3365])).
% 6.08/2.20  tff(c_3523, plain, (![B_376]: (k11_lattice3(k3_yellow_1('#skF_6'), B_376, '#skF_8')=k3_xboole_0(B_376, '#skF_8') | ~m1_subset_1(B_376, k9_setfam_1('#skF_6')))), inference(resolution, [status(thm)], [c_108, c_3385])).
% 6.08/2.20  tff(c_3575, plain, (k11_lattice3(k3_yellow_1('#skF_6'), '#skF_7', '#skF_8')=k3_xboole_0('#skF_7', '#skF_8')), inference(resolution, [status(thm)], [c_109, c_3523])).
% 6.08/2.20  tff(c_2912, plain, (![A_324]: (r2_hidden('#skF_4'(A_324), A_324) | v2_lattice3(k2_yellow_1(A_324)) | v1_xboole_0(A_324))), inference(cnfTransformation, [status(thm)], [f_118])).
% 6.08/2.20  tff(c_2919, plain, (![A_324]: (m1_subset_1('#skF_4'(A_324), A_324) | v2_lattice3(k2_yellow_1(A_324)) | v1_xboole_0(A_324))), inference(resolution, [status(thm)], [c_2912, c_6])).
% 6.08/2.20  tff(c_2921, plain, (![A_325]: (r2_hidden('#skF_5'(A_325), A_325) | v2_lattice3(k2_yellow_1(A_325)) | v1_xboole_0(A_325))), inference(cnfTransformation, [status(thm)], [f_118])).
% 6.08/2.20  tff(c_2928, plain, (![A_325]: (m1_subset_1('#skF_5'(A_325), A_325) | v2_lattice3(k2_yellow_1(A_325)) | v1_xboole_0(A_325))), inference(resolution, [status(thm)], [c_2921, c_6])).
% 6.08/2.20  tff(c_2976, plain, (![B_332, C_333, A_334]: (m1_subset_1(k3_xboole_0(B_332, C_333), k9_setfam_1(A_334)) | v1_xboole_0(k9_setfam_1(A_334)) | ~m1_subset_1(C_333, k9_setfam_1(A_334)) | ~m1_subset_1(B_332, k9_setfam_1(A_334)))), inference(resolution, [status(thm)], [c_2963, c_6])).
% 6.08/2.20  tff(c_3618, plain, (![B_384, C_385, A_386]: (m1_subset_1(k3_xboole_0(B_384, C_385), k9_setfam_1(A_386)) | ~m1_subset_1(C_385, k9_setfam_1(A_386)) | ~m1_subset_1(B_384, k9_setfam_1(A_386)))), inference(negUnitSimplification, [status(thm)], [c_3057, c_2976])).
% 6.08/2.20  tff(c_8, plain, (![B_6, A_5]: (r2_hidden(B_6, A_5) | ~m1_subset_1(B_6, A_5) | v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_44])).
% 6.08/2.20  tff(c_2940, plain, (![A_328]: (~r2_hidden(k3_xboole_0('#skF_4'(A_328), '#skF_5'(A_328)), A_328) | v2_lattice3(k2_yellow_1(A_328)) | v1_xboole_0(A_328))), inference(cnfTransformation, [status(thm)], [f_118])).
% 6.08/2.20  tff(c_2945, plain, (![A_5]: (v2_lattice3(k2_yellow_1(A_5)) | ~m1_subset_1(k3_xboole_0('#skF_4'(A_5), '#skF_5'(A_5)), A_5) | v1_xboole_0(A_5))), inference(resolution, [status(thm)], [c_8, c_2940])).
% 6.08/2.20  tff(c_3645, plain, (![A_386]: (v2_lattice3(k2_yellow_1(k9_setfam_1(A_386))) | v1_xboole_0(k9_setfam_1(A_386)) | ~m1_subset_1('#skF_5'(k9_setfam_1(A_386)), k9_setfam_1(A_386)) | ~m1_subset_1('#skF_4'(k9_setfam_1(A_386)), k9_setfam_1(A_386)))), inference(resolution, [status(thm)], [c_3618, c_2945])).
% 6.08/2.20  tff(c_3659, plain, (![A_386]: (v2_lattice3(k3_yellow_1(A_386)) | v1_xboole_0(k9_setfam_1(A_386)) | ~m1_subset_1('#skF_5'(k9_setfam_1(A_386)), k9_setfam_1(A_386)) | ~m1_subset_1('#skF_4'(k9_setfam_1(A_386)), k9_setfam_1(A_386)))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_3645])).
% 6.08/2.20  tff(c_3662, plain, (![A_387]: (v2_lattice3(k3_yellow_1(A_387)) | ~m1_subset_1('#skF_5'(k9_setfam_1(A_387)), k9_setfam_1(A_387)) | ~m1_subset_1('#skF_4'(k9_setfam_1(A_387)), k9_setfam_1(A_387)))), inference(negUnitSimplification, [status(thm)], [c_3057, c_3659])).
% 6.08/2.20  tff(c_3665, plain, (![A_387]: (v2_lattice3(k3_yellow_1(A_387)) | ~m1_subset_1('#skF_4'(k9_setfam_1(A_387)), k9_setfam_1(A_387)) | v2_lattice3(k2_yellow_1(k9_setfam_1(A_387))) | v1_xboole_0(k9_setfam_1(A_387)))), inference(resolution, [status(thm)], [c_2928, c_3662])).
% 6.08/2.20  tff(c_3670, plain, (![A_387]: (v2_lattice3(k3_yellow_1(A_387)) | ~m1_subset_1('#skF_4'(k9_setfam_1(A_387)), k9_setfam_1(A_387)) | v2_lattice3(k3_yellow_1(A_387)) | v1_xboole_0(k9_setfam_1(A_387)))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_3665])).
% 6.08/2.20  tff(c_3673, plain, (![A_388]: (v2_lattice3(k3_yellow_1(A_388)) | ~m1_subset_1('#skF_4'(k9_setfam_1(A_388)), k9_setfam_1(A_388)) | v2_lattice3(k3_yellow_1(A_388)))), inference(negUnitSimplification, [status(thm)], [c_3057, c_3670])).
% 6.08/2.20  tff(c_3676, plain, (![A_388]: (v2_lattice3(k3_yellow_1(A_388)) | v2_lattice3(k2_yellow_1(k9_setfam_1(A_388))) | v1_xboole_0(k9_setfam_1(A_388)))), inference(resolution, [status(thm)], [c_2919, c_3673])).
% 6.08/2.20  tff(c_3681, plain, (![A_388]: (v2_lattice3(k3_yellow_1(A_388)) | v2_lattice3(k3_yellow_1(A_388)) | v1_xboole_0(k9_setfam_1(A_388)))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_3676])).
% 6.08/2.20  tff(c_3682, plain, (![A_388]: (v2_lattice3(k3_yellow_1(A_388)) | v2_lattice3(k3_yellow_1(A_388)))), inference(negUnitSimplification, [status(thm)], [c_3057, c_3681])).
% 6.08/2.20  tff(c_3701, plain, (![A_388]: (v2_lattice3(k3_yellow_1(A_388)))), inference(factorization, [status(thm), theory('equality')], [c_3682])).
% 6.08/2.20  tff(c_3102, plain, (![A_349, B_350, C_351]: (k12_lattice3(A_349, B_350, C_351)=k11_lattice3(A_349, B_350, C_351) | ~m1_subset_1(C_351, u1_struct_0(A_349)) | ~m1_subset_1(B_350, u1_struct_0(A_349)) | ~l1_orders_2(A_349) | ~v2_lattice3(A_349) | ~v5_orders_2(A_349))), inference(cnfTransformation, [status(thm)], [f_58])).
% 6.08/2.20  tff(c_3122, plain, (![A_51, B_350, C_351]: (k12_lattice3(k3_yellow_1(A_51), B_350, C_351)=k11_lattice3(k3_yellow_1(A_51), B_350, C_351) | ~m1_subset_1(C_351, k9_setfam_1(A_51)) | ~m1_subset_1(B_350, u1_struct_0(k3_yellow_1(A_51))) | ~l1_orders_2(k3_yellow_1(A_51)) | ~v2_lattice3(k3_yellow_1(A_51)) | ~v5_orders_2(k3_yellow_1(A_51)))), inference(superposition, [status(thm), theory('equality')], [c_89, c_3102])).
% 6.08/2.20  tff(c_3132, plain, (![A_51, B_350, C_351]: (k12_lattice3(k3_yellow_1(A_51), B_350, C_351)=k11_lattice3(k3_yellow_1(A_51), B_350, C_351) | ~m1_subset_1(C_351, k9_setfam_1(A_51)) | ~m1_subset_1(B_350, k9_setfam_1(A_51)) | ~v2_lattice3(k3_yellow_1(A_51)))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_22, c_89, c_3122])).
% 6.08/2.20  tff(c_4046, plain, (![A_424, B_425, C_426]: (k12_lattice3(k3_yellow_1(A_424), B_425, C_426)=k11_lattice3(k3_yellow_1(A_424), B_425, C_426) | ~m1_subset_1(C_426, k9_setfam_1(A_424)) | ~m1_subset_1(B_425, k9_setfam_1(A_424)))), inference(demodulation, [status(thm), theory('equality')], [c_3701, c_3132])).
% 6.08/2.20  tff(c_4154, plain, (![B_428]: (k12_lattice3(k3_yellow_1('#skF_6'), B_428, '#skF_8')=k11_lattice3(k3_yellow_1('#skF_6'), B_428, '#skF_8') | ~m1_subset_1(B_428, k9_setfam_1('#skF_6')))), inference(resolution, [status(thm)], [c_108, c_4046])).
% 6.08/2.20  tff(c_4189, plain, (k12_lattice3(k3_yellow_1('#skF_6'), '#skF_7', '#skF_8')=k11_lattice3(k3_yellow_1('#skF_6'), '#skF_7', '#skF_8')), inference(resolution, [status(thm)], [c_109, c_4154])).
% 6.08/2.20  tff(c_4212, plain, (k12_lattice3(k3_yellow_1('#skF_6'), '#skF_7', '#skF_8')=k3_xboole_0('#skF_7', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_3575, c_4189])).
% 6.08/2.20  tff(c_4214, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2855, c_4212])).
% 6.08/2.20  tff(c_4215, plain, (![B_6]: (~v1_xboole_0(B_6))), inference(splitRight, [status(thm)], [c_3054])).
% 6.08/2.20  tff(c_65, plain, (![A_36, B_40, C_42]: (k11_lattice3(k2_yellow_1(A_36), B_40, C_42)=k3_xboole_0(B_40, C_42) | ~r2_hidden(k3_xboole_0(B_40, C_42), A_36) | ~m1_subset_1(C_42, A_36) | ~m1_subset_1(B_40, A_36) | v1_xboole_0(A_36))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_50, c_58])).
% 6.08/2.20  tff(c_4336, plain, (![A_454, B_455, C_456]: (k11_lattice3(k2_yellow_1(A_454), B_455, C_456)=k3_xboole_0(B_455, C_456) | ~r2_hidden(k3_xboole_0(B_455, C_456), A_454) | ~m1_subset_1(C_456, A_454) | ~m1_subset_1(B_455, A_454))), inference(negUnitSimplification, [status(thm)], [c_4215, c_65])).
% 6.08/2.20  tff(c_4343, plain, (![A_17, B_18, C_20]: (k11_lattice3(k2_yellow_1(k9_setfam_1(A_17)), B_18, C_20)=k3_xboole_0(B_18, C_20) | ~m1_subset_1(C_20, k9_setfam_1(A_17)) | ~m1_subset_1(B_18, k9_setfam_1(A_17)))), inference(resolution, [status(thm)], [c_2962, c_4336])).
% 6.08/2.20  tff(c_4621, plain, (![A_485, B_486, C_487]: (k11_lattice3(k3_yellow_1(A_485), B_486, C_487)=k3_xboole_0(B_486, C_487) | ~m1_subset_1(C_487, k9_setfam_1(A_485)) | ~m1_subset_1(B_486, k9_setfam_1(A_485)))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_4343])).
% 6.08/2.20  tff(c_4720, plain, (![B_492]: (k11_lattice3(k3_yellow_1('#skF_6'), B_492, '#skF_8')=k3_xboole_0(B_492, '#skF_8') | ~m1_subset_1(B_492, k9_setfam_1('#skF_6')))), inference(resolution, [status(thm)], [c_108, c_4621])).
% 6.08/2.20  tff(c_4766, plain, (k11_lattice3(k3_yellow_1('#skF_6'), '#skF_7', '#skF_8')=k3_xboole_0('#skF_7', '#skF_8')), inference(resolution, [status(thm)], [c_109, c_4720])).
% 6.08/2.20  tff(c_48, plain, (![A_24]: (r2_hidden('#skF_4'(A_24), A_24) | v2_lattice3(k2_yellow_1(A_24)) | v1_xboole_0(A_24))), inference(cnfTransformation, [status(thm)], [f_118])).
% 6.08/2.20  tff(c_4259, plain, (![A_438]: (r2_hidden('#skF_4'(A_438), A_438) | v2_lattice3(k2_yellow_1(A_438)))), inference(negUnitSimplification, [status(thm)], [c_4215, c_48])).
% 6.08/2.20  tff(c_4228, plain, (![B_6, A_5]: (m1_subset_1(B_6, A_5) | ~r2_hidden(B_6, A_5))), inference(negUnitSimplification, [status(thm)], [c_4215, c_6])).
% 6.08/2.20  tff(c_4263, plain, (![A_438]: (m1_subset_1('#skF_4'(A_438), A_438) | v2_lattice3(k2_yellow_1(A_438)))), inference(resolution, [status(thm)], [c_4259, c_4228])).
% 6.08/2.20  tff(c_46, plain, (![A_24]: (r2_hidden('#skF_5'(A_24), A_24) | v2_lattice3(k2_yellow_1(A_24)) | v1_xboole_0(A_24))), inference(cnfTransformation, [status(thm)], [f_118])).
% 6.08/2.20  tff(c_4254, plain, (![A_437]: (r2_hidden('#skF_5'(A_437), A_437) | v2_lattice3(k2_yellow_1(A_437)))), inference(negUnitSimplification, [status(thm)], [c_4215, c_46])).
% 6.08/2.20  tff(c_4258, plain, (![A_437]: (m1_subset_1('#skF_5'(A_437), A_437) | v2_lattice3(k2_yellow_1(A_437)))), inference(resolution, [status(thm)], [c_4254, c_4228])).
% 6.08/2.20  tff(c_44, plain, (![A_24]: (~r2_hidden(k3_xboole_0('#skF_4'(A_24), '#skF_5'(A_24)), A_24) | v2_lattice3(k2_yellow_1(A_24)) | v1_xboole_0(A_24))), inference(cnfTransformation, [status(thm)], [f_118])).
% 6.08/2.20  tff(c_4278, plain, (![A_446]: (~r2_hidden(k3_xboole_0('#skF_4'(A_446), '#skF_5'(A_446)), A_446) | v2_lattice3(k2_yellow_1(A_446)))), inference(negUnitSimplification, [status(thm)], [c_4215, c_44])).
% 6.08/2.20  tff(c_4286, plain, (![A_17]: (v2_lattice3(k2_yellow_1(k9_setfam_1(A_17))) | ~m1_subset_1('#skF_5'(k9_setfam_1(A_17)), k9_setfam_1(A_17)) | ~m1_subset_1('#skF_4'(k9_setfam_1(A_17)), k9_setfam_1(A_17)))), inference(resolution, [status(thm)], [c_2962, c_4278])).
% 6.08/2.20  tff(c_4361, plain, (![A_463]: (v2_lattice3(k3_yellow_1(A_463)) | ~m1_subset_1('#skF_5'(k9_setfam_1(A_463)), k9_setfam_1(A_463)) | ~m1_subset_1('#skF_4'(k9_setfam_1(A_463)), k9_setfam_1(A_463)))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_4286])).
% 6.08/2.20  tff(c_4364, plain, (![A_463]: (v2_lattice3(k3_yellow_1(A_463)) | ~m1_subset_1('#skF_4'(k9_setfam_1(A_463)), k9_setfam_1(A_463)) | v2_lattice3(k2_yellow_1(k9_setfam_1(A_463))))), inference(resolution, [status(thm)], [c_4258, c_4361])).
% 6.08/2.20  tff(c_4395, plain, (![A_467]: (v2_lattice3(k3_yellow_1(A_467)) | ~m1_subset_1('#skF_4'(k9_setfam_1(A_467)), k9_setfam_1(A_467)) | v2_lattice3(k3_yellow_1(A_467)))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_4364])).
% 6.08/2.20  tff(c_4398, plain, (![A_467]: (v2_lattice3(k3_yellow_1(A_467)) | v2_lattice3(k2_yellow_1(k9_setfam_1(A_467))))), inference(resolution, [status(thm)], [c_4263, c_4395])).
% 6.08/2.20  tff(c_4400, plain, (![A_467]: (v2_lattice3(k3_yellow_1(A_467)) | v2_lattice3(k3_yellow_1(A_467)))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_4398])).
% 6.08/2.20  tff(c_4409, plain, (![A_467]: (v2_lattice3(k3_yellow_1(A_467)))), inference(factorization, [status(thm), theory('equality')], [c_4400])).
% 6.08/2.20  tff(c_4367, plain, (![A_464, B_465, C_466]: (k12_lattice3(A_464, B_465, C_466)=k11_lattice3(A_464, B_465, C_466) | ~m1_subset_1(C_466, u1_struct_0(A_464)) | ~m1_subset_1(B_465, u1_struct_0(A_464)) | ~l1_orders_2(A_464) | ~v2_lattice3(A_464) | ~v5_orders_2(A_464))), inference(cnfTransformation, [status(thm)], [f_58])).
% 6.08/2.20  tff(c_4386, plain, (![A_27, B_465, C_466]: (k12_lattice3(k2_yellow_1(A_27), B_465, C_466)=k11_lattice3(k2_yellow_1(A_27), B_465, C_466) | ~m1_subset_1(C_466, A_27) | ~m1_subset_1(B_465, u1_struct_0(k2_yellow_1(A_27))) | ~l1_orders_2(k2_yellow_1(A_27)) | ~v2_lattice3(k2_yellow_1(A_27)) | ~v5_orders_2(k2_yellow_1(A_27)))), inference(superposition, [status(thm), theory('equality')], [c_50, c_4367])).
% 6.08/2.20  tff(c_4964, plain, (![A_505, B_506, C_507]: (k12_lattice3(k2_yellow_1(A_505), B_506, C_507)=k11_lattice3(k2_yellow_1(A_505), B_506, C_507) | ~m1_subset_1(C_507, A_505) | ~m1_subset_1(B_506, A_505) | ~l1_orders_2(k2_yellow_1(A_505)) | ~v2_lattice3(k2_yellow_1(A_505)) | ~v5_orders_2(k2_yellow_1(A_505)))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_4386])).
% 6.08/2.20  tff(c_4966, plain, (![A_28, B_506, C_507]: (k12_lattice3(k2_yellow_1(k9_setfam_1(A_28)), B_506, C_507)=k11_lattice3(k2_yellow_1(k9_setfam_1(A_28)), B_506, C_507) | ~m1_subset_1(C_507, k9_setfam_1(A_28)) | ~m1_subset_1(B_506, k9_setfam_1(A_28)) | ~l1_orders_2(k2_yellow_1(k9_setfam_1(A_28))) | ~v2_lattice3(k2_yellow_1(k9_setfam_1(A_28))) | ~v5_orders_2(k3_yellow_1(A_28)))), inference(superposition, [status(thm), theory('equality')], [c_54, c_4964])).
% 6.08/2.20  tff(c_4973, plain, (![A_508, B_509, C_510]: (k12_lattice3(k3_yellow_1(A_508), B_509, C_510)=k11_lattice3(k3_yellow_1(A_508), B_509, C_510) | ~m1_subset_1(C_510, k9_setfam_1(A_508)) | ~m1_subset_1(B_509, k9_setfam_1(A_508)))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_4409, c_54, c_22, c_54, c_54, c_54, c_4966])).
% 6.08/2.20  tff(c_5061, plain, (![B_512]: (k12_lattice3(k3_yellow_1('#skF_6'), B_512, '#skF_8')=k11_lattice3(k3_yellow_1('#skF_6'), B_512, '#skF_8') | ~m1_subset_1(B_512, k9_setfam_1('#skF_6')))), inference(resolution, [status(thm)], [c_108, c_4973])).
% 6.08/2.20  tff(c_5092, plain, (k12_lattice3(k3_yellow_1('#skF_6'), '#skF_7', '#skF_8')=k11_lattice3(k3_yellow_1('#skF_6'), '#skF_7', '#skF_8')), inference(resolution, [status(thm)], [c_109, c_5061])).
% 6.08/2.20  tff(c_5109, plain, (k12_lattice3(k3_yellow_1('#skF_6'), '#skF_7', '#skF_8')=k3_xboole_0('#skF_7', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_4766, c_5092])).
% 6.08/2.20  tff(c_5111, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2855, c_5109])).
% 6.08/2.20  tff(c_5112, plain, (![B_6]: (~v1_xboole_0(B_6))), inference(splitRight, [status(thm)], [c_3010])).
% 6.08/2.20  tff(c_5233, plain, (![A_538, B_539, C_540]: (k11_lattice3(k2_yellow_1(A_538), B_539, C_540)=k3_xboole_0(B_539, C_540) | ~r2_hidden(k3_xboole_0(B_539, C_540), A_538) | ~m1_subset_1(C_540, A_538) | ~m1_subset_1(B_539, A_538))), inference(negUnitSimplification, [status(thm)], [c_5112, c_65])).
% 6.08/2.20  tff(c_5240, plain, (![A_17, B_18, C_20]: (k11_lattice3(k2_yellow_1(k9_setfam_1(A_17)), B_18, C_20)=k3_xboole_0(B_18, C_20) | ~m1_subset_1(C_20, k9_setfam_1(A_17)) | ~m1_subset_1(B_18, k9_setfam_1(A_17)))), inference(resolution, [status(thm)], [c_2962, c_5233])).
% 6.08/2.20  tff(c_5518, plain, (![A_569, B_570, C_571]: (k11_lattice3(k3_yellow_1(A_569), B_570, C_571)=k3_xboole_0(B_570, C_571) | ~m1_subset_1(C_571, k9_setfam_1(A_569)) | ~m1_subset_1(B_570, k9_setfam_1(A_569)))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_5240])).
% 6.08/2.20  tff(c_5617, plain, (![B_576]: (k11_lattice3(k3_yellow_1('#skF_6'), B_576, '#skF_8')=k3_xboole_0(B_576, '#skF_8') | ~m1_subset_1(B_576, k9_setfam_1('#skF_6')))), inference(resolution, [status(thm)], [c_108, c_5518])).
% 6.08/2.20  tff(c_5663, plain, (k11_lattice3(k3_yellow_1('#skF_6'), '#skF_7', '#skF_8')=k3_xboole_0('#skF_7', '#skF_8')), inference(resolution, [status(thm)], [c_109, c_5617])).
% 6.08/2.20  tff(c_5156, plain, (![A_522]: (r2_hidden('#skF_4'(A_522), A_522) | v2_lattice3(k2_yellow_1(A_522)))), inference(negUnitSimplification, [status(thm)], [c_5112, c_48])).
% 6.08/2.20  tff(c_5125, plain, (![B_6, A_5]: (m1_subset_1(B_6, A_5) | ~r2_hidden(B_6, A_5))), inference(negUnitSimplification, [status(thm)], [c_5112, c_6])).
% 6.08/2.20  tff(c_5160, plain, (![A_522]: (m1_subset_1('#skF_4'(A_522), A_522) | v2_lattice3(k2_yellow_1(A_522)))), inference(resolution, [status(thm)], [c_5156, c_5125])).
% 6.08/2.20  tff(c_5151, plain, (![A_521]: (r2_hidden('#skF_5'(A_521), A_521) | v2_lattice3(k2_yellow_1(A_521)))), inference(negUnitSimplification, [status(thm)], [c_5112, c_46])).
% 6.08/2.20  tff(c_5155, plain, (![A_521]: (m1_subset_1('#skF_5'(A_521), A_521) | v2_lattice3(k2_yellow_1(A_521)))), inference(resolution, [status(thm)], [c_5151, c_5125])).
% 6.08/2.20  tff(c_5175, plain, (![A_530]: (~r2_hidden(k3_xboole_0('#skF_4'(A_530), '#skF_5'(A_530)), A_530) | v2_lattice3(k2_yellow_1(A_530)))), inference(negUnitSimplification, [status(thm)], [c_5112, c_44])).
% 6.08/2.20  tff(c_5183, plain, (![A_17]: (v2_lattice3(k2_yellow_1(k9_setfam_1(A_17))) | ~m1_subset_1('#skF_5'(k9_setfam_1(A_17)), k9_setfam_1(A_17)) | ~m1_subset_1('#skF_4'(k9_setfam_1(A_17)), k9_setfam_1(A_17)))), inference(resolution, [status(thm)], [c_2962, c_5175])).
% 6.08/2.20  tff(c_5258, plain, (![A_547]: (v2_lattice3(k3_yellow_1(A_547)) | ~m1_subset_1('#skF_5'(k9_setfam_1(A_547)), k9_setfam_1(A_547)) | ~m1_subset_1('#skF_4'(k9_setfam_1(A_547)), k9_setfam_1(A_547)))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_5183])).
% 6.08/2.20  tff(c_5261, plain, (![A_547]: (v2_lattice3(k3_yellow_1(A_547)) | ~m1_subset_1('#skF_4'(k9_setfam_1(A_547)), k9_setfam_1(A_547)) | v2_lattice3(k2_yellow_1(k9_setfam_1(A_547))))), inference(resolution, [status(thm)], [c_5155, c_5258])).
% 6.08/2.20  tff(c_5292, plain, (![A_551]: (v2_lattice3(k3_yellow_1(A_551)) | ~m1_subset_1('#skF_4'(k9_setfam_1(A_551)), k9_setfam_1(A_551)) | v2_lattice3(k3_yellow_1(A_551)))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_5261])).
% 6.08/2.20  tff(c_5295, plain, (![A_551]: (v2_lattice3(k3_yellow_1(A_551)) | v2_lattice3(k2_yellow_1(k9_setfam_1(A_551))))), inference(resolution, [status(thm)], [c_5160, c_5292])).
% 6.08/2.20  tff(c_5297, plain, (![A_551]: (v2_lattice3(k3_yellow_1(A_551)) | v2_lattice3(k3_yellow_1(A_551)))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_5295])).
% 6.08/2.20  tff(c_5306, plain, (![A_551]: (v2_lattice3(k3_yellow_1(A_551)))), inference(factorization, [status(thm), theory('equality')], [c_5297])).
% 6.08/2.20  tff(c_5264, plain, (![A_548, B_549, C_550]: (k12_lattice3(A_548, B_549, C_550)=k11_lattice3(A_548, B_549, C_550) | ~m1_subset_1(C_550, u1_struct_0(A_548)) | ~m1_subset_1(B_549, u1_struct_0(A_548)) | ~l1_orders_2(A_548) | ~v2_lattice3(A_548) | ~v5_orders_2(A_548))), inference(cnfTransformation, [status(thm)], [f_58])).
% 6.08/2.20  tff(c_5283, plain, (![A_27, B_549, C_550]: (k12_lattice3(k2_yellow_1(A_27), B_549, C_550)=k11_lattice3(k2_yellow_1(A_27), B_549, C_550) | ~m1_subset_1(C_550, A_27) | ~m1_subset_1(B_549, u1_struct_0(k2_yellow_1(A_27))) | ~l1_orders_2(k2_yellow_1(A_27)) | ~v2_lattice3(k2_yellow_1(A_27)) | ~v5_orders_2(k2_yellow_1(A_27)))), inference(superposition, [status(thm), theory('equality')], [c_50, c_5264])).
% 6.08/2.20  tff(c_5861, plain, (![A_589, B_590, C_591]: (k12_lattice3(k2_yellow_1(A_589), B_590, C_591)=k11_lattice3(k2_yellow_1(A_589), B_590, C_591) | ~m1_subset_1(C_591, A_589) | ~m1_subset_1(B_590, A_589) | ~l1_orders_2(k2_yellow_1(A_589)) | ~v2_lattice3(k2_yellow_1(A_589)) | ~v5_orders_2(k2_yellow_1(A_589)))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_5283])).
% 6.08/2.20  tff(c_5863, plain, (![A_28, B_590, C_591]: (k12_lattice3(k2_yellow_1(k9_setfam_1(A_28)), B_590, C_591)=k11_lattice3(k2_yellow_1(k9_setfam_1(A_28)), B_590, C_591) | ~m1_subset_1(C_591, k9_setfam_1(A_28)) | ~m1_subset_1(B_590, k9_setfam_1(A_28)) | ~l1_orders_2(k2_yellow_1(k9_setfam_1(A_28))) | ~v2_lattice3(k2_yellow_1(k9_setfam_1(A_28))) | ~v5_orders_2(k3_yellow_1(A_28)))), inference(superposition, [status(thm), theory('equality')], [c_54, c_5861])).
% 6.08/2.20  tff(c_5870, plain, (![A_592, B_593, C_594]: (k12_lattice3(k3_yellow_1(A_592), B_593, C_594)=k11_lattice3(k3_yellow_1(A_592), B_593, C_594) | ~m1_subset_1(C_594, k9_setfam_1(A_592)) | ~m1_subset_1(B_593, k9_setfam_1(A_592)))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_5306, c_54, c_22, c_54, c_54, c_54, c_5863])).
% 6.08/2.20  tff(c_5958, plain, (![B_596]: (k12_lattice3(k3_yellow_1('#skF_6'), B_596, '#skF_8')=k11_lattice3(k3_yellow_1('#skF_6'), B_596, '#skF_8') | ~m1_subset_1(B_596, k9_setfam_1('#skF_6')))), inference(resolution, [status(thm)], [c_108, c_5870])).
% 6.08/2.20  tff(c_5989, plain, (k12_lattice3(k3_yellow_1('#skF_6'), '#skF_7', '#skF_8')=k11_lattice3(k3_yellow_1('#skF_6'), '#skF_7', '#skF_8')), inference(resolution, [status(thm)], [c_109, c_5958])).
% 6.08/2.20  tff(c_6006, plain, (k12_lattice3(k3_yellow_1('#skF_6'), '#skF_7', '#skF_8')=k3_xboole_0('#skF_7', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_5663, c_5989])).
% 6.08/2.20  tff(c_6008, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2855, c_6006])).
% 6.08/2.20  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.08/2.20  
% 6.08/2.20  Inference rules
% 6.08/2.20  ----------------------
% 6.08/2.20  #Ref     : 0
% 6.08/2.20  #Sup     : 1220
% 6.08/2.20  #Fact    : 24
% 6.08/2.20  #Define  : 0
% 6.08/2.20  #Split   : 8
% 6.08/2.20  #Chain   : 0
% 6.08/2.20  #Close   : 0
% 6.08/2.20  
% 6.08/2.20  Ordering : KBO
% 6.08/2.20  
% 6.08/2.20  Simplification rules
% 6.08/2.20  ----------------------
% 6.08/2.20  #Subsume      : 125
% 6.08/2.20  #Demod        : 877
% 6.08/2.20  #Tautology    : 653
% 6.08/2.20  #SimpNegUnit  : 223
% 6.08/2.20  #BackRed      : 60
% 6.08/2.20  
% 6.08/2.20  #Partial instantiations: 0
% 6.08/2.20  #Strategies tried      : 1
% 6.08/2.20  
% 6.08/2.20  Timing (in seconds)
% 6.08/2.20  ----------------------
% 6.08/2.20  Preprocessing        : 0.33
% 6.08/2.20  Parsing              : 0.18
% 6.08/2.20  CNF conversion       : 0.02
% 6.08/2.20  Main loop            : 1.05
% 6.08/2.20  Inferencing          : 0.39
% 6.08/2.20  Reduction            : 0.35
% 6.08/2.20  Demodulation         : 0.24
% 6.08/2.20  BG Simplification    : 0.05
% 6.08/2.20  Subsumption          : 0.16
% 6.08/2.20  Abstraction          : 0.07
% 6.08/2.20  MUC search           : 0.00
% 6.08/2.20  Cooper               : 0.00
% 6.08/2.20  Total                : 1.47
% 6.08/2.20  Index Insertion      : 0.00
% 6.08/2.20  Index Deletion       : 0.00
% 6.08/2.20  Index Matching       : 0.00
% 6.08/2.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
