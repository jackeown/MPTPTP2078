%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:56 EST 2020

% Result     : Theorem 2.24s
% Output     : CNFRefutation 2.68s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 436 expanded)
%              Number of leaves         :   34 ( 163 expanded)
%              Depth                    :   16
%              Number of atoms          :  234 (1814 expanded)
%              Number of equality atoms :    1 (   6 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_orders_2 > r2_lattice3 > r1_orders_2 > r1_lattice3 > r2_yellow_0 > r1_yellow_0 > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v3_lattice3 > v2_struct_0 > v2_lattice3 > v1_lattice3 > l1_orders_2 > k2_yellow_0 > k1_yellow_0 > #nlpp > u1_struct_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(r3_orders_2,type,(
    r3_orders_2: ( $i * $i * $i ) > $o )).

tff(k1_yellow_0,type,(
    k1_yellow_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff(v3_lattice3,type,(
    v3_lattice3: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r2_lattice3,type,(
    r2_lattice3: ( $i * $i * $i ) > $o )).

tff(v1_lattice3,type,(
    v1_lattice3: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(r2_yellow_0,type,(
    r2_yellow_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k2_yellow_0,type,(
    k2_yellow_0: ( $i * $i ) > $i )).

tff(r1_lattice3,type,(
    r1_lattice3: ( $i * $i * $i ) > $o )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(r1_yellow_0,type,(
    r1_yellow_0: ( $i * $i ) > $o )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_lattice3,type,(
    v2_lattice3: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_132,negated_conjecture,(
    ~ ! [A] :
        ( ( v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & v1_lattice3(A)
          & v2_lattice3(A)
          & v3_lattice3(A)
          & l1_orders_2(A) )
       => ! [B,C] :
            ( r1_tarski(B,C)
           => ( r3_orders_2(A,k1_yellow_0(A,B),k1_yellow_0(A,C))
              & r1_orders_2(A,k2_yellow_0(A,C),k2_yellow_0(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_waybel_7)).

tff(f_83,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v5_orders_2(A)
        & v3_lattice3(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( r1_yellow_0(A,B)
          & r2_yellow_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_yellow_0)).

tff(f_94,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B,C] :
          ( ( r1_tarski(B,C)
            & r2_yellow_0(A,B)
            & r2_yellow_0(A,C) )
         => r1_orders_2(A,k2_yellow_0(A,C),k2_yellow_0(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_yellow_0)).

tff(f_69,axiom,(
    ! [A,B] :
      ( l1_orders_2(A)
     => m1_subset_1(k1_yellow_0(A,B),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_yellow_0)).

tff(f_40,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => ( r3_orders_2(A,B,C)
      <=> r1_orders_2(A,B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_orders_2)).

tff(f_47,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v1_lattice3(A)
       => ~ v2_struct_0(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_lattice3)).

tff(f_65,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B,C] :
          ( m1_subset_1(C,u1_struct_0(A))
         => ( r1_yellow_0(A,B)
           => ( C = k1_yellow_0(A,B)
            <=> ( r2_lattice3(A,B,C)
                & ! [D] :
                    ( m1_subset_1(D,u1_struct_0(A))
                   => ( r2_lattice3(A,B,D)
                     => r1_orders_2(A,C,D) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_yellow_0)).

tff(f_110,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B,C] :
          ( r1_tarski(B,C)
         => ! [D] :
              ( m1_subset_1(D,u1_struct_0(A))
             => ( ( r1_lattice3(A,C,D)
                 => r1_lattice3(A,B,D) )
                & ( r2_lattice3(A,C,D)
                 => r2_lattice3(A,B,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_yellow_0)).

tff(c_34,plain,(
    l1_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_40,plain,(
    v1_lattice3('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_42,plain,(
    v5_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_36,plain,(
    v3_lattice3('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_22,plain,(
    ! [A_19,B_21] :
      ( r2_yellow_0(A_19,B_21)
      | ~ l1_orders_2(A_19)
      | ~ v3_lattice3(A_19)
      | ~ v5_orders_2(A_19)
      | v2_struct_0(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_32,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_293,plain,(
    ! [A_135,C_136,B_137] :
      ( r1_orders_2(A_135,k2_yellow_0(A_135,C_136),k2_yellow_0(A_135,B_137))
      | ~ r2_yellow_0(A_135,C_136)
      | ~ r2_yellow_0(A_135,B_137)
      | ~ r1_tarski(B_137,C_136)
      | ~ l1_orders_2(A_135) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_46,plain,(
    v3_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_18,plain,(
    ! [A_17,B_18] :
      ( m1_subset_1(k1_yellow_0(A_17,B_18),u1_struct_0(A_17))
      | ~ l1_orders_2(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_63,plain,(
    ! [A_60,B_61,C_62] :
      ( r3_orders_2(A_60,B_61,C_62)
      | ~ r1_orders_2(A_60,B_61,C_62)
      | ~ m1_subset_1(C_62,u1_struct_0(A_60))
      | ~ m1_subset_1(B_61,u1_struct_0(A_60))
      | ~ l1_orders_2(A_60)
      | ~ v3_orders_2(A_60)
      | v2_struct_0(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_76,plain,(
    ! [A_72,B_73,B_74] :
      ( r3_orders_2(A_72,B_73,k1_yellow_0(A_72,B_74))
      | ~ r1_orders_2(A_72,B_73,k1_yellow_0(A_72,B_74))
      | ~ m1_subset_1(B_73,u1_struct_0(A_72))
      | ~ v3_orders_2(A_72)
      | v2_struct_0(A_72)
      | ~ l1_orders_2(A_72) ) ),
    inference(resolution,[status(thm)],[c_18,c_63])).

tff(c_30,plain,
    ( ~ r1_orders_2('#skF_2',k2_yellow_0('#skF_2','#skF_4'),k2_yellow_0('#skF_2','#skF_3'))
    | ~ r3_orders_2('#skF_2',k1_yellow_0('#skF_2','#skF_3'),k1_yellow_0('#skF_2','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_48,plain,(
    ~ r3_orders_2('#skF_2',k1_yellow_0('#skF_2','#skF_3'),k1_yellow_0('#skF_2','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_81,plain,
    ( ~ r1_orders_2('#skF_2',k1_yellow_0('#skF_2','#skF_3'),k1_yellow_0('#skF_2','#skF_4'))
    | ~ m1_subset_1(k1_yellow_0('#skF_2','#skF_3'),u1_struct_0('#skF_2'))
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l1_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_76,c_48])).

tff(c_85,plain,
    ( ~ r1_orders_2('#skF_2',k1_yellow_0('#skF_2','#skF_3'),k1_yellow_0('#skF_2','#skF_4'))
    | ~ m1_subset_1(k1_yellow_0('#skF_2','#skF_3'),u1_struct_0('#skF_2'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_46,c_81])).

tff(c_86,plain,(
    ~ m1_subset_1(k1_yellow_0('#skF_2','#skF_3'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_85])).

tff(c_90,plain,(
    ~ l1_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_18,c_86])).

tff(c_94,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_90])).

tff(c_96,plain,(
    m1_subset_1(k1_yellow_0('#skF_2','#skF_3'),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_85])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3] :
      ( r3_orders_2(A_1,B_2,C_3)
      | ~ r1_orders_2(A_1,B_2,C_3)
      | ~ m1_subset_1(C_3,u1_struct_0(A_1))
      | ~ m1_subset_1(B_2,u1_struct_0(A_1))
      | ~ l1_orders_2(A_1)
      | ~ v3_orders_2(A_1)
      | v2_struct_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_98,plain,(
    ! [B_2] :
      ( r3_orders_2('#skF_2',B_2,k1_yellow_0('#skF_2','#skF_3'))
      | ~ r1_orders_2('#skF_2',B_2,k1_yellow_0('#skF_2','#skF_3'))
      | ~ m1_subset_1(B_2,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_96,c_2])).

tff(c_101,plain,(
    ! [B_2] :
      ( r3_orders_2('#skF_2',B_2,k1_yellow_0('#skF_2','#skF_3'))
      | ~ r1_orders_2('#skF_2',B_2,k1_yellow_0('#skF_2','#skF_3'))
      | ~ m1_subset_1(B_2,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_34,c_98])).

tff(c_103,plain,(
    v2_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_101])).

tff(c_6,plain,(
    ! [A_4] :
      ( ~ v2_struct_0(A_4)
      | ~ v1_lattice3(A_4)
      | ~ l1_orders_2(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_106,plain,
    ( ~ v1_lattice3('#skF_2')
    | ~ l1_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_103,c_6])).

tff(c_110,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_40,c_106])).

tff(c_112,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_101])).

tff(c_20,plain,(
    ! [A_19,B_21] :
      ( r1_yellow_0(A_19,B_21)
      | ~ l1_orders_2(A_19)
      | ~ v3_lattice3(A_19)
      | ~ v5_orders_2(A_19)
      | v2_struct_0(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_53,plain,(
    ! [A_49,B_50] :
      ( r2_lattice3(A_49,B_50,k1_yellow_0(A_49,B_50))
      | ~ r1_yellow_0(A_49,B_50)
      | ~ m1_subset_1(k1_yellow_0(A_49,B_50),u1_struct_0(A_49))
      | ~ l1_orders_2(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_57,plain,(
    ! [A_51,B_52] :
      ( r2_lattice3(A_51,B_52,k1_yellow_0(A_51,B_52))
      | ~ r1_yellow_0(A_51,B_52)
      | ~ l1_orders_2(A_51) ) ),
    inference(resolution,[status(thm)],[c_18,c_53])).

tff(c_26,plain,(
    ! [A_27,B_32,D_35,C_33] :
      ( r2_lattice3(A_27,B_32,D_35)
      | ~ r2_lattice3(A_27,C_33,D_35)
      | ~ m1_subset_1(D_35,u1_struct_0(A_27))
      | ~ r1_tarski(B_32,C_33)
      | ~ l1_orders_2(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_67,plain,(
    ! [A_63,B_64,B_65] :
      ( r2_lattice3(A_63,B_64,k1_yellow_0(A_63,B_65))
      | ~ m1_subset_1(k1_yellow_0(A_63,B_65),u1_struct_0(A_63))
      | ~ r1_tarski(B_64,B_65)
      | ~ r1_yellow_0(A_63,B_65)
      | ~ l1_orders_2(A_63) ) ),
    inference(resolution,[status(thm)],[c_57,c_26])).

tff(c_70,plain,(
    ! [A_17,B_64,B_18] :
      ( r2_lattice3(A_17,B_64,k1_yellow_0(A_17,B_18))
      | ~ r1_tarski(B_64,B_18)
      | ~ r1_yellow_0(A_17,B_18)
      | ~ l1_orders_2(A_17) ) ),
    inference(resolution,[status(thm)],[c_18,c_67])).

tff(c_71,plain,(
    ! [A_66,B_67,B_68] :
      ( r2_lattice3(A_66,B_67,k1_yellow_0(A_66,B_68))
      | ~ r1_tarski(B_67,B_68)
      | ~ r1_yellow_0(A_66,B_68)
      | ~ l1_orders_2(A_66) ) ),
    inference(resolution,[status(thm)],[c_18,c_67])).

tff(c_120,plain,(
    ! [A_79,B_80,B_81,B_82] :
      ( r2_lattice3(A_79,B_80,k1_yellow_0(A_79,B_81))
      | ~ m1_subset_1(k1_yellow_0(A_79,B_81),u1_struct_0(A_79))
      | ~ r1_tarski(B_80,B_82)
      | ~ r1_tarski(B_82,B_81)
      | ~ r1_yellow_0(A_79,B_81)
      | ~ l1_orders_2(A_79) ) ),
    inference(resolution,[status(thm)],[c_71,c_26])).

tff(c_122,plain,(
    ! [B_80,B_82] :
      ( r2_lattice3('#skF_2',B_80,k1_yellow_0('#skF_2','#skF_3'))
      | ~ r1_tarski(B_80,B_82)
      | ~ r1_tarski(B_82,'#skF_3')
      | ~ r1_yellow_0('#skF_2','#skF_3')
      | ~ l1_orders_2('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_96,c_120])).

tff(c_127,plain,(
    ! [B_80,B_82] :
      ( r2_lattice3('#skF_2',B_80,k1_yellow_0('#skF_2','#skF_3'))
      | ~ r1_tarski(B_80,B_82)
      | ~ r1_tarski(B_82,'#skF_3')
      | ~ r1_yellow_0('#skF_2','#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_122])).

tff(c_133,plain,(
    ~ r1_yellow_0('#skF_2','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_127])).

tff(c_136,plain,
    ( ~ l1_orders_2('#skF_2')
    | ~ v3_lattice3('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_20,c_133])).

tff(c_139,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_36,c_34,c_136])).

tff(c_141,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_112,c_139])).

tff(c_143,plain,(
    r1_yellow_0('#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_127])).

tff(c_175,plain,(
    ! [A_106,B_107,D_108] :
      ( r1_orders_2(A_106,k1_yellow_0(A_106,B_107),D_108)
      | ~ r2_lattice3(A_106,B_107,D_108)
      | ~ m1_subset_1(D_108,u1_struct_0(A_106))
      | ~ r1_yellow_0(A_106,B_107)
      | ~ m1_subset_1(k1_yellow_0(A_106,B_107),u1_struct_0(A_106))
      | ~ l1_orders_2(A_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_177,plain,(
    ! [D_108] :
      ( r1_orders_2('#skF_2',k1_yellow_0('#skF_2','#skF_3'),D_108)
      | ~ r2_lattice3('#skF_2','#skF_3',D_108)
      | ~ m1_subset_1(D_108,u1_struct_0('#skF_2'))
      | ~ r1_yellow_0('#skF_2','#skF_3')
      | ~ l1_orders_2('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_96,c_175])).

tff(c_193,plain,(
    ! [D_113] :
      ( r1_orders_2('#skF_2',k1_yellow_0('#skF_2','#skF_3'),D_113)
      | ~ r2_lattice3('#skF_2','#skF_3',D_113)
      | ~ m1_subset_1(D_113,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_143,c_177])).

tff(c_95,plain,
    ( ~ r1_orders_2('#skF_2',k1_yellow_0('#skF_2','#skF_3'),k1_yellow_0('#skF_2','#skF_4'))
    | v2_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_85])).

tff(c_102,plain,(
    ~ r1_orders_2('#skF_2',k1_yellow_0('#skF_2','#skF_3'),k1_yellow_0('#skF_2','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_95])).

tff(c_204,plain,
    ( ~ r2_lattice3('#skF_2','#skF_3',k1_yellow_0('#skF_2','#skF_4'))
    | ~ m1_subset_1(k1_yellow_0('#skF_2','#skF_4'),u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_193,c_102])).

tff(c_205,plain,(
    ~ m1_subset_1(k1_yellow_0('#skF_2','#skF_4'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_204])).

tff(c_208,plain,(
    ~ l1_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_18,c_205])).

tff(c_212,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_208])).

tff(c_213,plain,(
    ~ r2_lattice3('#skF_2','#skF_3',k1_yellow_0('#skF_2','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_204])).

tff(c_239,plain,
    ( ~ r1_tarski('#skF_3','#skF_4')
    | ~ r1_yellow_0('#skF_2','#skF_4')
    | ~ l1_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_70,c_213])).

tff(c_248,plain,(
    ~ r1_yellow_0('#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_239])).

tff(c_263,plain,
    ( ~ l1_orders_2('#skF_2')
    | ~ v3_lattice3('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_20,c_248])).

tff(c_266,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_36,c_34,c_263])).

tff(c_268,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_112,c_266])).

tff(c_269,plain,(
    v2_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_95])).

tff(c_273,plain,
    ( ~ v1_lattice3('#skF_2')
    | ~ l1_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_269,c_6])).

tff(c_277,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_40,c_273])).

tff(c_278,plain,(
    ~ r1_orders_2('#skF_2',k2_yellow_0('#skF_2','#skF_4'),k2_yellow_0('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_296,plain,
    ( ~ r2_yellow_0('#skF_2','#skF_4')
    | ~ r2_yellow_0('#skF_2','#skF_3')
    | ~ r1_tarski('#skF_3','#skF_4')
    | ~ l1_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_293,c_278])).

tff(c_299,plain,
    ( ~ r2_yellow_0('#skF_2','#skF_4')
    | ~ r2_yellow_0('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_296])).

tff(c_300,plain,(
    ~ r2_yellow_0('#skF_2','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_299])).

tff(c_303,plain,
    ( ~ l1_orders_2('#skF_2')
    | ~ v3_lattice3('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_22,c_300])).

tff(c_306,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_36,c_34,c_303])).

tff(c_309,plain,
    ( ~ v1_lattice3('#skF_2')
    | ~ l1_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_306,c_6])).

tff(c_313,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_40,c_309])).

tff(c_314,plain,(
    ~ r2_yellow_0('#skF_2','#skF_4') ),
    inference(splitRight,[status(thm)],[c_299])).

tff(c_318,plain,
    ( ~ l1_orders_2('#skF_2')
    | ~ v3_lattice3('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_22,c_314])).

tff(c_321,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_36,c_34,c_318])).

tff(c_324,plain,
    ( ~ v1_lattice3('#skF_2')
    | ~ l1_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_321,c_6])).

tff(c_328,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_40,c_324])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 15:52:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.24/1.33  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.68/1.34  
% 2.68/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.68/1.34  %$ r3_orders_2 > r2_lattice3 > r1_orders_2 > r1_lattice3 > r2_yellow_0 > r1_yellow_0 > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v3_lattice3 > v2_struct_0 > v2_lattice3 > v1_lattice3 > l1_orders_2 > k2_yellow_0 > k1_yellow_0 > #nlpp > u1_struct_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 2.68/1.34  
% 2.68/1.34  %Foreground sorts:
% 2.68/1.34  
% 2.68/1.34  
% 2.68/1.34  %Background operators:
% 2.68/1.34  
% 2.68/1.34  
% 2.68/1.34  %Foreground operators:
% 2.68/1.34  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.68/1.34  tff(r3_orders_2, type, r3_orders_2: ($i * $i * $i) > $o).
% 2.68/1.34  tff(k1_yellow_0, type, k1_yellow_0: ($i * $i) > $i).
% 2.68/1.34  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.68/1.34  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 2.68/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.68/1.34  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 2.68/1.34  tff(v3_lattice3, type, v3_lattice3: $i > $o).
% 2.68/1.34  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.68/1.34  tff(r2_lattice3, type, r2_lattice3: ($i * $i * $i) > $o).
% 2.68/1.34  tff(v1_lattice3, type, v1_lattice3: $i > $o).
% 2.68/1.34  tff('#skF_2', type, '#skF_2': $i).
% 2.68/1.34  tff(r2_yellow_0, type, r2_yellow_0: ($i * $i) > $o).
% 2.68/1.34  tff('#skF_3', type, '#skF_3': $i).
% 2.68/1.34  tff(k2_yellow_0, type, k2_yellow_0: ($i * $i) > $i).
% 2.68/1.34  tff(r1_lattice3, type, r1_lattice3: ($i * $i * $i) > $o).
% 2.68/1.34  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.68/1.34  tff(r1_yellow_0, type, r1_yellow_0: ($i * $i) > $o).
% 2.68/1.34  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 2.68/1.34  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.68/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.68/1.34  tff('#skF_4', type, '#skF_4': $i).
% 2.68/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.68/1.34  tff(v2_lattice3, type, v2_lattice3: $i > $o).
% 2.68/1.34  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.68/1.34  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.68/1.34  
% 2.68/1.36  tff(f_132, negated_conjecture, ~(![A]: (((((((v3_orders_2(A) & v4_orders_2(A)) & v5_orders_2(A)) & v1_lattice3(A)) & v2_lattice3(A)) & v3_lattice3(A)) & l1_orders_2(A)) => (![B, C]: (r1_tarski(B, C) => (r3_orders_2(A, k1_yellow_0(A, B), k1_yellow_0(A, C)) & r1_orders_2(A, k2_yellow_0(A, C), k2_yellow_0(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_waybel_7)).
% 2.68/1.36  tff(f_83, axiom, (![A]: ((((~v2_struct_0(A) & v5_orders_2(A)) & v3_lattice3(A)) & l1_orders_2(A)) => (![B]: (r1_yellow_0(A, B) & r2_yellow_0(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_yellow_0)).
% 2.68/1.36  tff(f_94, axiom, (![A]: (l1_orders_2(A) => (![B, C]: (((r1_tarski(B, C) & r2_yellow_0(A, B)) & r2_yellow_0(A, C)) => r1_orders_2(A, k2_yellow_0(A, C), k2_yellow_0(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_yellow_0)).
% 2.68/1.36  tff(f_69, axiom, (![A, B]: (l1_orders_2(A) => m1_subset_1(k1_yellow_0(A, B), u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_yellow_0)).
% 2.68/1.36  tff(f_40, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v3_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (r3_orders_2(A, B, C) <=> r1_orders_2(A, B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r3_orders_2)).
% 2.68/1.36  tff(f_47, axiom, (![A]: (l1_orders_2(A) => (v1_lattice3(A) => ~v2_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_lattice3)).
% 2.68/1.36  tff(f_65, axiom, (![A]: (l1_orders_2(A) => (![B, C]: (m1_subset_1(C, u1_struct_0(A)) => (r1_yellow_0(A, B) => ((C = k1_yellow_0(A, B)) <=> (r2_lattice3(A, B, C) & (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_lattice3(A, B, D) => r1_orders_2(A, C, D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_yellow_0)).
% 2.68/1.36  tff(f_110, axiom, (![A]: (l1_orders_2(A) => (![B, C]: (r1_tarski(B, C) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => ((r1_lattice3(A, C, D) => r1_lattice3(A, B, D)) & (r2_lattice3(A, C, D) => r2_lattice3(A, B, D))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_yellow_0)).
% 2.68/1.36  tff(c_34, plain, (l1_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_132])).
% 2.68/1.36  tff(c_40, plain, (v1_lattice3('#skF_2')), inference(cnfTransformation, [status(thm)], [f_132])).
% 2.68/1.36  tff(c_42, plain, (v5_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_132])).
% 2.68/1.36  tff(c_36, plain, (v3_lattice3('#skF_2')), inference(cnfTransformation, [status(thm)], [f_132])).
% 2.68/1.36  tff(c_22, plain, (![A_19, B_21]: (r2_yellow_0(A_19, B_21) | ~l1_orders_2(A_19) | ~v3_lattice3(A_19) | ~v5_orders_2(A_19) | v2_struct_0(A_19))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.68/1.36  tff(c_32, plain, (r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_132])).
% 2.68/1.36  tff(c_293, plain, (![A_135, C_136, B_137]: (r1_orders_2(A_135, k2_yellow_0(A_135, C_136), k2_yellow_0(A_135, B_137)) | ~r2_yellow_0(A_135, C_136) | ~r2_yellow_0(A_135, B_137) | ~r1_tarski(B_137, C_136) | ~l1_orders_2(A_135))), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.68/1.36  tff(c_46, plain, (v3_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_132])).
% 2.68/1.36  tff(c_18, plain, (![A_17, B_18]: (m1_subset_1(k1_yellow_0(A_17, B_18), u1_struct_0(A_17)) | ~l1_orders_2(A_17))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.68/1.36  tff(c_63, plain, (![A_60, B_61, C_62]: (r3_orders_2(A_60, B_61, C_62) | ~r1_orders_2(A_60, B_61, C_62) | ~m1_subset_1(C_62, u1_struct_0(A_60)) | ~m1_subset_1(B_61, u1_struct_0(A_60)) | ~l1_orders_2(A_60) | ~v3_orders_2(A_60) | v2_struct_0(A_60))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.68/1.36  tff(c_76, plain, (![A_72, B_73, B_74]: (r3_orders_2(A_72, B_73, k1_yellow_0(A_72, B_74)) | ~r1_orders_2(A_72, B_73, k1_yellow_0(A_72, B_74)) | ~m1_subset_1(B_73, u1_struct_0(A_72)) | ~v3_orders_2(A_72) | v2_struct_0(A_72) | ~l1_orders_2(A_72))), inference(resolution, [status(thm)], [c_18, c_63])).
% 2.68/1.36  tff(c_30, plain, (~r1_orders_2('#skF_2', k2_yellow_0('#skF_2', '#skF_4'), k2_yellow_0('#skF_2', '#skF_3')) | ~r3_orders_2('#skF_2', k1_yellow_0('#skF_2', '#skF_3'), k1_yellow_0('#skF_2', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_132])).
% 2.68/1.36  tff(c_48, plain, (~r3_orders_2('#skF_2', k1_yellow_0('#skF_2', '#skF_3'), k1_yellow_0('#skF_2', '#skF_4'))), inference(splitLeft, [status(thm)], [c_30])).
% 2.68/1.36  tff(c_81, plain, (~r1_orders_2('#skF_2', k1_yellow_0('#skF_2', '#skF_3'), k1_yellow_0('#skF_2', '#skF_4')) | ~m1_subset_1(k1_yellow_0('#skF_2', '#skF_3'), u1_struct_0('#skF_2')) | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | ~l1_orders_2('#skF_2')), inference(resolution, [status(thm)], [c_76, c_48])).
% 2.68/1.36  tff(c_85, plain, (~r1_orders_2('#skF_2', k1_yellow_0('#skF_2', '#skF_3'), k1_yellow_0('#skF_2', '#skF_4')) | ~m1_subset_1(k1_yellow_0('#skF_2', '#skF_3'), u1_struct_0('#skF_2')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_46, c_81])).
% 2.68/1.36  tff(c_86, plain, (~m1_subset_1(k1_yellow_0('#skF_2', '#skF_3'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_85])).
% 2.68/1.36  tff(c_90, plain, (~l1_orders_2('#skF_2')), inference(resolution, [status(thm)], [c_18, c_86])).
% 2.68/1.36  tff(c_94, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_90])).
% 2.68/1.36  tff(c_96, plain, (m1_subset_1(k1_yellow_0('#skF_2', '#skF_3'), u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_85])).
% 2.68/1.36  tff(c_2, plain, (![A_1, B_2, C_3]: (r3_orders_2(A_1, B_2, C_3) | ~r1_orders_2(A_1, B_2, C_3) | ~m1_subset_1(C_3, u1_struct_0(A_1)) | ~m1_subset_1(B_2, u1_struct_0(A_1)) | ~l1_orders_2(A_1) | ~v3_orders_2(A_1) | v2_struct_0(A_1))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.68/1.36  tff(c_98, plain, (![B_2]: (r3_orders_2('#skF_2', B_2, k1_yellow_0('#skF_2', '#skF_3')) | ~r1_orders_2('#skF_2', B_2, k1_yellow_0('#skF_2', '#skF_3')) | ~m1_subset_1(B_2, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_96, c_2])).
% 2.68/1.36  tff(c_101, plain, (![B_2]: (r3_orders_2('#skF_2', B_2, k1_yellow_0('#skF_2', '#skF_3')) | ~r1_orders_2('#skF_2', B_2, k1_yellow_0('#skF_2', '#skF_3')) | ~m1_subset_1(B_2, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_34, c_98])).
% 2.68/1.36  tff(c_103, plain, (v2_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_101])).
% 2.68/1.36  tff(c_6, plain, (![A_4]: (~v2_struct_0(A_4) | ~v1_lattice3(A_4) | ~l1_orders_2(A_4))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.68/1.36  tff(c_106, plain, (~v1_lattice3('#skF_2') | ~l1_orders_2('#skF_2')), inference(resolution, [status(thm)], [c_103, c_6])).
% 2.68/1.36  tff(c_110, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_40, c_106])).
% 2.68/1.36  tff(c_112, plain, (~v2_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_101])).
% 2.68/1.36  tff(c_20, plain, (![A_19, B_21]: (r1_yellow_0(A_19, B_21) | ~l1_orders_2(A_19) | ~v3_lattice3(A_19) | ~v5_orders_2(A_19) | v2_struct_0(A_19))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.68/1.36  tff(c_53, plain, (![A_49, B_50]: (r2_lattice3(A_49, B_50, k1_yellow_0(A_49, B_50)) | ~r1_yellow_0(A_49, B_50) | ~m1_subset_1(k1_yellow_0(A_49, B_50), u1_struct_0(A_49)) | ~l1_orders_2(A_49))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.68/1.36  tff(c_57, plain, (![A_51, B_52]: (r2_lattice3(A_51, B_52, k1_yellow_0(A_51, B_52)) | ~r1_yellow_0(A_51, B_52) | ~l1_orders_2(A_51))), inference(resolution, [status(thm)], [c_18, c_53])).
% 2.68/1.36  tff(c_26, plain, (![A_27, B_32, D_35, C_33]: (r2_lattice3(A_27, B_32, D_35) | ~r2_lattice3(A_27, C_33, D_35) | ~m1_subset_1(D_35, u1_struct_0(A_27)) | ~r1_tarski(B_32, C_33) | ~l1_orders_2(A_27))), inference(cnfTransformation, [status(thm)], [f_110])).
% 2.68/1.36  tff(c_67, plain, (![A_63, B_64, B_65]: (r2_lattice3(A_63, B_64, k1_yellow_0(A_63, B_65)) | ~m1_subset_1(k1_yellow_0(A_63, B_65), u1_struct_0(A_63)) | ~r1_tarski(B_64, B_65) | ~r1_yellow_0(A_63, B_65) | ~l1_orders_2(A_63))), inference(resolution, [status(thm)], [c_57, c_26])).
% 2.68/1.36  tff(c_70, plain, (![A_17, B_64, B_18]: (r2_lattice3(A_17, B_64, k1_yellow_0(A_17, B_18)) | ~r1_tarski(B_64, B_18) | ~r1_yellow_0(A_17, B_18) | ~l1_orders_2(A_17))), inference(resolution, [status(thm)], [c_18, c_67])).
% 2.68/1.36  tff(c_71, plain, (![A_66, B_67, B_68]: (r2_lattice3(A_66, B_67, k1_yellow_0(A_66, B_68)) | ~r1_tarski(B_67, B_68) | ~r1_yellow_0(A_66, B_68) | ~l1_orders_2(A_66))), inference(resolution, [status(thm)], [c_18, c_67])).
% 2.68/1.36  tff(c_120, plain, (![A_79, B_80, B_81, B_82]: (r2_lattice3(A_79, B_80, k1_yellow_0(A_79, B_81)) | ~m1_subset_1(k1_yellow_0(A_79, B_81), u1_struct_0(A_79)) | ~r1_tarski(B_80, B_82) | ~r1_tarski(B_82, B_81) | ~r1_yellow_0(A_79, B_81) | ~l1_orders_2(A_79))), inference(resolution, [status(thm)], [c_71, c_26])).
% 2.68/1.36  tff(c_122, plain, (![B_80, B_82]: (r2_lattice3('#skF_2', B_80, k1_yellow_0('#skF_2', '#skF_3')) | ~r1_tarski(B_80, B_82) | ~r1_tarski(B_82, '#skF_3') | ~r1_yellow_0('#skF_2', '#skF_3') | ~l1_orders_2('#skF_2'))), inference(resolution, [status(thm)], [c_96, c_120])).
% 2.68/1.36  tff(c_127, plain, (![B_80, B_82]: (r2_lattice3('#skF_2', B_80, k1_yellow_0('#skF_2', '#skF_3')) | ~r1_tarski(B_80, B_82) | ~r1_tarski(B_82, '#skF_3') | ~r1_yellow_0('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_122])).
% 2.68/1.36  tff(c_133, plain, (~r1_yellow_0('#skF_2', '#skF_3')), inference(splitLeft, [status(thm)], [c_127])).
% 2.68/1.36  tff(c_136, plain, (~l1_orders_2('#skF_2') | ~v3_lattice3('#skF_2') | ~v5_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_20, c_133])).
% 2.68/1.36  tff(c_139, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_36, c_34, c_136])).
% 2.68/1.36  tff(c_141, plain, $false, inference(negUnitSimplification, [status(thm)], [c_112, c_139])).
% 2.68/1.36  tff(c_143, plain, (r1_yellow_0('#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_127])).
% 2.68/1.36  tff(c_175, plain, (![A_106, B_107, D_108]: (r1_orders_2(A_106, k1_yellow_0(A_106, B_107), D_108) | ~r2_lattice3(A_106, B_107, D_108) | ~m1_subset_1(D_108, u1_struct_0(A_106)) | ~r1_yellow_0(A_106, B_107) | ~m1_subset_1(k1_yellow_0(A_106, B_107), u1_struct_0(A_106)) | ~l1_orders_2(A_106))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.68/1.36  tff(c_177, plain, (![D_108]: (r1_orders_2('#skF_2', k1_yellow_0('#skF_2', '#skF_3'), D_108) | ~r2_lattice3('#skF_2', '#skF_3', D_108) | ~m1_subset_1(D_108, u1_struct_0('#skF_2')) | ~r1_yellow_0('#skF_2', '#skF_3') | ~l1_orders_2('#skF_2'))), inference(resolution, [status(thm)], [c_96, c_175])).
% 2.68/1.36  tff(c_193, plain, (![D_113]: (r1_orders_2('#skF_2', k1_yellow_0('#skF_2', '#skF_3'), D_113) | ~r2_lattice3('#skF_2', '#skF_3', D_113) | ~m1_subset_1(D_113, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_143, c_177])).
% 2.68/1.36  tff(c_95, plain, (~r1_orders_2('#skF_2', k1_yellow_0('#skF_2', '#skF_3'), k1_yellow_0('#skF_2', '#skF_4')) | v2_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_85])).
% 2.68/1.36  tff(c_102, plain, (~r1_orders_2('#skF_2', k1_yellow_0('#skF_2', '#skF_3'), k1_yellow_0('#skF_2', '#skF_4'))), inference(splitLeft, [status(thm)], [c_95])).
% 2.68/1.36  tff(c_204, plain, (~r2_lattice3('#skF_2', '#skF_3', k1_yellow_0('#skF_2', '#skF_4')) | ~m1_subset_1(k1_yellow_0('#skF_2', '#skF_4'), u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_193, c_102])).
% 2.68/1.36  tff(c_205, plain, (~m1_subset_1(k1_yellow_0('#skF_2', '#skF_4'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_204])).
% 2.68/1.36  tff(c_208, plain, (~l1_orders_2('#skF_2')), inference(resolution, [status(thm)], [c_18, c_205])).
% 2.68/1.36  tff(c_212, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_208])).
% 2.68/1.36  tff(c_213, plain, (~r2_lattice3('#skF_2', '#skF_3', k1_yellow_0('#skF_2', '#skF_4'))), inference(splitRight, [status(thm)], [c_204])).
% 2.68/1.36  tff(c_239, plain, (~r1_tarski('#skF_3', '#skF_4') | ~r1_yellow_0('#skF_2', '#skF_4') | ~l1_orders_2('#skF_2')), inference(resolution, [status(thm)], [c_70, c_213])).
% 2.68/1.36  tff(c_248, plain, (~r1_yellow_0('#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_239])).
% 2.68/1.36  tff(c_263, plain, (~l1_orders_2('#skF_2') | ~v3_lattice3('#skF_2') | ~v5_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_20, c_248])).
% 2.68/1.36  tff(c_266, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_36, c_34, c_263])).
% 2.68/1.36  tff(c_268, plain, $false, inference(negUnitSimplification, [status(thm)], [c_112, c_266])).
% 2.68/1.36  tff(c_269, plain, (v2_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_95])).
% 2.68/1.36  tff(c_273, plain, (~v1_lattice3('#skF_2') | ~l1_orders_2('#skF_2')), inference(resolution, [status(thm)], [c_269, c_6])).
% 2.68/1.36  tff(c_277, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_40, c_273])).
% 2.68/1.36  tff(c_278, plain, (~r1_orders_2('#skF_2', k2_yellow_0('#skF_2', '#skF_4'), k2_yellow_0('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_30])).
% 2.68/1.36  tff(c_296, plain, (~r2_yellow_0('#skF_2', '#skF_4') | ~r2_yellow_0('#skF_2', '#skF_3') | ~r1_tarski('#skF_3', '#skF_4') | ~l1_orders_2('#skF_2')), inference(resolution, [status(thm)], [c_293, c_278])).
% 2.68/1.36  tff(c_299, plain, (~r2_yellow_0('#skF_2', '#skF_4') | ~r2_yellow_0('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_296])).
% 2.68/1.36  tff(c_300, plain, (~r2_yellow_0('#skF_2', '#skF_3')), inference(splitLeft, [status(thm)], [c_299])).
% 2.68/1.36  tff(c_303, plain, (~l1_orders_2('#skF_2') | ~v3_lattice3('#skF_2') | ~v5_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_22, c_300])).
% 2.68/1.36  tff(c_306, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_36, c_34, c_303])).
% 2.68/1.36  tff(c_309, plain, (~v1_lattice3('#skF_2') | ~l1_orders_2('#skF_2')), inference(resolution, [status(thm)], [c_306, c_6])).
% 2.68/1.36  tff(c_313, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_40, c_309])).
% 2.68/1.36  tff(c_314, plain, (~r2_yellow_0('#skF_2', '#skF_4')), inference(splitRight, [status(thm)], [c_299])).
% 2.68/1.36  tff(c_318, plain, (~l1_orders_2('#skF_2') | ~v3_lattice3('#skF_2') | ~v5_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_22, c_314])).
% 2.68/1.36  tff(c_321, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_36, c_34, c_318])).
% 2.68/1.36  tff(c_324, plain, (~v1_lattice3('#skF_2') | ~l1_orders_2('#skF_2')), inference(resolution, [status(thm)], [c_321, c_6])).
% 2.68/1.36  tff(c_328, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_40, c_324])).
% 2.68/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.68/1.36  
% 2.68/1.36  Inference rules
% 2.68/1.36  ----------------------
% 2.68/1.36  #Ref     : 0
% 2.68/1.36  #Sup     : 46
% 2.68/1.36  #Fact    : 0
% 2.68/1.36  #Define  : 0
% 2.68/1.36  #Split   : 8
% 2.68/1.36  #Chain   : 0
% 2.68/1.36  #Close   : 0
% 2.68/1.36  
% 2.68/1.36  Ordering : KBO
% 2.68/1.36  
% 2.68/1.36  Simplification rules
% 2.68/1.36  ----------------------
% 2.68/1.36  #Subsume      : 9
% 2.68/1.36  #Demod        : 51
% 2.68/1.36  #Tautology    : 2
% 2.68/1.36  #SimpNegUnit  : 4
% 2.68/1.36  #BackRed      : 0
% 2.68/1.36  
% 2.68/1.36  #Partial instantiations: 0
% 2.68/1.36  #Strategies tried      : 1
% 2.68/1.36  
% 2.68/1.36  Timing (in seconds)
% 2.68/1.36  ----------------------
% 2.68/1.36  Preprocessing        : 0.31
% 2.68/1.36  Parsing              : 0.18
% 2.68/1.36  CNF conversion       : 0.02
% 2.68/1.36  Main loop            : 0.27
% 2.68/1.36  Inferencing          : 0.11
% 2.68/1.36  Reduction            : 0.07
% 2.68/1.36  Demodulation         : 0.05
% 2.68/1.36  BG Simplification    : 0.02
% 2.68/1.36  Subsumption          : 0.05
% 2.68/1.36  Abstraction          : 0.01
% 2.68/1.37  MUC search           : 0.00
% 2.68/1.37  Cooper               : 0.00
% 2.68/1.37  Total                : 0.62
% 2.68/1.37  Index Insertion      : 0.00
% 2.68/1.37  Index Deletion       : 0.00
% 2.68/1.37  Index Matching       : 0.00
% 2.68/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
