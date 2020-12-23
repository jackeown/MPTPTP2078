%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:55 EST 2020

% Result     : Theorem 2.89s
% Output     : CNFRefutation 3.43s
% Verified   : 
% Statistics : Number of formulae       :  137 ( 550 expanded)
%              Number of leaves         :   36 ( 197 expanded)
%              Depth                    :   16
%              Number of atoms          :  313 (2289 expanded)
%              Number of equality atoms :    2 (  10 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_orders_2 > r2_lattice3 > r1_orders_2 > r1_lattice3 > r2_yellow_0 > r1_yellow_0 > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v3_lattice3 > v2_struct_0 > v2_lattice3 > v1_lattice3 > l1_orders_2 > k2_yellow_0 > k1_yellow_0 > #nlpp > u1_struct_0 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4

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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r2_yellow_0,type,(
    r2_yellow_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k2_yellow_0,type,(
    k2_yellow_0: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

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

tff(f_143,negated_conjecture,(
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

tff(f_91,axiom,(
    ! [A,B] :
      ( l1_orders_2(A)
     => m1_subset_1(k2_yellow_0(A,B),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_yellow_0)).

tff(f_87,axiom,(
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

tff(f_105,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v5_orders_2(A)
        & v3_lattice3(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( r1_yellow_0(A,B)
          & r2_yellow_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_yellow_0)).

tff(f_83,axiom,(
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

tff(f_121,axiom,(
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

tff(f_65,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B,C] :
          ( m1_subset_1(C,u1_struct_0(A))
         => ( r2_yellow_0(A,B)
           => ( C = k2_yellow_0(A,B)
            <=> ( r1_lattice3(A,B,C)
                & ! [D] :
                    ( m1_subset_1(D,u1_struct_0(A))
                   => ( r1_lattice3(A,B,D)
                     => r1_orders_2(A,D,C) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_yellow_0)).

tff(c_44,plain,(
    l1_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_30,plain,(
    ! [A_31,B_32] :
      ( m1_subset_1(k2_yellow_0(A_31,B_32),u1_struct_0(A_31))
      | ~ l1_orders_2(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_50,plain,(
    v1_lattice3('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_28,plain,(
    ! [A_29,B_30] :
      ( m1_subset_1(k1_yellow_0(A_29,B_30),u1_struct_0(A_29))
      | ~ l1_orders_2(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_56,plain,(
    v3_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_98,plain,(
    ! [A_87,B_88,C_89] :
      ( r3_orders_2(A_87,B_88,C_89)
      | ~ r1_orders_2(A_87,B_88,C_89)
      | ~ m1_subset_1(C_89,u1_struct_0(A_87))
      | ~ m1_subset_1(B_88,u1_struct_0(A_87))
      | ~ l1_orders_2(A_87)
      | ~ v3_orders_2(A_87)
      | v2_struct_0(A_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_105,plain,(
    ! [A_90,B_91,B_92] :
      ( r3_orders_2(A_90,B_91,k1_yellow_0(A_90,B_92))
      | ~ r1_orders_2(A_90,B_91,k1_yellow_0(A_90,B_92))
      | ~ m1_subset_1(B_91,u1_struct_0(A_90))
      | ~ v3_orders_2(A_90)
      | v2_struct_0(A_90)
      | ~ l1_orders_2(A_90) ) ),
    inference(resolution,[status(thm)],[c_28,c_98])).

tff(c_40,plain,
    ( ~ r1_orders_2('#skF_3',k2_yellow_0('#skF_3','#skF_5'),k2_yellow_0('#skF_3','#skF_4'))
    | ~ r3_orders_2('#skF_3',k1_yellow_0('#skF_3','#skF_4'),k1_yellow_0('#skF_3','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_58,plain,(
    ~ r3_orders_2('#skF_3',k1_yellow_0('#skF_3','#skF_4'),k1_yellow_0('#skF_3','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_110,plain,
    ( ~ r1_orders_2('#skF_3',k1_yellow_0('#skF_3','#skF_4'),k1_yellow_0('#skF_3','#skF_5'))
    | ~ m1_subset_1(k1_yellow_0('#skF_3','#skF_4'),u1_struct_0('#skF_3'))
    | ~ v3_orders_2('#skF_3')
    | v2_struct_0('#skF_3')
    | ~ l1_orders_2('#skF_3') ),
    inference(resolution,[status(thm)],[c_105,c_58])).

tff(c_114,plain,
    ( ~ r1_orders_2('#skF_3',k1_yellow_0('#skF_3','#skF_4'),k1_yellow_0('#skF_3','#skF_5'))
    | ~ m1_subset_1(k1_yellow_0('#skF_3','#skF_4'),u1_struct_0('#skF_3'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_56,c_110])).

tff(c_115,plain,(
    ~ m1_subset_1(k1_yellow_0('#skF_3','#skF_4'),u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_114])).

tff(c_118,plain,(
    ~ l1_orders_2('#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_115])).

tff(c_122,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_118])).

tff(c_124,plain,(
    m1_subset_1(k1_yellow_0('#skF_3','#skF_4'),u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_114])).

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

tff(c_126,plain,(
    ! [B_2] :
      ( r3_orders_2('#skF_3',B_2,k1_yellow_0('#skF_3','#skF_4'))
      | ~ r1_orders_2('#skF_3',B_2,k1_yellow_0('#skF_3','#skF_4'))
      | ~ m1_subset_1(B_2,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | ~ v3_orders_2('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_124,c_2])).

tff(c_129,plain,(
    ! [B_2] :
      ( r3_orders_2('#skF_3',B_2,k1_yellow_0('#skF_3','#skF_4'))
      | ~ r1_orders_2('#skF_3',B_2,k1_yellow_0('#skF_3','#skF_4'))
      | ~ m1_subset_1(B_2,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_44,c_126])).

tff(c_131,plain,(
    v2_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_129])).

tff(c_6,plain,(
    ! [A_4] :
      ( ~ v2_struct_0(A_4)
      | ~ v1_lattice3(A_4)
      | ~ l1_orders_2(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_134,plain,
    ( ~ v1_lattice3('#skF_3')
    | ~ l1_orders_2('#skF_3') ),
    inference(resolution,[status(thm)],[c_131,c_6])).

tff(c_138,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_50,c_134])).

tff(c_140,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_129])).

tff(c_52,plain,(
    v5_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_46,plain,(
    v3_lattice3('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_32,plain,(
    ! [A_33,B_35] :
      ( r1_yellow_0(A_33,B_35)
      | ~ l1_orders_2(A_33)
      | ~ v3_lattice3(A_33)
      | ~ v5_orders_2(A_33)
      | v2_struct_0(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_42,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_63,plain,(
    ! [A_56,B_57] :
      ( r2_lattice3(A_56,B_57,k1_yellow_0(A_56,B_57))
      | ~ r1_yellow_0(A_56,B_57)
      | ~ m1_subset_1(k1_yellow_0(A_56,B_57),u1_struct_0(A_56))
      | ~ l1_orders_2(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_66,plain,(
    ! [A_29,B_30] :
      ( r2_lattice3(A_29,B_30,k1_yellow_0(A_29,B_30))
      | ~ r1_yellow_0(A_29,B_30)
      | ~ l1_orders_2(A_29) ) ),
    inference(resolution,[status(thm)],[c_28,c_63])).

tff(c_73,plain,(
    ! [A_66,B_67,D_68,C_69] :
      ( r2_lattice3(A_66,B_67,D_68)
      | ~ r2_lattice3(A_66,C_69,D_68)
      | ~ m1_subset_1(D_68,u1_struct_0(A_66))
      | ~ r1_tarski(B_67,C_69)
      | ~ l1_orders_2(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_81,plain,(
    ! [A_72,B_73,B_74] :
      ( r2_lattice3(A_72,B_73,k1_yellow_0(A_72,B_74))
      | ~ m1_subset_1(k1_yellow_0(A_72,B_74),u1_struct_0(A_72))
      | ~ r1_tarski(B_73,B_74)
      | ~ r1_yellow_0(A_72,B_74)
      | ~ l1_orders_2(A_72) ) ),
    inference(resolution,[status(thm)],[c_66,c_73])).

tff(c_84,plain,(
    ! [A_29,B_73,B_30] :
      ( r2_lattice3(A_29,B_73,k1_yellow_0(A_29,B_30))
      | ~ r1_tarski(B_73,B_30)
      | ~ r1_yellow_0(A_29,B_30)
      | ~ l1_orders_2(A_29) ) ),
    inference(resolution,[status(thm)],[c_28,c_81])).

tff(c_85,plain,(
    ! [A_75,B_76,B_77] :
      ( r2_lattice3(A_75,B_76,k1_yellow_0(A_75,B_77))
      | ~ r1_tarski(B_76,B_77)
      | ~ r1_yellow_0(A_75,B_77)
      | ~ l1_orders_2(A_75) ) ),
    inference(resolution,[status(thm)],[c_28,c_81])).

tff(c_36,plain,(
    ! [A_36,B_41,D_44,C_42] :
      ( r2_lattice3(A_36,B_41,D_44)
      | ~ r2_lattice3(A_36,C_42,D_44)
      | ~ m1_subset_1(D_44,u1_struct_0(A_36))
      | ~ r1_tarski(B_41,C_42)
      | ~ l1_orders_2(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_169,plain,(
    ! [A_113,B_114,B_115,B_116] :
      ( r2_lattice3(A_113,B_114,k1_yellow_0(A_113,B_115))
      | ~ m1_subset_1(k1_yellow_0(A_113,B_115),u1_struct_0(A_113))
      | ~ r1_tarski(B_114,B_116)
      | ~ r1_tarski(B_116,B_115)
      | ~ r1_yellow_0(A_113,B_115)
      | ~ l1_orders_2(A_113) ) ),
    inference(resolution,[status(thm)],[c_85,c_36])).

tff(c_171,plain,(
    ! [B_114,B_116] :
      ( r2_lattice3('#skF_3',B_114,k1_yellow_0('#skF_3','#skF_4'))
      | ~ r1_tarski(B_114,B_116)
      | ~ r1_tarski(B_116,'#skF_4')
      | ~ r1_yellow_0('#skF_3','#skF_4')
      | ~ l1_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_124,c_169])).

tff(c_176,plain,(
    ! [B_114,B_116] :
      ( r2_lattice3('#skF_3',B_114,k1_yellow_0('#skF_3','#skF_4'))
      | ~ r1_tarski(B_114,B_116)
      | ~ r1_tarski(B_116,'#skF_4')
      | ~ r1_yellow_0('#skF_3','#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_171])).

tff(c_178,plain,(
    ~ r1_yellow_0('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_176])).

tff(c_185,plain,
    ( ~ l1_orders_2('#skF_3')
    | ~ v3_lattice3('#skF_3')
    | ~ v5_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_178])).

tff(c_188,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_46,c_44,c_185])).

tff(c_190,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_140,c_188])).

tff(c_192,plain,(
    r1_yellow_0('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_176])).

tff(c_263,plain,(
    ! [A_166,B_167,D_168] :
      ( r1_orders_2(A_166,k1_yellow_0(A_166,B_167),D_168)
      | ~ r2_lattice3(A_166,B_167,D_168)
      | ~ m1_subset_1(D_168,u1_struct_0(A_166))
      | ~ r1_yellow_0(A_166,B_167)
      | ~ m1_subset_1(k1_yellow_0(A_166,B_167),u1_struct_0(A_166))
      | ~ l1_orders_2(A_166) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_265,plain,(
    ! [D_168] :
      ( r1_orders_2('#skF_3',k1_yellow_0('#skF_3','#skF_4'),D_168)
      | ~ r2_lattice3('#skF_3','#skF_4',D_168)
      | ~ m1_subset_1(D_168,u1_struct_0('#skF_3'))
      | ~ r1_yellow_0('#skF_3','#skF_4')
      | ~ l1_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_124,c_263])).

tff(c_272,plain,(
    ! [D_169] :
      ( r1_orders_2('#skF_3',k1_yellow_0('#skF_3','#skF_4'),D_169)
      | ~ r2_lattice3('#skF_3','#skF_4',D_169)
      | ~ m1_subset_1(D_169,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_192,c_265])).

tff(c_123,plain,
    ( ~ r1_orders_2('#skF_3',k1_yellow_0('#skF_3','#skF_4'),k1_yellow_0('#skF_3','#skF_5'))
    | v2_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_114])).

tff(c_130,plain,(
    ~ r1_orders_2('#skF_3',k1_yellow_0('#skF_3','#skF_4'),k1_yellow_0('#skF_3','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_123])).

tff(c_283,plain,
    ( ~ r2_lattice3('#skF_3','#skF_4',k1_yellow_0('#skF_3','#skF_5'))
    | ~ m1_subset_1(k1_yellow_0('#skF_3','#skF_5'),u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_272,c_130])).

tff(c_284,plain,(
    ~ m1_subset_1(k1_yellow_0('#skF_3','#skF_5'),u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_283])).

tff(c_287,plain,(
    ~ l1_orders_2('#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_284])).

tff(c_291,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_287])).

tff(c_292,plain,(
    ~ r2_lattice3('#skF_3','#skF_4',k1_yellow_0('#skF_3','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_283])).

tff(c_317,plain,
    ( ~ r1_tarski('#skF_4','#skF_5')
    | ~ r1_yellow_0('#skF_3','#skF_5')
    | ~ l1_orders_2('#skF_3') ),
    inference(resolution,[status(thm)],[c_84,c_292])).

tff(c_326,plain,(
    ~ r1_yellow_0('#skF_3','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_317])).

tff(c_329,plain,
    ( ~ l1_orders_2('#skF_3')
    | ~ v3_lattice3('#skF_3')
    | ~ v5_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_326])).

tff(c_332,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_46,c_44,c_329])).

tff(c_334,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_140,c_332])).

tff(c_335,plain,(
    v2_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_123])).

tff(c_339,plain,
    ( ~ v1_lattice3('#skF_3')
    | ~ l1_orders_2('#skF_3') ),
    inference(resolution,[status(thm)],[c_335,c_6])).

tff(c_343,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_50,c_339])).

tff(c_345,plain,(
    r3_orders_2('#skF_3',k1_yellow_0('#skF_3','#skF_4'),k1_yellow_0('#skF_3','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_383,plain,(
    ! [A_207,B_208,C_209] :
      ( r1_orders_2(A_207,B_208,C_209)
      | ~ r3_orders_2(A_207,B_208,C_209)
      | ~ m1_subset_1(C_209,u1_struct_0(A_207))
      | ~ m1_subset_1(B_208,u1_struct_0(A_207))
      | ~ l1_orders_2(A_207)
      | ~ v3_orders_2(A_207)
      | v2_struct_0(A_207) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_385,plain,
    ( r1_orders_2('#skF_3',k1_yellow_0('#skF_3','#skF_4'),k1_yellow_0('#skF_3','#skF_5'))
    | ~ m1_subset_1(k1_yellow_0('#skF_3','#skF_5'),u1_struct_0('#skF_3'))
    | ~ m1_subset_1(k1_yellow_0('#skF_3','#skF_4'),u1_struct_0('#skF_3'))
    | ~ l1_orders_2('#skF_3')
    | ~ v3_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_345,c_383])).

tff(c_388,plain,
    ( r1_orders_2('#skF_3',k1_yellow_0('#skF_3','#skF_4'),k1_yellow_0('#skF_3','#skF_5'))
    | ~ m1_subset_1(k1_yellow_0('#skF_3','#skF_5'),u1_struct_0('#skF_3'))
    | ~ m1_subset_1(k1_yellow_0('#skF_3','#skF_4'),u1_struct_0('#skF_3'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_44,c_385])).

tff(c_397,plain,(
    ~ m1_subset_1(k1_yellow_0('#skF_3','#skF_4'),u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_388])).

tff(c_400,plain,(
    ~ l1_orders_2('#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_397])).

tff(c_404,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_400])).

tff(c_405,plain,
    ( ~ m1_subset_1(k1_yellow_0('#skF_3','#skF_5'),u1_struct_0('#skF_3'))
    | v2_struct_0('#skF_3')
    | r1_orders_2('#skF_3',k1_yellow_0('#skF_3','#skF_4'),k1_yellow_0('#skF_3','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_388])).

tff(c_416,plain,(
    ~ m1_subset_1(k1_yellow_0('#skF_3','#skF_5'),u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_405])).

tff(c_419,plain,(
    ~ l1_orders_2('#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_416])).

tff(c_423,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_419])).

tff(c_424,plain,
    ( r1_orders_2('#skF_3',k1_yellow_0('#skF_3','#skF_4'),k1_yellow_0('#skF_3','#skF_5'))
    | v2_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_405])).

tff(c_431,plain,(
    v2_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_424])).

tff(c_434,plain,
    ( ~ v1_lattice3('#skF_3')
    | ~ l1_orders_2('#skF_3') ),
    inference(resolution,[status(thm)],[c_431,c_6])).

tff(c_438,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_50,c_434])).

tff(c_440,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_424])).

tff(c_34,plain,(
    ! [A_33,B_35] :
      ( r2_yellow_0(A_33,B_35)
      | ~ l1_orders_2(A_33)
      | ~ v3_lattice3(A_33)
      | ~ v5_orders_2(A_33)
      | v2_struct_0(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_351,plain,(
    ! [A_186,B_187] :
      ( r1_lattice3(A_186,B_187,k2_yellow_0(A_186,B_187))
      | ~ r2_yellow_0(A_186,B_187)
      | ~ m1_subset_1(k2_yellow_0(A_186,B_187),u1_struct_0(A_186))
      | ~ l1_orders_2(A_186) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_354,plain,(
    ! [A_31,B_32] :
      ( r1_lattice3(A_31,B_32,k2_yellow_0(A_31,B_32))
      | ~ r2_yellow_0(A_31,B_32)
      | ~ l1_orders_2(A_31) ) ),
    inference(resolution,[status(thm)],[c_30,c_351])).

tff(c_356,plain,(
    ! [A_190,B_191,D_192,C_193] :
      ( r1_lattice3(A_190,B_191,D_192)
      | ~ r1_lattice3(A_190,C_193,D_192)
      | ~ m1_subset_1(D_192,u1_struct_0(A_190))
      | ~ r1_tarski(B_191,C_193)
      | ~ l1_orders_2(A_190) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_375,plain,(
    ! [A_201,B_202,B_203] :
      ( r1_lattice3(A_201,B_202,k2_yellow_0(A_201,B_203))
      | ~ m1_subset_1(k2_yellow_0(A_201,B_203),u1_struct_0(A_201))
      | ~ r1_tarski(B_202,B_203)
      | ~ r2_yellow_0(A_201,B_203)
      | ~ l1_orders_2(A_201) ) ),
    inference(resolution,[status(thm)],[c_354,c_356])).

tff(c_378,plain,(
    ! [A_31,B_202,B_32] :
      ( r1_lattice3(A_31,B_202,k2_yellow_0(A_31,B_32))
      | ~ r1_tarski(B_202,B_32)
      | ~ r2_yellow_0(A_31,B_32)
      | ~ l1_orders_2(A_31) ) ),
    inference(resolution,[status(thm)],[c_30,c_375])).

tff(c_585,plain,(
    ! [A_281,D_282,B_283] :
      ( r1_orders_2(A_281,D_282,k2_yellow_0(A_281,B_283))
      | ~ r1_lattice3(A_281,B_283,D_282)
      | ~ m1_subset_1(D_282,u1_struct_0(A_281))
      | ~ r2_yellow_0(A_281,B_283)
      | ~ m1_subset_1(k2_yellow_0(A_281,B_283),u1_struct_0(A_281))
      | ~ l1_orders_2(A_281) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_615,plain,(
    ! [A_293,D_294,B_295] :
      ( r1_orders_2(A_293,D_294,k2_yellow_0(A_293,B_295))
      | ~ r1_lattice3(A_293,B_295,D_294)
      | ~ m1_subset_1(D_294,u1_struct_0(A_293))
      | ~ r2_yellow_0(A_293,B_295)
      | ~ l1_orders_2(A_293) ) ),
    inference(resolution,[status(thm)],[c_30,c_585])).

tff(c_344,plain,(
    ~ r1_orders_2('#skF_3',k2_yellow_0('#skF_3','#skF_5'),k2_yellow_0('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_622,plain,
    ( ~ r1_lattice3('#skF_3','#skF_4',k2_yellow_0('#skF_3','#skF_5'))
    | ~ m1_subset_1(k2_yellow_0('#skF_3','#skF_5'),u1_struct_0('#skF_3'))
    | ~ r2_yellow_0('#skF_3','#skF_4')
    | ~ l1_orders_2('#skF_3') ),
    inference(resolution,[status(thm)],[c_615,c_344])).

tff(c_626,plain,
    ( ~ r1_lattice3('#skF_3','#skF_4',k2_yellow_0('#skF_3','#skF_5'))
    | ~ m1_subset_1(k2_yellow_0('#skF_3','#skF_5'),u1_struct_0('#skF_3'))
    | ~ r2_yellow_0('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_622])).

tff(c_627,plain,(
    ~ r2_yellow_0('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_626])).

tff(c_630,plain,
    ( ~ l1_orders_2('#skF_3')
    | ~ v3_lattice3('#skF_3')
    | ~ v5_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_627])).

tff(c_633,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_46,c_44,c_630])).

tff(c_635,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_440,c_633])).

tff(c_636,plain,
    ( ~ m1_subset_1(k2_yellow_0('#skF_3','#skF_5'),u1_struct_0('#skF_3'))
    | ~ r1_lattice3('#skF_3','#skF_4',k2_yellow_0('#skF_3','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_626])).

tff(c_638,plain,(
    ~ r1_lattice3('#skF_3','#skF_4',k2_yellow_0('#skF_3','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_636])).

tff(c_651,plain,
    ( ~ r1_tarski('#skF_4','#skF_5')
    | ~ r2_yellow_0('#skF_3','#skF_5')
    | ~ l1_orders_2('#skF_3') ),
    inference(resolution,[status(thm)],[c_378,c_638])).

tff(c_660,plain,(
    ~ r2_yellow_0('#skF_3','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_651])).

tff(c_663,plain,
    ( ~ l1_orders_2('#skF_3')
    | ~ v3_lattice3('#skF_3')
    | ~ v5_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_660])).

tff(c_666,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_46,c_44,c_663])).

tff(c_668,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_440,c_666])).

tff(c_669,plain,(
    ~ m1_subset_1(k2_yellow_0('#skF_3','#skF_5'),u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_636])).

tff(c_673,plain,(
    ~ l1_orders_2('#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_669])).

tff(c_677,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_673])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:44:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.89/1.46  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.32/1.48  
% 3.32/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.32/1.48  %$ r3_orders_2 > r2_lattice3 > r1_orders_2 > r1_lattice3 > r2_yellow_0 > r1_yellow_0 > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v3_lattice3 > v2_struct_0 > v2_lattice3 > v1_lattice3 > l1_orders_2 > k2_yellow_0 > k1_yellow_0 > #nlpp > u1_struct_0 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4
% 3.32/1.48  
% 3.32/1.48  %Foreground sorts:
% 3.32/1.48  
% 3.32/1.48  
% 3.32/1.48  %Background operators:
% 3.32/1.48  
% 3.32/1.48  
% 3.32/1.48  %Foreground operators:
% 3.32/1.48  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.32/1.48  tff(r3_orders_2, type, r3_orders_2: ($i * $i * $i) > $o).
% 3.32/1.48  tff(k1_yellow_0, type, k1_yellow_0: ($i * $i) > $i).
% 3.32/1.48  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.32/1.48  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 3.32/1.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.32/1.48  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 3.32/1.48  tff(v3_lattice3, type, v3_lattice3: $i > $o).
% 3.32/1.48  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.32/1.48  tff(r2_lattice3, type, r2_lattice3: ($i * $i * $i) > $o).
% 3.32/1.48  tff(v1_lattice3, type, v1_lattice3: $i > $o).
% 3.32/1.48  tff('#skF_5', type, '#skF_5': $i).
% 3.32/1.48  tff(r2_yellow_0, type, r2_yellow_0: ($i * $i) > $o).
% 3.32/1.48  tff('#skF_3', type, '#skF_3': $i).
% 3.32/1.48  tff(k2_yellow_0, type, k2_yellow_0: ($i * $i) > $i).
% 3.32/1.48  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.32/1.48  tff(r1_lattice3, type, r1_lattice3: ($i * $i * $i) > $o).
% 3.32/1.48  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 3.32/1.48  tff(r1_yellow_0, type, r1_yellow_0: ($i * $i) > $o).
% 3.32/1.48  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 3.32/1.48  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 3.32/1.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.32/1.48  tff('#skF_4', type, '#skF_4': $i).
% 3.32/1.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.32/1.48  tff(v2_lattice3, type, v2_lattice3: $i > $o).
% 3.32/1.48  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.32/1.48  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.32/1.48  
% 3.43/1.50  tff(f_143, negated_conjecture, ~(![A]: (((((((v3_orders_2(A) & v4_orders_2(A)) & v5_orders_2(A)) & v1_lattice3(A)) & v2_lattice3(A)) & v3_lattice3(A)) & l1_orders_2(A)) => (![B, C]: (r1_tarski(B, C) => (r3_orders_2(A, k1_yellow_0(A, B), k1_yellow_0(A, C)) & r1_orders_2(A, k2_yellow_0(A, C), k2_yellow_0(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_waybel_7)).
% 3.43/1.50  tff(f_91, axiom, (![A, B]: (l1_orders_2(A) => m1_subset_1(k2_yellow_0(A, B), u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_yellow_0)).
% 3.43/1.50  tff(f_87, axiom, (![A, B]: (l1_orders_2(A) => m1_subset_1(k1_yellow_0(A, B), u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_yellow_0)).
% 3.43/1.50  tff(f_40, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v3_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (r3_orders_2(A, B, C) <=> r1_orders_2(A, B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r3_orders_2)).
% 3.43/1.50  tff(f_47, axiom, (![A]: (l1_orders_2(A) => (v1_lattice3(A) => ~v2_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_lattice3)).
% 3.43/1.50  tff(f_105, axiom, (![A]: ((((~v2_struct_0(A) & v5_orders_2(A)) & v3_lattice3(A)) & l1_orders_2(A)) => (![B]: (r1_yellow_0(A, B) & r2_yellow_0(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_yellow_0)).
% 3.43/1.50  tff(f_83, axiom, (![A]: (l1_orders_2(A) => (![B, C]: (m1_subset_1(C, u1_struct_0(A)) => (r1_yellow_0(A, B) => ((C = k1_yellow_0(A, B)) <=> (r2_lattice3(A, B, C) & (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_lattice3(A, B, D) => r1_orders_2(A, C, D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_yellow_0)).
% 3.43/1.50  tff(f_121, axiom, (![A]: (l1_orders_2(A) => (![B, C]: (r1_tarski(B, C) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => ((r1_lattice3(A, C, D) => r1_lattice3(A, B, D)) & (r2_lattice3(A, C, D) => r2_lattice3(A, B, D))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_yellow_0)).
% 3.43/1.50  tff(f_65, axiom, (![A]: (l1_orders_2(A) => (![B, C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_yellow_0(A, B) => ((C = k2_yellow_0(A, B)) <=> (r1_lattice3(A, B, C) & (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r1_lattice3(A, B, D) => r1_orders_2(A, D, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_yellow_0)).
% 3.43/1.50  tff(c_44, plain, (l1_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.43/1.50  tff(c_30, plain, (![A_31, B_32]: (m1_subset_1(k2_yellow_0(A_31, B_32), u1_struct_0(A_31)) | ~l1_orders_2(A_31))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.43/1.50  tff(c_50, plain, (v1_lattice3('#skF_3')), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.43/1.50  tff(c_28, plain, (![A_29, B_30]: (m1_subset_1(k1_yellow_0(A_29, B_30), u1_struct_0(A_29)) | ~l1_orders_2(A_29))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.43/1.50  tff(c_56, plain, (v3_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.43/1.50  tff(c_98, plain, (![A_87, B_88, C_89]: (r3_orders_2(A_87, B_88, C_89) | ~r1_orders_2(A_87, B_88, C_89) | ~m1_subset_1(C_89, u1_struct_0(A_87)) | ~m1_subset_1(B_88, u1_struct_0(A_87)) | ~l1_orders_2(A_87) | ~v3_orders_2(A_87) | v2_struct_0(A_87))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.43/1.50  tff(c_105, plain, (![A_90, B_91, B_92]: (r3_orders_2(A_90, B_91, k1_yellow_0(A_90, B_92)) | ~r1_orders_2(A_90, B_91, k1_yellow_0(A_90, B_92)) | ~m1_subset_1(B_91, u1_struct_0(A_90)) | ~v3_orders_2(A_90) | v2_struct_0(A_90) | ~l1_orders_2(A_90))), inference(resolution, [status(thm)], [c_28, c_98])).
% 3.43/1.50  tff(c_40, plain, (~r1_orders_2('#skF_3', k2_yellow_0('#skF_3', '#skF_5'), k2_yellow_0('#skF_3', '#skF_4')) | ~r3_orders_2('#skF_3', k1_yellow_0('#skF_3', '#skF_4'), k1_yellow_0('#skF_3', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.43/1.50  tff(c_58, plain, (~r3_orders_2('#skF_3', k1_yellow_0('#skF_3', '#skF_4'), k1_yellow_0('#skF_3', '#skF_5'))), inference(splitLeft, [status(thm)], [c_40])).
% 3.43/1.50  tff(c_110, plain, (~r1_orders_2('#skF_3', k1_yellow_0('#skF_3', '#skF_4'), k1_yellow_0('#skF_3', '#skF_5')) | ~m1_subset_1(k1_yellow_0('#skF_3', '#skF_4'), u1_struct_0('#skF_3')) | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3') | ~l1_orders_2('#skF_3')), inference(resolution, [status(thm)], [c_105, c_58])).
% 3.43/1.50  tff(c_114, plain, (~r1_orders_2('#skF_3', k1_yellow_0('#skF_3', '#skF_4'), k1_yellow_0('#skF_3', '#skF_5')) | ~m1_subset_1(k1_yellow_0('#skF_3', '#skF_4'), u1_struct_0('#skF_3')) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_56, c_110])).
% 3.43/1.50  tff(c_115, plain, (~m1_subset_1(k1_yellow_0('#skF_3', '#skF_4'), u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_114])).
% 3.43/1.50  tff(c_118, plain, (~l1_orders_2('#skF_3')), inference(resolution, [status(thm)], [c_28, c_115])).
% 3.43/1.50  tff(c_122, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_118])).
% 3.43/1.50  tff(c_124, plain, (m1_subset_1(k1_yellow_0('#skF_3', '#skF_4'), u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_114])).
% 3.43/1.50  tff(c_2, plain, (![A_1, B_2, C_3]: (r3_orders_2(A_1, B_2, C_3) | ~r1_orders_2(A_1, B_2, C_3) | ~m1_subset_1(C_3, u1_struct_0(A_1)) | ~m1_subset_1(B_2, u1_struct_0(A_1)) | ~l1_orders_2(A_1) | ~v3_orders_2(A_1) | v2_struct_0(A_1))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.43/1.50  tff(c_126, plain, (![B_2]: (r3_orders_2('#skF_3', B_2, k1_yellow_0('#skF_3', '#skF_4')) | ~r1_orders_2('#skF_3', B_2, k1_yellow_0('#skF_3', '#skF_4')) | ~m1_subset_1(B_2, u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_124, c_2])).
% 3.43/1.50  tff(c_129, plain, (![B_2]: (r3_orders_2('#skF_3', B_2, k1_yellow_0('#skF_3', '#skF_4')) | ~r1_orders_2('#skF_3', B_2, k1_yellow_0('#skF_3', '#skF_4')) | ~m1_subset_1(B_2, u1_struct_0('#skF_3')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_44, c_126])).
% 3.43/1.50  tff(c_131, plain, (v2_struct_0('#skF_3')), inference(splitLeft, [status(thm)], [c_129])).
% 3.43/1.50  tff(c_6, plain, (![A_4]: (~v2_struct_0(A_4) | ~v1_lattice3(A_4) | ~l1_orders_2(A_4))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.43/1.50  tff(c_134, plain, (~v1_lattice3('#skF_3') | ~l1_orders_2('#skF_3')), inference(resolution, [status(thm)], [c_131, c_6])).
% 3.43/1.50  tff(c_138, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_50, c_134])).
% 3.43/1.50  tff(c_140, plain, (~v2_struct_0('#skF_3')), inference(splitRight, [status(thm)], [c_129])).
% 3.43/1.50  tff(c_52, plain, (v5_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.43/1.50  tff(c_46, plain, (v3_lattice3('#skF_3')), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.43/1.50  tff(c_32, plain, (![A_33, B_35]: (r1_yellow_0(A_33, B_35) | ~l1_orders_2(A_33) | ~v3_lattice3(A_33) | ~v5_orders_2(A_33) | v2_struct_0(A_33))), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.43/1.50  tff(c_42, plain, (r1_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.43/1.50  tff(c_63, plain, (![A_56, B_57]: (r2_lattice3(A_56, B_57, k1_yellow_0(A_56, B_57)) | ~r1_yellow_0(A_56, B_57) | ~m1_subset_1(k1_yellow_0(A_56, B_57), u1_struct_0(A_56)) | ~l1_orders_2(A_56))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.43/1.50  tff(c_66, plain, (![A_29, B_30]: (r2_lattice3(A_29, B_30, k1_yellow_0(A_29, B_30)) | ~r1_yellow_0(A_29, B_30) | ~l1_orders_2(A_29))), inference(resolution, [status(thm)], [c_28, c_63])).
% 3.43/1.50  tff(c_73, plain, (![A_66, B_67, D_68, C_69]: (r2_lattice3(A_66, B_67, D_68) | ~r2_lattice3(A_66, C_69, D_68) | ~m1_subset_1(D_68, u1_struct_0(A_66)) | ~r1_tarski(B_67, C_69) | ~l1_orders_2(A_66))), inference(cnfTransformation, [status(thm)], [f_121])).
% 3.43/1.50  tff(c_81, plain, (![A_72, B_73, B_74]: (r2_lattice3(A_72, B_73, k1_yellow_0(A_72, B_74)) | ~m1_subset_1(k1_yellow_0(A_72, B_74), u1_struct_0(A_72)) | ~r1_tarski(B_73, B_74) | ~r1_yellow_0(A_72, B_74) | ~l1_orders_2(A_72))), inference(resolution, [status(thm)], [c_66, c_73])).
% 3.43/1.50  tff(c_84, plain, (![A_29, B_73, B_30]: (r2_lattice3(A_29, B_73, k1_yellow_0(A_29, B_30)) | ~r1_tarski(B_73, B_30) | ~r1_yellow_0(A_29, B_30) | ~l1_orders_2(A_29))), inference(resolution, [status(thm)], [c_28, c_81])).
% 3.43/1.50  tff(c_85, plain, (![A_75, B_76, B_77]: (r2_lattice3(A_75, B_76, k1_yellow_0(A_75, B_77)) | ~r1_tarski(B_76, B_77) | ~r1_yellow_0(A_75, B_77) | ~l1_orders_2(A_75))), inference(resolution, [status(thm)], [c_28, c_81])).
% 3.43/1.50  tff(c_36, plain, (![A_36, B_41, D_44, C_42]: (r2_lattice3(A_36, B_41, D_44) | ~r2_lattice3(A_36, C_42, D_44) | ~m1_subset_1(D_44, u1_struct_0(A_36)) | ~r1_tarski(B_41, C_42) | ~l1_orders_2(A_36))), inference(cnfTransformation, [status(thm)], [f_121])).
% 3.43/1.50  tff(c_169, plain, (![A_113, B_114, B_115, B_116]: (r2_lattice3(A_113, B_114, k1_yellow_0(A_113, B_115)) | ~m1_subset_1(k1_yellow_0(A_113, B_115), u1_struct_0(A_113)) | ~r1_tarski(B_114, B_116) | ~r1_tarski(B_116, B_115) | ~r1_yellow_0(A_113, B_115) | ~l1_orders_2(A_113))), inference(resolution, [status(thm)], [c_85, c_36])).
% 3.43/1.50  tff(c_171, plain, (![B_114, B_116]: (r2_lattice3('#skF_3', B_114, k1_yellow_0('#skF_3', '#skF_4')) | ~r1_tarski(B_114, B_116) | ~r1_tarski(B_116, '#skF_4') | ~r1_yellow_0('#skF_3', '#skF_4') | ~l1_orders_2('#skF_3'))), inference(resolution, [status(thm)], [c_124, c_169])).
% 3.43/1.50  tff(c_176, plain, (![B_114, B_116]: (r2_lattice3('#skF_3', B_114, k1_yellow_0('#skF_3', '#skF_4')) | ~r1_tarski(B_114, B_116) | ~r1_tarski(B_116, '#skF_4') | ~r1_yellow_0('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_171])).
% 3.43/1.50  tff(c_178, plain, (~r1_yellow_0('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_176])).
% 3.43/1.50  tff(c_185, plain, (~l1_orders_2('#skF_3') | ~v3_lattice3('#skF_3') | ~v5_orders_2('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_32, c_178])).
% 3.43/1.50  tff(c_188, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_46, c_44, c_185])).
% 3.43/1.50  tff(c_190, plain, $false, inference(negUnitSimplification, [status(thm)], [c_140, c_188])).
% 3.43/1.50  tff(c_192, plain, (r1_yellow_0('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_176])).
% 3.43/1.50  tff(c_263, plain, (![A_166, B_167, D_168]: (r1_orders_2(A_166, k1_yellow_0(A_166, B_167), D_168) | ~r2_lattice3(A_166, B_167, D_168) | ~m1_subset_1(D_168, u1_struct_0(A_166)) | ~r1_yellow_0(A_166, B_167) | ~m1_subset_1(k1_yellow_0(A_166, B_167), u1_struct_0(A_166)) | ~l1_orders_2(A_166))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.43/1.50  tff(c_265, plain, (![D_168]: (r1_orders_2('#skF_3', k1_yellow_0('#skF_3', '#skF_4'), D_168) | ~r2_lattice3('#skF_3', '#skF_4', D_168) | ~m1_subset_1(D_168, u1_struct_0('#skF_3')) | ~r1_yellow_0('#skF_3', '#skF_4') | ~l1_orders_2('#skF_3'))), inference(resolution, [status(thm)], [c_124, c_263])).
% 3.43/1.50  tff(c_272, plain, (![D_169]: (r1_orders_2('#skF_3', k1_yellow_0('#skF_3', '#skF_4'), D_169) | ~r2_lattice3('#skF_3', '#skF_4', D_169) | ~m1_subset_1(D_169, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_192, c_265])).
% 3.43/1.50  tff(c_123, plain, (~r1_orders_2('#skF_3', k1_yellow_0('#skF_3', '#skF_4'), k1_yellow_0('#skF_3', '#skF_5')) | v2_struct_0('#skF_3')), inference(splitRight, [status(thm)], [c_114])).
% 3.43/1.50  tff(c_130, plain, (~r1_orders_2('#skF_3', k1_yellow_0('#skF_3', '#skF_4'), k1_yellow_0('#skF_3', '#skF_5'))), inference(splitLeft, [status(thm)], [c_123])).
% 3.43/1.50  tff(c_283, plain, (~r2_lattice3('#skF_3', '#skF_4', k1_yellow_0('#skF_3', '#skF_5')) | ~m1_subset_1(k1_yellow_0('#skF_3', '#skF_5'), u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_272, c_130])).
% 3.43/1.50  tff(c_284, plain, (~m1_subset_1(k1_yellow_0('#skF_3', '#skF_5'), u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_283])).
% 3.43/1.50  tff(c_287, plain, (~l1_orders_2('#skF_3')), inference(resolution, [status(thm)], [c_28, c_284])).
% 3.43/1.50  tff(c_291, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_287])).
% 3.43/1.50  tff(c_292, plain, (~r2_lattice3('#skF_3', '#skF_4', k1_yellow_0('#skF_3', '#skF_5'))), inference(splitRight, [status(thm)], [c_283])).
% 3.43/1.50  tff(c_317, plain, (~r1_tarski('#skF_4', '#skF_5') | ~r1_yellow_0('#skF_3', '#skF_5') | ~l1_orders_2('#skF_3')), inference(resolution, [status(thm)], [c_84, c_292])).
% 3.43/1.50  tff(c_326, plain, (~r1_yellow_0('#skF_3', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_317])).
% 3.43/1.50  tff(c_329, plain, (~l1_orders_2('#skF_3') | ~v3_lattice3('#skF_3') | ~v5_orders_2('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_32, c_326])).
% 3.43/1.50  tff(c_332, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_46, c_44, c_329])).
% 3.43/1.50  tff(c_334, plain, $false, inference(negUnitSimplification, [status(thm)], [c_140, c_332])).
% 3.43/1.50  tff(c_335, plain, (v2_struct_0('#skF_3')), inference(splitRight, [status(thm)], [c_123])).
% 3.43/1.50  tff(c_339, plain, (~v1_lattice3('#skF_3') | ~l1_orders_2('#skF_3')), inference(resolution, [status(thm)], [c_335, c_6])).
% 3.43/1.50  tff(c_343, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_50, c_339])).
% 3.43/1.50  tff(c_345, plain, (r3_orders_2('#skF_3', k1_yellow_0('#skF_3', '#skF_4'), k1_yellow_0('#skF_3', '#skF_5'))), inference(splitRight, [status(thm)], [c_40])).
% 3.43/1.50  tff(c_383, plain, (![A_207, B_208, C_209]: (r1_orders_2(A_207, B_208, C_209) | ~r3_orders_2(A_207, B_208, C_209) | ~m1_subset_1(C_209, u1_struct_0(A_207)) | ~m1_subset_1(B_208, u1_struct_0(A_207)) | ~l1_orders_2(A_207) | ~v3_orders_2(A_207) | v2_struct_0(A_207))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.43/1.50  tff(c_385, plain, (r1_orders_2('#skF_3', k1_yellow_0('#skF_3', '#skF_4'), k1_yellow_0('#skF_3', '#skF_5')) | ~m1_subset_1(k1_yellow_0('#skF_3', '#skF_5'), u1_struct_0('#skF_3')) | ~m1_subset_1(k1_yellow_0('#skF_3', '#skF_4'), u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_345, c_383])).
% 3.43/1.50  tff(c_388, plain, (r1_orders_2('#skF_3', k1_yellow_0('#skF_3', '#skF_4'), k1_yellow_0('#skF_3', '#skF_5')) | ~m1_subset_1(k1_yellow_0('#skF_3', '#skF_5'), u1_struct_0('#skF_3')) | ~m1_subset_1(k1_yellow_0('#skF_3', '#skF_4'), u1_struct_0('#skF_3')) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_44, c_385])).
% 3.43/1.50  tff(c_397, plain, (~m1_subset_1(k1_yellow_0('#skF_3', '#skF_4'), u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_388])).
% 3.43/1.50  tff(c_400, plain, (~l1_orders_2('#skF_3')), inference(resolution, [status(thm)], [c_28, c_397])).
% 3.43/1.50  tff(c_404, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_400])).
% 3.43/1.50  tff(c_405, plain, (~m1_subset_1(k1_yellow_0('#skF_3', '#skF_5'), u1_struct_0('#skF_3')) | v2_struct_0('#skF_3') | r1_orders_2('#skF_3', k1_yellow_0('#skF_3', '#skF_4'), k1_yellow_0('#skF_3', '#skF_5'))), inference(splitRight, [status(thm)], [c_388])).
% 3.43/1.50  tff(c_416, plain, (~m1_subset_1(k1_yellow_0('#skF_3', '#skF_5'), u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_405])).
% 3.43/1.50  tff(c_419, plain, (~l1_orders_2('#skF_3')), inference(resolution, [status(thm)], [c_28, c_416])).
% 3.43/1.50  tff(c_423, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_419])).
% 3.43/1.50  tff(c_424, plain, (r1_orders_2('#skF_3', k1_yellow_0('#skF_3', '#skF_4'), k1_yellow_0('#skF_3', '#skF_5')) | v2_struct_0('#skF_3')), inference(splitRight, [status(thm)], [c_405])).
% 3.43/1.50  tff(c_431, plain, (v2_struct_0('#skF_3')), inference(splitLeft, [status(thm)], [c_424])).
% 3.43/1.50  tff(c_434, plain, (~v1_lattice3('#skF_3') | ~l1_orders_2('#skF_3')), inference(resolution, [status(thm)], [c_431, c_6])).
% 3.43/1.50  tff(c_438, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_50, c_434])).
% 3.43/1.50  tff(c_440, plain, (~v2_struct_0('#skF_3')), inference(splitRight, [status(thm)], [c_424])).
% 3.43/1.50  tff(c_34, plain, (![A_33, B_35]: (r2_yellow_0(A_33, B_35) | ~l1_orders_2(A_33) | ~v3_lattice3(A_33) | ~v5_orders_2(A_33) | v2_struct_0(A_33))), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.43/1.50  tff(c_351, plain, (![A_186, B_187]: (r1_lattice3(A_186, B_187, k2_yellow_0(A_186, B_187)) | ~r2_yellow_0(A_186, B_187) | ~m1_subset_1(k2_yellow_0(A_186, B_187), u1_struct_0(A_186)) | ~l1_orders_2(A_186))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.43/1.50  tff(c_354, plain, (![A_31, B_32]: (r1_lattice3(A_31, B_32, k2_yellow_0(A_31, B_32)) | ~r2_yellow_0(A_31, B_32) | ~l1_orders_2(A_31))), inference(resolution, [status(thm)], [c_30, c_351])).
% 3.43/1.50  tff(c_356, plain, (![A_190, B_191, D_192, C_193]: (r1_lattice3(A_190, B_191, D_192) | ~r1_lattice3(A_190, C_193, D_192) | ~m1_subset_1(D_192, u1_struct_0(A_190)) | ~r1_tarski(B_191, C_193) | ~l1_orders_2(A_190))), inference(cnfTransformation, [status(thm)], [f_121])).
% 3.43/1.50  tff(c_375, plain, (![A_201, B_202, B_203]: (r1_lattice3(A_201, B_202, k2_yellow_0(A_201, B_203)) | ~m1_subset_1(k2_yellow_0(A_201, B_203), u1_struct_0(A_201)) | ~r1_tarski(B_202, B_203) | ~r2_yellow_0(A_201, B_203) | ~l1_orders_2(A_201))), inference(resolution, [status(thm)], [c_354, c_356])).
% 3.43/1.50  tff(c_378, plain, (![A_31, B_202, B_32]: (r1_lattice3(A_31, B_202, k2_yellow_0(A_31, B_32)) | ~r1_tarski(B_202, B_32) | ~r2_yellow_0(A_31, B_32) | ~l1_orders_2(A_31))), inference(resolution, [status(thm)], [c_30, c_375])).
% 3.43/1.50  tff(c_585, plain, (![A_281, D_282, B_283]: (r1_orders_2(A_281, D_282, k2_yellow_0(A_281, B_283)) | ~r1_lattice3(A_281, B_283, D_282) | ~m1_subset_1(D_282, u1_struct_0(A_281)) | ~r2_yellow_0(A_281, B_283) | ~m1_subset_1(k2_yellow_0(A_281, B_283), u1_struct_0(A_281)) | ~l1_orders_2(A_281))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.43/1.50  tff(c_615, plain, (![A_293, D_294, B_295]: (r1_orders_2(A_293, D_294, k2_yellow_0(A_293, B_295)) | ~r1_lattice3(A_293, B_295, D_294) | ~m1_subset_1(D_294, u1_struct_0(A_293)) | ~r2_yellow_0(A_293, B_295) | ~l1_orders_2(A_293))), inference(resolution, [status(thm)], [c_30, c_585])).
% 3.43/1.50  tff(c_344, plain, (~r1_orders_2('#skF_3', k2_yellow_0('#skF_3', '#skF_5'), k2_yellow_0('#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_40])).
% 3.43/1.50  tff(c_622, plain, (~r1_lattice3('#skF_3', '#skF_4', k2_yellow_0('#skF_3', '#skF_5')) | ~m1_subset_1(k2_yellow_0('#skF_3', '#skF_5'), u1_struct_0('#skF_3')) | ~r2_yellow_0('#skF_3', '#skF_4') | ~l1_orders_2('#skF_3')), inference(resolution, [status(thm)], [c_615, c_344])).
% 3.43/1.50  tff(c_626, plain, (~r1_lattice3('#skF_3', '#skF_4', k2_yellow_0('#skF_3', '#skF_5')) | ~m1_subset_1(k2_yellow_0('#skF_3', '#skF_5'), u1_struct_0('#skF_3')) | ~r2_yellow_0('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_622])).
% 3.43/1.50  tff(c_627, plain, (~r2_yellow_0('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_626])).
% 3.43/1.50  tff(c_630, plain, (~l1_orders_2('#skF_3') | ~v3_lattice3('#skF_3') | ~v5_orders_2('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_34, c_627])).
% 3.43/1.50  tff(c_633, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_46, c_44, c_630])).
% 3.43/1.50  tff(c_635, plain, $false, inference(negUnitSimplification, [status(thm)], [c_440, c_633])).
% 3.43/1.50  tff(c_636, plain, (~m1_subset_1(k2_yellow_0('#skF_3', '#skF_5'), u1_struct_0('#skF_3')) | ~r1_lattice3('#skF_3', '#skF_4', k2_yellow_0('#skF_3', '#skF_5'))), inference(splitRight, [status(thm)], [c_626])).
% 3.43/1.50  tff(c_638, plain, (~r1_lattice3('#skF_3', '#skF_4', k2_yellow_0('#skF_3', '#skF_5'))), inference(splitLeft, [status(thm)], [c_636])).
% 3.43/1.50  tff(c_651, plain, (~r1_tarski('#skF_4', '#skF_5') | ~r2_yellow_0('#skF_3', '#skF_5') | ~l1_orders_2('#skF_3')), inference(resolution, [status(thm)], [c_378, c_638])).
% 3.43/1.50  tff(c_660, plain, (~r2_yellow_0('#skF_3', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_651])).
% 3.43/1.50  tff(c_663, plain, (~l1_orders_2('#skF_3') | ~v3_lattice3('#skF_3') | ~v5_orders_2('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_34, c_660])).
% 3.43/1.50  tff(c_666, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_46, c_44, c_663])).
% 3.43/1.50  tff(c_668, plain, $false, inference(negUnitSimplification, [status(thm)], [c_440, c_666])).
% 3.43/1.50  tff(c_669, plain, (~m1_subset_1(k2_yellow_0('#skF_3', '#skF_5'), u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_636])).
% 3.43/1.50  tff(c_673, plain, (~l1_orders_2('#skF_3')), inference(resolution, [status(thm)], [c_30, c_669])).
% 3.43/1.50  tff(c_677, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_673])).
% 3.43/1.50  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.43/1.50  
% 3.43/1.50  Inference rules
% 3.43/1.50  ----------------------
% 3.43/1.50  #Ref     : 0
% 3.43/1.50  #Sup     : 113
% 3.43/1.50  #Fact    : 0
% 3.43/1.50  #Define  : 0
% 3.43/1.50  #Split   : 16
% 3.43/1.50  #Chain   : 0
% 3.43/1.50  #Close   : 0
% 3.43/1.50  
% 3.43/1.50  Ordering : KBO
% 3.43/1.50  
% 3.43/1.50  Simplification rules
% 3.43/1.50  ----------------------
% 3.43/1.50  #Subsume      : 27
% 3.43/1.50  #Demod        : 83
% 3.43/1.50  #Tautology    : 7
% 3.43/1.50  #SimpNegUnit  : 12
% 3.43/1.50  #BackRed      : 0
% 3.43/1.50  
% 3.43/1.50  #Partial instantiations: 0
% 3.43/1.50  #Strategies tried      : 1
% 3.43/1.50  
% 3.43/1.50  Timing (in seconds)
% 3.43/1.50  ----------------------
% 3.43/1.50  Preprocessing        : 0.32
% 3.43/1.50  Parsing              : 0.18
% 3.43/1.50  CNF conversion       : 0.02
% 3.43/1.50  Main loop            : 0.41
% 3.43/1.50  Inferencing          : 0.17
% 3.43/1.51  Reduction            : 0.10
% 3.43/1.51  Demodulation         : 0.07
% 3.43/1.51  BG Simplification    : 0.02
% 3.43/1.51  Subsumption          : 0.08
% 3.43/1.51  Abstraction          : 0.02
% 3.43/1.51  MUC search           : 0.00
% 3.43/1.51  Cooper               : 0.00
% 3.43/1.51  Total                : 0.78
% 3.43/1.51  Index Insertion      : 0.00
% 3.43/1.51  Index Deletion       : 0.00
% 3.43/1.51  Index Matching       : 0.00
% 3.43/1.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
