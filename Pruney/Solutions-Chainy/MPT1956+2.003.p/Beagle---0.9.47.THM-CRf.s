%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:56 EST 2020

% Result     : Theorem 2.74s
% Output     : CNFRefutation 2.74s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 330 expanded)
%              Number of leaves         :   35 ( 126 expanded)
%              Depth                    :   13
%              Number of atoms          :  233 (1303 expanded)
%              Number of equality atoms :    1 (   4 expanded)
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

tff(f_136,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_waybel_7)).

tff(f_73,axiom,(
    ! [A,B] :
      ( l1_orders_2(A)
     => m1_subset_1(k2_yellow_0(A,B),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_yellow_0)).

tff(f_69,axiom,(
    ! [A,B] :
      ( l1_orders_2(A)
     => m1_subset_1(k1_yellow_0(A,B),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_yellow_0)).

tff(f_87,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v5_orders_2(A)
        & v3_lattice3(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( r1_yellow_0(A,B)
          & r2_yellow_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_yellow_0)).

tff(f_98,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B,C] :
          ( ( r1_tarski(B,C)
            & r1_yellow_0(A,B)
            & r1_yellow_0(A,C) )
         => r1_orders_2(A,k1_yellow_0(A,B),k1_yellow_0(A,C)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_yellow_0)).

tff(f_40,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => ( r3_orders_2(A,B,C)
      <=> r1_orders_2(A,B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r3_orders_2)).

tff(f_47,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v1_lattice3(A)
       => ~ v2_struct_0(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_lattice3)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_yellow_0)).

tff(f_114,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_yellow_0)).

tff(c_36,plain,(
    l1_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_20,plain,(
    ! [A_19,B_20] :
      ( m1_subset_1(k2_yellow_0(A_19,B_20),u1_struct_0(A_19))
      | ~ l1_orders_2(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_42,plain,(
    v1_lattice3('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_18,plain,(
    ! [A_17,B_18] :
      ( m1_subset_1(k1_yellow_0(A_17,B_18),u1_struct_0(A_17))
      | ~ l1_orders_2(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_48,plain,(
    v3_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_44,plain,(
    v5_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_38,plain,(
    v3_lattice3('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_22,plain,(
    ! [A_21,B_23] :
      ( r1_yellow_0(A_21,B_23)
      | ~ l1_orders_2(A_21)
      | ~ v3_lattice3(A_21)
      | ~ v5_orders_2(A_21)
      | v2_struct_0(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_34,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_26,plain,(
    ! [A_24,B_27,C_28] :
      ( r1_orders_2(A_24,k1_yellow_0(A_24,B_27),k1_yellow_0(A_24,C_28))
      | ~ r1_yellow_0(A_24,C_28)
      | ~ r1_yellow_0(A_24,B_27)
      | ~ r1_tarski(B_27,C_28)
      | ~ l1_orders_2(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_75,plain,(
    ! [A_73,B_74,C_75] :
      ( r3_orders_2(A_73,B_74,C_75)
      | ~ r1_orders_2(A_73,B_74,C_75)
      | ~ m1_subset_1(C_75,u1_struct_0(A_73))
      | ~ m1_subset_1(B_74,u1_struct_0(A_73))
      | ~ l1_orders_2(A_73)
      | ~ v3_orders_2(A_73)
      | v2_struct_0(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_82,plain,(
    ! [A_76,B_77,B_78] :
      ( r3_orders_2(A_76,B_77,k1_yellow_0(A_76,B_78))
      | ~ r1_orders_2(A_76,B_77,k1_yellow_0(A_76,B_78))
      | ~ m1_subset_1(B_77,u1_struct_0(A_76))
      | ~ v3_orders_2(A_76)
      | v2_struct_0(A_76)
      | ~ l1_orders_2(A_76) ) ),
    inference(resolution,[status(thm)],[c_18,c_75])).

tff(c_32,plain,
    ( ~ r1_orders_2('#skF_2',k2_yellow_0('#skF_2','#skF_4'),k2_yellow_0('#skF_2','#skF_3'))
    | ~ r3_orders_2('#skF_2',k1_yellow_0('#skF_2','#skF_3'),k1_yellow_0('#skF_2','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_50,plain,(
    ~ r3_orders_2('#skF_2',k1_yellow_0('#skF_2','#skF_3'),k1_yellow_0('#skF_2','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_87,plain,
    ( ~ r1_orders_2('#skF_2',k1_yellow_0('#skF_2','#skF_3'),k1_yellow_0('#skF_2','#skF_4'))
    | ~ m1_subset_1(k1_yellow_0('#skF_2','#skF_3'),u1_struct_0('#skF_2'))
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l1_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_82,c_50])).

tff(c_91,plain,
    ( ~ r1_orders_2('#skF_2',k1_yellow_0('#skF_2','#skF_3'),k1_yellow_0('#skF_2','#skF_4'))
    | ~ m1_subset_1(k1_yellow_0('#skF_2','#skF_3'),u1_struct_0('#skF_2'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_48,c_87])).

tff(c_93,plain,(
    ~ m1_subset_1(k1_yellow_0('#skF_2','#skF_3'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_91])).

tff(c_96,plain,(
    ~ l1_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_18,c_93])).

tff(c_100,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_96])).

tff(c_101,plain,
    ( ~ r1_orders_2('#skF_2',k1_yellow_0('#skF_2','#skF_3'),k1_yellow_0('#skF_2','#skF_4'))
    | v2_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_91])).

tff(c_108,plain,(
    ~ r1_orders_2('#skF_2',k1_yellow_0('#skF_2','#skF_3'),k1_yellow_0('#skF_2','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_101])).

tff(c_111,plain,
    ( ~ r1_yellow_0('#skF_2','#skF_4')
    | ~ r1_yellow_0('#skF_2','#skF_3')
    | ~ r1_tarski('#skF_3','#skF_4')
    | ~ l1_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_108])).

tff(c_114,plain,
    ( ~ r1_yellow_0('#skF_2','#skF_4')
    | ~ r1_yellow_0('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_111])).

tff(c_115,plain,(
    ~ r1_yellow_0('#skF_2','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_114])).

tff(c_118,plain,
    ( ~ l1_orders_2('#skF_2')
    | ~ v3_lattice3('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_22,c_115])).

tff(c_121,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_38,c_36,c_118])).

tff(c_6,plain,(
    ! [A_4] :
      ( ~ v2_struct_0(A_4)
      | ~ v1_lattice3(A_4)
      | ~ l1_orders_2(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_124,plain,
    ( ~ v1_lattice3('#skF_2')
    | ~ l1_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_121,c_6])).

tff(c_128,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_42,c_124])).

tff(c_129,plain,(
    ~ r1_yellow_0('#skF_2','#skF_4') ),
    inference(splitRight,[status(thm)],[c_114])).

tff(c_137,plain,
    ( ~ l1_orders_2('#skF_2')
    | ~ v3_lattice3('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_22,c_129])).

tff(c_140,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_38,c_36,c_137])).

tff(c_143,plain,
    ( ~ v1_lattice3('#skF_2')
    | ~ l1_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_140,c_6])).

tff(c_147,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_42,c_143])).

tff(c_148,plain,(
    v2_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_101])).

tff(c_152,plain,
    ( ~ v1_lattice3('#skF_2')
    | ~ l1_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_148,c_6])).

tff(c_156,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_42,c_152])).

tff(c_158,plain,(
    r3_orders_2('#skF_2',k1_yellow_0('#skF_2','#skF_3'),k1_yellow_0('#skF_2','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_189,plain,(
    ! [A_117,B_118,C_119] :
      ( r1_orders_2(A_117,B_118,C_119)
      | ~ r3_orders_2(A_117,B_118,C_119)
      | ~ m1_subset_1(C_119,u1_struct_0(A_117))
      | ~ m1_subset_1(B_118,u1_struct_0(A_117))
      | ~ l1_orders_2(A_117)
      | ~ v3_orders_2(A_117)
      | v2_struct_0(A_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_191,plain,
    ( r1_orders_2('#skF_2',k1_yellow_0('#skF_2','#skF_3'),k1_yellow_0('#skF_2','#skF_4'))
    | ~ m1_subset_1(k1_yellow_0('#skF_2','#skF_4'),u1_struct_0('#skF_2'))
    | ~ m1_subset_1(k1_yellow_0('#skF_2','#skF_3'),u1_struct_0('#skF_2'))
    | ~ l1_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_158,c_189])).

tff(c_194,plain,
    ( r1_orders_2('#skF_2',k1_yellow_0('#skF_2','#skF_3'),k1_yellow_0('#skF_2','#skF_4'))
    | ~ m1_subset_1(k1_yellow_0('#skF_2','#skF_4'),u1_struct_0('#skF_2'))
    | ~ m1_subset_1(k1_yellow_0('#skF_2','#skF_3'),u1_struct_0('#skF_2'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_36,c_191])).

tff(c_200,plain,(
    ~ m1_subset_1(k1_yellow_0('#skF_2','#skF_3'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_194])).

tff(c_203,plain,(
    ~ l1_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_18,c_200])).

tff(c_207,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_203])).

tff(c_208,plain,
    ( ~ m1_subset_1(k1_yellow_0('#skF_2','#skF_4'),u1_struct_0('#skF_2'))
    | v2_struct_0('#skF_2')
    | r1_orders_2('#skF_2',k1_yellow_0('#skF_2','#skF_3'),k1_yellow_0('#skF_2','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_194])).

tff(c_215,plain,(
    ~ m1_subset_1(k1_yellow_0('#skF_2','#skF_4'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_208])).

tff(c_218,plain,(
    ~ l1_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_18,c_215])).

tff(c_222,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_218])).

tff(c_223,plain,
    ( r1_orders_2('#skF_2',k1_yellow_0('#skF_2','#skF_3'),k1_yellow_0('#skF_2','#skF_4'))
    | v2_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_208])).

tff(c_230,plain,(
    v2_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_223])).

tff(c_233,plain,
    ( ~ v1_lattice3('#skF_2')
    | ~ l1_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_230,c_6])).

tff(c_237,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_42,c_233])).

tff(c_239,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_223])).

tff(c_24,plain,(
    ! [A_21,B_23] :
      ( r2_yellow_0(A_21,B_23)
      | ~ l1_orders_2(A_21)
      | ~ v3_lattice3(A_21)
      | ~ v5_orders_2(A_21)
      | v2_struct_0(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_164,plain,(
    ! [A_97,B_98] :
      ( r1_lattice3(A_97,B_98,k2_yellow_0(A_97,B_98))
      | ~ r2_yellow_0(A_97,B_98)
      | ~ m1_subset_1(k2_yellow_0(A_97,B_98),u1_struct_0(A_97))
      | ~ l1_orders_2(A_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_167,plain,(
    ! [A_19,B_20] :
      ( r1_lattice3(A_19,B_20,k2_yellow_0(A_19,B_20))
      | ~ r2_yellow_0(A_19,B_20)
      | ~ l1_orders_2(A_19) ) ),
    inference(resolution,[status(thm)],[c_20,c_164])).

tff(c_169,plain,(
    ! [A_101,B_102,D_103,C_104] :
      ( r1_lattice3(A_101,B_102,D_103)
      | ~ r1_lattice3(A_101,C_104,D_103)
      | ~ m1_subset_1(D_103,u1_struct_0(A_101))
      | ~ r1_tarski(B_102,C_104)
      | ~ l1_orders_2(A_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_174,plain,(
    ! [A_108,B_109,B_110] :
      ( r1_lattice3(A_108,B_109,k2_yellow_0(A_108,B_110))
      | ~ m1_subset_1(k2_yellow_0(A_108,B_110),u1_struct_0(A_108))
      | ~ r1_tarski(B_109,B_110)
      | ~ r2_yellow_0(A_108,B_110)
      | ~ l1_orders_2(A_108) ) ),
    inference(resolution,[status(thm)],[c_167,c_169])).

tff(c_177,plain,(
    ! [A_19,B_109,B_20] :
      ( r1_lattice3(A_19,B_109,k2_yellow_0(A_19,B_20))
      | ~ r1_tarski(B_109,B_20)
      | ~ r2_yellow_0(A_19,B_20)
      | ~ l1_orders_2(A_19) ) ),
    inference(resolution,[status(thm)],[c_20,c_174])).

tff(c_284,plain,(
    ! [A_150,D_151,B_152] :
      ( r1_orders_2(A_150,D_151,k2_yellow_0(A_150,B_152))
      | ~ r1_lattice3(A_150,B_152,D_151)
      | ~ m1_subset_1(D_151,u1_struct_0(A_150))
      | ~ r2_yellow_0(A_150,B_152)
      | ~ m1_subset_1(k2_yellow_0(A_150,B_152),u1_struct_0(A_150))
      | ~ l1_orders_2(A_150) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_292,plain,(
    ! [A_156,D_157,B_158] :
      ( r1_orders_2(A_156,D_157,k2_yellow_0(A_156,B_158))
      | ~ r1_lattice3(A_156,B_158,D_157)
      | ~ m1_subset_1(D_157,u1_struct_0(A_156))
      | ~ r2_yellow_0(A_156,B_158)
      | ~ l1_orders_2(A_156) ) ),
    inference(resolution,[status(thm)],[c_20,c_284])).

tff(c_157,plain,(
    ~ r1_orders_2('#skF_2',k2_yellow_0('#skF_2','#skF_4'),k2_yellow_0('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_299,plain,
    ( ~ r1_lattice3('#skF_2','#skF_3',k2_yellow_0('#skF_2','#skF_4'))
    | ~ m1_subset_1(k2_yellow_0('#skF_2','#skF_4'),u1_struct_0('#skF_2'))
    | ~ r2_yellow_0('#skF_2','#skF_3')
    | ~ l1_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_292,c_157])).

tff(c_303,plain,
    ( ~ r1_lattice3('#skF_2','#skF_3',k2_yellow_0('#skF_2','#skF_4'))
    | ~ m1_subset_1(k2_yellow_0('#skF_2','#skF_4'),u1_struct_0('#skF_2'))
    | ~ r2_yellow_0('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_299])).

tff(c_304,plain,(
    ~ r2_yellow_0('#skF_2','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_303])).

tff(c_307,plain,
    ( ~ l1_orders_2('#skF_2')
    | ~ v3_lattice3('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_304])).

tff(c_310,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_38,c_36,c_307])).

tff(c_312,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_239,c_310])).

tff(c_313,plain,
    ( ~ m1_subset_1(k2_yellow_0('#skF_2','#skF_4'),u1_struct_0('#skF_2'))
    | ~ r1_lattice3('#skF_2','#skF_3',k2_yellow_0('#skF_2','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_303])).

tff(c_315,plain,(
    ~ r1_lattice3('#skF_2','#skF_3',k2_yellow_0('#skF_2','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_313])).

tff(c_324,plain,
    ( ~ r1_tarski('#skF_3','#skF_4')
    | ~ r2_yellow_0('#skF_2','#skF_4')
    | ~ l1_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_177,c_315])).

tff(c_333,plain,(
    ~ r2_yellow_0('#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_324])).

tff(c_336,plain,
    ( ~ l1_orders_2('#skF_2')
    | ~ v3_lattice3('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_333])).

tff(c_339,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_38,c_36,c_336])).

tff(c_341,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_239,c_339])).

tff(c_342,plain,(
    ~ m1_subset_1(k2_yellow_0('#skF_2','#skF_4'),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_313])).

tff(c_346,plain,(
    ~ l1_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_20,c_342])).

tff(c_350,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_346])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n001.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 09:49:29 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.74/1.36  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.74/1.37  
% 2.74/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.74/1.37  %$ r3_orders_2 > r2_lattice3 > r1_orders_2 > r1_lattice3 > r2_yellow_0 > r1_yellow_0 > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v3_lattice3 > v2_struct_0 > v2_lattice3 > v1_lattice3 > l1_orders_2 > k2_yellow_0 > k1_yellow_0 > #nlpp > u1_struct_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 2.74/1.37  
% 2.74/1.37  %Foreground sorts:
% 2.74/1.37  
% 2.74/1.37  
% 2.74/1.37  %Background operators:
% 2.74/1.37  
% 2.74/1.37  
% 2.74/1.37  %Foreground operators:
% 2.74/1.37  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.74/1.37  tff(r3_orders_2, type, r3_orders_2: ($i * $i * $i) > $o).
% 2.74/1.37  tff(k1_yellow_0, type, k1_yellow_0: ($i * $i) > $i).
% 2.74/1.37  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.74/1.37  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 2.74/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.74/1.37  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 2.74/1.37  tff(v3_lattice3, type, v3_lattice3: $i > $o).
% 2.74/1.37  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.74/1.37  tff(r2_lattice3, type, r2_lattice3: ($i * $i * $i) > $o).
% 2.74/1.37  tff(v1_lattice3, type, v1_lattice3: $i > $o).
% 2.74/1.37  tff('#skF_2', type, '#skF_2': $i).
% 2.74/1.37  tff(r2_yellow_0, type, r2_yellow_0: ($i * $i) > $o).
% 2.74/1.37  tff('#skF_3', type, '#skF_3': $i).
% 2.74/1.37  tff(k2_yellow_0, type, k2_yellow_0: ($i * $i) > $i).
% 2.74/1.37  tff(r1_lattice3, type, r1_lattice3: ($i * $i * $i) > $o).
% 2.74/1.37  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.74/1.37  tff(r1_yellow_0, type, r1_yellow_0: ($i * $i) > $o).
% 2.74/1.37  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 2.74/1.37  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.74/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.74/1.37  tff('#skF_4', type, '#skF_4': $i).
% 2.74/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.74/1.37  tff(v2_lattice3, type, v2_lattice3: $i > $o).
% 2.74/1.37  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.74/1.37  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.74/1.37  
% 2.74/1.39  tff(f_136, negated_conjecture, ~(![A]: (((((((v3_orders_2(A) & v4_orders_2(A)) & v5_orders_2(A)) & v1_lattice3(A)) & v2_lattice3(A)) & v3_lattice3(A)) & l1_orders_2(A)) => (![B, C]: (r1_tarski(B, C) => (r3_orders_2(A, k1_yellow_0(A, B), k1_yellow_0(A, C)) & r1_orders_2(A, k2_yellow_0(A, C), k2_yellow_0(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_waybel_7)).
% 2.74/1.39  tff(f_73, axiom, (![A, B]: (l1_orders_2(A) => m1_subset_1(k2_yellow_0(A, B), u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_yellow_0)).
% 2.74/1.39  tff(f_69, axiom, (![A, B]: (l1_orders_2(A) => m1_subset_1(k1_yellow_0(A, B), u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_yellow_0)).
% 2.74/1.39  tff(f_87, axiom, (![A]: ((((~v2_struct_0(A) & v5_orders_2(A)) & v3_lattice3(A)) & l1_orders_2(A)) => (![B]: (r1_yellow_0(A, B) & r2_yellow_0(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_yellow_0)).
% 2.74/1.39  tff(f_98, axiom, (![A]: (l1_orders_2(A) => (![B, C]: (((r1_tarski(B, C) & r1_yellow_0(A, B)) & r1_yellow_0(A, C)) => r1_orders_2(A, k1_yellow_0(A, B), k1_yellow_0(A, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_yellow_0)).
% 2.74/1.39  tff(f_40, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v3_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (r3_orders_2(A, B, C) <=> r1_orders_2(A, B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r3_orders_2)).
% 2.74/1.39  tff(f_47, axiom, (![A]: (l1_orders_2(A) => (v1_lattice3(A) => ~v2_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_lattice3)).
% 2.74/1.39  tff(f_65, axiom, (![A]: (l1_orders_2(A) => (![B, C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_yellow_0(A, B) => ((C = k2_yellow_0(A, B)) <=> (r1_lattice3(A, B, C) & (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r1_lattice3(A, B, D) => r1_orders_2(A, D, C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_yellow_0)).
% 2.74/1.39  tff(f_114, axiom, (![A]: (l1_orders_2(A) => (![B, C]: (r1_tarski(B, C) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => ((r1_lattice3(A, C, D) => r1_lattice3(A, B, D)) & (r2_lattice3(A, C, D) => r2_lattice3(A, B, D))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_yellow_0)).
% 2.74/1.39  tff(c_36, plain, (l1_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_136])).
% 2.74/1.39  tff(c_20, plain, (![A_19, B_20]: (m1_subset_1(k2_yellow_0(A_19, B_20), u1_struct_0(A_19)) | ~l1_orders_2(A_19))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.74/1.39  tff(c_42, plain, (v1_lattice3('#skF_2')), inference(cnfTransformation, [status(thm)], [f_136])).
% 2.74/1.39  tff(c_18, plain, (![A_17, B_18]: (m1_subset_1(k1_yellow_0(A_17, B_18), u1_struct_0(A_17)) | ~l1_orders_2(A_17))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.74/1.39  tff(c_48, plain, (v3_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_136])).
% 2.74/1.39  tff(c_44, plain, (v5_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_136])).
% 2.74/1.39  tff(c_38, plain, (v3_lattice3('#skF_2')), inference(cnfTransformation, [status(thm)], [f_136])).
% 2.74/1.39  tff(c_22, plain, (![A_21, B_23]: (r1_yellow_0(A_21, B_23) | ~l1_orders_2(A_21) | ~v3_lattice3(A_21) | ~v5_orders_2(A_21) | v2_struct_0(A_21))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.74/1.39  tff(c_34, plain, (r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_136])).
% 2.74/1.39  tff(c_26, plain, (![A_24, B_27, C_28]: (r1_orders_2(A_24, k1_yellow_0(A_24, B_27), k1_yellow_0(A_24, C_28)) | ~r1_yellow_0(A_24, C_28) | ~r1_yellow_0(A_24, B_27) | ~r1_tarski(B_27, C_28) | ~l1_orders_2(A_24))), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.74/1.39  tff(c_75, plain, (![A_73, B_74, C_75]: (r3_orders_2(A_73, B_74, C_75) | ~r1_orders_2(A_73, B_74, C_75) | ~m1_subset_1(C_75, u1_struct_0(A_73)) | ~m1_subset_1(B_74, u1_struct_0(A_73)) | ~l1_orders_2(A_73) | ~v3_orders_2(A_73) | v2_struct_0(A_73))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.74/1.39  tff(c_82, plain, (![A_76, B_77, B_78]: (r3_orders_2(A_76, B_77, k1_yellow_0(A_76, B_78)) | ~r1_orders_2(A_76, B_77, k1_yellow_0(A_76, B_78)) | ~m1_subset_1(B_77, u1_struct_0(A_76)) | ~v3_orders_2(A_76) | v2_struct_0(A_76) | ~l1_orders_2(A_76))), inference(resolution, [status(thm)], [c_18, c_75])).
% 2.74/1.39  tff(c_32, plain, (~r1_orders_2('#skF_2', k2_yellow_0('#skF_2', '#skF_4'), k2_yellow_0('#skF_2', '#skF_3')) | ~r3_orders_2('#skF_2', k1_yellow_0('#skF_2', '#skF_3'), k1_yellow_0('#skF_2', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_136])).
% 2.74/1.39  tff(c_50, plain, (~r3_orders_2('#skF_2', k1_yellow_0('#skF_2', '#skF_3'), k1_yellow_0('#skF_2', '#skF_4'))), inference(splitLeft, [status(thm)], [c_32])).
% 2.74/1.39  tff(c_87, plain, (~r1_orders_2('#skF_2', k1_yellow_0('#skF_2', '#skF_3'), k1_yellow_0('#skF_2', '#skF_4')) | ~m1_subset_1(k1_yellow_0('#skF_2', '#skF_3'), u1_struct_0('#skF_2')) | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | ~l1_orders_2('#skF_2')), inference(resolution, [status(thm)], [c_82, c_50])).
% 2.74/1.39  tff(c_91, plain, (~r1_orders_2('#skF_2', k1_yellow_0('#skF_2', '#skF_3'), k1_yellow_0('#skF_2', '#skF_4')) | ~m1_subset_1(k1_yellow_0('#skF_2', '#skF_3'), u1_struct_0('#skF_2')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_48, c_87])).
% 2.74/1.39  tff(c_93, plain, (~m1_subset_1(k1_yellow_0('#skF_2', '#skF_3'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_91])).
% 2.74/1.39  tff(c_96, plain, (~l1_orders_2('#skF_2')), inference(resolution, [status(thm)], [c_18, c_93])).
% 2.74/1.39  tff(c_100, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_96])).
% 2.74/1.39  tff(c_101, plain, (~r1_orders_2('#skF_2', k1_yellow_0('#skF_2', '#skF_3'), k1_yellow_0('#skF_2', '#skF_4')) | v2_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_91])).
% 2.74/1.39  tff(c_108, plain, (~r1_orders_2('#skF_2', k1_yellow_0('#skF_2', '#skF_3'), k1_yellow_0('#skF_2', '#skF_4'))), inference(splitLeft, [status(thm)], [c_101])).
% 2.74/1.39  tff(c_111, plain, (~r1_yellow_0('#skF_2', '#skF_4') | ~r1_yellow_0('#skF_2', '#skF_3') | ~r1_tarski('#skF_3', '#skF_4') | ~l1_orders_2('#skF_2')), inference(resolution, [status(thm)], [c_26, c_108])).
% 2.74/1.39  tff(c_114, plain, (~r1_yellow_0('#skF_2', '#skF_4') | ~r1_yellow_0('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_111])).
% 2.74/1.39  tff(c_115, plain, (~r1_yellow_0('#skF_2', '#skF_3')), inference(splitLeft, [status(thm)], [c_114])).
% 2.74/1.39  tff(c_118, plain, (~l1_orders_2('#skF_2') | ~v3_lattice3('#skF_2') | ~v5_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_22, c_115])).
% 2.74/1.39  tff(c_121, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_38, c_36, c_118])).
% 2.74/1.39  tff(c_6, plain, (![A_4]: (~v2_struct_0(A_4) | ~v1_lattice3(A_4) | ~l1_orders_2(A_4))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.74/1.39  tff(c_124, plain, (~v1_lattice3('#skF_2') | ~l1_orders_2('#skF_2')), inference(resolution, [status(thm)], [c_121, c_6])).
% 2.74/1.39  tff(c_128, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_42, c_124])).
% 2.74/1.39  tff(c_129, plain, (~r1_yellow_0('#skF_2', '#skF_4')), inference(splitRight, [status(thm)], [c_114])).
% 2.74/1.39  tff(c_137, plain, (~l1_orders_2('#skF_2') | ~v3_lattice3('#skF_2') | ~v5_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_22, c_129])).
% 2.74/1.39  tff(c_140, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_38, c_36, c_137])).
% 2.74/1.39  tff(c_143, plain, (~v1_lattice3('#skF_2') | ~l1_orders_2('#skF_2')), inference(resolution, [status(thm)], [c_140, c_6])).
% 2.74/1.39  tff(c_147, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_42, c_143])).
% 2.74/1.39  tff(c_148, plain, (v2_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_101])).
% 2.74/1.39  tff(c_152, plain, (~v1_lattice3('#skF_2') | ~l1_orders_2('#skF_2')), inference(resolution, [status(thm)], [c_148, c_6])).
% 2.74/1.39  tff(c_156, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_42, c_152])).
% 2.74/1.39  tff(c_158, plain, (r3_orders_2('#skF_2', k1_yellow_0('#skF_2', '#skF_3'), k1_yellow_0('#skF_2', '#skF_4'))), inference(splitRight, [status(thm)], [c_32])).
% 2.74/1.39  tff(c_189, plain, (![A_117, B_118, C_119]: (r1_orders_2(A_117, B_118, C_119) | ~r3_orders_2(A_117, B_118, C_119) | ~m1_subset_1(C_119, u1_struct_0(A_117)) | ~m1_subset_1(B_118, u1_struct_0(A_117)) | ~l1_orders_2(A_117) | ~v3_orders_2(A_117) | v2_struct_0(A_117))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.74/1.39  tff(c_191, plain, (r1_orders_2('#skF_2', k1_yellow_0('#skF_2', '#skF_3'), k1_yellow_0('#skF_2', '#skF_4')) | ~m1_subset_1(k1_yellow_0('#skF_2', '#skF_4'), u1_struct_0('#skF_2')) | ~m1_subset_1(k1_yellow_0('#skF_2', '#skF_3'), u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_158, c_189])).
% 2.74/1.39  tff(c_194, plain, (r1_orders_2('#skF_2', k1_yellow_0('#skF_2', '#skF_3'), k1_yellow_0('#skF_2', '#skF_4')) | ~m1_subset_1(k1_yellow_0('#skF_2', '#skF_4'), u1_struct_0('#skF_2')) | ~m1_subset_1(k1_yellow_0('#skF_2', '#skF_3'), u1_struct_0('#skF_2')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_36, c_191])).
% 2.74/1.39  tff(c_200, plain, (~m1_subset_1(k1_yellow_0('#skF_2', '#skF_3'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_194])).
% 2.74/1.39  tff(c_203, plain, (~l1_orders_2('#skF_2')), inference(resolution, [status(thm)], [c_18, c_200])).
% 2.74/1.39  tff(c_207, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_203])).
% 2.74/1.39  tff(c_208, plain, (~m1_subset_1(k1_yellow_0('#skF_2', '#skF_4'), u1_struct_0('#skF_2')) | v2_struct_0('#skF_2') | r1_orders_2('#skF_2', k1_yellow_0('#skF_2', '#skF_3'), k1_yellow_0('#skF_2', '#skF_4'))), inference(splitRight, [status(thm)], [c_194])).
% 2.74/1.39  tff(c_215, plain, (~m1_subset_1(k1_yellow_0('#skF_2', '#skF_4'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_208])).
% 2.74/1.39  tff(c_218, plain, (~l1_orders_2('#skF_2')), inference(resolution, [status(thm)], [c_18, c_215])).
% 2.74/1.39  tff(c_222, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_218])).
% 2.74/1.39  tff(c_223, plain, (r1_orders_2('#skF_2', k1_yellow_0('#skF_2', '#skF_3'), k1_yellow_0('#skF_2', '#skF_4')) | v2_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_208])).
% 2.74/1.39  tff(c_230, plain, (v2_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_223])).
% 2.74/1.39  tff(c_233, plain, (~v1_lattice3('#skF_2') | ~l1_orders_2('#skF_2')), inference(resolution, [status(thm)], [c_230, c_6])).
% 2.74/1.39  tff(c_237, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_42, c_233])).
% 2.74/1.39  tff(c_239, plain, (~v2_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_223])).
% 2.74/1.39  tff(c_24, plain, (![A_21, B_23]: (r2_yellow_0(A_21, B_23) | ~l1_orders_2(A_21) | ~v3_lattice3(A_21) | ~v5_orders_2(A_21) | v2_struct_0(A_21))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.74/1.39  tff(c_164, plain, (![A_97, B_98]: (r1_lattice3(A_97, B_98, k2_yellow_0(A_97, B_98)) | ~r2_yellow_0(A_97, B_98) | ~m1_subset_1(k2_yellow_0(A_97, B_98), u1_struct_0(A_97)) | ~l1_orders_2(A_97))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.74/1.39  tff(c_167, plain, (![A_19, B_20]: (r1_lattice3(A_19, B_20, k2_yellow_0(A_19, B_20)) | ~r2_yellow_0(A_19, B_20) | ~l1_orders_2(A_19))), inference(resolution, [status(thm)], [c_20, c_164])).
% 2.74/1.39  tff(c_169, plain, (![A_101, B_102, D_103, C_104]: (r1_lattice3(A_101, B_102, D_103) | ~r1_lattice3(A_101, C_104, D_103) | ~m1_subset_1(D_103, u1_struct_0(A_101)) | ~r1_tarski(B_102, C_104) | ~l1_orders_2(A_101))), inference(cnfTransformation, [status(thm)], [f_114])).
% 2.74/1.39  tff(c_174, plain, (![A_108, B_109, B_110]: (r1_lattice3(A_108, B_109, k2_yellow_0(A_108, B_110)) | ~m1_subset_1(k2_yellow_0(A_108, B_110), u1_struct_0(A_108)) | ~r1_tarski(B_109, B_110) | ~r2_yellow_0(A_108, B_110) | ~l1_orders_2(A_108))), inference(resolution, [status(thm)], [c_167, c_169])).
% 2.74/1.39  tff(c_177, plain, (![A_19, B_109, B_20]: (r1_lattice3(A_19, B_109, k2_yellow_0(A_19, B_20)) | ~r1_tarski(B_109, B_20) | ~r2_yellow_0(A_19, B_20) | ~l1_orders_2(A_19))), inference(resolution, [status(thm)], [c_20, c_174])).
% 2.74/1.39  tff(c_284, plain, (![A_150, D_151, B_152]: (r1_orders_2(A_150, D_151, k2_yellow_0(A_150, B_152)) | ~r1_lattice3(A_150, B_152, D_151) | ~m1_subset_1(D_151, u1_struct_0(A_150)) | ~r2_yellow_0(A_150, B_152) | ~m1_subset_1(k2_yellow_0(A_150, B_152), u1_struct_0(A_150)) | ~l1_orders_2(A_150))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.74/1.39  tff(c_292, plain, (![A_156, D_157, B_158]: (r1_orders_2(A_156, D_157, k2_yellow_0(A_156, B_158)) | ~r1_lattice3(A_156, B_158, D_157) | ~m1_subset_1(D_157, u1_struct_0(A_156)) | ~r2_yellow_0(A_156, B_158) | ~l1_orders_2(A_156))), inference(resolution, [status(thm)], [c_20, c_284])).
% 2.74/1.39  tff(c_157, plain, (~r1_orders_2('#skF_2', k2_yellow_0('#skF_2', '#skF_4'), k2_yellow_0('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_32])).
% 2.74/1.39  tff(c_299, plain, (~r1_lattice3('#skF_2', '#skF_3', k2_yellow_0('#skF_2', '#skF_4')) | ~m1_subset_1(k2_yellow_0('#skF_2', '#skF_4'), u1_struct_0('#skF_2')) | ~r2_yellow_0('#skF_2', '#skF_3') | ~l1_orders_2('#skF_2')), inference(resolution, [status(thm)], [c_292, c_157])).
% 2.74/1.39  tff(c_303, plain, (~r1_lattice3('#skF_2', '#skF_3', k2_yellow_0('#skF_2', '#skF_4')) | ~m1_subset_1(k2_yellow_0('#skF_2', '#skF_4'), u1_struct_0('#skF_2')) | ~r2_yellow_0('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_299])).
% 2.74/1.39  tff(c_304, plain, (~r2_yellow_0('#skF_2', '#skF_3')), inference(splitLeft, [status(thm)], [c_303])).
% 2.74/1.39  tff(c_307, plain, (~l1_orders_2('#skF_2') | ~v3_lattice3('#skF_2') | ~v5_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_24, c_304])).
% 2.74/1.39  tff(c_310, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_38, c_36, c_307])).
% 2.74/1.39  tff(c_312, plain, $false, inference(negUnitSimplification, [status(thm)], [c_239, c_310])).
% 2.74/1.39  tff(c_313, plain, (~m1_subset_1(k2_yellow_0('#skF_2', '#skF_4'), u1_struct_0('#skF_2')) | ~r1_lattice3('#skF_2', '#skF_3', k2_yellow_0('#skF_2', '#skF_4'))), inference(splitRight, [status(thm)], [c_303])).
% 2.74/1.39  tff(c_315, plain, (~r1_lattice3('#skF_2', '#skF_3', k2_yellow_0('#skF_2', '#skF_4'))), inference(splitLeft, [status(thm)], [c_313])).
% 2.74/1.39  tff(c_324, plain, (~r1_tarski('#skF_3', '#skF_4') | ~r2_yellow_0('#skF_2', '#skF_4') | ~l1_orders_2('#skF_2')), inference(resolution, [status(thm)], [c_177, c_315])).
% 2.74/1.39  tff(c_333, plain, (~r2_yellow_0('#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_324])).
% 2.74/1.39  tff(c_336, plain, (~l1_orders_2('#skF_2') | ~v3_lattice3('#skF_2') | ~v5_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_24, c_333])).
% 2.74/1.39  tff(c_339, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_38, c_36, c_336])).
% 2.74/1.39  tff(c_341, plain, $false, inference(negUnitSimplification, [status(thm)], [c_239, c_339])).
% 2.74/1.39  tff(c_342, plain, (~m1_subset_1(k2_yellow_0('#skF_2', '#skF_4'), u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_313])).
% 2.74/1.39  tff(c_346, plain, (~l1_orders_2('#skF_2')), inference(resolution, [status(thm)], [c_20, c_342])).
% 2.74/1.39  tff(c_350, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_346])).
% 2.74/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.74/1.39  
% 2.74/1.39  Inference rules
% 2.74/1.39  ----------------------
% 2.74/1.39  #Ref     : 0
% 2.74/1.39  #Sup     : 49
% 2.74/1.39  #Fact    : 0
% 2.74/1.39  #Define  : 0
% 2.74/1.39  #Split   : 9
% 2.74/1.39  #Chain   : 0
% 2.74/1.39  #Close   : 0
% 2.74/1.39  
% 2.74/1.39  Ordering : KBO
% 2.74/1.39  
% 2.74/1.39  Simplification rules
% 2.74/1.39  ----------------------
% 2.74/1.39  #Subsume      : 7
% 2.74/1.39  #Demod        : 47
% 2.74/1.39  #Tautology    : 5
% 2.74/1.39  #SimpNegUnit  : 6
% 2.74/1.39  #BackRed      : 0
% 2.74/1.39  
% 2.74/1.39  #Partial instantiations: 0
% 2.74/1.39  #Strategies tried      : 1
% 2.74/1.39  
% 2.74/1.39  Timing (in seconds)
% 2.74/1.39  ----------------------
% 2.74/1.39  Preprocessing        : 0.31
% 2.74/1.39  Parsing              : 0.17
% 2.74/1.39  CNF conversion       : 0.02
% 2.74/1.39  Main loop            : 0.28
% 2.74/1.39  Inferencing          : 0.11
% 2.74/1.39  Reduction            : 0.07
% 2.74/1.39  Demodulation         : 0.05
% 2.74/1.39  BG Simplification    : 0.02
% 2.74/1.39  Subsumption          : 0.05
% 2.74/1.39  Abstraction          : 0.01
% 2.74/1.39  MUC search           : 0.00
% 2.74/1.40  Cooper               : 0.00
% 2.74/1.40  Total                : 0.63
% 2.74/1.40  Index Insertion      : 0.00
% 2.74/1.40  Index Deletion       : 0.00
% 2.74/1.40  Index Matching       : 0.00
% 2.74/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
