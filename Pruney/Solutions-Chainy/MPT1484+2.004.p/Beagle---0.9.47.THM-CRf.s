%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:40 EST 2020

% Result     : Theorem 5.67s
% Output     : CNFRefutation 5.67s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 307 expanded)
%              Number of leaves         :   30 ( 130 expanded)
%              Depth                    :   12
%              Number of atoms          :  224 (1234 expanded)
%              Number of equality atoms :   33 ( 159 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_orders_2 > m1_subset_1 > v5_orders_2 > v3_orders_2 > v2_struct_0 > v2_lattice3 > v1_lattice3 > l1_orders_2 > k13_lattice3 > k12_lattice3 > k11_lattice3 > k10_lattice3 > #nlpp > u1_struct_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k13_lattice3,type,(
    k13_lattice3: ( $i * $i * $i ) > $i )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff(k10_lattice3,type,(
    k10_lattice3: ( $i * $i * $i ) > $i )).

tff(k11_lattice3,type,(
    k11_lattice3: ( $i * $i * $i ) > $i )).

tff(v1_lattice3,type,(
    v1_lattice3: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k12_lattice3,type,(
    k12_lattice3: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_173,negated_conjecture,(
    ~ ! [A] :
        ( ( v3_orders_2(A)
          & v5_orders_2(A)
          & v1_lattice3(A)
          & v2_lattice3(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => k13_lattice3(A,k12_lattice3(A,B,C),C) = C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_lattice3)).

tff(f_142,axiom,(
    ! [A,B,C] :
      ( ( v5_orders_2(A)
        & v2_lattice3(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => k12_lattice3(A,B,C) = k11_lattice3(A,B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k12_lattice3)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( ( v5_orders_2(A)
        & v2_lattice3(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => k12_lattice3(A,B,C) = k12_lattice3(A,C,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k12_lattice3)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( ( l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => m1_subset_1(k11_lattice3(A,B,C),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k11_lattice3)).

tff(f_154,axiom,(
    ! [A,B,C] :
      ( ( v5_orders_2(A)
        & v1_lattice3(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => k13_lattice3(A,B,C) = k10_lattice3(A,B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k13_lattice3)).

tff(f_37,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => r1_orders_2(A,B,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_orders_2)).

tff(f_44,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v1_lattice3(A)
       => ~ v2_struct_0(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_lattice3)).

tff(f_130,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v5_orders_2(A)
        & v2_lattice3(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ! [D] :
                  ( m1_subset_1(D,u1_struct_0(A))
                 => ( D = k11_lattice3(A,B,C)
                  <=> ( r1_orders_2(A,D,B)
                      & r1_orders_2(A,D,C)
                      & ! [E] :
                          ( m1_subset_1(E,u1_struct_0(A))
                         => ( ( r1_orders_2(A,E,B)
                              & r1_orders_2(A,E,C) )
                           => r1_orders_2(A,E,D) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l28_lattice3)).

tff(f_97,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v5_orders_2(A)
        & v1_lattice3(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ! [D] :
                  ( m1_subset_1(D,u1_struct_0(A))
                 => ( D = k10_lattice3(A,B,C)
                  <=> ( r1_orders_2(A,B,D)
                      & r1_orders_2(A,C,D)
                      & ! [E] :
                          ( m1_subset_1(E,u1_struct_0(A))
                         => ( ( r1_orders_2(A,B,E)
                              & r1_orders_2(A,C,E) )
                           => r1_orders_2(A,D,E) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l26_lattice3)).

tff(c_48,plain,(
    l1_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_44,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_46,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_54,plain,(
    v5_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_50,plain,(
    v2_lattice3('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_84,plain,(
    ! [A_119,B_120,C_121] :
      ( k12_lattice3(A_119,B_120,C_121) = k11_lattice3(A_119,B_120,C_121)
      | ~ m1_subset_1(C_121,u1_struct_0(A_119))
      | ~ m1_subset_1(B_120,u1_struct_0(A_119))
      | ~ l1_orders_2(A_119)
      | ~ v2_lattice3(A_119)
      | ~ v5_orders_2(A_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_90,plain,(
    ! [B_120] :
      ( k12_lattice3('#skF_3',B_120,'#skF_4') = k11_lattice3('#skF_3',B_120,'#skF_4')
      | ~ m1_subset_1(B_120,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | ~ v2_lattice3('#skF_3')
      | ~ v5_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_46,c_84])).

tff(c_123,plain,(
    ! [B_123] :
      ( k12_lattice3('#skF_3',B_123,'#skF_4') = k11_lattice3('#skF_3',B_123,'#skF_4')
      | ~ m1_subset_1(B_123,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_50,c_48,c_90])).

tff(c_137,plain,(
    k12_lattice3('#skF_3','#skF_5','#skF_4') = k11_lattice3('#skF_3','#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_123])).

tff(c_88,plain,(
    ! [B_120] :
      ( k12_lattice3('#skF_3',B_120,'#skF_5') = k11_lattice3('#skF_3',B_120,'#skF_5')
      | ~ m1_subset_1(B_120,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | ~ v2_lattice3('#skF_3')
      | ~ v5_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_44,c_84])).

tff(c_98,plain,(
    ! [B_122] :
      ( k12_lattice3('#skF_3',B_122,'#skF_5') = k11_lattice3('#skF_3',B_122,'#skF_5')
      | ~ m1_subset_1(B_122,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_50,c_48,c_88])).

tff(c_113,plain,(
    k12_lattice3('#skF_3','#skF_4','#skF_5') = k11_lattice3('#skF_3','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_46,c_98])).

tff(c_161,plain,(
    ! [A_127,C_128,B_129] :
      ( k12_lattice3(A_127,C_128,B_129) = k12_lattice3(A_127,B_129,C_128)
      | ~ m1_subset_1(C_128,u1_struct_0(A_127))
      | ~ m1_subset_1(B_129,u1_struct_0(A_127))
      | ~ l1_orders_2(A_127)
      | ~ v2_lattice3(A_127)
      | ~ v5_orders_2(A_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_165,plain,(
    ! [B_129] :
      ( k12_lattice3('#skF_3',B_129,'#skF_5') = k12_lattice3('#skF_3','#skF_5',B_129)
      | ~ m1_subset_1(B_129,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | ~ v2_lattice3('#skF_3')
      | ~ v5_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_44,c_161])).

tff(c_199,plain,(
    ! [B_131] :
      ( k12_lattice3('#skF_3',B_131,'#skF_5') = k12_lattice3('#skF_3','#skF_5',B_131)
      | ~ m1_subset_1(B_131,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_50,c_48,c_165])).

tff(c_209,plain,(
    k12_lattice3('#skF_3','#skF_5','#skF_4') = k12_lattice3('#skF_3','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_46,c_199])).

tff(c_216,plain,(
    k11_lattice3('#skF_3','#skF_5','#skF_4') = k11_lattice3('#skF_3','#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_113,c_209])).

tff(c_8,plain,(
    ! [A_8,B_9,C_10] :
      ( m1_subset_1(k11_lattice3(A_8,B_9,C_10),u1_struct_0(A_8))
      | ~ m1_subset_1(C_10,u1_struct_0(A_8))
      | ~ m1_subset_1(B_9,u1_struct_0(A_8))
      | ~ l1_orders_2(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_221,plain,
    ( m1_subset_1(k11_lattice3('#skF_3','#skF_4','#skF_5'),u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
    | ~ l1_orders_2('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_216,c_8])).

tff(c_225,plain,(
    m1_subset_1(k11_lattice3('#skF_3','#skF_4','#skF_5'),u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_44,c_46,c_221])).

tff(c_52,plain,(
    v1_lattice3('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_147,plain,(
    ! [A_124,B_125,C_126] :
      ( k13_lattice3(A_124,B_125,C_126) = k10_lattice3(A_124,B_125,C_126)
      | ~ m1_subset_1(C_126,u1_struct_0(A_124))
      | ~ m1_subset_1(B_125,u1_struct_0(A_124))
      | ~ l1_orders_2(A_124)
      | ~ v1_lattice3(A_124)
      | ~ v5_orders_2(A_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_151,plain,(
    ! [B_125] :
      ( k13_lattice3('#skF_3',B_125,'#skF_5') = k10_lattice3('#skF_3',B_125,'#skF_5')
      | ~ m1_subset_1(B_125,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | ~ v1_lattice3('#skF_3')
      | ~ v5_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_44,c_147])).

tff(c_157,plain,(
    ! [B_125] :
      ( k13_lattice3('#skF_3',B_125,'#skF_5') = k10_lattice3('#skF_3',B_125,'#skF_5')
      | ~ m1_subset_1(B_125,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_48,c_151])).

tff(c_248,plain,(
    k13_lattice3('#skF_3',k11_lattice3('#skF_3','#skF_4','#skF_5'),'#skF_5') = k10_lattice3('#skF_3',k11_lattice3('#skF_3','#skF_4','#skF_5'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_225,c_157])).

tff(c_42,plain,(
    k13_lattice3('#skF_3',k12_lattice3('#skF_3','#skF_4','#skF_5'),'#skF_5') != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_118,plain,(
    k13_lattice3('#skF_3',k11_lattice3('#skF_3','#skF_4','#skF_5'),'#skF_5') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_42])).

tff(c_332,plain,(
    k10_lattice3('#skF_3',k11_lattice3('#skF_3','#skF_4','#skF_5'),'#skF_5') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_248,c_118])).

tff(c_56,plain,(
    v3_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_58,plain,(
    ! [A_114,B_115] :
      ( r1_orders_2(A_114,B_115,B_115)
      | ~ m1_subset_1(B_115,u1_struct_0(A_114))
      | ~ l1_orders_2(A_114)
      | ~ v3_orders_2(A_114)
      | v2_struct_0(A_114) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_60,plain,
    ( r1_orders_2('#skF_3','#skF_5','#skF_5')
    | ~ l1_orders_2('#skF_3')
    | ~ v3_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_58])).

tff(c_65,plain,
    ( r1_orders_2('#skF_3','#skF_5','#skF_5')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_48,c_60])).

tff(c_69,plain,(
    v2_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_65])).

tff(c_4,plain,(
    ! [A_4] :
      ( ~ v2_struct_0(A_4)
      | ~ v1_lattice3(A_4)
      | ~ l1_orders_2(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_72,plain,
    ( ~ v1_lattice3('#skF_3')
    | ~ l1_orders_2('#skF_3') ),
    inference(resolution,[status(thm)],[c_69,c_4])).

tff(c_76,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_52,c_72])).

tff(c_78,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_65])).

tff(c_341,plain,(
    ! [A_137,B_138,C_139] :
      ( r1_orders_2(A_137,k11_lattice3(A_137,B_138,C_139),C_139)
      | ~ m1_subset_1(k11_lattice3(A_137,B_138,C_139),u1_struct_0(A_137))
      | ~ m1_subset_1(C_139,u1_struct_0(A_137))
      | ~ m1_subset_1(B_138,u1_struct_0(A_137))
      | ~ l1_orders_2(A_137)
      | ~ v2_lattice3(A_137)
      | ~ v5_orders_2(A_137)
      | v2_struct_0(A_137) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_343,plain,
    ( r1_orders_2('#skF_3',k11_lattice3('#skF_3','#skF_4','#skF_5'),'#skF_5')
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ l1_orders_2('#skF_3')
    | ~ v2_lattice3('#skF_3')
    | ~ v5_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_225,c_341])).

tff(c_350,plain,
    ( r1_orders_2('#skF_3',k11_lattice3('#skF_3','#skF_4','#skF_5'),'#skF_5')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_50,c_48,c_46,c_44,c_343])).

tff(c_351,plain,(
    r1_orders_2('#skF_3',k11_lattice3('#skF_3','#skF_4','#skF_5'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_350])).

tff(c_77,plain,(
    r1_orders_2('#skF_3','#skF_5','#skF_5') ),
    inference(splitRight,[status(thm)],[c_65])).

tff(c_1907,plain,(
    ! [A_209,C_210,B_211,D_212] :
      ( r1_orders_2(A_209,C_210,'#skF_1'(A_209,B_211,C_210,D_212))
      | k10_lattice3(A_209,B_211,C_210) = D_212
      | ~ r1_orders_2(A_209,C_210,D_212)
      | ~ r1_orders_2(A_209,B_211,D_212)
      | ~ m1_subset_1(D_212,u1_struct_0(A_209))
      | ~ m1_subset_1(C_210,u1_struct_0(A_209))
      | ~ m1_subset_1(B_211,u1_struct_0(A_209))
      | ~ l1_orders_2(A_209)
      | ~ v1_lattice3(A_209)
      | ~ v5_orders_2(A_209)
      | v2_struct_0(A_209) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_10,plain,(
    ! [A_11,D_53,B_35,C_47] :
      ( ~ r1_orders_2(A_11,D_53,'#skF_1'(A_11,B_35,C_47,D_53))
      | k10_lattice3(A_11,B_35,C_47) = D_53
      | ~ r1_orders_2(A_11,C_47,D_53)
      | ~ r1_orders_2(A_11,B_35,D_53)
      | ~ m1_subset_1(D_53,u1_struct_0(A_11))
      | ~ m1_subset_1(C_47,u1_struct_0(A_11))
      | ~ m1_subset_1(B_35,u1_struct_0(A_11))
      | ~ l1_orders_2(A_11)
      | ~ v1_lattice3(A_11)
      | ~ v5_orders_2(A_11)
      | v2_struct_0(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_2773,plain,(
    ! [A_232,B_233,D_234] :
      ( k10_lattice3(A_232,B_233,D_234) = D_234
      | ~ r1_orders_2(A_232,D_234,D_234)
      | ~ r1_orders_2(A_232,B_233,D_234)
      | ~ m1_subset_1(D_234,u1_struct_0(A_232))
      | ~ m1_subset_1(B_233,u1_struct_0(A_232))
      | ~ l1_orders_2(A_232)
      | ~ v1_lattice3(A_232)
      | ~ v5_orders_2(A_232)
      | v2_struct_0(A_232) ) ),
    inference(resolution,[status(thm)],[c_1907,c_10])).

tff(c_2790,plain,(
    ! [B_233] :
      ( k10_lattice3('#skF_3',B_233,'#skF_5') = '#skF_5'
      | ~ r1_orders_2('#skF_3',B_233,'#skF_5')
      | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
      | ~ m1_subset_1(B_233,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | ~ v1_lattice3('#skF_3')
      | ~ v5_orders_2('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_77,c_2773])).

tff(c_2818,plain,(
    ! [B_233] :
      ( k10_lattice3('#skF_3',B_233,'#skF_5') = '#skF_5'
      | ~ r1_orders_2('#skF_3',B_233,'#skF_5')
      | ~ m1_subset_1(B_233,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_48,c_44,c_2790])).

tff(c_3010,plain,(
    ! [B_239] :
      ( k10_lattice3('#skF_3',B_239,'#skF_5') = '#skF_5'
      | ~ r1_orders_2('#skF_3',B_239,'#skF_5')
      | ~ m1_subset_1(B_239,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_2818])).

tff(c_3033,plain,
    ( k10_lattice3('#skF_3',k11_lattice3('#skF_3','#skF_4','#skF_5'),'#skF_5') = '#skF_5'
    | ~ r1_orders_2('#skF_3',k11_lattice3('#skF_3','#skF_4','#skF_5'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_225,c_3010])).

tff(c_3062,plain,(
    k10_lattice3('#skF_3',k11_lattice3('#skF_3','#skF_4','#skF_5'),'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_351,c_3033])).

tff(c_3064,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_332,c_3062])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:16:19 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.67/2.12  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.67/2.13  
% 5.67/2.13  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.67/2.13  %$ r1_orders_2 > m1_subset_1 > v5_orders_2 > v3_orders_2 > v2_struct_0 > v2_lattice3 > v1_lattice3 > l1_orders_2 > k13_lattice3 > k12_lattice3 > k11_lattice3 > k10_lattice3 > #nlpp > u1_struct_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 5.67/2.13  
% 5.67/2.13  %Foreground sorts:
% 5.67/2.13  
% 5.67/2.13  
% 5.67/2.13  %Background operators:
% 5.67/2.13  
% 5.67/2.13  
% 5.67/2.13  %Foreground operators:
% 5.67/2.13  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 5.67/2.13  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 5.67/2.13  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.67/2.13  tff(k13_lattice3, type, k13_lattice3: ($i * $i * $i) > $i).
% 5.67/2.13  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 5.67/2.13  tff(k10_lattice3, type, k10_lattice3: ($i * $i * $i) > $i).
% 5.67/2.13  tff(k11_lattice3, type, k11_lattice3: ($i * $i * $i) > $i).
% 5.67/2.13  tff(v1_lattice3, type, v1_lattice3: $i > $o).
% 5.67/2.13  tff('#skF_5', type, '#skF_5': $i).
% 5.67/2.13  tff(k12_lattice3, type, k12_lattice3: ($i * $i * $i) > $i).
% 5.67/2.13  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 5.67/2.13  tff('#skF_3', type, '#skF_3': $i).
% 5.67/2.13  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 5.67/2.13  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 5.67/2.13  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.67/2.13  tff('#skF_4', type, '#skF_4': $i).
% 5.67/2.13  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.67/2.13  tff(v2_lattice3, type, v2_lattice3: $i > $o).
% 5.67/2.13  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 5.67/2.13  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.67/2.13  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.67/2.13  
% 5.67/2.15  tff(f_173, negated_conjecture, ~(![A]: (((((v3_orders_2(A) & v5_orders_2(A)) & v1_lattice3(A)) & v2_lattice3(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (k13_lattice3(A, k12_lattice3(A, B, C), C) = C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_lattice3)).
% 5.67/2.15  tff(f_142, axiom, (![A, B, C]: (((((v5_orders_2(A) & v2_lattice3(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (k12_lattice3(A, B, C) = k11_lattice3(A, B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k12_lattice3)).
% 5.67/2.15  tff(f_56, axiom, (![A, B, C]: (((((v5_orders_2(A) & v2_lattice3(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (k12_lattice3(A, B, C) = k12_lattice3(A, C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k12_lattice3)).
% 5.67/2.15  tff(f_64, axiom, (![A, B, C]: (((l1_orders_2(A) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => m1_subset_1(k11_lattice3(A, B, C), u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k11_lattice3)).
% 5.67/2.15  tff(f_154, axiom, (![A, B, C]: (((((v5_orders_2(A) & v1_lattice3(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (k13_lattice3(A, B, C) = k10_lattice3(A, B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k13_lattice3)).
% 5.67/2.15  tff(f_37, axiom, (![A]: (((~v2_struct_0(A) & v3_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => r1_orders_2(A, B, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_orders_2)).
% 5.67/2.15  tff(f_44, axiom, (![A]: (l1_orders_2(A) => (v1_lattice3(A) => ~v2_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_lattice3)).
% 5.67/2.15  tff(f_130, axiom, (![A]: ((((~v2_struct_0(A) & v5_orders_2(A)) & v2_lattice3(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => ((D = k11_lattice3(A, B, C)) <=> ((r1_orders_2(A, D, B) & r1_orders_2(A, D, C)) & (![E]: (m1_subset_1(E, u1_struct_0(A)) => ((r1_orders_2(A, E, B) & r1_orders_2(A, E, C)) => r1_orders_2(A, E, D)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l28_lattice3)).
% 5.67/2.15  tff(f_97, axiom, (![A]: ((((~v2_struct_0(A) & v5_orders_2(A)) & v1_lattice3(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => ((D = k10_lattice3(A, B, C)) <=> ((r1_orders_2(A, B, D) & r1_orders_2(A, C, D)) & (![E]: (m1_subset_1(E, u1_struct_0(A)) => ((r1_orders_2(A, B, E) & r1_orders_2(A, C, E)) => r1_orders_2(A, D, E)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l26_lattice3)).
% 5.67/2.15  tff(c_48, plain, (l1_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_173])).
% 5.67/2.15  tff(c_44, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_173])).
% 5.67/2.15  tff(c_46, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_173])).
% 5.67/2.15  tff(c_54, plain, (v5_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_173])).
% 5.67/2.15  tff(c_50, plain, (v2_lattice3('#skF_3')), inference(cnfTransformation, [status(thm)], [f_173])).
% 5.67/2.15  tff(c_84, plain, (![A_119, B_120, C_121]: (k12_lattice3(A_119, B_120, C_121)=k11_lattice3(A_119, B_120, C_121) | ~m1_subset_1(C_121, u1_struct_0(A_119)) | ~m1_subset_1(B_120, u1_struct_0(A_119)) | ~l1_orders_2(A_119) | ~v2_lattice3(A_119) | ~v5_orders_2(A_119))), inference(cnfTransformation, [status(thm)], [f_142])).
% 5.67/2.15  tff(c_90, plain, (![B_120]: (k12_lattice3('#skF_3', B_120, '#skF_4')=k11_lattice3('#skF_3', B_120, '#skF_4') | ~m1_subset_1(B_120, u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v2_lattice3('#skF_3') | ~v5_orders_2('#skF_3'))), inference(resolution, [status(thm)], [c_46, c_84])).
% 5.67/2.15  tff(c_123, plain, (![B_123]: (k12_lattice3('#skF_3', B_123, '#skF_4')=k11_lattice3('#skF_3', B_123, '#skF_4') | ~m1_subset_1(B_123, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_50, c_48, c_90])).
% 5.67/2.15  tff(c_137, plain, (k12_lattice3('#skF_3', '#skF_5', '#skF_4')=k11_lattice3('#skF_3', '#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_44, c_123])).
% 5.67/2.15  tff(c_88, plain, (![B_120]: (k12_lattice3('#skF_3', B_120, '#skF_5')=k11_lattice3('#skF_3', B_120, '#skF_5') | ~m1_subset_1(B_120, u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v2_lattice3('#skF_3') | ~v5_orders_2('#skF_3'))), inference(resolution, [status(thm)], [c_44, c_84])).
% 5.67/2.15  tff(c_98, plain, (![B_122]: (k12_lattice3('#skF_3', B_122, '#skF_5')=k11_lattice3('#skF_3', B_122, '#skF_5') | ~m1_subset_1(B_122, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_50, c_48, c_88])).
% 5.67/2.15  tff(c_113, plain, (k12_lattice3('#skF_3', '#skF_4', '#skF_5')=k11_lattice3('#skF_3', '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_46, c_98])).
% 5.67/2.15  tff(c_161, plain, (![A_127, C_128, B_129]: (k12_lattice3(A_127, C_128, B_129)=k12_lattice3(A_127, B_129, C_128) | ~m1_subset_1(C_128, u1_struct_0(A_127)) | ~m1_subset_1(B_129, u1_struct_0(A_127)) | ~l1_orders_2(A_127) | ~v2_lattice3(A_127) | ~v5_orders_2(A_127))), inference(cnfTransformation, [status(thm)], [f_56])).
% 5.67/2.15  tff(c_165, plain, (![B_129]: (k12_lattice3('#skF_3', B_129, '#skF_5')=k12_lattice3('#skF_3', '#skF_5', B_129) | ~m1_subset_1(B_129, u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v2_lattice3('#skF_3') | ~v5_orders_2('#skF_3'))), inference(resolution, [status(thm)], [c_44, c_161])).
% 5.67/2.15  tff(c_199, plain, (![B_131]: (k12_lattice3('#skF_3', B_131, '#skF_5')=k12_lattice3('#skF_3', '#skF_5', B_131) | ~m1_subset_1(B_131, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_50, c_48, c_165])).
% 5.67/2.15  tff(c_209, plain, (k12_lattice3('#skF_3', '#skF_5', '#skF_4')=k12_lattice3('#skF_3', '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_46, c_199])).
% 5.67/2.15  tff(c_216, plain, (k11_lattice3('#skF_3', '#skF_5', '#skF_4')=k11_lattice3('#skF_3', '#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_137, c_113, c_209])).
% 5.67/2.15  tff(c_8, plain, (![A_8, B_9, C_10]: (m1_subset_1(k11_lattice3(A_8, B_9, C_10), u1_struct_0(A_8)) | ~m1_subset_1(C_10, u1_struct_0(A_8)) | ~m1_subset_1(B_9, u1_struct_0(A_8)) | ~l1_orders_2(A_8))), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.67/2.15  tff(c_221, plain, (m1_subset_1(k11_lattice3('#skF_3', '#skF_4', '#skF_5'), u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_216, c_8])).
% 5.67/2.15  tff(c_225, plain, (m1_subset_1(k11_lattice3('#skF_3', '#skF_4', '#skF_5'), u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_44, c_46, c_221])).
% 5.67/2.15  tff(c_52, plain, (v1_lattice3('#skF_3')), inference(cnfTransformation, [status(thm)], [f_173])).
% 5.67/2.15  tff(c_147, plain, (![A_124, B_125, C_126]: (k13_lattice3(A_124, B_125, C_126)=k10_lattice3(A_124, B_125, C_126) | ~m1_subset_1(C_126, u1_struct_0(A_124)) | ~m1_subset_1(B_125, u1_struct_0(A_124)) | ~l1_orders_2(A_124) | ~v1_lattice3(A_124) | ~v5_orders_2(A_124))), inference(cnfTransformation, [status(thm)], [f_154])).
% 5.67/2.15  tff(c_151, plain, (![B_125]: (k13_lattice3('#skF_3', B_125, '#skF_5')=k10_lattice3('#skF_3', B_125, '#skF_5') | ~m1_subset_1(B_125, u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v1_lattice3('#skF_3') | ~v5_orders_2('#skF_3'))), inference(resolution, [status(thm)], [c_44, c_147])).
% 5.67/2.15  tff(c_157, plain, (![B_125]: (k13_lattice3('#skF_3', B_125, '#skF_5')=k10_lattice3('#skF_3', B_125, '#skF_5') | ~m1_subset_1(B_125, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_48, c_151])).
% 5.67/2.15  tff(c_248, plain, (k13_lattice3('#skF_3', k11_lattice3('#skF_3', '#skF_4', '#skF_5'), '#skF_5')=k10_lattice3('#skF_3', k11_lattice3('#skF_3', '#skF_4', '#skF_5'), '#skF_5')), inference(resolution, [status(thm)], [c_225, c_157])).
% 5.67/2.15  tff(c_42, plain, (k13_lattice3('#skF_3', k12_lattice3('#skF_3', '#skF_4', '#skF_5'), '#skF_5')!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_173])).
% 5.67/2.15  tff(c_118, plain, (k13_lattice3('#skF_3', k11_lattice3('#skF_3', '#skF_4', '#skF_5'), '#skF_5')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_113, c_42])).
% 5.67/2.15  tff(c_332, plain, (k10_lattice3('#skF_3', k11_lattice3('#skF_3', '#skF_4', '#skF_5'), '#skF_5')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_248, c_118])).
% 5.67/2.15  tff(c_56, plain, (v3_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_173])).
% 5.67/2.15  tff(c_58, plain, (![A_114, B_115]: (r1_orders_2(A_114, B_115, B_115) | ~m1_subset_1(B_115, u1_struct_0(A_114)) | ~l1_orders_2(A_114) | ~v3_orders_2(A_114) | v2_struct_0(A_114))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.67/2.15  tff(c_60, plain, (r1_orders_2('#skF_3', '#skF_5', '#skF_5') | ~l1_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_44, c_58])).
% 5.67/2.15  tff(c_65, plain, (r1_orders_2('#skF_3', '#skF_5', '#skF_5') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_48, c_60])).
% 5.67/2.15  tff(c_69, plain, (v2_struct_0('#skF_3')), inference(splitLeft, [status(thm)], [c_65])).
% 5.67/2.15  tff(c_4, plain, (![A_4]: (~v2_struct_0(A_4) | ~v1_lattice3(A_4) | ~l1_orders_2(A_4))), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.67/2.15  tff(c_72, plain, (~v1_lattice3('#skF_3') | ~l1_orders_2('#skF_3')), inference(resolution, [status(thm)], [c_69, c_4])).
% 5.67/2.15  tff(c_76, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_52, c_72])).
% 5.67/2.15  tff(c_78, plain, (~v2_struct_0('#skF_3')), inference(splitRight, [status(thm)], [c_65])).
% 5.67/2.15  tff(c_341, plain, (![A_137, B_138, C_139]: (r1_orders_2(A_137, k11_lattice3(A_137, B_138, C_139), C_139) | ~m1_subset_1(k11_lattice3(A_137, B_138, C_139), u1_struct_0(A_137)) | ~m1_subset_1(C_139, u1_struct_0(A_137)) | ~m1_subset_1(B_138, u1_struct_0(A_137)) | ~l1_orders_2(A_137) | ~v2_lattice3(A_137) | ~v5_orders_2(A_137) | v2_struct_0(A_137))), inference(cnfTransformation, [status(thm)], [f_130])).
% 5.67/2.15  tff(c_343, plain, (r1_orders_2('#skF_3', k11_lattice3('#skF_3', '#skF_4', '#skF_5'), '#skF_5') | ~m1_subset_1('#skF_5', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v2_lattice3('#skF_3') | ~v5_orders_2('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_225, c_341])).
% 5.67/2.15  tff(c_350, plain, (r1_orders_2('#skF_3', k11_lattice3('#skF_3', '#skF_4', '#skF_5'), '#skF_5') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_50, c_48, c_46, c_44, c_343])).
% 5.67/2.15  tff(c_351, plain, (r1_orders_2('#skF_3', k11_lattice3('#skF_3', '#skF_4', '#skF_5'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_78, c_350])).
% 5.67/2.15  tff(c_77, plain, (r1_orders_2('#skF_3', '#skF_5', '#skF_5')), inference(splitRight, [status(thm)], [c_65])).
% 5.67/2.15  tff(c_1907, plain, (![A_209, C_210, B_211, D_212]: (r1_orders_2(A_209, C_210, '#skF_1'(A_209, B_211, C_210, D_212)) | k10_lattice3(A_209, B_211, C_210)=D_212 | ~r1_orders_2(A_209, C_210, D_212) | ~r1_orders_2(A_209, B_211, D_212) | ~m1_subset_1(D_212, u1_struct_0(A_209)) | ~m1_subset_1(C_210, u1_struct_0(A_209)) | ~m1_subset_1(B_211, u1_struct_0(A_209)) | ~l1_orders_2(A_209) | ~v1_lattice3(A_209) | ~v5_orders_2(A_209) | v2_struct_0(A_209))), inference(cnfTransformation, [status(thm)], [f_97])).
% 5.67/2.15  tff(c_10, plain, (![A_11, D_53, B_35, C_47]: (~r1_orders_2(A_11, D_53, '#skF_1'(A_11, B_35, C_47, D_53)) | k10_lattice3(A_11, B_35, C_47)=D_53 | ~r1_orders_2(A_11, C_47, D_53) | ~r1_orders_2(A_11, B_35, D_53) | ~m1_subset_1(D_53, u1_struct_0(A_11)) | ~m1_subset_1(C_47, u1_struct_0(A_11)) | ~m1_subset_1(B_35, u1_struct_0(A_11)) | ~l1_orders_2(A_11) | ~v1_lattice3(A_11) | ~v5_orders_2(A_11) | v2_struct_0(A_11))), inference(cnfTransformation, [status(thm)], [f_97])).
% 5.67/2.15  tff(c_2773, plain, (![A_232, B_233, D_234]: (k10_lattice3(A_232, B_233, D_234)=D_234 | ~r1_orders_2(A_232, D_234, D_234) | ~r1_orders_2(A_232, B_233, D_234) | ~m1_subset_1(D_234, u1_struct_0(A_232)) | ~m1_subset_1(B_233, u1_struct_0(A_232)) | ~l1_orders_2(A_232) | ~v1_lattice3(A_232) | ~v5_orders_2(A_232) | v2_struct_0(A_232))), inference(resolution, [status(thm)], [c_1907, c_10])).
% 5.67/2.15  tff(c_2790, plain, (![B_233]: (k10_lattice3('#skF_3', B_233, '#skF_5')='#skF_5' | ~r1_orders_2('#skF_3', B_233, '#skF_5') | ~m1_subset_1('#skF_5', u1_struct_0('#skF_3')) | ~m1_subset_1(B_233, u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v1_lattice3('#skF_3') | ~v5_orders_2('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_77, c_2773])).
% 5.67/2.15  tff(c_2818, plain, (![B_233]: (k10_lattice3('#skF_3', B_233, '#skF_5')='#skF_5' | ~r1_orders_2('#skF_3', B_233, '#skF_5') | ~m1_subset_1(B_233, u1_struct_0('#skF_3')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_48, c_44, c_2790])).
% 5.67/2.15  tff(c_3010, plain, (![B_239]: (k10_lattice3('#skF_3', B_239, '#skF_5')='#skF_5' | ~r1_orders_2('#skF_3', B_239, '#skF_5') | ~m1_subset_1(B_239, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_78, c_2818])).
% 5.67/2.15  tff(c_3033, plain, (k10_lattice3('#skF_3', k11_lattice3('#skF_3', '#skF_4', '#skF_5'), '#skF_5')='#skF_5' | ~r1_orders_2('#skF_3', k11_lattice3('#skF_3', '#skF_4', '#skF_5'), '#skF_5')), inference(resolution, [status(thm)], [c_225, c_3010])).
% 5.67/2.15  tff(c_3062, plain, (k10_lattice3('#skF_3', k11_lattice3('#skF_3', '#skF_4', '#skF_5'), '#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_351, c_3033])).
% 5.67/2.15  tff(c_3064, plain, $false, inference(negUnitSimplification, [status(thm)], [c_332, c_3062])).
% 5.67/2.15  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.67/2.15  
% 5.67/2.15  Inference rules
% 5.67/2.15  ----------------------
% 5.67/2.15  #Ref     : 0
% 5.67/2.15  #Sup     : 655
% 5.67/2.15  #Fact    : 0
% 5.67/2.15  #Define  : 0
% 5.67/2.15  #Split   : 2
% 5.67/2.15  #Chain   : 0
% 5.67/2.15  #Close   : 0
% 5.67/2.15  
% 5.67/2.15  Ordering : KBO
% 5.67/2.15  
% 5.67/2.15  Simplification rules
% 5.67/2.15  ----------------------
% 5.67/2.15  #Subsume      : 3
% 5.67/2.15  #Demod        : 954
% 5.67/2.15  #Tautology    : 293
% 5.67/2.15  #SimpNegUnit  : 131
% 5.67/2.15  #BackRed      : 20
% 5.67/2.15  
% 5.67/2.15  #Partial instantiations: 0
% 5.67/2.15  #Strategies tried      : 1
% 5.67/2.15  
% 5.67/2.15  Timing (in seconds)
% 5.67/2.15  ----------------------
% 5.67/2.15  Preprocessing        : 0.37
% 5.67/2.15  Parsing              : 0.19
% 5.67/2.15  CNF conversion       : 0.03
% 5.67/2.15  Main loop            : 0.94
% 5.67/2.15  Inferencing          : 0.29
% 5.67/2.15  Reduction            : 0.34
% 5.67/2.15  Demodulation         : 0.25
% 5.67/2.15  BG Simplification    : 0.05
% 5.67/2.15  Subsumption          : 0.21
% 5.67/2.15  Abstraction          : 0.06
% 5.67/2.15  MUC search           : 0.00
% 5.67/2.15  Cooper               : 0.00
% 5.67/2.15  Total                : 1.35
% 5.67/2.15  Index Insertion      : 0.00
% 5.67/2.15  Index Deletion       : 0.00
% 5.67/2.15  Index Matching       : 0.00
% 5.67/2.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------
