%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:40 EST 2020

% Result     : Theorem 7.19s
% Output     : CNFRefutation 7.19s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 226 expanded)
%              Number of leaves         :   29 ( 100 expanded)
%              Depth                    :   11
%              Number of atoms          :  201 ( 913 expanded)
%              Number of equality atoms :   24 ( 102 expanded)
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

tff(f_165,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_lattice3)).

tff(f_134,axiom,(
    ! [A,B,C] :
      ( ( v5_orders_2(A)
        & v2_lattice3(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => k12_lattice3(A,B,C) = k11_lattice3(A,B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k12_lattice3)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( ( v5_orders_2(A)
        & v2_lattice3(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => m1_subset_1(k12_lattice3(A,B,C),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k12_lattice3)).

tff(f_146,axiom,(
    ! [A,B,C] :
      ( ( v5_orders_2(A)
        & v1_lattice3(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => k13_lattice3(A,B,C) = k10_lattice3(A,B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k13_lattice3)).

tff(f_37,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => r1_orders_2(A,B,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_orders_2)).

tff(f_44,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v1_lattice3(A)
       => ~ v2_struct_0(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_lattice3)).

tff(f_122,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l28_lattice3)).

tff(f_89,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l26_lattice3)).

tff(c_52,plain,(
    v5_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_48,plain,(
    v2_lattice3('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_46,plain,(
    l1_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_44,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_42,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_144,plain,(
    ! [A_121,B_122,C_123] :
      ( k12_lattice3(A_121,B_122,C_123) = k11_lattice3(A_121,B_122,C_123)
      | ~ m1_subset_1(C_123,u1_struct_0(A_121))
      | ~ m1_subset_1(B_122,u1_struct_0(A_121))
      | ~ l1_orders_2(A_121)
      | ~ v2_lattice3(A_121)
      | ~ v5_orders_2(A_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_148,plain,(
    ! [B_122] :
      ( k12_lattice3('#skF_3',B_122,'#skF_5') = k11_lattice3('#skF_3',B_122,'#skF_5')
      | ~ m1_subset_1(B_122,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | ~ v2_lattice3('#skF_3')
      | ~ v5_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_42,c_144])).

tff(c_158,plain,(
    ! [B_124] :
      ( k12_lattice3('#skF_3',B_124,'#skF_5') = k11_lattice3('#skF_3',B_124,'#skF_5')
      | ~ m1_subset_1(B_124,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_48,c_46,c_148])).

tff(c_173,plain,(
    k12_lattice3('#skF_3','#skF_4','#skF_5') = k11_lattice3('#skF_3','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_44,c_158])).

tff(c_6,plain,(
    ! [A_5,B_6,C_7] :
      ( m1_subset_1(k12_lattice3(A_5,B_6,C_7),u1_struct_0(A_5))
      | ~ m1_subset_1(C_7,u1_struct_0(A_5))
      | ~ m1_subset_1(B_6,u1_struct_0(A_5))
      | ~ l1_orders_2(A_5)
      | ~ v2_lattice3(A_5)
      | ~ v5_orders_2(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_222,plain,
    ( m1_subset_1(k11_lattice3('#skF_3','#skF_4','#skF_5'),u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ l1_orders_2('#skF_3')
    | ~ v2_lattice3('#skF_3')
    | ~ v5_orders_2('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_173,c_6])).

tff(c_226,plain,(
    m1_subset_1(k11_lattice3('#skF_3','#skF_4','#skF_5'),u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_48,c_46,c_44,c_42,c_222])).

tff(c_50,plain,(
    v1_lattice3('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_82,plain,(
    ! [A_116,B_117,C_118] :
      ( k13_lattice3(A_116,B_117,C_118) = k10_lattice3(A_116,B_117,C_118)
      | ~ m1_subset_1(C_118,u1_struct_0(A_116))
      | ~ m1_subset_1(B_117,u1_struct_0(A_116))
      | ~ l1_orders_2(A_116)
      | ~ v1_lattice3(A_116)
      | ~ v5_orders_2(A_116) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_86,plain,(
    ! [B_117] :
      ( k13_lattice3('#skF_3',B_117,'#skF_5') = k10_lattice3('#skF_3',B_117,'#skF_5')
      | ~ m1_subset_1(B_117,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | ~ v1_lattice3('#skF_3')
      | ~ v5_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_42,c_82])).

tff(c_92,plain,(
    ! [B_117] :
      ( k13_lattice3('#skF_3',B_117,'#skF_5') = k10_lattice3('#skF_3',B_117,'#skF_5')
      | ~ m1_subset_1(B_117,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_46,c_86])).

tff(c_254,plain,(
    k13_lattice3('#skF_3',k11_lattice3('#skF_3','#skF_4','#skF_5'),'#skF_5') = k10_lattice3('#skF_3',k11_lattice3('#skF_3','#skF_4','#skF_5'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_226,c_92])).

tff(c_40,plain,(
    k13_lattice3('#skF_3',k12_lattice3('#skF_3','#skF_4','#skF_5'),'#skF_5') != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_218,plain,(
    k13_lattice3('#skF_3',k11_lattice3('#skF_3','#skF_4','#skF_5'),'#skF_5') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_173,c_40])).

tff(c_441,plain,(
    k10_lattice3('#skF_3',k11_lattice3('#skF_3','#skF_4','#skF_5'),'#skF_5') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_254,c_218])).

tff(c_54,plain,(
    v3_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_56,plain,(
    ! [A_111,B_112] :
      ( r1_orders_2(A_111,B_112,B_112)
      | ~ m1_subset_1(B_112,u1_struct_0(A_111))
      | ~ l1_orders_2(A_111)
      | ~ v3_orders_2(A_111)
      | v2_struct_0(A_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_58,plain,
    ( r1_orders_2('#skF_3','#skF_5','#skF_5')
    | ~ l1_orders_2('#skF_3')
    | ~ v3_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_56])).

tff(c_63,plain,
    ( r1_orders_2('#skF_3','#skF_5','#skF_5')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_46,c_58])).

tff(c_67,plain,(
    v2_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_63])).

tff(c_4,plain,(
    ! [A_4] :
      ( ~ v2_struct_0(A_4)
      | ~ v1_lattice3(A_4)
      | ~ l1_orders_2(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_70,plain,
    ( ~ v1_lattice3('#skF_3')
    | ~ l1_orders_2('#skF_3') ),
    inference(resolution,[status(thm)],[c_67,c_4])).

tff(c_74,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_50,c_70])).

tff(c_76,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_63])).

tff(c_455,plain,(
    ! [A_135,B_136,C_137] :
      ( r1_orders_2(A_135,k11_lattice3(A_135,B_136,C_137),C_137)
      | ~ m1_subset_1(k11_lattice3(A_135,B_136,C_137),u1_struct_0(A_135))
      | ~ m1_subset_1(C_137,u1_struct_0(A_135))
      | ~ m1_subset_1(B_136,u1_struct_0(A_135))
      | ~ l1_orders_2(A_135)
      | ~ v2_lattice3(A_135)
      | ~ v5_orders_2(A_135)
      | v2_struct_0(A_135) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_463,plain,
    ( r1_orders_2('#skF_3',k11_lattice3('#skF_3','#skF_4','#skF_5'),'#skF_5')
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ l1_orders_2('#skF_3')
    | ~ v2_lattice3('#skF_3')
    | ~ v5_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_226,c_455])).

tff(c_480,plain,
    ( r1_orders_2('#skF_3',k11_lattice3('#skF_3','#skF_4','#skF_5'),'#skF_5')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_48,c_46,c_44,c_42,c_463])).

tff(c_481,plain,(
    r1_orders_2('#skF_3',k11_lattice3('#skF_3','#skF_4','#skF_5'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_480])).

tff(c_75,plain,(
    r1_orders_2('#skF_3','#skF_5','#skF_5') ),
    inference(splitRight,[status(thm)],[c_63])).

tff(c_10,plain,(
    ! [A_8,C_44,B_32,D_50] :
      ( r1_orders_2(A_8,C_44,'#skF_1'(A_8,B_32,C_44,D_50))
      | k10_lattice3(A_8,B_32,C_44) = D_50
      | ~ r1_orders_2(A_8,C_44,D_50)
      | ~ r1_orders_2(A_8,B_32,D_50)
      | ~ m1_subset_1(D_50,u1_struct_0(A_8))
      | ~ m1_subset_1(C_44,u1_struct_0(A_8))
      | ~ m1_subset_1(B_32,u1_struct_0(A_8))
      | ~ l1_orders_2(A_8)
      | ~ v1_lattice3(A_8)
      | ~ v5_orders_2(A_8)
      | v2_struct_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_989,plain,(
    ! [A_155,D_156,B_157,C_158] :
      ( ~ r1_orders_2(A_155,D_156,'#skF_1'(A_155,B_157,C_158,D_156))
      | k10_lattice3(A_155,B_157,C_158) = D_156
      | ~ r1_orders_2(A_155,C_158,D_156)
      | ~ r1_orders_2(A_155,B_157,D_156)
      | ~ m1_subset_1(D_156,u1_struct_0(A_155))
      | ~ m1_subset_1(C_158,u1_struct_0(A_155))
      | ~ m1_subset_1(B_157,u1_struct_0(A_155))
      | ~ l1_orders_2(A_155)
      | ~ v1_lattice3(A_155)
      | ~ v5_orders_2(A_155)
      | v2_struct_0(A_155) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_2922,plain,(
    ! [A_191,B_192,D_193] :
      ( k10_lattice3(A_191,B_192,D_193) = D_193
      | ~ r1_orders_2(A_191,D_193,D_193)
      | ~ r1_orders_2(A_191,B_192,D_193)
      | ~ m1_subset_1(D_193,u1_struct_0(A_191))
      | ~ m1_subset_1(B_192,u1_struct_0(A_191))
      | ~ l1_orders_2(A_191)
      | ~ v1_lattice3(A_191)
      | ~ v5_orders_2(A_191)
      | v2_struct_0(A_191) ) ),
    inference(resolution,[status(thm)],[c_10,c_989])).

tff(c_2972,plain,(
    ! [B_192] :
      ( k10_lattice3('#skF_3',B_192,'#skF_5') = '#skF_5'
      | ~ r1_orders_2('#skF_3',B_192,'#skF_5')
      | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
      | ~ m1_subset_1(B_192,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | ~ v1_lattice3('#skF_3')
      | ~ v5_orders_2('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_75,c_2922])).

tff(c_3064,plain,(
    ! [B_192] :
      ( k10_lattice3('#skF_3',B_192,'#skF_5') = '#skF_5'
      | ~ r1_orders_2('#skF_3',B_192,'#skF_5')
      | ~ m1_subset_1(B_192,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_46,c_42,c_2972])).

tff(c_5508,plain,(
    ! [B_230] :
      ( k10_lattice3('#skF_3',B_230,'#skF_5') = '#skF_5'
      | ~ r1_orders_2('#skF_3',B_230,'#skF_5')
      | ~ m1_subset_1(B_230,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_3064])).

tff(c_5534,plain,
    ( k10_lattice3('#skF_3',k11_lattice3('#skF_3','#skF_4','#skF_5'),'#skF_5') = '#skF_5'
    | ~ r1_orders_2('#skF_3',k11_lattice3('#skF_3','#skF_4','#skF_5'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_226,c_5508])).

tff(c_5566,plain,(
    k10_lattice3('#skF_3',k11_lattice3('#skF_3','#skF_4','#skF_5'),'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_481,c_5534])).

tff(c_5568,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_441,c_5566])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:17:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.19/2.62  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.19/2.63  
% 7.19/2.63  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.19/2.63  %$ r1_orders_2 > m1_subset_1 > v5_orders_2 > v3_orders_2 > v2_struct_0 > v2_lattice3 > v1_lattice3 > l1_orders_2 > k13_lattice3 > k12_lattice3 > k11_lattice3 > k10_lattice3 > #nlpp > u1_struct_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 7.19/2.63  
% 7.19/2.63  %Foreground sorts:
% 7.19/2.63  
% 7.19/2.63  
% 7.19/2.63  %Background operators:
% 7.19/2.63  
% 7.19/2.63  
% 7.19/2.63  %Foreground operators:
% 7.19/2.63  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 7.19/2.63  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 7.19/2.63  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.19/2.63  tff(k13_lattice3, type, k13_lattice3: ($i * $i * $i) > $i).
% 7.19/2.63  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 7.19/2.63  tff(k10_lattice3, type, k10_lattice3: ($i * $i * $i) > $i).
% 7.19/2.63  tff(k11_lattice3, type, k11_lattice3: ($i * $i * $i) > $i).
% 7.19/2.63  tff(v1_lattice3, type, v1_lattice3: $i > $o).
% 7.19/2.63  tff('#skF_5', type, '#skF_5': $i).
% 7.19/2.63  tff(k12_lattice3, type, k12_lattice3: ($i * $i * $i) > $i).
% 7.19/2.63  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 7.19/2.63  tff('#skF_3', type, '#skF_3': $i).
% 7.19/2.63  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 7.19/2.63  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 7.19/2.63  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.19/2.63  tff('#skF_4', type, '#skF_4': $i).
% 7.19/2.63  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.19/2.63  tff(v2_lattice3, type, v2_lattice3: $i > $o).
% 7.19/2.63  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 7.19/2.63  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 7.19/2.63  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.19/2.63  
% 7.19/2.64  tff(f_165, negated_conjecture, ~(![A]: (((((v3_orders_2(A) & v5_orders_2(A)) & v1_lattice3(A)) & v2_lattice3(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (k13_lattice3(A, k12_lattice3(A, B, C), C) = C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_lattice3)).
% 7.19/2.64  tff(f_134, axiom, (![A, B, C]: (((((v5_orders_2(A) & v2_lattice3(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (k12_lattice3(A, B, C) = k11_lattice3(A, B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k12_lattice3)).
% 7.19/2.64  tff(f_56, axiom, (![A, B, C]: (((((v5_orders_2(A) & v2_lattice3(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => m1_subset_1(k12_lattice3(A, B, C), u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k12_lattice3)).
% 7.19/2.64  tff(f_146, axiom, (![A, B, C]: (((((v5_orders_2(A) & v1_lattice3(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (k13_lattice3(A, B, C) = k10_lattice3(A, B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k13_lattice3)).
% 7.19/2.64  tff(f_37, axiom, (![A]: (((~v2_struct_0(A) & v3_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => r1_orders_2(A, B, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_orders_2)).
% 7.19/2.64  tff(f_44, axiom, (![A]: (l1_orders_2(A) => (v1_lattice3(A) => ~v2_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_lattice3)).
% 7.19/2.64  tff(f_122, axiom, (![A]: ((((~v2_struct_0(A) & v5_orders_2(A)) & v2_lattice3(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => ((D = k11_lattice3(A, B, C)) <=> ((r1_orders_2(A, D, B) & r1_orders_2(A, D, C)) & (![E]: (m1_subset_1(E, u1_struct_0(A)) => ((r1_orders_2(A, E, B) & r1_orders_2(A, E, C)) => r1_orders_2(A, E, D)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l28_lattice3)).
% 7.19/2.64  tff(f_89, axiom, (![A]: ((((~v2_struct_0(A) & v5_orders_2(A)) & v1_lattice3(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => ((D = k10_lattice3(A, B, C)) <=> ((r1_orders_2(A, B, D) & r1_orders_2(A, C, D)) & (![E]: (m1_subset_1(E, u1_struct_0(A)) => ((r1_orders_2(A, B, E) & r1_orders_2(A, C, E)) => r1_orders_2(A, D, E)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l26_lattice3)).
% 7.19/2.64  tff(c_52, plain, (v5_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_165])).
% 7.19/2.64  tff(c_48, plain, (v2_lattice3('#skF_3')), inference(cnfTransformation, [status(thm)], [f_165])).
% 7.19/2.64  tff(c_46, plain, (l1_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_165])).
% 7.19/2.64  tff(c_44, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_165])).
% 7.19/2.64  tff(c_42, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_165])).
% 7.19/2.64  tff(c_144, plain, (![A_121, B_122, C_123]: (k12_lattice3(A_121, B_122, C_123)=k11_lattice3(A_121, B_122, C_123) | ~m1_subset_1(C_123, u1_struct_0(A_121)) | ~m1_subset_1(B_122, u1_struct_0(A_121)) | ~l1_orders_2(A_121) | ~v2_lattice3(A_121) | ~v5_orders_2(A_121))), inference(cnfTransformation, [status(thm)], [f_134])).
% 7.19/2.64  tff(c_148, plain, (![B_122]: (k12_lattice3('#skF_3', B_122, '#skF_5')=k11_lattice3('#skF_3', B_122, '#skF_5') | ~m1_subset_1(B_122, u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v2_lattice3('#skF_3') | ~v5_orders_2('#skF_3'))), inference(resolution, [status(thm)], [c_42, c_144])).
% 7.19/2.64  tff(c_158, plain, (![B_124]: (k12_lattice3('#skF_3', B_124, '#skF_5')=k11_lattice3('#skF_3', B_124, '#skF_5') | ~m1_subset_1(B_124, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_48, c_46, c_148])).
% 7.19/2.64  tff(c_173, plain, (k12_lattice3('#skF_3', '#skF_4', '#skF_5')=k11_lattice3('#skF_3', '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_44, c_158])).
% 7.19/2.64  tff(c_6, plain, (![A_5, B_6, C_7]: (m1_subset_1(k12_lattice3(A_5, B_6, C_7), u1_struct_0(A_5)) | ~m1_subset_1(C_7, u1_struct_0(A_5)) | ~m1_subset_1(B_6, u1_struct_0(A_5)) | ~l1_orders_2(A_5) | ~v2_lattice3(A_5) | ~v5_orders_2(A_5))), inference(cnfTransformation, [status(thm)], [f_56])).
% 7.19/2.64  tff(c_222, plain, (m1_subset_1(k11_lattice3('#skF_3', '#skF_4', '#skF_5'), u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v2_lattice3('#skF_3') | ~v5_orders_2('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_173, c_6])).
% 7.19/2.64  tff(c_226, plain, (m1_subset_1(k11_lattice3('#skF_3', '#skF_4', '#skF_5'), u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_48, c_46, c_44, c_42, c_222])).
% 7.19/2.64  tff(c_50, plain, (v1_lattice3('#skF_3')), inference(cnfTransformation, [status(thm)], [f_165])).
% 7.19/2.64  tff(c_82, plain, (![A_116, B_117, C_118]: (k13_lattice3(A_116, B_117, C_118)=k10_lattice3(A_116, B_117, C_118) | ~m1_subset_1(C_118, u1_struct_0(A_116)) | ~m1_subset_1(B_117, u1_struct_0(A_116)) | ~l1_orders_2(A_116) | ~v1_lattice3(A_116) | ~v5_orders_2(A_116))), inference(cnfTransformation, [status(thm)], [f_146])).
% 7.19/2.64  tff(c_86, plain, (![B_117]: (k13_lattice3('#skF_3', B_117, '#skF_5')=k10_lattice3('#skF_3', B_117, '#skF_5') | ~m1_subset_1(B_117, u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v1_lattice3('#skF_3') | ~v5_orders_2('#skF_3'))), inference(resolution, [status(thm)], [c_42, c_82])).
% 7.19/2.64  tff(c_92, plain, (![B_117]: (k13_lattice3('#skF_3', B_117, '#skF_5')=k10_lattice3('#skF_3', B_117, '#skF_5') | ~m1_subset_1(B_117, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_46, c_86])).
% 7.19/2.64  tff(c_254, plain, (k13_lattice3('#skF_3', k11_lattice3('#skF_3', '#skF_4', '#skF_5'), '#skF_5')=k10_lattice3('#skF_3', k11_lattice3('#skF_3', '#skF_4', '#skF_5'), '#skF_5')), inference(resolution, [status(thm)], [c_226, c_92])).
% 7.19/2.64  tff(c_40, plain, (k13_lattice3('#skF_3', k12_lattice3('#skF_3', '#skF_4', '#skF_5'), '#skF_5')!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_165])).
% 7.19/2.64  tff(c_218, plain, (k13_lattice3('#skF_3', k11_lattice3('#skF_3', '#skF_4', '#skF_5'), '#skF_5')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_173, c_40])).
% 7.19/2.64  tff(c_441, plain, (k10_lattice3('#skF_3', k11_lattice3('#skF_3', '#skF_4', '#skF_5'), '#skF_5')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_254, c_218])).
% 7.19/2.64  tff(c_54, plain, (v3_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_165])).
% 7.19/2.64  tff(c_56, plain, (![A_111, B_112]: (r1_orders_2(A_111, B_112, B_112) | ~m1_subset_1(B_112, u1_struct_0(A_111)) | ~l1_orders_2(A_111) | ~v3_orders_2(A_111) | v2_struct_0(A_111))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.19/2.64  tff(c_58, plain, (r1_orders_2('#skF_3', '#skF_5', '#skF_5') | ~l1_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_42, c_56])).
% 7.19/2.64  tff(c_63, plain, (r1_orders_2('#skF_3', '#skF_5', '#skF_5') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_46, c_58])).
% 7.19/2.64  tff(c_67, plain, (v2_struct_0('#skF_3')), inference(splitLeft, [status(thm)], [c_63])).
% 7.19/2.64  tff(c_4, plain, (![A_4]: (~v2_struct_0(A_4) | ~v1_lattice3(A_4) | ~l1_orders_2(A_4))), inference(cnfTransformation, [status(thm)], [f_44])).
% 7.19/2.64  tff(c_70, plain, (~v1_lattice3('#skF_3') | ~l1_orders_2('#skF_3')), inference(resolution, [status(thm)], [c_67, c_4])).
% 7.19/2.64  tff(c_74, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_50, c_70])).
% 7.19/2.64  tff(c_76, plain, (~v2_struct_0('#skF_3')), inference(splitRight, [status(thm)], [c_63])).
% 7.19/2.64  tff(c_455, plain, (![A_135, B_136, C_137]: (r1_orders_2(A_135, k11_lattice3(A_135, B_136, C_137), C_137) | ~m1_subset_1(k11_lattice3(A_135, B_136, C_137), u1_struct_0(A_135)) | ~m1_subset_1(C_137, u1_struct_0(A_135)) | ~m1_subset_1(B_136, u1_struct_0(A_135)) | ~l1_orders_2(A_135) | ~v2_lattice3(A_135) | ~v5_orders_2(A_135) | v2_struct_0(A_135))), inference(cnfTransformation, [status(thm)], [f_122])).
% 7.19/2.64  tff(c_463, plain, (r1_orders_2('#skF_3', k11_lattice3('#skF_3', '#skF_4', '#skF_5'), '#skF_5') | ~m1_subset_1('#skF_5', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v2_lattice3('#skF_3') | ~v5_orders_2('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_226, c_455])).
% 7.19/2.64  tff(c_480, plain, (r1_orders_2('#skF_3', k11_lattice3('#skF_3', '#skF_4', '#skF_5'), '#skF_5') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_48, c_46, c_44, c_42, c_463])).
% 7.19/2.64  tff(c_481, plain, (r1_orders_2('#skF_3', k11_lattice3('#skF_3', '#skF_4', '#skF_5'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_76, c_480])).
% 7.19/2.64  tff(c_75, plain, (r1_orders_2('#skF_3', '#skF_5', '#skF_5')), inference(splitRight, [status(thm)], [c_63])).
% 7.19/2.64  tff(c_10, plain, (![A_8, C_44, B_32, D_50]: (r1_orders_2(A_8, C_44, '#skF_1'(A_8, B_32, C_44, D_50)) | k10_lattice3(A_8, B_32, C_44)=D_50 | ~r1_orders_2(A_8, C_44, D_50) | ~r1_orders_2(A_8, B_32, D_50) | ~m1_subset_1(D_50, u1_struct_0(A_8)) | ~m1_subset_1(C_44, u1_struct_0(A_8)) | ~m1_subset_1(B_32, u1_struct_0(A_8)) | ~l1_orders_2(A_8) | ~v1_lattice3(A_8) | ~v5_orders_2(A_8) | v2_struct_0(A_8))), inference(cnfTransformation, [status(thm)], [f_89])).
% 7.19/2.64  tff(c_989, plain, (![A_155, D_156, B_157, C_158]: (~r1_orders_2(A_155, D_156, '#skF_1'(A_155, B_157, C_158, D_156)) | k10_lattice3(A_155, B_157, C_158)=D_156 | ~r1_orders_2(A_155, C_158, D_156) | ~r1_orders_2(A_155, B_157, D_156) | ~m1_subset_1(D_156, u1_struct_0(A_155)) | ~m1_subset_1(C_158, u1_struct_0(A_155)) | ~m1_subset_1(B_157, u1_struct_0(A_155)) | ~l1_orders_2(A_155) | ~v1_lattice3(A_155) | ~v5_orders_2(A_155) | v2_struct_0(A_155))), inference(cnfTransformation, [status(thm)], [f_89])).
% 7.19/2.64  tff(c_2922, plain, (![A_191, B_192, D_193]: (k10_lattice3(A_191, B_192, D_193)=D_193 | ~r1_orders_2(A_191, D_193, D_193) | ~r1_orders_2(A_191, B_192, D_193) | ~m1_subset_1(D_193, u1_struct_0(A_191)) | ~m1_subset_1(B_192, u1_struct_0(A_191)) | ~l1_orders_2(A_191) | ~v1_lattice3(A_191) | ~v5_orders_2(A_191) | v2_struct_0(A_191))), inference(resolution, [status(thm)], [c_10, c_989])).
% 7.19/2.64  tff(c_2972, plain, (![B_192]: (k10_lattice3('#skF_3', B_192, '#skF_5')='#skF_5' | ~r1_orders_2('#skF_3', B_192, '#skF_5') | ~m1_subset_1('#skF_5', u1_struct_0('#skF_3')) | ~m1_subset_1(B_192, u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v1_lattice3('#skF_3') | ~v5_orders_2('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_75, c_2922])).
% 7.19/2.64  tff(c_3064, plain, (![B_192]: (k10_lattice3('#skF_3', B_192, '#skF_5')='#skF_5' | ~r1_orders_2('#skF_3', B_192, '#skF_5') | ~m1_subset_1(B_192, u1_struct_0('#skF_3')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_46, c_42, c_2972])).
% 7.19/2.64  tff(c_5508, plain, (![B_230]: (k10_lattice3('#skF_3', B_230, '#skF_5')='#skF_5' | ~r1_orders_2('#skF_3', B_230, '#skF_5') | ~m1_subset_1(B_230, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_76, c_3064])).
% 7.19/2.64  tff(c_5534, plain, (k10_lattice3('#skF_3', k11_lattice3('#skF_3', '#skF_4', '#skF_5'), '#skF_5')='#skF_5' | ~r1_orders_2('#skF_3', k11_lattice3('#skF_3', '#skF_4', '#skF_5'), '#skF_5')), inference(resolution, [status(thm)], [c_226, c_5508])).
% 7.19/2.64  tff(c_5566, plain, (k10_lattice3('#skF_3', k11_lattice3('#skF_3', '#skF_4', '#skF_5'), '#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_481, c_5534])).
% 7.19/2.64  tff(c_5568, plain, $false, inference(negUnitSimplification, [status(thm)], [c_441, c_5566])).
% 7.19/2.64  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.19/2.64  
% 7.19/2.64  Inference rules
% 7.19/2.64  ----------------------
% 7.19/2.64  #Ref     : 0
% 7.19/2.64  #Sup     : 1138
% 7.19/2.64  #Fact    : 0
% 7.19/2.64  #Define  : 0
% 7.19/2.64  #Split   : 5
% 7.19/2.64  #Chain   : 0
% 7.19/2.64  #Close   : 0
% 7.19/2.64  
% 7.19/2.64  Ordering : KBO
% 7.19/2.64  
% 7.19/2.64  Simplification rules
% 7.19/2.64  ----------------------
% 7.19/2.64  #Subsume      : 4
% 7.19/2.64  #Demod        : 3283
% 7.19/2.64  #Tautology    : 430
% 7.19/2.64  #SimpNegUnit  : 450
% 7.19/2.64  #BackRed      : 107
% 7.19/2.64  
% 7.19/2.64  #Partial instantiations: 0
% 7.19/2.64  #Strategies tried      : 1
% 7.19/2.64  
% 7.19/2.64  Timing (in seconds)
% 7.19/2.64  ----------------------
% 7.19/2.65  Preprocessing        : 0.37
% 7.19/2.65  Parsing              : 0.19
% 7.19/2.65  CNF conversion       : 0.03
% 7.19/2.65  Main loop            : 1.49
% 7.19/2.65  Inferencing          : 0.40
% 7.19/2.65  Reduction            : 0.64
% 7.19/2.65  Demodulation         : 0.50
% 7.19/2.65  BG Simplification    : 0.06
% 7.19/2.65  Subsumption          : 0.31
% 7.19/2.65  Abstraction          : 0.08
% 7.19/2.65  MUC search           : 0.00
% 7.19/2.65  Cooper               : 0.00
% 7.19/2.65  Total                : 1.90
% 7.19/2.65  Index Insertion      : 0.00
% 7.19/2.65  Index Deletion       : 0.00
% 7.19/2.65  Index Matching       : 0.00
% 7.19/2.65  BG Taut test         : 0.00
%------------------------------------------------------------------------------
