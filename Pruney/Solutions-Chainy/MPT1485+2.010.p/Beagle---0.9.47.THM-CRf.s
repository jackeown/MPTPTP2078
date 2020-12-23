%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:41 EST 2020

% Result     : Theorem 4.62s
% Output     : CNFRefutation 4.62s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 194 expanded)
%              Number of leaves         :   30 (  84 expanded)
%              Depth                    :   15
%              Number of atoms          :  251 ( 756 expanded)
%              Number of equality atoms :   40 (  87 expanded)
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
               => k12_lattice3(A,B,k13_lattice3(A,B,C)) = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_lattice3)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( ( l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => m1_subset_1(k10_lattice3(A,B,C),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k10_lattice3)).

tff(f_142,axiom,(
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
     => k12_lattice3(A,B,C) = k12_lattice3(A,C,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k12_lattice3)).

tff(f_154,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l26_lattice3)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l28_lattice3)).

tff(c_46,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_44,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_48,plain,(
    l1_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_8,plain,(
    ! [A_8,B_9,C_10] :
      ( m1_subset_1(k10_lattice3(A_8,B_9,C_10),u1_struct_0(A_8))
      | ~ m1_subset_1(C_10,u1_struct_0(A_8))
      | ~ m1_subset_1(B_9,u1_struct_0(A_8))
      | ~ l1_orders_2(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

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

tff(c_122,plain,(
    ! [B_123] :
      ( k12_lattice3('#skF_3',B_123,'#skF_4') = k11_lattice3('#skF_3',B_123,'#skF_4')
      | ~ m1_subset_1(B_123,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_50,c_48,c_90])).

tff(c_126,plain,(
    ! [B_9,C_10] :
      ( k12_lattice3('#skF_3',k10_lattice3('#skF_3',B_9,C_10),'#skF_4') = k11_lattice3('#skF_3',k10_lattice3('#skF_3',B_9,C_10),'#skF_4')
      | ~ m1_subset_1(C_10,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(B_9,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_8,c_122])).

tff(c_436,plain,(
    ! [B_153,C_154] :
      ( k12_lattice3('#skF_3',k10_lattice3('#skF_3',B_153,C_154),'#skF_4') = k11_lattice3('#skF_3',k10_lattice3('#skF_3',B_153,C_154),'#skF_4')
      | ~ m1_subset_1(C_154,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(B_153,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_126])).

tff(c_449,plain,(
    ! [B_155] :
      ( k12_lattice3('#skF_3',k10_lattice3('#skF_3',B_155,'#skF_5'),'#skF_4') = k11_lattice3('#skF_3',k10_lattice3('#skF_3',B_155,'#skF_5'),'#skF_4')
      | ~ m1_subset_1(B_155,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_44,c_436])).

tff(c_464,plain,(
    k12_lattice3('#skF_3',k10_lattice3('#skF_3','#skF_4','#skF_5'),'#skF_4') = k11_lattice3('#skF_3',k10_lattice3('#skF_3','#skF_4','#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_449])).

tff(c_176,plain,(
    ! [A_128,C_129,B_130] :
      ( k12_lattice3(A_128,C_129,B_130) = k12_lattice3(A_128,B_130,C_129)
      | ~ m1_subset_1(C_129,u1_struct_0(A_128))
      | ~ m1_subset_1(B_130,u1_struct_0(A_128))
      | ~ l1_orders_2(A_128)
      | ~ v2_lattice3(A_128)
      | ~ v5_orders_2(A_128) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_182,plain,(
    ! [B_130] :
      ( k12_lattice3('#skF_3',B_130,'#skF_4') = k12_lattice3('#skF_3','#skF_4',B_130)
      | ~ m1_subset_1(B_130,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | ~ v2_lattice3('#skF_3')
      | ~ v5_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_46,c_176])).

tff(c_254,plain,(
    ! [B_136] :
      ( k12_lattice3('#skF_3',B_136,'#skF_4') = k12_lattice3('#skF_3','#skF_4',B_136)
      | ~ m1_subset_1(B_136,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_50,c_48,c_182])).

tff(c_258,plain,(
    ! [B_9,C_10] :
      ( k12_lattice3('#skF_3',k10_lattice3('#skF_3',B_9,C_10),'#skF_4') = k12_lattice3('#skF_3','#skF_4',k10_lattice3('#skF_3',B_9,C_10))
      | ~ m1_subset_1(C_10,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(B_9,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_8,c_254])).

tff(c_563,plain,(
    ! [B_168,C_169] :
      ( k12_lattice3('#skF_3',k10_lattice3('#skF_3',B_168,C_169),'#skF_4') = k12_lattice3('#skF_3','#skF_4',k10_lattice3('#skF_3',B_168,C_169))
      | ~ m1_subset_1(C_169,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(B_168,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_258])).

tff(c_576,plain,(
    ! [B_170] :
      ( k12_lattice3('#skF_3',k10_lattice3('#skF_3',B_170,'#skF_5'),'#skF_4') = k12_lattice3('#skF_3','#skF_4',k10_lattice3('#skF_3',B_170,'#skF_5'))
      | ~ m1_subset_1(B_170,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_44,c_563])).

tff(c_586,plain,(
    k12_lattice3('#skF_3',k10_lattice3('#skF_3','#skF_4','#skF_5'),'#skF_4') = k12_lattice3('#skF_3','#skF_4',k10_lattice3('#skF_3','#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_46,c_576])).

tff(c_593,plain,(
    k12_lattice3('#skF_3','#skF_4',k10_lattice3('#skF_3','#skF_4','#skF_5')) = k11_lattice3('#skF_3',k10_lattice3('#skF_3','#skF_4','#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_464,c_586])).

tff(c_52,plain,(
    v1_lattice3('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_146,plain,(
    ! [A_124,B_125,C_126] :
      ( k13_lattice3(A_124,B_125,C_126) = k10_lattice3(A_124,B_125,C_126)
      | ~ m1_subset_1(C_126,u1_struct_0(A_124))
      | ~ m1_subset_1(B_125,u1_struct_0(A_124))
      | ~ l1_orders_2(A_124)
      | ~ v1_lattice3(A_124)
      | ~ v5_orders_2(A_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_150,plain,(
    ! [B_125] :
      ( k13_lattice3('#skF_3',B_125,'#skF_5') = k10_lattice3('#skF_3',B_125,'#skF_5')
      | ~ m1_subset_1(B_125,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | ~ v1_lattice3('#skF_3')
      | ~ v5_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_44,c_146])).

tff(c_160,plain,(
    ! [B_127] :
      ( k13_lattice3('#skF_3',B_127,'#skF_5') = k10_lattice3('#skF_3',B_127,'#skF_5')
      | ~ m1_subset_1(B_127,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_48,c_150])).

tff(c_175,plain,(
    k13_lattice3('#skF_3','#skF_4','#skF_5') = k10_lattice3('#skF_3','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_46,c_160])).

tff(c_42,plain,(
    k12_lattice3('#skF_3','#skF_4',k13_lattice3('#skF_3','#skF_4','#skF_5')) != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_194,plain,(
    k12_lattice3('#skF_3','#skF_4',k10_lattice3('#skF_3','#skF_4','#skF_5')) != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_175,c_42])).

tff(c_616,plain,(
    k11_lattice3('#skF_3',k10_lattice3('#skF_3','#skF_4','#skF_5'),'#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_593,c_194])).

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

tff(c_489,plain,(
    ! [A_157,B_158,C_159] :
      ( r1_orders_2(A_157,B_158,k10_lattice3(A_157,B_158,C_159))
      | ~ m1_subset_1(k10_lattice3(A_157,B_158,C_159),u1_struct_0(A_157))
      | ~ m1_subset_1(C_159,u1_struct_0(A_157))
      | ~ m1_subset_1(B_158,u1_struct_0(A_157))
      | ~ l1_orders_2(A_157)
      | ~ v1_lattice3(A_157)
      | ~ v5_orders_2(A_157)
      | v2_struct_0(A_157) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_492,plain,(
    ! [A_8,B_9,C_10] :
      ( r1_orders_2(A_8,B_9,k10_lattice3(A_8,B_9,C_10))
      | ~ v1_lattice3(A_8)
      | ~ v5_orders_2(A_8)
      | v2_struct_0(A_8)
      | ~ m1_subset_1(C_10,u1_struct_0(A_8))
      | ~ m1_subset_1(B_9,u1_struct_0(A_8))
      | ~ l1_orders_2(A_8) ) ),
    inference(resolution,[status(thm)],[c_8,c_489])).

tff(c_62,plain,
    ( r1_orders_2('#skF_3','#skF_4','#skF_4')
    | ~ l1_orders_2('#skF_3')
    | ~ v3_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_58])).

tff(c_68,plain,
    ( r1_orders_2('#skF_3','#skF_4','#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_48,c_62])).

tff(c_79,plain,(
    r1_orders_2('#skF_3','#skF_4','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_68])).

tff(c_26,plain,(
    ! [A_57,B_81,C_93,D_99] :
      ( r1_orders_2(A_57,'#skF_2'(A_57,B_81,C_93,D_99),C_93)
      | k11_lattice3(A_57,B_81,C_93) = D_99
      | ~ r1_orders_2(A_57,D_99,C_93)
      | ~ r1_orders_2(A_57,D_99,B_81)
      | ~ m1_subset_1(D_99,u1_struct_0(A_57))
      | ~ m1_subset_1(C_93,u1_struct_0(A_57))
      | ~ m1_subset_1(B_81,u1_struct_0(A_57))
      | ~ l1_orders_2(A_57)
      | ~ v2_lattice3(A_57)
      | ~ v5_orders_2(A_57)
      | v2_struct_0(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_1351,plain,(
    ! [A_231,B_232,C_233,D_234] :
      ( ~ r1_orders_2(A_231,'#skF_2'(A_231,B_232,C_233,D_234),D_234)
      | k11_lattice3(A_231,B_232,C_233) = D_234
      | ~ r1_orders_2(A_231,D_234,C_233)
      | ~ r1_orders_2(A_231,D_234,B_232)
      | ~ m1_subset_1(D_234,u1_struct_0(A_231))
      | ~ m1_subset_1(C_233,u1_struct_0(A_231))
      | ~ m1_subset_1(B_232,u1_struct_0(A_231))
      | ~ l1_orders_2(A_231)
      | ~ v2_lattice3(A_231)
      | ~ v5_orders_2(A_231)
      | v2_struct_0(A_231) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_1379,plain,(
    ! [A_239,B_240,C_241] :
      ( k11_lattice3(A_239,B_240,C_241) = C_241
      | ~ r1_orders_2(A_239,C_241,C_241)
      | ~ r1_orders_2(A_239,C_241,B_240)
      | ~ m1_subset_1(C_241,u1_struct_0(A_239))
      | ~ m1_subset_1(B_240,u1_struct_0(A_239))
      | ~ l1_orders_2(A_239)
      | ~ v2_lattice3(A_239)
      | ~ v5_orders_2(A_239)
      | v2_struct_0(A_239) ) ),
    inference(resolution,[status(thm)],[c_26,c_1351])).

tff(c_1383,plain,(
    ! [B_240] :
      ( k11_lattice3('#skF_3',B_240,'#skF_4') = '#skF_4'
      | ~ r1_orders_2('#skF_3','#skF_4',B_240)
      | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
      | ~ m1_subset_1(B_240,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | ~ v2_lattice3('#skF_3')
      | ~ v5_orders_2('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_79,c_1379])).

tff(c_1389,plain,(
    ! [B_240] :
      ( k11_lattice3('#skF_3',B_240,'#skF_4') = '#skF_4'
      | ~ r1_orders_2('#skF_3','#skF_4',B_240)
      | ~ m1_subset_1(B_240,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_50,c_48,c_46,c_1383])).

tff(c_1395,plain,(
    ! [B_242] :
      ( k11_lattice3('#skF_3',B_242,'#skF_4') = '#skF_4'
      | ~ r1_orders_2('#skF_3','#skF_4',B_242)
      | ~ m1_subset_1(B_242,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_1389])).

tff(c_1403,plain,(
    ! [B_9,C_10] :
      ( k11_lattice3('#skF_3',k10_lattice3('#skF_3',B_9,C_10),'#skF_4') = '#skF_4'
      | ~ r1_orders_2('#skF_3','#skF_4',k10_lattice3('#skF_3',B_9,C_10))
      | ~ m1_subset_1(C_10,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(B_9,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_8,c_1395])).

tff(c_1495,plain,(
    ! [B_248,C_249] :
      ( k11_lattice3('#skF_3',k10_lattice3('#skF_3',B_248,C_249),'#skF_4') = '#skF_4'
      | ~ r1_orders_2('#skF_3','#skF_4',k10_lattice3('#skF_3',B_248,C_249))
      | ~ m1_subset_1(C_249,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(B_248,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_1403])).

tff(c_1509,plain,(
    ! [C_10] :
      ( k11_lattice3('#skF_3',k10_lattice3('#skF_3','#skF_4',C_10),'#skF_4') = '#skF_4'
      | ~ v1_lattice3('#skF_3')
      | ~ v5_orders_2('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ m1_subset_1(C_10,u1_struct_0('#skF_3'))
      | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_492,c_1495])).

tff(c_1520,plain,(
    ! [C_10] :
      ( k11_lattice3('#skF_3',k10_lattice3('#skF_3','#skF_4',C_10),'#skF_4') = '#skF_4'
      | v2_struct_0('#skF_3')
      | ~ m1_subset_1(C_10,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_54,c_52,c_1509])).

tff(c_1571,plain,(
    ! [C_251] :
      ( k11_lattice3('#skF_3',k10_lattice3('#skF_3','#skF_4',C_251),'#skF_4') = '#skF_4'
      | ~ m1_subset_1(C_251,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_1520])).

tff(c_1582,plain,(
    k11_lattice3('#skF_3',k10_lattice3('#skF_3','#skF_4','#skF_5'),'#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_44,c_1571])).

tff(c_1596,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_616,c_1582])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:50:53 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.62/2.07  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.62/2.08  
% 4.62/2.08  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.62/2.08  %$ r1_orders_2 > m1_subset_1 > v5_orders_2 > v3_orders_2 > v2_struct_0 > v2_lattice3 > v1_lattice3 > l1_orders_2 > k13_lattice3 > k12_lattice3 > k11_lattice3 > k10_lattice3 > #nlpp > u1_struct_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 4.62/2.08  
% 4.62/2.08  %Foreground sorts:
% 4.62/2.08  
% 4.62/2.08  
% 4.62/2.08  %Background operators:
% 4.62/2.08  
% 4.62/2.08  
% 4.62/2.08  %Foreground operators:
% 4.62/2.08  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.62/2.08  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 4.62/2.08  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.62/2.08  tff(k13_lattice3, type, k13_lattice3: ($i * $i * $i) > $i).
% 4.62/2.08  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 4.62/2.08  tff(k10_lattice3, type, k10_lattice3: ($i * $i * $i) > $i).
% 4.62/2.08  tff(k11_lattice3, type, k11_lattice3: ($i * $i * $i) > $i).
% 4.62/2.08  tff(v1_lattice3, type, v1_lattice3: $i > $o).
% 4.62/2.08  tff('#skF_5', type, '#skF_5': $i).
% 4.62/2.08  tff(k12_lattice3, type, k12_lattice3: ($i * $i * $i) > $i).
% 4.62/2.08  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 4.62/2.08  tff('#skF_3', type, '#skF_3': $i).
% 4.62/2.08  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 4.62/2.08  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 4.62/2.08  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.62/2.08  tff('#skF_4', type, '#skF_4': $i).
% 4.62/2.08  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.62/2.08  tff(v2_lattice3, type, v2_lattice3: $i > $o).
% 4.62/2.08  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 4.62/2.08  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.62/2.08  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.62/2.08  
% 4.62/2.10  tff(f_173, negated_conjecture, ~(![A]: (((((v3_orders_2(A) & v5_orders_2(A)) & v1_lattice3(A)) & v2_lattice3(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (k12_lattice3(A, B, k13_lattice3(A, B, C)) = B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_lattice3)).
% 4.62/2.10  tff(f_64, axiom, (![A, B, C]: (((l1_orders_2(A) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => m1_subset_1(k10_lattice3(A, B, C), u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k10_lattice3)).
% 4.62/2.10  tff(f_142, axiom, (![A, B, C]: (((((v5_orders_2(A) & v2_lattice3(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (k12_lattice3(A, B, C) = k11_lattice3(A, B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k12_lattice3)).
% 4.62/2.10  tff(f_56, axiom, (![A, B, C]: (((((v5_orders_2(A) & v2_lattice3(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (k12_lattice3(A, B, C) = k12_lattice3(A, C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k12_lattice3)).
% 4.62/2.10  tff(f_154, axiom, (![A, B, C]: (((((v5_orders_2(A) & v1_lattice3(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (k13_lattice3(A, B, C) = k10_lattice3(A, B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k13_lattice3)).
% 4.62/2.10  tff(f_37, axiom, (![A]: (((~v2_struct_0(A) & v3_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => r1_orders_2(A, B, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_orders_2)).
% 4.62/2.10  tff(f_44, axiom, (![A]: (l1_orders_2(A) => (v1_lattice3(A) => ~v2_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_lattice3)).
% 4.62/2.10  tff(f_97, axiom, (![A]: ((((~v2_struct_0(A) & v5_orders_2(A)) & v1_lattice3(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => ((D = k10_lattice3(A, B, C)) <=> ((r1_orders_2(A, B, D) & r1_orders_2(A, C, D)) & (![E]: (m1_subset_1(E, u1_struct_0(A)) => ((r1_orders_2(A, B, E) & r1_orders_2(A, C, E)) => r1_orders_2(A, D, E)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l26_lattice3)).
% 4.62/2.10  tff(f_130, axiom, (![A]: ((((~v2_struct_0(A) & v5_orders_2(A)) & v2_lattice3(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => ((D = k11_lattice3(A, B, C)) <=> ((r1_orders_2(A, D, B) & r1_orders_2(A, D, C)) & (![E]: (m1_subset_1(E, u1_struct_0(A)) => ((r1_orders_2(A, E, B) & r1_orders_2(A, E, C)) => r1_orders_2(A, E, D)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l28_lattice3)).
% 4.62/2.10  tff(c_46, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_173])).
% 4.62/2.10  tff(c_44, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_173])).
% 4.62/2.10  tff(c_48, plain, (l1_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_173])).
% 4.62/2.10  tff(c_8, plain, (![A_8, B_9, C_10]: (m1_subset_1(k10_lattice3(A_8, B_9, C_10), u1_struct_0(A_8)) | ~m1_subset_1(C_10, u1_struct_0(A_8)) | ~m1_subset_1(B_9, u1_struct_0(A_8)) | ~l1_orders_2(A_8))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.62/2.10  tff(c_54, plain, (v5_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_173])).
% 4.62/2.10  tff(c_50, plain, (v2_lattice3('#skF_3')), inference(cnfTransformation, [status(thm)], [f_173])).
% 4.62/2.10  tff(c_84, plain, (![A_119, B_120, C_121]: (k12_lattice3(A_119, B_120, C_121)=k11_lattice3(A_119, B_120, C_121) | ~m1_subset_1(C_121, u1_struct_0(A_119)) | ~m1_subset_1(B_120, u1_struct_0(A_119)) | ~l1_orders_2(A_119) | ~v2_lattice3(A_119) | ~v5_orders_2(A_119))), inference(cnfTransformation, [status(thm)], [f_142])).
% 4.62/2.10  tff(c_90, plain, (![B_120]: (k12_lattice3('#skF_3', B_120, '#skF_4')=k11_lattice3('#skF_3', B_120, '#skF_4') | ~m1_subset_1(B_120, u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v2_lattice3('#skF_3') | ~v5_orders_2('#skF_3'))), inference(resolution, [status(thm)], [c_46, c_84])).
% 4.62/2.10  tff(c_122, plain, (![B_123]: (k12_lattice3('#skF_3', B_123, '#skF_4')=k11_lattice3('#skF_3', B_123, '#skF_4') | ~m1_subset_1(B_123, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_50, c_48, c_90])).
% 4.62/2.10  tff(c_126, plain, (![B_9, C_10]: (k12_lattice3('#skF_3', k10_lattice3('#skF_3', B_9, C_10), '#skF_4')=k11_lattice3('#skF_3', k10_lattice3('#skF_3', B_9, C_10), '#skF_4') | ~m1_subset_1(C_10, u1_struct_0('#skF_3')) | ~m1_subset_1(B_9, u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3'))), inference(resolution, [status(thm)], [c_8, c_122])).
% 4.62/2.10  tff(c_436, plain, (![B_153, C_154]: (k12_lattice3('#skF_3', k10_lattice3('#skF_3', B_153, C_154), '#skF_4')=k11_lattice3('#skF_3', k10_lattice3('#skF_3', B_153, C_154), '#skF_4') | ~m1_subset_1(C_154, u1_struct_0('#skF_3')) | ~m1_subset_1(B_153, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_126])).
% 4.62/2.10  tff(c_449, plain, (![B_155]: (k12_lattice3('#skF_3', k10_lattice3('#skF_3', B_155, '#skF_5'), '#skF_4')=k11_lattice3('#skF_3', k10_lattice3('#skF_3', B_155, '#skF_5'), '#skF_4') | ~m1_subset_1(B_155, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_44, c_436])).
% 4.62/2.10  tff(c_464, plain, (k12_lattice3('#skF_3', k10_lattice3('#skF_3', '#skF_4', '#skF_5'), '#skF_4')=k11_lattice3('#skF_3', k10_lattice3('#skF_3', '#skF_4', '#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_46, c_449])).
% 4.62/2.10  tff(c_176, plain, (![A_128, C_129, B_130]: (k12_lattice3(A_128, C_129, B_130)=k12_lattice3(A_128, B_130, C_129) | ~m1_subset_1(C_129, u1_struct_0(A_128)) | ~m1_subset_1(B_130, u1_struct_0(A_128)) | ~l1_orders_2(A_128) | ~v2_lattice3(A_128) | ~v5_orders_2(A_128))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.62/2.10  tff(c_182, plain, (![B_130]: (k12_lattice3('#skF_3', B_130, '#skF_4')=k12_lattice3('#skF_3', '#skF_4', B_130) | ~m1_subset_1(B_130, u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v2_lattice3('#skF_3') | ~v5_orders_2('#skF_3'))), inference(resolution, [status(thm)], [c_46, c_176])).
% 4.62/2.10  tff(c_254, plain, (![B_136]: (k12_lattice3('#skF_3', B_136, '#skF_4')=k12_lattice3('#skF_3', '#skF_4', B_136) | ~m1_subset_1(B_136, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_50, c_48, c_182])).
% 4.62/2.10  tff(c_258, plain, (![B_9, C_10]: (k12_lattice3('#skF_3', k10_lattice3('#skF_3', B_9, C_10), '#skF_4')=k12_lattice3('#skF_3', '#skF_4', k10_lattice3('#skF_3', B_9, C_10)) | ~m1_subset_1(C_10, u1_struct_0('#skF_3')) | ~m1_subset_1(B_9, u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3'))), inference(resolution, [status(thm)], [c_8, c_254])).
% 4.62/2.10  tff(c_563, plain, (![B_168, C_169]: (k12_lattice3('#skF_3', k10_lattice3('#skF_3', B_168, C_169), '#skF_4')=k12_lattice3('#skF_3', '#skF_4', k10_lattice3('#skF_3', B_168, C_169)) | ~m1_subset_1(C_169, u1_struct_0('#skF_3')) | ~m1_subset_1(B_168, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_258])).
% 4.62/2.10  tff(c_576, plain, (![B_170]: (k12_lattice3('#skF_3', k10_lattice3('#skF_3', B_170, '#skF_5'), '#skF_4')=k12_lattice3('#skF_3', '#skF_4', k10_lattice3('#skF_3', B_170, '#skF_5')) | ~m1_subset_1(B_170, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_44, c_563])).
% 4.62/2.10  tff(c_586, plain, (k12_lattice3('#skF_3', k10_lattice3('#skF_3', '#skF_4', '#skF_5'), '#skF_4')=k12_lattice3('#skF_3', '#skF_4', k10_lattice3('#skF_3', '#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_46, c_576])).
% 4.62/2.10  tff(c_593, plain, (k12_lattice3('#skF_3', '#skF_4', k10_lattice3('#skF_3', '#skF_4', '#skF_5'))=k11_lattice3('#skF_3', k10_lattice3('#skF_3', '#skF_4', '#skF_5'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_464, c_586])).
% 4.62/2.10  tff(c_52, plain, (v1_lattice3('#skF_3')), inference(cnfTransformation, [status(thm)], [f_173])).
% 4.62/2.10  tff(c_146, plain, (![A_124, B_125, C_126]: (k13_lattice3(A_124, B_125, C_126)=k10_lattice3(A_124, B_125, C_126) | ~m1_subset_1(C_126, u1_struct_0(A_124)) | ~m1_subset_1(B_125, u1_struct_0(A_124)) | ~l1_orders_2(A_124) | ~v1_lattice3(A_124) | ~v5_orders_2(A_124))), inference(cnfTransformation, [status(thm)], [f_154])).
% 4.62/2.10  tff(c_150, plain, (![B_125]: (k13_lattice3('#skF_3', B_125, '#skF_5')=k10_lattice3('#skF_3', B_125, '#skF_5') | ~m1_subset_1(B_125, u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v1_lattice3('#skF_3') | ~v5_orders_2('#skF_3'))), inference(resolution, [status(thm)], [c_44, c_146])).
% 4.62/2.10  tff(c_160, plain, (![B_127]: (k13_lattice3('#skF_3', B_127, '#skF_5')=k10_lattice3('#skF_3', B_127, '#skF_5') | ~m1_subset_1(B_127, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_48, c_150])).
% 4.62/2.10  tff(c_175, plain, (k13_lattice3('#skF_3', '#skF_4', '#skF_5')=k10_lattice3('#skF_3', '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_46, c_160])).
% 4.62/2.10  tff(c_42, plain, (k12_lattice3('#skF_3', '#skF_4', k13_lattice3('#skF_3', '#skF_4', '#skF_5'))!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_173])).
% 4.62/2.10  tff(c_194, plain, (k12_lattice3('#skF_3', '#skF_4', k10_lattice3('#skF_3', '#skF_4', '#skF_5'))!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_175, c_42])).
% 4.62/2.10  tff(c_616, plain, (k11_lattice3('#skF_3', k10_lattice3('#skF_3', '#skF_4', '#skF_5'), '#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_593, c_194])).
% 4.62/2.10  tff(c_56, plain, (v3_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_173])).
% 4.62/2.10  tff(c_58, plain, (![A_114, B_115]: (r1_orders_2(A_114, B_115, B_115) | ~m1_subset_1(B_115, u1_struct_0(A_114)) | ~l1_orders_2(A_114) | ~v3_orders_2(A_114) | v2_struct_0(A_114))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.62/2.10  tff(c_60, plain, (r1_orders_2('#skF_3', '#skF_5', '#skF_5') | ~l1_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_44, c_58])).
% 4.62/2.10  tff(c_65, plain, (r1_orders_2('#skF_3', '#skF_5', '#skF_5') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_48, c_60])).
% 4.62/2.10  tff(c_69, plain, (v2_struct_0('#skF_3')), inference(splitLeft, [status(thm)], [c_65])).
% 4.62/2.10  tff(c_4, plain, (![A_4]: (~v2_struct_0(A_4) | ~v1_lattice3(A_4) | ~l1_orders_2(A_4))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.62/2.10  tff(c_72, plain, (~v1_lattice3('#skF_3') | ~l1_orders_2('#skF_3')), inference(resolution, [status(thm)], [c_69, c_4])).
% 4.62/2.10  tff(c_76, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_52, c_72])).
% 4.62/2.10  tff(c_78, plain, (~v2_struct_0('#skF_3')), inference(splitRight, [status(thm)], [c_65])).
% 4.62/2.10  tff(c_489, plain, (![A_157, B_158, C_159]: (r1_orders_2(A_157, B_158, k10_lattice3(A_157, B_158, C_159)) | ~m1_subset_1(k10_lattice3(A_157, B_158, C_159), u1_struct_0(A_157)) | ~m1_subset_1(C_159, u1_struct_0(A_157)) | ~m1_subset_1(B_158, u1_struct_0(A_157)) | ~l1_orders_2(A_157) | ~v1_lattice3(A_157) | ~v5_orders_2(A_157) | v2_struct_0(A_157))), inference(cnfTransformation, [status(thm)], [f_97])).
% 4.62/2.10  tff(c_492, plain, (![A_8, B_9, C_10]: (r1_orders_2(A_8, B_9, k10_lattice3(A_8, B_9, C_10)) | ~v1_lattice3(A_8) | ~v5_orders_2(A_8) | v2_struct_0(A_8) | ~m1_subset_1(C_10, u1_struct_0(A_8)) | ~m1_subset_1(B_9, u1_struct_0(A_8)) | ~l1_orders_2(A_8))), inference(resolution, [status(thm)], [c_8, c_489])).
% 4.62/2.10  tff(c_62, plain, (r1_orders_2('#skF_3', '#skF_4', '#skF_4') | ~l1_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_46, c_58])).
% 4.62/2.10  tff(c_68, plain, (r1_orders_2('#skF_3', '#skF_4', '#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_48, c_62])).
% 4.62/2.10  tff(c_79, plain, (r1_orders_2('#skF_3', '#skF_4', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_78, c_68])).
% 4.62/2.10  tff(c_26, plain, (![A_57, B_81, C_93, D_99]: (r1_orders_2(A_57, '#skF_2'(A_57, B_81, C_93, D_99), C_93) | k11_lattice3(A_57, B_81, C_93)=D_99 | ~r1_orders_2(A_57, D_99, C_93) | ~r1_orders_2(A_57, D_99, B_81) | ~m1_subset_1(D_99, u1_struct_0(A_57)) | ~m1_subset_1(C_93, u1_struct_0(A_57)) | ~m1_subset_1(B_81, u1_struct_0(A_57)) | ~l1_orders_2(A_57) | ~v2_lattice3(A_57) | ~v5_orders_2(A_57) | v2_struct_0(A_57))), inference(cnfTransformation, [status(thm)], [f_130])).
% 4.62/2.10  tff(c_1351, plain, (![A_231, B_232, C_233, D_234]: (~r1_orders_2(A_231, '#skF_2'(A_231, B_232, C_233, D_234), D_234) | k11_lattice3(A_231, B_232, C_233)=D_234 | ~r1_orders_2(A_231, D_234, C_233) | ~r1_orders_2(A_231, D_234, B_232) | ~m1_subset_1(D_234, u1_struct_0(A_231)) | ~m1_subset_1(C_233, u1_struct_0(A_231)) | ~m1_subset_1(B_232, u1_struct_0(A_231)) | ~l1_orders_2(A_231) | ~v2_lattice3(A_231) | ~v5_orders_2(A_231) | v2_struct_0(A_231))), inference(cnfTransformation, [status(thm)], [f_130])).
% 4.62/2.10  tff(c_1379, plain, (![A_239, B_240, C_241]: (k11_lattice3(A_239, B_240, C_241)=C_241 | ~r1_orders_2(A_239, C_241, C_241) | ~r1_orders_2(A_239, C_241, B_240) | ~m1_subset_1(C_241, u1_struct_0(A_239)) | ~m1_subset_1(B_240, u1_struct_0(A_239)) | ~l1_orders_2(A_239) | ~v2_lattice3(A_239) | ~v5_orders_2(A_239) | v2_struct_0(A_239))), inference(resolution, [status(thm)], [c_26, c_1351])).
% 4.62/2.10  tff(c_1383, plain, (![B_240]: (k11_lattice3('#skF_3', B_240, '#skF_4')='#skF_4' | ~r1_orders_2('#skF_3', '#skF_4', B_240) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~m1_subset_1(B_240, u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v2_lattice3('#skF_3') | ~v5_orders_2('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_79, c_1379])).
% 4.62/2.10  tff(c_1389, plain, (![B_240]: (k11_lattice3('#skF_3', B_240, '#skF_4')='#skF_4' | ~r1_orders_2('#skF_3', '#skF_4', B_240) | ~m1_subset_1(B_240, u1_struct_0('#skF_3')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_50, c_48, c_46, c_1383])).
% 4.62/2.10  tff(c_1395, plain, (![B_242]: (k11_lattice3('#skF_3', B_242, '#skF_4')='#skF_4' | ~r1_orders_2('#skF_3', '#skF_4', B_242) | ~m1_subset_1(B_242, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_78, c_1389])).
% 4.62/2.10  tff(c_1403, plain, (![B_9, C_10]: (k11_lattice3('#skF_3', k10_lattice3('#skF_3', B_9, C_10), '#skF_4')='#skF_4' | ~r1_orders_2('#skF_3', '#skF_4', k10_lattice3('#skF_3', B_9, C_10)) | ~m1_subset_1(C_10, u1_struct_0('#skF_3')) | ~m1_subset_1(B_9, u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3'))), inference(resolution, [status(thm)], [c_8, c_1395])).
% 4.62/2.10  tff(c_1495, plain, (![B_248, C_249]: (k11_lattice3('#skF_3', k10_lattice3('#skF_3', B_248, C_249), '#skF_4')='#skF_4' | ~r1_orders_2('#skF_3', '#skF_4', k10_lattice3('#skF_3', B_248, C_249)) | ~m1_subset_1(C_249, u1_struct_0('#skF_3')) | ~m1_subset_1(B_248, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_1403])).
% 4.62/2.10  tff(c_1509, plain, (![C_10]: (k11_lattice3('#skF_3', k10_lattice3('#skF_3', '#skF_4', C_10), '#skF_4')='#skF_4' | ~v1_lattice3('#skF_3') | ~v5_orders_2('#skF_3') | v2_struct_0('#skF_3') | ~m1_subset_1(C_10, u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3'))), inference(resolution, [status(thm)], [c_492, c_1495])).
% 4.62/2.10  tff(c_1520, plain, (![C_10]: (k11_lattice3('#skF_3', k10_lattice3('#skF_3', '#skF_4', C_10), '#skF_4')='#skF_4' | v2_struct_0('#skF_3') | ~m1_subset_1(C_10, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_54, c_52, c_1509])).
% 4.62/2.10  tff(c_1571, plain, (![C_251]: (k11_lattice3('#skF_3', k10_lattice3('#skF_3', '#skF_4', C_251), '#skF_4')='#skF_4' | ~m1_subset_1(C_251, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_78, c_1520])).
% 4.62/2.10  tff(c_1582, plain, (k11_lattice3('#skF_3', k10_lattice3('#skF_3', '#skF_4', '#skF_5'), '#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_44, c_1571])).
% 4.62/2.10  tff(c_1596, plain, $false, inference(negUnitSimplification, [status(thm)], [c_616, c_1582])).
% 4.62/2.10  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.62/2.10  
% 4.62/2.10  Inference rules
% 4.62/2.10  ----------------------
% 4.62/2.10  #Ref     : 0
% 4.62/2.10  #Sup     : 338
% 4.62/2.10  #Fact    : 0
% 4.62/2.10  #Define  : 0
% 4.62/2.10  #Split   : 4
% 4.62/2.10  #Chain   : 0
% 4.62/2.10  #Close   : 0
% 4.62/2.10  
% 4.62/2.10  Ordering : KBO
% 4.62/2.10  
% 4.62/2.10  Simplification rules
% 4.62/2.10  ----------------------
% 4.62/2.10  #Subsume      : 8
% 4.62/2.10  #Demod        : 521
% 4.62/2.10  #Tautology    : 182
% 4.62/2.10  #SimpNegUnit  : 56
% 4.62/2.10  #BackRed      : 25
% 4.62/2.10  
% 4.62/2.10  #Partial instantiations: 0
% 4.62/2.10  #Strategies tried      : 1
% 4.62/2.10  
% 4.62/2.10  Timing (in seconds)
% 4.62/2.10  ----------------------
% 4.62/2.10  Preprocessing        : 0.56
% 4.62/2.10  Parsing              : 0.30
% 4.62/2.10  CNF conversion       : 0.05
% 4.62/2.10  Main loop            : 0.71
% 4.62/2.10  Inferencing          : 0.25
% 4.62/2.10  Reduction            : 0.23
% 4.62/2.10  Demodulation         : 0.16
% 4.62/2.10  BG Simplification    : 0.05
% 4.62/2.10  Subsumption          : 0.14
% 4.62/2.10  Abstraction          : 0.04
% 4.62/2.10  MUC search           : 0.00
% 4.62/2.10  Cooper               : 0.00
% 4.62/2.10  Total                : 1.31
% 4.62/2.10  Index Insertion      : 0.00
% 4.62/2.10  Index Deletion       : 0.00
% 4.62/2.10  Index Matching       : 0.00
% 4.62/2.10  BG Taut test         : 0.00
%------------------------------------------------------------------------------
