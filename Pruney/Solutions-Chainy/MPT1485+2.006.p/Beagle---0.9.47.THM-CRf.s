%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:41 EST 2020

% Result     : Theorem 8.48s
% Output     : CNFRefutation 8.48s
% Verified   : 
% Statistics : Number of formulae       :  113 (1237 expanded)
%              Number of leaves         :   30 ( 504 expanded)
%              Depth                    :   19
%              Number of atoms          :  371 (5572 expanded)
%              Number of equality atoms :   50 ( 662 expanded)
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

tff(f_186,negated_conjecture,(
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

tff(f_137,axiom,(
    ! [A,B,C] :
      ( ( v5_orders_2(A)
        & v2_lattice3(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => k12_lattice3(A,B,C) = k11_lattice3(A,B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k12_lattice3)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( ( v5_orders_2(A)
        & v2_lattice3(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => m1_subset_1(k12_lattice3(A,B,C),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k12_lattice3)).

tff(f_125,axiom,(
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

tff(f_32,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v1_lattice3(A)
       => ~ v2_struct_0(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_lattice3)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( ( l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => m1_subset_1(k10_lattice3(A,B,C),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k10_lattice3)).

tff(f_149,axiom,(
    ! [A,B,C] :
      ( ( v5_orders_2(A)
        & v1_lattice3(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => k13_lattice3(A,B,C) = k10_lattice3(A,B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k13_lattice3)).

tff(f_167,axiom,(
    ! [A] :
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

tff(f_92,axiom,(
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

tff(c_50,plain,(
    l1_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_54,plain,(
    v1_lattice3('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_56,plain,(
    v5_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_52,plain,(
    v2_lattice3('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_48,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_46,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_107,plain,(
    ! [A_130,B_131,C_132] :
      ( k12_lattice3(A_130,B_131,C_132) = k11_lattice3(A_130,B_131,C_132)
      | ~ m1_subset_1(C_132,u1_struct_0(A_130))
      | ~ m1_subset_1(B_131,u1_struct_0(A_130))
      | ~ l1_orders_2(A_130)
      | ~ v2_lattice3(A_130)
      | ~ v5_orders_2(A_130) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_113,plain,(
    ! [B_131] :
      ( k12_lattice3('#skF_3',B_131,'#skF_5') = k11_lattice3('#skF_3',B_131,'#skF_5')
      | ~ m1_subset_1(B_131,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | ~ v2_lattice3('#skF_3')
      | ~ v5_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_46,c_107])).

tff(c_319,plain,(
    ! [B_139] :
      ( k12_lattice3('#skF_3',B_139,'#skF_5') = k11_lattice3('#skF_3',B_139,'#skF_5')
      | ~ m1_subset_1(B_139,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_50,c_113])).

tff(c_349,plain,(
    k12_lattice3('#skF_3','#skF_4','#skF_5') = k11_lattice3('#skF_3','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_48,c_319])).

tff(c_8,plain,(
    ! [A_6,B_7,C_8] :
      ( m1_subset_1(k12_lattice3(A_6,B_7,C_8),u1_struct_0(A_6))
      | ~ m1_subset_1(C_8,u1_struct_0(A_6))
      | ~ m1_subset_1(B_7,u1_struct_0(A_6))
      | ~ l1_orders_2(A_6)
      | ~ v2_lattice3(A_6)
      | ~ v5_orders_2(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_419,plain,
    ( m1_subset_1(k11_lattice3('#skF_3','#skF_4','#skF_5'),u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ l1_orders_2('#skF_3')
    | ~ v2_lattice3('#skF_3')
    | ~ v5_orders_2('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_349,c_8])).

tff(c_423,plain,(
    m1_subset_1(k11_lattice3('#skF_3','#skF_4','#skF_5'),u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_50,c_48,c_46,c_419])).

tff(c_36,plain,(
    ! [A_55,B_79,C_91] :
      ( r1_orders_2(A_55,k11_lattice3(A_55,B_79,C_91),B_79)
      | ~ m1_subset_1(k11_lattice3(A_55,B_79,C_91),u1_struct_0(A_55))
      | ~ m1_subset_1(C_91,u1_struct_0(A_55))
      | ~ m1_subset_1(B_79,u1_struct_0(A_55))
      | ~ l1_orders_2(A_55)
      | ~ v2_lattice3(A_55)
      | ~ v5_orders_2(A_55)
      | v2_struct_0(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_426,plain,
    ( r1_orders_2('#skF_3',k11_lattice3('#skF_3','#skF_4','#skF_5'),'#skF_4')
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ l1_orders_2('#skF_3')
    | ~ v2_lattice3('#skF_3')
    | ~ v5_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_423,c_36])).

tff(c_450,plain,
    ( r1_orders_2('#skF_3',k11_lattice3('#skF_3','#skF_4','#skF_5'),'#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_50,c_48,c_46,c_426])).

tff(c_469,plain,(
    v2_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_450])).

tff(c_2,plain,(
    ! [A_1] :
      ( ~ v2_struct_0(A_1)
      | ~ v1_lattice3(A_1)
      | ~ l1_orders_2(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_472,plain,
    ( ~ v1_lattice3('#skF_3')
    | ~ l1_orders_2('#skF_3') ),
    inference(resolution,[status(thm)],[c_469,c_2])).

tff(c_479,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_54,c_472])).

tff(c_481,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_450])).

tff(c_6,plain,(
    ! [A_3,B_4,C_5] :
      ( m1_subset_1(k10_lattice3(A_3,B_4,C_5),u1_struct_0(A_3))
      | ~ m1_subset_1(C_5,u1_struct_0(A_3))
      | ~ m1_subset_1(B_4,u1_struct_0(A_3))
      | ~ l1_orders_2(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_4349,plain,(
    ! [A_222,B_223,B_224,C_225] :
      ( k12_lattice3(A_222,B_223,k10_lattice3(A_222,B_224,C_225)) = k11_lattice3(A_222,B_223,k10_lattice3(A_222,B_224,C_225))
      | ~ m1_subset_1(B_223,u1_struct_0(A_222))
      | ~ v2_lattice3(A_222)
      | ~ v5_orders_2(A_222)
      | ~ m1_subset_1(C_225,u1_struct_0(A_222))
      | ~ m1_subset_1(B_224,u1_struct_0(A_222))
      | ~ l1_orders_2(A_222) ) ),
    inference(resolution,[status(thm)],[c_6,c_107])).

tff(c_4381,plain,(
    ! [B_224,C_225] :
      ( k12_lattice3('#skF_3','#skF_4',k10_lattice3('#skF_3',B_224,C_225)) = k11_lattice3('#skF_3','#skF_4',k10_lattice3('#skF_3',B_224,C_225))
      | ~ v2_lattice3('#skF_3')
      | ~ v5_orders_2('#skF_3')
      | ~ m1_subset_1(C_225,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(B_224,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_48,c_4349])).

tff(c_6175,plain,(
    ! [B_257,C_258] :
      ( k12_lattice3('#skF_3','#skF_4',k10_lattice3('#skF_3',B_257,C_258)) = k11_lattice3('#skF_3','#skF_4',k10_lattice3('#skF_3',B_257,C_258))
      | ~ m1_subset_1(C_258,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(B_257,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_56,c_52,c_4381])).

tff(c_6630,plain,(
    ! [B_264] :
      ( k12_lattice3('#skF_3','#skF_4',k10_lattice3('#skF_3',B_264,'#skF_5')) = k11_lattice3('#skF_3','#skF_4',k10_lattice3('#skF_3',B_264,'#skF_5'))
      | ~ m1_subset_1(B_264,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_46,c_6175])).

tff(c_6723,plain,(
    k12_lattice3('#skF_3','#skF_4',k10_lattice3('#skF_3','#skF_4','#skF_5')) = k11_lattice3('#skF_3','#skF_4',k10_lattice3('#skF_3','#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_48,c_6630])).

tff(c_63,plain,(
    ! [A_126,B_127,C_128] :
      ( k13_lattice3(A_126,B_127,C_128) = k10_lattice3(A_126,B_127,C_128)
      | ~ m1_subset_1(C_128,u1_struct_0(A_126))
      | ~ m1_subset_1(B_127,u1_struct_0(A_126))
      | ~ l1_orders_2(A_126)
      | ~ v1_lattice3(A_126)
      | ~ v5_orders_2(A_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_69,plain,(
    ! [B_127] :
      ( k13_lattice3('#skF_3',B_127,'#skF_5') = k10_lattice3('#skF_3',B_127,'#skF_5')
      | ~ m1_subset_1(B_127,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | ~ v1_lattice3('#skF_3')
      | ~ v5_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_46,c_63])).

tff(c_80,plain,(
    ! [B_129] :
      ( k13_lattice3('#skF_3',B_129,'#skF_5') = k10_lattice3('#skF_3',B_129,'#skF_5')
      | ~ m1_subset_1(B_129,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_50,c_69])).

tff(c_102,plain,(
    k13_lattice3('#skF_3','#skF_4','#skF_5') = k10_lattice3('#skF_3','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_48,c_80])).

tff(c_44,plain,(
    k12_lattice3('#skF_3','#skF_4',k13_lattice3('#skF_3','#skF_4','#skF_5')) != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_124,plain,(
    k12_lattice3('#skF_3','#skF_4',k10_lattice3('#skF_3','#skF_4','#skF_5')) != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_44])).

tff(c_6736,plain,(
    k11_lattice3('#skF_3','#skF_4',k10_lattice3('#skF_3','#skF_4','#skF_5')) != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6723,c_124])).

tff(c_4379,plain,(
    ! [B_224,C_225] :
      ( k12_lattice3('#skF_3','#skF_5',k10_lattice3('#skF_3',B_224,C_225)) = k11_lattice3('#skF_3','#skF_5',k10_lattice3('#skF_3',B_224,C_225))
      | ~ v2_lattice3('#skF_3')
      | ~ v5_orders_2('#skF_3')
      | ~ m1_subset_1(C_225,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(B_224,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_46,c_4349])).

tff(c_4450,plain,(
    ! [B_226,C_227] :
      ( k12_lattice3('#skF_3','#skF_5',k10_lattice3('#skF_3',B_226,C_227)) = k11_lattice3('#skF_3','#skF_5',k10_lattice3('#skF_3',B_226,C_227))
      | ~ m1_subset_1(C_227,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(B_226,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_56,c_52,c_4379])).

tff(c_4694,plain,(
    ! [B_232] :
      ( k12_lattice3('#skF_3','#skF_5',k10_lattice3('#skF_3',B_232,'#skF_5')) = k11_lattice3('#skF_3','#skF_5',k10_lattice3('#skF_3',B_232,'#skF_5'))
      | ~ m1_subset_1(B_232,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_46,c_4450])).

tff(c_4778,plain,(
    k12_lattice3('#skF_3','#skF_5',k10_lattice3('#skF_3','#skF_4','#skF_5')) = k11_lattice3('#skF_3','#skF_5',k10_lattice3('#skF_3','#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_48,c_4694])).

tff(c_4913,plain,
    ( m1_subset_1(k11_lattice3('#skF_3','#skF_5',k10_lattice3('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_3'))
    | ~ m1_subset_1(k10_lattice3('#skF_3','#skF_4','#skF_5'),u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
    | ~ l1_orders_2('#skF_3')
    | ~ v2_lattice3('#skF_3')
    | ~ v5_orders_2('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_4778,c_8])).

tff(c_4917,plain,
    ( m1_subset_1(k11_lattice3('#skF_3','#skF_5',k10_lattice3('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_3'))
    | ~ m1_subset_1(k10_lattice3('#skF_3','#skF_4','#skF_5'),u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_50,c_46,c_4913])).

tff(c_6238,plain,(
    ~ m1_subset_1(k10_lattice3('#skF_3','#skF_4','#skF_5'),u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_4917])).

tff(c_6241,plain,
    ( ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ l1_orders_2('#skF_3') ),
    inference(resolution,[status(thm)],[c_6,c_6238])).

tff(c_6245,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_6241])).

tff(c_6247,plain,(
    m1_subset_1(k10_lattice3('#skF_3','#skF_4','#skF_5'),u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_4917])).

tff(c_115,plain,(
    ! [B_131] :
      ( k12_lattice3('#skF_3',B_131,'#skF_4') = k11_lattice3('#skF_3',B_131,'#skF_4')
      | ~ m1_subset_1(B_131,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | ~ v2_lattice3('#skF_3')
      | ~ v5_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_48,c_107])).

tff(c_160,plain,(
    ! [B_134] :
      ( k12_lattice3('#skF_3',B_134,'#skF_4') = k11_lattice3('#skF_3',B_134,'#skF_4')
      | ~ m1_subset_1(B_134,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_50,c_115])).

tff(c_182,plain,(
    k12_lattice3('#skF_3','#skF_4','#skF_4') = k11_lattice3('#skF_3','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_160])).

tff(c_217,plain,
    ( m1_subset_1(k11_lattice3('#skF_3','#skF_4','#skF_4'),u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ l1_orders_2('#skF_3')
    | ~ v2_lattice3('#skF_3')
    | ~ v5_orders_2('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_182,c_8])).

tff(c_221,plain,(
    m1_subset_1(k11_lattice3('#skF_3','#skF_4','#skF_4'),u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_50,c_48,c_48,c_217])).

tff(c_58,plain,(
    v3_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_223,plain,(
    ! [A_135,B_136,C_137] :
      ( k13_lattice3(A_135,k12_lattice3(A_135,B_136,C_137),C_137) = C_137
      | ~ m1_subset_1(C_137,u1_struct_0(A_135))
      | ~ m1_subset_1(B_136,u1_struct_0(A_135))
      | ~ l1_orders_2(A_135)
      | ~ v2_lattice3(A_135)
      | ~ v1_lattice3(A_135)
      | ~ v5_orders_2(A_135)
      | ~ v3_orders_2(A_135) ) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_233,plain,(
    ! [B_136] :
      ( k13_lattice3('#skF_3',k12_lattice3('#skF_3',B_136,'#skF_4'),'#skF_4') = '#skF_4'
      | ~ m1_subset_1(B_136,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | ~ v2_lattice3('#skF_3')
      | ~ v1_lattice3('#skF_3')
      | ~ v5_orders_2('#skF_3')
      | ~ v3_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_48,c_223])).

tff(c_493,plain,(
    ! [B_146] :
      ( k13_lattice3('#skF_3',k12_lattice3('#skF_3',B_146,'#skF_4'),'#skF_4') = '#skF_4'
      | ~ m1_subset_1(B_146,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_52,c_50,c_233])).

tff(c_519,plain,(
    k13_lattice3('#skF_3',k12_lattice3('#skF_3','#skF_4','#skF_4'),'#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_48,c_493])).

tff(c_533,plain,(
    k13_lattice3('#skF_3',k11_lattice3('#skF_3','#skF_4','#skF_4'),'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_182,c_519])).

tff(c_71,plain,(
    ! [B_127] :
      ( k13_lattice3('#skF_3',B_127,'#skF_4') = k10_lattice3('#skF_3',B_127,'#skF_4')
      | ~ m1_subset_1(B_127,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | ~ v1_lattice3('#skF_3')
      | ~ v5_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_48,c_63])).

tff(c_79,plain,(
    ! [B_127] :
      ( k13_lattice3('#skF_3',B_127,'#skF_4') = k10_lattice3('#skF_3',B_127,'#skF_4')
      | ~ m1_subset_1(B_127,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_50,c_71])).

tff(c_264,plain,(
    k13_lattice3('#skF_3',k11_lattice3('#skF_3','#skF_4','#skF_4'),'#skF_4') = k10_lattice3('#skF_3',k11_lattice3('#skF_3','#skF_4','#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_221,c_79])).

tff(c_576,plain,(
    k10_lattice3('#skF_3',k11_lattice3('#skF_3','#skF_4','#skF_4'),'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_533,c_264])).

tff(c_20,plain,(
    ! [A_9,C_45,B_33] :
      ( r1_orders_2(A_9,C_45,k10_lattice3(A_9,B_33,C_45))
      | ~ m1_subset_1(k10_lattice3(A_9,B_33,C_45),u1_struct_0(A_9))
      | ~ m1_subset_1(C_45,u1_struct_0(A_9))
      | ~ m1_subset_1(B_33,u1_struct_0(A_9))
      | ~ l1_orders_2(A_9)
      | ~ v1_lattice3(A_9)
      | ~ v5_orders_2(A_9)
      | v2_struct_0(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_581,plain,
    ( r1_orders_2('#skF_3','#skF_4',k10_lattice3('#skF_3',k11_lattice3('#skF_3','#skF_4','#skF_4'),'#skF_4'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ m1_subset_1(k11_lattice3('#skF_3','#skF_4','#skF_4'),u1_struct_0('#skF_3'))
    | ~ l1_orders_2('#skF_3')
    | ~ v1_lattice3('#skF_3')
    | ~ v5_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_576,c_20])).

tff(c_591,plain,
    ( r1_orders_2('#skF_3','#skF_4','#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_50,c_221,c_48,c_48,c_576,c_581])).

tff(c_592,plain,(
    r1_orders_2('#skF_3','#skF_4','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_481,c_591])).

tff(c_554,plain,(
    ! [A_147,B_148,C_149] :
      ( r1_orders_2(A_147,B_148,k10_lattice3(A_147,B_148,C_149))
      | ~ m1_subset_1(k10_lattice3(A_147,B_148,C_149),u1_struct_0(A_147))
      | ~ m1_subset_1(C_149,u1_struct_0(A_147))
      | ~ m1_subset_1(B_148,u1_struct_0(A_147))
      | ~ l1_orders_2(A_147)
      | ~ v1_lattice3(A_147)
      | ~ v5_orders_2(A_147)
      | v2_struct_0(A_147) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_557,plain,(
    ! [A_3,B_4,C_5] :
      ( r1_orders_2(A_3,B_4,k10_lattice3(A_3,B_4,C_5))
      | ~ v1_lattice3(A_3)
      | ~ v5_orders_2(A_3)
      | v2_struct_0(A_3)
      | ~ m1_subset_1(C_5,u1_struct_0(A_3))
      | ~ m1_subset_1(B_4,u1_struct_0(A_3))
      | ~ l1_orders_2(A_3) ) ),
    inference(resolution,[status(thm)],[c_6,c_554])).

tff(c_26,plain,(
    ! [A_55,B_79,C_91,D_97] :
      ( r1_orders_2(A_55,'#skF_2'(A_55,B_79,C_91,D_97),C_91)
      | k11_lattice3(A_55,B_79,C_91) = D_97
      | ~ r1_orders_2(A_55,D_97,C_91)
      | ~ r1_orders_2(A_55,D_97,B_79)
      | ~ m1_subset_1(D_97,u1_struct_0(A_55))
      | ~ m1_subset_1(C_91,u1_struct_0(A_55))
      | ~ m1_subset_1(B_79,u1_struct_0(A_55))
      | ~ l1_orders_2(A_55)
      | ~ v2_lattice3(A_55)
      | ~ v5_orders_2(A_55)
      | v2_struct_0(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_1273,plain,(
    ! [A_169,B_170,C_171,D_172] :
      ( ~ r1_orders_2(A_169,'#skF_2'(A_169,B_170,C_171,D_172),D_172)
      | k11_lattice3(A_169,B_170,C_171) = D_172
      | ~ r1_orders_2(A_169,D_172,C_171)
      | ~ r1_orders_2(A_169,D_172,B_170)
      | ~ m1_subset_1(D_172,u1_struct_0(A_169))
      | ~ m1_subset_1(C_171,u1_struct_0(A_169))
      | ~ m1_subset_1(B_170,u1_struct_0(A_169))
      | ~ l1_orders_2(A_169)
      | ~ v2_lattice3(A_169)
      | ~ v5_orders_2(A_169)
      | v2_struct_0(A_169) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_3705,plain,(
    ! [A_216,B_217,C_218] :
      ( k11_lattice3(A_216,B_217,C_218) = C_218
      | ~ r1_orders_2(A_216,C_218,C_218)
      | ~ r1_orders_2(A_216,C_218,B_217)
      | ~ m1_subset_1(C_218,u1_struct_0(A_216))
      | ~ m1_subset_1(B_217,u1_struct_0(A_216))
      | ~ l1_orders_2(A_216)
      | ~ v2_lattice3(A_216)
      | ~ v5_orders_2(A_216)
      | v2_struct_0(A_216) ) ),
    inference(resolution,[status(thm)],[c_26,c_1273])).

tff(c_3715,plain,(
    ! [B_217] :
      ( k11_lattice3('#skF_3',B_217,'#skF_4') = '#skF_4'
      | ~ r1_orders_2('#skF_3','#skF_4',B_217)
      | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
      | ~ m1_subset_1(B_217,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | ~ v2_lattice3('#skF_3')
      | ~ v5_orders_2('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_592,c_3705])).

tff(c_3730,plain,(
    ! [B_217] :
      ( k11_lattice3('#skF_3',B_217,'#skF_4') = '#skF_4'
      | ~ r1_orders_2('#skF_3','#skF_4',B_217)
      | ~ m1_subset_1(B_217,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_50,c_48,c_3715])).

tff(c_3731,plain,(
    ! [B_217] :
      ( k11_lattice3('#skF_3',B_217,'#skF_4') = '#skF_4'
      | ~ r1_orders_2('#skF_3','#skF_4',B_217)
      | ~ m1_subset_1(B_217,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_481,c_3730])).

tff(c_6316,plain,
    ( k11_lattice3('#skF_3',k10_lattice3('#skF_3','#skF_4','#skF_5'),'#skF_4') = '#skF_4'
    | ~ r1_orders_2('#skF_3','#skF_4',k10_lattice3('#skF_3','#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_6247,c_3731])).

tff(c_8172,plain,(
    ~ r1_orders_2('#skF_3','#skF_4',k10_lattice3('#skF_3','#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_6316])).

tff(c_8175,plain,
    ( ~ v1_lattice3('#skF_3')
    | ~ v5_orders_2('#skF_3')
    | v2_struct_0('#skF_3')
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ l1_orders_2('#skF_3') ),
    inference(resolution,[status(thm)],[c_557,c_8172])).

tff(c_8178,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_56,c_54,c_8175])).

tff(c_8180,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_481,c_8178])).

tff(c_8182,plain,(
    r1_orders_2('#skF_3','#skF_4',k10_lattice3('#skF_3','#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_6316])).

tff(c_1432,plain,(
    ! [A_178,B_179,C_180,D_181] :
      ( r1_orders_2(A_178,'#skF_2'(A_178,B_179,C_180,D_181),B_179)
      | k11_lattice3(A_178,B_179,C_180) = D_181
      | ~ r1_orders_2(A_178,D_181,C_180)
      | ~ r1_orders_2(A_178,D_181,B_179)
      | ~ m1_subset_1(D_181,u1_struct_0(A_178))
      | ~ m1_subset_1(C_180,u1_struct_0(A_178))
      | ~ m1_subset_1(B_179,u1_struct_0(A_178))
      | ~ l1_orders_2(A_178)
      | ~ v2_lattice3(A_178)
      | ~ v5_orders_2(A_178)
      | v2_struct_0(A_178) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_24,plain,(
    ! [A_55,B_79,C_91,D_97] :
      ( ~ r1_orders_2(A_55,'#skF_2'(A_55,B_79,C_91,D_97),D_97)
      | k11_lattice3(A_55,B_79,C_91) = D_97
      | ~ r1_orders_2(A_55,D_97,C_91)
      | ~ r1_orders_2(A_55,D_97,B_79)
      | ~ m1_subset_1(D_97,u1_struct_0(A_55))
      | ~ m1_subset_1(C_91,u1_struct_0(A_55))
      | ~ m1_subset_1(B_79,u1_struct_0(A_55))
      | ~ l1_orders_2(A_55)
      | ~ v2_lattice3(A_55)
      | ~ v5_orders_2(A_55)
      | v2_struct_0(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_1437,plain,(
    ! [A_178,B_179,C_180] :
      ( k11_lattice3(A_178,B_179,C_180) = B_179
      | ~ r1_orders_2(A_178,B_179,C_180)
      | ~ r1_orders_2(A_178,B_179,B_179)
      | ~ m1_subset_1(C_180,u1_struct_0(A_178))
      | ~ m1_subset_1(B_179,u1_struct_0(A_178))
      | ~ l1_orders_2(A_178)
      | ~ v2_lattice3(A_178)
      | ~ v5_orders_2(A_178)
      | v2_struct_0(A_178) ) ),
    inference(resolution,[status(thm)],[c_1432,c_24])).

tff(c_8184,plain,
    ( k11_lattice3('#skF_3','#skF_4',k10_lattice3('#skF_3','#skF_4','#skF_5')) = '#skF_4'
    | ~ r1_orders_2('#skF_3','#skF_4','#skF_4')
    | ~ m1_subset_1(k10_lattice3('#skF_3','#skF_4','#skF_5'),u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ l1_orders_2('#skF_3')
    | ~ v2_lattice3('#skF_3')
    | ~ v5_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_8182,c_1437])).

tff(c_8189,plain,
    ( k11_lattice3('#skF_3','#skF_4',k10_lattice3('#skF_3','#skF_4','#skF_5')) = '#skF_4'
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_50,c_48,c_6247,c_592,c_8184])).

tff(c_8191,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_481,c_6736,c_8189])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n022.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:54:40 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.48/3.09  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.48/3.10  
% 8.48/3.10  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.48/3.10  %$ r1_orders_2 > m1_subset_1 > v5_orders_2 > v3_orders_2 > v2_struct_0 > v2_lattice3 > v1_lattice3 > l1_orders_2 > k13_lattice3 > k12_lattice3 > k11_lattice3 > k10_lattice3 > #nlpp > u1_struct_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 8.48/3.10  
% 8.48/3.10  %Foreground sorts:
% 8.48/3.10  
% 8.48/3.10  
% 8.48/3.10  %Background operators:
% 8.48/3.10  
% 8.48/3.10  
% 8.48/3.10  %Foreground operators:
% 8.48/3.10  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 8.48/3.10  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 8.48/3.10  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.48/3.10  tff(k13_lattice3, type, k13_lattice3: ($i * $i * $i) > $i).
% 8.48/3.10  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 8.48/3.10  tff(k10_lattice3, type, k10_lattice3: ($i * $i * $i) > $i).
% 8.48/3.10  tff(k11_lattice3, type, k11_lattice3: ($i * $i * $i) > $i).
% 8.48/3.10  tff(v1_lattice3, type, v1_lattice3: $i > $o).
% 8.48/3.10  tff('#skF_5', type, '#skF_5': $i).
% 8.48/3.10  tff(k12_lattice3, type, k12_lattice3: ($i * $i * $i) > $i).
% 8.48/3.10  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 8.48/3.10  tff('#skF_3', type, '#skF_3': $i).
% 8.48/3.10  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 8.48/3.10  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 8.48/3.10  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.48/3.10  tff('#skF_4', type, '#skF_4': $i).
% 8.48/3.10  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.48/3.10  tff(v2_lattice3, type, v2_lattice3: $i > $o).
% 8.48/3.10  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 8.48/3.10  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 8.48/3.10  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.48/3.10  
% 8.48/3.12  tff(f_186, negated_conjecture, ~(![A]: (((((v3_orders_2(A) & v5_orders_2(A)) & v1_lattice3(A)) & v2_lattice3(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (k12_lattice3(A, B, k13_lattice3(A, B, C)) = B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_lattice3)).
% 8.48/3.12  tff(f_137, axiom, (![A, B, C]: (((((v5_orders_2(A) & v2_lattice3(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (k12_lattice3(A, B, C) = k11_lattice3(A, B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k12_lattice3)).
% 8.48/3.12  tff(f_59, axiom, (![A, B, C]: (((((v5_orders_2(A) & v2_lattice3(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => m1_subset_1(k12_lattice3(A, B, C), u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k12_lattice3)).
% 8.48/3.12  tff(f_125, axiom, (![A]: ((((~v2_struct_0(A) & v5_orders_2(A)) & v2_lattice3(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => ((D = k11_lattice3(A, B, C)) <=> ((r1_orders_2(A, D, B) & r1_orders_2(A, D, C)) & (![E]: (m1_subset_1(E, u1_struct_0(A)) => ((r1_orders_2(A, E, B) & r1_orders_2(A, E, C)) => r1_orders_2(A, E, D)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l28_lattice3)).
% 8.48/3.12  tff(f_32, axiom, (![A]: (l1_orders_2(A) => (v1_lattice3(A) => ~v2_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_lattice3)).
% 8.48/3.12  tff(f_47, axiom, (![A, B, C]: (((l1_orders_2(A) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => m1_subset_1(k10_lattice3(A, B, C), u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k10_lattice3)).
% 8.48/3.12  tff(f_149, axiom, (![A, B, C]: (((((v5_orders_2(A) & v1_lattice3(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (k13_lattice3(A, B, C) = k10_lattice3(A, B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k13_lattice3)).
% 8.48/3.12  tff(f_167, axiom, (![A]: (((((v3_orders_2(A) & v5_orders_2(A)) & v1_lattice3(A)) & v2_lattice3(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (k13_lattice3(A, k12_lattice3(A, B, C), C) = C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_lattice3)).
% 8.48/3.12  tff(f_92, axiom, (![A]: ((((~v2_struct_0(A) & v5_orders_2(A)) & v1_lattice3(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => ((D = k10_lattice3(A, B, C)) <=> ((r1_orders_2(A, B, D) & r1_orders_2(A, C, D)) & (![E]: (m1_subset_1(E, u1_struct_0(A)) => ((r1_orders_2(A, B, E) & r1_orders_2(A, C, E)) => r1_orders_2(A, D, E)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l26_lattice3)).
% 8.48/3.12  tff(c_50, plain, (l1_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_186])).
% 8.48/3.12  tff(c_54, plain, (v1_lattice3('#skF_3')), inference(cnfTransformation, [status(thm)], [f_186])).
% 8.48/3.12  tff(c_56, plain, (v5_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_186])).
% 8.48/3.12  tff(c_52, plain, (v2_lattice3('#skF_3')), inference(cnfTransformation, [status(thm)], [f_186])).
% 8.48/3.12  tff(c_48, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_186])).
% 8.48/3.12  tff(c_46, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_186])).
% 8.48/3.12  tff(c_107, plain, (![A_130, B_131, C_132]: (k12_lattice3(A_130, B_131, C_132)=k11_lattice3(A_130, B_131, C_132) | ~m1_subset_1(C_132, u1_struct_0(A_130)) | ~m1_subset_1(B_131, u1_struct_0(A_130)) | ~l1_orders_2(A_130) | ~v2_lattice3(A_130) | ~v5_orders_2(A_130))), inference(cnfTransformation, [status(thm)], [f_137])).
% 8.48/3.12  tff(c_113, plain, (![B_131]: (k12_lattice3('#skF_3', B_131, '#skF_5')=k11_lattice3('#skF_3', B_131, '#skF_5') | ~m1_subset_1(B_131, u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v2_lattice3('#skF_3') | ~v5_orders_2('#skF_3'))), inference(resolution, [status(thm)], [c_46, c_107])).
% 8.48/3.12  tff(c_319, plain, (![B_139]: (k12_lattice3('#skF_3', B_139, '#skF_5')=k11_lattice3('#skF_3', B_139, '#skF_5') | ~m1_subset_1(B_139, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_52, c_50, c_113])).
% 8.48/3.12  tff(c_349, plain, (k12_lattice3('#skF_3', '#skF_4', '#skF_5')=k11_lattice3('#skF_3', '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_48, c_319])).
% 8.48/3.12  tff(c_8, plain, (![A_6, B_7, C_8]: (m1_subset_1(k12_lattice3(A_6, B_7, C_8), u1_struct_0(A_6)) | ~m1_subset_1(C_8, u1_struct_0(A_6)) | ~m1_subset_1(B_7, u1_struct_0(A_6)) | ~l1_orders_2(A_6) | ~v2_lattice3(A_6) | ~v5_orders_2(A_6))), inference(cnfTransformation, [status(thm)], [f_59])).
% 8.48/3.12  tff(c_419, plain, (m1_subset_1(k11_lattice3('#skF_3', '#skF_4', '#skF_5'), u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v2_lattice3('#skF_3') | ~v5_orders_2('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_349, c_8])).
% 8.48/3.12  tff(c_423, plain, (m1_subset_1(k11_lattice3('#skF_3', '#skF_4', '#skF_5'), u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_52, c_50, c_48, c_46, c_419])).
% 8.48/3.12  tff(c_36, plain, (![A_55, B_79, C_91]: (r1_orders_2(A_55, k11_lattice3(A_55, B_79, C_91), B_79) | ~m1_subset_1(k11_lattice3(A_55, B_79, C_91), u1_struct_0(A_55)) | ~m1_subset_1(C_91, u1_struct_0(A_55)) | ~m1_subset_1(B_79, u1_struct_0(A_55)) | ~l1_orders_2(A_55) | ~v2_lattice3(A_55) | ~v5_orders_2(A_55) | v2_struct_0(A_55))), inference(cnfTransformation, [status(thm)], [f_125])).
% 8.48/3.12  tff(c_426, plain, (r1_orders_2('#skF_3', k11_lattice3('#skF_3', '#skF_4', '#skF_5'), '#skF_4') | ~m1_subset_1('#skF_5', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v2_lattice3('#skF_3') | ~v5_orders_2('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_423, c_36])).
% 8.48/3.12  tff(c_450, plain, (r1_orders_2('#skF_3', k11_lattice3('#skF_3', '#skF_4', '#skF_5'), '#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_52, c_50, c_48, c_46, c_426])).
% 8.48/3.12  tff(c_469, plain, (v2_struct_0('#skF_3')), inference(splitLeft, [status(thm)], [c_450])).
% 8.48/3.12  tff(c_2, plain, (![A_1]: (~v2_struct_0(A_1) | ~v1_lattice3(A_1) | ~l1_orders_2(A_1))), inference(cnfTransformation, [status(thm)], [f_32])).
% 8.48/3.12  tff(c_472, plain, (~v1_lattice3('#skF_3') | ~l1_orders_2('#skF_3')), inference(resolution, [status(thm)], [c_469, c_2])).
% 8.48/3.12  tff(c_479, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_54, c_472])).
% 8.48/3.12  tff(c_481, plain, (~v2_struct_0('#skF_3')), inference(splitRight, [status(thm)], [c_450])).
% 8.48/3.12  tff(c_6, plain, (![A_3, B_4, C_5]: (m1_subset_1(k10_lattice3(A_3, B_4, C_5), u1_struct_0(A_3)) | ~m1_subset_1(C_5, u1_struct_0(A_3)) | ~m1_subset_1(B_4, u1_struct_0(A_3)) | ~l1_orders_2(A_3))), inference(cnfTransformation, [status(thm)], [f_47])).
% 8.48/3.12  tff(c_4349, plain, (![A_222, B_223, B_224, C_225]: (k12_lattice3(A_222, B_223, k10_lattice3(A_222, B_224, C_225))=k11_lattice3(A_222, B_223, k10_lattice3(A_222, B_224, C_225)) | ~m1_subset_1(B_223, u1_struct_0(A_222)) | ~v2_lattice3(A_222) | ~v5_orders_2(A_222) | ~m1_subset_1(C_225, u1_struct_0(A_222)) | ~m1_subset_1(B_224, u1_struct_0(A_222)) | ~l1_orders_2(A_222))), inference(resolution, [status(thm)], [c_6, c_107])).
% 8.48/3.12  tff(c_4381, plain, (![B_224, C_225]: (k12_lattice3('#skF_3', '#skF_4', k10_lattice3('#skF_3', B_224, C_225))=k11_lattice3('#skF_3', '#skF_4', k10_lattice3('#skF_3', B_224, C_225)) | ~v2_lattice3('#skF_3') | ~v5_orders_2('#skF_3') | ~m1_subset_1(C_225, u1_struct_0('#skF_3')) | ~m1_subset_1(B_224, u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3'))), inference(resolution, [status(thm)], [c_48, c_4349])).
% 8.48/3.12  tff(c_6175, plain, (![B_257, C_258]: (k12_lattice3('#skF_3', '#skF_4', k10_lattice3('#skF_3', B_257, C_258))=k11_lattice3('#skF_3', '#skF_4', k10_lattice3('#skF_3', B_257, C_258)) | ~m1_subset_1(C_258, u1_struct_0('#skF_3')) | ~m1_subset_1(B_257, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_56, c_52, c_4381])).
% 8.48/3.12  tff(c_6630, plain, (![B_264]: (k12_lattice3('#skF_3', '#skF_4', k10_lattice3('#skF_3', B_264, '#skF_5'))=k11_lattice3('#skF_3', '#skF_4', k10_lattice3('#skF_3', B_264, '#skF_5')) | ~m1_subset_1(B_264, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_46, c_6175])).
% 8.48/3.12  tff(c_6723, plain, (k12_lattice3('#skF_3', '#skF_4', k10_lattice3('#skF_3', '#skF_4', '#skF_5'))=k11_lattice3('#skF_3', '#skF_4', k10_lattice3('#skF_3', '#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_48, c_6630])).
% 8.48/3.12  tff(c_63, plain, (![A_126, B_127, C_128]: (k13_lattice3(A_126, B_127, C_128)=k10_lattice3(A_126, B_127, C_128) | ~m1_subset_1(C_128, u1_struct_0(A_126)) | ~m1_subset_1(B_127, u1_struct_0(A_126)) | ~l1_orders_2(A_126) | ~v1_lattice3(A_126) | ~v5_orders_2(A_126))), inference(cnfTransformation, [status(thm)], [f_149])).
% 8.48/3.12  tff(c_69, plain, (![B_127]: (k13_lattice3('#skF_3', B_127, '#skF_5')=k10_lattice3('#skF_3', B_127, '#skF_5') | ~m1_subset_1(B_127, u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v1_lattice3('#skF_3') | ~v5_orders_2('#skF_3'))), inference(resolution, [status(thm)], [c_46, c_63])).
% 8.48/3.12  tff(c_80, plain, (![B_129]: (k13_lattice3('#skF_3', B_129, '#skF_5')=k10_lattice3('#skF_3', B_129, '#skF_5') | ~m1_subset_1(B_129, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_50, c_69])).
% 8.48/3.12  tff(c_102, plain, (k13_lattice3('#skF_3', '#skF_4', '#skF_5')=k10_lattice3('#skF_3', '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_48, c_80])).
% 8.48/3.12  tff(c_44, plain, (k12_lattice3('#skF_3', '#skF_4', k13_lattice3('#skF_3', '#skF_4', '#skF_5'))!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_186])).
% 8.48/3.12  tff(c_124, plain, (k12_lattice3('#skF_3', '#skF_4', k10_lattice3('#skF_3', '#skF_4', '#skF_5'))!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_102, c_44])).
% 8.48/3.12  tff(c_6736, plain, (k11_lattice3('#skF_3', '#skF_4', k10_lattice3('#skF_3', '#skF_4', '#skF_5'))!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_6723, c_124])).
% 8.48/3.12  tff(c_4379, plain, (![B_224, C_225]: (k12_lattice3('#skF_3', '#skF_5', k10_lattice3('#skF_3', B_224, C_225))=k11_lattice3('#skF_3', '#skF_5', k10_lattice3('#skF_3', B_224, C_225)) | ~v2_lattice3('#skF_3') | ~v5_orders_2('#skF_3') | ~m1_subset_1(C_225, u1_struct_0('#skF_3')) | ~m1_subset_1(B_224, u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3'))), inference(resolution, [status(thm)], [c_46, c_4349])).
% 8.48/3.12  tff(c_4450, plain, (![B_226, C_227]: (k12_lattice3('#skF_3', '#skF_5', k10_lattice3('#skF_3', B_226, C_227))=k11_lattice3('#skF_3', '#skF_5', k10_lattice3('#skF_3', B_226, C_227)) | ~m1_subset_1(C_227, u1_struct_0('#skF_3')) | ~m1_subset_1(B_226, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_56, c_52, c_4379])).
% 8.48/3.12  tff(c_4694, plain, (![B_232]: (k12_lattice3('#skF_3', '#skF_5', k10_lattice3('#skF_3', B_232, '#skF_5'))=k11_lattice3('#skF_3', '#skF_5', k10_lattice3('#skF_3', B_232, '#skF_5')) | ~m1_subset_1(B_232, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_46, c_4450])).
% 8.48/3.12  tff(c_4778, plain, (k12_lattice3('#skF_3', '#skF_5', k10_lattice3('#skF_3', '#skF_4', '#skF_5'))=k11_lattice3('#skF_3', '#skF_5', k10_lattice3('#skF_3', '#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_48, c_4694])).
% 8.48/3.12  tff(c_4913, plain, (m1_subset_1(k11_lattice3('#skF_3', '#skF_5', k10_lattice3('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_3')) | ~m1_subset_1(k10_lattice3('#skF_3', '#skF_4', '#skF_5'), u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v2_lattice3('#skF_3') | ~v5_orders_2('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_4778, c_8])).
% 8.48/3.12  tff(c_4917, plain, (m1_subset_1(k11_lattice3('#skF_3', '#skF_5', k10_lattice3('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_3')) | ~m1_subset_1(k10_lattice3('#skF_3', '#skF_4', '#skF_5'), u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_52, c_50, c_46, c_4913])).
% 8.48/3.12  tff(c_6238, plain, (~m1_subset_1(k10_lattice3('#skF_3', '#skF_4', '#skF_5'), u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_4917])).
% 8.48/3.12  tff(c_6241, plain, (~m1_subset_1('#skF_5', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3')), inference(resolution, [status(thm)], [c_6, c_6238])).
% 8.48/3.12  tff(c_6245, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_6241])).
% 8.48/3.12  tff(c_6247, plain, (m1_subset_1(k10_lattice3('#skF_3', '#skF_4', '#skF_5'), u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_4917])).
% 8.48/3.12  tff(c_115, plain, (![B_131]: (k12_lattice3('#skF_3', B_131, '#skF_4')=k11_lattice3('#skF_3', B_131, '#skF_4') | ~m1_subset_1(B_131, u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v2_lattice3('#skF_3') | ~v5_orders_2('#skF_3'))), inference(resolution, [status(thm)], [c_48, c_107])).
% 8.48/3.12  tff(c_160, plain, (![B_134]: (k12_lattice3('#skF_3', B_134, '#skF_4')=k11_lattice3('#skF_3', B_134, '#skF_4') | ~m1_subset_1(B_134, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_52, c_50, c_115])).
% 8.48/3.12  tff(c_182, plain, (k12_lattice3('#skF_3', '#skF_4', '#skF_4')=k11_lattice3('#skF_3', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_48, c_160])).
% 8.48/3.12  tff(c_217, plain, (m1_subset_1(k11_lattice3('#skF_3', '#skF_4', '#skF_4'), u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v2_lattice3('#skF_3') | ~v5_orders_2('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_182, c_8])).
% 8.48/3.12  tff(c_221, plain, (m1_subset_1(k11_lattice3('#skF_3', '#skF_4', '#skF_4'), u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_52, c_50, c_48, c_48, c_217])).
% 8.48/3.12  tff(c_58, plain, (v3_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_186])).
% 8.48/3.12  tff(c_223, plain, (![A_135, B_136, C_137]: (k13_lattice3(A_135, k12_lattice3(A_135, B_136, C_137), C_137)=C_137 | ~m1_subset_1(C_137, u1_struct_0(A_135)) | ~m1_subset_1(B_136, u1_struct_0(A_135)) | ~l1_orders_2(A_135) | ~v2_lattice3(A_135) | ~v1_lattice3(A_135) | ~v5_orders_2(A_135) | ~v3_orders_2(A_135))), inference(cnfTransformation, [status(thm)], [f_167])).
% 8.48/3.12  tff(c_233, plain, (![B_136]: (k13_lattice3('#skF_3', k12_lattice3('#skF_3', B_136, '#skF_4'), '#skF_4')='#skF_4' | ~m1_subset_1(B_136, u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v2_lattice3('#skF_3') | ~v1_lattice3('#skF_3') | ~v5_orders_2('#skF_3') | ~v3_orders_2('#skF_3'))), inference(resolution, [status(thm)], [c_48, c_223])).
% 8.48/3.12  tff(c_493, plain, (![B_146]: (k13_lattice3('#skF_3', k12_lattice3('#skF_3', B_146, '#skF_4'), '#skF_4')='#skF_4' | ~m1_subset_1(B_146, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_52, c_50, c_233])).
% 8.48/3.12  tff(c_519, plain, (k13_lattice3('#skF_3', k12_lattice3('#skF_3', '#skF_4', '#skF_4'), '#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_48, c_493])).
% 8.48/3.12  tff(c_533, plain, (k13_lattice3('#skF_3', k11_lattice3('#skF_3', '#skF_4', '#skF_4'), '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_182, c_519])).
% 8.48/3.12  tff(c_71, plain, (![B_127]: (k13_lattice3('#skF_3', B_127, '#skF_4')=k10_lattice3('#skF_3', B_127, '#skF_4') | ~m1_subset_1(B_127, u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v1_lattice3('#skF_3') | ~v5_orders_2('#skF_3'))), inference(resolution, [status(thm)], [c_48, c_63])).
% 8.48/3.12  tff(c_79, plain, (![B_127]: (k13_lattice3('#skF_3', B_127, '#skF_4')=k10_lattice3('#skF_3', B_127, '#skF_4') | ~m1_subset_1(B_127, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_50, c_71])).
% 8.48/3.12  tff(c_264, plain, (k13_lattice3('#skF_3', k11_lattice3('#skF_3', '#skF_4', '#skF_4'), '#skF_4')=k10_lattice3('#skF_3', k11_lattice3('#skF_3', '#skF_4', '#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_221, c_79])).
% 8.48/3.12  tff(c_576, plain, (k10_lattice3('#skF_3', k11_lattice3('#skF_3', '#skF_4', '#skF_4'), '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_533, c_264])).
% 8.48/3.12  tff(c_20, plain, (![A_9, C_45, B_33]: (r1_orders_2(A_9, C_45, k10_lattice3(A_9, B_33, C_45)) | ~m1_subset_1(k10_lattice3(A_9, B_33, C_45), u1_struct_0(A_9)) | ~m1_subset_1(C_45, u1_struct_0(A_9)) | ~m1_subset_1(B_33, u1_struct_0(A_9)) | ~l1_orders_2(A_9) | ~v1_lattice3(A_9) | ~v5_orders_2(A_9) | v2_struct_0(A_9))), inference(cnfTransformation, [status(thm)], [f_92])).
% 8.48/3.12  tff(c_581, plain, (r1_orders_2('#skF_3', '#skF_4', k10_lattice3('#skF_3', k11_lattice3('#skF_3', '#skF_4', '#skF_4'), '#skF_4')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~m1_subset_1(k11_lattice3('#skF_3', '#skF_4', '#skF_4'), u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v1_lattice3('#skF_3') | ~v5_orders_2('#skF_3') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_576, c_20])).
% 8.48/3.12  tff(c_591, plain, (r1_orders_2('#skF_3', '#skF_4', '#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_50, c_221, c_48, c_48, c_576, c_581])).
% 8.48/3.12  tff(c_592, plain, (r1_orders_2('#skF_3', '#skF_4', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_481, c_591])).
% 8.48/3.12  tff(c_554, plain, (![A_147, B_148, C_149]: (r1_orders_2(A_147, B_148, k10_lattice3(A_147, B_148, C_149)) | ~m1_subset_1(k10_lattice3(A_147, B_148, C_149), u1_struct_0(A_147)) | ~m1_subset_1(C_149, u1_struct_0(A_147)) | ~m1_subset_1(B_148, u1_struct_0(A_147)) | ~l1_orders_2(A_147) | ~v1_lattice3(A_147) | ~v5_orders_2(A_147) | v2_struct_0(A_147))), inference(cnfTransformation, [status(thm)], [f_92])).
% 8.48/3.12  tff(c_557, plain, (![A_3, B_4, C_5]: (r1_orders_2(A_3, B_4, k10_lattice3(A_3, B_4, C_5)) | ~v1_lattice3(A_3) | ~v5_orders_2(A_3) | v2_struct_0(A_3) | ~m1_subset_1(C_5, u1_struct_0(A_3)) | ~m1_subset_1(B_4, u1_struct_0(A_3)) | ~l1_orders_2(A_3))), inference(resolution, [status(thm)], [c_6, c_554])).
% 8.48/3.12  tff(c_26, plain, (![A_55, B_79, C_91, D_97]: (r1_orders_2(A_55, '#skF_2'(A_55, B_79, C_91, D_97), C_91) | k11_lattice3(A_55, B_79, C_91)=D_97 | ~r1_orders_2(A_55, D_97, C_91) | ~r1_orders_2(A_55, D_97, B_79) | ~m1_subset_1(D_97, u1_struct_0(A_55)) | ~m1_subset_1(C_91, u1_struct_0(A_55)) | ~m1_subset_1(B_79, u1_struct_0(A_55)) | ~l1_orders_2(A_55) | ~v2_lattice3(A_55) | ~v5_orders_2(A_55) | v2_struct_0(A_55))), inference(cnfTransformation, [status(thm)], [f_125])).
% 8.48/3.12  tff(c_1273, plain, (![A_169, B_170, C_171, D_172]: (~r1_orders_2(A_169, '#skF_2'(A_169, B_170, C_171, D_172), D_172) | k11_lattice3(A_169, B_170, C_171)=D_172 | ~r1_orders_2(A_169, D_172, C_171) | ~r1_orders_2(A_169, D_172, B_170) | ~m1_subset_1(D_172, u1_struct_0(A_169)) | ~m1_subset_1(C_171, u1_struct_0(A_169)) | ~m1_subset_1(B_170, u1_struct_0(A_169)) | ~l1_orders_2(A_169) | ~v2_lattice3(A_169) | ~v5_orders_2(A_169) | v2_struct_0(A_169))), inference(cnfTransformation, [status(thm)], [f_125])).
% 8.48/3.12  tff(c_3705, plain, (![A_216, B_217, C_218]: (k11_lattice3(A_216, B_217, C_218)=C_218 | ~r1_orders_2(A_216, C_218, C_218) | ~r1_orders_2(A_216, C_218, B_217) | ~m1_subset_1(C_218, u1_struct_0(A_216)) | ~m1_subset_1(B_217, u1_struct_0(A_216)) | ~l1_orders_2(A_216) | ~v2_lattice3(A_216) | ~v5_orders_2(A_216) | v2_struct_0(A_216))), inference(resolution, [status(thm)], [c_26, c_1273])).
% 8.48/3.12  tff(c_3715, plain, (![B_217]: (k11_lattice3('#skF_3', B_217, '#skF_4')='#skF_4' | ~r1_orders_2('#skF_3', '#skF_4', B_217) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~m1_subset_1(B_217, u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v2_lattice3('#skF_3') | ~v5_orders_2('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_592, c_3705])).
% 8.48/3.12  tff(c_3730, plain, (![B_217]: (k11_lattice3('#skF_3', B_217, '#skF_4')='#skF_4' | ~r1_orders_2('#skF_3', '#skF_4', B_217) | ~m1_subset_1(B_217, u1_struct_0('#skF_3')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_52, c_50, c_48, c_3715])).
% 8.48/3.12  tff(c_3731, plain, (![B_217]: (k11_lattice3('#skF_3', B_217, '#skF_4')='#skF_4' | ~r1_orders_2('#skF_3', '#skF_4', B_217) | ~m1_subset_1(B_217, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_481, c_3730])).
% 8.48/3.12  tff(c_6316, plain, (k11_lattice3('#skF_3', k10_lattice3('#skF_3', '#skF_4', '#skF_5'), '#skF_4')='#skF_4' | ~r1_orders_2('#skF_3', '#skF_4', k10_lattice3('#skF_3', '#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_6247, c_3731])).
% 8.48/3.12  tff(c_8172, plain, (~r1_orders_2('#skF_3', '#skF_4', k10_lattice3('#skF_3', '#skF_4', '#skF_5'))), inference(splitLeft, [status(thm)], [c_6316])).
% 8.48/3.12  tff(c_8175, plain, (~v1_lattice3('#skF_3') | ~v5_orders_2('#skF_3') | v2_struct_0('#skF_3') | ~m1_subset_1('#skF_5', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3')), inference(resolution, [status(thm)], [c_557, c_8172])).
% 8.48/3.12  tff(c_8178, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_56, c_54, c_8175])).
% 8.48/3.12  tff(c_8180, plain, $false, inference(negUnitSimplification, [status(thm)], [c_481, c_8178])).
% 8.48/3.12  tff(c_8182, plain, (r1_orders_2('#skF_3', '#skF_4', k10_lattice3('#skF_3', '#skF_4', '#skF_5'))), inference(splitRight, [status(thm)], [c_6316])).
% 8.48/3.12  tff(c_1432, plain, (![A_178, B_179, C_180, D_181]: (r1_orders_2(A_178, '#skF_2'(A_178, B_179, C_180, D_181), B_179) | k11_lattice3(A_178, B_179, C_180)=D_181 | ~r1_orders_2(A_178, D_181, C_180) | ~r1_orders_2(A_178, D_181, B_179) | ~m1_subset_1(D_181, u1_struct_0(A_178)) | ~m1_subset_1(C_180, u1_struct_0(A_178)) | ~m1_subset_1(B_179, u1_struct_0(A_178)) | ~l1_orders_2(A_178) | ~v2_lattice3(A_178) | ~v5_orders_2(A_178) | v2_struct_0(A_178))), inference(cnfTransformation, [status(thm)], [f_125])).
% 8.48/3.12  tff(c_24, plain, (![A_55, B_79, C_91, D_97]: (~r1_orders_2(A_55, '#skF_2'(A_55, B_79, C_91, D_97), D_97) | k11_lattice3(A_55, B_79, C_91)=D_97 | ~r1_orders_2(A_55, D_97, C_91) | ~r1_orders_2(A_55, D_97, B_79) | ~m1_subset_1(D_97, u1_struct_0(A_55)) | ~m1_subset_1(C_91, u1_struct_0(A_55)) | ~m1_subset_1(B_79, u1_struct_0(A_55)) | ~l1_orders_2(A_55) | ~v2_lattice3(A_55) | ~v5_orders_2(A_55) | v2_struct_0(A_55))), inference(cnfTransformation, [status(thm)], [f_125])).
% 8.48/3.12  tff(c_1437, plain, (![A_178, B_179, C_180]: (k11_lattice3(A_178, B_179, C_180)=B_179 | ~r1_orders_2(A_178, B_179, C_180) | ~r1_orders_2(A_178, B_179, B_179) | ~m1_subset_1(C_180, u1_struct_0(A_178)) | ~m1_subset_1(B_179, u1_struct_0(A_178)) | ~l1_orders_2(A_178) | ~v2_lattice3(A_178) | ~v5_orders_2(A_178) | v2_struct_0(A_178))), inference(resolution, [status(thm)], [c_1432, c_24])).
% 8.48/3.12  tff(c_8184, plain, (k11_lattice3('#skF_3', '#skF_4', k10_lattice3('#skF_3', '#skF_4', '#skF_5'))='#skF_4' | ~r1_orders_2('#skF_3', '#skF_4', '#skF_4') | ~m1_subset_1(k10_lattice3('#skF_3', '#skF_4', '#skF_5'), u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v2_lattice3('#skF_3') | ~v5_orders_2('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_8182, c_1437])).
% 8.48/3.12  tff(c_8189, plain, (k11_lattice3('#skF_3', '#skF_4', k10_lattice3('#skF_3', '#skF_4', '#skF_5'))='#skF_4' | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_52, c_50, c_48, c_6247, c_592, c_8184])).
% 8.48/3.12  tff(c_8191, plain, $false, inference(negUnitSimplification, [status(thm)], [c_481, c_6736, c_8189])).
% 8.48/3.12  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.48/3.12  
% 8.48/3.12  Inference rules
% 8.48/3.12  ----------------------
% 8.48/3.12  #Ref     : 0
% 8.48/3.12  #Sup     : 1773
% 8.48/3.12  #Fact    : 0
% 8.48/3.12  #Define  : 0
% 8.48/3.12  #Split   : 12
% 8.48/3.12  #Chain   : 0
% 8.48/3.12  #Close   : 0
% 8.48/3.12  
% 8.48/3.12  Ordering : KBO
% 8.48/3.12  
% 8.48/3.12  Simplification rules
% 8.48/3.12  ----------------------
% 8.48/3.12  #Subsume      : 80
% 8.48/3.12  #Demod        : 4583
% 8.48/3.12  #Tautology    : 643
% 8.48/3.12  #SimpNegUnit  : 444
% 8.48/3.12  #BackRed      : 107
% 8.48/3.12  
% 8.48/3.12  #Partial instantiations: 0
% 8.48/3.12  #Strategies tried      : 1
% 8.48/3.12  
% 8.48/3.12  Timing (in seconds)
% 8.48/3.12  ----------------------
% 8.48/3.13  Preprocessing        : 0.35
% 8.48/3.13  Parsing              : 0.18
% 8.48/3.13  CNF conversion       : 0.03
% 8.48/3.13  Main loop            : 2.01
% 8.48/3.13  Inferencing          : 0.48
% 8.48/3.13  Reduction            : 0.89
% 8.48/3.13  Demodulation         : 0.72
% 8.48/3.13  BG Simplification    : 0.07
% 8.48/3.13  Subsumption          : 0.45
% 8.48/3.13  Abstraction          : 0.10
% 8.48/3.13  MUC search           : 0.00
% 8.48/3.13  Cooper               : 0.00
% 8.48/3.13  Total                : 2.40
% 8.48/3.13  Index Insertion      : 0.00
% 8.48/3.13  Index Deletion       : 0.00
% 8.48/3.13  Index Matching       : 0.00
% 8.48/3.13  BG Taut test         : 0.00
%------------------------------------------------------------------------------
