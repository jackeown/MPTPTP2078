%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:41 EST 2020

% Result     : Theorem 6.41s
% Output     : CNFRefutation 6.41s
% Verified   : 
% Statistics : Number of formulae       :  108 (1213 expanded)
%              Number of leaves         :   31 ( 456 expanded)
%              Depth                    :   26
%              Number of atoms          :  353 (5745 expanded)
%              Number of equality atoms :   38 ( 484 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_orders_2 > r1_orders_2 > m1_subset_1 > v5_orders_2 > v3_orders_2 > v2_struct_0 > v2_lattice3 > v1_lattice3 > l1_orders_2 > k13_lattice3 > k12_lattice3 > k11_lattice3 > k10_lattice3 > #nlpp > u1_struct_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(r3_orders_2,type,(
    r3_orders_2: ( $i * $i * $i ) > $o )).

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

tff(f_184,negated_conjecture,(
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

tff(f_53,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => r3_orders_2(A,B,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r3_orders_2)).

tff(f_67,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v2_lattice3(A)
       => ~ v2_struct_0(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_lattice3)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( ( l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => m1_subset_1(k10_lattice3(A,B,C),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k10_lattice3)).

tff(f_153,axiom,(
    ! [A,B,C] :
      ( ( v5_orders_2(A)
        & v2_lattice3(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => k12_lattice3(A,B,C) = k11_lattice3(A,B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k12_lattice3)).

tff(f_165,axiom,(
    ! [A,B,C] :
      ( ( v5_orders_2(A)
        & v1_lattice3(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => k13_lattice3(A,B,C) = k10_lattice3(A,B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k13_lattice3)).

tff(f_108,axiom,(
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

tff(f_141,axiom,(
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

tff(c_52,plain,(
    l1_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_54,plain,(
    v2_lattice3('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_60,plain,(
    v3_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_48,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_64,plain,(
    ! [A_119,B_120,C_121] :
      ( r3_orders_2(A_119,B_120,B_120)
      | ~ m1_subset_1(C_121,u1_struct_0(A_119))
      | ~ m1_subset_1(B_120,u1_struct_0(A_119))
      | ~ l1_orders_2(A_119)
      | ~ v3_orders_2(A_119)
      | v2_struct_0(A_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_68,plain,(
    ! [B_120] :
      ( r3_orders_2('#skF_3',B_120,B_120)
      | ~ m1_subset_1(B_120,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | ~ v3_orders_2('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_48,c_64])).

tff(c_74,plain,(
    ! [B_120] :
      ( r3_orders_2('#skF_3',B_120,B_120)
      | ~ m1_subset_1(B_120,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_52,c_68])).

tff(c_78,plain,(
    v2_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_74])).

tff(c_10,plain,(
    ! [A_8] :
      ( ~ v2_struct_0(A_8)
      | ~ v2_lattice3(A_8)
      | ~ l1_orders_2(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_81,plain,
    ( ~ v2_lattice3('#skF_3')
    | ~ l1_orders_2('#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_10])).

tff(c_88,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_54,c_81])).

tff(c_90,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_50,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_58,plain,(
    v5_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_12,plain,(
    ! [A_9,B_10,C_11] :
      ( m1_subset_1(k10_lattice3(A_9,B_10,C_11),u1_struct_0(A_9))
      | ~ m1_subset_1(C_11,u1_struct_0(A_9))
      | ~ m1_subset_1(B_10,u1_struct_0(A_9))
      | ~ l1_orders_2(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_91,plain,(
    ! [A_122,B_123,C_124] :
      ( k12_lattice3(A_122,B_123,C_124) = k11_lattice3(A_122,B_123,C_124)
      | ~ m1_subset_1(C_124,u1_struct_0(A_122))
      | ~ m1_subset_1(B_123,u1_struct_0(A_122))
      | ~ l1_orders_2(A_122)
      | ~ v2_lattice3(A_122)
      | ~ v5_orders_2(A_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_664,plain,(
    ! [A_207,B_208,B_209,C_210] :
      ( k12_lattice3(A_207,B_208,k10_lattice3(A_207,B_209,C_210)) = k11_lattice3(A_207,B_208,k10_lattice3(A_207,B_209,C_210))
      | ~ m1_subset_1(B_208,u1_struct_0(A_207))
      | ~ v2_lattice3(A_207)
      | ~ v5_orders_2(A_207)
      | ~ m1_subset_1(C_210,u1_struct_0(A_207))
      | ~ m1_subset_1(B_209,u1_struct_0(A_207))
      | ~ l1_orders_2(A_207) ) ),
    inference(resolution,[status(thm)],[c_12,c_91])).

tff(c_670,plain,(
    ! [B_209,C_210] :
      ( k12_lattice3('#skF_3','#skF_4',k10_lattice3('#skF_3',B_209,C_210)) = k11_lattice3('#skF_3','#skF_4',k10_lattice3('#skF_3',B_209,C_210))
      | ~ v2_lattice3('#skF_3')
      | ~ v5_orders_2('#skF_3')
      | ~ m1_subset_1(C_210,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(B_209,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_50,c_664])).

tff(c_745,plain,(
    ! [B_219,C_220] :
      ( k12_lattice3('#skF_3','#skF_4',k10_lattice3('#skF_3',B_219,C_220)) = k11_lattice3('#skF_3','#skF_4',k10_lattice3('#skF_3',B_219,C_220))
      | ~ m1_subset_1(C_220,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(B_219,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_58,c_54,c_670])).

tff(c_758,plain,(
    ! [B_221] :
      ( k12_lattice3('#skF_3','#skF_4',k10_lattice3('#skF_3',B_221,'#skF_5')) = k11_lattice3('#skF_3','#skF_4',k10_lattice3('#skF_3',B_221,'#skF_5'))
      | ~ m1_subset_1(B_221,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_48,c_745])).

tff(c_773,plain,(
    k12_lattice3('#skF_3','#skF_4',k10_lattice3('#skF_3','#skF_4','#skF_5')) = k11_lattice3('#skF_3','#skF_4',k10_lattice3('#skF_3','#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_50,c_758])).

tff(c_56,plain,(
    v1_lattice3('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_163,plain,(
    ! [A_128,B_129,C_130] :
      ( k13_lattice3(A_128,B_129,C_130) = k10_lattice3(A_128,B_129,C_130)
      | ~ m1_subset_1(C_130,u1_struct_0(A_128))
      | ~ m1_subset_1(B_129,u1_struct_0(A_128))
      | ~ l1_orders_2(A_128)
      | ~ v1_lattice3(A_128)
      | ~ v5_orders_2(A_128) ) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_167,plain,(
    ! [B_129] :
      ( k13_lattice3('#skF_3',B_129,'#skF_5') = k10_lattice3('#skF_3',B_129,'#skF_5')
      | ~ m1_subset_1(B_129,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | ~ v1_lattice3('#skF_3')
      | ~ v5_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_48,c_163])).

tff(c_181,plain,(
    ! [B_131] :
      ( k13_lattice3('#skF_3',B_131,'#skF_5') = k10_lattice3('#skF_3',B_131,'#skF_5')
      | ~ m1_subset_1(B_131,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_52,c_167])).

tff(c_196,plain,(
    k13_lattice3('#skF_3','#skF_4','#skF_5') = k10_lattice3('#skF_3','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_181])).

tff(c_46,plain,(
    k12_lattice3('#skF_3','#skF_4',k13_lattice3('#skF_3','#skF_4','#skF_5')) != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_201,plain,(
    k12_lattice3('#skF_3','#skF_4',k10_lattice3('#skF_3','#skF_4','#skF_5')) != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_196,c_46])).

tff(c_778,plain,(
    k11_lattice3('#skF_3','#skF_4',k10_lattice3('#skF_3','#skF_4','#skF_5')) != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_773,c_201])).

tff(c_304,plain,(
    ! [A_143,C_144,B_145] :
      ( r1_orders_2(A_143,C_144,k10_lattice3(A_143,B_145,C_144))
      | ~ m1_subset_1(k10_lattice3(A_143,B_145,C_144),u1_struct_0(A_143))
      | ~ m1_subset_1(C_144,u1_struct_0(A_143))
      | ~ m1_subset_1(B_145,u1_struct_0(A_143))
      | ~ l1_orders_2(A_143)
      | ~ v1_lattice3(A_143)
      | ~ v5_orders_2(A_143)
      | v2_struct_0(A_143) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_307,plain,(
    ! [A_9,C_11,B_10] :
      ( r1_orders_2(A_9,C_11,k10_lattice3(A_9,B_10,C_11))
      | ~ v1_lattice3(A_9)
      | ~ v5_orders_2(A_9)
      | v2_struct_0(A_9)
      | ~ m1_subset_1(C_11,u1_struct_0(A_9))
      | ~ m1_subset_1(B_10,u1_struct_0(A_9))
      | ~ l1_orders_2(A_9) ) ),
    inference(resolution,[status(thm)],[c_12,c_304])).

tff(c_105,plain,(
    ! [B_125] :
      ( r3_orders_2('#skF_3',B_125,B_125)
      | ~ m1_subset_1(B_125,u1_struct_0('#skF_3')) ) ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_116,plain,(
    r3_orders_2('#skF_3','#skF_5','#skF_5') ),
    inference(resolution,[status(thm)],[c_48,c_105])).

tff(c_231,plain,(
    ! [A_135,B_136,C_137] :
      ( r1_orders_2(A_135,B_136,C_137)
      | ~ r3_orders_2(A_135,B_136,C_137)
      | ~ m1_subset_1(C_137,u1_struct_0(A_135))
      | ~ m1_subset_1(B_136,u1_struct_0(A_135))
      | ~ l1_orders_2(A_135)
      | ~ v3_orders_2(A_135)
      | v2_struct_0(A_135) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_237,plain,
    ( r1_orders_2('#skF_3','#skF_5','#skF_5')
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
    | ~ l1_orders_2('#skF_3')
    | ~ v3_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_116,c_231])).

tff(c_248,plain,
    ( r1_orders_2('#skF_3','#skF_5','#skF_5')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_52,c_48,c_237])).

tff(c_249,plain,(
    r1_orders_2('#skF_3','#skF_5','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_248])).

tff(c_1541,plain,(
    ! [A_269,B_270,C_271,D_272] :
      ( r1_orders_2(A_269,'#skF_2'(A_269,B_270,C_271,D_272),C_271)
      | k11_lattice3(A_269,B_270,C_271) = D_272
      | ~ r1_orders_2(A_269,D_272,C_271)
      | ~ r1_orders_2(A_269,D_272,B_270)
      | ~ m1_subset_1(D_272,u1_struct_0(A_269))
      | ~ m1_subset_1(C_271,u1_struct_0(A_269))
      | ~ m1_subset_1(B_270,u1_struct_0(A_269))
      | ~ l1_orders_2(A_269)
      | ~ v2_lattice3(A_269)
      | ~ v5_orders_2(A_269)
      | v2_struct_0(A_269) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_28,plain,(
    ! [A_58,B_82,C_94,D_100] :
      ( ~ r1_orders_2(A_58,'#skF_2'(A_58,B_82,C_94,D_100),D_100)
      | k11_lattice3(A_58,B_82,C_94) = D_100
      | ~ r1_orders_2(A_58,D_100,C_94)
      | ~ r1_orders_2(A_58,D_100,B_82)
      | ~ m1_subset_1(D_100,u1_struct_0(A_58))
      | ~ m1_subset_1(C_94,u1_struct_0(A_58))
      | ~ m1_subset_1(B_82,u1_struct_0(A_58))
      | ~ l1_orders_2(A_58)
      | ~ v2_lattice3(A_58)
      | ~ v5_orders_2(A_58)
      | v2_struct_0(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_2117,plain,(
    ! [A_300,B_301,C_302] :
      ( k11_lattice3(A_300,B_301,C_302) = C_302
      | ~ r1_orders_2(A_300,C_302,C_302)
      | ~ r1_orders_2(A_300,C_302,B_301)
      | ~ m1_subset_1(C_302,u1_struct_0(A_300))
      | ~ m1_subset_1(B_301,u1_struct_0(A_300))
      | ~ l1_orders_2(A_300)
      | ~ v2_lattice3(A_300)
      | ~ v5_orders_2(A_300)
      | v2_struct_0(A_300) ) ),
    inference(resolution,[status(thm)],[c_1541,c_28])).

tff(c_2121,plain,(
    ! [B_301] :
      ( k11_lattice3('#skF_3',B_301,'#skF_5') = '#skF_5'
      | ~ r1_orders_2('#skF_3','#skF_5',B_301)
      | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
      | ~ m1_subset_1(B_301,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | ~ v2_lattice3('#skF_3')
      | ~ v5_orders_2('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_249,c_2117])).

tff(c_2130,plain,(
    ! [B_301] :
      ( k11_lattice3('#skF_3',B_301,'#skF_5') = '#skF_5'
      | ~ r1_orders_2('#skF_3','#skF_5',B_301)
      | ~ m1_subset_1(B_301,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_54,c_52,c_48,c_2121])).

tff(c_2136,plain,(
    ! [B_303] :
      ( k11_lattice3('#skF_3',B_303,'#skF_5') = '#skF_5'
      | ~ r1_orders_2('#skF_3','#skF_5',B_303)
      | ~ m1_subset_1(B_303,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_2130])).

tff(c_2148,plain,(
    ! [B_10,C_11] :
      ( k11_lattice3('#skF_3',k10_lattice3('#skF_3',B_10,C_11),'#skF_5') = '#skF_5'
      | ~ r1_orders_2('#skF_3','#skF_5',k10_lattice3('#skF_3',B_10,C_11))
      | ~ m1_subset_1(C_11,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(B_10,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_12,c_2136])).

tff(c_2223,plain,(
    ! [B_308,C_309] :
      ( k11_lattice3('#skF_3',k10_lattice3('#skF_3',B_308,C_309),'#skF_5') = '#skF_5'
      | ~ r1_orders_2('#skF_3','#skF_5',k10_lattice3('#skF_3',B_308,C_309))
      | ~ m1_subset_1(C_309,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(B_308,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_2148])).

tff(c_2233,plain,(
    ! [B_10] :
      ( k11_lattice3('#skF_3',k10_lattice3('#skF_3',B_10,'#skF_5'),'#skF_5') = '#skF_5'
      | ~ v1_lattice3('#skF_3')
      | ~ v5_orders_2('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
      | ~ m1_subset_1(B_10,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_307,c_2223])).

tff(c_2244,plain,(
    ! [B_10] :
      ( k11_lattice3('#skF_3',k10_lattice3('#skF_3',B_10,'#skF_5'),'#skF_5') = '#skF_5'
      | v2_struct_0('#skF_3')
      | ~ m1_subset_1(B_10,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_48,c_58,c_56,c_2233])).

tff(c_2250,plain,(
    ! [B_310] :
      ( k11_lattice3('#skF_3',k10_lattice3('#skF_3',B_310,'#skF_5'),'#skF_5') = '#skF_5'
      | ~ m1_subset_1(B_310,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_2244])).

tff(c_2282,plain,(
    k11_lattice3('#skF_3',k10_lattice3('#skF_3','#skF_4','#skF_5'),'#skF_5') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_50,c_2250])).

tff(c_40,plain,(
    ! [A_58,B_82,C_94] :
      ( r1_orders_2(A_58,k11_lattice3(A_58,B_82,C_94),B_82)
      | ~ m1_subset_1(k11_lattice3(A_58,B_82,C_94),u1_struct_0(A_58))
      | ~ m1_subset_1(C_94,u1_struct_0(A_58))
      | ~ m1_subset_1(B_82,u1_struct_0(A_58))
      | ~ l1_orders_2(A_58)
      | ~ v2_lattice3(A_58)
      | ~ v5_orders_2(A_58)
      | v2_struct_0(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_2286,plain,
    ( r1_orders_2('#skF_3',k11_lattice3('#skF_3',k10_lattice3('#skF_3','#skF_4','#skF_5'),'#skF_5'),k10_lattice3('#skF_3','#skF_4','#skF_5'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
    | ~ m1_subset_1(k10_lattice3('#skF_3','#skF_4','#skF_5'),u1_struct_0('#skF_3'))
    | ~ l1_orders_2('#skF_3')
    | ~ v2_lattice3('#skF_3')
    | ~ v5_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2282,c_40])).

tff(c_2292,plain,
    ( r1_orders_2('#skF_3','#skF_5',k10_lattice3('#skF_3','#skF_4','#skF_5'))
    | ~ m1_subset_1(k10_lattice3('#skF_3','#skF_4','#skF_5'),u1_struct_0('#skF_3'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_54,c_52,c_48,c_48,c_2282,c_2286])).

tff(c_2293,plain,
    ( r1_orders_2('#skF_3','#skF_5',k10_lattice3('#skF_3','#skF_4','#skF_5'))
    | ~ m1_subset_1(k10_lattice3('#skF_3','#skF_4','#skF_5'),u1_struct_0('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_2292])).

tff(c_2368,plain,(
    ~ m1_subset_1(k10_lattice3('#skF_3','#skF_4','#skF_5'),u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_2293])).

tff(c_2372,plain,
    ( ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ l1_orders_2('#skF_3') ),
    inference(resolution,[status(thm)],[c_12,c_2368])).

tff(c_2376,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_2372])).

tff(c_2378,plain,(
    m1_subset_1(k10_lattice3('#skF_3','#skF_4','#skF_5'),u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_2293])).

tff(c_117,plain,(
    r3_orders_2('#skF_3','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_105])).

tff(c_235,plain,
    ( r1_orders_2('#skF_3','#skF_4','#skF_4')
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ l1_orders_2('#skF_3')
    | ~ v3_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_117,c_231])).

tff(c_244,plain,
    ( r1_orders_2('#skF_3','#skF_4','#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_52,c_50,c_235])).

tff(c_245,plain,(
    r1_orders_2('#skF_3','#skF_4','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_244])).

tff(c_556,plain,(
    ! [A_175,B_176,C_177] :
      ( r1_orders_2(A_175,B_176,k10_lattice3(A_175,B_176,C_177))
      | ~ m1_subset_1(k10_lattice3(A_175,B_176,C_177),u1_struct_0(A_175))
      | ~ m1_subset_1(C_177,u1_struct_0(A_175))
      | ~ m1_subset_1(B_176,u1_struct_0(A_175))
      | ~ l1_orders_2(A_175)
      | ~ v1_lattice3(A_175)
      | ~ v5_orders_2(A_175)
      | v2_struct_0(A_175) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_559,plain,(
    ! [A_9,B_10,C_11] :
      ( r1_orders_2(A_9,B_10,k10_lattice3(A_9,B_10,C_11))
      | ~ v1_lattice3(A_9)
      | ~ v5_orders_2(A_9)
      | v2_struct_0(A_9)
      | ~ m1_subset_1(C_11,u1_struct_0(A_9))
      | ~ m1_subset_1(B_10,u1_struct_0(A_9))
      | ~ l1_orders_2(A_9) ) ),
    inference(resolution,[status(thm)],[c_12,c_556])).

tff(c_2123,plain,(
    ! [B_301] :
      ( k11_lattice3('#skF_3',B_301,'#skF_4') = '#skF_4'
      | ~ r1_orders_2('#skF_3','#skF_4',B_301)
      | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
      | ~ m1_subset_1(B_301,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | ~ v2_lattice3('#skF_3')
      | ~ v5_orders_2('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_245,c_2117])).

tff(c_2134,plain,(
    ! [B_301] :
      ( k11_lattice3('#skF_3',B_301,'#skF_4') = '#skF_4'
      | ~ r1_orders_2('#skF_3','#skF_4',B_301)
      | ~ m1_subset_1(B_301,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_54,c_52,c_50,c_2123])).

tff(c_2135,plain,(
    ! [B_301] :
      ( k11_lattice3('#skF_3',B_301,'#skF_4') = '#skF_4'
      | ~ r1_orders_2('#skF_3','#skF_4',B_301)
      | ~ m1_subset_1(B_301,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_2134])).

tff(c_2521,plain,
    ( k11_lattice3('#skF_3',k10_lattice3('#skF_3','#skF_4','#skF_5'),'#skF_4') = '#skF_4'
    | ~ r1_orders_2('#skF_3','#skF_4',k10_lattice3('#skF_3','#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_2378,c_2135])).

tff(c_3999,plain,(
    ~ r1_orders_2('#skF_3','#skF_4',k10_lattice3('#skF_3','#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_2521])).

tff(c_4003,plain,
    ( ~ v1_lattice3('#skF_3')
    | ~ v5_orders_2('#skF_3')
    | v2_struct_0('#skF_3')
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ l1_orders_2('#skF_3') ),
    inference(resolution,[status(thm)],[c_559,c_3999])).

tff(c_4006,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_58,c_56,c_4003])).

tff(c_4008,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_4006])).

tff(c_4010,plain,(
    r1_orders_2('#skF_3','#skF_4',k10_lattice3('#skF_3','#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_2521])).

tff(c_1680,plain,(
    ! [A_280,B_281,C_282,D_283] :
      ( r1_orders_2(A_280,'#skF_2'(A_280,B_281,C_282,D_283),B_281)
      | k11_lattice3(A_280,B_281,C_282) = D_283
      | ~ r1_orders_2(A_280,D_283,C_282)
      | ~ r1_orders_2(A_280,D_283,B_281)
      | ~ m1_subset_1(D_283,u1_struct_0(A_280))
      | ~ m1_subset_1(C_282,u1_struct_0(A_280))
      | ~ m1_subset_1(B_281,u1_struct_0(A_280))
      | ~ l1_orders_2(A_280)
      | ~ v2_lattice3(A_280)
      | ~ v5_orders_2(A_280)
      | v2_struct_0(A_280) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_1688,plain,(
    ! [A_280,B_281,C_282] :
      ( k11_lattice3(A_280,B_281,C_282) = B_281
      | ~ r1_orders_2(A_280,B_281,C_282)
      | ~ r1_orders_2(A_280,B_281,B_281)
      | ~ m1_subset_1(C_282,u1_struct_0(A_280))
      | ~ m1_subset_1(B_281,u1_struct_0(A_280))
      | ~ l1_orders_2(A_280)
      | ~ v2_lattice3(A_280)
      | ~ v5_orders_2(A_280)
      | v2_struct_0(A_280) ) ),
    inference(resolution,[status(thm)],[c_1680,c_28])).

tff(c_4012,plain,
    ( k11_lattice3('#skF_3','#skF_4',k10_lattice3('#skF_3','#skF_4','#skF_5')) = '#skF_4'
    | ~ r1_orders_2('#skF_3','#skF_4','#skF_4')
    | ~ m1_subset_1(k10_lattice3('#skF_3','#skF_4','#skF_5'),u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ l1_orders_2('#skF_3')
    | ~ v2_lattice3('#skF_3')
    | ~ v5_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_4010,c_1688])).

tff(c_4017,plain,
    ( k11_lattice3('#skF_3','#skF_4',k10_lattice3('#skF_3','#skF_4','#skF_5')) = '#skF_4'
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_54,c_52,c_50,c_2378,c_245,c_4012])).

tff(c_4019,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_778,c_4017])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:36:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.41/2.24  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.41/2.25  
% 6.41/2.25  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.41/2.25  %$ r3_orders_2 > r1_orders_2 > m1_subset_1 > v5_orders_2 > v3_orders_2 > v2_struct_0 > v2_lattice3 > v1_lattice3 > l1_orders_2 > k13_lattice3 > k12_lattice3 > k11_lattice3 > k10_lattice3 > #nlpp > u1_struct_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 6.41/2.25  
% 6.41/2.25  %Foreground sorts:
% 6.41/2.25  
% 6.41/2.25  
% 6.41/2.25  %Background operators:
% 6.41/2.25  
% 6.41/2.25  
% 6.41/2.25  %Foreground operators:
% 6.41/2.25  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 6.41/2.25  tff(r3_orders_2, type, r3_orders_2: ($i * $i * $i) > $o).
% 6.41/2.25  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 6.41/2.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.41/2.25  tff(k13_lattice3, type, k13_lattice3: ($i * $i * $i) > $i).
% 6.41/2.25  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 6.41/2.25  tff(k10_lattice3, type, k10_lattice3: ($i * $i * $i) > $i).
% 6.41/2.25  tff(k11_lattice3, type, k11_lattice3: ($i * $i * $i) > $i).
% 6.41/2.25  tff(v1_lattice3, type, v1_lattice3: $i > $o).
% 6.41/2.25  tff('#skF_5', type, '#skF_5': $i).
% 6.41/2.25  tff(k12_lattice3, type, k12_lattice3: ($i * $i * $i) > $i).
% 6.41/2.25  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 6.41/2.25  tff('#skF_3', type, '#skF_3': $i).
% 6.41/2.25  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 6.41/2.25  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 6.41/2.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.41/2.25  tff('#skF_4', type, '#skF_4': $i).
% 6.41/2.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.41/2.25  tff(v2_lattice3, type, v2_lattice3: $i > $o).
% 6.41/2.25  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 6.41/2.25  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 6.41/2.25  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.41/2.25  
% 6.41/2.27  tff(f_184, negated_conjecture, ~(![A]: (((((v3_orders_2(A) & v5_orders_2(A)) & v1_lattice3(A)) & v2_lattice3(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (k12_lattice3(A, B, k13_lattice3(A, B, C)) = B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_lattice3)).
% 6.41/2.27  tff(f_53, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v3_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => r3_orders_2(A, B, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', reflexivity_r3_orders_2)).
% 6.41/2.27  tff(f_67, axiom, (![A]: (l1_orders_2(A) => (v2_lattice3(A) => ~v2_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_lattice3)).
% 6.41/2.27  tff(f_75, axiom, (![A, B, C]: (((l1_orders_2(A) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => m1_subset_1(k10_lattice3(A, B, C), u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k10_lattice3)).
% 6.41/2.27  tff(f_153, axiom, (![A, B, C]: (((((v5_orders_2(A) & v2_lattice3(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (k12_lattice3(A, B, C) = k11_lattice3(A, B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k12_lattice3)).
% 6.41/2.27  tff(f_165, axiom, (![A, B, C]: (((((v5_orders_2(A) & v1_lattice3(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (k13_lattice3(A, B, C) = k10_lattice3(A, B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k13_lattice3)).
% 6.41/2.27  tff(f_108, axiom, (![A]: ((((~v2_struct_0(A) & v5_orders_2(A)) & v1_lattice3(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => ((D = k10_lattice3(A, B, C)) <=> ((r1_orders_2(A, B, D) & r1_orders_2(A, C, D)) & (![E]: (m1_subset_1(E, u1_struct_0(A)) => ((r1_orders_2(A, B, E) & r1_orders_2(A, C, E)) => r1_orders_2(A, D, E)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l26_lattice3)).
% 6.41/2.27  tff(f_40, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v3_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (r3_orders_2(A, B, C) <=> r1_orders_2(A, B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r3_orders_2)).
% 6.41/2.27  tff(f_141, axiom, (![A]: ((((~v2_struct_0(A) & v5_orders_2(A)) & v2_lattice3(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => ((D = k11_lattice3(A, B, C)) <=> ((r1_orders_2(A, D, B) & r1_orders_2(A, D, C)) & (![E]: (m1_subset_1(E, u1_struct_0(A)) => ((r1_orders_2(A, E, B) & r1_orders_2(A, E, C)) => r1_orders_2(A, E, D)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l28_lattice3)).
% 6.41/2.27  tff(c_52, plain, (l1_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_184])).
% 6.41/2.27  tff(c_54, plain, (v2_lattice3('#skF_3')), inference(cnfTransformation, [status(thm)], [f_184])).
% 6.41/2.27  tff(c_60, plain, (v3_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_184])).
% 6.41/2.27  tff(c_48, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_184])).
% 6.41/2.27  tff(c_64, plain, (![A_119, B_120, C_121]: (r3_orders_2(A_119, B_120, B_120) | ~m1_subset_1(C_121, u1_struct_0(A_119)) | ~m1_subset_1(B_120, u1_struct_0(A_119)) | ~l1_orders_2(A_119) | ~v3_orders_2(A_119) | v2_struct_0(A_119))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.41/2.27  tff(c_68, plain, (![B_120]: (r3_orders_2('#skF_3', B_120, B_120) | ~m1_subset_1(B_120, u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_48, c_64])).
% 6.41/2.27  tff(c_74, plain, (![B_120]: (r3_orders_2('#skF_3', B_120, B_120) | ~m1_subset_1(B_120, u1_struct_0('#skF_3')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_52, c_68])).
% 6.41/2.27  tff(c_78, plain, (v2_struct_0('#skF_3')), inference(splitLeft, [status(thm)], [c_74])).
% 6.41/2.27  tff(c_10, plain, (![A_8]: (~v2_struct_0(A_8) | ~v2_lattice3(A_8) | ~l1_orders_2(A_8))), inference(cnfTransformation, [status(thm)], [f_67])).
% 6.41/2.27  tff(c_81, plain, (~v2_lattice3('#skF_3') | ~l1_orders_2('#skF_3')), inference(resolution, [status(thm)], [c_78, c_10])).
% 6.41/2.27  tff(c_88, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_54, c_81])).
% 6.41/2.27  tff(c_90, plain, (~v2_struct_0('#skF_3')), inference(splitRight, [status(thm)], [c_74])).
% 6.41/2.27  tff(c_50, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_184])).
% 6.41/2.27  tff(c_58, plain, (v5_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_184])).
% 6.41/2.27  tff(c_12, plain, (![A_9, B_10, C_11]: (m1_subset_1(k10_lattice3(A_9, B_10, C_11), u1_struct_0(A_9)) | ~m1_subset_1(C_11, u1_struct_0(A_9)) | ~m1_subset_1(B_10, u1_struct_0(A_9)) | ~l1_orders_2(A_9))), inference(cnfTransformation, [status(thm)], [f_75])).
% 6.41/2.27  tff(c_91, plain, (![A_122, B_123, C_124]: (k12_lattice3(A_122, B_123, C_124)=k11_lattice3(A_122, B_123, C_124) | ~m1_subset_1(C_124, u1_struct_0(A_122)) | ~m1_subset_1(B_123, u1_struct_0(A_122)) | ~l1_orders_2(A_122) | ~v2_lattice3(A_122) | ~v5_orders_2(A_122))), inference(cnfTransformation, [status(thm)], [f_153])).
% 6.41/2.27  tff(c_664, plain, (![A_207, B_208, B_209, C_210]: (k12_lattice3(A_207, B_208, k10_lattice3(A_207, B_209, C_210))=k11_lattice3(A_207, B_208, k10_lattice3(A_207, B_209, C_210)) | ~m1_subset_1(B_208, u1_struct_0(A_207)) | ~v2_lattice3(A_207) | ~v5_orders_2(A_207) | ~m1_subset_1(C_210, u1_struct_0(A_207)) | ~m1_subset_1(B_209, u1_struct_0(A_207)) | ~l1_orders_2(A_207))), inference(resolution, [status(thm)], [c_12, c_91])).
% 6.41/2.27  tff(c_670, plain, (![B_209, C_210]: (k12_lattice3('#skF_3', '#skF_4', k10_lattice3('#skF_3', B_209, C_210))=k11_lattice3('#skF_3', '#skF_4', k10_lattice3('#skF_3', B_209, C_210)) | ~v2_lattice3('#skF_3') | ~v5_orders_2('#skF_3') | ~m1_subset_1(C_210, u1_struct_0('#skF_3')) | ~m1_subset_1(B_209, u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3'))), inference(resolution, [status(thm)], [c_50, c_664])).
% 6.41/2.27  tff(c_745, plain, (![B_219, C_220]: (k12_lattice3('#skF_3', '#skF_4', k10_lattice3('#skF_3', B_219, C_220))=k11_lattice3('#skF_3', '#skF_4', k10_lattice3('#skF_3', B_219, C_220)) | ~m1_subset_1(C_220, u1_struct_0('#skF_3')) | ~m1_subset_1(B_219, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_58, c_54, c_670])).
% 6.41/2.27  tff(c_758, plain, (![B_221]: (k12_lattice3('#skF_3', '#skF_4', k10_lattice3('#skF_3', B_221, '#skF_5'))=k11_lattice3('#skF_3', '#skF_4', k10_lattice3('#skF_3', B_221, '#skF_5')) | ~m1_subset_1(B_221, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_48, c_745])).
% 6.41/2.27  tff(c_773, plain, (k12_lattice3('#skF_3', '#skF_4', k10_lattice3('#skF_3', '#skF_4', '#skF_5'))=k11_lattice3('#skF_3', '#skF_4', k10_lattice3('#skF_3', '#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_50, c_758])).
% 6.41/2.27  tff(c_56, plain, (v1_lattice3('#skF_3')), inference(cnfTransformation, [status(thm)], [f_184])).
% 6.41/2.27  tff(c_163, plain, (![A_128, B_129, C_130]: (k13_lattice3(A_128, B_129, C_130)=k10_lattice3(A_128, B_129, C_130) | ~m1_subset_1(C_130, u1_struct_0(A_128)) | ~m1_subset_1(B_129, u1_struct_0(A_128)) | ~l1_orders_2(A_128) | ~v1_lattice3(A_128) | ~v5_orders_2(A_128))), inference(cnfTransformation, [status(thm)], [f_165])).
% 6.41/2.27  tff(c_167, plain, (![B_129]: (k13_lattice3('#skF_3', B_129, '#skF_5')=k10_lattice3('#skF_3', B_129, '#skF_5') | ~m1_subset_1(B_129, u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v1_lattice3('#skF_3') | ~v5_orders_2('#skF_3'))), inference(resolution, [status(thm)], [c_48, c_163])).
% 6.41/2.27  tff(c_181, plain, (![B_131]: (k13_lattice3('#skF_3', B_131, '#skF_5')=k10_lattice3('#skF_3', B_131, '#skF_5') | ~m1_subset_1(B_131, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_52, c_167])).
% 6.41/2.27  tff(c_196, plain, (k13_lattice3('#skF_3', '#skF_4', '#skF_5')=k10_lattice3('#skF_3', '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_50, c_181])).
% 6.41/2.27  tff(c_46, plain, (k12_lattice3('#skF_3', '#skF_4', k13_lattice3('#skF_3', '#skF_4', '#skF_5'))!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_184])).
% 6.41/2.27  tff(c_201, plain, (k12_lattice3('#skF_3', '#skF_4', k10_lattice3('#skF_3', '#skF_4', '#skF_5'))!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_196, c_46])).
% 6.41/2.27  tff(c_778, plain, (k11_lattice3('#skF_3', '#skF_4', k10_lattice3('#skF_3', '#skF_4', '#skF_5'))!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_773, c_201])).
% 6.41/2.27  tff(c_304, plain, (![A_143, C_144, B_145]: (r1_orders_2(A_143, C_144, k10_lattice3(A_143, B_145, C_144)) | ~m1_subset_1(k10_lattice3(A_143, B_145, C_144), u1_struct_0(A_143)) | ~m1_subset_1(C_144, u1_struct_0(A_143)) | ~m1_subset_1(B_145, u1_struct_0(A_143)) | ~l1_orders_2(A_143) | ~v1_lattice3(A_143) | ~v5_orders_2(A_143) | v2_struct_0(A_143))), inference(cnfTransformation, [status(thm)], [f_108])).
% 6.41/2.27  tff(c_307, plain, (![A_9, C_11, B_10]: (r1_orders_2(A_9, C_11, k10_lattice3(A_9, B_10, C_11)) | ~v1_lattice3(A_9) | ~v5_orders_2(A_9) | v2_struct_0(A_9) | ~m1_subset_1(C_11, u1_struct_0(A_9)) | ~m1_subset_1(B_10, u1_struct_0(A_9)) | ~l1_orders_2(A_9))), inference(resolution, [status(thm)], [c_12, c_304])).
% 6.41/2.27  tff(c_105, plain, (![B_125]: (r3_orders_2('#skF_3', B_125, B_125) | ~m1_subset_1(B_125, u1_struct_0('#skF_3')))), inference(splitRight, [status(thm)], [c_74])).
% 6.41/2.27  tff(c_116, plain, (r3_orders_2('#skF_3', '#skF_5', '#skF_5')), inference(resolution, [status(thm)], [c_48, c_105])).
% 6.41/2.27  tff(c_231, plain, (![A_135, B_136, C_137]: (r1_orders_2(A_135, B_136, C_137) | ~r3_orders_2(A_135, B_136, C_137) | ~m1_subset_1(C_137, u1_struct_0(A_135)) | ~m1_subset_1(B_136, u1_struct_0(A_135)) | ~l1_orders_2(A_135) | ~v3_orders_2(A_135) | v2_struct_0(A_135))), inference(cnfTransformation, [status(thm)], [f_40])).
% 6.41/2.27  tff(c_237, plain, (r1_orders_2('#skF_3', '#skF_5', '#skF_5') | ~m1_subset_1('#skF_5', u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_116, c_231])).
% 6.41/2.27  tff(c_248, plain, (r1_orders_2('#skF_3', '#skF_5', '#skF_5') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_52, c_48, c_237])).
% 6.41/2.27  tff(c_249, plain, (r1_orders_2('#skF_3', '#skF_5', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_90, c_248])).
% 6.41/2.27  tff(c_1541, plain, (![A_269, B_270, C_271, D_272]: (r1_orders_2(A_269, '#skF_2'(A_269, B_270, C_271, D_272), C_271) | k11_lattice3(A_269, B_270, C_271)=D_272 | ~r1_orders_2(A_269, D_272, C_271) | ~r1_orders_2(A_269, D_272, B_270) | ~m1_subset_1(D_272, u1_struct_0(A_269)) | ~m1_subset_1(C_271, u1_struct_0(A_269)) | ~m1_subset_1(B_270, u1_struct_0(A_269)) | ~l1_orders_2(A_269) | ~v2_lattice3(A_269) | ~v5_orders_2(A_269) | v2_struct_0(A_269))), inference(cnfTransformation, [status(thm)], [f_141])).
% 6.41/2.27  tff(c_28, plain, (![A_58, B_82, C_94, D_100]: (~r1_orders_2(A_58, '#skF_2'(A_58, B_82, C_94, D_100), D_100) | k11_lattice3(A_58, B_82, C_94)=D_100 | ~r1_orders_2(A_58, D_100, C_94) | ~r1_orders_2(A_58, D_100, B_82) | ~m1_subset_1(D_100, u1_struct_0(A_58)) | ~m1_subset_1(C_94, u1_struct_0(A_58)) | ~m1_subset_1(B_82, u1_struct_0(A_58)) | ~l1_orders_2(A_58) | ~v2_lattice3(A_58) | ~v5_orders_2(A_58) | v2_struct_0(A_58))), inference(cnfTransformation, [status(thm)], [f_141])).
% 6.41/2.27  tff(c_2117, plain, (![A_300, B_301, C_302]: (k11_lattice3(A_300, B_301, C_302)=C_302 | ~r1_orders_2(A_300, C_302, C_302) | ~r1_orders_2(A_300, C_302, B_301) | ~m1_subset_1(C_302, u1_struct_0(A_300)) | ~m1_subset_1(B_301, u1_struct_0(A_300)) | ~l1_orders_2(A_300) | ~v2_lattice3(A_300) | ~v5_orders_2(A_300) | v2_struct_0(A_300))), inference(resolution, [status(thm)], [c_1541, c_28])).
% 6.41/2.27  tff(c_2121, plain, (![B_301]: (k11_lattice3('#skF_3', B_301, '#skF_5')='#skF_5' | ~r1_orders_2('#skF_3', '#skF_5', B_301) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_3')) | ~m1_subset_1(B_301, u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v2_lattice3('#skF_3') | ~v5_orders_2('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_249, c_2117])).
% 6.41/2.27  tff(c_2130, plain, (![B_301]: (k11_lattice3('#skF_3', B_301, '#skF_5')='#skF_5' | ~r1_orders_2('#skF_3', '#skF_5', B_301) | ~m1_subset_1(B_301, u1_struct_0('#skF_3')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_54, c_52, c_48, c_2121])).
% 6.41/2.27  tff(c_2136, plain, (![B_303]: (k11_lattice3('#skF_3', B_303, '#skF_5')='#skF_5' | ~r1_orders_2('#skF_3', '#skF_5', B_303) | ~m1_subset_1(B_303, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_90, c_2130])).
% 6.41/2.27  tff(c_2148, plain, (![B_10, C_11]: (k11_lattice3('#skF_3', k10_lattice3('#skF_3', B_10, C_11), '#skF_5')='#skF_5' | ~r1_orders_2('#skF_3', '#skF_5', k10_lattice3('#skF_3', B_10, C_11)) | ~m1_subset_1(C_11, u1_struct_0('#skF_3')) | ~m1_subset_1(B_10, u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3'))), inference(resolution, [status(thm)], [c_12, c_2136])).
% 6.41/2.27  tff(c_2223, plain, (![B_308, C_309]: (k11_lattice3('#skF_3', k10_lattice3('#skF_3', B_308, C_309), '#skF_5')='#skF_5' | ~r1_orders_2('#skF_3', '#skF_5', k10_lattice3('#skF_3', B_308, C_309)) | ~m1_subset_1(C_309, u1_struct_0('#skF_3')) | ~m1_subset_1(B_308, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_2148])).
% 6.41/2.27  tff(c_2233, plain, (![B_10]: (k11_lattice3('#skF_3', k10_lattice3('#skF_3', B_10, '#skF_5'), '#skF_5')='#skF_5' | ~v1_lattice3('#skF_3') | ~v5_orders_2('#skF_3') | v2_struct_0('#skF_3') | ~m1_subset_1('#skF_5', u1_struct_0('#skF_3')) | ~m1_subset_1(B_10, u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3'))), inference(resolution, [status(thm)], [c_307, c_2223])).
% 6.41/2.27  tff(c_2244, plain, (![B_10]: (k11_lattice3('#skF_3', k10_lattice3('#skF_3', B_10, '#skF_5'), '#skF_5')='#skF_5' | v2_struct_0('#skF_3') | ~m1_subset_1(B_10, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_48, c_58, c_56, c_2233])).
% 6.41/2.27  tff(c_2250, plain, (![B_310]: (k11_lattice3('#skF_3', k10_lattice3('#skF_3', B_310, '#skF_5'), '#skF_5')='#skF_5' | ~m1_subset_1(B_310, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_90, c_2244])).
% 6.41/2.27  tff(c_2282, plain, (k11_lattice3('#skF_3', k10_lattice3('#skF_3', '#skF_4', '#skF_5'), '#skF_5')='#skF_5'), inference(resolution, [status(thm)], [c_50, c_2250])).
% 6.41/2.27  tff(c_40, plain, (![A_58, B_82, C_94]: (r1_orders_2(A_58, k11_lattice3(A_58, B_82, C_94), B_82) | ~m1_subset_1(k11_lattice3(A_58, B_82, C_94), u1_struct_0(A_58)) | ~m1_subset_1(C_94, u1_struct_0(A_58)) | ~m1_subset_1(B_82, u1_struct_0(A_58)) | ~l1_orders_2(A_58) | ~v2_lattice3(A_58) | ~v5_orders_2(A_58) | v2_struct_0(A_58))), inference(cnfTransformation, [status(thm)], [f_141])).
% 6.41/2.27  tff(c_2286, plain, (r1_orders_2('#skF_3', k11_lattice3('#skF_3', k10_lattice3('#skF_3', '#skF_4', '#skF_5'), '#skF_5'), k10_lattice3('#skF_3', '#skF_4', '#skF_5')) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_3')) | ~m1_subset_1(k10_lattice3('#skF_3', '#skF_4', '#skF_5'), u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v2_lattice3('#skF_3') | ~v5_orders_2('#skF_3') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2282, c_40])).
% 6.41/2.27  tff(c_2292, plain, (r1_orders_2('#skF_3', '#skF_5', k10_lattice3('#skF_3', '#skF_4', '#skF_5')) | ~m1_subset_1(k10_lattice3('#skF_3', '#skF_4', '#skF_5'), u1_struct_0('#skF_3')) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_54, c_52, c_48, c_48, c_2282, c_2286])).
% 6.41/2.27  tff(c_2293, plain, (r1_orders_2('#skF_3', '#skF_5', k10_lattice3('#skF_3', '#skF_4', '#skF_5')) | ~m1_subset_1(k10_lattice3('#skF_3', '#skF_4', '#skF_5'), u1_struct_0('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_90, c_2292])).
% 6.41/2.27  tff(c_2368, plain, (~m1_subset_1(k10_lattice3('#skF_3', '#skF_4', '#skF_5'), u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_2293])).
% 6.41/2.27  tff(c_2372, plain, (~m1_subset_1('#skF_5', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3')), inference(resolution, [status(thm)], [c_12, c_2368])).
% 6.41/2.27  tff(c_2376, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_2372])).
% 6.41/2.27  tff(c_2378, plain, (m1_subset_1(k10_lattice3('#skF_3', '#skF_4', '#skF_5'), u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_2293])).
% 6.41/2.27  tff(c_117, plain, (r3_orders_2('#skF_3', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_50, c_105])).
% 6.41/2.27  tff(c_235, plain, (r1_orders_2('#skF_3', '#skF_4', '#skF_4') | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_117, c_231])).
% 6.41/2.27  tff(c_244, plain, (r1_orders_2('#skF_3', '#skF_4', '#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_52, c_50, c_235])).
% 6.41/2.27  tff(c_245, plain, (r1_orders_2('#skF_3', '#skF_4', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_90, c_244])).
% 6.41/2.27  tff(c_556, plain, (![A_175, B_176, C_177]: (r1_orders_2(A_175, B_176, k10_lattice3(A_175, B_176, C_177)) | ~m1_subset_1(k10_lattice3(A_175, B_176, C_177), u1_struct_0(A_175)) | ~m1_subset_1(C_177, u1_struct_0(A_175)) | ~m1_subset_1(B_176, u1_struct_0(A_175)) | ~l1_orders_2(A_175) | ~v1_lattice3(A_175) | ~v5_orders_2(A_175) | v2_struct_0(A_175))), inference(cnfTransformation, [status(thm)], [f_108])).
% 6.41/2.27  tff(c_559, plain, (![A_9, B_10, C_11]: (r1_orders_2(A_9, B_10, k10_lattice3(A_9, B_10, C_11)) | ~v1_lattice3(A_9) | ~v5_orders_2(A_9) | v2_struct_0(A_9) | ~m1_subset_1(C_11, u1_struct_0(A_9)) | ~m1_subset_1(B_10, u1_struct_0(A_9)) | ~l1_orders_2(A_9))), inference(resolution, [status(thm)], [c_12, c_556])).
% 6.41/2.27  tff(c_2123, plain, (![B_301]: (k11_lattice3('#skF_3', B_301, '#skF_4')='#skF_4' | ~r1_orders_2('#skF_3', '#skF_4', B_301) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~m1_subset_1(B_301, u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v2_lattice3('#skF_3') | ~v5_orders_2('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_245, c_2117])).
% 6.41/2.27  tff(c_2134, plain, (![B_301]: (k11_lattice3('#skF_3', B_301, '#skF_4')='#skF_4' | ~r1_orders_2('#skF_3', '#skF_4', B_301) | ~m1_subset_1(B_301, u1_struct_0('#skF_3')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_54, c_52, c_50, c_2123])).
% 6.41/2.27  tff(c_2135, plain, (![B_301]: (k11_lattice3('#skF_3', B_301, '#skF_4')='#skF_4' | ~r1_orders_2('#skF_3', '#skF_4', B_301) | ~m1_subset_1(B_301, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_90, c_2134])).
% 6.41/2.27  tff(c_2521, plain, (k11_lattice3('#skF_3', k10_lattice3('#skF_3', '#skF_4', '#skF_5'), '#skF_4')='#skF_4' | ~r1_orders_2('#skF_3', '#skF_4', k10_lattice3('#skF_3', '#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_2378, c_2135])).
% 6.41/2.27  tff(c_3999, plain, (~r1_orders_2('#skF_3', '#skF_4', k10_lattice3('#skF_3', '#skF_4', '#skF_5'))), inference(splitLeft, [status(thm)], [c_2521])).
% 6.41/2.27  tff(c_4003, plain, (~v1_lattice3('#skF_3') | ~v5_orders_2('#skF_3') | v2_struct_0('#skF_3') | ~m1_subset_1('#skF_5', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3')), inference(resolution, [status(thm)], [c_559, c_3999])).
% 6.41/2.27  tff(c_4006, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_58, c_56, c_4003])).
% 6.41/2.27  tff(c_4008, plain, $false, inference(negUnitSimplification, [status(thm)], [c_90, c_4006])).
% 6.41/2.27  tff(c_4010, plain, (r1_orders_2('#skF_3', '#skF_4', k10_lattice3('#skF_3', '#skF_4', '#skF_5'))), inference(splitRight, [status(thm)], [c_2521])).
% 6.41/2.27  tff(c_1680, plain, (![A_280, B_281, C_282, D_283]: (r1_orders_2(A_280, '#skF_2'(A_280, B_281, C_282, D_283), B_281) | k11_lattice3(A_280, B_281, C_282)=D_283 | ~r1_orders_2(A_280, D_283, C_282) | ~r1_orders_2(A_280, D_283, B_281) | ~m1_subset_1(D_283, u1_struct_0(A_280)) | ~m1_subset_1(C_282, u1_struct_0(A_280)) | ~m1_subset_1(B_281, u1_struct_0(A_280)) | ~l1_orders_2(A_280) | ~v2_lattice3(A_280) | ~v5_orders_2(A_280) | v2_struct_0(A_280))), inference(cnfTransformation, [status(thm)], [f_141])).
% 6.41/2.27  tff(c_1688, plain, (![A_280, B_281, C_282]: (k11_lattice3(A_280, B_281, C_282)=B_281 | ~r1_orders_2(A_280, B_281, C_282) | ~r1_orders_2(A_280, B_281, B_281) | ~m1_subset_1(C_282, u1_struct_0(A_280)) | ~m1_subset_1(B_281, u1_struct_0(A_280)) | ~l1_orders_2(A_280) | ~v2_lattice3(A_280) | ~v5_orders_2(A_280) | v2_struct_0(A_280))), inference(resolution, [status(thm)], [c_1680, c_28])).
% 6.41/2.27  tff(c_4012, plain, (k11_lattice3('#skF_3', '#skF_4', k10_lattice3('#skF_3', '#skF_4', '#skF_5'))='#skF_4' | ~r1_orders_2('#skF_3', '#skF_4', '#skF_4') | ~m1_subset_1(k10_lattice3('#skF_3', '#skF_4', '#skF_5'), u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v2_lattice3('#skF_3') | ~v5_orders_2('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_4010, c_1688])).
% 6.41/2.27  tff(c_4017, plain, (k11_lattice3('#skF_3', '#skF_4', k10_lattice3('#skF_3', '#skF_4', '#skF_5'))='#skF_4' | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_54, c_52, c_50, c_2378, c_245, c_4012])).
% 6.41/2.27  tff(c_4019, plain, $false, inference(negUnitSimplification, [status(thm)], [c_90, c_778, c_4017])).
% 6.41/2.27  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.41/2.27  
% 6.41/2.27  Inference rules
% 6.41/2.27  ----------------------
% 6.41/2.27  #Ref     : 0
% 6.41/2.27  #Sup     : 825
% 6.41/2.27  #Fact    : 0
% 6.41/2.27  #Define  : 0
% 6.41/2.27  #Split   : 12
% 6.41/2.27  #Chain   : 0
% 6.41/2.27  #Close   : 0
% 6.41/2.27  
% 6.41/2.27  Ordering : KBO
% 6.41/2.27  
% 6.41/2.27  Simplification rules
% 6.41/2.27  ----------------------
% 6.41/2.27  #Subsume      : 45
% 6.41/2.27  #Demod        : 1812
% 6.41/2.27  #Tautology    : 383
% 6.41/2.27  #SimpNegUnit  : 207
% 6.41/2.27  #BackRed      : 27
% 6.41/2.27  
% 6.41/2.27  #Partial instantiations: 0
% 6.41/2.27  #Strategies tried      : 1
% 6.41/2.27  
% 6.41/2.27  Timing (in seconds)
% 6.41/2.27  ----------------------
% 6.41/2.28  Preprocessing        : 0.36
% 6.41/2.28  Parsing              : 0.19
% 6.41/2.28  CNF conversion       : 0.03
% 6.41/2.28  Main loop            : 1.13
% 6.41/2.28  Inferencing          : 0.37
% 6.41/2.28  Reduction            : 0.41
% 6.41/2.28  Demodulation         : 0.30
% 6.41/2.28  BG Simplification    : 0.05
% 6.41/2.28  Subsumption          : 0.23
% 6.41/2.28  Abstraction          : 0.07
% 6.41/2.28  MUC search           : 0.00
% 6.41/2.28  Cooper               : 0.00
% 6.41/2.28  Total                : 1.54
% 6.41/2.28  Index Insertion      : 0.00
% 6.41/2.28  Index Deletion       : 0.00
% 6.41/2.28  Index Matching       : 0.00
% 6.41/2.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
