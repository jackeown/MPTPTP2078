%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:41 EST 2020

% Result     : Theorem 4.69s
% Output     : CNFRefutation 4.69s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 731 expanded)
%              Number of leaves         :   29 ( 281 expanded)
%              Depth                    :   22
%              Number of atoms          :  294 (3336 expanded)
%              Number of equality atoms :   35 ( 304 expanded)
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

tff(f_168,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_lattice3)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( ( l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => m1_subset_1(k10_lattice3(A,B,C),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k10_lattice3)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l26_lattice3)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l28_lattice3)).

tff(f_137,axiom,(
    ! [A,B,C] :
      ( ( v5_orders_2(A)
        & v2_lattice3(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => k12_lattice3(A,B,C) = k11_lattice3(A,B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k12_lattice3)).

tff(f_149,axiom,(
    ! [A,B,C] :
      ( ( v5_orders_2(A)
        & v1_lattice3(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => k13_lattice3(A,B,C) = k10_lattice3(A,B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k13_lattice3)).

tff(c_48,plain,(
    l1_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_46,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_44,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_8,plain,(
    ! [A_6,B_7,C_8] :
      ( m1_subset_1(k10_lattice3(A_6,B_7,C_8),u1_struct_0(A_6))
      | ~ m1_subset_1(C_8,u1_struct_0(A_6))
      | ~ m1_subset_1(B_7,u1_struct_0(A_6))
      | ~ l1_orders_2(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_52,plain,(
    v1_lattice3('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_56,plain,(
    v3_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_59,plain,(
    ! [A_113,B_114] :
      ( r1_orders_2(A_113,B_114,B_114)
      | ~ m1_subset_1(B_114,u1_struct_0(A_113))
      | ~ l1_orders_2(A_113)
      | ~ v3_orders_2(A_113)
      | v2_struct_0(A_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_61,plain,
    ( r1_orders_2('#skF_3','#skF_5','#skF_5')
    | ~ l1_orders_2('#skF_3')
    | ~ v3_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_59])).

tff(c_66,plain,
    ( r1_orders_2('#skF_3','#skF_5','#skF_5')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_48,c_61])).

tff(c_70,plain,(
    v2_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_4,plain,(
    ! [A_4] :
      ( ~ v2_struct_0(A_4)
      | ~ v1_lattice3(A_4)
      | ~ l1_orders_2(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_73,plain,
    ( ~ v1_lattice3('#skF_3')
    | ~ l1_orders_2('#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_4])).

tff(c_80,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_52,c_73])).

tff(c_82,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_54,plain,(
    v5_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_50,plain,(
    v2_lattice3('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_465,plain,(
    ! [A_159,B_160,C_161] :
      ( r1_orders_2(A_159,B_160,k10_lattice3(A_159,B_160,C_161))
      | ~ m1_subset_1(k10_lattice3(A_159,B_160,C_161),u1_struct_0(A_159))
      | ~ m1_subset_1(C_161,u1_struct_0(A_159))
      | ~ m1_subset_1(B_160,u1_struct_0(A_159))
      | ~ l1_orders_2(A_159)
      | ~ v1_lattice3(A_159)
      | ~ v5_orders_2(A_159)
      | v2_struct_0(A_159) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_468,plain,(
    ! [A_6,B_7,C_8] :
      ( r1_orders_2(A_6,B_7,k10_lattice3(A_6,B_7,C_8))
      | ~ v1_lattice3(A_6)
      | ~ v5_orders_2(A_6)
      | v2_struct_0(A_6)
      | ~ m1_subset_1(C_8,u1_struct_0(A_6))
      | ~ m1_subset_1(B_7,u1_struct_0(A_6))
      | ~ l1_orders_2(A_6) ) ),
    inference(resolution,[status(thm)],[c_8,c_465])).

tff(c_63,plain,
    ( r1_orders_2('#skF_3','#skF_4','#skF_4')
    | ~ l1_orders_2('#skF_3')
    | ~ v3_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_59])).

tff(c_69,plain,
    ( r1_orders_2('#skF_3','#skF_4','#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_48,c_63])).

tff(c_87,plain,(
    r1_orders_2('#skF_3','#skF_4','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_69])).

tff(c_831,plain,(
    ! [A_223,B_224,C_225,D_226] :
      ( r1_orders_2(A_223,'#skF_2'(A_223,B_224,C_225,D_226),C_225)
      | k11_lattice3(A_223,B_224,C_225) = D_226
      | ~ r1_orders_2(A_223,D_226,C_225)
      | ~ r1_orders_2(A_223,D_226,B_224)
      | ~ m1_subset_1(D_226,u1_struct_0(A_223))
      | ~ m1_subset_1(C_225,u1_struct_0(A_223))
      | ~ m1_subset_1(B_224,u1_struct_0(A_223))
      | ~ l1_orders_2(A_223)
      | ~ v2_lattice3(A_223)
      | ~ v5_orders_2(A_223)
      | v2_struct_0(A_223) ) ),
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

tff(c_974,plain,(
    ! [A_244,B_245,C_246] :
      ( k11_lattice3(A_244,B_245,C_246) = C_246
      | ~ r1_orders_2(A_244,C_246,C_246)
      | ~ r1_orders_2(A_244,C_246,B_245)
      | ~ m1_subset_1(C_246,u1_struct_0(A_244))
      | ~ m1_subset_1(B_245,u1_struct_0(A_244))
      | ~ l1_orders_2(A_244)
      | ~ v2_lattice3(A_244)
      | ~ v5_orders_2(A_244)
      | v2_struct_0(A_244) ) ),
    inference(resolution,[status(thm)],[c_831,c_24])).

tff(c_978,plain,(
    ! [B_245] :
      ( k11_lattice3('#skF_3',B_245,'#skF_4') = '#skF_4'
      | ~ r1_orders_2('#skF_3','#skF_4',B_245)
      | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
      | ~ m1_subset_1(B_245,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | ~ v2_lattice3('#skF_3')
      | ~ v5_orders_2('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_87,c_974])).

tff(c_984,plain,(
    ! [B_245] :
      ( k11_lattice3('#skF_3',B_245,'#skF_4') = '#skF_4'
      | ~ r1_orders_2('#skF_3','#skF_4',B_245)
      | ~ m1_subset_1(B_245,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_50,c_48,c_46,c_978])).

tff(c_1222,plain,(
    ! [B_251] :
      ( k11_lattice3('#skF_3',B_251,'#skF_4') = '#skF_4'
      | ~ r1_orders_2('#skF_3','#skF_4',B_251)
      | ~ m1_subset_1(B_251,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_984])).

tff(c_1230,plain,(
    ! [B_7,C_8] :
      ( k11_lattice3('#skF_3',k10_lattice3('#skF_3',B_7,C_8),'#skF_4') = '#skF_4'
      | ~ r1_orders_2('#skF_3','#skF_4',k10_lattice3('#skF_3',B_7,C_8))
      | ~ m1_subset_1(C_8,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(B_7,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_8,c_1222])).

tff(c_1276,plain,(
    ! [B_253,C_254] :
      ( k11_lattice3('#skF_3',k10_lattice3('#skF_3',B_253,C_254),'#skF_4') = '#skF_4'
      | ~ r1_orders_2('#skF_3','#skF_4',k10_lattice3('#skF_3',B_253,C_254))
      | ~ m1_subset_1(C_254,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(B_253,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_1230])).

tff(c_1280,plain,(
    ! [C_8] :
      ( k11_lattice3('#skF_3',k10_lattice3('#skF_3','#skF_4',C_8),'#skF_4') = '#skF_4'
      | ~ v1_lattice3('#skF_3')
      | ~ v5_orders_2('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ m1_subset_1(C_8,u1_struct_0('#skF_3'))
      | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_468,c_1276])).

tff(c_1287,plain,(
    ! [C_8] :
      ( k11_lattice3('#skF_3',k10_lattice3('#skF_3','#skF_4',C_8),'#skF_4') = '#skF_4'
      | v2_struct_0('#skF_3')
      | ~ m1_subset_1(C_8,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_54,c_52,c_1280])).

tff(c_1293,plain,(
    ! [C_255] :
      ( k11_lattice3('#skF_3',k10_lattice3('#skF_3','#skF_4',C_255),'#skF_4') = '#skF_4'
      | ~ m1_subset_1(C_255,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_1287])).

tff(c_1315,plain,(
    k11_lattice3('#skF_3',k10_lattice3('#skF_3','#skF_4','#skF_5'),'#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_44,c_1293])).

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

tff(c_1320,plain,
    ( r1_orders_2('#skF_3',k11_lattice3('#skF_3',k10_lattice3('#skF_3','#skF_4','#skF_5'),'#skF_4'),k10_lattice3('#skF_3','#skF_4','#skF_5'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ m1_subset_1(k10_lattice3('#skF_3','#skF_4','#skF_5'),u1_struct_0('#skF_3'))
    | ~ l1_orders_2('#skF_3')
    | ~ v2_lattice3('#skF_3')
    | ~ v5_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1315,c_36])).

tff(c_1326,plain,
    ( r1_orders_2('#skF_3','#skF_4',k10_lattice3('#skF_3','#skF_4','#skF_5'))
    | ~ m1_subset_1(k10_lattice3('#skF_3','#skF_4','#skF_5'),u1_struct_0('#skF_3'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_50,c_48,c_46,c_46,c_1315,c_1320])).

tff(c_1327,plain,
    ( r1_orders_2('#skF_3','#skF_4',k10_lattice3('#skF_3','#skF_4','#skF_5'))
    | ~ m1_subset_1(k10_lattice3('#skF_3','#skF_4','#skF_5'),u1_struct_0('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_1326])).

tff(c_1663,plain,(
    ~ m1_subset_1(k10_lattice3('#skF_3','#skF_4','#skF_5'),u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1327])).

tff(c_1666,plain,
    ( ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ l1_orders_2('#skF_3') ),
    inference(resolution,[status(thm)],[c_8,c_1663])).

tff(c_1670,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_1666])).

tff(c_1672,plain,(
    m1_subset_1(k10_lattice3('#skF_3','#skF_4','#skF_5'),u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_1327])).

tff(c_151,plain,(
    ! [A_123,B_124,C_125] :
      ( k12_lattice3(A_123,B_124,C_125) = k11_lattice3(A_123,B_124,C_125)
      | ~ m1_subset_1(C_125,u1_struct_0(A_123))
      | ~ m1_subset_1(B_124,u1_struct_0(A_123))
      | ~ l1_orders_2(A_123)
      | ~ v2_lattice3(A_123)
      | ~ v5_orders_2(A_123) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_788,plain,(
    ! [A_216,B_217,B_218,C_219] :
      ( k12_lattice3(A_216,B_217,k10_lattice3(A_216,B_218,C_219)) = k11_lattice3(A_216,B_217,k10_lattice3(A_216,B_218,C_219))
      | ~ m1_subset_1(B_217,u1_struct_0(A_216))
      | ~ v2_lattice3(A_216)
      | ~ v5_orders_2(A_216)
      | ~ m1_subset_1(C_219,u1_struct_0(A_216))
      | ~ m1_subset_1(B_218,u1_struct_0(A_216))
      | ~ l1_orders_2(A_216) ) ),
    inference(resolution,[status(thm)],[c_8,c_151])).

tff(c_794,plain,(
    ! [B_218,C_219] :
      ( k12_lattice3('#skF_3','#skF_4',k10_lattice3('#skF_3',B_218,C_219)) = k11_lattice3('#skF_3','#skF_4',k10_lattice3('#skF_3',B_218,C_219))
      | ~ v2_lattice3('#skF_3')
      | ~ v5_orders_2('#skF_3')
      | ~ m1_subset_1(C_219,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(B_218,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_46,c_788])).

tff(c_872,plain,(
    ! [B_228,C_229] :
      ( k12_lattice3('#skF_3','#skF_4',k10_lattice3('#skF_3',B_228,C_229)) = k11_lattice3('#skF_3','#skF_4',k10_lattice3('#skF_3',B_228,C_229))
      | ~ m1_subset_1(C_229,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(B_228,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_54,c_50,c_794])).

tff(c_885,plain,(
    ! [B_230] :
      ( k12_lattice3('#skF_3','#skF_4',k10_lattice3('#skF_3',B_230,'#skF_5')) = k11_lattice3('#skF_3','#skF_4',k10_lattice3('#skF_3',B_230,'#skF_5'))
      | ~ m1_subset_1(B_230,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_44,c_872])).

tff(c_900,plain,(
    k12_lattice3('#skF_3','#skF_4',k10_lattice3('#skF_3','#skF_4','#skF_5')) = k11_lattice3('#skF_3','#skF_4',k10_lattice3('#skF_3','#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_46,c_885])).

tff(c_88,plain,(
    ! [A_118,B_119,C_120] :
      ( k13_lattice3(A_118,B_119,C_120) = k10_lattice3(A_118,B_119,C_120)
      | ~ m1_subset_1(C_120,u1_struct_0(A_118))
      | ~ m1_subset_1(B_119,u1_struct_0(A_118))
      | ~ l1_orders_2(A_118)
      | ~ v1_lattice3(A_118)
      | ~ v5_orders_2(A_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_92,plain,(
    ! [B_119] :
      ( k13_lattice3('#skF_3',B_119,'#skF_5') = k10_lattice3('#skF_3',B_119,'#skF_5')
      | ~ m1_subset_1(B_119,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | ~ v1_lattice3('#skF_3')
      | ~ v5_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_44,c_88])).

tff(c_102,plain,(
    ! [B_121] :
      ( k13_lattice3('#skF_3',B_121,'#skF_5') = k10_lattice3('#skF_3',B_121,'#skF_5')
      | ~ m1_subset_1(B_121,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_48,c_92])).

tff(c_117,plain,(
    k13_lattice3('#skF_3','#skF_4','#skF_5') = k10_lattice3('#skF_3','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_46,c_102])).

tff(c_42,plain,(
    k12_lattice3('#skF_3','#skF_4',k13_lattice3('#skF_3','#skF_4','#skF_5')) != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_122,plain,(
    k12_lattice3('#skF_3','#skF_4',k10_lattice3('#skF_3','#skF_4','#skF_5')) != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_42])).

tff(c_905,plain,(
    k11_lattice3('#skF_3','#skF_4',k10_lattice3('#skF_3','#skF_4','#skF_5')) != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_900,c_122])).

tff(c_1671,plain,(
    r1_orders_2('#skF_3','#skF_4',k10_lattice3('#skF_3','#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_1327])).

tff(c_28,plain,(
    ! [A_55,B_79,C_91,D_97] :
      ( r1_orders_2(A_55,'#skF_2'(A_55,B_79,C_91,D_97),B_79)
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

tff(c_707,plain,(
    ! [A_207,B_208,C_209,D_210] :
      ( ~ r1_orders_2(A_207,'#skF_2'(A_207,B_208,C_209,D_210),D_210)
      | k11_lattice3(A_207,B_208,C_209) = D_210
      | ~ r1_orders_2(A_207,D_210,C_209)
      | ~ r1_orders_2(A_207,D_210,B_208)
      | ~ m1_subset_1(D_210,u1_struct_0(A_207))
      | ~ m1_subset_1(C_209,u1_struct_0(A_207))
      | ~ m1_subset_1(B_208,u1_struct_0(A_207))
      | ~ l1_orders_2(A_207)
      | ~ v2_lattice3(A_207)
      | ~ v5_orders_2(A_207)
      | v2_struct_0(A_207) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_712,plain,(
    ! [A_55,B_79,C_91] :
      ( k11_lattice3(A_55,B_79,C_91) = B_79
      | ~ r1_orders_2(A_55,B_79,C_91)
      | ~ r1_orders_2(A_55,B_79,B_79)
      | ~ m1_subset_1(C_91,u1_struct_0(A_55))
      | ~ m1_subset_1(B_79,u1_struct_0(A_55))
      | ~ l1_orders_2(A_55)
      | ~ v2_lattice3(A_55)
      | ~ v5_orders_2(A_55)
      | v2_struct_0(A_55) ) ),
    inference(resolution,[status(thm)],[c_28,c_707])).

tff(c_1677,plain,
    ( k11_lattice3('#skF_3','#skF_4',k10_lattice3('#skF_3','#skF_4','#skF_5')) = '#skF_4'
    | ~ r1_orders_2('#skF_3','#skF_4','#skF_4')
    | ~ m1_subset_1(k10_lattice3('#skF_3','#skF_4','#skF_5'),u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ l1_orders_2('#skF_3')
    | ~ v2_lattice3('#skF_3')
    | ~ v5_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_1671,c_712])).

tff(c_1683,plain,
    ( k11_lattice3('#skF_3','#skF_4',k10_lattice3('#skF_3','#skF_4','#skF_5')) = '#skF_4'
    | ~ m1_subset_1(k10_lattice3('#skF_3','#skF_4','#skF_5'),u1_struct_0('#skF_3'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_50,c_48,c_46,c_87,c_1677])).

tff(c_1684,plain,(
    ~ m1_subset_1(k10_lattice3('#skF_3','#skF_4','#skF_5'),u1_struct_0('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_905,c_1683])).

tff(c_1849,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1672,c_1684])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:53:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.69/1.85  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.69/1.86  
% 4.69/1.86  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.69/1.86  %$ r1_orders_2 > m1_subset_1 > v5_orders_2 > v3_orders_2 > v2_struct_0 > v2_lattice3 > v1_lattice3 > l1_orders_2 > k13_lattice3 > k12_lattice3 > k11_lattice3 > k10_lattice3 > #nlpp > u1_struct_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 4.69/1.86  
% 4.69/1.86  %Foreground sorts:
% 4.69/1.86  
% 4.69/1.86  
% 4.69/1.86  %Background operators:
% 4.69/1.86  
% 4.69/1.86  
% 4.69/1.86  %Foreground operators:
% 4.69/1.86  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.69/1.86  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 4.69/1.86  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.69/1.86  tff(k13_lattice3, type, k13_lattice3: ($i * $i * $i) > $i).
% 4.69/1.86  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 4.69/1.86  tff(k10_lattice3, type, k10_lattice3: ($i * $i * $i) > $i).
% 4.69/1.86  tff(k11_lattice3, type, k11_lattice3: ($i * $i * $i) > $i).
% 4.69/1.86  tff(v1_lattice3, type, v1_lattice3: $i > $o).
% 4.69/1.86  tff('#skF_5', type, '#skF_5': $i).
% 4.69/1.86  tff(k12_lattice3, type, k12_lattice3: ($i * $i * $i) > $i).
% 4.69/1.86  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 4.69/1.86  tff('#skF_3', type, '#skF_3': $i).
% 4.69/1.86  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 4.69/1.86  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 4.69/1.86  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.69/1.86  tff('#skF_4', type, '#skF_4': $i).
% 4.69/1.86  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.69/1.86  tff(v2_lattice3, type, v2_lattice3: $i > $o).
% 4.69/1.86  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 4.69/1.86  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.69/1.86  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.69/1.86  
% 4.69/1.87  tff(f_168, negated_conjecture, ~(![A]: (((((v3_orders_2(A) & v5_orders_2(A)) & v1_lattice3(A)) & v2_lattice3(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (k12_lattice3(A, B, k13_lattice3(A, B, C)) = B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_lattice3)).
% 4.69/1.87  tff(f_59, axiom, (![A, B, C]: (((l1_orders_2(A) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => m1_subset_1(k10_lattice3(A, B, C), u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k10_lattice3)).
% 4.69/1.87  tff(f_37, axiom, (![A]: (((~v2_struct_0(A) & v3_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => r1_orders_2(A, B, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_orders_2)).
% 4.69/1.87  tff(f_44, axiom, (![A]: (l1_orders_2(A) => (v1_lattice3(A) => ~v2_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_lattice3)).
% 4.69/1.87  tff(f_92, axiom, (![A]: ((((~v2_struct_0(A) & v5_orders_2(A)) & v1_lattice3(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => ((D = k10_lattice3(A, B, C)) <=> ((r1_orders_2(A, B, D) & r1_orders_2(A, C, D)) & (![E]: (m1_subset_1(E, u1_struct_0(A)) => ((r1_orders_2(A, B, E) & r1_orders_2(A, C, E)) => r1_orders_2(A, D, E)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l26_lattice3)).
% 4.69/1.87  tff(f_125, axiom, (![A]: ((((~v2_struct_0(A) & v5_orders_2(A)) & v2_lattice3(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => ((D = k11_lattice3(A, B, C)) <=> ((r1_orders_2(A, D, B) & r1_orders_2(A, D, C)) & (![E]: (m1_subset_1(E, u1_struct_0(A)) => ((r1_orders_2(A, E, B) & r1_orders_2(A, E, C)) => r1_orders_2(A, E, D)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l28_lattice3)).
% 4.69/1.87  tff(f_137, axiom, (![A, B, C]: (((((v5_orders_2(A) & v2_lattice3(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (k12_lattice3(A, B, C) = k11_lattice3(A, B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k12_lattice3)).
% 4.69/1.87  tff(f_149, axiom, (![A, B, C]: (((((v5_orders_2(A) & v1_lattice3(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (k13_lattice3(A, B, C) = k10_lattice3(A, B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k13_lattice3)).
% 4.69/1.87  tff(c_48, plain, (l1_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_168])).
% 4.69/1.87  tff(c_46, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_168])).
% 4.69/1.87  tff(c_44, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_168])).
% 4.69/1.87  tff(c_8, plain, (![A_6, B_7, C_8]: (m1_subset_1(k10_lattice3(A_6, B_7, C_8), u1_struct_0(A_6)) | ~m1_subset_1(C_8, u1_struct_0(A_6)) | ~m1_subset_1(B_7, u1_struct_0(A_6)) | ~l1_orders_2(A_6))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.69/1.87  tff(c_52, plain, (v1_lattice3('#skF_3')), inference(cnfTransformation, [status(thm)], [f_168])).
% 4.69/1.87  tff(c_56, plain, (v3_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_168])).
% 4.69/1.87  tff(c_59, plain, (![A_113, B_114]: (r1_orders_2(A_113, B_114, B_114) | ~m1_subset_1(B_114, u1_struct_0(A_113)) | ~l1_orders_2(A_113) | ~v3_orders_2(A_113) | v2_struct_0(A_113))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.69/1.87  tff(c_61, plain, (r1_orders_2('#skF_3', '#skF_5', '#skF_5') | ~l1_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_44, c_59])).
% 4.69/1.87  tff(c_66, plain, (r1_orders_2('#skF_3', '#skF_5', '#skF_5') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_48, c_61])).
% 4.69/1.87  tff(c_70, plain, (v2_struct_0('#skF_3')), inference(splitLeft, [status(thm)], [c_66])).
% 4.69/1.87  tff(c_4, plain, (![A_4]: (~v2_struct_0(A_4) | ~v1_lattice3(A_4) | ~l1_orders_2(A_4))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.69/1.87  tff(c_73, plain, (~v1_lattice3('#skF_3') | ~l1_orders_2('#skF_3')), inference(resolution, [status(thm)], [c_70, c_4])).
% 4.69/1.87  tff(c_80, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_52, c_73])).
% 4.69/1.87  tff(c_82, plain, (~v2_struct_0('#skF_3')), inference(splitRight, [status(thm)], [c_66])).
% 4.69/1.87  tff(c_54, plain, (v5_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_168])).
% 4.69/1.87  tff(c_50, plain, (v2_lattice3('#skF_3')), inference(cnfTransformation, [status(thm)], [f_168])).
% 4.69/1.87  tff(c_465, plain, (![A_159, B_160, C_161]: (r1_orders_2(A_159, B_160, k10_lattice3(A_159, B_160, C_161)) | ~m1_subset_1(k10_lattice3(A_159, B_160, C_161), u1_struct_0(A_159)) | ~m1_subset_1(C_161, u1_struct_0(A_159)) | ~m1_subset_1(B_160, u1_struct_0(A_159)) | ~l1_orders_2(A_159) | ~v1_lattice3(A_159) | ~v5_orders_2(A_159) | v2_struct_0(A_159))), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.69/1.87  tff(c_468, plain, (![A_6, B_7, C_8]: (r1_orders_2(A_6, B_7, k10_lattice3(A_6, B_7, C_8)) | ~v1_lattice3(A_6) | ~v5_orders_2(A_6) | v2_struct_0(A_6) | ~m1_subset_1(C_8, u1_struct_0(A_6)) | ~m1_subset_1(B_7, u1_struct_0(A_6)) | ~l1_orders_2(A_6))), inference(resolution, [status(thm)], [c_8, c_465])).
% 4.69/1.87  tff(c_63, plain, (r1_orders_2('#skF_3', '#skF_4', '#skF_4') | ~l1_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_46, c_59])).
% 4.69/1.87  tff(c_69, plain, (r1_orders_2('#skF_3', '#skF_4', '#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_48, c_63])).
% 4.69/1.87  tff(c_87, plain, (r1_orders_2('#skF_3', '#skF_4', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_82, c_69])).
% 4.69/1.87  tff(c_831, plain, (![A_223, B_224, C_225, D_226]: (r1_orders_2(A_223, '#skF_2'(A_223, B_224, C_225, D_226), C_225) | k11_lattice3(A_223, B_224, C_225)=D_226 | ~r1_orders_2(A_223, D_226, C_225) | ~r1_orders_2(A_223, D_226, B_224) | ~m1_subset_1(D_226, u1_struct_0(A_223)) | ~m1_subset_1(C_225, u1_struct_0(A_223)) | ~m1_subset_1(B_224, u1_struct_0(A_223)) | ~l1_orders_2(A_223) | ~v2_lattice3(A_223) | ~v5_orders_2(A_223) | v2_struct_0(A_223))), inference(cnfTransformation, [status(thm)], [f_125])).
% 4.69/1.87  tff(c_24, plain, (![A_55, B_79, C_91, D_97]: (~r1_orders_2(A_55, '#skF_2'(A_55, B_79, C_91, D_97), D_97) | k11_lattice3(A_55, B_79, C_91)=D_97 | ~r1_orders_2(A_55, D_97, C_91) | ~r1_orders_2(A_55, D_97, B_79) | ~m1_subset_1(D_97, u1_struct_0(A_55)) | ~m1_subset_1(C_91, u1_struct_0(A_55)) | ~m1_subset_1(B_79, u1_struct_0(A_55)) | ~l1_orders_2(A_55) | ~v2_lattice3(A_55) | ~v5_orders_2(A_55) | v2_struct_0(A_55))), inference(cnfTransformation, [status(thm)], [f_125])).
% 4.69/1.87  tff(c_974, plain, (![A_244, B_245, C_246]: (k11_lattice3(A_244, B_245, C_246)=C_246 | ~r1_orders_2(A_244, C_246, C_246) | ~r1_orders_2(A_244, C_246, B_245) | ~m1_subset_1(C_246, u1_struct_0(A_244)) | ~m1_subset_1(B_245, u1_struct_0(A_244)) | ~l1_orders_2(A_244) | ~v2_lattice3(A_244) | ~v5_orders_2(A_244) | v2_struct_0(A_244))), inference(resolution, [status(thm)], [c_831, c_24])).
% 4.69/1.87  tff(c_978, plain, (![B_245]: (k11_lattice3('#skF_3', B_245, '#skF_4')='#skF_4' | ~r1_orders_2('#skF_3', '#skF_4', B_245) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~m1_subset_1(B_245, u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v2_lattice3('#skF_3') | ~v5_orders_2('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_87, c_974])).
% 4.69/1.87  tff(c_984, plain, (![B_245]: (k11_lattice3('#skF_3', B_245, '#skF_4')='#skF_4' | ~r1_orders_2('#skF_3', '#skF_4', B_245) | ~m1_subset_1(B_245, u1_struct_0('#skF_3')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_50, c_48, c_46, c_978])).
% 4.69/1.87  tff(c_1222, plain, (![B_251]: (k11_lattice3('#skF_3', B_251, '#skF_4')='#skF_4' | ~r1_orders_2('#skF_3', '#skF_4', B_251) | ~m1_subset_1(B_251, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_82, c_984])).
% 4.69/1.87  tff(c_1230, plain, (![B_7, C_8]: (k11_lattice3('#skF_3', k10_lattice3('#skF_3', B_7, C_8), '#skF_4')='#skF_4' | ~r1_orders_2('#skF_3', '#skF_4', k10_lattice3('#skF_3', B_7, C_8)) | ~m1_subset_1(C_8, u1_struct_0('#skF_3')) | ~m1_subset_1(B_7, u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3'))), inference(resolution, [status(thm)], [c_8, c_1222])).
% 4.69/1.87  tff(c_1276, plain, (![B_253, C_254]: (k11_lattice3('#skF_3', k10_lattice3('#skF_3', B_253, C_254), '#skF_4')='#skF_4' | ~r1_orders_2('#skF_3', '#skF_4', k10_lattice3('#skF_3', B_253, C_254)) | ~m1_subset_1(C_254, u1_struct_0('#skF_3')) | ~m1_subset_1(B_253, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_1230])).
% 4.69/1.87  tff(c_1280, plain, (![C_8]: (k11_lattice3('#skF_3', k10_lattice3('#skF_3', '#skF_4', C_8), '#skF_4')='#skF_4' | ~v1_lattice3('#skF_3') | ~v5_orders_2('#skF_3') | v2_struct_0('#skF_3') | ~m1_subset_1(C_8, u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3'))), inference(resolution, [status(thm)], [c_468, c_1276])).
% 4.69/1.87  tff(c_1287, plain, (![C_8]: (k11_lattice3('#skF_3', k10_lattice3('#skF_3', '#skF_4', C_8), '#skF_4')='#skF_4' | v2_struct_0('#skF_3') | ~m1_subset_1(C_8, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_54, c_52, c_1280])).
% 4.69/1.87  tff(c_1293, plain, (![C_255]: (k11_lattice3('#skF_3', k10_lattice3('#skF_3', '#skF_4', C_255), '#skF_4')='#skF_4' | ~m1_subset_1(C_255, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_82, c_1287])).
% 4.69/1.87  tff(c_1315, plain, (k11_lattice3('#skF_3', k10_lattice3('#skF_3', '#skF_4', '#skF_5'), '#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_44, c_1293])).
% 4.69/1.87  tff(c_36, plain, (![A_55, B_79, C_91]: (r1_orders_2(A_55, k11_lattice3(A_55, B_79, C_91), B_79) | ~m1_subset_1(k11_lattice3(A_55, B_79, C_91), u1_struct_0(A_55)) | ~m1_subset_1(C_91, u1_struct_0(A_55)) | ~m1_subset_1(B_79, u1_struct_0(A_55)) | ~l1_orders_2(A_55) | ~v2_lattice3(A_55) | ~v5_orders_2(A_55) | v2_struct_0(A_55))), inference(cnfTransformation, [status(thm)], [f_125])).
% 4.69/1.87  tff(c_1320, plain, (r1_orders_2('#skF_3', k11_lattice3('#skF_3', k10_lattice3('#skF_3', '#skF_4', '#skF_5'), '#skF_4'), k10_lattice3('#skF_3', '#skF_4', '#skF_5')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~m1_subset_1(k10_lattice3('#skF_3', '#skF_4', '#skF_5'), u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v2_lattice3('#skF_3') | ~v5_orders_2('#skF_3') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1315, c_36])).
% 4.69/1.87  tff(c_1326, plain, (r1_orders_2('#skF_3', '#skF_4', k10_lattice3('#skF_3', '#skF_4', '#skF_5')) | ~m1_subset_1(k10_lattice3('#skF_3', '#skF_4', '#skF_5'), u1_struct_0('#skF_3')) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_50, c_48, c_46, c_46, c_1315, c_1320])).
% 4.69/1.87  tff(c_1327, plain, (r1_orders_2('#skF_3', '#skF_4', k10_lattice3('#skF_3', '#skF_4', '#skF_5')) | ~m1_subset_1(k10_lattice3('#skF_3', '#skF_4', '#skF_5'), u1_struct_0('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_82, c_1326])).
% 4.69/1.87  tff(c_1663, plain, (~m1_subset_1(k10_lattice3('#skF_3', '#skF_4', '#skF_5'), u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_1327])).
% 4.69/1.87  tff(c_1666, plain, (~m1_subset_1('#skF_5', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3')), inference(resolution, [status(thm)], [c_8, c_1663])).
% 4.69/1.87  tff(c_1670, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_1666])).
% 4.69/1.87  tff(c_1672, plain, (m1_subset_1(k10_lattice3('#skF_3', '#skF_4', '#skF_5'), u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_1327])).
% 4.69/1.87  tff(c_151, plain, (![A_123, B_124, C_125]: (k12_lattice3(A_123, B_124, C_125)=k11_lattice3(A_123, B_124, C_125) | ~m1_subset_1(C_125, u1_struct_0(A_123)) | ~m1_subset_1(B_124, u1_struct_0(A_123)) | ~l1_orders_2(A_123) | ~v2_lattice3(A_123) | ~v5_orders_2(A_123))), inference(cnfTransformation, [status(thm)], [f_137])).
% 4.69/1.87  tff(c_788, plain, (![A_216, B_217, B_218, C_219]: (k12_lattice3(A_216, B_217, k10_lattice3(A_216, B_218, C_219))=k11_lattice3(A_216, B_217, k10_lattice3(A_216, B_218, C_219)) | ~m1_subset_1(B_217, u1_struct_0(A_216)) | ~v2_lattice3(A_216) | ~v5_orders_2(A_216) | ~m1_subset_1(C_219, u1_struct_0(A_216)) | ~m1_subset_1(B_218, u1_struct_0(A_216)) | ~l1_orders_2(A_216))), inference(resolution, [status(thm)], [c_8, c_151])).
% 4.69/1.87  tff(c_794, plain, (![B_218, C_219]: (k12_lattice3('#skF_3', '#skF_4', k10_lattice3('#skF_3', B_218, C_219))=k11_lattice3('#skF_3', '#skF_4', k10_lattice3('#skF_3', B_218, C_219)) | ~v2_lattice3('#skF_3') | ~v5_orders_2('#skF_3') | ~m1_subset_1(C_219, u1_struct_0('#skF_3')) | ~m1_subset_1(B_218, u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3'))), inference(resolution, [status(thm)], [c_46, c_788])).
% 4.69/1.87  tff(c_872, plain, (![B_228, C_229]: (k12_lattice3('#skF_3', '#skF_4', k10_lattice3('#skF_3', B_228, C_229))=k11_lattice3('#skF_3', '#skF_4', k10_lattice3('#skF_3', B_228, C_229)) | ~m1_subset_1(C_229, u1_struct_0('#skF_3')) | ~m1_subset_1(B_228, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_54, c_50, c_794])).
% 4.69/1.87  tff(c_885, plain, (![B_230]: (k12_lattice3('#skF_3', '#skF_4', k10_lattice3('#skF_3', B_230, '#skF_5'))=k11_lattice3('#skF_3', '#skF_4', k10_lattice3('#skF_3', B_230, '#skF_5')) | ~m1_subset_1(B_230, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_44, c_872])).
% 4.69/1.87  tff(c_900, plain, (k12_lattice3('#skF_3', '#skF_4', k10_lattice3('#skF_3', '#skF_4', '#skF_5'))=k11_lattice3('#skF_3', '#skF_4', k10_lattice3('#skF_3', '#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_46, c_885])).
% 4.69/1.87  tff(c_88, plain, (![A_118, B_119, C_120]: (k13_lattice3(A_118, B_119, C_120)=k10_lattice3(A_118, B_119, C_120) | ~m1_subset_1(C_120, u1_struct_0(A_118)) | ~m1_subset_1(B_119, u1_struct_0(A_118)) | ~l1_orders_2(A_118) | ~v1_lattice3(A_118) | ~v5_orders_2(A_118))), inference(cnfTransformation, [status(thm)], [f_149])).
% 4.69/1.87  tff(c_92, plain, (![B_119]: (k13_lattice3('#skF_3', B_119, '#skF_5')=k10_lattice3('#skF_3', B_119, '#skF_5') | ~m1_subset_1(B_119, u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v1_lattice3('#skF_3') | ~v5_orders_2('#skF_3'))), inference(resolution, [status(thm)], [c_44, c_88])).
% 4.69/1.87  tff(c_102, plain, (![B_121]: (k13_lattice3('#skF_3', B_121, '#skF_5')=k10_lattice3('#skF_3', B_121, '#skF_5') | ~m1_subset_1(B_121, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_48, c_92])).
% 4.69/1.87  tff(c_117, plain, (k13_lattice3('#skF_3', '#skF_4', '#skF_5')=k10_lattice3('#skF_3', '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_46, c_102])).
% 4.69/1.87  tff(c_42, plain, (k12_lattice3('#skF_3', '#skF_4', k13_lattice3('#skF_3', '#skF_4', '#skF_5'))!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_168])).
% 4.69/1.87  tff(c_122, plain, (k12_lattice3('#skF_3', '#skF_4', k10_lattice3('#skF_3', '#skF_4', '#skF_5'))!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_117, c_42])).
% 4.69/1.87  tff(c_905, plain, (k11_lattice3('#skF_3', '#skF_4', k10_lattice3('#skF_3', '#skF_4', '#skF_5'))!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_900, c_122])).
% 4.69/1.87  tff(c_1671, plain, (r1_orders_2('#skF_3', '#skF_4', k10_lattice3('#skF_3', '#skF_4', '#skF_5'))), inference(splitRight, [status(thm)], [c_1327])).
% 4.69/1.87  tff(c_28, plain, (![A_55, B_79, C_91, D_97]: (r1_orders_2(A_55, '#skF_2'(A_55, B_79, C_91, D_97), B_79) | k11_lattice3(A_55, B_79, C_91)=D_97 | ~r1_orders_2(A_55, D_97, C_91) | ~r1_orders_2(A_55, D_97, B_79) | ~m1_subset_1(D_97, u1_struct_0(A_55)) | ~m1_subset_1(C_91, u1_struct_0(A_55)) | ~m1_subset_1(B_79, u1_struct_0(A_55)) | ~l1_orders_2(A_55) | ~v2_lattice3(A_55) | ~v5_orders_2(A_55) | v2_struct_0(A_55))), inference(cnfTransformation, [status(thm)], [f_125])).
% 4.69/1.87  tff(c_707, plain, (![A_207, B_208, C_209, D_210]: (~r1_orders_2(A_207, '#skF_2'(A_207, B_208, C_209, D_210), D_210) | k11_lattice3(A_207, B_208, C_209)=D_210 | ~r1_orders_2(A_207, D_210, C_209) | ~r1_orders_2(A_207, D_210, B_208) | ~m1_subset_1(D_210, u1_struct_0(A_207)) | ~m1_subset_1(C_209, u1_struct_0(A_207)) | ~m1_subset_1(B_208, u1_struct_0(A_207)) | ~l1_orders_2(A_207) | ~v2_lattice3(A_207) | ~v5_orders_2(A_207) | v2_struct_0(A_207))), inference(cnfTransformation, [status(thm)], [f_125])).
% 4.69/1.87  tff(c_712, plain, (![A_55, B_79, C_91]: (k11_lattice3(A_55, B_79, C_91)=B_79 | ~r1_orders_2(A_55, B_79, C_91) | ~r1_orders_2(A_55, B_79, B_79) | ~m1_subset_1(C_91, u1_struct_0(A_55)) | ~m1_subset_1(B_79, u1_struct_0(A_55)) | ~l1_orders_2(A_55) | ~v2_lattice3(A_55) | ~v5_orders_2(A_55) | v2_struct_0(A_55))), inference(resolution, [status(thm)], [c_28, c_707])).
% 4.69/1.87  tff(c_1677, plain, (k11_lattice3('#skF_3', '#skF_4', k10_lattice3('#skF_3', '#skF_4', '#skF_5'))='#skF_4' | ~r1_orders_2('#skF_3', '#skF_4', '#skF_4') | ~m1_subset_1(k10_lattice3('#skF_3', '#skF_4', '#skF_5'), u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v2_lattice3('#skF_3') | ~v5_orders_2('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_1671, c_712])).
% 4.69/1.87  tff(c_1683, plain, (k11_lattice3('#skF_3', '#skF_4', k10_lattice3('#skF_3', '#skF_4', '#skF_5'))='#skF_4' | ~m1_subset_1(k10_lattice3('#skF_3', '#skF_4', '#skF_5'), u1_struct_0('#skF_3')) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_50, c_48, c_46, c_87, c_1677])).
% 4.69/1.87  tff(c_1684, plain, (~m1_subset_1(k10_lattice3('#skF_3', '#skF_4', '#skF_5'), u1_struct_0('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_82, c_905, c_1683])).
% 4.69/1.87  tff(c_1849, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1672, c_1684])).
% 4.69/1.87  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.69/1.87  
% 4.69/1.87  Inference rules
% 4.69/1.87  ----------------------
% 4.69/1.87  #Ref     : 0
% 4.69/1.87  #Sup     : 389
% 4.69/1.87  #Fact    : 0
% 4.69/1.87  #Define  : 0
% 4.69/1.87  #Split   : 4
% 4.69/1.87  #Chain   : 0
% 4.69/1.87  #Close   : 0
% 4.69/1.87  
% 4.69/1.87  Ordering : KBO
% 4.69/1.87  
% 4.69/1.87  Simplification rules
% 4.69/1.87  ----------------------
% 4.69/1.87  #Subsume      : 2
% 4.69/1.87  #Demod        : 396
% 4.69/1.87  #Tautology    : 148
% 4.69/1.87  #SimpNegUnit  : 83
% 4.69/1.87  #BackRed      : 7
% 4.69/1.87  
% 4.69/1.87  #Partial instantiations: 0
% 4.69/1.87  #Strategies tried      : 1
% 4.69/1.88  
% 4.69/1.88  Timing (in seconds)
% 4.69/1.88  ----------------------
% 4.69/1.88  Preprocessing        : 0.34
% 4.69/1.88  Parsing              : 0.17
% 4.69/1.88  CNF conversion       : 0.03
% 4.69/1.88  Main loop            : 0.73
% 4.69/1.88  Inferencing          : 0.24
% 4.69/1.88  Reduction            : 0.25
% 4.69/1.88  Demodulation         : 0.18
% 4.69/1.88  BG Simplification    : 0.04
% 4.69/1.88  Subsumption          : 0.16
% 4.69/1.88  Abstraction          : 0.05
% 4.69/1.88  MUC search           : 0.00
% 4.69/1.88  Cooper               : 0.00
% 4.69/1.88  Total                : 1.11
% 4.69/1.88  Index Insertion      : 0.00
% 4.69/1.88  Index Deletion       : 0.00
% 4.69/1.88  Index Matching       : 0.00
% 4.69/1.88  BG Taut test         : 0.00
%------------------------------------------------------------------------------
