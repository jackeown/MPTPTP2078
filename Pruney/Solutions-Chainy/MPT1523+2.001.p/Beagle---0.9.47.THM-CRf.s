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
% DateTime   : Thu Dec  3 10:24:55 EST 2020

% Result     : Theorem 2.98s
% Output     : CNFRefutation 3.29s
% Verified   : 
% Statistics : Number of formulae       :  145 (1485 expanded)
%              Number of leaves         :   25 ( 490 expanded)
%              Depth                    :   20
%              Number of atoms          :  314 (6286 expanded)
%              Number of equality atoms :   68 (1884 expanded)
%              Maximal formula depth    :   18 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_orders_2 > r1_orders_2 > r2_hidden > m1_subset_1 > l1_orders_2 > k4_tarski > k2_zfmisc_1 > g1_orders_2 > #nlpp > u1_struct_0 > u1_orders_2 > k1_zfmisc_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff(g1_orders_2,type,(
    g1_orders_2: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(r2_orders_2,type,(
    r2_orders_2: ( $i * $i * $i ) > $o )).

tff(u1_orders_2,type,(
    u1_orders_2: $i > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_97,negated_conjecture,(
    ~ ! [A] :
        ( l1_orders_2(A)
       => ! [B] :
            ( l1_orders_2(B)
           => ( g1_orders_2(u1_struct_0(A),u1_orders_2(A)) = g1_orders_2(u1_struct_0(B),u1_orders_2(B))
             => ! [C] :
                  ( m1_subset_1(C,u1_struct_0(A))
                 => ! [D] :
                      ( m1_subset_1(D,u1_struct_0(A))
                     => ! [E] :
                          ( m1_subset_1(E,u1_struct_0(B))
                         => ! [F] :
                              ( m1_subset_1(F,u1_struct_0(B))
                             => ( ( C = E
                                  & D = F )
                               => ( ( r1_orders_2(A,C,D)
                                   => r1_orders_2(B,E,F) )
                                  & ( r2_orders_2(A,C,D)
                                   => r2_orders_2(B,E,F) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_yellow_0)).

tff(f_52,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( r1_orders_2(A,B,C)
              <=> r2_hidden(k4_tarski(B,C),u1_orders_2(A)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_orders_2)).

tff(f_56,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => m1_subset_1(u1_orders_2(A),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_orders_2)).

tff(f_65,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A)))
     => ! [C,D] :
          ( g1_orders_2(A,B) = g1_orders_2(C,D)
         => ( A = C
            & B = D ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_orders_2)).

tff(f_40,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( r2_orders_2(A,B,C)
              <=> ( r1_orders_2(A,B,C)
                  & B != C ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_orders_2)).

tff(c_34,plain,(
    l1_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_26,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_10,plain,(
    ! [B_12,C_14,A_8] :
      ( r2_hidden(k4_tarski(B_12,C_14),u1_orders_2(A_8))
      | ~ r1_orders_2(A_8,B_12,C_14)
      | ~ m1_subset_1(C_14,u1_struct_0(A_8))
      | ~ m1_subset_1(B_12,u1_struct_0(A_8))
      | ~ l1_orders_2(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_32,plain,(
    l1_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_12,plain,(
    ! [A_15] :
      ( m1_subset_1(u1_orders_2(A_15),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_15),u1_struct_0(A_15))))
      | ~ l1_orders_2(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_30,plain,(
    g1_orders_2(u1_struct_0('#skF_2'),u1_orders_2('#skF_2')) = g1_orders_2(u1_struct_0('#skF_1'),u1_orders_2('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_72,plain,(
    ! [D_82,B_83,C_84,A_85] :
      ( D_82 = B_83
      | g1_orders_2(C_84,D_82) != g1_orders_2(A_85,B_83)
      | ~ m1_subset_1(B_83,k1_zfmisc_1(k2_zfmisc_1(A_85,A_85))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_86,plain,(
    ! [B_90,A_91] :
      ( u1_orders_2('#skF_2') = B_90
      | g1_orders_2(u1_struct_0('#skF_1'),u1_orders_2('#skF_1')) != g1_orders_2(A_91,B_90)
      | ~ m1_subset_1(B_90,k1_zfmisc_1(k2_zfmisc_1(A_91,A_91))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_72])).

tff(c_90,plain,(
    ! [A_15] :
      ( u1_orders_2(A_15) = u1_orders_2('#skF_2')
      | g1_orders_2(u1_struct_0(A_15),u1_orders_2(A_15)) != g1_orders_2(u1_struct_0('#skF_1'),u1_orders_2('#skF_1'))
      | ~ l1_orders_2(A_15) ) ),
    inference(resolution,[status(thm)],[c_12,c_86])).

tff(c_93,plain,
    ( u1_orders_2('#skF_2') = u1_orders_2('#skF_1')
    | ~ l1_orders_2('#skF_1') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_90])).

tff(c_95,plain,(
    u1_orders_2('#skF_2') = u1_orders_2('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_93])).

tff(c_110,plain,
    ( m1_subset_1(u1_orders_2('#skF_1'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_2'))))
    | ~ l1_orders_2('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_95,c_12])).

tff(c_114,plain,(
    m1_subset_1(u1_orders_2('#skF_1'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_110])).

tff(c_106,plain,(
    g1_orders_2(u1_struct_0('#skF_2'),u1_orders_2('#skF_1')) = g1_orders_2(u1_struct_0('#skF_1'),u1_orders_2('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_30])).

tff(c_16,plain,(
    ! [C_20,A_16,D_21,B_17] :
      ( C_20 = A_16
      | g1_orders_2(C_20,D_21) != g1_orders_2(A_16,B_17)
      | ~ m1_subset_1(B_17,k1_zfmisc_1(k2_zfmisc_1(A_16,A_16))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_120,plain,(
    ! [C_20,D_21] :
      ( u1_struct_0('#skF_2') = C_20
      | g1_orders_2(u1_struct_0('#skF_1'),u1_orders_2('#skF_1')) != g1_orders_2(C_20,D_21)
      | ~ m1_subset_1(u1_orders_2('#skF_1'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_2')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_106,c_16])).

tff(c_128,plain,(
    ! [C_20,D_21] :
      ( u1_struct_0('#skF_2') = C_20
      | g1_orders_2(u1_struct_0('#skF_1'),u1_orders_2('#skF_1')) != g1_orders_2(C_20,D_21) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_120])).

tff(c_134,plain,(
    u1_struct_0('#skF_2') = u1_struct_0('#skF_1') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_128])).

tff(c_189,plain,(
    ! [A_107,B_108,C_109] :
      ( r1_orders_2(A_107,B_108,C_109)
      | ~ r2_hidden(k4_tarski(B_108,C_109),u1_orders_2(A_107))
      | ~ m1_subset_1(C_109,u1_struct_0(A_107))
      | ~ m1_subset_1(B_108,u1_struct_0(A_107))
      | ~ l1_orders_2(A_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_198,plain,(
    ! [B_108,C_109] :
      ( r1_orders_2('#skF_2',B_108,C_109)
      | ~ r2_hidden(k4_tarski(B_108,C_109),u1_orders_2('#skF_1'))
      | ~ m1_subset_1(C_109,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_108,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_95,c_189])).

tff(c_208,plain,(
    ! [B_112,C_113] :
      ( r1_orders_2('#skF_2',B_112,C_113)
      | ~ r2_hidden(k4_tarski(B_112,C_113),u1_orders_2('#skF_1'))
      | ~ m1_subset_1(C_113,u1_struct_0('#skF_1'))
      | ~ m1_subset_1(B_112,u1_struct_0('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_134,c_134,c_198])).

tff(c_215,plain,(
    ! [B_12,C_14] :
      ( r1_orders_2('#skF_2',B_12,C_14)
      | ~ r1_orders_2('#skF_1',B_12,C_14)
      | ~ m1_subset_1(C_14,u1_struct_0('#skF_1'))
      | ~ m1_subset_1(B_12,u1_struct_0('#skF_1'))
      | ~ l1_orders_2('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_10,c_208])).

tff(c_220,plain,(
    ! [B_114,C_115] :
      ( r1_orders_2('#skF_2',B_114,C_115)
      | ~ r1_orders_2('#skF_1',B_114,C_115)
      | ~ m1_subset_1(C_115,u1_struct_0('#skF_1'))
      | ~ m1_subset_1(B_114,u1_struct_0('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_215])).

tff(c_227,plain,(
    ! [B_116] :
      ( r1_orders_2('#skF_2',B_116,'#skF_4')
      | ~ r1_orders_2('#skF_1',B_116,'#skF_4')
      | ~ m1_subset_1(B_116,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_26,c_220])).

tff(c_234,plain,
    ( r1_orders_2('#skF_2','#skF_4','#skF_4')
    | ~ r1_orders_2('#skF_1','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_26,c_227])).

tff(c_258,plain,(
    ~ r1_orders_2('#skF_1','#skF_4','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_234])).

tff(c_18,plain,(
    '#skF_6' = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_20,plain,(
    '#skF_5' = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_36,plain,
    ( ~ r1_orders_2('#skF_2','#skF_5','#skF_6')
    | ~ r2_orders_2('#skF_2','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_45,plain,
    ( ~ r1_orders_2('#skF_2','#skF_3','#skF_6')
    | ~ r2_orders_2('#skF_2','#skF_3','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_20,c_36])).

tff(c_49,plain,
    ( ~ r1_orders_2('#skF_2','#skF_3','#skF_4')
    | ~ r2_orders_2('#skF_2','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_18,c_45])).

tff(c_59,plain,(
    ~ r2_orders_2('#skF_2','#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_49])).

tff(c_28,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_42,plain,
    ( r1_orders_2('#skF_1','#skF_3','#skF_4')
    | r2_orders_2('#skF_1','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_60,plain,(
    r2_orders_2('#skF_1','#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_141,plain,(
    ! [A_95,B_96,C_97] :
      ( r1_orders_2(A_95,B_96,C_97)
      | ~ r2_orders_2(A_95,B_96,C_97)
      | ~ m1_subset_1(C_97,u1_struct_0(A_95))
      | ~ m1_subset_1(B_96,u1_struct_0(A_95))
      | ~ l1_orders_2(A_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_143,plain,
    ( r1_orders_2('#skF_1','#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_1'))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_1'))
    | ~ l1_orders_2('#skF_1') ),
    inference(resolution,[status(thm)],[c_60,c_141])).

tff(c_146,plain,(
    r1_orders_2('#skF_1','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_28,c_26,c_143])).

tff(c_233,plain,
    ( r1_orders_2('#skF_2','#skF_3','#skF_4')
    | ~ r1_orders_2('#skF_1','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_227])).

tff(c_237,plain,(
    r1_orders_2('#skF_2','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_233])).

tff(c_243,plain,(
    ! [A_117,B_118,C_119] :
      ( r2_orders_2(A_117,B_118,C_119)
      | C_119 = B_118
      | ~ r1_orders_2(A_117,B_118,C_119)
      | ~ m1_subset_1(C_119,u1_struct_0(A_117))
      | ~ m1_subset_1(B_118,u1_struct_0(A_117))
      | ~ l1_orders_2(A_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_245,plain,(
    ! [B_118,C_119] :
      ( r2_orders_2('#skF_2',B_118,C_119)
      | C_119 = B_118
      | ~ r1_orders_2('#skF_2',B_118,C_119)
      | ~ m1_subset_1(C_119,u1_struct_0('#skF_1'))
      | ~ m1_subset_1(B_118,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_134,c_243])).

tff(c_292,plain,(
    ! [B_123,C_124] :
      ( r2_orders_2('#skF_2',B_123,C_124)
      | C_124 = B_123
      | ~ r1_orders_2('#skF_2',B_123,C_124)
      | ~ m1_subset_1(C_124,u1_struct_0('#skF_1'))
      | ~ m1_subset_1(B_123,u1_struct_0('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_134,c_245])).

tff(c_299,plain,(
    ! [B_125] :
      ( r2_orders_2('#skF_2',B_125,'#skF_4')
      | B_125 = '#skF_4'
      | ~ r1_orders_2('#skF_2',B_125,'#skF_4')
      | ~ m1_subset_1(B_125,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_26,c_292])).

tff(c_305,plain,
    ( r2_orders_2('#skF_2','#skF_3','#skF_4')
    | '#skF_3' = '#skF_4'
    | ~ r1_orders_2('#skF_2','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_299])).

tff(c_310,plain,
    ( r2_orders_2('#skF_2','#skF_3','#skF_4')
    | '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_237,c_305])).

tff(c_311,plain,(
    '#skF_3' = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_59,c_310])).

tff(c_317,plain,(
    r1_orders_2('#skF_1','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_311,c_146])).

tff(c_323,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_258,c_317])).

tff(c_325,plain,(
    r1_orders_2('#skF_1','#skF_4','#skF_4') ),
    inference(splitRight,[status(thm)],[c_234])).

tff(c_508,plain,(
    ! [B_138,C_139] :
      ( r2_orders_2('#skF_2',B_138,C_139)
      | C_139 = B_138
      | ~ r1_orders_2('#skF_2',B_138,C_139)
      | ~ m1_subset_1(C_139,u1_struct_0('#skF_1'))
      | ~ m1_subset_1(B_138,u1_struct_0('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_134,c_245])).

tff(c_515,plain,(
    ! [B_140] :
      ( r2_orders_2('#skF_2',B_140,'#skF_4')
      | B_140 = '#skF_4'
      | ~ r1_orders_2('#skF_2',B_140,'#skF_4')
      | ~ m1_subset_1(B_140,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_26,c_508])).

tff(c_521,plain,
    ( r2_orders_2('#skF_2','#skF_3','#skF_4')
    | '#skF_3' = '#skF_4'
    | ~ r1_orders_2('#skF_2','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_515])).

tff(c_528,plain,
    ( r2_orders_2('#skF_2','#skF_3','#skF_4')
    | '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_237,c_521])).

tff(c_529,plain,(
    '#skF_3' = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_59,c_528])).

tff(c_326,plain,(
    ! [B_126] :
      ( r1_orders_2('#skF_2',B_126,'#skF_3')
      | ~ r1_orders_2('#skF_1',B_126,'#skF_3')
      | ~ m1_subset_1(B_126,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_28,c_220])).

tff(c_333,plain,
    ( r1_orders_2('#skF_2','#skF_4','#skF_3')
    | ~ r1_orders_2('#skF_1','#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_326])).

tff(c_493,plain,(
    ~ r1_orders_2('#skF_1','#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_333])).

tff(c_531,plain,(
    ~ r1_orders_2('#skF_1','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_529,c_493])).

tff(c_543,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_325,c_531])).

tff(c_545,plain,(
    r1_orders_2('#skF_1','#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_333])).

tff(c_249,plain,(
    ! [B_118] :
      ( r2_orders_2('#skF_1',B_118,'#skF_3')
      | B_118 = '#skF_3'
      | ~ r1_orders_2('#skF_1',B_118,'#skF_3')
      | ~ m1_subset_1(B_118,u1_struct_0('#skF_1'))
      | ~ l1_orders_2('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_28,c_243])).

tff(c_546,plain,(
    ! [B_141] :
      ( r2_orders_2('#skF_1',B_141,'#skF_3')
      | B_141 = '#skF_3'
      | ~ r1_orders_2('#skF_1',B_141,'#skF_3')
      | ~ m1_subset_1(B_141,u1_struct_0('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_249])).

tff(c_553,plain,
    ( r2_orders_2('#skF_1','#skF_4','#skF_3')
    | '#skF_3' = '#skF_4'
    | ~ r1_orders_2('#skF_1','#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_546])).

tff(c_565,plain,
    ( r2_orders_2('#skF_1','#skF_4','#skF_3')
    | '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_545,c_553])).

tff(c_566,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_565])).

tff(c_575,plain,(
    r2_orders_2('#skF_1','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_566,c_60])).

tff(c_4,plain,(
    ! [A_1,C_7] :
      ( ~ r2_orders_2(A_1,C_7,C_7)
      | ~ m1_subset_1(C_7,u1_struct_0(A_1))
      | ~ l1_orders_2(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_597,plain,
    ( ~ m1_subset_1('#skF_4',u1_struct_0('#skF_1'))
    | ~ l1_orders_2('#skF_1') ),
    inference(resolution,[status(thm)],[c_575,c_4])).

tff(c_604,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_26,c_597])).

tff(c_606,plain,(
    '#skF_3' != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_565])).

tff(c_614,plain,(
    ! [B_142,C_143] :
      ( r2_orders_2('#skF_2',B_142,C_143)
      | C_143 = B_142
      | ~ r1_orders_2('#skF_2',B_142,C_143)
      | ~ m1_subset_1(C_143,u1_struct_0('#skF_1'))
      | ~ m1_subset_1(B_142,u1_struct_0('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_134,c_245])).

tff(c_621,plain,(
    ! [B_144] :
      ( r2_orders_2('#skF_2',B_144,'#skF_4')
      | B_144 = '#skF_4'
      | ~ r1_orders_2('#skF_2',B_144,'#skF_4')
      | ~ m1_subset_1(B_144,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_26,c_614])).

tff(c_627,plain,
    ( r2_orders_2('#skF_2','#skF_3','#skF_4')
    | '#skF_3' = '#skF_4'
    | ~ r1_orders_2('#skF_2','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_621])).

tff(c_634,plain,
    ( r2_orders_2('#skF_2','#skF_3','#skF_4')
    | '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_237,c_627])).

tff(c_636,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_606,c_59,c_634])).

tff(c_638,plain,(
    ~ r2_orders_2('#skF_1','#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_637,plain,(
    r1_orders_2('#skF_1','#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_763,plain,(
    ! [A_173,B_174,C_175] :
      ( r2_orders_2(A_173,B_174,C_175)
      | C_175 = B_174
      | ~ r1_orders_2(A_173,B_174,C_175)
      | ~ m1_subset_1(C_175,u1_struct_0(A_173))
      | ~ m1_subset_1(B_174,u1_struct_0(A_173))
      | ~ l1_orders_2(A_173) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_767,plain,(
    ! [B_174] :
      ( r2_orders_2('#skF_1',B_174,'#skF_4')
      | B_174 = '#skF_4'
      | ~ r1_orders_2('#skF_1',B_174,'#skF_4')
      | ~ m1_subset_1(B_174,u1_struct_0('#skF_1'))
      | ~ l1_orders_2('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_26,c_763])).

tff(c_778,plain,(
    ! [B_176] :
      ( r2_orders_2('#skF_1',B_176,'#skF_4')
      | B_176 = '#skF_4'
      | ~ r1_orders_2('#skF_1',B_176,'#skF_4')
      | ~ m1_subset_1(B_176,u1_struct_0('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_767])).

tff(c_784,plain,
    ( r2_orders_2('#skF_1','#skF_3','#skF_4')
    | '#skF_3' = '#skF_4'
    | ~ r1_orders_2('#skF_1','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_778])).

tff(c_789,plain,
    ( r2_orders_2('#skF_1','#skF_3','#skF_4')
    | '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_637,c_784])).

tff(c_790,plain,(
    '#skF_3' = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_638,c_789])).

tff(c_40,plain,
    ( ~ r1_orders_2('#skF_2','#skF_5','#skF_6')
    | r2_orders_2('#skF_1','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_46,plain,
    ( ~ r1_orders_2('#skF_2','#skF_3','#skF_6')
    | r2_orders_2('#skF_1','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_40])).

tff(c_50,plain,
    ( ~ r1_orders_2('#skF_2','#skF_3','#skF_4')
    | r2_orders_2('#skF_1','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_46])).

tff(c_643,plain,(
    ~ r1_orders_2('#skF_2','#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_638,c_50])).

tff(c_793,plain,(
    ~ r1_orders_2('#skF_2','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_790,c_643])).

tff(c_796,plain,(
    r1_orders_2('#skF_1','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_790,c_637])).

tff(c_651,plain,(
    ! [D_148,B_149,C_150,A_151] :
      ( D_148 = B_149
      | g1_orders_2(C_150,D_148) != g1_orders_2(A_151,B_149)
      | ~ m1_subset_1(B_149,k1_zfmisc_1(k2_zfmisc_1(A_151,A_151))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_665,plain,(
    ! [B_156,A_157] :
      ( u1_orders_2('#skF_2') = B_156
      | g1_orders_2(u1_struct_0('#skF_1'),u1_orders_2('#skF_1')) != g1_orders_2(A_157,B_156)
      | ~ m1_subset_1(B_156,k1_zfmisc_1(k2_zfmisc_1(A_157,A_157))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_651])).

tff(c_669,plain,(
    ! [A_15] :
      ( u1_orders_2(A_15) = u1_orders_2('#skF_2')
      | g1_orders_2(u1_struct_0(A_15),u1_orders_2(A_15)) != g1_orders_2(u1_struct_0('#skF_1'),u1_orders_2('#skF_1'))
      | ~ l1_orders_2(A_15) ) ),
    inference(resolution,[status(thm)],[c_12,c_665])).

tff(c_672,plain,
    ( u1_orders_2('#skF_2') = u1_orders_2('#skF_1')
    | ~ l1_orders_2('#skF_1') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_669])).

tff(c_674,plain,(
    u1_orders_2('#skF_2') = u1_orders_2('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_672])).

tff(c_689,plain,
    ( m1_subset_1(u1_orders_2('#skF_1'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_2'))))
    | ~ l1_orders_2('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_674,c_12])).

tff(c_693,plain,(
    m1_subset_1(u1_orders_2('#skF_1'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_689])).

tff(c_685,plain,(
    g1_orders_2(u1_struct_0('#skF_2'),u1_orders_2('#skF_1')) = g1_orders_2(u1_struct_0('#skF_1'),u1_orders_2('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_674,c_30])).

tff(c_699,plain,(
    ! [C_20,D_21] :
      ( u1_struct_0('#skF_2') = C_20
      | g1_orders_2(u1_struct_0('#skF_1'),u1_orders_2('#skF_1')) != g1_orders_2(C_20,D_21)
      | ~ m1_subset_1(u1_orders_2('#skF_1'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_2')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_685,c_16])).

tff(c_707,plain,(
    ! [C_20,D_21] :
      ( u1_struct_0('#skF_2') = C_20
      | g1_orders_2(u1_struct_0('#skF_1'),u1_orders_2('#skF_1')) != g1_orders_2(C_20,D_21) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_693,c_699])).

tff(c_713,plain,(
    u1_struct_0('#skF_2') = u1_struct_0('#skF_1') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_707])).

tff(c_808,plain,(
    ! [A_177,B_178,C_179] :
      ( r1_orders_2(A_177,B_178,C_179)
      | ~ r2_hidden(k4_tarski(B_178,C_179),u1_orders_2(A_177))
      | ~ m1_subset_1(C_179,u1_struct_0(A_177))
      | ~ m1_subset_1(B_178,u1_struct_0(A_177))
      | ~ l1_orders_2(A_177) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_817,plain,(
    ! [B_178,C_179] :
      ( r1_orders_2('#skF_2',B_178,C_179)
      | ~ r2_hidden(k4_tarski(B_178,C_179),u1_orders_2('#skF_1'))
      | ~ m1_subset_1(C_179,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_178,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_674,c_808])).

tff(c_828,plain,(
    ! [B_182,C_183] :
      ( r1_orders_2('#skF_2',B_182,C_183)
      | ~ r2_hidden(k4_tarski(B_182,C_183),u1_orders_2('#skF_1'))
      | ~ m1_subset_1(C_183,u1_struct_0('#skF_1'))
      | ~ m1_subset_1(B_182,u1_struct_0('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_713,c_713,c_817])).

tff(c_835,plain,(
    ! [B_12,C_14] :
      ( r1_orders_2('#skF_2',B_12,C_14)
      | ~ r1_orders_2('#skF_1',B_12,C_14)
      | ~ m1_subset_1(C_14,u1_struct_0('#skF_1'))
      | ~ m1_subset_1(B_12,u1_struct_0('#skF_1'))
      | ~ l1_orders_2('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_10,c_828])).

tff(c_840,plain,(
    ! [B_184,C_185] :
      ( r1_orders_2('#skF_2',B_184,C_185)
      | ~ r1_orders_2('#skF_1',B_184,C_185)
      | ~ m1_subset_1(C_185,u1_struct_0('#skF_1'))
      | ~ m1_subset_1(B_184,u1_struct_0('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_835])).

tff(c_844,plain,(
    ! [B_186] :
      ( r1_orders_2('#skF_2',B_186,'#skF_4')
      | ~ r1_orders_2('#skF_1',B_186,'#skF_4')
      | ~ m1_subset_1(B_186,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_26,c_840])).

tff(c_847,plain,
    ( r1_orders_2('#skF_2','#skF_4','#skF_4')
    | ~ r1_orders_2('#skF_1','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_26,c_844])).

tff(c_850,plain,(
    r1_orders_2('#skF_2','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_796,c_847])).

tff(c_852,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_793,c_850])).

tff(c_853,plain,(
    ~ r1_orders_2('#skF_2','#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_49])).

tff(c_24,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_43,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_24])).

tff(c_22,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_48,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_22])).

tff(c_854,plain,(
    r2_orders_2('#skF_2','#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_49])).

tff(c_887,plain,(
    ! [A_200,B_201,C_202] :
      ( r1_orders_2(A_200,B_201,C_202)
      | ~ r2_orders_2(A_200,B_201,C_202)
      | ~ m1_subset_1(C_202,u1_struct_0(A_200))
      | ~ m1_subset_1(B_201,u1_struct_0(A_200))
      | ~ l1_orders_2(A_200) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_891,plain,
    ( r1_orders_2('#skF_2','#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_854,c_887])).

tff(c_897,plain,(
    r1_orders_2('#skF_2','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_43,c_48,c_891])).

tff(c_899,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_853,c_897])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n004.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:10:08 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.98/1.51  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.98/1.52  
% 2.98/1.52  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.98/1.52  %$ r2_orders_2 > r1_orders_2 > r2_hidden > m1_subset_1 > l1_orders_2 > k4_tarski > k2_zfmisc_1 > g1_orders_2 > #nlpp > u1_struct_0 > u1_orders_2 > k1_zfmisc_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.98/1.52  
% 2.98/1.52  %Foreground sorts:
% 2.98/1.52  
% 2.98/1.52  
% 2.98/1.52  %Background operators:
% 2.98/1.52  
% 2.98/1.52  
% 2.98/1.52  %Foreground operators:
% 2.98/1.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.98/1.52  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.98/1.52  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.98/1.52  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 2.98/1.52  tff(g1_orders_2, type, g1_orders_2: ($i * $i) > $i).
% 2.98/1.52  tff('#skF_5', type, '#skF_5': $i).
% 2.98/1.52  tff('#skF_6', type, '#skF_6': $i).
% 2.98/1.52  tff('#skF_2', type, '#skF_2': $i).
% 2.98/1.52  tff('#skF_3', type, '#skF_3': $i).
% 2.98/1.52  tff('#skF_1', type, '#skF_1': $i).
% 2.98/1.52  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.98/1.52  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.98/1.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.98/1.52  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.98/1.52  tff('#skF_4', type, '#skF_4': $i).
% 2.98/1.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.98/1.52  tff(r2_orders_2, type, r2_orders_2: ($i * $i * $i) > $o).
% 2.98/1.52  tff(u1_orders_2, type, u1_orders_2: $i > $i).
% 2.98/1.52  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.98/1.52  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.98/1.52  
% 3.29/1.55  tff(f_97, negated_conjecture, ~(![A]: (l1_orders_2(A) => (![B]: (l1_orders_2(B) => ((g1_orders_2(u1_struct_0(A), u1_orders_2(A)) = g1_orders_2(u1_struct_0(B), u1_orders_2(B))) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => (![E]: (m1_subset_1(E, u1_struct_0(B)) => (![F]: (m1_subset_1(F, u1_struct_0(B)) => (((C = E) & (D = F)) => ((r1_orders_2(A, C, D) => r1_orders_2(B, E, F)) & (r2_orders_2(A, C, D) => r2_orders_2(B, E, F))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_yellow_0)).
% 3.29/1.55  tff(f_52, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r1_orders_2(A, B, C) <=> r2_hidden(k4_tarski(B, C), u1_orders_2(A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_orders_2)).
% 3.29/1.55  tff(f_56, axiom, (![A]: (l1_orders_2(A) => m1_subset_1(u1_orders_2(A), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_u1_orders_2)).
% 3.29/1.55  tff(f_65, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A))) => (![C, D]: ((g1_orders_2(A, B) = g1_orders_2(C, D)) => ((A = C) & (B = D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', free_g1_orders_2)).
% 3.29/1.55  tff(f_40, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_orders_2(A, B, C) <=> (r1_orders_2(A, B, C) & ~(B = C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_orders_2)).
% 3.29/1.55  tff(c_34, plain, (l1_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.29/1.55  tff(c_26, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.29/1.55  tff(c_10, plain, (![B_12, C_14, A_8]: (r2_hidden(k4_tarski(B_12, C_14), u1_orders_2(A_8)) | ~r1_orders_2(A_8, B_12, C_14) | ~m1_subset_1(C_14, u1_struct_0(A_8)) | ~m1_subset_1(B_12, u1_struct_0(A_8)) | ~l1_orders_2(A_8))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.29/1.55  tff(c_32, plain, (l1_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.29/1.55  tff(c_12, plain, (![A_15]: (m1_subset_1(u1_orders_2(A_15), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_15), u1_struct_0(A_15)))) | ~l1_orders_2(A_15))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.29/1.55  tff(c_30, plain, (g1_orders_2(u1_struct_0('#skF_2'), u1_orders_2('#skF_2'))=g1_orders_2(u1_struct_0('#skF_1'), u1_orders_2('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.29/1.55  tff(c_72, plain, (![D_82, B_83, C_84, A_85]: (D_82=B_83 | g1_orders_2(C_84, D_82)!=g1_orders_2(A_85, B_83) | ~m1_subset_1(B_83, k1_zfmisc_1(k2_zfmisc_1(A_85, A_85))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.29/1.55  tff(c_86, plain, (![B_90, A_91]: (u1_orders_2('#skF_2')=B_90 | g1_orders_2(u1_struct_0('#skF_1'), u1_orders_2('#skF_1'))!=g1_orders_2(A_91, B_90) | ~m1_subset_1(B_90, k1_zfmisc_1(k2_zfmisc_1(A_91, A_91))))), inference(superposition, [status(thm), theory('equality')], [c_30, c_72])).
% 3.29/1.55  tff(c_90, plain, (![A_15]: (u1_orders_2(A_15)=u1_orders_2('#skF_2') | g1_orders_2(u1_struct_0(A_15), u1_orders_2(A_15))!=g1_orders_2(u1_struct_0('#skF_1'), u1_orders_2('#skF_1')) | ~l1_orders_2(A_15))), inference(resolution, [status(thm)], [c_12, c_86])).
% 3.29/1.55  tff(c_93, plain, (u1_orders_2('#skF_2')=u1_orders_2('#skF_1') | ~l1_orders_2('#skF_1')), inference(reflexivity, [status(thm), theory('equality')], [c_90])).
% 3.29/1.55  tff(c_95, plain, (u1_orders_2('#skF_2')=u1_orders_2('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_93])).
% 3.29/1.55  tff(c_110, plain, (m1_subset_1(u1_orders_2('#skF_1'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_2')))) | ~l1_orders_2('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_95, c_12])).
% 3.29/1.55  tff(c_114, plain, (m1_subset_1(u1_orders_2('#skF_1'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_110])).
% 3.29/1.55  tff(c_106, plain, (g1_orders_2(u1_struct_0('#skF_2'), u1_orders_2('#skF_1'))=g1_orders_2(u1_struct_0('#skF_1'), u1_orders_2('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_95, c_30])).
% 3.29/1.55  tff(c_16, plain, (![C_20, A_16, D_21, B_17]: (C_20=A_16 | g1_orders_2(C_20, D_21)!=g1_orders_2(A_16, B_17) | ~m1_subset_1(B_17, k1_zfmisc_1(k2_zfmisc_1(A_16, A_16))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.29/1.55  tff(c_120, plain, (![C_20, D_21]: (u1_struct_0('#skF_2')=C_20 | g1_orders_2(u1_struct_0('#skF_1'), u1_orders_2('#skF_1'))!=g1_orders_2(C_20, D_21) | ~m1_subset_1(u1_orders_2('#skF_1'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_2')))))), inference(superposition, [status(thm), theory('equality')], [c_106, c_16])).
% 3.29/1.55  tff(c_128, plain, (![C_20, D_21]: (u1_struct_0('#skF_2')=C_20 | g1_orders_2(u1_struct_0('#skF_1'), u1_orders_2('#skF_1'))!=g1_orders_2(C_20, D_21))), inference(demodulation, [status(thm), theory('equality')], [c_114, c_120])).
% 3.29/1.55  tff(c_134, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_1')), inference(reflexivity, [status(thm), theory('equality')], [c_128])).
% 3.29/1.55  tff(c_189, plain, (![A_107, B_108, C_109]: (r1_orders_2(A_107, B_108, C_109) | ~r2_hidden(k4_tarski(B_108, C_109), u1_orders_2(A_107)) | ~m1_subset_1(C_109, u1_struct_0(A_107)) | ~m1_subset_1(B_108, u1_struct_0(A_107)) | ~l1_orders_2(A_107))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.29/1.55  tff(c_198, plain, (![B_108, C_109]: (r1_orders_2('#skF_2', B_108, C_109) | ~r2_hidden(k4_tarski(B_108, C_109), u1_orders_2('#skF_1')) | ~m1_subset_1(C_109, u1_struct_0('#skF_2')) | ~m1_subset_1(B_108, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_95, c_189])).
% 3.29/1.55  tff(c_208, plain, (![B_112, C_113]: (r1_orders_2('#skF_2', B_112, C_113) | ~r2_hidden(k4_tarski(B_112, C_113), u1_orders_2('#skF_1')) | ~m1_subset_1(C_113, u1_struct_0('#skF_1')) | ~m1_subset_1(B_112, u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_134, c_134, c_198])).
% 3.29/1.55  tff(c_215, plain, (![B_12, C_14]: (r1_orders_2('#skF_2', B_12, C_14) | ~r1_orders_2('#skF_1', B_12, C_14) | ~m1_subset_1(C_14, u1_struct_0('#skF_1')) | ~m1_subset_1(B_12, u1_struct_0('#skF_1')) | ~l1_orders_2('#skF_1'))), inference(resolution, [status(thm)], [c_10, c_208])).
% 3.29/1.55  tff(c_220, plain, (![B_114, C_115]: (r1_orders_2('#skF_2', B_114, C_115) | ~r1_orders_2('#skF_1', B_114, C_115) | ~m1_subset_1(C_115, u1_struct_0('#skF_1')) | ~m1_subset_1(B_114, u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_215])).
% 3.29/1.55  tff(c_227, plain, (![B_116]: (r1_orders_2('#skF_2', B_116, '#skF_4') | ~r1_orders_2('#skF_1', B_116, '#skF_4') | ~m1_subset_1(B_116, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_26, c_220])).
% 3.29/1.55  tff(c_234, plain, (r1_orders_2('#skF_2', '#skF_4', '#skF_4') | ~r1_orders_2('#skF_1', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_26, c_227])).
% 3.29/1.55  tff(c_258, plain, (~r1_orders_2('#skF_1', '#skF_4', '#skF_4')), inference(splitLeft, [status(thm)], [c_234])).
% 3.29/1.55  tff(c_18, plain, ('#skF_6'='#skF_4'), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.29/1.55  tff(c_20, plain, ('#skF_5'='#skF_3'), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.29/1.55  tff(c_36, plain, (~r1_orders_2('#skF_2', '#skF_5', '#skF_6') | ~r2_orders_2('#skF_2', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.29/1.55  tff(c_45, plain, (~r1_orders_2('#skF_2', '#skF_3', '#skF_6') | ~r2_orders_2('#skF_2', '#skF_3', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_20, c_36])).
% 3.29/1.55  tff(c_49, plain, (~r1_orders_2('#skF_2', '#skF_3', '#skF_4') | ~r2_orders_2('#skF_2', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_18, c_45])).
% 3.29/1.55  tff(c_59, plain, (~r2_orders_2('#skF_2', '#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_49])).
% 3.29/1.55  tff(c_28, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.29/1.55  tff(c_42, plain, (r1_orders_2('#skF_1', '#skF_3', '#skF_4') | r2_orders_2('#skF_1', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.29/1.55  tff(c_60, plain, (r2_orders_2('#skF_1', '#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_42])).
% 3.29/1.55  tff(c_141, plain, (![A_95, B_96, C_97]: (r1_orders_2(A_95, B_96, C_97) | ~r2_orders_2(A_95, B_96, C_97) | ~m1_subset_1(C_97, u1_struct_0(A_95)) | ~m1_subset_1(B_96, u1_struct_0(A_95)) | ~l1_orders_2(A_95))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.29/1.55  tff(c_143, plain, (r1_orders_2('#skF_1', '#skF_3', '#skF_4') | ~m1_subset_1('#skF_4', u1_struct_0('#skF_1')) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_1')) | ~l1_orders_2('#skF_1')), inference(resolution, [status(thm)], [c_60, c_141])).
% 3.29/1.55  tff(c_146, plain, (r1_orders_2('#skF_1', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_28, c_26, c_143])).
% 3.29/1.55  tff(c_233, plain, (r1_orders_2('#skF_2', '#skF_3', '#skF_4') | ~r1_orders_2('#skF_1', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_28, c_227])).
% 3.29/1.55  tff(c_237, plain, (r1_orders_2('#skF_2', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_146, c_233])).
% 3.29/1.55  tff(c_243, plain, (![A_117, B_118, C_119]: (r2_orders_2(A_117, B_118, C_119) | C_119=B_118 | ~r1_orders_2(A_117, B_118, C_119) | ~m1_subset_1(C_119, u1_struct_0(A_117)) | ~m1_subset_1(B_118, u1_struct_0(A_117)) | ~l1_orders_2(A_117))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.29/1.55  tff(c_245, plain, (![B_118, C_119]: (r2_orders_2('#skF_2', B_118, C_119) | C_119=B_118 | ~r1_orders_2('#skF_2', B_118, C_119) | ~m1_subset_1(C_119, u1_struct_0('#skF_1')) | ~m1_subset_1(B_118, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_134, c_243])).
% 3.29/1.55  tff(c_292, plain, (![B_123, C_124]: (r2_orders_2('#skF_2', B_123, C_124) | C_124=B_123 | ~r1_orders_2('#skF_2', B_123, C_124) | ~m1_subset_1(C_124, u1_struct_0('#skF_1')) | ~m1_subset_1(B_123, u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_134, c_245])).
% 3.29/1.55  tff(c_299, plain, (![B_125]: (r2_orders_2('#skF_2', B_125, '#skF_4') | B_125='#skF_4' | ~r1_orders_2('#skF_2', B_125, '#skF_4') | ~m1_subset_1(B_125, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_26, c_292])).
% 3.29/1.55  tff(c_305, plain, (r2_orders_2('#skF_2', '#skF_3', '#skF_4') | '#skF_3'='#skF_4' | ~r1_orders_2('#skF_2', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_28, c_299])).
% 3.29/1.55  tff(c_310, plain, (r2_orders_2('#skF_2', '#skF_3', '#skF_4') | '#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_237, c_305])).
% 3.29/1.55  tff(c_311, plain, ('#skF_3'='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_59, c_310])).
% 3.29/1.55  tff(c_317, plain, (r1_orders_2('#skF_1', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_311, c_146])).
% 3.29/1.55  tff(c_323, plain, $false, inference(negUnitSimplification, [status(thm)], [c_258, c_317])).
% 3.29/1.55  tff(c_325, plain, (r1_orders_2('#skF_1', '#skF_4', '#skF_4')), inference(splitRight, [status(thm)], [c_234])).
% 3.29/1.55  tff(c_508, plain, (![B_138, C_139]: (r2_orders_2('#skF_2', B_138, C_139) | C_139=B_138 | ~r1_orders_2('#skF_2', B_138, C_139) | ~m1_subset_1(C_139, u1_struct_0('#skF_1')) | ~m1_subset_1(B_138, u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_134, c_245])).
% 3.29/1.55  tff(c_515, plain, (![B_140]: (r2_orders_2('#skF_2', B_140, '#skF_4') | B_140='#skF_4' | ~r1_orders_2('#skF_2', B_140, '#skF_4') | ~m1_subset_1(B_140, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_26, c_508])).
% 3.29/1.55  tff(c_521, plain, (r2_orders_2('#skF_2', '#skF_3', '#skF_4') | '#skF_3'='#skF_4' | ~r1_orders_2('#skF_2', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_28, c_515])).
% 3.29/1.55  tff(c_528, plain, (r2_orders_2('#skF_2', '#skF_3', '#skF_4') | '#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_237, c_521])).
% 3.29/1.55  tff(c_529, plain, ('#skF_3'='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_59, c_528])).
% 3.29/1.55  tff(c_326, plain, (![B_126]: (r1_orders_2('#skF_2', B_126, '#skF_3') | ~r1_orders_2('#skF_1', B_126, '#skF_3') | ~m1_subset_1(B_126, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_28, c_220])).
% 3.29/1.55  tff(c_333, plain, (r1_orders_2('#skF_2', '#skF_4', '#skF_3') | ~r1_orders_2('#skF_1', '#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_26, c_326])).
% 3.29/1.55  tff(c_493, plain, (~r1_orders_2('#skF_1', '#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_333])).
% 3.29/1.55  tff(c_531, plain, (~r1_orders_2('#skF_1', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_529, c_493])).
% 3.29/1.55  tff(c_543, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_325, c_531])).
% 3.29/1.55  tff(c_545, plain, (r1_orders_2('#skF_1', '#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_333])).
% 3.29/1.55  tff(c_249, plain, (![B_118]: (r2_orders_2('#skF_1', B_118, '#skF_3') | B_118='#skF_3' | ~r1_orders_2('#skF_1', B_118, '#skF_3') | ~m1_subset_1(B_118, u1_struct_0('#skF_1')) | ~l1_orders_2('#skF_1'))), inference(resolution, [status(thm)], [c_28, c_243])).
% 3.29/1.55  tff(c_546, plain, (![B_141]: (r2_orders_2('#skF_1', B_141, '#skF_3') | B_141='#skF_3' | ~r1_orders_2('#skF_1', B_141, '#skF_3') | ~m1_subset_1(B_141, u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_249])).
% 3.29/1.55  tff(c_553, plain, (r2_orders_2('#skF_1', '#skF_4', '#skF_3') | '#skF_3'='#skF_4' | ~r1_orders_2('#skF_1', '#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_26, c_546])).
% 3.29/1.55  tff(c_565, plain, (r2_orders_2('#skF_1', '#skF_4', '#skF_3') | '#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_545, c_553])).
% 3.29/1.55  tff(c_566, plain, ('#skF_3'='#skF_4'), inference(splitLeft, [status(thm)], [c_565])).
% 3.29/1.55  tff(c_575, plain, (r2_orders_2('#skF_1', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_566, c_60])).
% 3.29/1.55  tff(c_4, plain, (![A_1, C_7]: (~r2_orders_2(A_1, C_7, C_7) | ~m1_subset_1(C_7, u1_struct_0(A_1)) | ~l1_orders_2(A_1))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.29/1.55  tff(c_597, plain, (~m1_subset_1('#skF_4', u1_struct_0('#skF_1')) | ~l1_orders_2('#skF_1')), inference(resolution, [status(thm)], [c_575, c_4])).
% 3.29/1.55  tff(c_604, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_26, c_597])).
% 3.29/1.55  tff(c_606, plain, ('#skF_3'!='#skF_4'), inference(splitRight, [status(thm)], [c_565])).
% 3.29/1.55  tff(c_614, plain, (![B_142, C_143]: (r2_orders_2('#skF_2', B_142, C_143) | C_143=B_142 | ~r1_orders_2('#skF_2', B_142, C_143) | ~m1_subset_1(C_143, u1_struct_0('#skF_1')) | ~m1_subset_1(B_142, u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_134, c_245])).
% 3.29/1.55  tff(c_621, plain, (![B_144]: (r2_orders_2('#skF_2', B_144, '#skF_4') | B_144='#skF_4' | ~r1_orders_2('#skF_2', B_144, '#skF_4') | ~m1_subset_1(B_144, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_26, c_614])).
% 3.29/1.55  tff(c_627, plain, (r2_orders_2('#skF_2', '#skF_3', '#skF_4') | '#skF_3'='#skF_4' | ~r1_orders_2('#skF_2', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_28, c_621])).
% 3.29/1.55  tff(c_634, plain, (r2_orders_2('#skF_2', '#skF_3', '#skF_4') | '#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_237, c_627])).
% 3.29/1.55  tff(c_636, plain, $false, inference(negUnitSimplification, [status(thm)], [c_606, c_59, c_634])).
% 3.29/1.55  tff(c_638, plain, (~r2_orders_2('#skF_1', '#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_42])).
% 3.29/1.55  tff(c_637, plain, (r1_orders_2('#skF_1', '#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_42])).
% 3.29/1.55  tff(c_763, plain, (![A_173, B_174, C_175]: (r2_orders_2(A_173, B_174, C_175) | C_175=B_174 | ~r1_orders_2(A_173, B_174, C_175) | ~m1_subset_1(C_175, u1_struct_0(A_173)) | ~m1_subset_1(B_174, u1_struct_0(A_173)) | ~l1_orders_2(A_173))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.29/1.55  tff(c_767, plain, (![B_174]: (r2_orders_2('#skF_1', B_174, '#skF_4') | B_174='#skF_4' | ~r1_orders_2('#skF_1', B_174, '#skF_4') | ~m1_subset_1(B_174, u1_struct_0('#skF_1')) | ~l1_orders_2('#skF_1'))), inference(resolution, [status(thm)], [c_26, c_763])).
% 3.29/1.55  tff(c_778, plain, (![B_176]: (r2_orders_2('#skF_1', B_176, '#skF_4') | B_176='#skF_4' | ~r1_orders_2('#skF_1', B_176, '#skF_4') | ~m1_subset_1(B_176, u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_767])).
% 3.29/1.55  tff(c_784, plain, (r2_orders_2('#skF_1', '#skF_3', '#skF_4') | '#skF_3'='#skF_4' | ~r1_orders_2('#skF_1', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_28, c_778])).
% 3.29/1.55  tff(c_789, plain, (r2_orders_2('#skF_1', '#skF_3', '#skF_4') | '#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_637, c_784])).
% 3.29/1.55  tff(c_790, plain, ('#skF_3'='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_638, c_789])).
% 3.29/1.55  tff(c_40, plain, (~r1_orders_2('#skF_2', '#skF_5', '#skF_6') | r2_orders_2('#skF_1', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.29/1.55  tff(c_46, plain, (~r1_orders_2('#skF_2', '#skF_3', '#skF_6') | r2_orders_2('#skF_1', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_40])).
% 3.29/1.55  tff(c_50, plain, (~r1_orders_2('#skF_2', '#skF_3', '#skF_4') | r2_orders_2('#skF_1', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_46])).
% 3.29/1.55  tff(c_643, plain, (~r1_orders_2('#skF_2', '#skF_3', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_638, c_50])).
% 3.29/1.55  tff(c_793, plain, (~r1_orders_2('#skF_2', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_790, c_643])).
% 3.29/1.55  tff(c_796, plain, (r1_orders_2('#skF_1', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_790, c_637])).
% 3.29/1.55  tff(c_651, plain, (![D_148, B_149, C_150, A_151]: (D_148=B_149 | g1_orders_2(C_150, D_148)!=g1_orders_2(A_151, B_149) | ~m1_subset_1(B_149, k1_zfmisc_1(k2_zfmisc_1(A_151, A_151))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.29/1.55  tff(c_665, plain, (![B_156, A_157]: (u1_orders_2('#skF_2')=B_156 | g1_orders_2(u1_struct_0('#skF_1'), u1_orders_2('#skF_1'))!=g1_orders_2(A_157, B_156) | ~m1_subset_1(B_156, k1_zfmisc_1(k2_zfmisc_1(A_157, A_157))))), inference(superposition, [status(thm), theory('equality')], [c_30, c_651])).
% 3.29/1.55  tff(c_669, plain, (![A_15]: (u1_orders_2(A_15)=u1_orders_2('#skF_2') | g1_orders_2(u1_struct_0(A_15), u1_orders_2(A_15))!=g1_orders_2(u1_struct_0('#skF_1'), u1_orders_2('#skF_1')) | ~l1_orders_2(A_15))), inference(resolution, [status(thm)], [c_12, c_665])).
% 3.29/1.55  tff(c_672, plain, (u1_orders_2('#skF_2')=u1_orders_2('#skF_1') | ~l1_orders_2('#skF_1')), inference(reflexivity, [status(thm), theory('equality')], [c_669])).
% 3.29/1.55  tff(c_674, plain, (u1_orders_2('#skF_2')=u1_orders_2('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_672])).
% 3.29/1.55  tff(c_689, plain, (m1_subset_1(u1_orders_2('#skF_1'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_2')))) | ~l1_orders_2('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_674, c_12])).
% 3.29/1.55  tff(c_693, plain, (m1_subset_1(u1_orders_2('#skF_1'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_689])).
% 3.29/1.55  tff(c_685, plain, (g1_orders_2(u1_struct_0('#skF_2'), u1_orders_2('#skF_1'))=g1_orders_2(u1_struct_0('#skF_1'), u1_orders_2('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_674, c_30])).
% 3.29/1.55  tff(c_699, plain, (![C_20, D_21]: (u1_struct_0('#skF_2')=C_20 | g1_orders_2(u1_struct_0('#skF_1'), u1_orders_2('#skF_1'))!=g1_orders_2(C_20, D_21) | ~m1_subset_1(u1_orders_2('#skF_1'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_2')))))), inference(superposition, [status(thm), theory('equality')], [c_685, c_16])).
% 3.29/1.55  tff(c_707, plain, (![C_20, D_21]: (u1_struct_0('#skF_2')=C_20 | g1_orders_2(u1_struct_0('#skF_1'), u1_orders_2('#skF_1'))!=g1_orders_2(C_20, D_21))), inference(demodulation, [status(thm), theory('equality')], [c_693, c_699])).
% 3.29/1.55  tff(c_713, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_1')), inference(reflexivity, [status(thm), theory('equality')], [c_707])).
% 3.29/1.55  tff(c_808, plain, (![A_177, B_178, C_179]: (r1_orders_2(A_177, B_178, C_179) | ~r2_hidden(k4_tarski(B_178, C_179), u1_orders_2(A_177)) | ~m1_subset_1(C_179, u1_struct_0(A_177)) | ~m1_subset_1(B_178, u1_struct_0(A_177)) | ~l1_orders_2(A_177))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.29/1.55  tff(c_817, plain, (![B_178, C_179]: (r1_orders_2('#skF_2', B_178, C_179) | ~r2_hidden(k4_tarski(B_178, C_179), u1_orders_2('#skF_1')) | ~m1_subset_1(C_179, u1_struct_0('#skF_2')) | ~m1_subset_1(B_178, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_674, c_808])).
% 3.29/1.55  tff(c_828, plain, (![B_182, C_183]: (r1_orders_2('#skF_2', B_182, C_183) | ~r2_hidden(k4_tarski(B_182, C_183), u1_orders_2('#skF_1')) | ~m1_subset_1(C_183, u1_struct_0('#skF_1')) | ~m1_subset_1(B_182, u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_713, c_713, c_817])).
% 3.29/1.55  tff(c_835, plain, (![B_12, C_14]: (r1_orders_2('#skF_2', B_12, C_14) | ~r1_orders_2('#skF_1', B_12, C_14) | ~m1_subset_1(C_14, u1_struct_0('#skF_1')) | ~m1_subset_1(B_12, u1_struct_0('#skF_1')) | ~l1_orders_2('#skF_1'))), inference(resolution, [status(thm)], [c_10, c_828])).
% 3.29/1.55  tff(c_840, plain, (![B_184, C_185]: (r1_orders_2('#skF_2', B_184, C_185) | ~r1_orders_2('#skF_1', B_184, C_185) | ~m1_subset_1(C_185, u1_struct_0('#skF_1')) | ~m1_subset_1(B_184, u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_835])).
% 3.29/1.55  tff(c_844, plain, (![B_186]: (r1_orders_2('#skF_2', B_186, '#skF_4') | ~r1_orders_2('#skF_1', B_186, '#skF_4') | ~m1_subset_1(B_186, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_26, c_840])).
% 3.29/1.55  tff(c_847, plain, (r1_orders_2('#skF_2', '#skF_4', '#skF_4') | ~r1_orders_2('#skF_1', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_26, c_844])).
% 3.29/1.55  tff(c_850, plain, (r1_orders_2('#skF_2', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_796, c_847])).
% 3.29/1.55  tff(c_852, plain, $false, inference(negUnitSimplification, [status(thm)], [c_793, c_850])).
% 3.29/1.55  tff(c_853, plain, (~r1_orders_2('#skF_2', '#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_49])).
% 3.29/1.55  tff(c_24, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.29/1.55  tff(c_43, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_24])).
% 3.29/1.55  tff(c_22, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.29/1.55  tff(c_48, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_22])).
% 3.29/1.55  tff(c_854, plain, (r2_orders_2('#skF_2', '#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_49])).
% 3.29/1.55  tff(c_887, plain, (![A_200, B_201, C_202]: (r1_orders_2(A_200, B_201, C_202) | ~r2_orders_2(A_200, B_201, C_202) | ~m1_subset_1(C_202, u1_struct_0(A_200)) | ~m1_subset_1(B_201, u1_struct_0(A_200)) | ~l1_orders_2(A_200))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.29/1.55  tff(c_891, plain, (r1_orders_2('#skF_2', '#skF_3', '#skF_4') | ~m1_subset_1('#skF_4', u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2')), inference(resolution, [status(thm)], [c_854, c_887])).
% 3.29/1.55  tff(c_897, plain, (r1_orders_2('#skF_2', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_43, c_48, c_891])).
% 3.29/1.55  tff(c_899, plain, $false, inference(negUnitSimplification, [status(thm)], [c_853, c_897])).
% 3.29/1.55  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.29/1.55  
% 3.29/1.55  Inference rules
% 3.29/1.55  ----------------------
% 3.29/1.55  #Ref     : 14
% 3.29/1.55  #Sup     : 141
% 3.29/1.55  #Fact    : 0
% 3.29/1.55  #Define  : 0
% 3.29/1.55  #Split   : 11
% 3.29/1.55  #Chain   : 0
% 3.29/1.55  #Close   : 0
% 3.29/1.55  
% 3.29/1.55  Ordering : KBO
% 3.29/1.55  
% 3.29/1.55  Simplification rules
% 3.29/1.55  ----------------------
% 3.29/1.55  #Subsume      : 38
% 3.29/1.55  #Demod        : 287
% 3.29/1.55  #Tautology    : 91
% 3.29/1.55  #SimpNegUnit  : 10
% 3.29/1.55  #BackRed      : 74
% 3.29/1.55  
% 3.29/1.55  #Partial instantiations: 0
% 3.29/1.55  #Strategies tried      : 1
% 3.29/1.55  
% 3.29/1.55  Timing (in seconds)
% 3.29/1.55  ----------------------
% 3.29/1.55  Preprocessing        : 0.30
% 3.29/1.55  Parsing              : 0.15
% 3.29/1.55  CNF conversion       : 0.03
% 3.29/1.55  Main loop            : 0.45
% 3.29/1.55  Inferencing          : 0.15
% 3.29/1.55  Reduction            : 0.16
% 3.29/1.55  Demodulation         : 0.11
% 3.29/1.55  BG Simplification    : 0.02
% 3.29/1.55  Subsumption          : 0.09
% 3.29/1.55  Abstraction          : 0.02
% 3.29/1.55  MUC search           : 0.00
% 3.29/1.55  Cooper               : 0.00
% 3.29/1.55  Total                : 0.80
% 3.29/1.55  Index Insertion      : 0.00
% 3.29/1.55  Index Deletion       : 0.00
% 3.29/1.55  Index Matching       : 0.00
% 3.29/1.55  BG Taut test         : 0.00
%------------------------------------------------------------------------------
