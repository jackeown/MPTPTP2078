%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1952+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:42 EST 2020

% Result     : Theorem 4.87s
% Output     : CNFRefutation 5.10s
% Verified   : 
% Statistics : Number of formulae       :  154 (1415 expanded)
%              Number of leaves         :   35 ( 473 expanded)
%              Depth                    :   20
%              Number of atoms          :  438 (7476 expanded)
%              Number of equality atoms :   23 ( 293 expanded)
%              Maximal formula depth    :   18 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_waybel_0 > v8_yellow_6 > v3_pre_topc > r2_hidden > m4_yellow_6 > m1_subset_1 > l1_waybel_0 > v7_waybel_0 > v4_orders_2 > v2_struct_0 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k4_tarski > k13_yellow_6 > a_2_1_yellow_6 > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_1 > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_8 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k13_yellow_6,type,(
    k13_yellow_6: ( $i * $i ) > $i )).

tff(v7_waybel_0,type,(
    v7_waybel_0: $i > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_waybel_0,type,(
    r1_waybel_0: ( $i * $i * $i ) > $o )).

tff(v8_yellow_6,type,(
    v8_yellow_6: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(a_2_1_yellow_6,type,(
    a_2_1_yellow_6: ( $i * $i ) > $i )).

tff(l1_waybel_0,type,(
    l1_waybel_0: ( $i * $i ) > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m4_yellow_6,type,(
    m4_yellow_6: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_137,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & l1_struct_0(A) )
       => ! [B] :
            ( ( v8_yellow_6(B,A)
              & m4_yellow_6(B,A) )
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(k13_yellow_6(A,B))))
               => ( v3_pre_topc(C,k13_yellow_6(A,B))
                <=> ! [D] :
                      ( m1_subset_1(D,u1_struct_0(A))
                     => ( r2_hidden(D,C)
                       => ! [E] :
                            ( ( ~ v2_struct_0(E)
                              & v4_orders_2(E)
                              & v7_waybel_0(E)
                              & l1_waybel_0(E,A) )
                           => ( r2_hidden(k4_tarski(E,D),B)
                             => r1_waybel_0(A,E,C) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_yellow_6)).

tff(f_63,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A)
        & m4_yellow_6(B,A) )
     => ( v1_pre_topc(k13_yellow_6(A,B))
        & l1_pre_topc(k13_yellow_6(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k13_yellow_6)).

tff(f_52,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_pre_topc(B,A)
          <=> r2_hidden(B,u1_pre_topc(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_pre_topc)).

tff(f_43,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ! [B] :
          ( m4_yellow_6(B,A)
         => ! [C] :
              ( ( v1_pre_topc(C)
                & l1_pre_topc(C) )
             => ( C = k13_yellow_6(A,B)
              <=> ( u1_struct_0(C) = u1_struct_0(A)
                  & u1_pre_topc(C) = a_2_1_yellow_6(A,B) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d27_yellow_6)).

tff(f_96,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(B)
        & l1_struct_0(B)
        & m4_yellow_6(C,B) )
     => ( r2_hidden(A,a_2_1_yellow_6(B,C))
      <=> ? [D] :
            ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(B)))
            & A = D
            & ! [E] :
                ( m1_subset_1(E,u1_struct_0(B))
               => ( r2_hidden(E,D)
                 => ! [F] :
                      ( ( ~ v2_struct_0(F)
                        & v4_orders_2(F)
                        & v7_waybel_0(F)
                        & l1_waybel_0(F,B) )
                     => ( r2_hidden(k4_tarski(F,E),C)
                       => r1_waybel_0(B,F,D) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fraenkel_a_2_1_yellow_6)).

tff(c_48,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_46,plain,(
    l1_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_42,plain,(
    m4_yellow_6('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_12,plain,(
    ! [A_11,B_12] :
      ( l1_pre_topc(k13_yellow_6(A_11,B_12))
      | ~ m4_yellow_6(B_12,A_11)
      | ~ l1_struct_0(A_11)
      | v2_struct_0(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_60,plain,
    ( ~ v2_struct_0('#skF_8')
    | ~ v3_pre_topc('#skF_6',k13_yellow_6('#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_85,plain,(
    ~ v3_pre_topc('#skF_6',k13_yellow_6('#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_40,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0(k13_yellow_6('#skF_4','#skF_5')))) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_93,plain,(
    ! [B_102,A_103] :
      ( v3_pre_topc(B_102,A_103)
      | ~ r2_hidden(B_102,u1_pre_topc(A_103))
      | ~ m1_subset_1(B_102,k1_zfmisc_1(u1_struct_0(A_103)))
      | ~ l1_pre_topc(A_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_96,plain,
    ( v3_pre_topc('#skF_6',k13_yellow_6('#skF_4','#skF_5'))
    | ~ r2_hidden('#skF_6',u1_pre_topc(k13_yellow_6('#skF_4','#skF_5')))
    | ~ l1_pre_topc(k13_yellow_6('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_40,c_93])).

tff(c_99,plain,
    ( ~ r2_hidden('#skF_6',u1_pre_topc(k13_yellow_6('#skF_4','#skF_5')))
    | ~ l1_pre_topc(k13_yellow_6('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_85,c_96])).

tff(c_101,plain,(
    ~ l1_pre_topc(k13_yellow_6('#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_99])).

tff(c_104,plain,
    ( ~ m4_yellow_6('#skF_5','#skF_4')
    | ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_12,c_101])).

tff(c_107,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_42,c_104])).

tff(c_109,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_107])).

tff(c_111,plain,(
    l1_pre_topc(k13_yellow_6('#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_99])).

tff(c_14,plain,(
    ! [A_11,B_12] :
      ( v1_pre_topc(k13_yellow_6(A_11,B_12))
      | ~ m4_yellow_6(B_12,A_11)
      | ~ l1_struct_0(A_11)
      | v2_struct_0(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_182,plain,(
    ! [A_117,B_118] :
      ( u1_pre_topc(k13_yellow_6(A_117,B_118)) = a_2_1_yellow_6(A_117,B_118)
      | ~ l1_pre_topc(k13_yellow_6(A_117,B_118))
      | ~ v1_pre_topc(k13_yellow_6(A_117,B_118))
      | ~ m4_yellow_6(B_118,A_117)
      | ~ l1_struct_0(A_117)
      | v2_struct_0(A_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_256,plain,(
    ! [A_128,B_129] :
      ( u1_pre_topc(k13_yellow_6(A_128,B_129)) = a_2_1_yellow_6(A_128,B_129)
      | ~ l1_pre_topc(k13_yellow_6(A_128,B_129))
      | ~ m4_yellow_6(B_129,A_128)
      | ~ l1_struct_0(A_128)
      | v2_struct_0(A_128) ) ),
    inference(resolution,[status(thm)],[c_14,c_182])).

tff(c_259,plain,
    ( u1_pre_topc(k13_yellow_6('#skF_4','#skF_5')) = a_2_1_yellow_6('#skF_4','#skF_5')
    | ~ m4_yellow_6('#skF_5','#skF_4')
    | ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_111,c_256])).

tff(c_265,plain,
    ( u1_pre_topc(k13_yellow_6('#skF_4','#skF_5')) = a_2_1_yellow_6('#skF_4','#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_42,c_259])).

tff(c_266,plain,(
    u1_pre_topc(k13_yellow_6('#skF_4','#skF_5')) = a_2_1_yellow_6('#skF_4','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_265])).

tff(c_110,plain,(
    ~ r2_hidden('#skF_6',u1_pre_topc(k13_yellow_6('#skF_4','#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_99])).

tff(c_271,plain,(
    ~ r2_hidden('#skF_6',a_2_1_yellow_6('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_266,c_110])).

tff(c_133,plain,(
    ! [A_112,B_113] :
      ( u1_struct_0(k13_yellow_6(A_112,B_113)) = u1_struct_0(A_112)
      | ~ l1_pre_topc(k13_yellow_6(A_112,B_113))
      | ~ v1_pre_topc(k13_yellow_6(A_112,B_113))
      | ~ m4_yellow_6(B_113,A_112)
      | ~ l1_struct_0(A_112)
      | v2_struct_0(A_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_139,plain,(
    ! [A_114,B_115] :
      ( u1_struct_0(k13_yellow_6(A_114,B_115)) = u1_struct_0(A_114)
      | ~ l1_pre_topc(k13_yellow_6(A_114,B_115))
      | ~ m4_yellow_6(B_115,A_114)
      | ~ l1_struct_0(A_114)
      | v2_struct_0(A_114) ) ),
    inference(resolution,[status(thm)],[c_14,c_133])).

tff(c_142,plain,
    ( u1_struct_0(k13_yellow_6('#skF_4','#skF_5')) = u1_struct_0('#skF_4')
    | ~ m4_yellow_6('#skF_5','#skF_4')
    | ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_111,c_139])).

tff(c_148,plain,
    ( u1_struct_0(k13_yellow_6('#skF_4','#skF_5')) = u1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_42,c_142])).

tff(c_149,plain,(
    u1_struct_0(k13_yellow_6('#skF_4','#skF_5')) = u1_struct_0('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_148])).

tff(c_152,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_149,c_40])).

tff(c_372,plain,(
    ! [D_149,B_150,C_151] :
      ( r2_hidden('#skF_2'(D_149,B_150,C_151,D_149),D_149)
      | r2_hidden(D_149,a_2_1_yellow_6(B_150,C_151))
      | ~ m1_subset_1(D_149,k1_zfmisc_1(u1_struct_0(B_150)))
      | ~ m4_yellow_6(C_151,B_150)
      | ~ l1_struct_0(B_150)
      | v2_struct_0(B_150) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_376,plain,(
    ! [C_151] :
      ( r2_hidden('#skF_2'('#skF_6','#skF_4',C_151,'#skF_6'),'#skF_6')
      | r2_hidden('#skF_6',a_2_1_yellow_6('#skF_4',C_151))
      | ~ m4_yellow_6(C_151,'#skF_4')
      | ~ l1_struct_0('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_152,c_372])).

tff(c_383,plain,(
    ! [C_151] :
      ( r2_hidden('#skF_2'('#skF_6','#skF_4',C_151,'#skF_6'),'#skF_6')
      | r2_hidden('#skF_6',a_2_1_yellow_6('#skF_4',C_151))
      | ~ m4_yellow_6(C_151,'#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_376])).

tff(c_384,plain,(
    ! [C_151] :
      ( r2_hidden('#skF_2'('#skF_6','#skF_4',C_151,'#skF_6'),'#skF_6')
      | r2_hidden('#skF_6',a_2_1_yellow_6('#skF_4',C_151))
      | ~ m4_yellow_6(C_151,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_383])).

tff(c_233,plain,(
    ! [D_123,B_124,C_125] :
      ( v4_orders_2('#skF_3'(D_123,B_124,C_125,D_123))
      | r2_hidden(D_123,a_2_1_yellow_6(B_124,C_125))
      | ~ m1_subset_1(D_123,k1_zfmisc_1(u1_struct_0(B_124)))
      | ~ m4_yellow_6(C_125,B_124)
      | ~ l1_struct_0(B_124)
      | v2_struct_0(B_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_237,plain,(
    ! [C_125] :
      ( v4_orders_2('#skF_3'('#skF_6','#skF_4',C_125,'#skF_6'))
      | r2_hidden('#skF_6',a_2_1_yellow_6('#skF_4',C_125))
      | ~ m4_yellow_6(C_125,'#skF_4')
      | ~ l1_struct_0('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_152,c_233])).

tff(c_244,plain,(
    ! [C_125] :
      ( v4_orders_2('#skF_3'('#skF_6','#skF_4',C_125,'#skF_6'))
      | r2_hidden('#skF_6',a_2_1_yellow_6('#skF_4',C_125))
      | ~ m4_yellow_6(C_125,'#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_237])).

tff(c_245,plain,(
    ! [C_125] :
      ( v4_orders_2('#skF_3'('#skF_6','#skF_4',C_125,'#skF_6'))
      | r2_hidden('#skF_6',a_2_1_yellow_6('#skF_4',C_125))
      | ~ m4_yellow_6(C_125,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_244])).

tff(c_278,plain,
    ( v4_orders_2('#skF_3'('#skF_6','#skF_4','#skF_5','#skF_6'))
    | ~ m4_yellow_6('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_245,c_271])).

tff(c_281,plain,(
    v4_orders_2('#skF_3'('#skF_6','#skF_4','#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_278])).

tff(c_336,plain,(
    ! [D_141,B_142,C_143] :
      ( v7_waybel_0('#skF_3'(D_141,B_142,C_143,D_141))
      | r2_hidden(D_141,a_2_1_yellow_6(B_142,C_143))
      | ~ m1_subset_1(D_141,k1_zfmisc_1(u1_struct_0(B_142)))
      | ~ m4_yellow_6(C_143,B_142)
      | ~ l1_struct_0(B_142)
      | v2_struct_0(B_142) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_340,plain,(
    ! [C_143] :
      ( v7_waybel_0('#skF_3'('#skF_6','#skF_4',C_143,'#skF_6'))
      | r2_hidden('#skF_6',a_2_1_yellow_6('#skF_4',C_143))
      | ~ m4_yellow_6(C_143,'#skF_4')
      | ~ l1_struct_0('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_152,c_336])).

tff(c_347,plain,(
    ! [C_143] :
      ( v7_waybel_0('#skF_3'('#skF_6','#skF_4',C_143,'#skF_6'))
      | r2_hidden('#skF_6',a_2_1_yellow_6('#skF_4',C_143))
      | ~ m4_yellow_6(C_143,'#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_340])).

tff(c_350,plain,(
    ! [C_144] :
      ( v7_waybel_0('#skF_3'('#skF_6','#skF_4',C_144,'#skF_6'))
      | r2_hidden('#skF_6',a_2_1_yellow_6('#skF_4',C_144))
      | ~ m4_yellow_6(C_144,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_347])).

tff(c_353,plain,
    ( v7_waybel_0('#skF_3'('#skF_6','#skF_4','#skF_5','#skF_6'))
    | ~ m4_yellow_6('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_350,c_271])).

tff(c_359,plain,(
    v7_waybel_0('#skF_3'('#skF_6','#skF_4','#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_353])).

tff(c_387,plain,(
    ! [D_153,B_154,C_155] :
      ( l1_waybel_0('#skF_3'(D_153,B_154,C_155,D_153),B_154)
      | r2_hidden(D_153,a_2_1_yellow_6(B_154,C_155))
      | ~ m1_subset_1(D_153,k1_zfmisc_1(u1_struct_0(B_154)))
      | ~ m4_yellow_6(C_155,B_154)
      | ~ l1_struct_0(B_154)
      | v2_struct_0(B_154) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_391,plain,(
    ! [C_155] :
      ( l1_waybel_0('#skF_3'('#skF_6','#skF_4',C_155,'#skF_6'),'#skF_4')
      | r2_hidden('#skF_6',a_2_1_yellow_6('#skF_4',C_155))
      | ~ m4_yellow_6(C_155,'#skF_4')
      | ~ l1_struct_0('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_152,c_387])).

tff(c_398,plain,(
    ! [C_155] :
      ( l1_waybel_0('#skF_3'('#skF_6','#skF_4',C_155,'#skF_6'),'#skF_4')
      | r2_hidden('#skF_6',a_2_1_yellow_6('#skF_4',C_155))
      | ~ m4_yellow_6(C_155,'#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_391])).

tff(c_402,plain,(
    ! [C_156] :
      ( l1_waybel_0('#skF_3'('#skF_6','#skF_4',C_156,'#skF_6'),'#skF_4')
      | r2_hidden('#skF_6',a_2_1_yellow_6('#skF_4',C_156))
      | ~ m4_yellow_6(C_156,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_398])).

tff(c_405,plain,
    ( l1_waybel_0('#skF_3'('#skF_6','#skF_4','#skF_5','#skF_6'),'#skF_4')
    | ~ m4_yellow_6('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_402,c_271])).

tff(c_411,plain,(
    l1_waybel_0('#skF_3'('#skF_6','#skF_4','#skF_5','#skF_6'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_405])).

tff(c_30,plain,(
    ! [D_36,B_14,C_15] :
      ( m1_subset_1('#skF_2'(D_36,B_14,C_15,D_36),u1_struct_0(B_14))
      | r2_hidden(D_36,a_2_1_yellow_6(B_14,C_15))
      | ~ m1_subset_1(D_36,k1_zfmisc_1(u1_struct_0(B_14)))
      | ~ m4_yellow_6(C_15,B_14)
      | ~ l1_struct_0(B_14)
      | v2_struct_0(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_513,plain,(
    ! [D_186,B_187,C_188] :
      ( r2_hidden(k4_tarski('#skF_3'(D_186,B_187,C_188,D_186),'#skF_2'(D_186,B_187,C_188,D_186)),C_188)
      | r2_hidden(D_186,a_2_1_yellow_6(B_187,C_188))
      | ~ m1_subset_1(D_186,k1_zfmisc_1(u1_struct_0(B_187)))
      | ~ m4_yellow_6(C_188,B_187)
      | ~ l1_struct_0(B_187)
      | v2_struct_0(B_187) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_84,plain,(
    ! [E_93,D_91] :
      ( v3_pre_topc('#skF_6',k13_yellow_6('#skF_4','#skF_5'))
      | r1_waybel_0('#skF_4',E_93,'#skF_6')
      | ~ r2_hidden(k4_tarski(E_93,D_91),'#skF_5')
      | ~ l1_waybel_0(E_93,'#skF_4')
      | ~ v7_waybel_0(E_93)
      | ~ v4_orders_2(E_93)
      | v2_struct_0(E_93)
      | ~ r2_hidden(D_91,'#skF_6')
      | ~ m1_subset_1(D_91,u1_struct_0('#skF_4')) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_511,plain,(
    ! [E_93,D_91] :
      ( r1_waybel_0('#skF_4',E_93,'#skF_6')
      | ~ r2_hidden(k4_tarski(E_93,D_91),'#skF_5')
      | ~ l1_waybel_0(E_93,'#skF_4')
      | ~ v7_waybel_0(E_93)
      | ~ v4_orders_2(E_93)
      | v2_struct_0(E_93)
      | ~ r2_hidden(D_91,'#skF_6')
      | ~ m1_subset_1(D_91,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_85,c_84])).

tff(c_840,plain,(
    ! [D_276,B_277] :
      ( r1_waybel_0('#skF_4','#skF_3'(D_276,B_277,'#skF_5',D_276),'#skF_6')
      | ~ l1_waybel_0('#skF_3'(D_276,B_277,'#skF_5',D_276),'#skF_4')
      | ~ v7_waybel_0('#skF_3'(D_276,B_277,'#skF_5',D_276))
      | ~ v4_orders_2('#skF_3'(D_276,B_277,'#skF_5',D_276))
      | v2_struct_0('#skF_3'(D_276,B_277,'#skF_5',D_276))
      | ~ r2_hidden('#skF_2'(D_276,B_277,'#skF_5',D_276),'#skF_6')
      | ~ m1_subset_1('#skF_2'(D_276,B_277,'#skF_5',D_276),u1_struct_0('#skF_4'))
      | r2_hidden(D_276,a_2_1_yellow_6(B_277,'#skF_5'))
      | ~ m1_subset_1(D_276,k1_zfmisc_1(u1_struct_0(B_277)))
      | ~ m4_yellow_6('#skF_5',B_277)
      | ~ l1_struct_0(B_277)
      | v2_struct_0(B_277) ) ),
    inference(resolution,[status(thm)],[c_513,c_511])).

tff(c_848,plain,(
    ! [D_36] :
      ( r1_waybel_0('#skF_4','#skF_3'(D_36,'#skF_4','#skF_5',D_36),'#skF_6')
      | ~ l1_waybel_0('#skF_3'(D_36,'#skF_4','#skF_5',D_36),'#skF_4')
      | ~ v7_waybel_0('#skF_3'(D_36,'#skF_4','#skF_5',D_36))
      | ~ v4_orders_2('#skF_3'(D_36,'#skF_4','#skF_5',D_36))
      | v2_struct_0('#skF_3'(D_36,'#skF_4','#skF_5',D_36))
      | ~ r2_hidden('#skF_2'(D_36,'#skF_4','#skF_5',D_36),'#skF_6')
      | r2_hidden(D_36,a_2_1_yellow_6('#skF_4','#skF_5'))
      | ~ m1_subset_1(D_36,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m4_yellow_6('#skF_5','#skF_4')
      | ~ l1_struct_0('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_30,c_840])).

tff(c_858,plain,(
    ! [D_36] :
      ( r1_waybel_0('#skF_4','#skF_3'(D_36,'#skF_4','#skF_5',D_36),'#skF_6')
      | ~ l1_waybel_0('#skF_3'(D_36,'#skF_4','#skF_5',D_36),'#skF_4')
      | ~ v7_waybel_0('#skF_3'(D_36,'#skF_4','#skF_5',D_36))
      | ~ v4_orders_2('#skF_3'(D_36,'#skF_4','#skF_5',D_36))
      | v2_struct_0('#skF_3'(D_36,'#skF_4','#skF_5',D_36))
      | ~ r2_hidden('#skF_2'(D_36,'#skF_4','#skF_5',D_36),'#skF_6')
      | r2_hidden(D_36,a_2_1_yellow_6('#skF_4','#skF_5'))
      | ~ m1_subset_1(D_36,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_42,c_848])).

tff(c_887,plain,(
    ! [D_289] :
      ( r1_waybel_0('#skF_4','#skF_3'(D_289,'#skF_4','#skF_5',D_289),'#skF_6')
      | ~ l1_waybel_0('#skF_3'(D_289,'#skF_4','#skF_5',D_289),'#skF_4')
      | ~ v7_waybel_0('#skF_3'(D_289,'#skF_4','#skF_5',D_289))
      | ~ v4_orders_2('#skF_3'(D_289,'#skF_4','#skF_5',D_289))
      | v2_struct_0('#skF_3'(D_289,'#skF_4','#skF_5',D_289))
      | ~ r2_hidden('#skF_2'(D_289,'#skF_4','#skF_5',D_289),'#skF_6')
      | r2_hidden(D_289,a_2_1_yellow_6('#skF_4','#skF_5'))
      | ~ m1_subset_1(D_289,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_858])).

tff(c_892,plain,
    ( r1_waybel_0('#skF_4','#skF_3'('#skF_6','#skF_4','#skF_5','#skF_6'),'#skF_6')
    | ~ l1_waybel_0('#skF_3'('#skF_6','#skF_4','#skF_5','#skF_6'),'#skF_4')
    | ~ v7_waybel_0('#skF_3'('#skF_6','#skF_4','#skF_5','#skF_6'))
    | ~ v4_orders_2('#skF_3'('#skF_6','#skF_4','#skF_5','#skF_6'))
    | v2_struct_0('#skF_3'('#skF_6','#skF_4','#skF_5','#skF_6'))
    | ~ r2_hidden('#skF_2'('#skF_6','#skF_4','#skF_5','#skF_6'),'#skF_6')
    | r2_hidden('#skF_6',a_2_1_yellow_6('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_152,c_887])).

tff(c_902,plain,
    ( r1_waybel_0('#skF_4','#skF_3'('#skF_6','#skF_4','#skF_5','#skF_6'),'#skF_6')
    | v2_struct_0('#skF_3'('#skF_6','#skF_4','#skF_5','#skF_6'))
    | ~ r2_hidden('#skF_2'('#skF_6','#skF_4','#skF_5','#skF_6'),'#skF_6')
    | r2_hidden('#skF_6',a_2_1_yellow_6('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_281,c_359,c_411,c_892])).

tff(c_903,plain,
    ( r1_waybel_0('#skF_4','#skF_3'('#skF_6','#skF_4','#skF_5','#skF_6'),'#skF_6')
    | v2_struct_0('#skF_3'('#skF_6','#skF_4','#skF_5','#skF_6'))
    | ~ r2_hidden('#skF_2'('#skF_6','#skF_4','#skF_5','#skF_6'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_271,c_902])).

tff(c_908,plain,(
    ~ r2_hidden('#skF_2'('#skF_6','#skF_4','#skF_5','#skF_6'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_903])).

tff(c_911,plain,
    ( r2_hidden('#skF_6',a_2_1_yellow_6('#skF_4','#skF_5'))
    | ~ m4_yellow_6('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_384,c_908])).

tff(c_914,plain,(
    r2_hidden('#skF_6',a_2_1_yellow_6('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_911])).

tff(c_916,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_271,c_914])).

tff(c_917,plain,
    ( v2_struct_0('#skF_3'('#skF_6','#skF_4','#skF_5','#skF_6'))
    | r1_waybel_0('#skF_4','#skF_3'('#skF_6','#skF_4','#skF_5','#skF_6'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_903])).

tff(c_919,plain,(
    r1_waybel_0('#skF_4','#skF_3'('#skF_6','#skF_4','#skF_5','#skF_6'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_917])).

tff(c_16,plain,(
    ! [B_14,D_36,C_15] :
      ( ~ r1_waybel_0(B_14,'#skF_3'(D_36,B_14,C_15,D_36),D_36)
      | r2_hidden(D_36,a_2_1_yellow_6(B_14,C_15))
      | ~ m1_subset_1(D_36,k1_zfmisc_1(u1_struct_0(B_14)))
      | ~ m4_yellow_6(C_15,B_14)
      | ~ l1_struct_0(B_14)
      | v2_struct_0(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_921,plain,
    ( r2_hidden('#skF_6',a_2_1_yellow_6('#skF_4','#skF_5'))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ m4_yellow_6('#skF_5','#skF_4')
    | ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_919,c_16])).

tff(c_924,plain,
    ( r2_hidden('#skF_6',a_2_1_yellow_6('#skF_4','#skF_5'))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_42,c_152,c_921])).

tff(c_926,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_271,c_924])).

tff(c_927,plain,(
    v2_struct_0('#skF_3'('#skF_6','#skF_4','#skF_5','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_917])).

tff(c_26,plain,(
    ! [D_36,B_14,C_15] :
      ( ~ v2_struct_0('#skF_3'(D_36,B_14,C_15,D_36))
      | r2_hidden(D_36,a_2_1_yellow_6(B_14,C_15))
      | ~ m1_subset_1(D_36,k1_zfmisc_1(u1_struct_0(B_14)))
      | ~ m4_yellow_6(C_15,B_14)
      | ~ l1_struct_0(B_14)
      | v2_struct_0(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_938,plain,
    ( r2_hidden('#skF_6',a_2_1_yellow_6('#skF_4','#skF_5'))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ m4_yellow_6('#skF_5','#skF_4')
    | ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_927,c_26])).

tff(c_941,plain,
    ( r2_hidden('#skF_6',a_2_1_yellow_6('#skF_4','#skF_5'))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_42,c_152,c_938])).

tff(c_943,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_271,c_941])).

tff(c_945,plain,(
    v3_pre_topc('#skF_6',k13_yellow_6('#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_50,plain,
    ( ~ r1_waybel_0('#skF_4','#skF_8','#skF_6')
    | ~ v3_pre_topc('#skF_6',k13_yellow_6('#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_955,plain,(
    ~ r1_waybel_0('#skF_4','#skF_8','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_945,c_50])).

tff(c_974,plain,(
    ! [B_305,A_306] :
      ( r2_hidden(B_305,u1_pre_topc(A_306))
      | ~ v3_pre_topc(B_305,A_306)
      | ~ m1_subset_1(B_305,k1_zfmisc_1(u1_struct_0(A_306)))
      | ~ l1_pre_topc(A_306) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_977,plain,
    ( r2_hidden('#skF_6',u1_pre_topc(k13_yellow_6('#skF_4','#skF_5')))
    | ~ v3_pre_topc('#skF_6',k13_yellow_6('#skF_4','#skF_5'))
    | ~ l1_pre_topc(k13_yellow_6('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_40,c_974])).

tff(c_980,plain,
    ( r2_hidden('#skF_6',u1_pre_topc(k13_yellow_6('#skF_4','#skF_5')))
    | ~ l1_pre_topc(k13_yellow_6('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_945,c_977])).

tff(c_981,plain,(
    ~ l1_pre_topc(k13_yellow_6('#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_980])).

tff(c_985,plain,
    ( ~ m4_yellow_6('#skF_5','#skF_4')
    | ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_12,c_981])).

tff(c_988,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_42,c_985])).

tff(c_990,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_988])).

tff(c_992,plain,(
    l1_pre_topc(k13_yellow_6('#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_980])).

tff(c_1043,plain,(
    ! [A_320,B_321] :
      ( u1_pre_topc(k13_yellow_6(A_320,B_321)) = a_2_1_yellow_6(A_320,B_321)
      | ~ l1_pre_topc(k13_yellow_6(A_320,B_321))
      | ~ v1_pre_topc(k13_yellow_6(A_320,B_321))
      | ~ m4_yellow_6(B_321,A_320)
      | ~ l1_struct_0(A_320)
      | v2_struct_0(A_320) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1106,plain,(
    ! [A_330,B_331] :
      ( u1_pre_topc(k13_yellow_6(A_330,B_331)) = a_2_1_yellow_6(A_330,B_331)
      | ~ l1_pre_topc(k13_yellow_6(A_330,B_331))
      | ~ m4_yellow_6(B_331,A_330)
      | ~ l1_struct_0(A_330)
      | v2_struct_0(A_330) ) ),
    inference(resolution,[status(thm)],[c_14,c_1043])).

tff(c_1109,plain,
    ( u1_pre_topc(k13_yellow_6('#skF_4','#skF_5')) = a_2_1_yellow_6('#skF_4','#skF_5')
    | ~ m4_yellow_6('#skF_5','#skF_4')
    | ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_992,c_1106])).

tff(c_1115,plain,
    ( u1_pre_topc(k13_yellow_6('#skF_4','#skF_5')) = a_2_1_yellow_6('#skF_4','#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_42,c_1109])).

tff(c_1116,plain,(
    u1_pre_topc(k13_yellow_6('#skF_4','#skF_5')) = a_2_1_yellow_6('#skF_4','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_1115])).

tff(c_991,plain,(
    r2_hidden('#skF_6',u1_pre_topc(k13_yellow_6('#skF_4','#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_980])).

tff(c_1120,plain,(
    r2_hidden('#skF_6',a_2_1_yellow_6('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1116,c_991])).

tff(c_64,plain,
    ( m1_subset_1('#skF_7',u1_struct_0('#skF_4'))
    | ~ v3_pre_topc('#skF_6',k13_yellow_6('#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_957,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_945,c_64])).

tff(c_62,plain,
    ( r2_hidden('#skF_7','#skF_6')
    | ~ v3_pre_topc('#skF_6',k13_yellow_6('#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_953,plain,(
    r2_hidden('#skF_7','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_945,c_62])).

tff(c_34,plain,(
    ! [A_13,B_14,C_15] :
      ( '#skF_1'(A_13,B_14,C_15) = A_13
      | ~ r2_hidden(A_13,a_2_1_yellow_6(B_14,C_15))
      | ~ m4_yellow_6(C_15,B_14)
      | ~ l1_struct_0(B_14)
      | v2_struct_0(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_1128,plain,
    ( '#skF_1'('#skF_6','#skF_4','#skF_5') = '#skF_6'
    | ~ m4_yellow_6('#skF_5','#skF_4')
    | ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_1120,c_34])).

tff(c_1131,plain,
    ( '#skF_1'('#skF_6','#skF_4','#skF_5') = '#skF_6'
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_42,c_1128])).

tff(c_1132,plain,(
    '#skF_1'('#skF_6','#skF_4','#skF_5') = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_1131])).

tff(c_54,plain,
    ( l1_waybel_0('#skF_8','#skF_4')
    | ~ v3_pre_topc('#skF_6',k13_yellow_6('#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_951,plain,(
    l1_waybel_0('#skF_8','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_945,c_54])).

tff(c_944,plain,(
    ~ v2_struct_0('#skF_8') ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_58,plain,
    ( v4_orders_2('#skF_8')
    | ~ v3_pre_topc('#skF_6',k13_yellow_6('#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_949,plain,(
    v4_orders_2('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_945,c_58])).

tff(c_56,plain,
    ( v7_waybel_0('#skF_8')
    | ~ v3_pre_topc('#skF_6',k13_yellow_6('#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_947,plain,(
    v7_waybel_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_945,c_56])).

tff(c_52,plain,
    ( r2_hidden(k4_tarski('#skF_8','#skF_7'),'#skF_5')
    | ~ v3_pre_topc('#skF_6',k13_yellow_6('#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_959,plain,(
    r2_hidden(k4_tarski('#skF_8','#skF_7'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_945,c_52])).

tff(c_1473,plain,(
    ! [F_401,E_403,B_400,A_402,C_404] :
      ( r1_waybel_0(B_400,F_401,'#skF_1'(A_402,B_400,C_404))
      | ~ r2_hidden(k4_tarski(F_401,E_403),C_404)
      | ~ l1_waybel_0(F_401,B_400)
      | ~ v7_waybel_0(F_401)
      | ~ v4_orders_2(F_401)
      | v2_struct_0(F_401)
      | ~ r2_hidden(E_403,'#skF_1'(A_402,B_400,C_404))
      | ~ m1_subset_1(E_403,u1_struct_0(B_400))
      | ~ r2_hidden(A_402,a_2_1_yellow_6(B_400,C_404))
      | ~ m4_yellow_6(C_404,B_400)
      | ~ l1_struct_0(B_400)
      | v2_struct_0(B_400) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_1480,plain,(
    ! [B_400,A_402] :
      ( r1_waybel_0(B_400,'#skF_8','#skF_1'(A_402,B_400,'#skF_5'))
      | ~ l1_waybel_0('#skF_8',B_400)
      | ~ v7_waybel_0('#skF_8')
      | ~ v4_orders_2('#skF_8')
      | v2_struct_0('#skF_8')
      | ~ r2_hidden('#skF_7','#skF_1'(A_402,B_400,'#skF_5'))
      | ~ m1_subset_1('#skF_7',u1_struct_0(B_400))
      | ~ r2_hidden(A_402,a_2_1_yellow_6(B_400,'#skF_5'))
      | ~ m4_yellow_6('#skF_5',B_400)
      | ~ l1_struct_0(B_400)
      | v2_struct_0(B_400) ) ),
    inference(resolution,[status(thm)],[c_959,c_1473])).

tff(c_1485,plain,(
    ! [B_400,A_402] :
      ( r1_waybel_0(B_400,'#skF_8','#skF_1'(A_402,B_400,'#skF_5'))
      | ~ l1_waybel_0('#skF_8',B_400)
      | v2_struct_0('#skF_8')
      | ~ r2_hidden('#skF_7','#skF_1'(A_402,B_400,'#skF_5'))
      | ~ m1_subset_1('#skF_7',u1_struct_0(B_400))
      | ~ r2_hidden(A_402,a_2_1_yellow_6(B_400,'#skF_5'))
      | ~ m4_yellow_6('#skF_5',B_400)
      | ~ l1_struct_0(B_400)
      | v2_struct_0(B_400) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_949,c_947,c_1480])).

tff(c_1487,plain,(
    ! [B_405,A_406] :
      ( r1_waybel_0(B_405,'#skF_8','#skF_1'(A_406,B_405,'#skF_5'))
      | ~ l1_waybel_0('#skF_8',B_405)
      | ~ r2_hidden('#skF_7','#skF_1'(A_406,B_405,'#skF_5'))
      | ~ m1_subset_1('#skF_7',u1_struct_0(B_405))
      | ~ r2_hidden(A_406,a_2_1_yellow_6(B_405,'#skF_5'))
      | ~ m4_yellow_6('#skF_5',B_405)
      | ~ l1_struct_0(B_405)
      | v2_struct_0(B_405) ) ),
    inference(negUnitSimplification,[status(thm)],[c_944,c_1485])).

tff(c_1490,plain,
    ( r1_waybel_0('#skF_4','#skF_8','#skF_6')
    | ~ l1_waybel_0('#skF_8','#skF_4')
    | ~ r2_hidden('#skF_7','#skF_1'('#skF_6','#skF_4','#skF_5'))
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_4'))
    | ~ r2_hidden('#skF_6',a_2_1_yellow_6('#skF_4','#skF_5'))
    | ~ m4_yellow_6('#skF_5','#skF_4')
    | ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1132,c_1487])).

tff(c_1492,plain,
    ( r1_waybel_0('#skF_4','#skF_8','#skF_6')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_42,c_1120,c_957,c_953,c_1132,c_951,c_1490])).

tff(c_1494,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_955,c_1492])).

%------------------------------------------------------------------------------
