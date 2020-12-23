%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1617+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:08 EST 2020

% Result     : Theorem 5.40s
% Output     : CNFRefutation 5.85s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 283 expanded)
%              Number of leaves         :   39 ( 112 expanded)
%              Depth                    :   15
%              Number of atoms          :  223 ( 645 expanded)
%              Number of equality atoms :   38 ( 122 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v1_tops_2 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v8_relat_2 > v4_relat_2 > v2_pre_topc > v1_relat_2 > v1_orders_2 > l1_pre_topc > l1_orders_2 > k2_zfmisc_1 > g1_orders_2 > #nlpp > u1_struct_0 > u1_pre_topc > u1_orders_2 > k2_yellow_1 > k1_zfmisc_1 > k1_yellow_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_orders_2,type,(
    v1_orders_2: $i > $o )).

tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(v1_tops_2,type,(
    v1_tops_2: ( $i * $i ) > $o )).

tff(k2_yellow_1,type,(
    k2_yellow_1: $i > $i )).

tff(v1_relat_2,type,(
    v1_relat_2: $i > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(v8_relat_2,type,(
    v8_relat_2: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(g1_orders_2,type,(
    g1_orders_2: ( $i * $i ) > $i )).

tff(v4_relat_2,type,(
    v4_relat_2: $i > $o )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(k1_yellow_1,type,(
    k1_yellow_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_orders_2,type,(
    u1_orders_2: $i > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_76,axiom,(
    ! [A] :
      ( v1_orders_2(k2_yellow_1(A))
      & l1_orders_2(k2_yellow_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_yellow_1)).

tff(f_30,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v1_orders_2(A)
       => A = g1_orders_2(u1_struct_0(A),u1_orders_2(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',abstractness_v1_orders_2)).

tff(f_72,axiom,(
    ! [A] :
      ( v1_relat_2(k1_yellow_1(A))
      & v4_relat_2(k1_yellow_1(A))
      & v8_relat_2(k1_yellow_1(A))
      & v1_partfun1(k1_yellow_1(A),A)
      & m1_subset_1(k1_yellow_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_yellow_1)).

tff(f_46,axiom,(
    ! [A] : k2_yellow_1(A) = g1_orders_2(A,k1_yellow_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_yellow_1)).

tff(f_89,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A)))
     => ! [C,D] :
          ( g1_orders_2(A,B) = g1_orders_2(C,D)
         => ( A = C
            & B = D ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',free_g1_orders_2)).

tff(f_93,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_111,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
           => ( v1_tops_2(B,A)
            <=> m1_subset_1(B,k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(A))))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_yellow_1)).

tff(f_44,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
         => ( v1_tops_2(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( r2_hidden(C,B)
                 => v3_pre_topc(C,A) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tops_2)).

tff(f_53,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_99,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_62,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_pre_topc(B,A)
          <=> r2_hidden(B,u1_pre_topc(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_pre_topc)).

tff(c_36,plain,(
    ! [A_22] : l1_orders_2(k2_yellow_1(A_22)) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_34,plain,(
    ! [A_22] : v1_orders_2(k2_yellow_1(A_22)) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_2,plain,(
    ! [A_1] :
      ( g1_orders_2(u1_struct_0(A_1),u1_orders_2(A_1)) = A_1
      | ~ v1_orders_2(A_1)
      | ~ l1_orders_2(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_32,plain,(
    ! [A_21] : m1_subset_1(k1_yellow_1(A_21),k1_zfmisc_1(k2_zfmisc_1(A_21,A_21))) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_12,plain,(
    ! [A_12] : g1_orders_2(A_12,k1_yellow_1(A_12)) = k2_yellow_1(A_12) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_962,plain,(
    ! [D_199,B_200,C_201,A_202] :
      ( D_199 = B_200
      | g1_orders_2(C_201,D_199) != g1_orders_2(A_202,B_200)
      | ~ m1_subset_1(B_200,k1_zfmisc_1(k2_zfmisc_1(A_202,A_202))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_970,plain,(
    ! [A_12,D_199,C_201] :
      ( k1_yellow_1(A_12) = D_199
      | k2_yellow_1(A_12) != g1_orders_2(C_201,D_199)
      | ~ m1_subset_1(k1_yellow_1(A_12),k1_zfmisc_1(k2_zfmisc_1(A_12,A_12))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_962])).

tff(c_973,plain,(
    ! [A_203,D_204,C_205] :
      ( k1_yellow_1(A_203) = D_204
      | k2_yellow_1(A_203) != g1_orders_2(C_205,D_204) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_970])).

tff(c_976,plain,(
    ! [A_1,A_203] :
      ( u1_orders_2(A_1) = k1_yellow_1(A_203)
      | k2_yellow_1(A_203) != A_1
      | ~ v1_orders_2(A_1)
      | ~ l1_orders_2(A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_973])).

tff(c_988,plain,(
    ! [A_203] :
      ( u1_orders_2(k2_yellow_1(A_203)) = k1_yellow_1(A_203)
      | ~ v1_orders_2(k2_yellow_1(A_203))
      | ~ l1_orders_2(k2_yellow_1(A_203)) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_976])).

tff(c_993,plain,(
    ! [A_210] : u1_orders_2(k2_yellow_1(A_210)) = k1_yellow_1(A_210) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_988])).

tff(c_999,plain,(
    ! [A_210] :
      ( g1_orders_2(u1_struct_0(k2_yellow_1(A_210)),k1_yellow_1(A_210)) = k2_yellow_1(A_210)
      | ~ v1_orders_2(k2_yellow_1(A_210))
      | ~ l1_orders_2(k2_yellow_1(A_210)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_993,c_2])).

tff(c_1005,plain,(
    ! [A_210] : g1_orders_2(u1_struct_0(k2_yellow_1(A_210)),k1_yellow_1(A_210)) = k2_yellow_1(A_210) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_999])).

tff(c_1182,plain,(
    ! [C_233,A_234,D_235,B_236] :
      ( C_233 = A_234
      | g1_orders_2(C_233,D_235) != g1_orders_2(A_234,B_236)
      | ~ m1_subset_1(B_236,k1_zfmisc_1(k2_zfmisc_1(A_234,A_234))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_1194,plain,(
    ! [C_233,A_12,D_235] :
      ( C_233 = A_12
      | k2_yellow_1(A_12) != g1_orders_2(C_233,D_235)
      | ~ m1_subset_1(k1_yellow_1(A_12),k1_zfmisc_1(k2_zfmisc_1(A_12,A_12))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_1182])).

tff(c_1197,plain,(
    ! [C_237,A_238,D_239] :
      ( C_237 = A_238
      | k2_yellow_1(A_238) != g1_orders_2(C_237,D_239) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_1194])).

tff(c_1200,plain,(
    ! [A_210,A_238] :
      ( u1_struct_0(k2_yellow_1(A_210)) = A_238
      | k2_yellow_1(A_238) != k2_yellow_1(A_210) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1005,c_1197])).

tff(c_1214,plain,(
    ! [A_210] : u1_struct_0(k2_yellow_1(A_210)) = A_210 ),
    inference(reflexivity,[status(thm),theory(equality)],[c_1200])).

tff(c_46,plain,(
    ! [A_30,B_31] :
      ( m1_subset_1(A_30,k1_zfmisc_1(B_31))
      | ~ r1_tarski(A_30,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_56,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc('#skF_3')))))
    | ~ v1_tops_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_106,plain,(
    ~ v1_tops_2('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_52,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_50,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_197,plain,(
    ! [C_78,A_79,D_80,B_81] :
      ( C_78 = A_79
      | g1_orders_2(C_78,D_80) != g1_orders_2(A_79,B_81)
      | ~ m1_subset_1(B_81,k1_zfmisc_1(k2_zfmisc_1(A_79,A_79))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_205,plain,(
    ! [C_78,A_12,D_80] :
      ( C_78 = A_12
      | k2_yellow_1(A_12) != g1_orders_2(C_78,D_80)
      | ~ m1_subset_1(k1_yellow_1(A_12),k1_zfmisc_1(k2_zfmisc_1(A_12,A_12))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_197])).

tff(c_208,plain,(
    ! [C_82,A_83,D_84] :
      ( C_82 = A_83
      | k2_yellow_1(A_83) != g1_orders_2(C_82,D_84) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_205])).

tff(c_211,plain,(
    ! [A_1,A_83] :
      ( u1_struct_0(A_1) = A_83
      | k2_yellow_1(A_83) != A_1
      | ~ v1_orders_2(A_1)
      | ~ l1_orders_2(A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_208])).

tff(c_235,plain,(
    ! [A_83] :
      ( u1_struct_0(k2_yellow_1(A_83)) = A_83
      | ~ v1_orders_2(k2_yellow_1(A_83))
      | ~ l1_orders_2(k2_yellow_1(A_83)) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_211])).

tff(c_237,plain,(
    ! [A_83] : u1_struct_0(k2_yellow_1(A_83)) = A_83 ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_235])).

tff(c_62,plain,
    ( v1_tops_2('#skF_4','#skF_3')
    | m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc('#skF_3'))))) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_113,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc('#skF_3'))))) ),
    inference(negUnitSimplification,[status(thm)],[c_106,c_62])).

tff(c_44,plain,(
    ! [A_30,B_31] :
      ( r1_tarski(A_30,B_31)
      | ~ m1_subset_1(A_30,k1_zfmisc_1(B_31)) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_117,plain,(
    r1_tarski('#skF_4',u1_struct_0(k2_yellow_1(u1_pre_topc('#skF_3')))) ),
    inference(resolution,[status(thm)],[c_113,c_44])).

tff(c_240,plain,(
    r1_tarski('#skF_4',u1_pre_topc('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_237,c_117])).

tff(c_674,plain,(
    ! [A_158,B_159] :
      ( r2_hidden('#skF_1'(A_158,B_159),B_159)
      | v1_tops_2(B_159,A_158)
      | ~ m1_subset_1(B_159,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_158))))
      | ~ l1_pre_topc(A_158) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_689,plain,
    ( r2_hidden('#skF_1'('#skF_3','#skF_4'),'#skF_4')
    | v1_tops_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_674])).

tff(c_696,plain,
    ( r2_hidden('#skF_1'('#skF_3','#skF_4'),'#skF_4')
    | v1_tops_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_689])).

tff(c_697,plain,(
    r2_hidden('#skF_1'('#skF_3','#skF_4'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_106,c_696])).

tff(c_14,plain,(
    ! [C_17,B_14,A_13] :
      ( r2_hidden(C_17,B_14)
      | ~ r2_hidden(C_17,A_13)
      | ~ r1_tarski(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_732,plain,(
    ! [B_161] :
      ( r2_hidden('#skF_1'('#skF_3','#skF_4'),B_161)
      | ~ r1_tarski('#skF_4',B_161) ) ),
    inference(resolution,[status(thm)],[c_697,c_14])).

tff(c_118,plain,(
    ! [A_59,C_60,B_61] :
      ( m1_subset_1(A_59,C_60)
      | ~ m1_subset_1(B_61,k1_zfmisc_1(C_60))
      | ~ r2_hidden(A_59,B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_133,plain,(
    ! [A_59] :
      ( m1_subset_1(A_59,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ r2_hidden(A_59,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_50,c_118])).

tff(c_367,plain,(
    ! [B_111,A_112] :
      ( v3_pre_topc(B_111,A_112)
      | ~ r2_hidden(B_111,u1_pre_topc(A_112))
      | ~ m1_subset_1(B_111,k1_zfmisc_1(u1_struct_0(A_112)))
      | ~ l1_pre_topc(A_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_380,plain,(
    ! [A_59] :
      ( v3_pre_topc(A_59,'#skF_3')
      | ~ r2_hidden(A_59,u1_pre_topc('#skF_3'))
      | ~ l1_pre_topc('#skF_3')
      | ~ r2_hidden(A_59,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_133,c_367])).

tff(c_389,plain,(
    ! [A_59] :
      ( v3_pre_topc(A_59,'#skF_3')
      | ~ r2_hidden(A_59,u1_pre_topc('#skF_3'))
      | ~ r2_hidden(A_59,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_380])).

tff(c_741,plain,
    ( v3_pre_topc('#skF_1'('#skF_3','#skF_4'),'#skF_3')
    | ~ r2_hidden('#skF_1'('#skF_3','#skF_4'),'#skF_4')
    | ~ r1_tarski('#skF_4',u1_pre_topc('#skF_3')) ),
    inference(resolution,[status(thm)],[c_732,c_389])).

tff(c_769,plain,(
    v3_pre_topc('#skF_1'('#skF_3','#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_240,c_697,c_741])).

tff(c_6,plain,(
    ! [A_2,B_8] :
      ( ~ v3_pre_topc('#skF_1'(A_2,B_8),A_2)
      | v1_tops_2(B_8,A_2)
      | ~ m1_subset_1(B_8,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_2))))
      | ~ l1_pre_topc(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_796,plain,
    ( v1_tops_2('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3'))))
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_769,c_6])).

tff(c_799,plain,(
    v1_tops_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_796])).

tff(c_801,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_106,c_799])).

tff(c_802,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc('#skF_3'))))) ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_807,plain,(
    ~ r1_tarski('#skF_4',u1_struct_0(k2_yellow_1(u1_pre_topc('#skF_3')))) ),
    inference(resolution,[status(thm)],[c_46,c_802])).

tff(c_1219,plain,(
    ~ r1_tarski('#skF_4',u1_pre_topc('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1214,c_807])).

tff(c_95,plain,(
    ! [A_51,B_52] :
      ( r2_hidden('#skF_2'(A_51,B_52),A_51)
      | r1_tarski(A_51,B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_16,plain,(
    ! [A_13,B_14] :
      ( ~ r2_hidden('#skF_2'(A_13,B_14),B_14)
      | r1_tarski(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_100,plain,(
    ! [A_51] : r1_tarski(A_51,A_51) ),
    inference(resolution,[status(thm)],[c_95,c_16])).

tff(c_18,plain,(
    ! [A_13,B_14] :
      ( r2_hidden('#skF_2'(A_13,B_14),A_13)
      | r1_tarski(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_102,plain,(
    ! [C_54,B_55,A_56] :
      ( r2_hidden(C_54,B_55)
      | ~ r2_hidden(C_54,A_56)
      | ~ r1_tarski(A_56,B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_105,plain,(
    ! [A_13,B_14,B_55] :
      ( r2_hidden('#skF_2'(A_13,B_14),B_55)
      | ~ r1_tarski(A_13,B_55)
      | r1_tarski(A_13,B_14) ) ),
    inference(resolution,[status(thm)],[c_18,c_102])).

tff(c_803,plain,(
    v1_tops_2('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_825,plain,(
    ! [A_167,C_168,B_169] :
      ( m1_subset_1(A_167,C_168)
      | ~ m1_subset_1(B_169,k1_zfmisc_1(C_168))
      | ~ r2_hidden(A_167,B_169) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_837,plain,(
    ! [A_167] :
      ( m1_subset_1(A_167,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ r2_hidden(A_167,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_50,c_825])).

tff(c_1575,plain,(
    ! [C_297,A_298,B_299] :
      ( v3_pre_topc(C_297,A_298)
      | ~ r2_hidden(C_297,B_299)
      | ~ m1_subset_1(C_297,k1_zfmisc_1(u1_struct_0(A_298)))
      | ~ v1_tops_2(B_299,A_298)
      | ~ m1_subset_1(B_299,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_298))))
      | ~ l1_pre_topc(A_298) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_2638,plain,(
    ! [A_419,B_420,A_421] :
      ( v3_pre_topc('#skF_2'(A_419,B_420),A_421)
      | ~ m1_subset_1('#skF_2'(A_419,B_420),k1_zfmisc_1(u1_struct_0(A_421)))
      | ~ v1_tops_2(A_419,A_421)
      | ~ m1_subset_1(A_419,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_421))))
      | ~ l1_pre_topc(A_421)
      | r1_tarski(A_419,B_420) ) ),
    inference(resolution,[status(thm)],[c_18,c_1575])).

tff(c_2659,plain,(
    ! [A_419,B_420] :
      ( v3_pre_topc('#skF_2'(A_419,B_420),'#skF_3')
      | ~ v1_tops_2(A_419,'#skF_3')
      | ~ m1_subset_1(A_419,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3'))))
      | ~ l1_pre_topc('#skF_3')
      | r1_tarski(A_419,B_420)
      | ~ r2_hidden('#skF_2'(A_419,B_420),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_837,c_2638])).

tff(c_3412,plain,(
    ! [A_507,B_508] :
      ( v3_pre_topc('#skF_2'(A_507,B_508),'#skF_3')
      | ~ v1_tops_2(A_507,'#skF_3')
      | ~ m1_subset_1(A_507,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3'))))
      | r1_tarski(A_507,B_508)
      | ~ r2_hidden('#skF_2'(A_507,B_508),'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_2659])).

tff(c_3432,plain,(
    ! [B_508] :
      ( v3_pre_topc('#skF_2'('#skF_4',B_508),'#skF_3')
      | ~ v1_tops_2('#skF_4','#skF_3')
      | r1_tarski('#skF_4',B_508)
      | ~ r2_hidden('#skF_2'('#skF_4',B_508),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_50,c_3412])).

tff(c_3444,plain,(
    ! [B_509] :
      ( v3_pre_topc('#skF_2'('#skF_4',B_509),'#skF_3')
      | r1_tarski('#skF_4',B_509)
      | ~ r2_hidden('#skF_2'('#skF_4',B_509),'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_803,c_3432])).

tff(c_872,plain,(
    ! [B_181,A_182] :
      ( r2_hidden(B_181,u1_pre_topc(A_182))
      | ~ v3_pre_topc(B_181,A_182)
      | ~ m1_subset_1(B_181,k1_zfmisc_1(u1_struct_0(A_182)))
      | ~ l1_pre_topc(A_182) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_878,plain,(
    ! [A_167] :
      ( r2_hidden(A_167,u1_pre_topc('#skF_3'))
      | ~ v3_pre_topc(A_167,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ r2_hidden(A_167,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_837,c_872])).

tff(c_895,plain,(
    ! [A_185] :
      ( r2_hidden(A_185,u1_pre_topc('#skF_3'))
      | ~ v3_pre_topc(A_185,'#skF_3')
      | ~ r2_hidden(A_185,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_878])).

tff(c_915,plain,(
    ! [A_13] :
      ( r1_tarski(A_13,u1_pre_topc('#skF_3'))
      | ~ v3_pre_topc('#skF_2'(A_13,u1_pre_topc('#skF_3')),'#skF_3')
      | ~ r2_hidden('#skF_2'(A_13,u1_pre_topc('#skF_3')),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_895,c_16])).

tff(c_3456,plain,
    ( r1_tarski('#skF_4',u1_pre_topc('#skF_3'))
    | ~ r2_hidden('#skF_2'('#skF_4',u1_pre_topc('#skF_3')),'#skF_4') ),
    inference(resolution,[status(thm)],[c_3444,c_915])).

tff(c_3467,plain,(
    ~ r2_hidden('#skF_2'('#skF_4',u1_pre_topc('#skF_3')),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_1219,c_1219,c_3456])).

tff(c_3473,plain,
    ( ~ r1_tarski('#skF_4','#skF_4')
    | r1_tarski('#skF_4',u1_pre_topc('#skF_3')) ),
    inference(resolution,[status(thm)],[c_105,c_3467])).

tff(c_3481,plain,(
    r1_tarski('#skF_4',u1_pre_topc('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_3473])).

tff(c_3483,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1219,c_3481])).

%------------------------------------------------------------------------------
