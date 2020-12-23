%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1617+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:08 EST 2020

% Result     : Theorem 5.93s
% Output     : CNFRefutation 6.39s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 260 expanded)
%              Number of leaves         :   41 ( 105 expanded)
%              Depth                    :   12
%              Number of atoms          :  212 ( 568 expanded)
%              Number of equality atoms :   30 (  88 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v1_tops_2 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v8_relat_2 > v4_relat_2 > v2_pre_topc > v1_relat_2 > v1_orders_2 > l1_pre_topc > l1_orders_2 > k2_zfmisc_1 > g1_orders_2 > #nlpp > u1_struct_0 > u1_pre_topc > u1_orders_2 > k2_yellow_1 > k1_zfmisc_1 > k1_yellow_1 > k1_wellord2 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(k1_wellord2,type,(
    k1_wellord2: $i > $i )).

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

tff(f_87,axiom,(
    ! [A] : k1_yellow_1(A) = k1_wellord2(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_yellow_1)).

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

tff(f_85,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A)))
     => ! [C,D] :
          ( g1_orders_2(A,B) = g1_orders_2(C,D)
         => ( A = C
            & B = D ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',free_g1_orders_2)).

tff(f_91,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_109,negated_conjecture,(
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

tff(f_97,axiom,(
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

tff(c_42,plain,(
    ! [A_29] : k1_yellow_1(A_29) = k1_wellord2(A_29) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_32,plain,(
    ! [A_21] : m1_subset_1(k1_yellow_1(A_21),k1_zfmisc_1(k2_zfmisc_1(A_21,A_21))) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_63,plain,(
    ! [A_21] : m1_subset_1(k1_wellord2(A_21),k1_zfmisc_1(k2_zfmisc_1(A_21,A_21))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_32])).

tff(c_12,plain,(
    ! [A_12] : g1_orders_2(A_12,k1_yellow_1(A_12)) = k2_yellow_1(A_12) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_68,plain,(
    ! [A_12] : g1_orders_2(A_12,k1_wellord2(A_12)) = k2_yellow_1(A_12) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_12])).

tff(c_715,plain,(
    ! [C_168,A_169,D_170,B_171] :
      ( C_168 = A_169
      | g1_orders_2(C_168,D_170) != g1_orders_2(A_169,B_171)
      | ~ m1_subset_1(B_171,k1_zfmisc_1(k2_zfmisc_1(A_169,A_169))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_723,plain,(
    ! [C_168,A_12,D_170] :
      ( C_168 = A_12
      | k2_yellow_1(A_12) != g1_orders_2(C_168,D_170)
      | ~ m1_subset_1(k1_wellord2(A_12),k1_zfmisc_1(k2_zfmisc_1(A_12,A_12))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_715])).

tff(c_726,plain,(
    ! [C_172,A_173,D_174] :
      ( C_172 = A_173
      | k2_yellow_1(A_173) != g1_orders_2(C_172,D_174) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_723])).

tff(c_729,plain,(
    ! [A_1,A_173] :
      ( u1_struct_0(A_1) = A_173
      | k2_yellow_1(A_173) != A_1
      | ~ v1_orders_2(A_1)
      | ~ l1_orders_2(A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_726])).

tff(c_758,plain,(
    ! [A_173] :
      ( u1_struct_0(k2_yellow_1(A_173)) = A_173
      | ~ v1_orders_2(k2_yellow_1(A_173))
      | ~ l1_orders_2(k2_yellow_1(A_173)) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_729])).

tff(c_760,plain,(
    ! [A_173] : u1_struct_0(k2_yellow_1(A_173)) = A_173 ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_758])).

tff(c_46,plain,(
    ! [A_30,B_31] :
      ( m1_subset_1(A_30,k1_zfmisc_1(B_31))
      | ~ r1_tarski(A_30,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_62,plain,
    ( v1_tops_2('#skF_4','#skF_3')
    | m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc('#skF_3'))))) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_117,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc('#skF_3'))))) ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_56,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc('#skF_3')))))
    | ~ v1_tops_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_127,plain,(
    ~ v1_tops_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_56])).

tff(c_52,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_50,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_207,plain,(
    ! [C_80,A_81,D_82,B_83] :
      ( C_80 = A_81
      | g1_orders_2(C_80,D_82) != g1_orders_2(A_81,B_83)
      | ~ m1_subset_1(B_83,k1_zfmisc_1(k2_zfmisc_1(A_81,A_81))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_215,plain,(
    ! [C_80,A_12,D_82] :
      ( C_80 = A_12
      | k2_yellow_1(A_12) != g1_orders_2(C_80,D_82)
      | ~ m1_subset_1(k1_wellord2(A_12),k1_zfmisc_1(k2_zfmisc_1(A_12,A_12))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_207])).

tff(c_218,plain,(
    ! [C_84,A_85,D_86] :
      ( C_84 = A_85
      | k2_yellow_1(A_85) != g1_orders_2(C_84,D_86) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_215])).

tff(c_221,plain,(
    ! [A_1,A_85] :
      ( u1_struct_0(A_1) = A_85
      | k2_yellow_1(A_85) != A_1
      | ~ v1_orders_2(A_1)
      | ~ l1_orders_2(A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_218])).

tff(c_233,plain,(
    ! [A_85] :
      ( u1_struct_0(k2_yellow_1(A_85)) = A_85
      | ~ v1_orders_2(k2_yellow_1(A_85))
      | ~ l1_orders_2(k2_yellow_1(A_85)) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_221])).

tff(c_235,plain,(
    ! [A_85] : u1_struct_0(k2_yellow_1(A_85)) = A_85 ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_233])).

tff(c_44,plain,(
    ! [A_30,B_31] :
      ( r1_tarski(A_30,B_31)
      | ~ m1_subset_1(A_30,k1_zfmisc_1(B_31)) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_121,plain,(
    r1_tarski('#skF_4',u1_struct_0(k2_yellow_1(u1_pre_topc('#skF_3')))) ),
    inference(resolution,[status(thm)],[c_117,c_44])).

tff(c_239,plain,(
    r1_tarski('#skF_4',u1_pre_topc('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_235,c_121])).

tff(c_484,plain,(
    ! [A_130,B_131] :
      ( r2_hidden('#skF_1'(A_130,B_131),B_131)
      | v1_tops_2(B_131,A_130)
      | ~ m1_subset_1(B_131,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_130))))
      | ~ l1_pre_topc(A_130) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_494,plain,
    ( r2_hidden('#skF_1'('#skF_3','#skF_4'),'#skF_4')
    | v1_tops_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_484])).

tff(c_499,plain,
    ( r2_hidden('#skF_1'('#skF_3','#skF_4'),'#skF_4')
    | v1_tops_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_494])).

tff(c_500,plain,(
    r2_hidden('#skF_1'('#skF_3','#skF_4'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_127,c_499])).

tff(c_14,plain,(
    ! [C_17,B_14,A_13] :
      ( r2_hidden(C_17,B_14)
      | ~ r2_hidden(C_17,A_13)
      | ~ r1_tarski(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_537,plain,(
    ! [B_133] :
      ( r2_hidden('#skF_1'('#skF_3','#skF_4'),B_133)
      | ~ r1_tarski('#skF_4',B_133) ) ),
    inference(resolution,[status(thm)],[c_500,c_14])).

tff(c_137,plain,(
    ! [A_59,C_60,B_61] :
      ( m1_subset_1(A_59,C_60)
      | ~ m1_subset_1(B_61,k1_zfmisc_1(C_60))
      | ~ r2_hidden(A_59,B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_149,plain,(
    ! [A_59] :
      ( m1_subset_1(A_59,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ r2_hidden(A_59,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_50,c_137])).

tff(c_421,plain,(
    ! [B_125,A_126] :
      ( v3_pre_topc(B_125,A_126)
      | ~ r2_hidden(B_125,u1_pre_topc(A_126))
      | ~ m1_subset_1(B_125,k1_zfmisc_1(u1_struct_0(A_126)))
      | ~ l1_pre_topc(A_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_431,plain,(
    ! [A_59] :
      ( v3_pre_topc(A_59,'#skF_3')
      | ~ r2_hidden(A_59,u1_pre_topc('#skF_3'))
      | ~ l1_pre_topc('#skF_3')
      | ~ r2_hidden(A_59,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_149,c_421])).

tff(c_439,plain,(
    ! [A_59] :
      ( v3_pre_topc(A_59,'#skF_3')
      | ~ r2_hidden(A_59,u1_pre_topc('#skF_3'))
      | ~ r2_hidden(A_59,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_431])).

tff(c_545,plain,
    ( v3_pre_topc('#skF_1'('#skF_3','#skF_4'),'#skF_3')
    | ~ r2_hidden('#skF_1'('#skF_3','#skF_4'),'#skF_4')
    | ~ r1_tarski('#skF_4',u1_pre_topc('#skF_3')) ),
    inference(resolution,[status(thm)],[c_537,c_439])).

tff(c_561,plain,(
    v3_pre_topc('#skF_1'('#skF_3','#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_239,c_500,c_545])).

tff(c_618,plain,(
    ! [A_137,B_138] :
      ( ~ v3_pre_topc('#skF_1'(A_137,B_138),A_137)
      | v1_tops_2(B_138,A_137)
      | ~ m1_subset_1(B_138,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_137))))
      | ~ l1_pre_topc(A_137) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_620,plain,
    ( v1_tops_2('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3'))))
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_561,c_618])).

tff(c_623,plain,(
    v1_tops_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_620])).

tff(c_625,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_127,c_623])).

tff(c_627,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc('#skF_3'))))) ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_631,plain,(
    ~ r1_tarski('#skF_4',u1_struct_0(k2_yellow_1(u1_pre_topc('#skF_3')))) ),
    inference(resolution,[status(thm)],[c_46,c_627])).

tff(c_762,plain,(
    ~ r1_tarski('#skF_4',u1_pre_topc('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_760,c_631])).

tff(c_110,plain,(
    ! [A_52,B_53] :
      ( r2_hidden('#skF_2'(A_52,B_53),A_52)
      | r1_tarski(A_52,B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_16,plain,(
    ! [A_13,B_14] :
      ( ~ r2_hidden('#skF_2'(A_13,B_14),B_14)
      | r1_tarski(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_115,plain,(
    ! [A_52] : r1_tarski(A_52,A_52) ),
    inference(resolution,[status(thm)],[c_110,c_16])).

tff(c_18,plain,(
    ! [A_13,B_14] :
      ( r2_hidden('#skF_2'(A_13,B_14),A_13)
      | r1_tarski(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_634,plain,(
    ! [C_139,B_140,A_141] :
      ( r2_hidden(C_139,B_140)
      | ~ r2_hidden(C_139,A_141)
      | ~ r1_tarski(A_141,B_140) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_637,plain,(
    ! [A_13,B_14,B_140] :
      ( r2_hidden('#skF_2'(A_13,B_14),B_140)
      | ~ r1_tarski(A_13,B_140)
      | r1_tarski(A_13,B_14) ) ),
    inference(resolution,[status(thm)],[c_18,c_634])).

tff(c_626,plain,(
    v1_tops_2('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_638,plain,(
    ! [A_142,C_143,B_144] :
      ( m1_subset_1(A_142,C_143)
      | ~ m1_subset_1(B_144,k1_zfmisc_1(C_143))
      | ~ r2_hidden(A_142,B_144) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_647,plain,(
    ! [A_142] :
      ( m1_subset_1(A_142,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ r2_hidden(A_142,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_50,c_638])).

tff(c_1303,plain,(
    ! [C_258,A_259,B_260] :
      ( v3_pre_topc(C_258,A_259)
      | ~ r2_hidden(C_258,B_260)
      | ~ m1_subset_1(C_258,k1_zfmisc_1(u1_struct_0(A_259)))
      | ~ v1_tops_2(B_260,A_259)
      | ~ m1_subset_1(B_260,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_259))))
      | ~ l1_pre_topc(A_259) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_2310,plain,(
    ! [A_403,B_404,A_405] :
      ( v3_pre_topc('#skF_2'(A_403,B_404),A_405)
      | ~ m1_subset_1('#skF_2'(A_403,B_404),k1_zfmisc_1(u1_struct_0(A_405)))
      | ~ v1_tops_2(A_403,A_405)
      | ~ m1_subset_1(A_403,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_405))))
      | ~ l1_pre_topc(A_405)
      | r1_tarski(A_403,B_404) ) ),
    inference(resolution,[status(thm)],[c_18,c_1303])).

tff(c_2324,plain,(
    ! [A_403,B_404] :
      ( v3_pre_topc('#skF_2'(A_403,B_404),'#skF_3')
      | ~ v1_tops_2(A_403,'#skF_3')
      | ~ m1_subset_1(A_403,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3'))))
      | ~ l1_pre_topc('#skF_3')
      | r1_tarski(A_403,B_404)
      | ~ r2_hidden('#skF_2'(A_403,B_404),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_647,c_2310])).

tff(c_3739,plain,(
    ! [A_512,B_513] :
      ( v3_pre_topc('#skF_2'(A_512,B_513),'#skF_3')
      | ~ v1_tops_2(A_512,'#skF_3')
      | ~ m1_subset_1(A_512,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3'))))
      | r1_tarski(A_512,B_513)
      | ~ r2_hidden('#skF_2'(A_512,B_513),'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_2324])).

tff(c_3759,plain,(
    ! [B_513] :
      ( v3_pre_topc('#skF_2'('#skF_4',B_513),'#skF_3')
      | ~ v1_tops_2('#skF_4','#skF_3')
      | r1_tarski('#skF_4',B_513)
      | ~ r2_hidden('#skF_2'('#skF_4',B_513),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_50,c_3739])).

tff(c_3769,plain,(
    ! [B_514] :
      ( v3_pre_topc('#skF_2'('#skF_4',B_514),'#skF_3')
      | r1_tarski('#skF_4',B_514)
      | ~ r2_hidden('#skF_2'('#skF_4',B_514),'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_626,c_3759])).

tff(c_894,plain,(
    ! [B_203,A_204] :
      ( r2_hidden(B_203,u1_pre_topc(A_204))
      | ~ v3_pre_topc(B_203,A_204)
      | ~ m1_subset_1(B_203,k1_zfmisc_1(u1_struct_0(A_204)))
      | ~ l1_pre_topc(A_204) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_904,plain,(
    ! [A_142] :
      ( r2_hidden(A_142,u1_pre_topc('#skF_3'))
      | ~ v3_pre_topc(A_142,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ r2_hidden(A_142,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_647,c_894])).

tff(c_914,plain,(
    ! [A_205] :
      ( r2_hidden(A_205,u1_pre_topc('#skF_3'))
      | ~ v3_pre_topc(A_205,'#skF_3')
      | ~ r2_hidden(A_205,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_904])).

tff(c_938,plain,(
    ! [A_13] :
      ( r1_tarski(A_13,u1_pre_topc('#skF_3'))
      | ~ v3_pre_topc('#skF_2'(A_13,u1_pre_topc('#skF_3')),'#skF_3')
      | ~ r2_hidden('#skF_2'(A_13,u1_pre_topc('#skF_3')),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_914,c_16])).

tff(c_3781,plain,
    ( r1_tarski('#skF_4',u1_pre_topc('#skF_3'))
    | ~ r2_hidden('#skF_2'('#skF_4',u1_pre_topc('#skF_3')),'#skF_4') ),
    inference(resolution,[status(thm)],[c_3769,c_938])).

tff(c_3792,plain,(
    ~ r2_hidden('#skF_2'('#skF_4',u1_pre_topc('#skF_3')),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_762,c_762,c_3781])).

tff(c_3798,plain,
    ( ~ r1_tarski('#skF_4','#skF_4')
    | r1_tarski('#skF_4',u1_pre_topc('#skF_3')) ),
    inference(resolution,[status(thm)],[c_637,c_3792])).

tff(c_3806,plain,(
    r1_tarski('#skF_4',u1_pre_topc('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_115,c_3798])).

tff(c_3808,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_762,c_3806])).

%------------------------------------------------------------------------------
