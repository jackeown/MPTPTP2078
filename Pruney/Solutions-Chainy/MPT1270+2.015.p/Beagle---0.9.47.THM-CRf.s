%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:57 EST 2020

% Result     : Theorem 4.35s
% Output     : CNFRefutation 4.35s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 209 expanded)
%              Number of leaves         :   41 (  93 expanded)
%              Depth                    :   11
%              Number of atoms          :  136 ( 409 expanded)
%              Number of equality atoms :   34 (  81 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_tops_1 > r2_hidden > r1_tarski > m1_subset_1 > l1_pre_topc > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k7_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_7 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k2_tops_1,type,(
    k2_tops_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(v2_tops_1,type,(
    v2_tops_1: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_121,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v2_tops_1(B,A)
            <=> r1_tarski(B,k2_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_tops_1)).

tff(f_111,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> k1_tops_1(A,B) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_tops_1)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_102,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
        <=> r2_hidden(C,B) )
     => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).

tff(f_55,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(c_80,plain,
    ( v2_tops_1('#skF_7','#skF_6')
    | r1_tarski('#skF_7',k2_tops_1('#skF_6','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_126,plain,(
    r1_tarski('#skF_7',k2_tops_1('#skF_6','#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_80])).

tff(c_74,plain,
    ( ~ r1_tarski('#skF_7',k2_tops_1('#skF_6','#skF_7'))
    | ~ v2_tops_1('#skF_7','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_128,plain,(
    ~ v2_tops_1('#skF_7','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_74])).

tff(c_72,plain,(
    l1_pre_topc('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_70,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_558,plain,(
    ! [B_151,A_152] :
      ( v2_tops_1(B_151,A_152)
      | k1_tops_1(A_152,B_151) != k1_xboole_0
      | ~ m1_subset_1(B_151,k1_zfmisc_1(u1_struct_0(A_152)))
      | ~ l1_pre_topc(A_152) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_561,plain,
    ( v2_tops_1('#skF_7','#skF_6')
    | k1_tops_1('#skF_6','#skF_7') != k1_xboole_0
    | ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_70,c_558])).

tff(c_564,plain,
    ( v2_tops_1('#skF_7','#skF_6')
    | k1_tops_1('#skF_6','#skF_7') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_561])).

tff(c_565,plain,(
    k1_tops_1('#skF_6','#skF_7') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_128,c_564])).

tff(c_189,plain,(
    ! [A_95,B_96,C_97] :
      ( k7_subset_1(A_95,B_96,C_97) = k4_xboole_0(B_96,C_97)
      | ~ m1_subset_1(B_96,k1_zfmisc_1(A_95)) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_192,plain,(
    ! [C_97] : k7_subset_1(u1_struct_0('#skF_6'),'#skF_7',C_97) = k4_xboole_0('#skF_7',C_97) ),
    inference(resolution,[status(thm)],[c_70,c_189])).

tff(c_1198,plain,(
    ! [A_220,B_221] :
      ( k7_subset_1(u1_struct_0(A_220),B_221,k2_tops_1(A_220,B_221)) = k1_tops_1(A_220,B_221)
      | ~ m1_subset_1(B_221,k1_zfmisc_1(u1_struct_0(A_220)))
      | ~ l1_pre_topc(A_220) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_1202,plain,
    ( k7_subset_1(u1_struct_0('#skF_6'),'#skF_7',k2_tops_1('#skF_6','#skF_7')) = k1_tops_1('#skF_6','#skF_7')
    | ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_70,c_1198])).

tff(c_1206,plain,(
    k4_xboole_0('#skF_7',k2_tops_1('#skF_6','#skF_7')) = k1_tops_1('#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_192,c_1202])).

tff(c_32,plain,(
    ! [A_12,B_13] :
      ( r2_hidden('#skF_4'(A_12,B_13),B_13)
      | r2_hidden('#skF_5'(A_12,B_13),A_12)
      | B_13 = A_12 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_294,plain,(
    ! [A_118,B_119] :
      ( r2_hidden('#skF_4'(A_118,B_119),B_119)
      | r2_hidden('#skF_5'(A_118,B_119),A_118)
      | B_119 = A_118 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_38,plain,(
    ! [A_18] : k4_xboole_0(A_18,k1_xboole_0) = A_18 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_129,plain,(
    ! [D_74,B_75,A_76] :
      ( ~ r2_hidden(D_74,B_75)
      | ~ r2_hidden(D_74,k4_xboole_0(A_76,B_75)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_132,plain,(
    ! [D_74,A_18] :
      ( ~ r2_hidden(D_74,k1_xboole_0)
      | ~ r2_hidden(D_74,A_18) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_129])).

tff(c_499,plain,(
    ! [B_146,A_147] :
      ( ~ r2_hidden('#skF_5'(k1_xboole_0,B_146),A_147)
      | r2_hidden('#skF_4'(k1_xboole_0,B_146),B_146)
      | k1_xboole_0 = B_146 ) ),
    inference(resolution,[status(thm)],[c_294,c_132])).

tff(c_512,plain,(
    ! [B_148] :
      ( r2_hidden('#skF_4'(k1_xboole_0,B_148),B_148)
      | k1_xboole_0 = B_148 ) ),
    inference(resolution,[status(thm)],[c_32,c_499])).

tff(c_12,plain,(
    ! [D_11,A_6,B_7] :
      ( r2_hidden(D_11,A_6)
      | ~ r2_hidden(D_11,k4_xboole_0(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_532,plain,(
    ! [A_6,B_7] :
      ( r2_hidden('#skF_4'(k1_xboole_0,k4_xboole_0(A_6,B_7)),A_6)
      | k4_xboole_0(A_6,B_7) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_512,c_12])).

tff(c_1236,plain,
    ( r2_hidden('#skF_4'(k1_xboole_0,k1_tops_1('#skF_6','#skF_7')),'#skF_7')
    | k4_xboole_0('#skF_7',k2_tops_1('#skF_6','#skF_7')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1206,c_532])).

tff(c_1269,plain,
    ( r2_hidden('#skF_4'(k1_xboole_0,k1_tops_1('#skF_6','#skF_7')),'#skF_7')
    | k1_tops_1('#skF_6','#skF_7') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1206,c_1236])).

tff(c_1270,plain,(
    r2_hidden('#skF_4'(k1_xboole_0,k1_tops_1('#skF_6','#skF_7')),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_565,c_1269])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1465,plain,(
    ! [B_228] :
      ( r2_hidden('#skF_4'(k1_xboole_0,k1_tops_1('#skF_6','#skF_7')),B_228)
      | ~ r1_tarski('#skF_7',B_228) ) ),
    inference(resolution,[status(thm)],[c_1270,c_2])).

tff(c_10,plain,(
    ! [D_11,B_7,A_6] :
      ( ~ r2_hidden(D_11,B_7)
      | ~ r2_hidden(D_11,k4_xboole_0(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_535,plain,(
    ! [A_6,B_7] :
      ( ~ r2_hidden('#skF_4'(k1_xboole_0,k4_xboole_0(A_6,B_7)),B_7)
      | k4_xboole_0(A_6,B_7) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_512,c_10])).

tff(c_1233,plain,
    ( ~ r2_hidden('#skF_4'(k1_xboole_0,k1_tops_1('#skF_6','#skF_7')),k2_tops_1('#skF_6','#skF_7'))
    | k4_xboole_0('#skF_7',k2_tops_1('#skF_6','#skF_7')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1206,c_535])).

tff(c_1267,plain,
    ( ~ r2_hidden('#skF_4'(k1_xboole_0,k1_tops_1('#skF_6','#skF_7')),k2_tops_1('#skF_6','#skF_7'))
    | k1_tops_1('#skF_6','#skF_7') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1206,c_1233])).

tff(c_1268,plain,(
    ~ r2_hidden('#skF_4'(k1_xboole_0,k1_tops_1('#skF_6','#skF_7')),k2_tops_1('#skF_6','#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_565,c_1267])).

tff(c_1472,plain,(
    ~ r1_tarski('#skF_7',k2_tops_1('#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_1465,c_1268])).

tff(c_1508,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_1472])).

tff(c_1510,plain,(
    ~ r1_tarski('#skF_7',k2_tops_1('#skF_6','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_80])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1509,plain,(
    v2_tops_1('#skF_7','#skF_6') ),
    inference(splitRight,[status(thm)],[c_80])).

tff(c_1979,plain,(
    ! [A_309,B_310] :
      ( k1_tops_1(A_309,B_310) = k1_xboole_0
      | ~ v2_tops_1(B_310,A_309)
      | ~ m1_subset_1(B_310,k1_zfmisc_1(u1_struct_0(A_309)))
      | ~ l1_pre_topc(A_309) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_1985,plain,
    ( k1_tops_1('#skF_6','#skF_7') = k1_xboole_0
    | ~ v2_tops_1('#skF_7','#skF_6')
    | ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_70,c_1979])).

tff(c_1989,plain,(
    k1_tops_1('#skF_6','#skF_7') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_1509,c_1985])).

tff(c_1605,plain,(
    ! [A_257,B_258,C_259] :
      ( k7_subset_1(A_257,B_258,C_259) = k4_xboole_0(B_258,C_259)
      | ~ m1_subset_1(B_258,k1_zfmisc_1(A_257)) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1608,plain,(
    ! [C_259] : k7_subset_1(u1_struct_0('#skF_6'),'#skF_7',C_259) = k4_xboole_0('#skF_7',C_259) ),
    inference(resolution,[status(thm)],[c_70,c_1605])).

tff(c_2621,plain,(
    ! [A_381,B_382] :
      ( k7_subset_1(u1_struct_0(A_381),B_382,k2_tops_1(A_381,B_382)) = k1_tops_1(A_381,B_382)
      | ~ m1_subset_1(B_382,k1_zfmisc_1(u1_struct_0(A_381)))
      | ~ l1_pre_topc(A_381) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_2625,plain,
    ( k7_subset_1(u1_struct_0('#skF_6'),'#skF_7',k2_tops_1('#skF_6','#skF_7')) = k1_tops_1('#skF_6','#skF_7')
    | ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_70,c_2621])).

tff(c_2629,plain,(
    k4_xboole_0('#skF_7',k2_tops_1('#skF_6','#skF_7')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_1989,c_1608,c_2625])).

tff(c_8,plain,(
    ! [D_11,A_6,B_7] :
      ( r2_hidden(D_11,k4_xboole_0(A_6,B_7))
      | r2_hidden(D_11,B_7)
      | ~ r2_hidden(D_11,A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_2698,plain,(
    ! [D_383] :
      ( r2_hidden(D_383,k1_xboole_0)
      | r2_hidden(D_383,k2_tops_1('#skF_6','#skF_7'))
      | ~ r2_hidden(D_383,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2629,c_8])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_3319,plain,(
    ! [A_438] :
      ( r1_tarski(A_438,k2_tops_1('#skF_6','#skF_7'))
      | r2_hidden('#skF_1'(A_438,k2_tops_1('#skF_6','#skF_7')),k1_xboole_0)
      | ~ r2_hidden('#skF_1'(A_438,k2_tops_1('#skF_6','#skF_7')),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_2698,c_4])).

tff(c_1538,plain,(
    ! [A_241,B_242] :
      ( r2_hidden('#skF_1'(A_241,B_242),A_241)
      | r1_tarski(A_241,B_242) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1746,plain,(
    ! [A_279,B_280,B_281] :
      ( ~ r2_hidden('#skF_1'(k4_xboole_0(A_279,B_280),B_281),B_280)
      | r1_tarski(k4_xboole_0(A_279,B_280),B_281) ) ),
    inference(resolution,[status(thm)],[c_1538,c_10])).

tff(c_1757,plain,(
    ! [A_18,B_281] :
      ( ~ r2_hidden('#skF_1'(A_18,B_281),k1_xboole_0)
      | r1_tarski(k4_xboole_0(A_18,k1_xboole_0),B_281) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_1746])).

tff(c_1763,plain,(
    ! [A_18,B_281] :
      ( ~ r2_hidden('#skF_1'(A_18,B_281),k1_xboole_0)
      | r1_tarski(A_18,B_281) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_1757])).

tff(c_3345,plain,(
    ! [A_439] :
      ( r1_tarski(A_439,k2_tops_1('#skF_6','#skF_7'))
      | ~ r2_hidden('#skF_1'(A_439,k2_tops_1('#skF_6','#skF_7')),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_3319,c_1763])).

tff(c_3357,plain,(
    r1_tarski('#skF_7',k2_tops_1('#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_6,c_3345])).

tff(c_3363,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1510,c_1510,c_3357])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:42:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.35/1.88  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.35/1.89  
% 4.35/1.89  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.35/1.89  %$ v2_tops_1 > r2_hidden > r1_tarski > m1_subset_1 > l1_pre_topc > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k7_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_7 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_5 > #skF_4
% 4.35/1.89  
% 4.35/1.89  %Foreground sorts:
% 4.35/1.89  
% 4.35/1.89  
% 4.35/1.89  %Background operators:
% 4.35/1.89  
% 4.35/1.89  
% 4.35/1.89  %Foreground operators:
% 4.35/1.89  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.35/1.89  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.35/1.89  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.35/1.89  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 4.35/1.89  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.35/1.89  tff(v2_tops_1, type, v2_tops_1: ($i * $i) > $o).
% 4.35/1.89  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.35/1.89  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.35/1.89  tff('#skF_7', type, '#skF_7': $i).
% 4.35/1.89  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.35/1.89  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.35/1.89  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.35/1.89  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.35/1.89  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 4.35/1.89  tff('#skF_6', type, '#skF_6': $i).
% 4.35/1.89  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.35/1.89  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 4.35/1.89  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.35/1.89  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.35/1.89  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.35/1.89  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 4.35/1.89  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.35/1.89  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 4.35/1.89  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.35/1.89  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.35/1.89  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 4.35/1.89  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.35/1.89  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.35/1.89  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 4.35/1.89  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 4.35/1.89  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 4.35/1.89  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.35/1.89  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 4.35/1.89  
% 4.35/1.91  tff(f_121, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> r1_tarski(B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_tops_1)).
% 4.35/1.91  tff(f_111, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (k1_tops_1(A, B) = k1_xboole_0)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t84_tops_1)).
% 4.35/1.91  tff(f_73, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 4.35/1.91  tff(f_102, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_tops_1)).
% 4.35/1.91  tff(f_49, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) <=> r2_hidden(C, B))) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tarski)).
% 4.35/1.91  tff(f_55, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 4.35/1.91  tff(f_42, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 4.35/1.91  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 4.35/1.91  tff(c_80, plain, (v2_tops_1('#skF_7', '#skF_6') | r1_tarski('#skF_7', k2_tops_1('#skF_6', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_121])).
% 4.35/1.91  tff(c_126, plain, (r1_tarski('#skF_7', k2_tops_1('#skF_6', '#skF_7'))), inference(splitLeft, [status(thm)], [c_80])).
% 4.35/1.91  tff(c_74, plain, (~r1_tarski('#skF_7', k2_tops_1('#skF_6', '#skF_7')) | ~v2_tops_1('#skF_7', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_121])).
% 4.35/1.91  tff(c_128, plain, (~v2_tops_1('#skF_7', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_126, c_74])).
% 4.35/1.91  tff(c_72, plain, (l1_pre_topc('#skF_6')), inference(cnfTransformation, [status(thm)], [f_121])).
% 4.35/1.91  tff(c_70, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0('#skF_6')))), inference(cnfTransformation, [status(thm)], [f_121])).
% 4.35/1.91  tff(c_558, plain, (![B_151, A_152]: (v2_tops_1(B_151, A_152) | k1_tops_1(A_152, B_151)!=k1_xboole_0 | ~m1_subset_1(B_151, k1_zfmisc_1(u1_struct_0(A_152))) | ~l1_pre_topc(A_152))), inference(cnfTransformation, [status(thm)], [f_111])).
% 4.35/1.91  tff(c_561, plain, (v2_tops_1('#skF_7', '#skF_6') | k1_tops_1('#skF_6', '#skF_7')!=k1_xboole_0 | ~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_70, c_558])).
% 4.35/1.91  tff(c_564, plain, (v2_tops_1('#skF_7', '#skF_6') | k1_tops_1('#skF_6', '#skF_7')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_72, c_561])).
% 4.35/1.91  tff(c_565, plain, (k1_tops_1('#skF_6', '#skF_7')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_128, c_564])).
% 4.35/1.91  tff(c_189, plain, (![A_95, B_96, C_97]: (k7_subset_1(A_95, B_96, C_97)=k4_xboole_0(B_96, C_97) | ~m1_subset_1(B_96, k1_zfmisc_1(A_95)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.35/1.91  tff(c_192, plain, (![C_97]: (k7_subset_1(u1_struct_0('#skF_6'), '#skF_7', C_97)=k4_xboole_0('#skF_7', C_97))), inference(resolution, [status(thm)], [c_70, c_189])).
% 4.35/1.91  tff(c_1198, plain, (![A_220, B_221]: (k7_subset_1(u1_struct_0(A_220), B_221, k2_tops_1(A_220, B_221))=k1_tops_1(A_220, B_221) | ~m1_subset_1(B_221, k1_zfmisc_1(u1_struct_0(A_220))) | ~l1_pre_topc(A_220))), inference(cnfTransformation, [status(thm)], [f_102])).
% 4.35/1.91  tff(c_1202, plain, (k7_subset_1(u1_struct_0('#skF_6'), '#skF_7', k2_tops_1('#skF_6', '#skF_7'))=k1_tops_1('#skF_6', '#skF_7') | ~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_70, c_1198])).
% 4.35/1.91  tff(c_1206, plain, (k4_xboole_0('#skF_7', k2_tops_1('#skF_6', '#skF_7'))=k1_tops_1('#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_192, c_1202])).
% 4.35/1.91  tff(c_32, plain, (![A_12, B_13]: (r2_hidden('#skF_4'(A_12, B_13), B_13) | r2_hidden('#skF_5'(A_12, B_13), A_12) | B_13=A_12)), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.35/1.91  tff(c_294, plain, (![A_118, B_119]: (r2_hidden('#skF_4'(A_118, B_119), B_119) | r2_hidden('#skF_5'(A_118, B_119), A_118) | B_119=A_118)), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.35/1.91  tff(c_38, plain, (![A_18]: (k4_xboole_0(A_18, k1_xboole_0)=A_18)), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.35/1.91  tff(c_129, plain, (![D_74, B_75, A_76]: (~r2_hidden(D_74, B_75) | ~r2_hidden(D_74, k4_xboole_0(A_76, B_75)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.35/1.91  tff(c_132, plain, (![D_74, A_18]: (~r2_hidden(D_74, k1_xboole_0) | ~r2_hidden(D_74, A_18))), inference(superposition, [status(thm), theory('equality')], [c_38, c_129])).
% 4.35/1.91  tff(c_499, plain, (![B_146, A_147]: (~r2_hidden('#skF_5'(k1_xboole_0, B_146), A_147) | r2_hidden('#skF_4'(k1_xboole_0, B_146), B_146) | k1_xboole_0=B_146)), inference(resolution, [status(thm)], [c_294, c_132])).
% 4.35/1.91  tff(c_512, plain, (![B_148]: (r2_hidden('#skF_4'(k1_xboole_0, B_148), B_148) | k1_xboole_0=B_148)), inference(resolution, [status(thm)], [c_32, c_499])).
% 4.35/1.91  tff(c_12, plain, (![D_11, A_6, B_7]: (r2_hidden(D_11, A_6) | ~r2_hidden(D_11, k4_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.35/1.91  tff(c_532, plain, (![A_6, B_7]: (r2_hidden('#skF_4'(k1_xboole_0, k4_xboole_0(A_6, B_7)), A_6) | k4_xboole_0(A_6, B_7)=k1_xboole_0)), inference(resolution, [status(thm)], [c_512, c_12])).
% 4.35/1.91  tff(c_1236, plain, (r2_hidden('#skF_4'(k1_xboole_0, k1_tops_1('#skF_6', '#skF_7')), '#skF_7') | k4_xboole_0('#skF_7', k2_tops_1('#skF_6', '#skF_7'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_1206, c_532])).
% 4.35/1.91  tff(c_1269, plain, (r2_hidden('#skF_4'(k1_xboole_0, k1_tops_1('#skF_6', '#skF_7')), '#skF_7') | k1_tops_1('#skF_6', '#skF_7')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1206, c_1236])).
% 4.35/1.91  tff(c_1270, plain, (r2_hidden('#skF_4'(k1_xboole_0, k1_tops_1('#skF_6', '#skF_7')), '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_565, c_1269])).
% 4.35/1.91  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.35/1.91  tff(c_1465, plain, (![B_228]: (r2_hidden('#skF_4'(k1_xboole_0, k1_tops_1('#skF_6', '#skF_7')), B_228) | ~r1_tarski('#skF_7', B_228))), inference(resolution, [status(thm)], [c_1270, c_2])).
% 4.35/1.91  tff(c_10, plain, (![D_11, B_7, A_6]: (~r2_hidden(D_11, B_7) | ~r2_hidden(D_11, k4_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.35/1.91  tff(c_535, plain, (![A_6, B_7]: (~r2_hidden('#skF_4'(k1_xboole_0, k4_xboole_0(A_6, B_7)), B_7) | k4_xboole_0(A_6, B_7)=k1_xboole_0)), inference(resolution, [status(thm)], [c_512, c_10])).
% 4.35/1.91  tff(c_1233, plain, (~r2_hidden('#skF_4'(k1_xboole_0, k1_tops_1('#skF_6', '#skF_7')), k2_tops_1('#skF_6', '#skF_7')) | k4_xboole_0('#skF_7', k2_tops_1('#skF_6', '#skF_7'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_1206, c_535])).
% 4.35/1.91  tff(c_1267, plain, (~r2_hidden('#skF_4'(k1_xboole_0, k1_tops_1('#skF_6', '#skF_7')), k2_tops_1('#skF_6', '#skF_7')) | k1_tops_1('#skF_6', '#skF_7')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1206, c_1233])).
% 4.35/1.91  tff(c_1268, plain, (~r2_hidden('#skF_4'(k1_xboole_0, k1_tops_1('#skF_6', '#skF_7')), k2_tops_1('#skF_6', '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_565, c_1267])).
% 4.35/1.91  tff(c_1472, plain, (~r1_tarski('#skF_7', k2_tops_1('#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_1465, c_1268])).
% 4.35/1.91  tff(c_1508, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_126, c_1472])).
% 4.35/1.91  tff(c_1510, plain, (~r1_tarski('#skF_7', k2_tops_1('#skF_6', '#skF_7'))), inference(splitRight, [status(thm)], [c_80])).
% 4.35/1.91  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.35/1.91  tff(c_1509, plain, (v2_tops_1('#skF_7', '#skF_6')), inference(splitRight, [status(thm)], [c_80])).
% 4.35/1.91  tff(c_1979, plain, (![A_309, B_310]: (k1_tops_1(A_309, B_310)=k1_xboole_0 | ~v2_tops_1(B_310, A_309) | ~m1_subset_1(B_310, k1_zfmisc_1(u1_struct_0(A_309))) | ~l1_pre_topc(A_309))), inference(cnfTransformation, [status(thm)], [f_111])).
% 4.35/1.91  tff(c_1985, plain, (k1_tops_1('#skF_6', '#skF_7')=k1_xboole_0 | ~v2_tops_1('#skF_7', '#skF_6') | ~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_70, c_1979])).
% 4.35/1.91  tff(c_1989, plain, (k1_tops_1('#skF_6', '#skF_7')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_72, c_1509, c_1985])).
% 4.35/1.91  tff(c_1605, plain, (![A_257, B_258, C_259]: (k7_subset_1(A_257, B_258, C_259)=k4_xboole_0(B_258, C_259) | ~m1_subset_1(B_258, k1_zfmisc_1(A_257)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.35/1.91  tff(c_1608, plain, (![C_259]: (k7_subset_1(u1_struct_0('#skF_6'), '#skF_7', C_259)=k4_xboole_0('#skF_7', C_259))), inference(resolution, [status(thm)], [c_70, c_1605])).
% 4.35/1.91  tff(c_2621, plain, (![A_381, B_382]: (k7_subset_1(u1_struct_0(A_381), B_382, k2_tops_1(A_381, B_382))=k1_tops_1(A_381, B_382) | ~m1_subset_1(B_382, k1_zfmisc_1(u1_struct_0(A_381))) | ~l1_pre_topc(A_381))), inference(cnfTransformation, [status(thm)], [f_102])).
% 4.35/1.91  tff(c_2625, plain, (k7_subset_1(u1_struct_0('#skF_6'), '#skF_7', k2_tops_1('#skF_6', '#skF_7'))=k1_tops_1('#skF_6', '#skF_7') | ~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_70, c_2621])).
% 4.35/1.91  tff(c_2629, plain, (k4_xboole_0('#skF_7', k2_tops_1('#skF_6', '#skF_7'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_72, c_1989, c_1608, c_2625])).
% 4.35/1.91  tff(c_8, plain, (![D_11, A_6, B_7]: (r2_hidden(D_11, k4_xboole_0(A_6, B_7)) | r2_hidden(D_11, B_7) | ~r2_hidden(D_11, A_6))), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.35/1.91  tff(c_2698, plain, (![D_383]: (r2_hidden(D_383, k1_xboole_0) | r2_hidden(D_383, k2_tops_1('#skF_6', '#skF_7')) | ~r2_hidden(D_383, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_2629, c_8])).
% 4.35/1.91  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.35/1.91  tff(c_3319, plain, (![A_438]: (r1_tarski(A_438, k2_tops_1('#skF_6', '#skF_7')) | r2_hidden('#skF_1'(A_438, k2_tops_1('#skF_6', '#skF_7')), k1_xboole_0) | ~r2_hidden('#skF_1'(A_438, k2_tops_1('#skF_6', '#skF_7')), '#skF_7'))), inference(resolution, [status(thm)], [c_2698, c_4])).
% 4.35/1.91  tff(c_1538, plain, (![A_241, B_242]: (r2_hidden('#skF_1'(A_241, B_242), A_241) | r1_tarski(A_241, B_242))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.35/1.91  tff(c_1746, plain, (![A_279, B_280, B_281]: (~r2_hidden('#skF_1'(k4_xboole_0(A_279, B_280), B_281), B_280) | r1_tarski(k4_xboole_0(A_279, B_280), B_281))), inference(resolution, [status(thm)], [c_1538, c_10])).
% 4.35/1.91  tff(c_1757, plain, (![A_18, B_281]: (~r2_hidden('#skF_1'(A_18, B_281), k1_xboole_0) | r1_tarski(k4_xboole_0(A_18, k1_xboole_0), B_281))), inference(superposition, [status(thm), theory('equality')], [c_38, c_1746])).
% 4.35/1.91  tff(c_1763, plain, (![A_18, B_281]: (~r2_hidden('#skF_1'(A_18, B_281), k1_xboole_0) | r1_tarski(A_18, B_281))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_1757])).
% 4.35/1.91  tff(c_3345, plain, (![A_439]: (r1_tarski(A_439, k2_tops_1('#skF_6', '#skF_7')) | ~r2_hidden('#skF_1'(A_439, k2_tops_1('#skF_6', '#skF_7')), '#skF_7'))), inference(resolution, [status(thm)], [c_3319, c_1763])).
% 4.35/1.91  tff(c_3357, plain, (r1_tarski('#skF_7', k2_tops_1('#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_6, c_3345])).
% 4.35/1.91  tff(c_3363, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1510, c_1510, c_3357])).
% 4.35/1.91  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.35/1.91  
% 4.35/1.91  Inference rules
% 4.35/1.91  ----------------------
% 4.35/1.91  #Ref     : 0
% 4.35/1.91  #Sup     : 726
% 4.35/1.91  #Fact    : 0
% 4.35/1.91  #Define  : 0
% 4.35/1.91  #Split   : 2
% 4.35/1.91  #Chain   : 0
% 4.35/1.91  #Close   : 0
% 4.35/1.91  
% 4.35/1.91  Ordering : KBO
% 4.35/1.91  
% 4.35/1.91  Simplification rules
% 4.35/1.91  ----------------------
% 4.35/1.91  #Subsume      : 164
% 4.35/1.91  #Demod        : 325
% 4.35/1.91  #Tautology    : 264
% 4.35/1.91  #SimpNegUnit  : 12
% 4.35/1.91  #BackRed      : 2
% 4.35/1.91  
% 4.35/1.91  #Partial instantiations: 0
% 4.35/1.91  #Strategies tried      : 1
% 4.35/1.91  
% 4.35/1.91  Timing (in seconds)
% 4.35/1.91  ----------------------
% 4.35/1.91  Preprocessing        : 0.37
% 4.35/1.91  Parsing              : 0.20
% 4.35/1.91  CNF conversion       : 0.03
% 4.35/1.91  Main loop            : 0.71
% 4.35/1.91  Inferencing          : 0.25
% 4.35/1.91  Reduction            : 0.21
% 4.35/1.91  Demodulation         : 0.15
% 4.35/1.91  BG Simplification    : 0.03
% 4.35/1.91  Subsumption          : 0.15
% 4.35/1.91  Abstraction          : 0.04
% 4.35/1.91  MUC search           : 0.00
% 4.35/1.91  Cooper               : 0.00
% 4.35/1.91  Total                : 1.11
% 4.35/1.91  Index Insertion      : 0.00
% 4.35/1.91  Index Deletion       : 0.00
% 4.35/1.91  Index Matching       : 0.00
% 4.35/1.91  BG Taut test         : 0.00
%------------------------------------------------------------------------------
