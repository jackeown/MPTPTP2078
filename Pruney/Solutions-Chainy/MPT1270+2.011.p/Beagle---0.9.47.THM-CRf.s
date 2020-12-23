%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:56 EST 2020

% Result     : Theorem 4.34s
% Output     : CNFRefutation 4.34s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 209 expanded)
%              Number of leaves         :   39 (  91 expanded)
%              Depth                    :   11
%              Number of atoms          :  145 ( 423 expanded)
%              Number of equality atoms :   34 (  73 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_tops_1 > r2_hidden > r1_tarski > m1_subset_1 > l1_pre_topc > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k7_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1

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

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_125,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v2_tops_1(B,A)
            <=> r1_tarski(B,k2_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_tops_1)).

tff(f_115,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> k1_tops_1(A,B) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_tops_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_52,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_106,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).

tff(c_72,plain,
    ( ~ r1_tarski('#skF_5',k2_tops_1('#skF_4','#skF_5'))
    | ~ v2_tops_1('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_132,plain,(
    ~ v2_tops_1('#skF_5','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_72])).

tff(c_78,plain,
    ( v2_tops_1('#skF_5','#skF_4')
    | r1_tarski('#skF_5',k2_tops_1('#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_133,plain,(
    r1_tarski('#skF_5',k2_tops_1('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_132,c_78])).

tff(c_70,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_68,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_417,plain,(
    ! [B_136,A_137] :
      ( v2_tops_1(B_136,A_137)
      | k1_tops_1(A_137,B_136) != k1_xboole_0
      | ~ m1_subset_1(B_136,k1_zfmisc_1(u1_struct_0(A_137)))
      | ~ l1_pre_topc(A_137) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_423,plain,
    ( v2_tops_1('#skF_5','#skF_4')
    | k1_tops_1('#skF_4','#skF_5') != k1_xboole_0
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_417])).

tff(c_427,plain,
    ( v2_tops_1('#skF_5','#skF_4')
    | k1_tops_1('#skF_4','#skF_5') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_423])).

tff(c_428,plain,(
    k1_tops_1('#skF_4','#skF_5') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_132,c_427])).

tff(c_141,plain,(
    ! [A_81,B_82] :
      ( r2_hidden('#skF_1'(A_81,B_82),A_81)
      | r1_tarski(A_81,B_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_12,plain,(
    ! [D_11,A_6,B_7] :
      ( r2_hidden(D_11,A_6)
      | ~ r2_hidden(D_11,k4_xboole_0(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_146,plain,(
    ! [A_6,B_7,B_82] :
      ( r2_hidden('#skF_1'(k4_xboole_0(A_6,B_7),B_82),A_6)
      | r1_tarski(k4_xboole_0(A_6,B_7),B_82) ) ),
    inference(resolution,[status(thm)],[c_141,c_12])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_147,plain,(
    ! [D_83,B_84,A_85] :
      ( ~ r2_hidden(D_83,B_84)
      | ~ r2_hidden(D_83,k4_xboole_0(A_85,B_84)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_429,plain,(
    ! [A_138,B_139,B_140] :
      ( ~ r2_hidden('#skF_1'(k4_xboole_0(A_138,B_139),B_140),B_139)
      | r1_tarski(k4_xboole_0(A_138,B_139),B_140) ) ),
    inference(resolution,[status(thm)],[c_6,c_147])).

tff(c_453,plain,(
    ! [A_141,B_142] : r1_tarski(k4_xboole_0(A_141,A_141),B_142) ),
    inference(resolution,[status(thm)],[c_146,c_429])).

tff(c_34,plain,(
    ! [A_16] : r1_tarski(k1_xboole_0,A_16) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_109,plain,(
    ! [B_75,A_76] :
      ( B_75 = A_76
      | ~ r1_tarski(B_75,A_76)
      | ~ r1_tarski(A_76,B_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_118,plain,(
    ! [A_16] :
      ( k1_xboole_0 = A_16
      | ~ r1_tarski(A_16,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_34,c_109])).

tff(c_477,plain,(
    ! [A_141] : k4_xboole_0(A_141,A_141) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_453,c_118])).

tff(c_24,plain,(
    ! [A_6,B_7,C_8] :
      ( r2_hidden('#skF_2'(A_6,B_7,C_8),A_6)
      | r2_hidden('#skF_3'(A_6,B_7,C_8),C_8)
      | k4_xboole_0(A_6,B_7) = C_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_831,plain,(
    ! [A_196,B_197,C_198] :
      ( ~ r2_hidden('#skF_2'(A_196,B_197,C_198),B_197)
      | r2_hidden('#skF_3'(A_196,B_197,C_198),C_198)
      | k4_xboole_0(A_196,B_197) = C_198 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_834,plain,(
    ! [A_6,C_8] :
      ( r2_hidden('#skF_3'(A_6,A_6,C_8),C_8)
      | k4_xboole_0(A_6,A_6) = C_8 ) ),
    inference(resolution,[status(thm)],[c_24,c_831])).

tff(c_839,plain,(
    ! [A_6,C_8] :
      ( r2_hidden('#skF_3'(A_6,A_6,C_8),C_8)
      | k1_xboole_0 = C_8 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_477,c_834])).

tff(c_221,plain,(
    ! [A_105,B_106,C_107] :
      ( k7_subset_1(A_105,B_106,C_107) = k4_xboole_0(B_106,C_107)
      | ~ m1_subset_1(B_106,k1_zfmisc_1(A_105)) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_224,plain,(
    ! [C_107] : k7_subset_1(u1_struct_0('#skF_4'),'#skF_5',C_107) = k4_xboole_0('#skF_5',C_107) ),
    inference(resolution,[status(thm)],[c_68,c_221])).

tff(c_1037,plain,(
    ! [A_223,B_224] :
      ( k7_subset_1(u1_struct_0(A_223),B_224,k2_tops_1(A_223,B_224)) = k1_tops_1(A_223,B_224)
      | ~ m1_subset_1(B_224,k1_zfmisc_1(u1_struct_0(A_223)))
      | ~ l1_pre_topc(A_223) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_1041,plain,
    ( k7_subset_1(u1_struct_0('#skF_4'),'#skF_5',k2_tops_1('#skF_4','#skF_5')) = k1_tops_1('#skF_4','#skF_5')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_1037])).

tff(c_1045,plain,(
    k4_xboole_0('#skF_5',k2_tops_1('#skF_4','#skF_5')) = k1_tops_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_224,c_1041])).

tff(c_1106,plain,(
    ! [D_225] :
      ( r2_hidden(D_225,'#skF_5')
      | ~ r2_hidden(D_225,k1_tops_1('#skF_4','#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1045,c_12])).

tff(c_1118,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_3'(A_6,A_6,k1_tops_1('#skF_4','#skF_5')),'#skF_5')
      | k1_tops_1('#skF_4','#skF_5') = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_839,c_1106])).

tff(c_1159,plain,(
    ! [A_226] : r2_hidden('#skF_3'(A_226,A_226,k1_tops_1('#skF_4','#skF_5')),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_428,c_1118])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1238,plain,(
    ! [A_231,B_232] :
      ( r2_hidden('#skF_3'(A_231,A_231,k1_tops_1('#skF_4','#skF_5')),B_232)
      | ~ r1_tarski('#skF_5',B_232) ) ),
    inference(resolution,[status(thm)],[c_1159,c_2])).

tff(c_857,plain,(
    ! [A_201,C_202] :
      ( r2_hidden('#skF_3'(A_201,A_201,C_202),C_202)
      | k1_xboole_0 = C_202 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_477,c_834])).

tff(c_10,plain,(
    ! [D_11,B_7,A_6] :
      ( ~ r2_hidden(D_11,B_7)
      | ~ r2_hidden(D_11,k4_xboole_0(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_879,plain,(
    ! [A_201,A_6,B_7] :
      ( ~ r2_hidden('#skF_3'(A_201,A_201,k4_xboole_0(A_6,B_7)),B_7)
      | k4_xboole_0(A_6,B_7) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_857,c_10])).

tff(c_1055,plain,(
    ! [A_201] :
      ( ~ r2_hidden('#skF_3'(A_201,A_201,k1_tops_1('#skF_4','#skF_5')),k2_tops_1('#skF_4','#skF_5'))
      | k4_xboole_0('#skF_5',k2_tops_1('#skF_4','#skF_5')) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1045,c_879])).

tff(c_1097,plain,(
    ! [A_201] :
      ( ~ r2_hidden('#skF_3'(A_201,A_201,k1_tops_1('#skF_4','#skF_5')),k2_tops_1('#skF_4','#skF_5'))
      | k1_tops_1('#skF_4','#skF_5') = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1045,c_1055])).

tff(c_1098,plain,(
    ! [A_201] : ~ r2_hidden('#skF_3'(A_201,A_201,k1_tops_1('#skF_4','#skF_5')),k2_tops_1('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_428,c_1097])).

tff(c_1242,plain,(
    ~ r1_tarski('#skF_5',k2_tops_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_1238,c_1098])).

tff(c_1274,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_1242])).

tff(c_1275,plain,(
    ~ r1_tarski('#skF_5',k2_tops_1('#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_1276,plain,(
    v2_tops_1('#skF_5','#skF_4') ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_1603,plain,(
    ! [A_294,B_295] :
      ( k1_tops_1(A_294,B_295) = k1_xboole_0
      | ~ v2_tops_1(B_295,A_294)
      | ~ m1_subset_1(B_295,k1_zfmisc_1(u1_struct_0(A_294)))
      | ~ l1_pre_topc(A_294) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_1606,plain,
    ( k1_tops_1('#skF_4','#skF_5') = k1_xboole_0
    | ~ v2_tops_1('#skF_5','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_1603])).

tff(c_1609,plain,(
    k1_tops_1('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_1276,c_1606])).

tff(c_1356,plain,(
    ! [A_256,B_257,C_258] :
      ( k7_subset_1(A_256,B_257,C_258) = k4_xboole_0(B_257,C_258)
      | ~ m1_subset_1(B_257,k1_zfmisc_1(A_256)) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_1359,plain,(
    ! [C_258] : k7_subset_1(u1_struct_0('#skF_4'),'#skF_5',C_258) = k4_xboole_0('#skF_5',C_258) ),
    inference(resolution,[status(thm)],[c_68,c_1356])).

tff(c_2833,plain,(
    ! [A_421,B_422] :
      ( k7_subset_1(u1_struct_0(A_421),B_422,k2_tops_1(A_421,B_422)) = k1_tops_1(A_421,B_422)
      | ~ m1_subset_1(B_422,k1_zfmisc_1(u1_struct_0(A_421)))
      | ~ l1_pre_topc(A_421) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_2837,plain,
    ( k7_subset_1(u1_struct_0('#skF_4'),'#skF_5',k2_tops_1('#skF_4','#skF_5')) = k1_tops_1('#skF_4','#skF_5')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_2833])).

tff(c_2841,plain,(
    k4_xboole_0('#skF_5',k2_tops_1('#skF_4','#skF_5')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_1609,c_1359,c_2837])).

tff(c_1336,plain,(
    ! [D_253,A_254,B_255] :
      ( r2_hidden(D_253,k4_xboole_0(A_254,B_255))
      | r2_hidden(D_253,B_255)
      | ~ r2_hidden(D_253,A_254) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_1352,plain,(
    ! [D_253,B_2,A_254,B_255] :
      ( r2_hidden(D_253,B_2)
      | ~ r1_tarski(k4_xboole_0(A_254,B_255),B_2)
      | r2_hidden(D_253,B_255)
      | ~ r2_hidden(D_253,A_254) ) ),
    inference(resolution,[status(thm)],[c_1336,c_2])).

tff(c_2869,plain,(
    ! [D_253,B_2] :
      ( r2_hidden(D_253,B_2)
      | ~ r1_tarski(k1_xboole_0,B_2)
      | r2_hidden(D_253,k2_tops_1('#skF_4','#skF_5'))
      | ~ r2_hidden(D_253,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2841,c_1352])).

tff(c_2915,plain,(
    ! [D_253,B_2] :
      ( r2_hidden(D_253,B_2)
      | r2_hidden(D_253,k2_tops_1('#skF_4','#skF_5'))
      | ~ r2_hidden(D_253,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_2869])).

tff(c_3024,plain,(
    ! [D_425] :
      ( ~ r2_hidden(D_425,'#skF_5')
      | r2_hidden(D_425,k2_tops_1('#skF_4','#skF_5')) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_2915])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_3069,plain,(
    ! [A_428] :
      ( r1_tarski(A_428,k2_tops_1('#skF_4','#skF_5'))
      | ~ r2_hidden('#skF_1'(A_428,k2_tops_1('#skF_4','#skF_5')),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_3024,c_4])).

tff(c_3085,plain,(
    r1_tarski('#skF_5',k2_tops_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_6,c_3069])).

tff(c_3092,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1275,c_1275,c_3085])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 19:14:54 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.34/1.87  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.34/1.88  
% 4.34/1.88  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.34/1.88  %$ v2_tops_1 > r2_hidden > r1_tarski > m1_subset_1 > l1_pre_topc > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k7_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 4.34/1.88  
% 4.34/1.88  %Foreground sorts:
% 4.34/1.88  
% 4.34/1.88  
% 4.34/1.88  %Background operators:
% 4.34/1.88  
% 4.34/1.88  
% 4.34/1.88  %Foreground operators:
% 4.34/1.88  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.34/1.88  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.34/1.88  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.34/1.88  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 4.34/1.88  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.34/1.88  tff(v2_tops_1, type, v2_tops_1: ($i * $i) > $o).
% 4.34/1.88  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.34/1.88  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.34/1.88  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.34/1.88  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.34/1.88  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.34/1.88  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.34/1.88  tff('#skF_5', type, '#skF_5': $i).
% 4.34/1.88  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 4.34/1.88  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.34/1.88  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 4.34/1.88  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.34/1.88  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.34/1.88  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.34/1.88  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 4.34/1.88  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.34/1.88  tff('#skF_4', type, '#skF_4': $i).
% 4.34/1.88  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 4.34/1.88  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.34/1.88  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.34/1.88  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 4.34/1.88  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.34/1.88  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.34/1.88  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 4.34/1.88  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.34/1.88  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 4.34/1.88  
% 4.34/1.89  tff(f_125, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> r1_tarski(B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_tops_1)).
% 4.34/1.89  tff(f_115, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (k1_tops_1(A, B) = k1_xboole_0)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t84_tops_1)).
% 4.34/1.89  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 4.34/1.89  tff(f_42, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 4.34/1.89  tff(f_52, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 4.34/1.89  tff(f_48, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.34/1.89  tff(f_70, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 4.34/1.89  tff(f_106, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_tops_1)).
% 4.34/1.89  tff(c_72, plain, (~r1_tarski('#skF_5', k2_tops_1('#skF_4', '#skF_5')) | ~v2_tops_1('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_125])).
% 4.34/1.89  tff(c_132, plain, (~v2_tops_1('#skF_5', '#skF_4')), inference(splitLeft, [status(thm)], [c_72])).
% 4.34/1.89  tff(c_78, plain, (v2_tops_1('#skF_5', '#skF_4') | r1_tarski('#skF_5', k2_tops_1('#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_125])).
% 4.34/1.89  tff(c_133, plain, (r1_tarski('#skF_5', k2_tops_1('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_132, c_78])).
% 4.34/1.89  tff(c_70, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_125])).
% 4.34/1.89  tff(c_68, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_125])).
% 4.34/1.89  tff(c_417, plain, (![B_136, A_137]: (v2_tops_1(B_136, A_137) | k1_tops_1(A_137, B_136)!=k1_xboole_0 | ~m1_subset_1(B_136, k1_zfmisc_1(u1_struct_0(A_137))) | ~l1_pre_topc(A_137))), inference(cnfTransformation, [status(thm)], [f_115])).
% 4.34/1.89  tff(c_423, plain, (v2_tops_1('#skF_5', '#skF_4') | k1_tops_1('#skF_4', '#skF_5')!=k1_xboole_0 | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_68, c_417])).
% 4.34/1.89  tff(c_427, plain, (v2_tops_1('#skF_5', '#skF_4') | k1_tops_1('#skF_4', '#skF_5')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_70, c_423])).
% 4.34/1.89  tff(c_428, plain, (k1_tops_1('#skF_4', '#skF_5')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_132, c_427])).
% 4.34/1.89  tff(c_141, plain, (![A_81, B_82]: (r2_hidden('#skF_1'(A_81, B_82), A_81) | r1_tarski(A_81, B_82))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.34/1.89  tff(c_12, plain, (![D_11, A_6, B_7]: (r2_hidden(D_11, A_6) | ~r2_hidden(D_11, k4_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.34/1.89  tff(c_146, plain, (![A_6, B_7, B_82]: (r2_hidden('#skF_1'(k4_xboole_0(A_6, B_7), B_82), A_6) | r1_tarski(k4_xboole_0(A_6, B_7), B_82))), inference(resolution, [status(thm)], [c_141, c_12])).
% 4.34/1.89  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.34/1.89  tff(c_147, plain, (![D_83, B_84, A_85]: (~r2_hidden(D_83, B_84) | ~r2_hidden(D_83, k4_xboole_0(A_85, B_84)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.34/1.89  tff(c_429, plain, (![A_138, B_139, B_140]: (~r2_hidden('#skF_1'(k4_xboole_0(A_138, B_139), B_140), B_139) | r1_tarski(k4_xboole_0(A_138, B_139), B_140))), inference(resolution, [status(thm)], [c_6, c_147])).
% 4.34/1.89  tff(c_453, plain, (![A_141, B_142]: (r1_tarski(k4_xboole_0(A_141, A_141), B_142))), inference(resolution, [status(thm)], [c_146, c_429])).
% 4.34/1.89  tff(c_34, plain, (![A_16]: (r1_tarski(k1_xboole_0, A_16))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.34/1.89  tff(c_109, plain, (![B_75, A_76]: (B_75=A_76 | ~r1_tarski(B_75, A_76) | ~r1_tarski(A_76, B_75))), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.34/1.89  tff(c_118, plain, (![A_16]: (k1_xboole_0=A_16 | ~r1_tarski(A_16, k1_xboole_0))), inference(resolution, [status(thm)], [c_34, c_109])).
% 4.34/1.89  tff(c_477, plain, (![A_141]: (k4_xboole_0(A_141, A_141)=k1_xboole_0)), inference(resolution, [status(thm)], [c_453, c_118])).
% 4.34/1.89  tff(c_24, plain, (![A_6, B_7, C_8]: (r2_hidden('#skF_2'(A_6, B_7, C_8), A_6) | r2_hidden('#skF_3'(A_6, B_7, C_8), C_8) | k4_xboole_0(A_6, B_7)=C_8)), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.34/1.89  tff(c_831, plain, (![A_196, B_197, C_198]: (~r2_hidden('#skF_2'(A_196, B_197, C_198), B_197) | r2_hidden('#skF_3'(A_196, B_197, C_198), C_198) | k4_xboole_0(A_196, B_197)=C_198)), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.34/1.89  tff(c_834, plain, (![A_6, C_8]: (r2_hidden('#skF_3'(A_6, A_6, C_8), C_8) | k4_xboole_0(A_6, A_6)=C_8)), inference(resolution, [status(thm)], [c_24, c_831])).
% 4.34/1.89  tff(c_839, plain, (![A_6, C_8]: (r2_hidden('#skF_3'(A_6, A_6, C_8), C_8) | k1_xboole_0=C_8)), inference(demodulation, [status(thm), theory('equality')], [c_477, c_834])).
% 4.34/1.89  tff(c_221, plain, (![A_105, B_106, C_107]: (k7_subset_1(A_105, B_106, C_107)=k4_xboole_0(B_106, C_107) | ~m1_subset_1(B_106, k1_zfmisc_1(A_105)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.34/1.89  tff(c_224, plain, (![C_107]: (k7_subset_1(u1_struct_0('#skF_4'), '#skF_5', C_107)=k4_xboole_0('#skF_5', C_107))), inference(resolution, [status(thm)], [c_68, c_221])).
% 4.34/1.89  tff(c_1037, plain, (![A_223, B_224]: (k7_subset_1(u1_struct_0(A_223), B_224, k2_tops_1(A_223, B_224))=k1_tops_1(A_223, B_224) | ~m1_subset_1(B_224, k1_zfmisc_1(u1_struct_0(A_223))) | ~l1_pre_topc(A_223))), inference(cnfTransformation, [status(thm)], [f_106])).
% 4.34/1.89  tff(c_1041, plain, (k7_subset_1(u1_struct_0('#skF_4'), '#skF_5', k2_tops_1('#skF_4', '#skF_5'))=k1_tops_1('#skF_4', '#skF_5') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_68, c_1037])).
% 4.34/1.89  tff(c_1045, plain, (k4_xboole_0('#skF_5', k2_tops_1('#skF_4', '#skF_5'))=k1_tops_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_224, c_1041])).
% 4.34/1.89  tff(c_1106, plain, (![D_225]: (r2_hidden(D_225, '#skF_5') | ~r2_hidden(D_225, k1_tops_1('#skF_4', '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_1045, c_12])).
% 4.34/1.89  tff(c_1118, plain, (![A_6]: (r2_hidden('#skF_3'(A_6, A_6, k1_tops_1('#skF_4', '#skF_5')), '#skF_5') | k1_tops_1('#skF_4', '#skF_5')=k1_xboole_0)), inference(resolution, [status(thm)], [c_839, c_1106])).
% 4.34/1.89  tff(c_1159, plain, (![A_226]: (r2_hidden('#skF_3'(A_226, A_226, k1_tops_1('#skF_4', '#skF_5')), '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_428, c_1118])).
% 4.34/1.89  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.34/1.89  tff(c_1238, plain, (![A_231, B_232]: (r2_hidden('#skF_3'(A_231, A_231, k1_tops_1('#skF_4', '#skF_5')), B_232) | ~r1_tarski('#skF_5', B_232))), inference(resolution, [status(thm)], [c_1159, c_2])).
% 4.34/1.89  tff(c_857, plain, (![A_201, C_202]: (r2_hidden('#skF_3'(A_201, A_201, C_202), C_202) | k1_xboole_0=C_202)), inference(demodulation, [status(thm), theory('equality')], [c_477, c_834])).
% 4.34/1.89  tff(c_10, plain, (![D_11, B_7, A_6]: (~r2_hidden(D_11, B_7) | ~r2_hidden(D_11, k4_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.34/1.89  tff(c_879, plain, (![A_201, A_6, B_7]: (~r2_hidden('#skF_3'(A_201, A_201, k4_xboole_0(A_6, B_7)), B_7) | k4_xboole_0(A_6, B_7)=k1_xboole_0)), inference(resolution, [status(thm)], [c_857, c_10])).
% 4.34/1.89  tff(c_1055, plain, (![A_201]: (~r2_hidden('#skF_3'(A_201, A_201, k1_tops_1('#skF_4', '#skF_5')), k2_tops_1('#skF_4', '#skF_5')) | k4_xboole_0('#skF_5', k2_tops_1('#skF_4', '#skF_5'))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1045, c_879])).
% 4.34/1.89  tff(c_1097, plain, (![A_201]: (~r2_hidden('#skF_3'(A_201, A_201, k1_tops_1('#skF_4', '#skF_5')), k2_tops_1('#skF_4', '#skF_5')) | k1_tops_1('#skF_4', '#skF_5')=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1045, c_1055])).
% 4.34/1.89  tff(c_1098, plain, (![A_201]: (~r2_hidden('#skF_3'(A_201, A_201, k1_tops_1('#skF_4', '#skF_5')), k2_tops_1('#skF_4', '#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_428, c_1097])).
% 4.34/1.89  tff(c_1242, plain, (~r1_tarski('#skF_5', k2_tops_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_1238, c_1098])).
% 4.34/1.89  tff(c_1274, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_133, c_1242])).
% 4.34/1.89  tff(c_1275, plain, (~r1_tarski('#skF_5', k2_tops_1('#skF_4', '#skF_5'))), inference(splitRight, [status(thm)], [c_72])).
% 4.34/1.89  tff(c_1276, plain, (v2_tops_1('#skF_5', '#skF_4')), inference(splitRight, [status(thm)], [c_72])).
% 4.34/1.89  tff(c_1603, plain, (![A_294, B_295]: (k1_tops_1(A_294, B_295)=k1_xboole_0 | ~v2_tops_1(B_295, A_294) | ~m1_subset_1(B_295, k1_zfmisc_1(u1_struct_0(A_294))) | ~l1_pre_topc(A_294))), inference(cnfTransformation, [status(thm)], [f_115])).
% 4.34/1.89  tff(c_1606, plain, (k1_tops_1('#skF_4', '#skF_5')=k1_xboole_0 | ~v2_tops_1('#skF_5', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_68, c_1603])).
% 4.34/1.89  tff(c_1609, plain, (k1_tops_1('#skF_4', '#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_70, c_1276, c_1606])).
% 4.34/1.89  tff(c_1356, plain, (![A_256, B_257, C_258]: (k7_subset_1(A_256, B_257, C_258)=k4_xboole_0(B_257, C_258) | ~m1_subset_1(B_257, k1_zfmisc_1(A_256)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.34/1.89  tff(c_1359, plain, (![C_258]: (k7_subset_1(u1_struct_0('#skF_4'), '#skF_5', C_258)=k4_xboole_0('#skF_5', C_258))), inference(resolution, [status(thm)], [c_68, c_1356])).
% 4.34/1.89  tff(c_2833, plain, (![A_421, B_422]: (k7_subset_1(u1_struct_0(A_421), B_422, k2_tops_1(A_421, B_422))=k1_tops_1(A_421, B_422) | ~m1_subset_1(B_422, k1_zfmisc_1(u1_struct_0(A_421))) | ~l1_pre_topc(A_421))), inference(cnfTransformation, [status(thm)], [f_106])).
% 4.34/1.89  tff(c_2837, plain, (k7_subset_1(u1_struct_0('#skF_4'), '#skF_5', k2_tops_1('#skF_4', '#skF_5'))=k1_tops_1('#skF_4', '#skF_5') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_68, c_2833])).
% 4.34/1.89  tff(c_2841, plain, (k4_xboole_0('#skF_5', k2_tops_1('#skF_4', '#skF_5'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_70, c_1609, c_1359, c_2837])).
% 4.34/1.89  tff(c_1336, plain, (![D_253, A_254, B_255]: (r2_hidden(D_253, k4_xboole_0(A_254, B_255)) | r2_hidden(D_253, B_255) | ~r2_hidden(D_253, A_254))), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.34/1.89  tff(c_1352, plain, (![D_253, B_2, A_254, B_255]: (r2_hidden(D_253, B_2) | ~r1_tarski(k4_xboole_0(A_254, B_255), B_2) | r2_hidden(D_253, B_255) | ~r2_hidden(D_253, A_254))), inference(resolution, [status(thm)], [c_1336, c_2])).
% 4.34/1.89  tff(c_2869, plain, (![D_253, B_2]: (r2_hidden(D_253, B_2) | ~r1_tarski(k1_xboole_0, B_2) | r2_hidden(D_253, k2_tops_1('#skF_4', '#skF_5')) | ~r2_hidden(D_253, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_2841, c_1352])).
% 4.34/1.90  tff(c_2915, plain, (![D_253, B_2]: (r2_hidden(D_253, B_2) | r2_hidden(D_253, k2_tops_1('#skF_4', '#skF_5')) | ~r2_hidden(D_253, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_2869])).
% 4.34/1.90  tff(c_3024, plain, (![D_425]: (~r2_hidden(D_425, '#skF_5') | r2_hidden(D_425, k2_tops_1('#skF_4', '#skF_5')))), inference(factorization, [status(thm), theory('equality')], [c_2915])).
% 4.34/1.90  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.34/1.90  tff(c_3069, plain, (![A_428]: (r1_tarski(A_428, k2_tops_1('#skF_4', '#skF_5')) | ~r2_hidden('#skF_1'(A_428, k2_tops_1('#skF_4', '#skF_5')), '#skF_5'))), inference(resolution, [status(thm)], [c_3024, c_4])).
% 4.34/1.90  tff(c_3085, plain, (r1_tarski('#skF_5', k2_tops_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_6, c_3069])).
% 4.34/1.90  tff(c_3092, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1275, c_1275, c_3085])).
% 4.34/1.90  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.34/1.90  
% 4.34/1.90  Inference rules
% 4.34/1.90  ----------------------
% 4.34/1.90  #Ref     : 0
% 4.34/1.90  #Sup     : 668
% 4.34/1.90  #Fact    : 4
% 4.34/1.90  #Define  : 0
% 4.34/1.90  #Split   : 8
% 4.34/1.90  #Chain   : 0
% 4.34/1.90  #Close   : 0
% 4.34/1.90  
% 4.34/1.90  Ordering : KBO
% 4.34/1.90  
% 4.34/1.90  Simplification rules
% 4.34/1.90  ----------------------
% 4.34/1.90  #Subsume      : 148
% 4.34/1.90  #Demod        : 371
% 4.34/1.90  #Tautology    : 262
% 4.34/1.90  #SimpNegUnit  : 11
% 4.34/1.90  #BackRed      : 5
% 4.34/1.90  
% 4.34/1.90  #Partial instantiations: 0
% 4.34/1.90  #Strategies tried      : 1
% 4.34/1.90  
% 4.34/1.90  Timing (in seconds)
% 4.34/1.90  ----------------------
% 4.34/1.90  Preprocessing        : 0.40
% 4.34/1.90  Parsing              : 0.20
% 4.75/1.90  CNF conversion       : 0.03
% 4.75/1.90  Main loop            : 0.67
% 4.75/1.90  Inferencing          : 0.23
% 4.75/1.90  Reduction            : 0.21
% 4.75/1.90  Demodulation         : 0.15
% 4.75/1.90  BG Simplification    : 0.03
% 4.75/1.90  Subsumption          : 0.15
% 4.75/1.90  Abstraction          : 0.04
% 4.75/1.90  MUC search           : 0.00
% 4.75/1.90  Cooper               : 0.00
% 4.75/1.90  Total                : 1.12
% 4.75/1.90  Index Insertion      : 0.00
% 4.75/1.90  Index Deletion       : 0.00
% 4.75/1.90  Index Matching       : 0.00
% 4.75/1.90  BG Taut test         : 0.00
%------------------------------------------------------------------------------
