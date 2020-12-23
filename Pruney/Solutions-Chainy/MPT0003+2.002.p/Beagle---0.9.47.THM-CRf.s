%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:42:27 EST 2020

% Result     : Theorem 4.93s
% Output     : CNFRefutation 4.93s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 221 expanded)
%              Number of leaves         :   21 (  80 expanded)
%              Depth                    :    9
%              Number of atoms          :  165 ( 524 expanded)
%              Number of equality atoms :   33 (  74 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_8 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_44,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_64,negated_conjecture,(
    ~ ! [A,B] :
        ( ~ ( ~ r1_xboole_0(A,B)
            & ! [C] :
                ~ ( r2_hidden(C,A)
                  & r2_hidden(C,B) ) )
        & ~ ( ? [C] :
                ( r2_hidden(C,A)
                & r2_hidden(C,B) )
            & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_40,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_45,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(c_49,plain,(
    ! [A_21,B_22] :
      ( r1_xboole_0(A_21,B_22)
      | k3_xboole_0(A_21,B_22) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_38,plain,
    ( r2_hidden('#skF_6','#skF_5')
    | ~ r1_xboole_0('#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_47,plain,(
    ~ r1_xboole_0('#skF_7','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_57,plain,(
    k3_xboole_0('#skF_7','#skF_8') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_49,c_47])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2048,plain,(
    ! [D_138,B_139,A_140] :
      ( r2_hidden(D_138,B_139)
      | ~ r2_hidden(D_138,k3_xboole_0(A_140,B_139)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_2053,plain,(
    ! [A_140,B_139] :
      ( r2_hidden('#skF_1'(k3_xboole_0(A_140,B_139)),B_139)
      | v1_xboole_0(k3_xboole_0(A_140,B_139)) ) ),
    inference(resolution,[status(thm)],[c_4,c_2048])).

tff(c_2054,plain,(
    ! [D_141,A_142,B_143] :
      ( r2_hidden(D_141,A_142)
      | ~ r2_hidden(D_141,k3_xboole_0(A_142,B_143)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_2103,plain,(
    ! [A_152,B_153] :
      ( r2_hidden('#skF_1'(k3_xboole_0(A_152,B_153)),A_152)
      | v1_xboole_0(k3_xboole_0(A_152,B_153)) ) ),
    inference(resolution,[status(thm)],[c_4,c_2054])).

tff(c_34,plain,(
    ! [C_15] :
      ( r2_hidden('#skF_6','#skF_4')
      | ~ r2_hidden(C_15,'#skF_8')
      | ~ r2_hidden(C_15,'#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_2060,plain,(
    ! [C_15] :
      ( ~ r2_hidden(C_15,'#skF_8')
      | ~ r2_hidden(C_15,'#skF_7') ) ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_2140,plain,(
    ! [B_160] :
      ( ~ r2_hidden('#skF_1'(k3_xboole_0('#skF_7',B_160)),'#skF_8')
      | v1_xboole_0(k3_xboole_0('#skF_7',B_160)) ) ),
    inference(resolution,[status(thm)],[c_2103,c_2060])).

tff(c_2145,plain,(
    v1_xboole_0(k3_xboole_0('#skF_7','#skF_8')) ),
    inference(resolution,[status(thm)],[c_2053,c_2140])).

tff(c_28,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_22,plain,(
    ! [A_5,B_6,C_7] :
      ( r2_hidden('#skF_2'(A_5,B_6,C_7),A_5)
      | r2_hidden('#skF_3'(A_5,B_6,C_7),C_7)
      | k3_xboole_0(A_5,B_6) = C_7 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_2174,plain,(
    ! [A_164,B_165,C_166] :
      ( r2_hidden('#skF_2'(A_164,B_165,C_166),B_165)
      | r2_hidden('#skF_3'(A_164,B_165,C_166),C_166)
      | k3_xboole_0(A_164,B_165) = C_166 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_2440,plain,(
    ! [A_198,C_199] :
      ( ~ r2_hidden('#skF_2'(A_198,'#skF_7',C_199),'#skF_8')
      | r2_hidden('#skF_3'(A_198,'#skF_7',C_199),C_199)
      | k3_xboole_0(A_198,'#skF_7') = C_199 ) ),
    inference(resolution,[status(thm)],[c_2174,c_2060])).

tff(c_2445,plain,(
    ! [C_200] :
      ( r2_hidden('#skF_3'('#skF_8','#skF_7',C_200),C_200)
      | k3_xboole_0('#skF_8','#skF_7') = C_200 ) ),
    inference(resolution,[status(thm)],[c_22,c_2440])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2478,plain,(
    ! [C_201] :
      ( ~ v1_xboole_0(C_201)
      | k3_xboole_0('#skF_8','#skF_7') = C_201 ) ),
    inference(resolution,[status(thm)],[c_2445,c_2])).

tff(c_2519,plain,(
    k3_xboole_0('#skF_8','#skF_7') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_28,c_2478])).

tff(c_2477,plain,(
    ! [C_200] :
      ( ~ v1_xboole_0(C_200)
      | k3_xboole_0('#skF_8','#skF_7') = C_200 ) ),
    inference(resolution,[status(thm)],[c_2445,c_2])).

tff(c_2588,plain,(
    ! [C_202] :
      ( ~ v1_xboole_0(C_202)
      | k1_xboole_0 = C_202 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2519,c_2477])).

tff(c_2606,plain,(
    k3_xboole_0('#skF_7','#skF_8') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2145,c_2588])).

tff(c_2624,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_57,c_2606])).

tff(c_2625,plain,(
    r2_hidden('#skF_6','#skF_4') ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_66,plain,(
    ! [D_24,B_25,A_26] :
      ( r2_hidden(D_24,B_25)
      | ~ r2_hidden(D_24,k3_xboole_0(A_26,B_25)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_100,plain,(
    ! [A_35,B_36] :
      ( r2_hidden('#skF_1'(k3_xboole_0(A_35,B_36)),B_36)
      | v1_xboole_0(k3_xboole_0(A_35,B_36)) ) ),
    inference(resolution,[status(thm)],[c_4,c_66])).

tff(c_72,plain,(
    ! [D_27,A_28,B_29] :
      ( r2_hidden(D_27,A_28)
      | ~ r2_hidden(D_27,k3_xboole_0(A_28,B_29)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_78,plain,(
    ! [A_30,B_31] :
      ( r2_hidden('#skF_1'(k3_xboole_0(A_30,B_31)),A_30)
      | v1_xboole_0(k3_xboole_0(A_30,B_31)) ) ),
    inference(resolution,[status(thm)],[c_4,c_72])).

tff(c_32,plain,(
    ! [C_15] :
      ( r2_hidden('#skF_6','#skF_5')
      | ~ r2_hidden(C_15,'#skF_8')
      | ~ r2_hidden(C_15,'#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_58,plain,(
    ! [C_15] :
      ( ~ r2_hidden(C_15,'#skF_8')
      | ~ r2_hidden(C_15,'#skF_7') ) ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_96,plain,(
    ! [B_31] :
      ( ~ r2_hidden('#skF_1'(k3_xboole_0('#skF_7',B_31)),'#skF_8')
      | v1_xboole_0(k3_xboole_0('#skF_7',B_31)) ) ),
    inference(resolution,[status(thm)],[c_78,c_58])).

tff(c_120,plain,(
    v1_xboole_0(k3_xboole_0('#skF_7','#skF_8')) ),
    inference(resolution,[status(thm)],[c_100,c_96])).

tff(c_394,plain,(
    ! [A_82,B_83,C_84] :
      ( r2_hidden('#skF_2'(A_82,B_83,C_84),B_83)
      | r2_hidden('#skF_3'(A_82,B_83,C_84),C_84)
      | k3_xboole_0(A_82,B_83) = C_84 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_1451,plain,(
    ! [A_118,C_119] :
      ( ~ r2_hidden('#skF_2'(A_118,'#skF_7',C_119),'#skF_8')
      | r2_hidden('#skF_3'(A_118,'#skF_7',C_119),C_119)
      | k3_xboole_0(A_118,'#skF_7') = C_119 ) ),
    inference(resolution,[status(thm)],[c_394,c_58])).

tff(c_1740,plain,(
    ! [C_135] :
      ( r2_hidden('#skF_3'('#skF_8','#skF_7',C_135),C_135)
      | k3_xboole_0('#skF_8','#skF_7') = C_135 ) ),
    inference(resolution,[status(thm)],[c_22,c_1451])).

tff(c_1822,plain,(
    ! [C_136] :
      ( ~ v1_xboole_0(C_136)
      | k3_xboole_0('#skF_8','#skF_7') = C_136 ) ),
    inference(resolution,[status(thm)],[c_1740,c_2])).

tff(c_1891,plain,(
    k3_xboole_0('#skF_8','#skF_7') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_28,c_1822])).

tff(c_1821,plain,(
    ! [C_135] :
      ( ~ v1_xboole_0(C_135)
      | k3_xboole_0('#skF_8','#skF_7') = C_135 ) ),
    inference(resolution,[status(thm)],[c_1740,c_2])).

tff(c_1981,plain,(
    ! [C_137] :
      ( ~ v1_xboole_0(C_137)
      | k1_xboole_0 = C_137 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1891,c_1821])).

tff(c_2020,plain,(
    k3_xboole_0('#skF_7','#skF_8') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_120,c_1981])).

tff(c_2042,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_57,c_2020])).

tff(c_2043,plain,(
    r2_hidden('#skF_6','#skF_5') ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_2659,plain,(
    ! [A_208,B_209] :
      ( r2_hidden('#skF_1'(k3_xboole_0(A_208,B_209)),A_208)
      | v1_xboole_0(k3_xboole_0(A_208,B_209)) ) ),
    inference(resolution,[status(thm)],[c_4,c_2054])).

tff(c_30,plain,(
    ! [C_15] :
      ( r1_xboole_0('#skF_4','#skF_5')
      | ~ r2_hidden(C_15,'#skF_8')
      | ~ r2_hidden(C_15,'#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_2630,plain,(
    ! [C_15] :
      ( ~ r2_hidden(C_15,'#skF_8')
      | ~ r2_hidden(C_15,'#skF_7') ) ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_2680,plain,(
    ! [B_212] :
      ( ~ r2_hidden('#skF_1'(k3_xboole_0('#skF_7',B_212)),'#skF_8')
      | v1_xboole_0(k3_xboole_0('#skF_7',B_212)) ) ),
    inference(resolution,[status(thm)],[c_2659,c_2630])).

tff(c_2685,plain,(
    v1_xboole_0(k3_xboole_0('#skF_7','#skF_8')) ),
    inference(resolution,[status(thm)],[c_2053,c_2680])).

tff(c_2799,plain,(
    ! [A_233,B_234,C_235] :
      ( r2_hidden('#skF_2'(A_233,B_234,C_235),B_234)
      | r2_hidden('#skF_3'(A_233,B_234,C_235),C_235)
      | k3_xboole_0(A_233,B_234) = C_235 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_3507,plain,(
    ! [A_277,C_278] :
      ( ~ r2_hidden('#skF_2'(A_277,'#skF_7',C_278),'#skF_8')
      | r2_hidden('#skF_3'(A_277,'#skF_7',C_278),C_278)
      | k3_xboole_0(A_277,'#skF_7') = C_278 ) ),
    inference(resolution,[status(thm)],[c_2799,c_2630])).

tff(c_3663,plain,(
    ! [C_292] :
      ( r2_hidden('#skF_3'('#skF_8','#skF_7',C_292),C_292)
      | k3_xboole_0('#skF_8','#skF_7') = C_292 ) ),
    inference(resolution,[status(thm)],[c_22,c_3507])).

tff(c_3709,plain,(
    ! [C_293] :
      ( ~ v1_xboole_0(C_293)
      | k3_xboole_0('#skF_8','#skF_7') = C_293 ) ),
    inference(resolution,[status(thm)],[c_3663,c_2])).

tff(c_3754,plain,(
    k3_xboole_0('#skF_8','#skF_7') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_28,c_3709])).

tff(c_3708,plain,(
    ! [C_292] :
      ( ~ v1_xboole_0(C_292)
      | k3_xboole_0('#skF_8','#skF_7') = C_292 ) ),
    inference(resolution,[status(thm)],[c_3663,c_2])).

tff(c_3830,plain,(
    ! [C_294] :
      ( ~ v1_xboole_0(C_294)
      | k1_xboole_0 = C_294 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3754,c_3708])).

tff(c_3851,plain,(
    k3_xboole_0('#skF_7','#skF_8') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2685,c_3830])).

tff(c_3870,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_57,c_3851])).

tff(c_3871,plain,(
    r1_xboole_0('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_24,plain,(
    ! [A_11,B_12] :
      ( k3_xboole_0(A_11,B_12) = k1_xboole_0
      | ~ r1_xboole_0(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_3875,plain,(
    k3_xboole_0('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_3871,c_24])).

tff(c_6,plain,(
    ! [D_10,A_5,B_6] :
      ( r2_hidden(D_10,k3_xboole_0(A_5,B_6))
      | ~ r2_hidden(D_10,B_6)
      | ~ r2_hidden(D_10,A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_3916,plain,(
    ! [D_300] :
      ( r2_hidden(D_300,k1_xboole_0)
      | ~ r2_hidden(D_300,'#skF_5')
      | ~ r2_hidden(D_300,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3875,c_6])).

tff(c_3925,plain,(
    ! [D_300] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(D_300,'#skF_5')
      | ~ r2_hidden(D_300,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_3916,c_2])).

tff(c_3931,plain,(
    ! [D_301] :
      ( ~ r2_hidden(D_301,'#skF_5')
      | ~ r2_hidden(D_301,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_3925])).

tff(c_3934,plain,(
    ~ r2_hidden('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_2043,c_3931])).

tff(c_3942,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2625,c_3934])).

tff(c_3944,plain,(
    r1_xboole_0('#skF_7','#skF_8') ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_40,plain,
    ( r2_hidden('#skF_6','#skF_4')
    | ~ r1_xboole_0('#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_3950,plain,(
    r2_hidden('#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3944,c_40])).

tff(c_3943,plain,(
    r2_hidden('#skF_6','#skF_5') ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_36,plain,
    ( r1_xboole_0('#skF_4','#skF_5')
    | ~ r1_xboole_0('#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_3956,plain,(
    r1_xboole_0('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3944,c_36])).

tff(c_3957,plain,(
    ! [A_302,B_303] :
      ( k3_xboole_0(A_302,B_303) = k1_xboole_0
      | ~ r1_xboole_0(A_302,B_303) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_3964,plain,(
    k3_xboole_0('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_3956,c_3957])).

tff(c_4143,plain,(
    ! [D_325,A_326,B_327] :
      ( r2_hidden(D_325,k3_xboole_0(A_326,B_327))
      | ~ r2_hidden(D_325,B_327)
      | ~ r2_hidden(D_325,A_326) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_4202,plain,(
    ! [D_330] :
      ( r2_hidden(D_330,k1_xboole_0)
      | ~ r2_hidden(D_330,'#skF_5')
      | ~ r2_hidden(D_330,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3964,c_4143])).

tff(c_4217,plain,(
    ! [D_330] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(D_330,'#skF_5')
      | ~ r2_hidden(D_330,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_4202,c_2])).

tff(c_4225,plain,(
    ! [D_331] :
      ( ~ r2_hidden(D_331,'#skF_5')
      | ~ r2_hidden(D_331,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_4217])).

tff(c_4239,plain,(
    ~ r2_hidden('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_3943,c_4225])).

tff(c_4250,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3950,c_4239])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:25:32 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.93/2.19  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.93/2.20  
% 4.93/2.20  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.93/2.20  %$ r2_hidden > r1_xboole_0 > v1_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_8 > #skF_4 > #skF_3
% 4.93/2.20  
% 4.93/2.20  %Foreground sorts:
% 4.93/2.20  
% 4.93/2.20  
% 4.93/2.20  %Background operators:
% 4.93/2.20  
% 4.93/2.20  
% 4.93/2.20  %Foreground operators:
% 4.93/2.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.93/2.20  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.93/2.20  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.93/2.20  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.93/2.20  tff('#skF_7', type, '#skF_7': $i).
% 4.93/2.20  tff('#skF_5', type, '#skF_5': $i).
% 4.93/2.20  tff('#skF_6', type, '#skF_6': $i).
% 4.93/2.20  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.93/2.20  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.93/2.20  tff('#skF_8', type, '#skF_8': $i).
% 4.93/2.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.93/2.20  tff('#skF_4', type, '#skF_4': $i).
% 4.93/2.20  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 4.93/2.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.93/2.20  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.93/2.20  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.93/2.20  
% 4.93/2.22  tff(f_44, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 4.93/2.22  tff(f_64, negated_conjecture, ~(![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 4.93/2.22  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 4.93/2.22  tff(f_40, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 4.93/2.22  tff(f_45, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 4.93/2.22  tff(c_49, plain, (![A_21, B_22]: (r1_xboole_0(A_21, B_22) | k3_xboole_0(A_21, B_22)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.93/2.22  tff(c_38, plain, (r2_hidden('#skF_6', '#skF_5') | ~r1_xboole_0('#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.93/2.22  tff(c_47, plain, (~r1_xboole_0('#skF_7', '#skF_8')), inference(splitLeft, [status(thm)], [c_38])).
% 4.93/2.22  tff(c_57, plain, (k3_xboole_0('#skF_7', '#skF_8')!=k1_xboole_0), inference(resolution, [status(thm)], [c_49, c_47])).
% 4.93/2.22  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.93/2.22  tff(c_2048, plain, (![D_138, B_139, A_140]: (r2_hidden(D_138, B_139) | ~r2_hidden(D_138, k3_xboole_0(A_140, B_139)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.93/2.22  tff(c_2053, plain, (![A_140, B_139]: (r2_hidden('#skF_1'(k3_xboole_0(A_140, B_139)), B_139) | v1_xboole_0(k3_xboole_0(A_140, B_139)))), inference(resolution, [status(thm)], [c_4, c_2048])).
% 4.93/2.22  tff(c_2054, plain, (![D_141, A_142, B_143]: (r2_hidden(D_141, A_142) | ~r2_hidden(D_141, k3_xboole_0(A_142, B_143)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.93/2.22  tff(c_2103, plain, (![A_152, B_153]: (r2_hidden('#skF_1'(k3_xboole_0(A_152, B_153)), A_152) | v1_xboole_0(k3_xboole_0(A_152, B_153)))), inference(resolution, [status(thm)], [c_4, c_2054])).
% 4.93/2.22  tff(c_34, plain, (![C_15]: (r2_hidden('#skF_6', '#skF_4') | ~r2_hidden(C_15, '#skF_8') | ~r2_hidden(C_15, '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.93/2.22  tff(c_2060, plain, (![C_15]: (~r2_hidden(C_15, '#skF_8') | ~r2_hidden(C_15, '#skF_7'))), inference(splitLeft, [status(thm)], [c_34])).
% 4.93/2.22  tff(c_2140, plain, (![B_160]: (~r2_hidden('#skF_1'(k3_xboole_0('#skF_7', B_160)), '#skF_8') | v1_xboole_0(k3_xboole_0('#skF_7', B_160)))), inference(resolution, [status(thm)], [c_2103, c_2060])).
% 4.93/2.22  tff(c_2145, plain, (v1_xboole_0(k3_xboole_0('#skF_7', '#skF_8'))), inference(resolution, [status(thm)], [c_2053, c_2140])).
% 4.93/2.22  tff(c_28, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.93/2.22  tff(c_22, plain, (![A_5, B_6, C_7]: (r2_hidden('#skF_2'(A_5, B_6, C_7), A_5) | r2_hidden('#skF_3'(A_5, B_6, C_7), C_7) | k3_xboole_0(A_5, B_6)=C_7)), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.93/2.22  tff(c_2174, plain, (![A_164, B_165, C_166]: (r2_hidden('#skF_2'(A_164, B_165, C_166), B_165) | r2_hidden('#skF_3'(A_164, B_165, C_166), C_166) | k3_xboole_0(A_164, B_165)=C_166)), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.93/2.22  tff(c_2440, plain, (![A_198, C_199]: (~r2_hidden('#skF_2'(A_198, '#skF_7', C_199), '#skF_8') | r2_hidden('#skF_3'(A_198, '#skF_7', C_199), C_199) | k3_xboole_0(A_198, '#skF_7')=C_199)), inference(resolution, [status(thm)], [c_2174, c_2060])).
% 4.93/2.22  tff(c_2445, plain, (![C_200]: (r2_hidden('#skF_3'('#skF_8', '#skF_7', C_200), C_200) | k3_xboole_0('#skF_8', '#skF_7')=C_200)), inference(resolution, [status(thm)], [c_22, c_2440])).
% 4.93/2.22  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.93/2.22  tff(c_2478, plain, (![C_201]: (~v1_xboole_0(C_201) | k3_xboole_0('#skF_8', '#skF_7')=C_201)), inference(resolution, [status(thm)], [c_2445, c_2])).
% 4.93/2.22  tff(c_2519, plain, (k3_xboole_0('#skF_8', '#skF_7')=k1_xboole_0), inference(resolution, [status(thm)], [c_28, c_2478])).
% 4.93/2.22  tff(c_2477, plain, (![C_200]: (~v1_xboole_0(C_200) | k3_xboole_0('#skF_8', '#skF_7')=C_200)), inference(resolution, [status(thm)], [c_2445, c_2])).
% 4.93/2.22  tff(c_2588, plain, (![C_202]: (~v1_xboole_0(C_202) | k1_xboole_0=C_202)), inference(demodulation, [status(thm), theory('equality')], [c_2519, c_2477])).
% 4.93/2.22  tff(c_2606, plain, (k3_xboole_0('#skF_7', '#skF_8')=k1_xboole_0), inference(resolution, [status(thm)], [c_2145, c_2588])).
% 4.93/2.22  tff(c_2624, plain, $false, inference(negUnitSimplification, [status(thm)], [c_57, c_2606])).
% 4.93/2.22  tff(c_2625, plain, (r2_hidden('#skF_6', '#skF_4')), inference(splitRight, [status(thm)], [c_34])).
% 4.93/2.22  tff(c_66, plain, (![D_24, B_25, A_26]: (r2_hidden(D_24, B_25) | ~r2_hidden(D_24, k3_xboole_0(A_26, B_25)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.93/2.22  tff(c_100, plain, (![A_35, B_36]: (r2_hidden('#skF_1'(k3_xboole_0(A_35, B_36)), B_36) | v1_xboole_0(k3_xboole_0(A_35, B_36)))), inference(resolution, [status(thm)], [c_4, c_66])).
% 4.93/2.22  tff(c_72, plain, (![D_27, A_28, B_29]: (r2_hidden(D_27, A_28) | ~r2_hidden(D_27, k3_xboole_0(A_28, B_29)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.93/2.22  tff(c_78, plain, (![A_30, B_31]: (r2_hidden('#skF_1'(k3_xboole_0(A_30, B_31)), A_30) | v1_xboole_0(k3_xboole_0(A_30, B_31)))), inference(resolution, [status(thm)], [c_4, c_72])).
% 4.93/2.22  tff(c_32, plain, (![C_15]: (r2_hidden('#skF_6', '#skF_5') | ~r2_hidden(C_15, '#skF_8') | ~r2_hidden(C_15, '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.93/2.22  tff(c_58, plain, (![C_15]: (~r2_hidden(C_15, '#skF_8') | ~r2_hidden(C_15, '#skF_7'))), inference(splitLeft, [status(thm)], [c_32])).
% 4.93/2.22  tff(c_96, plain, (![B_31]: (~r2_hidden('#skF_1'(k3_xboole_0('#skF_7', B_31)), '#skF_8') | v1_xboole_0(k3_xboole_0('#skF_7', B_31)))), inference(resolution, [status(thm)], [c_78, c_58])).
% 4.93/2.22  tff(c_120, plain, (v1_xboole_0(k3_xboole_0('#skF_7', '#skF_8'))), inference(resolution, [status(thm)], [c_100, c_96])).
% 4.93/2.22  tff(c_394, plain, (![A_82, B_83, C_84]: (r2_hidden('#skF_2'(A_82, B_83, C_84), B_83) | r2_hidden('#skF_3'(A_82, B_83, C_84), C_84) | k3_xboole_0(A_82, B_83)=C_84)), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.93/2.22  tff(c_1451, plain, (![A_118, C_119]: (~r2_hidden('#skF_2'(A_118, '#skF_7', C_119), '#skF_8') | r2_hidden('#skF_3'(A_118, '#skF_7', C_119), C_119) | k3_xboole_0(A_118, '#skF_7')=C_119)), inference(resolution, [status(thm)], [c_394, c_58])).
% 4.93/2.22  tff(c_1740, plain, (![C_135]: (r2_hidden('#skF_3'('#skF_8', '#skF_7', C_135), C_135) | k3_xboole_0('#skF_8', '#skF_7')=C_135)), inference(resolution, [status(thm)], [c_22, c_1451])).
% 4.93/2.22  tff(c_1822, plain, (![C_136]: (~v1_xboole_0(C_136) | k3_xboole_0('#skF_8', '#skF_7')=C_136)), inference(resolution, [status(thm)], [c_1740, c_2])).
% 4.93/2.22  tff(c_1891, plain, (k3_xboole_0('#skF_8', '#skF_7')=k1_xboole_0), inference(resolution, [status(thm)], [c_28, c_1822])).
% 4.93/2.22  tff(c_1821, plain, (![C_135]: (~v1_xboole_0(C_135) | k3_xboole_0('#skF_8', '#skF_7')=C_135)), inference(resolution, [status(thm)], [c_1740, c_2])).
% 4.93/2.22  tff(c_1981, plain, (![C_137]: (~v1_xboole_0(C_137) | k1_xboole_0=C_137)), inference(demodulation, [status(thm), theory('equality')], [c_1891, c_1821])).
% 4.93/2.22  tff(c_2020, plain, (k3_xboole_0('#skF_7', '#skF_8')=k1_xboole_0), inference(resolution, [status(thm)], [c_120, c_1981])).
% 4.93/2.22  tff(c_2042, plain, $false, inference(negUnitSimplification, [status(thm)], [c_57, c_2020])).
% 4.93/2.22  tff(c_2043, plain, (r2_hidden('#skF_6', '#skF_5')), inference(splitRight, [status(thm)], [c_32])).
% 4.93/2.22  tff(c_2659, plain, (![A_208, B_209]: (r2_hidden('#skF_1'(k3_xboole_0(A_208, B_209)), A_208) | v1_xboole_0(k3_xboole_0(A_208, B_209)))), inference(resolution, [status(thm)], [c_4, c_2054])).
% 4.93/2.22  tff(c_30, plain, (![C_15]: (r1_xboole_0('#skF_4', '#skF_5') | ~r2_hidden(C_15, '#skF_8') | ~r2_hidden(C_15, '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.93/2.22  tff(c_2630, plain, (![C_15]: (~r2_hidden(C_15, '#skF_8') | ~r2_hidden(C_15, '#skF_7'))), inference(splitLeft, [status(thm)], [c_30])).
% 4.93/2.22  tff(c_2680, plain, (![B_212]: (~r2_hidden('#skF_1'(k3_xboole_0('#skF_7', B_212)), '#skF_8') | v1_xboole_0(k3_xboole_0('#skF_7', B_212)))), inference(resolution, [status(thm)], [c_2659, c_2630])).
% 4.93/2.22  tff(c_2685, plain, (v1_xboole_0(k3_xboole_0('#skF_7', '#skF_8'))), inference(resolution, [status(thm)], [c_2053, c_2680])).
% 4.93/2.22  tff(c_2799, plain, (![A_233, B_234, C_235]: (r2_hidden('#skF_2'(A_233, B_234, C_235), B_234) | r2_hidden('#skF_3'(A_233, B_234, C_235), C_235) | k3_xboole_0(A_233, B_234)=C_235)), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.93/2.22  tff(c_3507, plain, (![A_277, C_278]: (~r2_hidden('#skF_2'(A_277, '#skF_7', C_278), '#skF_8') | r2_hidden('#skF_3'(A_277, '#skF_7', C_278), C_278) | k3_xboole_0(A_277, '#skF_7')=C_278)), inference(resolution, [status(thm)], [c_2799, c_2630])).
% 4.93/2.22  tff(c_3663, plain, (![C_292]: (r2_hidden('#skF_3'('#skF_8', '#skF_7', C_292), C_292) | k3_xboole_0('#skF_8', '#skF_7')=C_292)), inference(resolution, [status(thm)], [c_22, c_3507])).
% 4.93/2.22  tff(c_3709, plain, (![C_293]: (~v1_xboole_0(C_293) | k3_xboole_0('#skF_8', '#skF_7')=C_293)), inference(resolution, [status(thm)], [c_3663, c_2])).
% 4.93/2.22  tff(c_3754, plain, (k3_xboole_0('#skF_8', '#skF_7')=k1_xboole_0), inference(resolution, [status(thm)], [c_28, c_3709])).
% 4.93/2.22  tff(c_3708, plain, (![C_292]: (~v1_xboole_0(C_292) | k3_xboole_0('#skF_8', '#skF_7')=C_292)), inference(resolution, [status(thm)], [c_3663, c_2])).
% 4.93/2.22  tff(c_3830, plain, (![C_294]: (~v1_xboole_0(C_294) | k1_xboole_0=C_294)), inference(demodulation, [status(thm), theory('equality')], [c_3754, c_3708])).
% 4.93/2.22  tff(c_3851, plain, (k3_xboole_0('#skF_7', '#skF_8')=k1_xboole_0), inference(resolution, [status(thm)], [c_2685, c_3830])).
% 4.93/2.22  tff(c_3870, plain, $false, inference(negUnitSimplification, [status(thm)], [c_57, c_3851])).
% 4.93/2.22  tff(c_3871, plain, (r1_xboole_0('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_30])).
% 4.93/2.22  tff(c_24, plain, (![A_11, B_12]: (k3_xboole_0(A_11, B_12)=k1_xboole_0 | ~r1_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.93/2.22  tff(c_3875, plain, (k3_xboole_0('#skF_4', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_3871, c_24])).
% 4.93/2.22  tff(c_6, plain, (![D_10, A_5, B_6]: (r2_hidden(D_10, k3_xboole_0(A_5, B_6)) | ~r2_hidden(D_10, B_6) | ~r2_hidden(D_10, A_5))), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.93/2.22  tff(c_3916, plain, (![D_300]: (r2_hidden(D_300, k1_xboole_0) | ~r2_hidden(D_300, '#skF_5') | ~r2_hidden(D_300, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_3875, c_6])).
% 4.93/2.22  tff(c_3925, plain, (![D_300]: (~v1_xboole_0(k1_xboole_0) | ~r2_hidden(D_300, '#skF_5') | ~r2_hidden(D_300, '#skF_4'))), inference(resolution, [status(thm)], [c_3916, c_2])).
% 4.93/2.22  tff(c_3931, plain, (![D_301]: (~r2_hidden(D_301, '#skF_5') | ~r2_hidden(D_301, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_3925])).
% 4.93/2.22  tff(c_3934, plain, (~r2_hidden('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_2043, c_3931])).
% 4.93/2.22  tff(c_3942, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2625, c_3934])).
% 4.93/2.22  tff(c_3944, plain, (r1_xboole_0('#skF_7', '#skF_8')), inference(splitRight, [status(thm)], [c_38])).
% 4.93/2.22  tff(c_40, plain, (r2_hidden('#skF_6', '#skF_4') | ~r1_xboole_0('#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.93/2.22  tff(c_3950, plain, (r2_hidden('#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3944, c_40])).
% 4.93/2.22  tff(c_3943, plain, (r2_hidden('#skF_6', '#skF_5')), inference(splitRight, [status(thm)], [c_38])).
% 4.93/2.22  tff(c_36, plain, (r1_xboole_0('#skF_4', '#skF_5') | ~r1_xboole_0('#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.93/2.22  tff(c_3956, plain, (r1_xboole_0('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_3944, c_36])).
% 4.93/2.22  tff(c_3957, plain, (![A_302, B_303]: (k3_xboole_0(A_302, B_303)=k1_xboole_0 | ~r1_xboole_0(A_302, B_303))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.93/2.22  tff(c_3964, plain, (k3_xboole_0('#skF_4', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_3956, c_3957])).
% 4.93/2.22  tff(c_4143, plain, (![D_325, A_326, B_327]: (r2_hidden(D_325, k3_xboole_0(A_326, B_327)) | ~r2_hidden(D_325, B_327) | ~r2_hidden(D_325, A_326))), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.93/2.22  tff(c_4202, plain, (![D_330]: (r2_hidden(D_330, k1_xboole_0) | ~r2_hidden(D_330, '#skF_5') | ~r2_hidden(D_330, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_3964, c_4143])).
% 4.93/2.22  tff(c_4217, plain, (![D_330]: (~v1_xboole_0(k1_xboole_0) | ~r2_hidden(D_330, '#skF_5') | ~r2_hidden(D_330, '#skF_4'))), inference(resolution, [status(thm)], [c_4202, c_2])).
% 4.93/2.22  tff(c_4225, plain, (![D_331]: (~r2_hidden(D_331, '#skF_5') | ~r2_hidden(D_331, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_4217])).
% 4.93/2.22  tff(c_4239, plain, (~r2_hidden('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_3943, c_4225])).
% 4.93/2.22  tff(c_4250, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3950, c_4239])).
% 4.93/2.22  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.93/2.22  
% 4.93/2.22  Inference rules
% 4.93/2.22  ----------------------
% 4.93/2.22  #Ref     : 0
% 4.93/2.22  #Sup     : 964
% 4.93/2.22  #Fact    : 0
% 4.93/2.22  #Define  : 0
% 4.93/2.22  #Split   : 11
% 4.93/2.22  #Chain   : 0
% 4.93/2.22  #Close   : 0
% 4.93/2.22  
% 4.93/2.22  Ordering : KBO
% 4.93/2.22  
% 4.93/2.22  Simplification rules
% 4.93/2.22  ----------------------
% 4.93/2.22  #Subsume      : 137
% 4.93/2.22  #Demod        : 467
% 4.93/2.22  #Tautology    : 310
% 4.93/2.22  #SimpNegUnit  : 24
% 4.93/2.22  #BackRed      : 29
% 4.93/2.22  
% 4.93/2.22  #Partial instantiations: 0
% 4.93/2.22  #Strategies tried      : 1
% 4.93/2.22  
% 4.93/2.22  Timing (in seconds)
% 4.93/2.22  ----------------------
% 4.93/2.22  Preprocessing        : 0.44
% 4.93/2.22  Parsing              : 0.22
% 4.93/2.22  CNF conversion       : 0.04
% 4.93/2.22  Main loop            : 0.85
% 4.93/2.22  Inferencing          : 0.30
% 4.93/2.22  Reduction            : 0.24
% 4.93/2.22  Demodulation         : 0.17
% 4.93/2.22  BG Simplification    : 0.06
% 4.93/2.22  Subsumption          : 0.19
% 4.93/2.22  Abstraction          : 0.04
% 4.93/2.22  MUC search           : 0.00
% 4.93/2.22  Cooper               : 0.00
% 4.93/2.22  Total                : 1.33
% 4.93/2.22  Index Insertion      : 0.00
% 4.93/2.22  Index Deletion       : 0.00
% 4.93/2.22  Index Matching       : 0.00
% 4.93/2.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
