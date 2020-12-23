%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:30 EST 2020

% Result     : Theorem 13.63s
% Output     : CNFRefutation 13.63s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 155 expanded)
%              Number of leaves         :   37 (  69 expanded)
%              Depth                    :   13
%              Number of atoms          :  144 ( 310 expanded)
%              Number of equality atoms :   19 (  48 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > k6_subset_1 > k4_xboole_0 > k4_tarski > k2_xboole_0 > #nlpp > k3_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_2 > #skF_9 > #skF_7 > #skF_8 > #skF_3 > #skF_1 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_119,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => ( r1_tarski(A,B)
             => r1_tarski(k3_relat_1(A),k3_relat_1(B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_relat_1)).

tff(f_109,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

tff(f_91,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_relat_1(A) = k2_xboole_0(k1_relat_1(A),k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).

tff(f_54,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_56,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k4_xboole_0(A,B),C)
     => r1_tarski(A,k2_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_87,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

tff(c_76,plain,(
    v1_relat_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_74,plain,(
    v1_relat_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_72,plain,(
    r1_tarski('#skF_8','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_66,plain,(
    ! [A_55,B_57] :
      ( r1_tarski(k2_relat_1(A_55),k2_relat_1(B_57))
      | ~ r1_tarski(A_55,B_57)
      | ~ v1_relat_1(B_57)
      | ~ v1_relat_1(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_199,plain,(
    ! [A_90] :
      ( k2_xboole_0(k1_relat_1(A_90),k2_relat_1(A_90)) = k3_relat_1(A_90)
      | ~ v1_relat_1(A_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_32,plain,(
    ! [A_14,C_16,B_15] :
      ( r1_tarski(A_14,k2_xboole_0(C_16,B_15))
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_205,plain,(
    ! [A_14,A_90] :
      ( r1_tarski(A_14,k3_relat_1(A_90))
      | ~ r1_tarski(A_14,k2_relat_1(A_90))
      | ~ v1_relat_1(A_90) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_199,c_32])).

tff(c_62,plain,(
    ! [A_51] :
      ( k2_xboole_0(k1_relat_1(A_51),k2_relat_1(A_51)) = k3_relat_1(A_51)
      | ~ v1_relat_1(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_328,plain,(
    ! [A_117,C_118,B_119] :
      ( r1_tarski(k2_xboole_0(A_117,C_118),B_119)
      | ~ r1_tarski(C_118,B_119)
      | ~ r1_tarski(A_117,B_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_5732,plain,(
    ! [A_355,B_356] :
      ( r1_tarski(k3_relat_1(A_355),B_356)
      | ~ r1_tarski(k2_relat_1(A_355),B_356)
      | ~ r1_tarski(k1_relat_1(A_355),B_356)
      | ~ v1_relat_1(A_355) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_328])).

tff(c_70,plain,(
    ~ r1_tarski(k3_relat_1('#skF_8'),k3_relat_1('#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_5807,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_8'),k3_relat_1('#skF_9'))
    | ~ r1_tarski(k1_relat_1('#skF_8'),k3_relat_1('#skF_9'))
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_5732,c_70])).

tff(c_5834,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_8'),k3_relat_1('#skF_9'))
    | ~ r1_tarski(k1_relat_1('#skF_8'),k3_relat_1('#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_5807])).

tff(c_6064,plain,(
    ~ r1_tarski(k1_relat_1('#skF_8'),k3_relat_1('#skF_9')) ),
    inference(splitLeft,[status(thm)],[c_5834])).

tff(c_34,plain,(
    ! [A_17] : r1_tarski(k1_xboole_0,A_17) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_1504,plain,(
    ! [A_207,B_208,C_209] :
      ( r2_hidden('#skF_2'(A_207,B_208,C_209),A_207)
      | r2_hidden('#skF_3'(A_207,B_208,C_209),C_209)
      | k4_xboole_0(A_207,B_208) = C_209 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_22,plain,(
    ! [A_6,B_7,C_8] :
      ( ~ r2_hidden('#skF_2'(A_6,B_7,C_8),B_7)
      | r2_hidden('#skF_3'(A_6,B_7,C_8),C_8)
      | k4_xboole_0(A_6,B_7) = C_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_1537,plain,(
    ! [A_207,C_209] :
      ( r2_hidden('#skF_3'(A_207,A_207,C_209),C_209)
      | k4_xboole_0(A_207,A_207) = C_209 ) ),
    inference(resolution,[status(thm)],[c_1504,c_22])).

tff(c_1565,plain,(
    ! [A_212,C_213] :
      ( r2_hidden('#skF_3'(A_212,A_212,C_213),C_213)
      | k4_xboole_0(A_212,A_212) = C_213 ) ),
    inference(resolution,[status(thm)],[c_1504,c_22])).

tff(c_36,plain,(
    ! [A_18] : k4_xboole_0(A_18,k1_xboole_0) = A_18 ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_176,plain,(
    ! [D_82,B_83,A_84] :
      ( ~ r2_hidden(D_82,B_83)
      | ~ r2_hidden(D_82,k4_xboole_0(A_84,B_83)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_183,plain,(
    ! [D_82,A_18] :
      ( ~ r2_hidden(D_82,k1_xboole_0)
      | ~ r2_hidden(D_82,A_18) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_176])).

tff(c_1583,plain,(
    ! [A_214,A_215] :
      ( ~ r2_hidden('#skF_3'(A_214,A_214,k1_xboole_0),A_215)
      | k4_xboole_0(A_214,A_214) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_1565,c_183])).

tff(c_1621,plain,(
    ! [A_218] : k4_xboole_0(A_218,A_218) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1537,c_1583])).

tff(c_38,plain,(
    ! [A_19,B_20,C_21] :
      ( r1_tarski(A_19,k2_xboole_0(B_20,C_21))
      | ~ r1_tarski(k4_xboole_0(A_19,B_20),C_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_1682,plain,(
    ! [A_218,C_21] :
      ( r1_tarski(A_218,k2_xboole_0(A_218,C_21))
      | ~ r1_tarski(k1_xboole_0,C_21) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1621,c_38])).

tff(c_1760,plain,(
    ! [A_220,C_221] : r1_tarski(A_220,k2_xboole_0(A_220,C_221)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_1682])).

tff(c_1797,plain,(
    ! [A_51] :
      ( r1_tarski(k1_relat_1(A_51),k3_relat_1(A_51))
      | ~ v1_relat_1(A_51) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_1760])).

tff(c_30,plain,(
    ! [B_13] : r1_tarski(B_13,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_40,plain,(
    ! [A_22,C_24,B_23] :
      ( r1_tarski(k2_xboole_0(A_22,C_24),B_23)
      | ~ r1_tarski(C_24,B_23)
      | ~ r1_tarski(A_22,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_26,plain,(
    ! [B_13,A_12] :
      ( B_13 = A_12
      | ~ r1_tarski(B_13,A_12)
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_2889,plain,(
    ! [A_275,C_276] :
      ( k2_xboole_0(A_275,C_276) = A_275
      | ~ r1_tarski(k2_xboole_0(A_275,C_276),A_275) ) ),
    inference(resolution,[status(thm)],[c_1760,c_26])).

tff(c_2925,plain,(
    ! [B_23,C_24] :
      ( k2_xboole_0(B_23,C_24) = B_23
      | ~ r1_tarski(C_24,B_23)
      | ~ r1_tarski(B_23,B_23) ) ),
    inference(resolution,[status(thm)],[c_40,c_2889])).

tff(c_2948,plain,(
    ! [B_277,C_278] :
      ( k2_xboole_0(B_277,C_278) = B_277
      | ~ r1_tarski(C_278,B_277) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_2925])).

tff(c_3003,plain,(
    ! [A_51] :
      ( k2_xboole_0(k3_relat_1(A_51),k1_relat_1(A_51)) = k3_relat_1(A_51)
      | ~ v1_relat_1(A_51) ) ),
    inference(resolution,[status(thm)],[c_1797,c_2948])).

tff(c_164,plain,(
    ! [A_80,B_81] :
      ( r2_hidden('#skF_1'(A_80,B_81),A_80)
      | r1_tarski(A_80,B_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_12,plain,(
    ! [D_11,A_6,B_7] :
      ( r2_hidden(D_11,A_6)
      | ~ r2_hidden(D_11,k4_xboole_0(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_175,plain,(
    ! [A_6,B_7,B_81] :
      ( r2_hidden('#skF_1'(k4_xboole_0(A_6,B_7),B_81),A_6)
      | r1_tarski(k4_xboole_0(A_6,B_7),B_81) ) ),
    inference(resolution,[status(thm)],[c_164,c_12])).

tff(c_561,plain,(
    ! [C_143,A_144] :
      ( r2_hidden(k4_tarski(C_143,'#skF_7'(A_144,k1_relat_1(A_144),C_143)),A_144)
      | ~ r2_hidden(C_143,k1_relat_1(A_144)) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_8740,plain,(
    ! [C_421,A_422,B_423] :
      ( r2_hidden(k4_tarski(C_421,'#skF_7'(A_422,k1_relat_1(A_422),C_421)),B_423)
      | ~ r1_tarski(A_422,B_423)
      | ~ r2_hidden(C_421,k1_relat_1(A_422)) ) ),
    inference(resolution,[status(thm)],[c_561,c_2])).

tff(c_52,plain,(
    ! [C_47,A_32,D_50] :
      ( r2_hidden(C_47,k1_relat_1(A_32))
      | ~ r2_hidden(k4_tarski(C_47,D_50),A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_36299,plain,(
    ! [C_873,B_874,A_875] :
      ( r2_hidden(C_873,k1_relat_1(B_874))
      | ~ r1_tarski(A_875,B_874)
      | ~ r2_hidden(C_873,k1_relat_1(A_875)) ) ),
    inference(resolution,[status(thm)],[c_8740,c_52])).

tff(c_37201,plain,(
    ! [C_878] :
      ( r2_hidden(C_878,k1_relat_1('#skF_9'))
      | ~ r2_hidden(C_878,k1_relat_1('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_72,c_36299])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_42588,plain,(
    ! [A_912] :
      ( r1_tarski(A_912,k1_relat_1('#skF_9'))
      | ~ r2_hidden('#skF_1'(A_912,k1_relat_1('#skF_9')),k1_relat_1('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_37201,c_4])).

tff(c_42605,plain,(
    ! [B_913] : r1_tarski(k4_xboole_0(k1_relat_1('#skF_8'),B_913),k1_relat_1('#skF_9')) ),
    inference(resolution,[status(thm)],[c_175,c_42588])).

tff(c_42713,plain,(
    ! [B_914] : r1_tarski(k1_relat_1('#skF_8'),k2_xboole_0(B_914,k1_relat_1('#skF_9'))) ),
    inference(resolution,[status(thm)],[c_42605,c_38])).

tff(c_42768,plain,
    ( r1_tarski(k1_relat_1('#skF_8'),k3_relat_1('#skF_9'))
    | ~ v1_relat_1('#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_3003,c_42713])).

tff(c_42810,plain,(
    r1_tarski(k1_relat_1('#skF_8'),k3_relat_1('#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_42768])).

tff(c_42812,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6064,c_42810])).

tff(c_42813,plain,(
    ~ r1_tarski(k2_relat_1('#skF_8'),k3_relat_1('#skF_9')) ),
    inference(splitRight,[status(thm)],[c_5834])).

tff(c_42817,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_8'),k2_relat_1('#skF_9'))
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_205,c_42813])).

tff(c_42820,plain,(
    ~ r1_tarski(k2_relat_1('#skF_8'),k2_relat_1('#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_42817])).

tff(c_42847,plain,
    ( ~ r1_tarski('#skF_8','#skF_9')
    | ~ v1_relat_1('#skF_9')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_66,c_42820])).

tff(c_42851,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_72,c_42847])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.32  % Computer   : n019.cluster.edu
% 0.13/0.32  % Model      : x86_64 x86_64
% 0.13/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.32  % Memory     : 8042.1875MB
% 0.13/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.32  % CPULimit   : 60
% 0.13/0.32  % DateTime   : Tue Dec  1 12:27:37 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.19/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 13.63/6.53  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.63/6.54  
% 13.63/6.54  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.63/6.54  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > k6_subset_1 > k4_xboole_0 > k4_tarski > k2_xboole_0 > #nlpp > k3_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_2 > #skF_9 > #skF_7 > #skF_8 > #skF_3 > #skF_1 > #skF_5 > #skF_4
% 13.63/6.54  
% 13.63/6.54  %Foreground sorts:
% 13.63/6.54  
% 13.63/6.54  
% 13.63/6.54  %Background operators:
% 13.63/6.54  
% 13.63/6.54  
% 13.63/6.54  %Foreground operators:
% 13.63/6.54  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 13.63/6.54  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 13.63/6.54  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 13.63/6.54  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 13.63/6.54  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 13.63/6.54  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 13.63/6.54  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 13.63/6.54  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 13.63/6.54  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 13.63/6.54  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 13.63/6.54  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 13.63/6.54  tff('#skF_9', type, '#skF_9': $i).
% 13.63/6.54  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 13.63/6.54  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 13.63/6.54  tff('#skF_8', type, '#skF_8': $i).
% 13.63/6.54  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 13.63/6.54  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 13.63/6.54  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 13.63/6.54  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 13.63/6.54  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 13.63/6.54  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 13.63/6.54  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 13.63/6.54  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 13.63/6.54  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 13.63/6.54  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 13.63/6.54  
% 13.63/6.56  tff(f_119, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => r1_tarski(k3_relat_1(A), k3_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_relat_1)).
% 13.63/6.56  tff(f_109, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_relat_1)).
% 13.63/6.56  tff(f_91, axiom, (![A]: (v1_relat_1(A) => (k3_relat_1(A) = k2_xboole_0(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_relat_1)).
% 13.63/6.56  tff(f_52, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_xboole_1)).
% 13.63/6.56  tff(f_66, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_xboole_1)).
% 13.63/6.56  tff(f_54, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 13.63/6.56  tff(f_42, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 13.63/6.56  tff(f_56, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 13.63/6.56  tff(f_60, axiom, (![A, B, C]: (r1_tarski(k4_xboole_0(A, B), C) => r1_tarski(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_xboole_1)).
% 13.63/6.56  tff(f_48, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 13.63/6.56  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 13.63/6.56  tff(f_87, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_relat_1)).
% 13.63/6.56  tff(c_76, plain, (v1_relat_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_119])).
% 13.63/6.56  tff(c_74, plain, (v1_relat_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_119])).
% 13.63/6.56  tff(c_72, plain, (r1_tarski('#skF_8', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_119])).
% 13.63/6.56  tff(c_66, plain, (![A_55, B_57]: (r1_tarski(k2_relat_1(A_55), k2_relat_1(B_57)) | ~r1_tarski(A_55, B_57) | ~v1_relat_1(B_57) | ~v1_relat_1(A_55))), inference(cnfTransformation, [status(thm)], [f_109])).
% 13.63/6.56  tff(c_199, plain, (![A_90]: (k2_xboole_0(k1_relat_1(A_90), k2_relat_1(A_90))=k3_relat_1(A_90) | ~v1_relat_1(A_90))), inference(cnfTransformation, [status(thm)], [f_91])).
% 13.63/6.56  tff(c_32, plain, (![A_14, C_16, B_15]: (r1_tarski(A_14, k2_xboole_0(C_16, B_15)) | ~r1_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_52])).
% 13.63/6.56  tff(c_205, plain, (![A_14, A_90]: (r1_tarski(A_14, k3_relat_1(A_90)) | ~r1_tarski(A_14, k2_relat_1(A_90)) | ~v1_relat_1(A_90))), inference(superposition, [status(thm), theory('equality')], [c_199, c_32])).
% 13.63/6.56  tff(c_62, plain, (![A_51]: (k2_xboole_0(k1_relat_1(A_51), k2_relat_1(A_51))=k3_relat_1(A_51) | ~v1_relat_1(A_51))), inference(cnfTransformation, [status(thm)], [f_91])).
% 13.63/6.56  tff(c_328, plain, (![A_117, C_118, B_119]: (r1_tarski(k2_xboole_0(A_117, C_118), B_119) | ~r1_tarski(C_118, B_119) | ~r1_tarski(A_117, B_119))), inference(cnfTransformation, [status(thm)], [f_66])).
% 13.63/6.56  tff(c_5732, plain, (![A_355, B_356]: (r1_tarski(k3_relat_1(A_355), B_356) | ~r1_tarski(k2_relat_1(A_355), B_356) | ~r1_tarski(k1_relat_1(A_355), B_356) | ~v1_relat_1(A_355))), inference(superposition, [status(thm), theory('equality')], [c_62, c_328])).
% 13.63/6.56  tff(c_70, plain, (~r1_tarski(k3_relat_1('#skF_8'), k3_relat_1('#skF_9'))), inference(cnfTransformation, [status(thm)], [f_119])).
% 13.63/6.56  tff(c_5807, plain, (~r1_tarski(k2_relat_1('#skF_8'), k3_relat_1('#skF_9')) | ~r1_tarski(k1_relat_1('#skF_8'), k3_relat_1('#skF_9')) | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_5732, c_70])).
% 13.63/6.56  tff(c_5834, plain, (~r1_tarski(k2_relat_1('#skF_8'), k3_relat_1('#skF_9')) | ~r1_tarski(k1_relat_1('#skF_8'), k3_relat_1('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_5807])).
% 13.63/6.56  tff(c_6064, plain, (~r1_tarski(k1_relat_1('#skF_8'), k3_relat_1('#skF_9'))), inference(splitLeft, [status(thm)], [c_5834])).
% 13.63/6.56  tff(c_34, plain, (![A_17]: (r1_tarski(k1_xboole_0, A_17))), inference(cnfTransformation, [status(thm)], [f_54])).
% 13.63/6.56  tff(c_1504, plain, (![A_207, B_208, C_209]: (r2_hidden('#skF_2'(A_207, B_208, C_209), A_207) | r2_hidden('#skF_3'(A_207, B_208, C_209), C_209) | k4_xboole_0(A_207, B_208)=C_209)), inference(cnfTransformation, [status(thm)], [f_42])).
% 13.63/6.56  tff(c_22, plain, (![A_6, B_7, C_8]: (~r2_hidden('#skF_2'(A_6, B_7, C_8), B_7) | r2_hidden('#skF_3'(A_6, B_7, C_8), C_8) | k4_xboole_0(A_6, B_7)=C_8)), inference(cnfTransformation, [status(thm)], [f_42])).
% 13.63/6.56  tff(c_1537, plain, (![A_207, C_209]: (r2_hidden('#skF_3'(A_207, A_207, C_209), C_209) | k4_xboole_0(A_207, A_207)=C_209)), inference(resolution, [status(thm)], [c_1504, c_22])).
% 13.63/6.56  tff(c_1565, plain, (![A_212, C_213]: (r2_hidden('#skF_3'(A_212, A_212, C_213), C_213) | k4_xboole_0(A_212, A_212)=C_213)), inference(resolution, [status(thm)], [c_1504, c_22])).
% 13.63/6.56  tff(c_36, plain, (![A_18]: (k4_xboole_0(A_18, k1_xboole_0)=A_18)), inference(cnfTransformation, [status(thm)], [f_56])).
% 13.63/6.56  tff(c_176, plain, (![D_82, B_83, A_84]: (~r2_hidden(D_82, B_83) | ~r2_hidden(D_82, k4_xboole_0(A_84, B_83)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 13.63/6.56  tff(c_183, plain, (![D_82, A_18]: (~r2_hidden(D_82, k1_xboole_0) | ~r2_hidden(D_82, A_18))), inference(superposition, [status(thm), theory('equality')], [c_36, c_176])).
% 13.63/6.56  tff(c_1583, plain, (![A_214, A_215]: (~r2_hidden('#skF_3'(A_214, A_214, k1_xboole_0), A_215) | k4_xboole_0(A_214, A_214)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1565, c_183])).
% 13.63/6.56  tff(c_1621, plain, (![A_218]: (k4_xboole_0(A_218, A_218)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1537, c_1583])).
% 13.63/6.56  tff(c_38, plain, (![A_19, B_20, C_21]: (r1_tarski(A_19, k2_xboole_0(B_20, C_21)) | ~r1_tarski(k4_xboole_0(A_19, B_20), C_21))), inference(cnfTransformation, [status(thm)], [f_60])).
% 13.63/6.56  tff(c_1682, plain, (![A_218, C_21]: (r1_tarski(A_218, k2_xboole_0(A_218, C_21)) | ~r1_tarski(k1_xboole_0, C_21))), inference(superposition, [status(thm), theory('equality')], [c_1621, c_38])).
% 13.63/6.56  tff(c_1760, plain, (![A_220, C_221]: (r1_tarski(A_220, k2_xboole_0(A_220, C_221)))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_1682])).
% 13.63/6.56  tff(c_1797, plain, (![A_51]: (r1_tarski(k1_relat_1(A_51), k3_relat_1(A_51)) | ~v1_relat_1(A_51))), inference(superposition, [status(thm), theory('equality')], [c_62, c_1760])).
% 13.63/6.56  tff(c_30, plain, (![B_13]: (r1_tarski(B_13, B_13))), inference(cnfTransformation, [status(thm)], [f_48])).
% 13.63/6.56  tff(c_40, plain, (![A_22, C_24, B_23]: (r1_tarski(k2_xboole_0(A_22, C_24), B_23) | ~r1_tarski(C_24, B_23) | ~r1_tarski(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_66])).
% 13.63/6.56  tff(c_26, plain, (![B_13, A_12]: (B_13=A_12 | ~r1_tarski(B_13, A_12) | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_48])).
% 13.63/6.56  tff(c_2889, plain, (![A_275, C_276]: (k2_xboole_0(A_275, C_276)=A_275 | ~r1_tarski(k2_xboole_0(A_275, C_276), A_275))), inference(resolution, [status(thm)], [c_1760, c_26])).
% 13.63/6.56  tff(c_2925, plain, (![B_23, C_24]: (k2_xboole_0(B_23, C_24)=B_23 | ~r1_tarski(C_24, B_23) | ~r1_tarski(B_23, B_23))), inference(resolution, [status(thm)], [c_40, c_2889])).
% 13.63/6.56  tff(c_2948, plain, (![B_277, C_278]: (k2_xboole_0(B_277, C_278)=B_277 | ~r1_tarski(C_278, B_277))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_2925])).
% 13.63/6.56  tff(c_3003, plain, (![A_51]: (k2_xboole_0(k3_relat_1(A_51), k1_relat_1(A_51))=k3_relat_1(A_51) | ~v1_relat_1(A_51))), inference(resolution, [status(thm)], [c_1797, c_2948])).
% 13.63/6.56  tff(c_164, plain, (![A_80, B_81]: (r2_hidden('#skF_1'(A_80, B_81), A_80) | r1_tarski(A_80, B_81))), inference(cnfTransformation, [status(thm)], [f_32])).
% 13.63/6.56  tff(c_12, plain, (![D_11, A_6, B_7]: (r2_hidden(D_11, A_6) | ~r2_hidden(D_11, k4_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 13.63/6.56  tff(c_175, plain, (![A_6, B_7, B_81]: (r2_hidden('#skF_1'(k4_xboole_0(A_6, B_7), B_81), A_6) | r1_tarski(k4_xboole_0(A_6, B_7), B_81))), inference(resolution, [status(thm)], [c_164, c_12])).
% 13.63/6.56  tff(c_561, plain, (![C_143, A_144]: (r2_hidden(k4_tarski(C_143, '#skF_7'(A_144, k1_relat_1(A_144), C_143)), A_144) | ~r2_hidden(C_143, k1_relat_1(A_144)))), inference(cnfTransformation, [status(thm)], [f_87])).
% 13.63/6.56  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 13.63/6.56  tff(c_8740, plain, (![C_421, A_422, B_423]: (r2_hidden(k4_tarski(C_421, '#skF_7'(A_422, k1_relat_1(A_422), C_421)), B_423) | ~r1_tarski(A_422, B_423) | ~r2_hidden(C_421, k1_relat_1(A_422)))), inference(resolution, [status(thm)], [c_561, c_2])).
% 13.63/6.56  tff(c_52, plain, (![C_47, A_32, D_50]: (r2_hidden(C_47, k1_relat_1(A_32)) | ~r2_hidden(k4_tarski(C_47, D_50), A_32))), inference(cnfTransformation, [status(thm)], [f_87])).
% 13.63/6.56  tff(c_36299, plain, (![C_873, B_874, A_875]: (r2_hidden(C_873, k1_relat_1(B_874)) | ~r1_tarski(A_875, B_874) | ~r2_hidden(C_873, k1_relat_1(A_875)))), inference(resolution, [status(thm)], [c_8740, c_52])).
% 13.63/6.56  tff(c_37201, plain, (![C_878]: (r2_hidden(C_878, k1_relat_1('#skF_9')) | ~r2_hidden(C_878, k1_relat_1('#skF_8')))), inference(resolution, [status(thm)], [c_72, c_36299])).
% 13.63/6.56  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 13.63/6.56  tff(c_42588, plain, (![A_912]: (r1_tarski(A_912, k1_relat_1('#skF_9')) | ~r2_hidden('#skF_1'(A_912, k1_relat_1('#skF_9')), k1_relat_1('#skF_8')))), inference(resolution, [status(thm)], [c_37201, c_4])).
% 13.63/6.56  tff(c_42605, plain, (![B_913]: (r1_tarski(k4_xboole_0(k1_relat_1('#skF_8'), B_913), k1_relat_1('#skF_9')))), inference(resolution, [status(thm)], [c_175, c_42588])).
% 13.63/6.56  tff(c_42713, plain, (![B_914]: (r1_tarski(k1_relat_1('#skF_8'), k2_xboole_0(B_914, k1_relat_1('#skF_9'))))), inference(resolution, [status(thm)], [c_42605, c_38])).
% 13.63/6.56  tff(c_42768, plain, (r1_tarski(k1_relat_1('#skF_8'), k3_relat_1('#skF_9')) | ~v1_relat_1('#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_3003, c_42713])).
% 13.63/6.56  tff(c_42810, plain, (r1_tarski(k1_relat_1('#skF_8'), k3_relat_1('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_42768])).
% 13.63/6.56  tff(c_42812, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6064, c_42810])).
% 13.63/6.56  tff(c_42813, plain, (~r1_tarski(k2_relat_1('#skF_8'), k3_relat_1('#skF_9'))), inference(splitRight, [status(thm)], [c_5834])).
% 13.63/6.56  tff(c_42817, plain, (~r1_tarski(k2_relat_1('#skF_8'), k2_relat_1('#skF_9')) | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_205, c_42813])).
% 13.63/6.56  tff(c_42820, plain, (~r1_tarski(k2_relat_1('#skF_8'), k2_relat_1('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_42817])).
% 13.63/6.56  tff(c_42847, plain, (~r1_tarski('#skF_8', '#skF_9') | ~v1_relat_1('#skF_9') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_66, c_42820])).
% 13.63/6.56  tff(c_42851, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_72, c_42847])).
% 13.63/6.56  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.63/6.56  
% 13.63/6.56  Inference rules
% 13.63/6.56  ----------------------
% 13.63/6.56  #Ref     : 0
% 13.63/6.56  #Sup     : 10699
% 13.63/6.56  #Fact    : 2
% 13.63/6.56  #Define  : 0
% 13.63/6.56  #Split   : 8
% 13.63/6.56  #Chain   : 0
% 13.63/6.56  #Close   : 0
% 13.63/6.56  
% 13.63/6.56  Ordering : KBO
% 13.63/6.56  
% 13.63/6.56  Simplification rules
% 13.63/6.56  ----------------------
% 13.63/6.56  #Subsume      : 3335
% 13.63/6.56  #Demod        : 7424
% 13.63/6.56  #Tautology    : 4004
% 13.63/6.56  #SimpNegUnit  : 85
% 13.63/6.56  #BackRed      : 16
% 13.63/6.56  
% 13.63/6.56  #Partial instantiations: 0
% 13.63/6.56  #Strategies tried      : 1
% 13.63/6.56  
% 13.63/6.56  Timing (in seconds)
% 13.63/6.56  ----------------------
% 13.63/6.56  Preprocessing        : 0.35
% 13.63/6.56  Parsing              : 0.18
% 13.63/6.56  CNF conversion       : 0.03
% 13.63/6.56  Main loop            : 5.44
% 13.63/6.56  Inferencing          : 1.03
% 13.63/6.56  Reduction            : 2.26
% 13.63/6.56  Demodulation         : 1.83
% 13.63/6.56  BG Simplification    : 0.10
% 13.63/6.56  Subsumption          : 1.71
% 13.63/6.56  Abstraction          : 0.17
% 13.63/6.56  MUC search           : 0.00
% 13.63/6.56  Cooper               : 0.00
% 13.63/6.56  Total                : 5.82
% 13.63/6.56  Index Insertion      : 0.00
% 13.63/6.56  Index Deletion       : 0.00
% 13.63/6.56  Index Matching       : 0.00
% 13.63/6.56  BG Taut test         : 0.00
%------------------------------------------------------------------------------
