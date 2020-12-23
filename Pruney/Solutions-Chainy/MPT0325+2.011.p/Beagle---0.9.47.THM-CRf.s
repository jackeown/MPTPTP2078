%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:22 EST 2020

% Result     : Theorem 6.04s
% Output     : CNFRefutation 6.43s
% Verified   : 
% Statistics : Number of formulae       :  130 ( 327 expanded)
%              Number of leaves         :   31 ( 116 expanded)
%              Depth                    :   13
%              Number of atoms          :  181 ( 610 expanded)
%              Number of equality atoms :   77 ( 186 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_33,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_94,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( r1_tarski(k2_zfmisc_1(A,B),k2_zfmisc_1(C,D))
       => ( k2_zfmisc_1(A,B) = k1_xboole_0
          | ( r1_tarski(A,C)
            & r1_tarski(B,D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_zfmisc_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_67,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_75,axiom,(
    ! [A,B,C,D] :
      ( ( r1_xboole_0(A,B)
        | r1_xboole_0(C,D) )
     => r1_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,D)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t127_zfmisc_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_69,axiom,(
    ! [A,B,C,D] : k2_zfmisc_1(k3_xboole_0(A,B),k3_xboole_0(C,D)) = k3_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_zfmisc_1)).

tff(f_85,axiom,(
    ! [A,B,C,D] :
      ( k2_zfmisc_1(A,B) = k2_zfmisc_1(C,D)
     => ( A = k1_xboole_0
        | B = k1_xboole_0
        | ( A = C
          & B = D ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t134_zfmisc_1)).

tff(f_61,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_41,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(c_6,plain,(
    ! [A_3] :
      ( v1_xboole_0(A_3)
      | r2_hidden('#skF_1'(A_3),A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_40,plain,(
    k2_zfmisc_1('#skF_3','#skF_4') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_1779,plain,(
    ! [A_153,B_154] :
      ( r1_tarski(A_153,B_154)
      | k4_xboole_0(A_153,B_154) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_96,plain,(
    ! [A_43,B_44] :
      ( r1_tarski(A_43,B_44)
      | k4_xboole_0(A_43,B_44) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_38,plain,
    ( ~ r1_tarski('#skF_4','#skF_6')
    | ~ r1_tarski('#skF_3','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_90,plain,(
    ~ r1_tarski('#skF_3','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_104,plain,(
    k4_xboole_0('#skF_3','#skF_5') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_96,c_90])).

tff(c_26,plain,(
    ! [A_21] : k5_xboole_0(A_21,A_21) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_10,plain,(
    ! [A_7,B_8] :
      ( r1_xboole_0(A_7,B_8)
      | k3_xboole_0(A_7,B_8) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_329,plain,(
    ! [A_81,B_82,C_83,D_84] :
      ( ~ r1_xboole_0(A_81,B_82)
      | r1_xboole_0(k2_zfmisc_1(A_81,C_83),k2_zfmisc_1(B_82,D_84)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_8,plain,(
    ! [A_7,B_8] :
      ( k3_xboole_0(A_7,B_8) = k1_xboole_0
      | ~ r1_xboole_0(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_400,plain,(
    ! [A_99,C_100,B_101,D_102] :
      ( k3_xboole_0(k2_zfmisc_1(A_99,C_100),k2_zfmisc_1(B_101,D_102)) = k1_xboole_0
      | ~ r1_xboole_0(A_99,B_101) ) ),
    inference(resolution,[status(thm)],[c_329,c_8])).

tff(c_42,plain,(
    r1_tarski(k2_zfmisc_1('#skF_3','#skF_4'),k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_111,plain,(
    ! [A_49,B_50] :
      ( k3_xboole_0(A_49,B_50) = A_49
      | ~ r1_tarski(A_49,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_119,plain,(
    k3_xboole_0(k2_zfmisc_1('#skF_3','#skF_4'),k2_zfmisc_1('#skF_5','#skF_6')) = k2_zfmisc_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_111])).

tff(c_411,plain,
    ( k2_zfmisc_1('#skF_3','#skF_4') = k1_xboole_0
    | ~ r1_xboole_0('#skF_3','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_400,c_119])).

tff(c_459,plain,(
    ~ r1_xboole_0('#skF_3','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_411])).

tff(c_470,plain,(
    k3_xboole_0('#skF_3','#skF_5') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_459])).

tff(c_341,plain,(
    ! [C_85,D_86,A_87,B_88] :
      ( ~ r1_xboole_0(C_85,D_86)
      | r1_xboole_0(k2_zfmisc_1(A_87,C_85),k2_zfmisc_1(B_88,D_86)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_477,plain,(
    ! [A_107,C_108,B_109,D_110] :
      ( k3_xboole_0(k2_zfmisc_1(A_107,C_108),k2_zfmisc_1(B_109,D_110)) = k1_xboole_0
      | ~ r1_xboole_0(C_108,D_110) ) ),
    inference(resolution,[status(thm)],[c_341,c_8])).

tff(c_491,plain,
    ( k2_zfmisc_1('#skF_3','#skF_4') = k1_xboole_0
    | ~ r1_xboole_0('#skF_4','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_477,c_119])).

tff(c_543,plain,(
    ~ r1_xboole_0('#skF_4','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_491])).

tff(c_555,plain,(
    k3_xboole_0('#skF_4','#skF_6') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_543])).

tff(c_774,plain,(
    ! [A_123,C_124,B_125,D_126] : k3_xboole_0(k2_zfmisc_1(A_123,C_124),k2_zfmisc_1(B_125,D_126)) = k2_zfmisc_1(k3_xboole_0(A_123,B_125),k3_xboole_0(C_124,D_126)) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_785,plain,(
    k2_zfmisc_1(k3_xboole_0('#skF_3','#skF_5'),k3_xboole_0('#skF_4','#skF_6')) = k2_zfmisc_1('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_774,c_119])).

tff(c_36,plain,(
    ! [C_32,A_30,B_31,D_33] :
      ( C_32 = A_30
      | k1_xboole_0 = B_31
      | k1_xboole_0 = A_30
      | k2_zfmisc_1(C_32,D_33) != k2_zfmisc_1(A_30,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_852,plain,(
    ! [C_32,D_33] :
      ( k3_xboole_0('#skF_3','#skF_5') = C_32
      | k3_xboole_0('#skF_4','#skF_6') = k1_xboole_0
      | k3_xboole_0('#skF_3','#skF_5') = k1_xboole_0
      | k2_zfmisc_1(C_32,D_33) != k2_zfmisc_1('#skF_3','#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_785,c_36])).

tff(c_882,plain,(
    ! [C_32,D_33] :
      ( k3_xboole_0('#skF_3','#skF_5') = C_32
      | k2_zfmisc_1(C_32,D_33) != k2_zfmisc_1('#skF_3','#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_470,c_555,c_852])).

tff(c_1679,plain,(
    k3_xboole_0('#skF_3','#skF_5') = '#skF_3' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_882])).

tff(c_22,plain,(
    ! [A_17,B_18] : k5_xboole_0(A_17,k3_xboole_0(A_17,B_18)) = k4_xboole_0(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1764,plain,(
    k5_xboole_0('#skF_3','#skF_3') = k4_xboole_0('#skF_3','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1679,c_22])).

tff(c_1774,plain,(
    k4_xboole_0('#skF_3','#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_1764])).

tff(c_1776,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_104,c_1774])).

tff(c_1777,plain,(
    ~ r1_tarski('#skF_4','#skF_6') ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_1783,plain,(
    k4_xboole_0('#skF_4','#skF_6') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1779,c_1777])).

tff(c_1778,plain,(
    r1_tarski('#skF_3','#skF_5') ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_1811,plain,(
    ! [A_161,B_162] :
      ( k3_xboole_0(A_161,B_162) = A_161
      | ~ r1_tarski(A_161,B_162) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1823,plain,(
    k3_xboole_0('#skF_3','#skF_5') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_1778,c_1811])).

tff(c_1847,plain,(
    ! [A_165,B_166,C_167] :
      ( ~ r1_xboole_0(A_165,B_166)
      | ~ r2_hidden(C_167,k3_xboole_0(A_165,B_166)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1850,plain,(
    ! [C_167] :
      ( ~ r1_xboole_0('#skF_3','#skF_5')
      | ~ r2_hidden(C_167,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1823,c_1847])).

tff(c_1862,plain,(
    ~ r1_xboole_0('#skF_3','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_1850])).

tff(c_1865,plain,(
    k3_xboole_0('#skF_3','#skF_5') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_1862])).

tff(c_1867,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1823,c_1865])).

tff(c_2119,plain,(
    ! [C_195,D_196,A_197,B_198] :
      ( ~ r1_xboole_0(C_195,D_196)
      | r1_xboole_0(k2_zfmisc_1(A_197,C_195),k2_zfmisc_1(B_198,D_196)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_1822,plain,(
    k3_xboole_0(k2_zfmisc_1('#skF_3','#skF_4'),k2_zfmisc_1('#skF_5','#skF_6')) = k2_zfmisc_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_1811])).

tff(c_1919,plain,(
    ! [A_172,B_173] :
      ( r2_hidden('#skF_2'(A_172,B_173),k3_xboole_0(A_172,B_173))
      | r1_xboole_0(A_172,B_173) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_4,plain,(
    ! [B_6,A_3] :
      ( ~ r2_hidden(B_6,A_3)
      | ~ v1_xboole_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1945,plain,(
    ! [A_174,B_175] :
      ( ~ v1_xboole_0(k3_xboole_0(A_174,B_175))
      | r1_xboole_0(A_174,B_175) ) ),
    inference(resolution,[status(thm)],[c_1919,c_4])).

tff(c_1954,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4'))
    | r1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4'),k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1822,c_1945])).

tff(c_1967,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_1954])).

tff(c_1879,plain,(
    ! [A_168,B_169] :
      ( ~ r1_xboole_0(A_168,B_169)
      | v1_xboole_0(k3_xboole_0(A_168,B_169)) ) ),
    inference(resolution,[status(thm)],[c_6,c_1847])).

tff(c_1885,plain,
    ( ~ r1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4'),k2_zfmisc_1('#skF_5','#skF_6'))
    | v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1822,c_1879])).

tff(c_2066,plain,(
    ~ r1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4'),k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_1967,c_1885])).

tff(c_2131,plain,(
    ~ r1_xboole_0('#skF_4','#skF_6') ),
    inference(resolution,[status(thm)],[c_2119,c_2066])).

tff(c_2143,plain,(
    k3_xboole_0('#skF_4','#skF_6') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_2131])).

tff(c_2570,plain,(
    ! [A_235,C_236,B_237,D_238] : k3_xboole_0(k2_zfmisc_1(A_235,C_236),k2_zfmisc_1(B_237,D_238)) = k2_zfmisc_1(k3_xboole_0(A_235,B_237),k3_xboole_0(C_236,D_238)) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_2602,plain,(
    k2_zfmisc_1(k3_xboole_0('#skF_3','#skF_5'),k3_xboole_0('#skF_4','#skF_6')) = k2_zfmisc_1('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2570,c_1822])).

tff(c_2629,plain,(
    k2_zfmisc_1('#skF_3',k3_xboole_0('#skF_4','#skF_6')) = k2_zfmisc_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1823,c_2602])).

tff(c_34,plain,(
    ! [D_33,B_31,A_30,C_32] :
      ( D_33 = B_31
      | k1_xboole_0 = B_31
      | k1_xboole_0 = A_30
      | k2_zfmisc_1(C_32,D_33) != k2_zfmisc_1(A_30,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_2644,plain,(
    ! [D_33,C_32] :
      ( k3_xboole_0('#skF_4','#skF_6') = D_33
      | k3_xboole_0('#skF_4','#skF_6') = k1_xboole_0
      | k1_xboole_0 = '#skF_3'
      | k2_zfmisc_1(C_32,D_33) != k2_zfmisc_1('#skF_3','#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2629,c_34])).

tff(c_2679,plain,(
    ! [D_33,C_32] :
      ( k3_xboole_0('#skF_4','#skF_6') = D_33
      | k2_zfmisc_1(C_32,D_33) != k2_zfmisc_1('#skF_3','#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_1867,c_2143,c_2644])).

tff(c_2698,plain,(
    k3_xboole_0('#skF_4','#skF_6') = '#skF_4' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_2679])).

tff(c_2739,plain,(
    k5_xboole_0('#skF_4','#skF_4') = k4_xboole_0('#skF_4','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_2698,c_22])).

tff(c_2747,plain,(
    k4_xboole_0('#skF_4','#skF_6') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_2739])).

tff(c_2749,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1783,c_2747])).

tff(c_2751,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_1954])).

tff(c_12,plain,(
    ! [A_9] :
      ( k1_xboole_0 = A_9
      | ~ v1_xboole_0(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2754,plain,(
    k2_zfmisc_1('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2751,c_12])).

tff(c_2758,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_2754])).

tff(c_2761,plain,(
    ! [C_243] : ~ r2_hidden(C_243,'#skF_3') ),
    inference(splitRight,[status(thm)],[c_1850])).

tff(c_2766,plain,(
    v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_6,c_2761])).

tff(c_2770,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_2766,c_12])).

tff(c_2785,plain,(
    k2_zfmisc_1('#skF_3','#skF_4') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2770,c_40])).

tff(c_2759,plain,(
    ! [C_167] : ~ r2_hidden(C_167,'#skF_3') ),
    inference(splitRight,[status(thm)],[c_1850])).

tff(c_2760,plain,(
    r1_xboole_0('#skF_3','#skF_5') ),
    inference(splitRight,[status(thm)],[c_1850])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_2807,plain,(
    ! [A_250,B_251] :
      ( ~ r1_xboole_0(A_250,B_251)
      | v1_xboole_0(k3_xboole_0(A_250,B_251)) ) ),
    inference(resolution,[status(thm)],[c_6,c_1847])).

tff(c_2823,plain,(
    ! [A_252,B_253] :
      ( ~ r1_xboole_0(A_252,B_253)
      | v1_xboole_0(k3_xboole_0(B_253,A_252)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_2807])).

tff(c_2783,plain,(
    ! [A_9] :
      ( A_9 = '#skF_3'
      | ~ v1_xboole_0(A_9) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2770,c_12])).

tff(c_2898,plain,(
    ! [B_266,A_267] :
      ( k3_xboole_0(B_266,A_267) = '#skF_3'
      | ~ r1_xboole_0(A_267,B_266) ) ),
    inference(resolution,[status(thm)],[c_2823,c_2783])).

tff(c_2913,plain,(
    k3_xboole_0('#skF_5','#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_2760,c_2898])).

tff(c_2950,plain,(
    ! [A_268,B_269] :
      ( r2_hidden('#skF_2'(A_268,B_269),k3_xboole_0(A_268,B_269))
      | r1_xboole_0(A_268,B_269) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_2959,plain,
    ( r2_hidden('#skF_2'('#skF_5','#skF_3'),'#skF_3')
    | r1_xboole_0('#skF_5','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2913,c_2950])).

tff(c_2974,plain,(
    r1_xboole_0('#skF_5','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_2759,c_2959])).

tff(c_32,plain,(
    ! [A_26,B_27,C_28,D_29] :
      ( ~ r1_xboole_0(A_26,B_27)
      | r1_xboole_0(k2_zfmisc_1(A_26,C_28),k2_zfmisc_1(B_27,D_29)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_2816,plain,(
    ! [A_1,B_2] :
      ( ~ r1_xboole_0(A_1,B_2)
      | v1_xboole_0(k3_xboole_0(B_2,A_1)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_2807])).

tff(c_2991,plain,(
    ! [A_270,B_271] :
      ( ~ v1_xboole_0(k3_xboole_0(A_270,B_271))
      | r1_xboole_0(A_270,B_271) ) ),
    inference(resolution,[status(thm)],[c_2950,c_4])).

tff(c_3023,plain,(
    ! [B_272,A_273] :
      ( r1_xboole_0(B_272,A_273)
      | ~ r1_xboole_0(A_273,B_272) ) ),
    inference(resolution,[status(thm)],[c_2816,c_2991])).

tff(c_3037,plain,(
    ! [B_27,D_29,A_26,C_28] :
      ( r1_xboole_0(k2_zfmisc_1(B_27,D_29),k2_zfmisc_1(A_26,C_28))
      | ~ r1_xboole_0(A_26,B_27) ) ),
    inference(resolution,[status(thm)],[c_32,c_3023])).

tff(c_2997,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4'))
    | r1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4'),k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1822,c_2991])).

tff(c_3236,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_2997])).

tff(c_1861,plain,(
    ! [A_165,B_166] :
      ( ~ r1_xboole_0(A_165,B_166)
      | v1_xboole_0(k3_xboole_0(A_165,B_166)) ) ),
    inference(resolution,[status(thm)],[c_6,c_1847])).

tff(c_2855,plain,
    ( ~ r1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4'),k2_zfmisc_1('#skF_5','#skF_6'))
    | v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1822,c_1861])).

tff(c_3444,plain,(
    ~ r1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4'),k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_3236,c_2855])).

tff(c_3450,plain,(
    ~ r1_xboole_0('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_3037,c_3444])).

tff(c_3467,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2974,c_3450])).

tff(c_3469,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_2997])).

tff(c_3472,plain,(
    k2_zfmisc_1('#skF_3','#skF_4') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_3469,c_2783])).

tff(c_3476,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2785,c_3472])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:53:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.04/2.60  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.43/2.62  
% 6.43/2.62  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.43/2.62  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2
% 6.43/2.62  
% 6.43/2.62  %Foreground sorts:
% 6.43/2.62  
% 6.43/2.62  
% 6.43/2.62  %Background operators:
% 6.43/2.62  
% 6.43/2.62  
% 6.43/2.62  %Foreground operators:
% 6.43/2.62  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.43/2.62  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.43/2.62  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.43/2.62  tff('#skF_1', type, '#skF_1': $i > $i).
% 6.43/2.62  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.43/2.62  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 6.43/2.62  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.43/2.62  tff('#skF_5', type, '#skF_5': $i).
% 6.43/2.62  tff('#skF_6', type, '#skF_6': $i).
% 6.43/2.62  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 6.43/2.62  tff('#skF_3', type, '#skF_3': $i).
% 6.43/2.62  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.43/2.62  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.43/2.62  tff('#skF_4', type, '#skF_4': $i).
% 6.43/2.62  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.43/2.62  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 6.43/2.62  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.43/2.62  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 6.43/2.62  
% 6.43/2.65  tff(f_33, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 6.43/2.65  tff(f_94, negated_conjecture, ~(![A, B, C, D]: (r1_tarski(k2_zfmisc_1(A, B), k2_zfmisc_1(C, D)) => ((k2_zfmisc_1(A, B) = k1_xboole_0) | (r1_tarski(A, C) & r1_tarski(B, D))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t138_zfmisc_1)).
% 6.43/2.65  tff(f_59, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 6.43/2.65  tff(f_67, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 6.43/2.65  tff(f_37, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 6.43/2.65  tff(f_75, axiom, (![A, B, C, D]: ((r1_xboole_0(A, B) | r1_xboole_0(C, D)) => r1_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t127_zfmisc_1)).
% 6.43/2.65  tff(f_65, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 6.43/2.65  tff(f_69, axiom, (![A, B, C, D]: (k2_zfmisc_1(k3_xboole_0(A, B), k3_xboole_0(C, D)) = k3_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t123_zfmisc_1)).
% 6.43/2.65  tff(f_85, axiom, (![A, B, C, D]: ((k2_zfmisc_1(A, B) = k2_zfmisc_1(C, D)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | ((A = C) & (B = D))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t134_zfmisc_1)).
% 6.43/2.65  tff(f_61, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 6.43/2.65  tff(f_55, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 6.43/2.65  tff(f_41, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 6.43/2.65  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 6.43/2.65  tff(c_6, plain, (![A_3]: (v1_xboole_0(A_3) | r2_hidden('#skF_1'(A_3), A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.43/2.65  tff(c_40, plain, (k2_zfmisc_1('#skF_3', '#skF_4')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_94])).
% 6.43/2.65  tff(c_1779, plain, (![A_153, B_154]: (r1_tarski(A_153, B_154) | k4_xboole_0(A_153, B_154)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_59])).
% 6.43/2.65  tff(c_96, plain, (![A_43, B_44]: (r1_tarski(A_43, B_44) | k4_xboole_0(A_43, B_44)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_59])).
% 6.43/2.65  tff(c_38, plain, (~r1_tarski('#skF_4', '#skF_6') | ~r1_tarski('#skF_3', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_94])).
% 6.43/2.65  tff(c_90, plain, (~r1_tarski('#skF_3', '#skF_5')), inference(splitLeft, [status(thm)], [c_38])).
% 6.43/2.65  tff(c_104, plain, (k4_xboole_0('#skF_3', '#skF_5')!=k1_xboole_0), inference(resolution, [status(thm)], [c_96, c_90])).
% 6.43/2.65  tff(c_26, plain, (![A_21]: (k5_xboole_0(A_21, A_21)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_67])).
% 6.43/2.65  tff(c_10, plain, (![A_7, B_8]: (r1_xboole_0(A_7, B_8) | k3_xboole_0(A_7, B_8)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 6.43/2.65  tff(c_329, plain, (![A_81, B_82, C_83, D_84]: (~r1_xboole_0(A_81, B_82) | r1_xboole_0(k2_zfmisc_1(A_81, C_83), k2_zfmisc_1(B_82, D_84)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 6.43/2.65  tff(c_8, plain, (![A_7, B_8]: (k3_xboole_0(A_7, B_8)=k1_xboole_0 | ~r1_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 6.43/2.65  tff(c_400, plain, (![A_99, C_100, B_101, D_102]: (k3_xboole_0(k2_zfmisc_1(A_99, C_100), k2_zfmisc_1(B_101, D_102))=k1_xboole_0 | ~r1_xboole_0(A_99, B_101))), inference(resolution, [status(thm)], [c_329, c_8])).
% 6.43/2.65  tff(c_42, plain, (r1_tarski(k2_zfmisc_1('#skF_3', '#skF_4'), k2_zfmisc_1('#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_94])).
% 6.43/2.65  tff(c_111, plain, (![A_49, B_50]: (k3_xboole_0(A_49, B_50)=A_49 | ~r1_tarski(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_65])).
% 6.43/2.65  tff(c_119, plain, (k3_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'), k2_zfmisc_1('#skF_5', '#skF_6'))=k2_zfmisc_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_42, c_111])).
% 6.43/2.65  tff(c_411, plain, (k2_zfmisc_1('#skF_3', '#skF_4')=k1_xboole_0 | ~r1_xboole_0('#skF_3', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_400, c_119])).
% 6.43/2.65  tff(c_459, plain, (~r1_xboole_0('#skF_3', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_40, c_411])).
% 6.43/2.65  tff(c_470, plain, (k3_xboole_0('#skF_3', '#skF_5')!=k1_xboole_0), inference(resolution, [status(thm)], [c_10, c_459])).
% 6.43/2.65  tff(c_341, plain, (![C_85, D_86, A_87, B_88]: (~r1_xboole_0(C_85, D_86) | r1_xboole_0(k2_zfmisc_1(A_87, C_85), k2_zfmisc_1(B_88, D_86)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 6.43/2.65  tff(c_477, plain, (![A_107, C_108, B_109, D_110]: (k3_xboole_0(k2_zfmisc_1(A_107, C_108), k2_zfmisc_1(B_109, D_110))=k1_xboole_0 | ~r1_xboole_0(C_108, D_110))), inference(resolution, [status(thm)], [c_341, c_8])).
% 6.43/2.65  tff(c_491, plain, (k2_zfmisc_1('#skF_3', '#skF_4')=k1_xboole_0 | ~r1_xboole_0('#skF_4', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_477, c_119])).
% 6.43/2.65  tff(c_543, plain, (~r1_xboole_0('#skF_4', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_40, c_491])).
% 6.43/2.65  tff(c_555, plain, (k3_xboole_0('#skF_4', '#skF_6')!=k1_xboole_0), inference(resolution, [status(thm)], [c_10, c_543])).
% 6.43/2.65  tff(c_774, plain, (![A_123, C_124, B_125, D_126]: (k3_xboole_0(k2_zfmisc_1(A_123, C_124), k2_zfmisc_1(B_125, D_126))=k2_zfmisc_1(k3_xboole_0(A_123, B_125), k3_xboole_0(C_124, D_126)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 6.43/2.65  tff(c_785, plain, (k2_zfmisc_1(k3_xboole_0('#skF_3', '#skF_5'), k3_xboole_0('#skF_4', '#skF_6'))=k2_zfmisc_1('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_774, c_119])).
% 6.43/2.65  tff(c_36, plain, (![C_32, A_30, B_31, D_33]: (C_32=A_30 | k1_xboole_0=B_31 | k1_xboole_0=A_30 | k2_zfmisc_1(C_32, D_33)!=k2_zfmisc_1(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_85])).
% 6.43/2.65  tff(c_852, plain, (![C_32, D_33]: (k3_xboole_0('#skF_3', '#skF_5')=C_32 | k3_xboole_0('#skF_4', '#skF_6')=k1_xboole_0 | k3_xboole_0('#skF_3', '#skF_5')=k1_xboole_0 | k2_zfmisc_1(C_32, D_33)!=k2_zfmisc_1('#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_785, c_36])).
% 6.43/2.65  tff(c_882, plain, (![C_32, D_33]: (k3_xboole_0('#skF_3', '#skF_5')=C_32 | k2_zfmisc_1(C_32, D_33)!=k2_zfmisc_1('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_470, c_555, c_852])).
% 6.43/2.65  tff(c_1679, plain, (k3_xboole_0('#skF_3', '#skF_5')='#skF_3'), inference(reflexivity, [status(thm), theory('equality')], [c_882])).
% 6.43/2.65  tff(c_22, plain, (![A_17, B_18]: (k5_xboole_0(A_17, k3_xboole_0(A_17, B_18))=k4_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_61])).
% 6.43/2.65  tff(c_1764, plain, (k5_xboole_0('#skF_3', '#skF_3')=k4_xboole_0('#skF_3', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1679, c_22])).
% 6.43/2.65  tff(c_1774, plain, (k4_xboole_0('#skF_3', '#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_26, c_1764])).
% 6.43/2.65  tff(c_1776, plain, $false, inference(negUnitSimplification, [status(thm)], [c_104, c_1774])).
% 6.43/2.65  tff(c_1777, plain, (~r1_tarski('#skF_4', '#skF_6')), inference(splitRight, [status(thm)], [c_38])).
% 6.43/2.65  tff(c_1783, plain, (k4_xboole_0('#skF_4', '#skF_6')!=k1_xboole_0), inference(resolution, [status(thm)], [c_1779, c_1777])).
% 6.43/2.65  tff(c_1778, plain, (r1_tarski('#skF_3', '#skF_5')), inference(splitRight, [status(thm)], [c_38])).
% 6.43/2.65  tff(c_1811, plain, (![A_161, B_162]: (k3_xboole_0(A_161, B_162)=A_161 | ~r1_tarski(A_161, B_162))), inference(cnfTransformation, [status(thm)], [f_65])).
% 6.43/2.65  tff(c_1823, plain, (k3_xboole_0('#skF_3', '#skF_5')='#skF_3'), inference(resolution, [status(thm)], [c_1778, c_1811])).
% 6.43/2.65  tff(c_1847, plain, (![A_165, B_166, C_167]: (~r1_xboole_0(A_165, B_166) | ~r2_hidden(C_167, k3_xboole_0(A_165, B_166)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 6.43/2.65  tff(c_1850, plain, (![C_167]: (~r1_xboole_0('#skF_3', '#skF_5') | ~r2_hidden(C_167, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1823, c_1847])).
% 6.43/2.65  tff(c_1862, plain, (~r1_xboole_0('#skF_3', '#skF_5')), inference(splitLeft, [status(thm)], [c_1850])).
% 6.43/2.65  tff(c_1865, plain, (k3_xboole_0('#skF_3', '#skF_5')!=k1_xboole_0), inference(resolution, [status(thm)], [c_10, c_1862])).
% 6.43/2.65  tff(c_1867, plain, (k1_xboole_0!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1823, c_1865])).
% 6.43/2.65  tff(c_2119, plain, (![C_195, D_196, A_197, B_198]: (~r1_xboole_0(C_195, D_196) | r1_xboole_0(k2_zfmisc_1(A_197, C_195), k2_zfmisc_1(B_198, D_196)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 6.43/2.65  tff(c_1822, plain, (k3_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'), k2_zfmisc_1('#skF_5', '#skF_6'))=k2_zfmisc_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_42, c_1811])).
% 6.43/2.65  tff(c_1919, plain, (![A_172, B_173]: (r2_hidden('#skF_2'(A_172, B_173), k3_xboole_0(A_172, B_173)) | r1_xboole_0(A_172, B_173))), inference(cnfTransformation, [status(thm)], [f_55])).
% 6.43/2.65  tff(c_4, plain, (![B_6, A_3]: (~r2_hidden(B_6, A_3) | ~v1_xboole_0(A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.43/2.65  tff(c_1945, plain, (![A_174, B_175]: (~v1_xboole_0(k3_xboole_0(A_174, B_175)) | r1_xboole_0(A_174, B_175))), inference(resolution, [status(thm)], [c_1919, c_4])).
% 6.43/2.65  tff(c_1954, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4')) | r1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'), k2_zfmisc_1('#skF_5', '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_1822, c_1945])).
% 6.43/2.65  tff(c_1967, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_1954])).
% 6.43/2.65  tff(c_1879, plain, (![A_168, B_169]: (~r1_xboole_0(A_168, B_169) | v1_xboole_0(k3_xboole_0(A_168, B_169)))), inference(resolution, [status(thm)], [c_6, c_1847])).
% 6.43/2.65  tff(c_1885, plain, (~r1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'), k2_zfmisc_1('#skF_5', '#skF_6')) | v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1822, c_1879])).
% 6.43/2.65  tff(c_2066, plain, (~r1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'), k2_zfmisc_1('#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_1967, c_1885])).
% 6.43/2.65  tff(c_2131, plain, (~r1_xboole_0('#skF_4', '#skF_6')), inference(resolution, [status(thm)], [c_2119, c_2066])).
% 6.43/2.65  tff(c_2143, plain, (k3_xboole_0('#skF_4', '#skF_6')!=k1_xboole_0), inference(resolution, [status(thm)], [c_10, c_2131])).
% 6.43/2.65  tff(c_2570, plain, (![A_235, C_236, B_237, D_238]: (k3_xboole_0(k2_zfmisc_1(A_235, C_236), k2_zfmisc_1(B_237, D_238))=k2_zfmisc_1(k3_xboole_0(A_235, B_237), k3_xboole_0(C_236, D_238)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 6.43/2.65  tff(c_2602, plain, (k2_zfmisc_1(k3_xboole_0('#skF_3', '#skF_5'), k3_xboole_0('#skF_4', '#skF_6'))=k2_zfmisc_1('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2570, c_1822])).
% 6.43/2.65  tff(c_2629, plain, (k2_zfmisc_1('#skF_3', k3_xboole_0('#skF_4', '#skF_6'))=k2_zfmisc_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1823, c_2602])).
% 6.43/2.65  tff(c_34, plain, (![D_33, B_31, A_30, C_32]: (D_33=B_31 | k1_xboole_0=B_31 | k1_xboole_0=A_30 | k2_zfmisc_1(C_32, D_33)!=k2_zfmisc_1(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_85])).
% 6.43/2.65  tff(c_2644, plain, (![D_33, C_32]: (k3_xboole_0('#skF_4', '#skF_6')=D_33 | k3_xboole_0('#skF_4', '#skF_6')=k1_xboole_0 | k1_xboole_0='#skF_3' | k2_zfmisc_1(C_32, D_33)!=k2_zfmisc_1('#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_2629, c_34])).
% 6.43/2.65  tff(c_2679, plain, (![D_33, C_32]: (k3_xboole_0('#skF_4', '#skF_6')=D_33 | k2_zfmisc_1(C_32, D_33)!=k2_zfmisc_1('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_1867, c_2143, c_2644])).
% 6.43/2.65  tff(c_2698, plain, (k3_xboole_0('#skF_4', '#skF_6')='#skF_4'), inference(reflexivity, [status(thm), theory('equality')], [c_2679])).
% 6.43/2.65  tff(c_2739, plain, (k5_xboole_0('#skF_4', '#skF_4')=k4_xboole_0('#skF_4', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_2698, c_22])).
% 6.43/2.65  tff(c_2747, plain, (k4_xboole_0('#skF_4', '#skF_6')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_26, c_2739])).
% 6.43/2.65  tff(c_2749, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1783, c_2747])).
% 6.43/2.65  tff(c_2751, plain, (v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_1954])).
% 6.43/2.65  tff(c_12, plain, (![A_9]: (k1_xboole_0=A_9 | ~v1_xboole_0(A_9))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.43/2.65  tff(c_2754, plain, (k2_zfmisc_1('#skF_3', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_2751, c_12])).
% 6.43/2.65  tff(c_2758, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_2754])).
% 6.43/2.65  tff(c_2761, plain, (![C_243]: (~r2_hidden(C_243, '#skF_3'))), inference(splitRight, [status(thm)], [c_1850])).
% 6.43/2.65  tff(c_2766, plain, (v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_6, c_2761])).
% 6.43/2.65  tff(c_2770, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_2766, c_12])).
% 6.43/2.65  tff(c_2785, plain, (k2_zfmisc_1('#skF_3', '#skF_4')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2770, c_40])).
% 6.43/2.65  tff(c_2759, plain, (![C_167]: (~r2_hidden(C_167, '#skF_3'))), inference(splitRight, [status(thm)], [c_1850])).
% 6.43/2.65  tff(c_2760, plain, (r1_xboole_0('#skF_3', '#skF_5')), inference(splitRight, [status(thm)], [c_1850])).
% 6.43/2.65  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.43/2.65  tff(c_2807, plain, (![A_250, B_251]: (~r1_xboole_0(A_250, B_251) | v1_xboole_0(k3_xboole_0(A_250, B_251)))), inference(resolution, [status(thm)], [c_6, c_1847])).
% 6.43/2.65  tff(c_2823, plain, (![A_252, B_253]: (~r1_xboole_0(A_252, B_253) | v1_xboole_0(k3_xboole_0(B_253, A_252)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_2807])).
% 6.43/2.65  tff(c_2783, plain, (![A_9]: (A_9='#skF_3' | ~v1_xboole_0(A_9))), inference(demodulation, [status(thm), theory('equality')], [c_2770, c_12])).
% 6.43/2.65  tff(c_2898, plain, (![B_266, A_267]: (k3_xboole_0(B_266, A_267)='#skF_3' | ~r1_xboole_0(A_267, B_266))), inference(resolution, [status(thm)], [c_2823, c_2783])).
% 6.43/2.65  tff(c_2913, plain, (k3_xboole_0('#skF_5', '#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_2760, c_2898])).
% 6.43/2.65  tff(c_2950, plain, (![A_268, B_269]: (r2_hidden('#skF_2'(A_268, B_269), k3_xboole_0(A_268, B_269)) | r1_xboole_0(A_268, B_269))), inference(cnfTransformation, [status(thm)], [f_55])).
% 6.43/2.65  tff(c_2959, plain, (r2_hidden('#skF_2'('#skF_5', '#skF_3'), '#skF_3') | r1_xboole_0('#skF_5', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2913, c_2950])).
% 6.43/2.65  tff(c_2974, plain, (r1_xboole_0('#skF_5', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_2759, c_2959])).
% 6.43/2.65  tff(c_32, plain, (![A_26, B_27, C_28, D_29]: (~r1_xboole_0(A_26, B_27) | r1_xboole_0(k2_zfmisc_1(A_26, C_28), k2_zfmisc_1(B_27, D_29)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 6.43/2.65  tff(c_2816, plain, (![A_1, B_2]: (~r1_xboole_0(A_1, B_2) | v1_xboole_0(k3_xboole_0(B_2, A_1)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_2807])).
% 6.43/2.65  tff(c_2991, plain, (![A_270, B_271]: (~v1_xboole_0(k3_xboole_0(A_270, B_271)) | r1_xboole_0(A_270, B_271))), inference(resolution, [status(thm)], [c_2950, c_4])).
% 6.43/2.65  tff(c_3023, plain, (![B_272, A_273]: (r1_xboole_0(B_272, A_273) | ~r1_xboole_0(A_273, B_272))), inference(resolution, [status(thm)], [c_2816, c_2991])).
% 6.43/2.65  tff(c_3037, plain, (![B_27, D_29, A_26, C_28]: (r1_xboole_0(k2_zfmisc_1(B_27, D_29), k2_zfmisc_1(A_26, C_28)) | ~r1_xboole_0(A_26, B_27))), inference(resolution, [status(thm)], [c_32, c_3023])).
% 6.43/2.65  tff(c_2997, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4')) | r1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'), k2_zfmisc_1('#skF_5', '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_1822, c_2991])).
% 6.43/2.65  tff(c_3236, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_2997])).
% 6.43/2.65  tff(c_1861, plain, (![A_165, B_166]: (~r1_xboole_0(A_165, B_166) | v1_xboole_0(k3_xboole_0(A_165, B_166)))), inference(resolution, [status(thm)], [c_6, c_1847])).
% 6.43/2.65  tff(c_2855, plain, (~r1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'), k2_zfmisc_1('#skF_5', '#skF_6')) | v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1822, c_1861])).
% 6.43/2.65  tff(c_3444, plain, (~r1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'), k2_zfmisc_1('#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_3236, c_2855])).
% 6.43/2.65  tff(c_3450, plain, (~r1_xboole_0('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_3037, c_3444])).
% 6.43/2.65  tff(c_3467, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2974, c_3450])).
% 6.43/2.65  tff(c_3469, plain, (v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_2997])).
% 6.43/2.65  tff(c_3472, plain, (k2_zfmisc_1('#skF_3', '#skF_4')='#skF_3'), inference(resolution, [status(thm)], [c_3469, c_2783])).
% 6.43/2.65  tff(c_3476, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2785, c_3472])).
% 6.43/2.65  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.43/2.65  
% 6.43/2.65  Inference rules
% 6.43/2.65  ----------------------
% 6.43/2.65  #Ref     : 11
% 6.43/2.65  #Sup     : 948
% 6.43/2.65  #Fact    : 0
% 6.43/2.65  #Define  : 0
% 6.43/2.65  #Split   : 6
% 6.43/2.65  #Chain   : 0
% 6.43/2.65  #Close   : 0
% 6.43/2.65  
% 6.43/2.65  Ordering : KBO
% 6.43/2.65  
% 6.43/2.65  Simplification rules
% 6.43/2.65  ----------------------
% 6.43/2.65  #Subsume      : 303
% 6.43/2.65  #Demod        : 164
% 6.43/2.65  #Tautology    : 238
% 6.43/2.65  #SimpNegUnit  : 80
% 6.43/2.65  #BackRed      : 26
% 6.43/2.65  
% 6.43/2.65  #Partial instantiations: 0
% 6.43/2.65  #Strategies tried      : 1
% 6.43/2.65  
% 6.43/2.65  Timing (in seconds)
% 6.43/2.65  ----------------------
% 6.43/2.66  Preprocessing        : 0.50
% 6.43/2.66  Parsing              : 0.27
% 6.43/2.66  CNF conversion       : 0.03
% 6.43/2.66  Main loop            : 1.30
% 6.43/2.66  Inferencing          : 0.46
% 6.43/2.66  Reduction            : 0.42
% 6.43/2.66  Demodulation         : 0.30
% 6.43/2.66  BG Simplification    : 0.05
% 6.43/2.66  Subsumption          : 0.27
% 6.43/2.66  Abstraction          : 0.06
% 6.43/2.66  MUC search           : 0.00
% 6.43/2.66  Cooper               : 0.00
% 6.43/2.66  Total                : 1.88
% 6.43/2.66  Index Insertion      : 0.00
% 6.43/2.66  Index Deletion       : 0.00
% 6.43/2.66  Index Matching       : 0.00
% 6.43/2.66  BG Taut test         : 0.00
%------------------------------------------------------------------------------
