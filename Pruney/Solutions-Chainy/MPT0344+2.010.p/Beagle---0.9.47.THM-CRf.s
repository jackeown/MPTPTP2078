%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:20 EST 2020

% Result     : Theorem 3.86s
% Output     : CNFRefutation 4.19s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 316 expanded)
%              Number of leaves         :   28 ( 110 expanded)
%              Depth                    :   14
%              Number of atoms          :  188 ( 783 expanded)
%              Number of equality atoms :   25 (  65 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k4_xboole_0 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_6 > #skF_1 > #skF_7 > #skF_3 > #skF_8 > #skF_2 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_88,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ~ ( B != k1_xboole_0
            & ! [C] :
                ( m1_subset_1(C,A)
               => ~ r2_hidden(C,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_subset_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
        <=> r2_hidden(C,B) )
     => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).

tff(f_47,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

tff(f_59,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_75,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(c_50,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_42,plain,(
    ! [B_22,A_21] :
      ( m1_subset_1(B_22,A_21)
      | ~ v1_xboole_0(B_22)
      | ~ v1_xboole_0(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_74,plain,(
    ! [B_32,A_33] :
      ( m1_subset_1(B_32,A_33)
      | ~ v1_xboole_0(B_32)
      | ~ v1_xboole_0(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_63,plain,(
    ! [A_31] :
      ( v1_xboole_0(A_31)
      | r2_hidden('#skF_1'(A_31),A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_48,plain,(
    ! [C_25] :
      ( ~ r2_hidden(C_25,'#skF_8')
      | ~ m1_subset_1(C_25,'#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_71,plain,
    ( ~ m1_subset_1('#skF_1'('#skF_8'),'#skF_7')
    | v1_xboole_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_63,c_48])).

tff(c_73,plain,(
    ~ m1_subset_1('#skF_1'('#skF_8'),'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_71])).

tff(c_78,plain,
    ( ~ v1_xboole_0('#skF_1'('#skF_8'))
    | ~ v1_xboole_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_74,c_73])).

tff(c_79,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_78])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_107,plain,(
    ! [B_41,A_42] :
      ( m1_subset_1(B_41,A_42)
      | ~ r2_hidden(B_41,A_42)
      | v1_xboole_0(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_117,plain,(
    ! [A_1] :
      ( m1_subset_1('#skF_1'(A_1),A_1)
      | v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_4,c_107])).

tff(c_179,plain,(
    ! [B_55,A_56] :
      ( r2_hidden(B_55,A_56)
      | ~ m1_subset_1(B_55,A_56)
      | v1_xboole_0(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_203,plain,(
    ! [B_55] :
      ( ~ m1_subset_1(B_55,'#skF_7')
      | ~ m1_subset_1(B_55,'#skF_8')
      | v1_xboole_0('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_179,c_48])).

tff(c_234,plain,(
    ! [B_61] :
      ( ~ m1_subset_1(B_61,'#skF_7')
      | ~ m1_subset_1(B_61,'#skF_8') ) ),
    inference(splitLeft,[status(thm)],[c_203])).

tff(c_238,plain,
    ( ~ m1_subset_1('#skF_1'('#skF_7'),'#skF_8')
    | v1_xboole_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_117,c_234])).

tff(c_245,plain,(
    ~ m1_subset_1('#skF_1'('#skF_7'),'#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_79,c_238])).

tff(c_250,plain,
    ( ~ v1_xboole_0('#skF_1'('#skF_7'))
    | ~ v1_xboole_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_42,c_245])).

tff(c_251,plain,(
    ~ v1_xboole_0('#skF_8') ),
    inference(splitLeft,[status(thm)],[c_250])).

tff(c_642,plain,(
    ! [A_108,B_109] :
      ( r2_hidden('#skF_3'(A_108,B_109),B_109)
      | r2_hidden('#skF_4'(A_108,B_109),A_108)
      | B_109 = A_108 ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_20,plain,(
    ! [A_13] : k4_xboole_0(k1_xboole_0,A_13) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_205,plain,(
    ! [B_57,A_58] :
      ( ~ r2_hidden(B_57,A_58)
      | k4_xboole_0(A_58,k1_tarski(B_57)) != A_58 ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_214,plain,(
    ! [B_57] : ~ r2_hidden(B_57,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_205])).

tff(c_702,plain,(
    ! [A_110] :
      ( r2_hidden('#skF_4'(A_110,k1_xboole_0),A_110)
      | k1_xboole_0 = A_110 ) ),
    inference(resolution,[status(thm)],[c_642,c_214])).

tff(c_38,plain,(
    ! [B_22,A_21] :
      ( m1_subset_1(B_22,A_21)
      | ~ r2_hidden(B_22,A_21)
      | v1_xboole_0(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_726,plain,(
    ! [A_110] :
      ( m1_subset_1('#skF_4'(A_110,k1_xboole_0),A_110)
      | v1_xboole_0(A_110)
      | k1_xboole_0 = A_110 ) ),
    inference(resolution,[status(thm)],[c_702,c_38])).

tff(c_52,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_46,plain,(
    ! [A_23] : ~ v1_xboole_0(k1_zfmisc_1(A_23)) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_22,plain,(
    ! [C_18,A_14] :
      ( r1_tarski(C_18,A_14)
      | ~ r2_hidden(C_18,k1_zfmisc_1(A_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_190,plain,(
    ! [B_55,A_14] :
      ( r1_tarski(B_55,A_14)
      | ~ m1_subset_1(B_55,k1_zfmisc_1(A_14))
      | v1_xboole_0(k1_zfmisc_1(A_14)) ) ),
    inference(resolution,[status(thm)],[c_179,c_22])).

tff(c_265,plain,(
    ! [B_65,A_66] :
      ( r1_tarski(B_65,A_66)
      | ~ m1_subset_1(B_65,k1_zfmisc_1(A_66)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_190])).

tff(c_285,plain,(
    r1_tarski('#skF_8','#skF_7') ),
    inference(resolution,[status(thm)],[c_52,c_265])).

tff(c_40,plain,(
    ! [B_22,A_21] :
      ( r2_hidden(B_22,A_21)
      | ~ m1_subset_1(B_22,A_21)
      | v1_xboole_0(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_252,plain,(
    ! [C_62,B_63,A_64] :
      ( r2_hidden(C_62,B_63)
      | ~ r2_hidden(C_62,A_64)
      | ~ r1_tarski(A_64,B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_1600,plain,(
    ! [B_151,B_152,A_153] :
      ( r2_hidden(B_151,B_152)
      | ~ r1_tarski(A_153,B_152)
      | ~ m1_subset_1(B_151,A_153)
      | v1_xboole_0(A_153) ) ),
    inference(resolution,[status(thm)],[c_40,c_252])).

tff(c_1620,plain,(
    ! [B_151] :
      ( r2_hidden(B_151,'#skF_7')
      | ~ m1_subset_1(B_151,'#skF_8')
      | v1_xboole_0('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_285,c_1600])).

tff(c_1656,plain,(
    ! [B_154] :
      ( r2_hidden(B_154,'#skF_7')
      | ~ m1_subset_1(B_154,'#skF_8') ) ),
    inference(negUnitSimplification,[status(thm)],[c_251,c_1620])).

tff(c_1675,plain,(
    ! [B_154] :
      ( m1_subset_1(B_154,'#skF_7')
      | v1_xboole_0('#skF_7')
      | ~ m1_subset_1(B_154,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_1656,c_38])).

tff(c_1688,plain,(
    ! [B_155] :
      ( m1_subset_1(B_155,'#skF_7')
      | ~ m1_subset_1(B_155,'#skF_8') ) ),
    inference(negUnitSimplification,[status(thm)],[c_79,c_1675])).

tff(c_232,plain,(
    ! [B_55] :
      ( ~ m1_subset_1(B_55,'#skF_7')
      | ~ m1_subset_1(B_55,'#skF_8') ) ),
    inference(splitLeft,[status(thm)],[c_203])).

tff(c_1740,plain,(
    ! [B_156] : ~ m1_subset_1(B_156,'#skF_8') ),
    inference(resolution,[status(thm)],[c_1688,c_232])).

tff(c_1744,plain,
    ( v1_xboole_0('#skF_8')
    | k1_xboole_0 = '#skF_8' ),
    inference(resolution,[status(thm)],[c_726,c_1740])).

tff(c_1760,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_251,c_1744])).

tff(c_1762,plain,(
    v1_xboole_0('#skF_8') ),
    inference(splitRight,[status(thm)],[c_250])).

tff(c_1892,plain,(
    ! [A_170,B_171] :
      ( r2_hidden('#skF_3'(A_170,B_171),B_171)
      | r2_hidden('#skF_4'(A_170,B_171),A_170)
      | B_171 = A_170 ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1939,plain,(
    ! [A_172] :
      ( r2_hidden('#skF_4'(A_172,k1_xboole_0),A_172)
      | k1_xboole_0 = A_172 ) ),
    inference(resolution,[status(thm)],[c_1892,c_214])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1969,plain,(
    ! [A_173] :
      ( ~ v1_xboole_0(A_173)
      | k1_xboole_0 = A_173 ) ),
    inference(resolution,[status(thm)],[c_1939,c_2])).

tff(c_1978,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(resolution,[status(thm)],[c_1762,c_1969])).

tff(c_1987,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_1978])).

tff(c_1988,plain,(
    v1_xboole_0('#skF_8') ),
    inference(splitRight,[status(thm)],[c_203])).

tff(c_2056,plain,(
    ! [A_182,B_183] :
      ( r2_hidden('#skF_3'(A_182,B_183),B_183)
      | r2_hidden('#skF_4'(A_182,B_183),A_182)
      | B_183 = A_182 ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_2126,plain,(
    ! [A_185] :
      ( r2_hidden('#skF_4'(A_185,k1_xboole_0),A_185)
      | k1_xboole_0 = A_185 ) ),
    inference(resolution,[status(thm)],[c_2056,c_214])).

tff(c_2160,plain,(
    ! [A_186] :
      ( ~ v1_xboole_0(A_186)
      | k1_xboole_0 = A_186 ) ),
    inference(resolution,[status(thm)],[c_2126,c_2])).

tff(c_2166,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(resolution,[status(thm)],[c_1988,c_2160])).

tff(c_2174,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_2166])).

tff(c_2176,plain,(
    v1_xboole_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_2243,plain,(
    ! [B_204,A_205] :
      ( r2_hidden(B_204,A_205)
      | ~ m1_subset_1(B_204,A_205)
      | v1_xboole_0(A_205) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_2273,plain,(
    ! [B_204] :
      ( ~ m1_subset_1(B_204,'#skF_7')
      | ~ m1_subset_1(B_204,'#skF_8')
      | v1_xboole_0('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_2243,c_48])).

tff(c_2375,plain,(
    ! [B_221] :
      ( ~ m1_subset_1(B_221,'#skF_7')
      | ~ m1_subset_1(B_221,'#skF_8') ) ),
    inference(splitLeft,[status(thm)],[c_2273])).

tff(c_2383,plain,(
    ! [B_22] :
      ( ~ m1_subset_1(B_22,'#skF_8')
      | ~ v1_xboole_0(B_22)
      | ~ v1_xboole_0('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_42,c_2375])).

tff(c_2389,plain,(
    ! [B_222] :
      ( ~ m1_subset_1(B_222,'#skF_8')
      | ~ v1_xboole_0(B_222) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2176,c_2383])).

tff(c_2399,plain,(
    ! [B_22] :
      ( ~ v1_xboole_0(B_22)
      | ~ v1_xboole_0('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_42,c_2389])).

tff(c_2400,plain,(
    ~ v1_xboole_0('#skF_8') ),
    inference(splitLeft,[status(thm)],[c_2399])).

tff(c_2258,plain,(
    ! [B_204,A_14] :
      ( r1_tarski(B_204,A_14)
      | ~ m1_subset_1(B_204,k1_zfmisc_1(A_14))
      | v1_xboole_0(k1_zfmisc_1(A_14)) ) ),
    inference(resolution,[status(thm)],[c_2243,c_22])).

tff(c_2300,plain,(
    ! [B_208,A_209] :
      ( r1_tarski(B_208,A_209)
      | ~ m1_subset_1(B_208,k1_zfmisc_1(A_209)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_2258])).

tff(c_2320,plain,(
    r1_tarski('#skF_8','#skF_7') ),
    inference(resolution,[status(thm)],[c_52,c_2300])).

tff(c_2362,plain,(
    ! [C_218,B_219,A_220] :
      ( r2_hidden(C_218,B_219)
      | ~ r2_hidden(C_218,A_220)
      | ~ r1_tarski(A_220,B_219) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2401,plain,(
    ! [A_223,B_224] :
      ( r2_hidden('#skF_1'(A_223),B_224)
      | ~ r1_tarski(A_223,B_224)
      | v1_xboole_0(A_223) ) ),
    inference(resolution,[status(thm)],[c_4,c_2362])).

tff(c_2451,plain,(
    ! [B_226,A_227] :
      ( ~ v1_xboole_0(B_226)
      | ~ r1_tarski(A_227,B_226)
      | v1_xboole_0(A_227) ) ),
    inference(resolution,[status(thm)],[c_2401,c_2])).

tff(c_2463,plain,
    ( ~ v1_xboole_0('#skF_7')
    | v1_xboole_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_2320,c_2451])).

tff(c_2473,plain,(
    v1_xboole_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2176,c_2463])).

tff(c_2475,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2400,c_2473])).

tff(c_2476,plain,(
    ! [B_22] : ~ v1_xboole_0(B_22) ),
    inference(splitRight,[status(thm)],[c_2399])).

tff(c_2477,plain,(
    v1_xboole_0('#skF_8') ),
    inference(splitRight,[status(thm)],[c_2399])).

tff(c_2497,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2476,c_2477])).

tff(c_2498,plain,(
    v1_xboole_0('#skF_8') ),
    inference(splitRight,[status(thm)],[c_2273])).

tff(c_2683,plain,(
    ! [A_255,B_256] :
      ( r2_hidden('#skF_3'(A_255,B_256),B_256)
      | r2_hidden('#skF_4'(A_255,B_256),A_255)
      | B_256 = A_255 ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_2231,plain,(
    ! [B_201,A_202] :
      ( ~ r2_hidden(B_201,A_202)
      | k4_xboole_0(A_202,k1_tarski(B_201)) != A_202 ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_2236,plain,(
    ! [B_201] : ~ r2_hidden(B_201,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_2231])).

tff(c_2747,plain,(
    ! [A_258] :
      ( r2_hidden('#skF_4'(A_258,k1_xboole_0),A_258)
      | k1_xboole_0 = A_258 ) ),
    inference(resolution,[status(thm)],[c_2683,c_2236])).

tff(c_2777,plain,(
    ! [A_259] :
      ( ~ v1_xboole_0(A_259)
      | k1_xboole_0 = A_259 ) ),
    inference(resolution,[status(thm)],[c_2747,c_2])).

tff(c_2789,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(resolution,[status(thm)],[c_2498,c_2777])).

tff(c_2802,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_2789])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:51:49 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.86/1.74  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.13/1.75  
% 4.13/1.75  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.13/1.75  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k4_xboole_0 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_6 > #skF_1 > #skF_7 > #skF_3 > #skF_8 > #skF_2 > #skF_5 > #skF_4
% 4.13/1.75  
% 4.13/1.75  %Foreground sorts:
% 4.13/1.75  
% 4.13/1.75  
% 4.13/1.75  %Background operators:
% 4.13/1.75  
% 4.13/1.75  
% 4.13/1.75  %Foreground operators:
% 4.13/1.75  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 4.13/1.75  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.13/1.75  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.13/1.75  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.13/1.75  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.13/1.75  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.13/1.75  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.13/1.75  tff('#skF_7', type, '#skF_7': $i).
% 4.13/1.75  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.13/1.75  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.13/1.75  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.13/1.75  tff('#skF_8', type, '#skF_8': $i).
% 4.13/1.75  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.13/1.75  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.13/1.75  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.13/1.75  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.13/1.75  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 4.13/1.75  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 4.13/1.75  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.13/1.75  
% 4.19/1.77  tff(f_88, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => ~(~(B = k1_xboole_0) & (![C]: (m1_subset_1(C, A) => ~r2_hidden(C, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_subset_1)).
% 4.19/1.77  tff(f_72, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 4.19/1.77  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 4.19/1.77  tff(f_45, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) <=> r2_hidden(C, B))) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tarski)).
% 4.19/1.77  tff(f_47, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 4.19/1.77  tff(f_59, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 4.19/1.77  tff(f_75, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 4.19/1.77  tff(f_54, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 4.19/1.77  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 4.19/1.77  tff(c_50, plain, (k1_xboole_0!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.19/1.77  tff(c_42, plain, (![B_22, A_21]: (m1_subset_1(B_22, A_21) | ~v1_xboole_0(B_22) | ~v1_xboole_0(A_21))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.19/1.77  tff(c_74, plain, (![B_32, A_33]: (m1_subset_1(B_32, A_33) | ~v1_xboole_0(B_32) | ~v1_xboole_0(A_33))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.19/1.77  tff(c_63, plain, (![A_31]: (v1_xboole_0(A_31) | r2_hidden('#skF_1'(A_31), A_31))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.19/1.77  tff(c_48, plain, (![C_25]: (~r2_hidden(C_25, '#skF_8') | ~m1_subset_1(C_25, '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.19/1.77  tff(c_71, plain, (~m1_subset_1('#skF_1'('#skF_8'), '#skF_7') | v1_xboole_0('#skF_8')), inference(resolution, [status(thm)], [c_63, c_48])).
% 4.19/1.77  tff(c_73, plain, (~m1_subset_1('#skF_1'('#skF_8'), '#skF_7')), inference(splitLeft, [status(thm)], [c_71])).
% 4.19/1.77  tff(c_78, plain, (~v1_xboole_0('#skF_1'('#skF_8')) | ~v1_xboole_0('#skF_7')), inference(resolution, [status(thm)], [c_74, c_73])).
% 4.19/1.77  tff(c_79, plain, (~v1_xboole_0('#skF_7')), inference(splitLeft, [status(thm)], [c_78])).
% 4.19/1.77  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.19/1.77  tff(c_107, plain, (![B_41, A_42]: (m1_subset_1(B_41, A_42) | ~r2_hidden(B_41, A_42) | v1_xboole_0(A_42))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.19/1.77  tff(c_117, plain, (![A_1]: (m1_subset_1('#skF_1'(A_1), A_1) | v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_4, c_107])).
% 4.19/1.77  tff(c_179, plain, (![B_55, A_56]: (r2_hidden(B_55, A_56) | ~m1_subset_1(B_55, A_56) | v1_xboole_0(A_56))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.19/1.77  tff(c_203, plain, (![B_55]: (~m1_subset_1(B_55, '#skF_7') | ~m1_subset_1(B_55, '#skF_8') | v1_xboole_0('#skF_8'))), inference(resolution, [status(thm)], [c_179, c_48])).
% 4.19/1.77  tff(c_234, plain, (![B_61]: (~m1_subset_1(B_61, '#skF_7') | ~m1_subset_1(B_61, '#skF_8'))), inference(splitLeft, [status(thm)], [c_203])).
% 4.19/1.77  tff(c_238, plain, (~m1_subset_1('#skF_1'('#skF_7'), '#skF_8') | v1_xboole_0('#skF_7')), inference(resolution, [status(thm)], [c_117, c_234])).
% 4.19/1.77  tff(c_245, plain, (~m1_subset_1('#skF_1'('#skF_7'), '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_79, c_238])).
% 4.19/1.77  tff(c_250, plain, (~v1_xboole_0('#skF_1'('#skF_7')) | ~v1_xboole_0('#skF_8')), inference(resolution, [status(thm)], [c_42, c_245])).
% 4.19/1.77  tff(c_251, plain, (~v1_xboole_0('#skF_8')), inference(splitLeft, [status(thm)], [c_250])).
% 4.19/1.77  tff(c_642, plain, (![A_108, B_109]: (r2_hidden('#skF_3'(A_108, B_109), B_109) | r2_hidden('#skF_4'(A_108, B_109), A_108) | B_109=A_108)), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.19/1.77  tff(c_20, plain, (![A_13]: (k4_xboole_0(k1_xboole_0, A_13)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.19/1.77  tff(c_205, plain, (![B_57, A_58]: (~r2_hidden(B_57, A_58) | k4_xboole_0(A_58, k1_tarski(B_57))!=A_58)), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.19/1.77  tff(c_214, plain, (![B_57]: (~r2_hidden(B_57, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_20, c_205])).
% 4.19/1.77  tff(c_702, plain, (![A_110]: (r2_hidden('#skF_4'(A_110, k1_xboole_0), A_110) | k1_xboole_0=A_110)), inference(resolution, [status(thm)], [c_642, c_214])).
% 4.19/1.77  tff(c_38, plain, (![B_22, A_21]: (m1_subset_1(B_22, A_21) | ~r2_hidden(B_22, A_21) | v1_xboole_0(A_21))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.19/1.77  tff(c_726, plain, (![A_110]: (m1_subset_1('#skF_4'(A_110, k1_xboole_0), A_110) | v1_xboole_0(A_110) | k1_xboole_0=A_110)), inference(resolution, [status(thm)], [c_702, c_38])).
% 4.19/1.77  tff(c_52, plain, (m1_subset_1('#skF_8', k1_zfmisc_1('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.19/1.77  tff(c_46, plain, (![A_23]: (~v1_xboole_0(k1_zfmisc_1(A_23)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.19/1.77  tff(c_22, plain, (![C_18, A_14]: (r1_tarski(C_18, A_14) | ~r2_hidden(C_18, k1_zfmisc_1(A_14)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.19/1.77  tff(c_190, plain, (![B_55, A_14]: (r1_tarski(B_55, A_14) | ~m1_subset_1(B_55, k1_zfmisc_1(A_14)) | v1_xboole_0(k1_zfmisc_1(A_14)))), inference(resolution, [status(thm)], [c_179, c_22])).
% 4.19/1.77  tff(c_265, plain, (![B_65, A_66]: (r1_tarski(B_65, A_66) | ~m1_subset_1(B_65, k1_zfmisc_1(A_66)))), inference(negUnitSimplification, [status(thm)], [c_46, c_190])).
% 4.19/1.77  tff(c_285, plain, (r1_tarski('#skF_8', '#skF_7')), inference(resolution, [status(thm)], [c_52, c_265])).
% 4.19/1.77  tff(c_40, plain, (![B_22, A_21]: (r2_hidden(B_22, A_21) | ~m1_subset_1(B_22, A_21) | v1_xboole_0(A_21))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.19/1.77  tff(c_252, plain, (![C_62, B_63, A_64]: (r2_hidden(C_62, B_63) | ~r2_hidden(C_62, A_64) | ~r1_tarski(A_64, B_63))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.19/1.77  tff(c_1600, plain, (![B_151, B_152, A_153]: (r2_hidden(B_151, B_152) | ~r1_tarski(A_153, B_152) | ~m1_subset_1(B_151, A_153) | v1_xboole_0(A_153))), inference(resolution, [status(thm)], [c_40, c_252])).
% 4.19/1.77  tff(c_1620, plain, (![B_151]: (r2_hidden(B_151, '#skF_7') | ~m1_subset_1(B_151, '#skF_8') | v1_xboole_0('#skF_8'))), inference(resolution, [status(thm)], [c_285, c_1600])).
% 4.19/1.77  tff(c_1656, plain, (![B_154]: (r2_hidden(B_154, '#skF_7') | ~m1_subset_1(B_154, '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_251, c_1620])).
% 4.19/1.77  tff(c_1675, plain, (![B_154]: (m1_subset_1(B_154, '#skF_7') | v1_xboole_0('#skF_7') | ~m1_subset_1(B_154, '#skF_8'))), inference(resolution, [status(thm)], [c_1656, c_38])).
% 4.19/1.77  tff(c_1688, plain, (![B_155]: (m1_subset_1(B_155, '#skF_7') | ~m1_subset_1(B_155, '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_79, c_1675])).
% 4.19/1.77  tff(c_232, plain, (![B_55]: (~m1_subset_1(B_55, '#skF_7') | ~m1_subset_1(B_55, '#skF_8'))), inference(splitLeft, [status(thm)], [c_203])).
% 4.19/1.77  tff(c_1740, plain, (![B_156]: (~m1_subset_1(B_156, '#skF_8'))), inference(resolution, [status(thm)], [c_1688, c_232])).
% 4.19/1.77  tff(c_1744, plain, (v1_xboole_0('#skF_8') | k1_xboole_0='#skF_8'), inference(resolution, [status(thm)], [c_726, c_1740])).
% 4.19/1.77  tff(c_1760, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_251, c_1744])).
% 4.19/1.77  tff(c_1762, plain, (v1_xboole_0('#skF_8')), inference(splitRight, [status(thm)], [c_250])).
% 4.19/1.77  tff(c_1892, plain, (![A_170, B_171]: (r2_hidden('#skF_3'(A_170, B_171), B_171) | r2_hidden('#skF_4'(A_170, B_171), A_170) | B_171=A_170)), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.19/1.77  tff(c_1939, plain, (![A_172]: (r2_hidden('#skF_4'(A_172, k1_xboole_0), A_172) | k1_xboole_0=A_172)), inference(resolution, [status(thm)], [c_1892, c_214])).
% 4.19/1.77  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.19/1.77  tff(c_1969, plain, (![A_173]: (~v1_xboole_0(A_173) | k1_xboole_0=A_173)), inference(resolution, [status(thm)], [c_1939, c_2])).
% 4.19/1.77  tff(c_1978, plain, (k1_xboole_0='#skF_8'), inference(resolution, [status(thm)], [c_1762, c_1969])).
% 4.19/1.77  tff(c_1987, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_1978])).
% 4.19/1.77  tff(c_1988, plain, (v1_xboole_0('#skF_8')), inference(splitRight, [status(thm)], [c_203])).
% 4.19/1.77  tff(c_2056, plain, (![A_182, B_183]: (r2_hidden('#skF_3'(A_182, B_183), B_183) | r2_hidden('#skF_4'(A_182, B_183), A_182) | B_183=A_182)), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.19/1.77  tff(c_2126, plain, (![A_185]: (r2_hidden('#skF_4'(A_185, k1_xboole_0), A_185) | k1_xboole_0=A_185)), inference(resolution, [status(thm)], [c_2056, c_214])).
% 4.19/1.77  tff(c_2160, plain, (![A_186]: (~v1_xboole_0(A_186) | k1_xboole_0=A_186)), inference(resolution, [status(thm)], [c_2126, c_2])).
% 4.19/1.77  tff(c_2166, plain, (k1_xboole_0='#skF_8'), inference(resolution, [status(thm)], [c_1988, c_2160])).
% 4.19/1.77  tff(c_2174, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_2166])).
% 4.19/1.77  tff(c_2176, plain, (v1_xboole_0('#skF_7')), inference(splitRight, [status(thm)], [c_78])).
% 4.19/1.77  tff(c_2243, plain, (![B_204, A_205]: (r2_hidden(B_204, A_205) | ~m1_subset_1(B_204, A_205) | v1_xboole_0(A_205))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.19/1.77  tff(c_2273, plain, (![B_204]: (~m1_subset_1(B_204, '#skF_7') | ~m1_subset_1(B_204, '#skF_8') | v1_xboole_0('#skF_8'))), inference(resolution, [status(thm)], [c_2243, c_48])).
% 4.19/1.77  tff(c_2375, plain, (![B_221]: (~m1_subset_1(B_221, '#skF_7') | ~m1_subset_1(B_221, '#skF_8'))), inference(splitLeft, [status(thm)], [c_2273])).
% 4.19/1.77  tff(c_2383, plain, (![B_22]: (~m1_subset_1(B_22, '#skF_8') | ~v1_xboole_0(B_22) | ~v1_xboole_0('#skF_7'))), inference(resolution, [status(thm)], [c_42, c_2375])).
% 4.19/1.77  tff(c_2389, plain, (![B_222]: (~m1_subset_1(B_222, '#skF_8') | ~v1_xboole_0(B_222))), inference(demodulation, [status(thm), theory('equality')], [c_2176, c_2383])).
% 4.19/1.77  tff(c_2399, plain, (![B_22]: (~v1_xboole_0(B_22) | ~v1_xboole_0('#skF_8'))), inference(resolution, [status(thm)], [c_42, c_2389])).
% 4.19/1.77  tff(c_2400, plain, (~v1_xboole_0('#skF_8')), inference(splitLeft, [status(thm)], [c_2399])).
% 4.19/1.77  tff(c_2258, plain, (![B_204, A_14]: (r1_tarski(B_204, A_14) | ~m1_subset_1(B_204, k1_zfmisc_1(A_14)) | v1_xboole_0(k1_zfmisc_1(A_14)))), inference(resolution, [status(thm)], [c_2243, c_22])).
% 4.19/1.77  tff(c_2300, plain, (![B_208, A_209]: (r1_tarski(B_208, A_209) | ~m1_subset_1(B_208, k1_zfmisc_1(A_209)))), inference(negUnitSimplification, [status(thm)], [c_46, c_2258])).
% 4.19/1.77  tff(c_2320, plain, (r1_tarski('#skF_8', '#skF_7')), inference(resolution, [status(thm)], [c_52, c_2300])).
% 4.19/1.77  tff(c_2362, plain, (![C_218, B_219, A_220]: (r2_hidden(C_218, B_219) | ~r2_hidden(C_218, A_220) | ~r1_tarski(A_220, B_219))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.19/1.77  tff(c_2401, plain, (![A_223, B_224]: (r2_hidden('#skF_1'(A_223), B_224) | ~r1_tarski(A_223, B_224) | v1_xboole_0(A_223))), inference(resolution, [status(thm)], [c_4, c_2362])).
% 4.19/1.77  tff(c_2451, plain, (![B_226, A_227]: (~v1_xboole_0(B_226) | ~r1_tarski(A_227, B_226) | v1_xboole_0(A_227))), inference(resolution, [status(thm)], [c_2401, c_2])).
% 4.19/1.77  tff(c_2463, plain, (~v1_xboole_0('#skF_7') | v1_xboole_0('#skF_8')), inference(resolution, [status(thm)], [c_2320, c_2451])).
% 4.19/1.77  tff(c_2473, plain, (v1_xboole_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_2176, c_2463])).
% 4.19/1.77  tff(c_2475, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2400, c_2473])).
% 4.19/1.77  tff(c_2476, plain, (![B_22]: (~v1_xboole_0(B_22))), inference(splitRight, [status(thm)], [c_2399])).
% 4.19/1.77  tff(c_2477, plain, (v1_xboole_0('#skF_8')), inference(splitRight, [status(thm)], [c_2399])).
% 4.19/1.77  tff(c_2497, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2476, c_2477])).
% 4.19/1.77  tff(c_2498, plain, (v1_xboole_0('#skF_8')), inference(splitRight, [status(thm)], [c_2273])).
% 4.19/1.77  tff(c_2683, plain, (![A_255, B_256]: (r2_hidden('#skF_3'(A_255, B_256), B_256) | r2_hidden('#skF_4'(A_255, B_256), A_255) | B_256=A_255)), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.19/1.77  tff(c_2231, plain, (![B_201, A_202]: (~r2_hidden(B_201, A_202) | k4_xboole_0(A_202, k1_tarski(B_201))!=A_202)), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.19/1.77  tff(c_2236, plain, (![B_201]: (~r2_hidden(B_201, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_20, c_2231])).
% 4.19/1.77  tff(c_2747, plain, (![A_258]: (r2_hidden('#skF_4'(A_258, k1_xboole_0), A_258) | k1_xboole_0=A_258)), inference(resolution, [status(thm)], [c_2683, c_2236])).
% 4.19/1.77  tff(c_2777, plain, (![A_259]: (~v1_xboole_0(A_259) | k1_xboole_0=A_259)), inference(resolution, [status(thm)], [c_2747, c_2])).
% 4.19/1.77  tff(c_2789, plain, (k1_xboole_0='#skF_8'), inference(resolution, [status(thm)], [c_2498, c_2777])).
% 4.19/1.77  tff(c_2802, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_2789])).
% 4.19/1.77  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.19/1.77  
% 4.19/1.77  Inference rules
% 4.19/1.77  ----------------------
% 4.19/1.77  #Ref     : 0
% 4.19/1.77  #Sup     : 560
% 4.19/1.77  #Fact    : 0
% 4.19/1.77  #Define  : 0
% 4.19/1.77  #Split   : 10
% 4.19/1.77  #Chain   : 0
% 4.19/1.77  #Close   : 0
% 4.19/1.77  
% 4.19/1.77  Ordering : KBO
% 4.19/1.77  
% 4.19/1.77  Simplification rules
% 4.19/1.77  ----------------------
% 4.19/1.77  #Subsume      : 97
% 4.19/1.77  #Demod        : 117
% 4.19/1.77  #Tautology    : 153
% 4.19/1.77  #SimpNegUnit  : 92
% 4.19/1.77  #BackRed      : 16
% 4.19/1.77  
% 4.19/1.77  #Partial instantiations: 0
% 4.19/1.77  #Strategies tried      : 1
% 4.19/1.77  
% 4.19/1.77  Timing (in seconds)
% 4.19/1.77  ----------------------
% 4.19/1.77  Preprocessing        : 0.32
% 4.19/1.77  Parsing              : 0.16
% 4.19/1.77  CNF conversion       : 0.02
% 4.19/1.77  Main loop            : 0.63
% 4.19/1.77  Inferencing          : 0.23
% 4.19/1.77  Reduction            : 0.18
% 4.19/1.77  Demodulation         : 0.10
% 4.19/1.77  BG Simplification    : 0.03
% 4.19/1.77  Subsumption          : 0.13
% 4.19/1.77  Abstraction          : 0.03
% 4.19/1.77  MUC search           : 0.00
% 4.19/1.77  Cooper               : 0.00
% 4.19/1.77  Total                : 0.99
% 4.19/1.77  Index Insertion      : 0.00
% 4.19/1.77  Index Deletion       : 0.00
% 4.19/1.77  Index Matching       : 0.00
% 4.19/1.77  BG Taut test         : 0.00
%------------------------------------------------------------------------------
