%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:04 EST 2020

% Result     : Theorem 6.91s
% Output     : CNFRefutation 7.22s
% Verified   : 
% Statistics : Number of formulae       :  108 (1007 expanded)
%              Number of leaves         :   28 ( 343 expanded)
%              Depth                    :   18
%              Number of atoms          :  257 (2448 expanded)
%              Number of equality atoms :   17 ( 162 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k5_partfun1 > k2_zfmisc_1 > k1_funct_2 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_2,type,(
    k1_funct_2: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k5_partfun1,type,(
    k5_partfun1: ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_95,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => r1_tarski(k5_partfun1(A,B,C),k1_funct_2(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t159_funct_2)).

tff(f_39,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_88,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [D] :
          ( r2_hidden(D,k5_partfun1(A,B,C))
         => ( v1_funct_1(D)
            & v1_funct_2(D,A,B)
            & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t158_funct_2)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( ( ~ v1_xboole_0(A)
        & v1_xboole_0(B)
        & v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => v1_xboole_0(k5_partfun1(A,B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_partfun1)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( B = k1_xboole_0
         => A = k1_xboole_0 )
       => r2_hidden(C,k1_funct_2(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_funct_2)).

tff(f_33,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_41,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(c_36,plain,(
    ~ r1_tarski(k5_partfun1('#skF_2','#skF_3','#skF_4'),k1_funct_2('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_14,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_40,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_38,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_160,plain,(
    ! [D_55,A_56,B_57,C_58] :
      ( v1_funct_1(D_55)
      | ~ r2_hidden(D_55,k5_partfun1(A_56,B_57,C_58))
      | ~ m1_subset_1(C_58,k1_zfmisc_1(k2_zfmisc_1(A_56,B_57)))
      | ~ v1_funct_1(C_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_634,plain,(
    ! [A_154,B_155,C_156,B_157] :
      ( v1_funct_1('#skF_1'(k5_partfun1(A_154,B_155,C_156),B_157))
      | ~ m1_subset_1(C_156,k1_zfmisc_1(k2_zfmisc_1(A_154,B_155)))
      | ~ v1_funct_1(C_156)
      | r1_tarski(k5_partfun1(A_154,B_155,C_156),B_157) ) ),
    inference(resolution,[status(thm)],[c_6,c_160])).

tff(c_639,plain,(
    ! [B_157] :
      ( v1_funct_1('#skF_1'(k5_partfun1('#skF_2','#skF_3','#skF_4'),B_157))
      | ~ v1_funct_1('#skF_4')
      | r1_tarski(k5_partfun1('#skF_2','#skF_3','#skF_4'),B_157) ) ),
    inference(resolution,[status(thm)],[c_38,c_634])).

tff(c_643,plain,(
    ! [B_157] :
      ( v1_funct_1('#skF_1'(k5_partfun1('#skF_2','#skF_3','#skF_4'),B_157))
      | r1_tarski(k5_partfun1('#skF_2','#skF_3','#skF_4'),B_157) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_639])).

tff(c_96,plain,(
    ! [C_41,B_42,A_43] :
      ( r2_hidden(C_41,B_42)
      | ~ r2_hidden(C_41,A_43)
      | ~ r1_tarski(A_43,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_99,plain,(
    ! [A_1,B_2,B_42] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_42)
      | ~ r1_tarski(A_1,B_42)
      | r1_tarski(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_96])).

tff(c_353,plain,(
    ! [D_89,A_90,B_91,C_92] :
      ( v1_funct_2(D_89,A_90,B_91)
      | ~ r2_hidden(D_89,k5_partfun1(A_90,B_91,C_92))
      | ~ m1_subset_1(C_92,k1_zfmisc_1(k2_zfmisc_1(A_90,B_91)))
      | ~ v1_funct_1(C_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_818,plain,(
    ! [B_208,C_209,B_210,A_211,A_212] :
      ( v1_funct_2('#skF_1'(A_211,B_210),A_212,B_208)
      | ~ m1_subset_1(C_209,k1_zfmisc_1(k2_zfmisc_1(A_212,B_208)))
      | ~ v1_funct_1(C_209)
      | ~ r1_tarski(A_211,k5_partfun1(A_212,B_208,C_209))
      | r1_tarski(A_211,B_210) ) ),
    inference(resolution,[status(thm)],[c_99,c_353])).

tff(c_825,plain,(
    ! [A_211,B_210] :
      ( v1_funct_2('#skF_1'(A_211,B_210),'#skF_2','#skF_3')
      | ~ v1_funct_1('#skF_4')
      | ~ r1_tarski(A_211,k5_partfun1('#skF_2','#skF_3','#skF_4'))
      | r1_tarski(A_211,B_210) ) ),
    inference(resolution,[status(thm)],[c_38,c_818])).

tff(c_830,plain,(
    ! [A_211,B_210] :
      ( v1_funct_2('#skF_1'(A_211,B_210),'#skF_2','#skF_3')
      | ~ r1_tarski(A_211,k5_partfun1('#skF_2','#skF_3','#skF_4'))
      | r1_tarski(A_211,B_210) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_825])).

tff(c_20,plain,(
    ! [A_9,B_10] :
      ( m1_subset_1(A_9,k1_zfmisc_1(B_10))
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_88,plain,(
    ! [C_38,B_39,A_40] :
      ( ~ v1_xboole_0(C_38)
      | ~ m1_subset_1(B_39,k1_zfmisc_1(C_38))
      | ~ r2_hidden(A_40,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_100,plain,(
    ! [B_44,A_45,A_46] :
      ( ~ v1_xboole_0(B_44)
      | ~ r2_hidden(A_45,A_46)
      | ~ r1_tarski(A_46,B_44) ) ),
    inference(resolution,[status(thm)],[c_20,c_88])).

tff(c_104,plain,(
    ! [B_47,A_48,B_49] :
      ( ~ v1_xboole_0(B_47)
      | ~ r1_tarski(A_48,B_47)
      | r1_tarski(A_48,B_49) ) ),
    inference(resolution,[status(thm)],[c_6,c_100])).

tff(c_116,plain,(
    ! [B_50,B_51] :
      ( ~ v1_xboole_0(B_50)
      | r1_tarski(B_50,B_51) ) ),
    inference(resolution,[status(thm)],[c_14,c_104])).

tff(c_135,plain,(
    ~ v1_xboole_0(k5_partfun1('#skF_2','#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_116,c_36])).

tff(c_198,plain,(
    ! [A_68,B_69,C_70] :
      ( v1_xboole_0(k5_partfun1(A_68,B_69,C_70))
      | ~ m1_subset_1(C_70,k1_zfmisc_1(k2_zfmisc_1(A_68,B_69)))
      | ~ v1_funct_1(C_70)
      | ~ v1_xboole_0(B_69)
      | v1_xboole_0(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_205,plain,
    ( v1_xboole_0(k5_partfun1('#skF_2','#skF_3','#skF_4'))
    | ~ v1_funct_1('#skF_4')
    | ~ v1_xboole_0('#skF_3')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_198])).

tff(c_209,plain,
    ( v1_xboole_0(k5_partfun1('#skF_2','#skF_3','#skF_4'))
    | ~ v1_xboole_0('#skF_3')
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_205])).

tff(c_210,plain,
    ( ~ v1_xboole_0('#skF_3')
    | v1_xboole_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_135,c_209])).

tff(c_211,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_210])).

tff(c_522,plain,(
    ! [D_128,A_129,B_130,C_131] :
      ( m1_subset_1(D_128,k1_zfmisc_1(k2_zfmisc_1(A_129,B_130)))
      | ~ r2_hidden(D_128,k5_partfun1(A_129,B_130,C_131))
      | ~ m1_subset_1(C_131,k1_zfmisc_1(k2_zfmisc_1(A_129,B_130)))
      | ~ v1_funct_1(C_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_923,plain,(
    ! [A_239,B_238,C_237,B_235,A_236] :
      ( m1_subset_1('#skF_1'(A_239,B_238),k1_zfmisc_1(k2_zfmisc_1(A_236,B_235)))
      | ~ m1_subset_1(C_237,k1_zfmisc_1(k2_zfmisc_1(A_236,B_235)))
      | ~ v1_funct_1(C_237)
      | ~ r1_tarski(A_239,k5_partfun1(A_236,B_235,C_237))
      | r1_tarski(A_239,B_238) ) ),
    inference(resolution,[status(thm)],[c_99,c_522])).

tff(c_930,plain,(
    ! [A_239,B_238] :
      ( m1_subset_1('#skF_1'(A_239,B_238),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
      | ~ v1_funct_1('#skF_4')
      | ~ r1_tarski(A_239,k5_partfun1('#skF_2','#skF_3','#skF_4'))
      | r1_tarski(A_239,B_238) ) ),
    inference(resolution,[status(thm)],[c_38,c_923])).

tff(c_936,plain,(
    ! [A_240,B_241] :
      ( m1_subset_1('#skF_1'(A_240,B_241),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
      | ~ r1_tarski(A_240,k5_partfun1('#skF_2','#skF_3','#skF_4'))
      | r1_tarski(A_240,B_241) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_930])).

tff(c_28,plain,(
    ! [B_18,C_19,A_17] :
      ( k1_xboole_0 = B_18
      | r2_hidden(C_19,k1_funct_2(A_17,B_18))
      | ~ m1_subset_1(C_19,k1_zfmisc_1(k2_zfmisc_1(A_17,B_18)))
      | ~ v1_funct_2(C_19,A_17,B_18)
      | ~ v1_funct_1(C_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_960,plain,(
    ! [A_240,B_241] :
      ( k1_xboole_0 = '#skF_3'
      | r2_hidden('#skF_1'(A_240,B_241),k1_funct_2('#skF_2','#skF_3'))
      | ~ v1_funct_2('#skF_1'(A_240,B_241),'#skF_2','#skF_3')
      | ~ v1_funct_1('#skF_1'(A_240,B_241))
      | ~ r1_tarski(A_240,k5_partfun1('#skF_2','#skF_3','#skF_4'))
      | r1_tarski(A_240,B_241) ) ),
    inference(resolution,[status(thm)],[c_936,c_28])).

tff(c_1006,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_960])).

tff(c_8,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1037,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1006,c_8])).

tff(c_1039,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_211,c_1037])).

tff(c_1041,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_960])).

tff(c_18,plain,(
    ! [A_9,B_10] :
      ( r1_tarski(A_9,B_10)
      | ~ m1_subset_1(A_9,k1_zfmisc_1(B_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_963,plain,(
    ! [A_240,B_241] :
      ( r1_tarski('#skF_1'(A_240,B_241),k2_zfmisc_1('#skF_2','#skF_3'))
      | ~ r1_tarski(A_240,k5_partfun1('#skF_2','#skF_3','#skF_4'))
      | r1_tarski(A_240,B_241) ) ),
    inference(resolution,[status(thm)],[c_936,c_18])).

tff(c_448,plain,(
    ! [B_114,C_115,A_116] :
      ( k1_xboole_0 = B_114
      | r2_hidden(C_115,k1_funct_2(A_116,B_114))
      | ~ m1_subset_1(C_115,k1_zfmisc_1(k2_zfmisc_1(A_116,B_114)))
      | ~ v1_funct_2(C_115,A_116,B_114)
      | ~ v1_funct_1(C_115) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_510,plain,(
    ! [B_125,A_126,A_127] :
      ( k1_xboole_0 = B_125
      | r2_hidden(A_126,k1_funct_2(A_127,B_125))
      | ~ v1_funct_2(A_126,A_127,B_125)
      | ~ v1_funct_1(A_126)
      | ~ r1_tarski(A_126,k2_zfmisc_1(A_127,B_125)) ) ),
    inference(resolution,[status(thm)],[c_20,c_448])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1838,plain,(
    ! [A_327,A_328,B_329] :
      ( r1_tarski(A_327,k1_funct_2(A_328,B_329))
      | k1_xboole_0 = B_329
      | ~ v1_funct_2('#skF_1'(A_327,k1_funct_2(A_328,B_329)),A_328,B_329)
      | ~ v1_funct_1('#skF_1'(A_327,k1_funct_2(A_328,B_329)))
      | ~ r1_tarski('#skF_1'(A_327,k1_funct_2(A_328,B_329)),k2_zfmisc_1(A_328,B_329)) ) ),
    inference(resolution,[status(thm)],[c_510,c_4])).

tff(c_1850,plain,(
    ! [A_240] :
      ( k1_xboole_0 = '#skF_3'
      | ~ v1_funct_2('#skF_1'(A_240,k1_funct_2('#skF_2','#skF_3')),'#skF_2','#skF_3')
      | ~ v1_funct_1('#skF_1'(A_240,k1_funct_2('#skF_2','#skF_3')))
      | ~ r1_tarski(A_240,k5_partfun1('#skF_2','#skF_3','#skF_4'))
      | r1_tarski(A_240,k1_funct_2('#skF_2','#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_963,c_1838])).

tff(c_1909,plain,(
    ! [A_336] :
      ( ~ v1_funct_2('#skF_1'(A_336,k1_funct_2('#skF_2','#skF_3')),'#skF_2','#skF_3')
      | ~ v1_funct_1('#skF_1'(A_336,k1_funct_2('#skF_2','#skF_3')))
      | ~ r1_tarski(A_336,k5_partfun1('#skF_2','#skF_3','#skF_4'))
      | r1_tarski(A_336,k1_funct_2('#skF_2','#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1041,c_1850])).

tff(c_1925,plain,(
    ! [A_337] :
      ( ~ v1_funct_1('#skF_1'(A_337,k1_funct_2('#skF_2','#skF_3')))
      | ~ r1_tarski(A_337,k5_partfun1('#skF_2','#skF_3','#skF_4'))
      | r1_tarski(A_337,k1_funct_2('#skF_2','#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_830,c_1909])).

tff(c_1937,plain,
    ( ~ r1_tarski(k5_partfun1('#skF_2','#skF_3','#skF_4'),k5_partfun1('#skF_2','#skF_3','#skF_4'))
    | r1_tarski(k5_partfun1('#skF_2','#skF_3','#skF_4'),k1_funct_2('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_643,c_1925])).

tff(c_1942,plain,(
    r1_tarski(k5_partfun1('#skF_2','#skF_3','#skF_4'),k1_funct_2('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_1937])).

tff(c_1944,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_1942])).

tff(c_1946,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_210])).

tff(c_16,plain,(
    ! [A_8] : r1_tarski(k1_xboole_0,A_8) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_55,plain,(
    ! [B_33,A_34] :
      ( B_33 = A_34
      | ~ r1_tarski(B_33,A_34)
      | ~ r1_tarski(A_34,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_67,plain,(
    ! [A_8] :
      ( k1_xboole_0 = A_8
      | ~ r1_tarski(A_8,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_16,c_55])).

tff(c_133,plain,(
    ! [B_50] :
      ( k1_xboole_0 = B_50
      | ~ v1_xboole_0(B_50) ) ),
    inference(resolution,[status(thm)],[c_116,c_67])).

tff(c_1960,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_1946,c_133])).

tff(c_1945,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_210])).

tff(c_1953,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_1945,c_133])).

tff(c_1977,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1960,c_1953])).

tff(c_1986,plain,(
    ~ r1_tarski(k5_partfun1('#skF_3','#skF_3','#skF_4'),k1_funct_2('#skF_3','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1977,c_1977,c_36])).

tff(c_1988,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1977,c_38])).

tff(c_2294,plain,(
    ! [A_378,B_379,C_380,B_381] :
      ( v1_funct_1('#skF_1'(k5_partfun1(A_378,B_379,C_380),B_381))
      | ~ m1_subset_1(C_380,k1_zfmisc_1(k2_zfmisc_1(A_378,B_379)))
      | ~ v1_funct_1(C_380)
      | r1_tarski(k5_partfun1(A_378,B_379,C_380),B_381) ) ),
    inference(resolution,[status(thm)],[c_6,c_160])).

tff(c_2296,plain,(
    ! [B_381] :
      ( v1_funct_1('#skF_1'(k5_partfun1('#skF_3','#skF_3','#skF_4'),B_381))
      | ~ v1_funct_1('#skF_4')
      | r1_tarski(k5_partfun1('#skF_3','#skF_3','#skF_4'),B_381) ) ),
    inference(resolution,[status(thm)],[c_1988,c_2294])).

tff(c_2302,plain,(
    ! [B_381] :
      ( v1_funct_1('#skF_1'(k5_partfun1('#skF_3','#skF_3','#skF_4'),B_381))
      | r1_tarski(k5_partfun1('#skF_3','#skF_3','#skF_4'),B_381) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_2296])).

tff(c_2031,plain,(
    ! [D_342,A_343,B_344,C_345] :
      ( v1_funct_2(D_342,A_343,B_344)
      | ~ r2_hidden(D_342,k5_partfun1(A_343,B_344,C_345))
      | ~ m1_subset_1(C_345,k1_zfmisc_1(k2_zfmisc_1(A_343,B_344)))
      | ~ v1_funct_1(C_345) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_2615,plain,(
    ! [A_459,B_461,C_463,B_460,A_462] :
      ( v1_funct_2('#skF_1'(A_462,B_461),A_459,B_460)
      | ~ m1_subset_1(C_463,k1_zfmisc_1(k2_zfmisc_1(A_459,B_460)))
      | ~ v1_funct_1(C_463)
      | ~ r1_tarski(A_462,k5_partfun1(A_459,B_460,C_463))
      | r1_tarski(A_462,B_461) ) ),
    inference(resolution,[status(thm)],[c_99,c_2031])).

tff(c_2619,plain,(
    ! [A_462,B_461] :
      ( v1_funct_2('#skF_1'(A_462,B_461),'#skF_3','#skF_3')
      | ~ v1_funct_1('#skF_4')
      | ~ r1_tarski(A_462,k5_partfun1('#skF_3','#skF_3','#skF_4'))
      | r1_tarski(A_462,B_461) ) ),
    inference(resolution,[status(thm)],[c_1988,c_2615])).

tff(c_2626,plain,(
    ! [A_462,B_461] :
      ( v1_funct_2('#skF_1'(A_462,B_461),'#skF_3','#skF_3')
      | ~ r1_tarski(A_462,k5_partfun1('#skF_3','#skF_3','#skF_4'))
      | r1_tarski(A_462,B_461) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_2619])).

tff(c_2174,plain,(
    ! [D_360,A_361,B_362,C_363] :
      ( m1_subset_1(D_360,k1_zfmisc_1(k2_zfmisc_1(A_361,B_362)))
      | ~ r2_hidden(D_360,k5_partfun1(A_361,B_362,C_363))
      | ~ m1_subset_1(C_363,k1_zfmisc_1(k2_zfmisc_1(A_361,B_362)))
      | ~ v1_funct_1(C_363) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_2910,plain,(
    ! [A_528,B_526,C_525,A_527,B_524] :
      ( m1_subset_1('#skF_1'(A_528,B_526),k1_zfmisc_1(k2_zfmisc_1(A_527,B_524)))
      | ~ m1_subset_1(C_525,k1_zfmisc_1(k2_zfmisc_1(A_527,B_524)))
      | ~ v1_funct_1(C_525)
      | ~ r1_tarski(A_528,k5_partfun1(A_527,B_524,C_525))
      | r1_tarski(A_528,B_526) ) ),
    inference(resolution,[status(thm)],[c_99,c_2174])).

tff(c_2914,plain,(
    ! [A_528,B_526] :
      ( m1_subset_1('#skF_1'(A_528,B_526),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3')))
      | ~ v1_funct_1('#skF_4')
      | ~ r1_tarski(A_528,k5_partfun1('#skF_3','#skF_3','#skF_4'))
      | r1_tarski(A_528,B_526) ) ),
    inference(resolution,[status(thm)],[c_1988,c_2910])).

tff(c_2923,plain,(
    ! [A_529,B_530] :
      ( m1_subset_1('#skF_1'(A_529,B_530),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3')))
      | ~ r1_tarski(A_529,k5_partfun1('#skF_3','#skF_3','#skF_4'))
      | r1_tarski(A_529,B_530) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_2914])).

tff(c_26,plain,(
    ! [C_19,B_18] :
      ( r2_hidden(C_19,k1_funct_2(k1_xboole_0,B_18))
      | ~ m1_subset_1(C_19,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_18)))
      | ~ v1_funct_2(C_19,k1_xboole_0,B_18)
      | ~ v1_funct_1(C_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_1967,plain,(
    ! [C_19,B_18] :
      ( r2_hidden(C_19,k1_funct_2('#skF_2',B_18))
      | ~ m1_subset_1(C_19,k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_18)))
      | ~ v1_funct_2(C_19,'#skF_2',B_18)
      | ~ v1_funct_1(C_19) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1953,c_1953,c_1953,c_26])).

tff(c_2384,plain,(
    ! [C_19,B_18] :
      ( r2_hidden(C_19,k1_funct_2('#skF_3',B_18))
      | ~ m1_subset_1(C_19,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_18)))
      | ~ v1_funct_2(C_19,'#skF_3',B_18)
      | ~ v1_funct_1(C_19) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1977,c_1977,c_1977,c_1967])).

tff(c_3049,plain,(
    ! [A_545,B_546] :
      ( r2_hidden('#skF_1'(A_545,B_546),k1_funct_2('#skF_3','#skF_3'))
      | ~ v1_funct_2('#skF_1'(A_545,B_546),'#skF_3','#skF_3')
      | ~ v1_funct_1('#skF_1'(A_545,B_546))
      | ~ r1_tarski(A_545,k5_partfun1('#skF_3','#skF_3','#skF_4'))
      | r1_tarski(A_545,B_546) ) ),
    inference(resolution,[status(thm)],[c_2923,c_2384])).

tff(c_3764,plain,(
    ! [A_608] :
      ( ~ v1_funct_2('#skF_1'(A_608,k1_funct_2('#skF_3','#skF_3')),'#skF_3','#skF_3')
      | ~ v1_funct_1('#skF_1'(A_608,k1_funct_2('#skF_3','#skF_3')))
      | ~ r1_tarski(A_608,k5_partfun1('#skF_3','#skF_3','#skF_4'))
      | r1_tarski(A_608,k1_funct_2('#skF_3','#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_3049,c_4])).

tff(c_3780,plain,(
    ! [A_609] :
      ( ~ v1_funct_1('#skF_1'(A_609,k1_funct_2('#skF_3','#skF_3')))
      | ~ r1_tarski(A_609,k5_partfun1('#skF_3','#skF_3','#skF_4'))
      | r1_tarski(A_609,k1_funct_2('#skF_3','#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_2626,c_3764])).

tff(c_3796,plain,
    ( ~ r1_tarski(k5_partfun1('#skF_3','#skF_3','#skF_4'),k5_partfun1('#skF_3','#skF_3','#skF_4'))
    | r1_tarski(k5_partfun1('#skF_3','#skF_3','#skF_4'),k1_funct_2('#skF_3','#skF_3')) ),
    inference(resolution,[status(thm)],[c_2302,c_3780])).

tff(c_3802,plain,(
    r1_tarski(k5_partfun1('#skF_3','#skF_3','#skF_4'),k1_funct_2('#skF_3','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_3796])).

tff(c_3804,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1986,c_3802])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 20:40:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.91/2.45  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.91/2.46  
% 6.91/2.46  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.91/2.46  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k5_partfun1 > k2_zfmisc_1 > k1_funct_2 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 6.91/2.46  
% 6.91/2.46  %Foreground sorts:
% 6.91/2.46  
% 6.91/2.46  
% 6.91/2.46  %Background operators:
% 6.91/2.46  
% 6.91/2.46  
% 6.91/2.46  %Foreground operators:
% 6.91/2.46  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.91/2.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.91/2.46  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.91/2.46  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.91/2.46  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.91/2.46  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.91/2.46  tff('#skF_2', type, '#skF_2': $i).
% 6.91/2.46  tff('#skF_3', type, '#skF_3': $i).
% 6.91/2.46  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.91/2.46  tff(k1_funct_2, type, k1_funct_2: ($i * $i) > $i).
% 6.91/2.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.91/2.46  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.91/2.46  tff('#skF_4', type, '#skF_4': $i).
% 6.91/2.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.91/2.46  tff(k5_partfun1, type, k5_partfun1: ($i * $i * $i) > $i).
% 6.91/2.46  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 6.91/2.46  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 6.91/2.46  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.91/2.46  
% 7.22/2.48  tff(f_95, negated_conjecture, ~(![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r1_tarski(k5_partfun1(A, B, C), k1_funct_2(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t159_funct_2)).
% 7.22/2.48  tff(f_39, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 7.22/2.48  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 7.22/2.48  tff(f_88, axiom, (![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (r2_hidden(D, k5_partfun1(A, B, C)) => ((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t158_funct_2)).
% 7.22/2.48  tff(f_45, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 7.22/2.48  tff(f_52, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 7.22/2.48  tff(f_63, axiom, (![A, B, C]: ((((~v1_xboole_0(A) & v1_xboole_0(B)) & v1_funct_1(C)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => v1_xboole_0(k5_partfun1(A, B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_partfun1)).
% 7.22/2.48  tff(f_75, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((B = k1_xboole_0) => (A = k1_xboole_0)) => r2_hidden(C, k1_funct_2(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_funct_2)).
% 7.22/2.48  tff(f_33, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 7.22/2.48  tff(f_41, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 7.22/2.48  tff(c_36, plain, (~r1_tarski(k5_partfun1('#skF_2', '#skF_3', '#skF_4'), k1_funct_2('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_95])).
% 7.22/2.48  tff(c_14, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.22/2.48  tff(c_40, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_95])).
% 7.22/2.48  tff(c_38, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_95])).
% 7.22/2.48  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.22/2.48  tff(c_160, plain, (![D_55, A_56, B_57, C_58]: (v1_funct_1(D_55) | ~r2_hidden(D_55, k5_partfun1(A_56, B_57, C_58)) | ~m1_subset_1(C_58, k1_zfmisc_1(k2_zfmisc_1(A_56, B_57))) | ~v1_funct_1(C_58))), inference(cnfTransformation, [status(thm)], [f_88])).
% 7.22/2.48  tff(c_634, plain, (![A_154, B_155, C_156, B_157]: (v1_funct_1('#skF_1'(k5_partfun1(A_154, B_155, C_156), B_157)) | ~m1_subset_1(C_156, k1_zfmisc_1(k2_zfmisc_1(A_154, B_155))) | ~v1_funct_1(C_156) | r1_tarski(k5_partfun1(A_154, B_155, C_156), B_157))), inference(resolution, [status(thm)], [c_6, c_160])).
% 7.22/2.48  tff(c_639, plain, (![B_157]: (v1_funct_1('#skF_1'(k5_partfun1('#skF_2', '#skF_3', '#skF_4'), B_157)) | ~v1_funct_1('#skF_4') | r1_tarski(k5_partfun1('#skF_2', '#skF_3', '#skF_4'), B_157))), inference(resolution, [status(thm)], [c_38, c_634])).
% 7.22/2.48  tff(c_643, plain, (![B_157]: (v1_funct_1('#skF_1'(k5_partfun1('#skF_2', '#skF_3', '#skF_4'), B_157)) | r1_tarski(k5_partfun1('#skF_2', '#skF_3', '#skF_4'), B_157))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_639])).
% 7.22/2.48  tff(c_96, plain, (![C_41, B_42, A_43]: (r2_hidden(C_41, B_42) | ~r2_hidden(C_41, A_43) | ~r1_tarski(A_43, B_42))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.22/2.48  tff(c_99, plain, (![A_1, B_2, B_42]: (r2_hidden('#skF_1'(A_1, B_2), B_42) | ~r1_tarski(A_1, B_42) | r1_tarski(A_1, B_2))), inference(resolution, [status(thm)], [c_6, c_96])).
% 7.22/2.48  tff(c_353, plain, (![D_89, A_90, B_91, C_92]: (v1_funct_2(D_89, A_90, B_91) | ~r2_hidden(D_89, k5_partfun1(A_90, B_91, C_92)) | ~m1_subset_1(C_92, k1_zfmisc_1(k2_zfmisc_1(A_90, B_91))) | ~v1_funct_1(C_92))), inference(cnfTransformation, [status(thm)], [f_88])).
% 7.22/2.48  tff(c_818, plain, (![B_208, C_209, B_210, A_211, A_212]: (v1_funct_2('#skF_1'(A_211, B_210), A_212, B_208) | ~m1_subset_1(C_209, k1_zfmisc_1(k2_zfmisc_1(A_212, B_208))) | ~v1_funct_1(C_209) | ~r1_tarski(A_211, k5_partfun1(A_212, B_208, C_209)) | r1_tarski(A_211, B_210))), inference(resolution, [status(thm)], [c_99, c_353])).
% 7.22/2.48  tff(c_825, plain, (![A_211, B_210]: (v1_funct_2('#skF_1'(A_211, B_210), '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4') | ~r1_tarski(A_211, k5_partfun1('#skF_2', '#skF_3', '#skF_4')) | r1_tarski(A_211, B_210))), inference(resolution, [status(thm)], [c_38, c_818])).
% 7.22/2.48  tff(c_830, plain, (![A_211, B_210]: (v1_funct_2('#skF_1'(A_211, B_210), '#skF_2', '#skF_3') | ~r1_tarski(A_211, k5_partfun1('#skF_2', '#skF_3', '#skF_4')) | r1_tarski(A_211, B_210))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_825])).
% 7.22/2.48  tff(c_20, plain, (![A_9, B_10]: (m1_subset_1(A_9, k1_zfmisc_1(B_10)) | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.22/2.48  tff(c_88, plain, (![C_38, B_39, A_40]: (~v1_xboole_0(C_38) | ~m1_subset_1(B_39, k1_zfmisc_1(C_38)) | ~r2_hidden(A_40, B_39))), inference(cnfTransformation, [status(thm)], [f_52])).
% 7.22/2.48  tff(c_100, plain, (![B_44, A_45, A_46]: (~v1_xboole_0(B_44) | ~r2_hidden(A_45, A_46) | ~r1_tarski(A_46, B_44))), inference(resolution, [status(thm)], [c_20, c_88])).
% 7.22/2.48  tff(c_104, plain, (![B_47, A_48, B_49]: (~v1_xboole_0(B_47) | ~r1_tarski(A_48, B_47) | r1_tarski(A_48, B_49))), inference(resolution, [status(thm)], [c_6, c_100])).
% 7.22/2.48  tff(c_116, plain, (![B_50, B_51]: (~v1_xboole_0(B_50) | r1_tarski(B_50, B_51))), inference(resolution, [status(thm)], [c_14, c_104])).
% 7.22/2.48  tff(c_135, plain, (~v1_xboole_0(k5_partfun1('#skF_2', '#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_116, c_36])).
% 7.22/2.48  tff(c_198, plain, (![A_68, B_69, C_70]: (v1_xboole_0(k5_partfun1(A_68, B_69, C_70)) | ~m1_subset_1(C_70, k1_zfmisc_1(k2_zfmisc_1(A_68, B_69))) | ~v1_funct_1(C_70) | ~v1_xboole_0(B_69) | v1_xboole_0(A_68))), inference(cnfTransformation, [status(thm)], [f_63])).
% 7.22/2.48  tff(c_205, plain, (v1_xboole_0(k5_partfun1('#skF_2', '#skF_3', '#skF_4')) | ~v1_funct_1('#skF_4') | ~v1_xboole_0('#skF_3') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_38, c_198])).
% 7.22/2.48  tff(c_209, plain, (v1_xboole_0(k5_partfun1('#skF_2', '#skF_3', '#skF_4')) | ~v1_xboole_0('#skF_3') | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_205])).
% 7.22/2.48  tff(c_210, plain, (~v1_xboole_0('#skF_3') | v1_xboole_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_135, c_209])).
% 7.22/2.48  tff(c_211, plain, (~v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_210])).
% 7.22/2.48  tff(c_522, plain, (![D_128, A_129, B_130, C_131]: (m1_subset_1(D_128, k1_zfmisc_1(k2_zfmisc_1(A_129, B_130))) | ~r2_hidden(D_128, k5_partfun1(A_129, B_130, C_131)) | ~m1_subset_1(C_131, k1_zfmisc_1(k2_zfmisc_1(A_129, B_130))) | ~v1_funct_1(C_131))), inference(cnfTransformation, [status(thm)], [f_88])).
% 7.22/2.48  tff(c_923, plain, (![A_239, B_238, C_237, B_235, A_236]: (m1_subset_1('#skF_1'(A_239, B_238), k1_zfmisc_1(k2_zfmisc_1(A_236, B_235))) | ~m1_subset_1(C_237, k1_zfmisc_1(k2_zfmisc_1(A_236, B_235))) | ~v1_funct_1(C_237) | ~r1_tarski(A_239, k5_partfun1(A_236, B_235, C_237)) | r1_tarski(A_239, B_238))), inference(resolution, [status(thm)], [c_99, c_522])).
% 7.22/2.48  tff(c_930, plain, (![A_239, B_238]: (m1_subset_1('#skF_1'(A_239, B_238), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_1('#skF_4') | ~r1_tarski(A_239, k5_partfun1('#skF_2', '#skF_3', '#skF_4')) | r1_tarski(A_239, B_238))), inference(resolution, [status(thm)], [c_38, c_923])).
% 7.22/2.48  tff(c_936, plain, (![A_240, B_241]: (m1_subset_1('#skF_1'(A_240, B_241), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~r1_tarski(A_240, k5_partfun1('#skF_2', '#skF_3', '#skF_4')) | r1_tarski(A_240, B_241))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_930])).
% 7.22/2.48  tff(c_28, plain, (![B_18, C_19, A_17]: (k1_xboole_0=B_18 | r2_hidden(C_19, k1_funct_2(A_17, B_18)) | ~m1_subset_1(C_19, k1_zfmisc_1(k2_zfmisc_1(A_17, B_18))) | ~v1_funct_2(C_19, A_17, B_18) | ~v1_funct_1(C_19))), inference(cnfTransformation, [status(thm)], [f_75])).
% 7.22/2.48  tff(c_960, plain, (![A_240, B_241]: (k1_xboole_0='#skF_3' | r2_hidden('#skF_1'(A_240, B_241), k1_funct_2('#skF_2', '#skF_3')) | ~v1_funct_2('#skF_1'(A_240, B_241), '#skF_2', '#skF_3') | ~v1_funct_1('#skF_1'(A_240, B_241)) | ~r1_tarski(A_240, k5_partfun1('#skF_2', '#skF_3', '#skF_4')) | r1_tarski(A_240, B_241))), inference(resolution, [status(thm)], [c_936, c_28])).
% 7.22/2.48  tff(c_1006, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_960])).
% 7.22/2.48  tff(c_8, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 7.22/2.48  tff(c_1037, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1006, c_8])).
% 7.22/2.48  tff(c_1039, plain, $false, inference(negUnitSimplification, [status(thm)], [c_211, c_1037])).
% 7.22/2.48  tff(c_1041, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_960])).
% 7.22/2.48  tff(c_18, plain, (![A_9, B_10]: (r1_tarski(A_9, B_10) | ~m1_subset_1(A_9, k1_zfmisc_1(B_10)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.22/2.48  tff(c_963, plain, (![A_240, B_241]: (r1_tarski('#skF_1'(A_240, B_241), k2_zfmisc_1('#skF_2', '#skF_3')) | ~r1_tarski(A_240, k5_partfun1('#skF_2', '#skF_3', '#skF_4')) | r1_tarski(A_240, B_241))), inference(resolution, [status(thm)], [c_936, c_18])).
% 7.22/2.48  tff(c_448, plain, (![B_114, C_115, A_116]: (k1_xboole_0=B_114 | r2_hidden(C_115, k1_funct_2(A_116, B_114)) | ~m1_subset_1(C_115, k1_zfmisc_1(k2_zfmisc_1(A_116, B_114))) | ~v1_funct_2(C_115, A_116, B_114) | ~v1_funct_1(C_115))), inference(cnfTransformation, [status(thm)], [f_75])).
% 7.22/2.48  tff(c_510, plain, (![B_125, A_126, A_127]: (k1_xboole_0=B_125 | r2_hidden(A_126, k1_funct_2(A_127, B_125)) | ~v1_funct_2(A_126, A_127, B_125) | ~v1_funct_1(A_126) | ~r1_tarski(A_126, k2_zfmisc_1(A_127, B_125)))), inference(resolution, [status(thm)], [c_20, c_448])).
% 7.22/2.48  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.22/2.48  tff(c_1838, plain, (![A_327, A_328, B_329]: (r1_tarski(A_327, k1_funct_2(A_328, B_329)) | k1_xboole_0=B_329 | ~v1_funct_2('#skF_1'(A_327, k1_funct_2(A_328, B_329)), A_328, B_329) | ~v1_funct_1('#skF_1'(A_327, k1_funct_2(A_328, B_329))) | ~r1_tarski('#skF_1'(A_327, k1_funct_2(A_328, B_329)), k2_zfmisc_1(A_328, B_329)))), inference(resolution, [status(thm)], [c_510, c_4])).
% 7.22/2.48  tff(c_1850, plain, (![A_240]: (k1_xboole_0='#skF_3' | ~v1_funct_2('#skF_1'(A_240, k1_funct_2('#skF_2', '#skF_3')), '#skF_2', '#skF_3') | ~v1_funct_1('#skF_1'(A_240, k1_funct_2('#skF_2', '#skF_3'))) | ~r1_tarski(A_240, k5_partfun1('#skF_2', '#skF_3', '#skF_4')) | r1_tarski(A_240, k1_funct_2('#skF_2', '#skF_3')))), inference(resolution, [status(thm)], [c_963, c_1838])).
% 7.22/2.48  tff(c_1909, plain, (![A_336]: (~v1_funct_2('#skF_1'(A_336, k1_funct_2('#skF_2', '#skF_3')), '#skF_2', '#skF_3') | ~v1_funct_1('#skF_1'(A_336, k1_funct_2('#skF_2', '#skF_3'))) | ~r1_tarski(A_336, k5_partfun1('#skF_2', '#skF_3', '#skF_4')) | r1_tarski(A_336, k1_funct_2('#skF_2', '#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_1041, c_1850])).
% 7.22/2.48  tff(c_1925, plain, (![A_337]: (~v1_funct_1('#skF_1'(A_337, k1_funct_2('#skF_2', '#skF_3'))) | ~r1_tarski(A_337, k5_partfun1('#skF_2', '#skF_3', '#skF_4')) | r1_tarski(A_337, k1_funct_2('#skF_2', '#skF_3')))), inference(resolution, [status(thm)], [c_830, c_1909])).
% 7.22/2.48  tff(c_1937, plain, (~r1_tarski(k5_partfun1('#skF_2', '#skF_3', '#skF_4'), k5_partfun1('#skF_2', '#skF_3', '#skF_4')) | r1_tarski(k5_partfun1('#skF_2', '#skF_3', '#skF_4'), k1_funct_2('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_643, c_1925])).
% 7.22/2.48  tff(c_1942, plain, (r1_tarski(k5_partfun1('#skF_2', '#skF_3', '#skF_4'), k1_funct_2('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_1937])).
% 7.22/2.48  tff(c_1944, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_1942])).
% 7.22/2.48  tff(c_1946, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_210])).
% 7.22/2.48  tff(c_16, plain, (![A_8]: (r1_tarski(k1_xboole_0, A_8))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.22/2.48  tff(c_55, plain, (![B_33, A_34]: (B_33=A_34 | ~r1_tarski(B_33, A_34) | ~r1_tarski(A_34, B_33))), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.22/2.48  tff(c_67, plain, (![A_8]: (k1_xboole_0=A_8 | ~r1_tarski(A_8, k1_xboole_0))), inference(resolution, [status(thm)], [c_16, c_55])).
% 7.22/2.48  tff(c_133, plain, (![B_50]: (k1_xboole_0=B_50 | ~v1_xboole_0(B_50))), inference(resolution, [status(thm)], [c_116, c_67])).
% 7.22/2.48  tff(c_1960, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_1946, c_133])).
% 7.22/2.48  tff(c_1945, plain, (v1_xboole_0('#skF_2')), inference(splitRight, [status(thm)], [c_210])).
% 7.22/2.48  tff(c_1953, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_1945, c_133])).
% 7.22/2.48  tff(c_1977, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1960, c_1953])).
% 7.22/2.48  tff(c_1986, plain, (~r1_tarski(k5_partfun1('#skF_3', '#skF_3', '#skF_4'), k1_funct_2('#skF_3', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1977, c_1977, c_36])).
% 7.22/2.48  tff(c_1988, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_1977, c_38])).
% 7.22/2.48  tff(c_2294, plain, (![A_378, B_379, C_380, B_381]: (v1_funct_1('#skF_1'(k5_partfun1(A_378, B_379, C_380), B_381)) | ~m1_subset_1(C_380, k1_zfmisc_1(k2_zfmisc_1(A_378, B_379))) | ~v1_funct_1(C_380) | r1_tarski(k5_partfun1(A_378, B_379, C_380), B_381))), inference(resolution, [status(thm)], [c_6, c_160])).
% 7.22/2.48  tff(c_2296, plain, (![B_381]: (v1_funct_1('#skF_1'(k5_partfun1('#skF_3', '#skF_3', '#skF_4'), B_381)) | ~v1_funct_1('#skF_4') | r1_tarski(k5_partfun1('#skF_3', '#skF_3', '#skF_4'), B_381))), inference(resolution, [status(thm)], [c_1988, c_2294])).
% 7.22/2.48  tff(c_2302, plain, (![B_381]: (v1_funct_1('#skF_1'(k5_partfun1('#skF_3', '#skF_3', '#skF_4'), B_381)) | r1_tarski(k5_partfun1('#skF_3', '#skF_3', '#skF_4'), B_381))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_2296])).
% 7.22/2.48  tff(c_2031, plain, (![D_342, A_343, B_344, C_345]: (v1_funct_2(D_342, A_343, B_344) | ~r2_hidden(D_342, k5_partfun1(A_343, B_344, C_345)) | ~m1_subset_1(C_345, k1_zfmisc_1(k2_zfmisc_1(A_343, B_344))) | ~v1_funct_1(C_345))), inference(cnfTransformation, [status(thm)], [f_88])).
% 7.22/2.48  tff(c_2615, plain, (![A_459, B_461, C_463, B_460, A_462]: (v1_funct_2('#skF_1'(A_462, B_461), A_459, B_460) | ~m1_subset_1(C_463, k1_zfmisc_1(k2_zfmisc_1(A_459, B_460))) | ~v1_funct_1(C_463) | ~r1_tarski(A_462, k5_partfun1(A_459, B_460, C_463)) | r1_tarski(A_462, B_461))), inference(resolution, [status(thm)], [c_99, c_2031])).
% 7.22/2.48  tff(c_2619, plain, (![A_462, B_461]: (v1_funct_2('#skF_1'(A_462, B_461), '#skF_3', '#skF_3') | ~v1_funct_1('#skF_4') | ~r1_tarski(A_462, k5_partfun1('#skF_3', '#skF_3', '#skF_4')) | r1_tarski(A_462, B_461))), inference(resolution, [status(thm)], [c_1988, c_2615])).
% 7.22/2.48  tff(c_2626, plain, (![A_462, B_461]: (v1_funct_2('#skF_1'(A_462, B_461), '#skF_3', '#skF_3') | ~r1_tarski(A_462, k5_partfun1('#skF_3', '#skF_3', '#skF_4')) | r1_tarski(A_462, B_461))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_2619])).
% 7.22/2.48  tff(c_2174, plain, (![D_360, A_361, B_362, C_363]: (m1_subset_1(D_360, k1_zfmisc_1(k2_zfmisc_1(A_361, B_362))) | ~r2_hidden(D_360, k5_partfun1(A_361, B_362, C_363)) | ~m1_subset_1(C_363, k1_zfmisc_1(k2_zfmisc_1(A_361, B_362))) | ~v1_funct_1(C_363))), inference(cnfTransformation, [status(thm)], [f_88])).
% 7.22/2.48  tff(c_2910, plain, (![A_528, B_526, C_525, A_527, B_524]: (m1_subset_1('#skF_1'(A_528, B_526), k1_zfmisc_1(k2_zfmisc_1(A_527, B_524))) | ~m1_subset_1(C_525, k1_zfmisc_1(k2_zfmisc_1(A_527, B_524))) | ~v1_funct_1(C_525) | ~r1_tarski(A_528, k5_partfun1(A_527, B_524, C_525)) | r1_tarski(A_528, B_526))), inference(resolution, [status(thm)], [c_99, c_2174])).
% 7.22/2.48  tff(c_2914, plain, (![A_528, B_526]: (m1_subset_1('#skF_1'(A_528, B_526), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3'))) | ~v1_funct_1('#skF_4') | ~r1_tarski(A_528, k5_partfun1('#skF_3', '#skF_3', '#skF_4')) | r1_tarski(A_528, B_526))), inference(resolution, [status(thm)], [c_1988, c_2910])).
% 7.22/2.48  tff(c_2923, plain, (![A_529, B_530]: (m1_subset_1('#skF_1'(A_529, B_530), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3'))) | ~r1_tarski(A_529, k5_partfun1('#skF_3', '#skF_3', '#skF_4')) | r1_tarski(A_529, B_530))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_2914])).
% 7.22/2.48  tff(c_26, plain, (![C_19, B_18]: (r2_hidden(C_19, k1_funct_2(k1_xboole_0, B_18)) | ~m1_subset_1(C_19, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_18))) | ~v1_funct_2(C_19, k1_xboole_0, B_18) | ~v1_funct_1(C_19))), inference(cnfTransformation, [status(thm)], [f_75])).
% 7.22/2.48  tff(c_1967, plain, (![C_19, B_18]: (r2_hidden(C_19, k1_funct_2('#skF_2', B_18)) | ~m1_subset_1(C_19, k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_18))) | ~v1_funct_2(C_19, '#skF_2', B_18) | ~v1_funct_1(C_19))), inference(demodulation, [status(thm), theory('equality')], [c_1953, c_1953, c_1953, c_26])).
% 7.22/2.48  tff(c_2384, plain, (![C_19, B_18]: (r2_hidden(C_19, k1_funct_2('#skF_3', B_18)) | ~m1_subset_1(C_19, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_18))) | ~v1_funct_2(C_19, '#skF_3', B_18) | ~v1_funct_1(C_19))), inference(demodulation, [status(thm), theory('equality')], [c_1977, c_1977, c_1977, c_1967])).
% 7.22/2.48  tff(c_3049, plain, (![A_545, B_546]: (r2_hidden('#skF_1'(A_545, B_546), k1_funct_2('#skF_3', '#skF_3')) | ~v1_funct_2('#skF_1'(A_545, B_546), '#skF_3', '#skF_3') | ~v1_funct_1('#skF_1'(A_545, B_546)) | ~r1_tarski(A_545, k5_partfun1('#skF_3', '#skF_3', '#skF_4')) | r1_tarski(A_545, B_546))), inference(resolution, [status(thm)], [c_2923, c_2384])).
% 7.22/2.48  tff(c_3764, plain, (![A_608]: (~v1_funct_2('#skF_1'(A_608, k1_funct_2('#skF_3', '#skF_3')), '#skF_3', '#skF_3') | ~v1_funct_1('#skF_1'(A_608, k1_funct_2('#skF_3', '#skF_3'))) | ~r1_tarski(A_608, k5_partfun1('#skF_3', '#skF_3', '#skF_4')) | r1_tarski(A_608, k1_funct_2('#skF_3', '#skF_3')))), inference(resolution, [status(thm)], [c_3049, c_4])).
% 7.22/2.48  tff(c_3780, plain, (![A_609]: (~v1_funct_1('#skF_1'(A_609, k1_funct_2('#skF_3', '#skF_3'))) | ~r1_tarski(A_609, k5_partfun1('#skF_3', '#skF_3', '#skF_4')) | r1_tarski(A_609, k1_funct_2('#skF_3', '#skF_3')))), inference(resolution, [status(thm)], [c_2626, c_3764])).
% 7.22/2.48  tff(c_3796, plain, (~r1_tarski(k5_partfun1('#skF_3', '#skF_3', '#skF_4'), k5_partfun1('#skF_3', '#skF_3', '#skF_4')) | r1_tarski(k5_partfun1('#skF_3', '#skF_3', '#skF_4'), k1_funct_2('#skF_3', '#skF_3'))), inference(resolution, [status(thm)], [c_2302, c_3780])).
% 7.22/2.48  tff(c_3802, plain, (r1_tarski(k5_partfun1('#skF_3', '#skF_3', '#skF_4'), k1_funct_2('#skF_3', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_3796])).
% 7.22/2.48  tff(c_3804, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1986, c_3802])).
% 7.22/2.48  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.22/2.48  
% 7.22/2.48  Inference rules
% 7.22/2.48  ----------------------
% 7.22/2.48  #Ref     : 0
% 7.22/2.48  #Sup     : 909
% 7.22/2.48  #Fact    : 0
% 7.22/2.48  #Define  : 0
% 7.22/2.48  #Split   : 22
% 7.22/2.48  #Chain   : 0
% 7.22/2.48  #Close   : 0
% 7.22/2.48  
% 7.22/2.48  Ordering : KBO
% 7.22/2.48  
% 7.22/2.48  Simplification rules
% 7.22/2.48  ----------------------
% 7.22/2.48  #Subsume      : 319
% 7.22/2.48  #Demod        : 213
% 7.22/2.48  #Tautology    : 92
% 7.22/2.48  #SimpNegUnit  : 14
% 7.22/2.49  #BackRed      : 46
% 7.22/2.49  
% 7.22/2.49  #Partial instantiations: 0
% 7.22/2.49  #Strategies tried      : 1
% 7.22/2.49  
% 7.27/2.49  Timing (in seconds)
% 7.27/2.49  ----------------------
% 7.27/2.49  Preprocessing        : 0.30
% 7.27/2.49  Parsing              : 0.16
% 7.27/2.49  CNF conversion       : 0.02
% 7.27/2.49  Main loop            : 1.40
% 7.27/2.49  Inferencing          : 0.41
% 7.27/2.49  Reduction            : 0.33
% 7.27/2.49  Demodulation         : 0.21
% 7.27/2.49  BG Simplification    : 0.04
% 7.27/2.49  Subsumption          : 0.53
% 7.27/2.49  Abstraction          : 0.05
% 7.27/2.49  MUC search           : 0.00
% 7.27/2.49  Cooper               : 0.00
% 7.27/2.49  Total                : 1.75
% 7.27/2.49  Index Insertion      : 0.00
% 7.27/2.49  Index Deletion       : 0.00
% 7.27/2.49  Index Matching       : 0.00
% 7.27/2.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
