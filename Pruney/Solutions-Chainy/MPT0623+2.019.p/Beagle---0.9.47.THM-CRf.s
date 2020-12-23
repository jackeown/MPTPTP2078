%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:08 EST 2020

% Result     : Theorem 14.02s
% Output     : CNFRefutation 14.28s
% Verified   : 
% Statistics : Number of formulae       :  192 (2041 expanded)
%              Number of leaves         :   31 ( 705 expanded)
%              Depth                    :   19
%              Number of atoms          :  400 (6469 expanded)
%              Number of equality atoms :  110 (2582 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_2 > #skF_6 > #skF_3 > #skF_10 > #skF_8 > #skF_9 > #skF_1 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_7',type,(
    '#skF_7': $i > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_79,axiom,(
    ! [A] :
    ? [B] :
      ( v1_relat_1(B)
      & v1_funct_1(B)
      & k1_relat_1(B) = A
      & ! [C] :
          ( r2_hidden(C,A)
         => k1_funct_1(B,C) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e2_25__funct_1)).

tff(f_110,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( ~ ( A = k1_xboole_0
              & B != k1_xboole_0 )
          & ! [C] :
              ( ( v1_relat_1(C)
                & v1_funct_1(C) )
             => ~ ( B = k1_relat_1(C)
                  & r1_tarski(k2_relat_1(C),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_funct_1)).

tff(f_40,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_92,axiom,(
    ! [A] :
      ( A != k1_xboole_0
     => ! [B] :
        ? [C] :
          ( v1_relat_1(C)
          & v1_funct_1(C)
          & k1_relat_1(C) = A
          & k2_relat_1(C) = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_funct_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_67,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( B = k2_relat_1(A)
        <=> ! [C] :
              ( r2_hidden(C,B)
            <=> ? [D] :
                  ( r2_hidden(D,k1_relat_1(A))
                  & C = k1_funct_1(A,D) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).

tff(f_48,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_46,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_46,plain,(
    ! [A_53] : v1_relat_1('#skF_7'(A_53)) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_44,plain,(
    ! [A_53] : v1_funct_1('#skF_7'(A_53)) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_42,plain,(
    ! [A_53] : k1_relat_1('#skF_7'(A_53)) = A_53 ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_58,plain,
    ( k1_xboole_0 = '#skF_10'
    | k1_xboole_0 != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_73,plain,(
    k1_xboole_0 != '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_8,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'(A_6),A_6)
      | k1_xboole_0 = A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_50,plain,(
    ! [A_59,B_63] :
      ( k1_relat_1('#skF_8'(A_59,B_63)) = A_59
      | k1_xboole_0 = A_59 ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_52,plain,(
    ! [A_59,B_63] :
      ( v1_funct_1('#skF_8'(A_59,B_63))
      | k1_xboole_0 = A_59 ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_54,plain,(
    ! [A_59,B_63] :
      ( v1_relat_1('#skF_8'(A_59,B_63))
      | k1_xboole_0 = A_59 ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_20,plain,(
    ! [A_11,B_12] :
      ( r1_tarski(k1_tarski(A_11),B_12)
      | ~ r2_hidden(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_111,plain,(
    ! [A_89,B_90] :
      ( k2_relat_1('#skF_8'(A_89,B_90)) = k1_tarski(B_90)
      | k1_xboole_0 = A_89 ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_56,plain,(
    ! [C_66] :
      ( ~ r1_tarski(k2_relat_1(C_66),'#skF_9')
      | k1_relat_1(C_66) != '#skF_10'
      | ~ v1_funct_1(C_66)
      | ~ v1_relat_1(C_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_130,plain,(
    ! [B_93,A_94] :
      ( ~ r1_tarski(k1_tarski(B_93),'#skF_9')
      | k1_relat_1('#skF_8'(A_94,B_93)) != '#skF_10'
      | ~ v1_funct_1('#skF_8'(A_94,B_93))
      | ~ v1_relat_1('#skF_8'(A_94,B_93))
      | k1_xboole_0 = A_94 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_111,c_56])).

tff(c_240,plain,(
    ! [A_110,A_111] :
      ( k1_relat_1('#skF_8'(A_110,A_111)) != '#skF_10'
      | ~ v1_funct_1('#skF_8'(A_110,A_111))
      | ~ v1_relat_1('#skF_8'(A_110,A_111))
      | k1_xboole_0 = A_110
      | ~ r2_hidden(A_111,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_20,c_130])).

tff(c_373,plain,(
    ! [A_128,B_129] :
      ( k1_relat_1('#skF_8'(A_128,B_129)) != '#skF_10'
      | ~ v1_funct_1('#skF_8'(A_128,B_129))
      | ~ r2_hidden(B_129,'#skF_9')
      | k1_xboole_0 = A_128 ) ),
    inference(resolution,[status(thm)],[c_54,c_240])).

tff(c_426,plain,(
    ! [A_133,B_134] :
      ( k1_relat_1('#skF_8'(A_133,B_134)) != '#skF_10'
      | ~ r2_hidden(B_134,'#skF_9')
      | k1_xboole_0 = A_133 ) ),
    inference(resolution,[status(thm)],[c_52,c_373])).

tff(c_429,plain,(
    ! [A_59,B_63] :
      ( A_59 != '#skF_10'
      | ~ r2_hidden(B_63,'#skF_9')
      | k1_xboole_0 = A_59
      | k1_xboole_0 = A_59 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_426])).

tff(c_431,plain,(
    ! [B_135] : ~ r2_hidden(B_135,'#skF_9') ),
    inference(splitLeft,[status(thm)],[c_429])).

tff(c_443,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(resolution,[status(thm)],[c_8,c_431])).

tff(c_449,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_73,c_443])).

tff(c_478,plain,(
    k1_xboole_0 = '#skF_10' ),
    inference(splitRight,[status(thm)],[c_429])).

tff(c_500,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'(A_6),A_6)
      | A_6 = '#skF_10' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_478,c_8])).

tff(c_316,plain,(
    ! [A_120,C_121] :
      ( r2_hidden('#skF_6'(A_120,k2_relat_1(A_120),C_121),k1_relat_1(A_120))
      | ~ r2_hidden(C_121,k2_relat_1(A_120))
      | ~ v1_funct_1(A_120)
      | ~ v1_relat_1(A_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_329,plain,(
    ! [A_53,C_121] :
      ( r2_hidden('#skF_6'('#skF_7'(A_53),k2_relat_1('#skF_7'(A_53)),C_121),A_53)
      | ~ r2_hidden(C_121,k2_relat_1('#skF_7'(A_53)))
      | ~ v1_funct_1('#skF_7'(A_53))
      | ~ v1_relat_1('#skF_7'(A_53)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_316])).

tff(c_333,plain,(
    ! [A_53,C_121] :
      ( r2_hidden('#skF_6'('#skF_7'(A_53),k2_relat_1('#skF_7'(A_53)),C_121),A_53)
      | ~ r2_hidden(C_121,k2_relat_1('#skF_7'(A_53))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_329])).

tff(c_1230,plain,(
    ! [A_233,C_234] :
      ( r2_hidden('#skF_6'('#skF_7'(A_233),k2_relat_1('#skF_7'(A_233)),C_234),A_233)
      | ~ r2_hidden(C_234,k2_relat_1('#skF_7'(A_233))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_329])).

tff(c_40,plain,(
    ! [A_53,C_58] :
      ( k1_funct_1('#skF_7'(A_53),C_58) = k1_xboole_0
      | ~ r2_hidden(C_58,A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_198,plain,(
    ! [A_104,D_105] :
      ( r2_hidden(k1_funct_1(A_104,D_105),k2_relat_1(A_104))
      | ~ r2_hidden(D_105,k1_relat_1(A_104))
      | ~ v1_funct_1(A_104)
      | ~ v1_relat_1(A_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_206,plain,(
    ! [A_53,C_58] :
      ( r2_hidden(k1_xboole_0,k2_relat_1('#skF_7'(A_53)))
      | ~ r2_hidden(C_58,k1_relat_1('#skF_7'(A_53)))
      | ~ v1_funct_1('#skF_7'(A_53))
      | ~ v1_relat_1('#skF_7'(A_53))
      | ~ r2_hidden(C_58,A_53) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_198])).

tff(c_209,plain,(
    ! [A_53,C_58] :
      ( r2_hidden(k1_xboole_0,k2_relat_1('#skF_7'(A_53)))
      | ~ r2_hidden(C_58,A_53) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_206])).

tff(c_491,plain,(
    ! [A_53,C_58] :
      ( r2_hidden('#skF_10',k2_relat_1('#skF_7'(A_53)))
      | ~ r2_hidden(C_58,A_53) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_478,c_209])).

tff(c_1259,plain,(
    ! [A_235,C_236] :
      ( r2_hidden('#skF_10',k2_relat_1('#skF_7'(A_235)))
      | ~ r2_hidden(C_236,k2_relat_1('#skF_7'(A_235))) ) ),
    inference(resolution,[status(thm)],[c_1230,c_491])).

tff(c_26708,plain,(
    ! [A_4173,C_4174] :
      ( r2_hidden('#skF_10',k2_relat_1('#skF_7'(A_4173)))
      | ~ r2_hidden(C_4174,k2_relat_1('#skF_7'(k2_relat_1('#skF_7'(A_4173))))) ) ),
    inference(resolution,[status(thm)],[c_333,c_1259])).

tff(c_26950,plain,(
    ! [A_4173] :
      ( r2_hidden('#skF_10',k2_relat_1('#skF_7'(A_4173)))
      | k2_relat_1('#skF_7'(k2_relat_1('#skF_7'(A_4173)))) = '#skF_10' ) ),
    inference(resolution,[status(thm)],[c_500,c_26708])).

tff(c_16,plain,(
    ! [A_10] : r1_tarski(k1_xboole_0,A_10) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_503,plain,(
    ! [A_10] : r1_tarski('#skF_10',A_10) ),
    inference(demodulation,[status(thm),theory(equality)],[c_478,c_16])).

tff(c_27275,plain,(
    ! [A_4256] :
      ( r2_hidden('#skF_10',k2_relat_1('#skF_7'(A_4256)))
      | k2_relat_1('#skF_7'(k2_relat_1('#skF_7'(A_4256)))) = '#skF_10' ) ),
    inference(resolution,[status(thm)],[c_500,c_26708])).

tff(c_27438,plain,(
    ! [A_4256] :
      ( ~ r1_tarski('#skF_10','#skF_9')
      | k1_relat_1('#skF_7'(k2_relat_1('#skF_7'(A_4256)))) != '#skF_10'
      | ~ v1_funct_1('#skF_7'(k2_relat_1('#skF_7'(A_4256))))
      | ~ v1_relat_1('#skF_7'(k2_relat_1('#skF_7'(A_4256))))
      | r2_hidden('#skF_10',k2_relat_1('#skF_7'(A_4256))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_27275,c_56])).

tff(c_28152,plain,(
    ! [A_4297] :
      ( k2_relat_1('#skF_7'(A_4297)) != '#skF_10'
      | r2_hidden('#skF_10',k2_relat_1('#skF_7'(A_4297))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_503,c_27438])).

tff(c_1300,plain,(
    ! [A_235,C_121] :
      ( r2_hidden('#skF_10',k2_relat_1('#skF_7'(A_235)))
      | ~ r2_hidden(C_121,k2_relat_1('#skF_7'(k2_relat_1('#skF_7'(A_235))))) ) ),
    inference(resolution,[status(thm)],[c_333,c_1259])).

tff(c_29540,plain,(
    ! [A_4433] :
      ( r2_hidden('#skF_10',k2_relat_1('#skF_7'(A_4433)))
      | k2_relat_1('#skF_7'(k2_relat_1('#skF_7'(A_4433)))) != '#skF_10' ) ),
    inference(resolution,[status(thm)],[c_28152,c_1300])).

tff(c_29661,plain,(
    ! [A_4173] : r2_hidden('#skF_10',k2_relat_1('#skF_7'(A_4173))) ),
    inference(superposition,[status(thm),theory(equality)],[c_26950,c_29540])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_451,plain,(
    ! [A_136,C_137] :
      ( k1_funct_1(A_136,'#skF_6'(A_136,k2_relat_1(A_136),C_137)) = C_137
      | ~ r2_hidden(C_137,k2_relat_1(A_136))
      | ~ v1_funct_1(A_136)
      | ~ v1_relat_1(A_136) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_471,plain,(
    ! [C_137,A_53] :
      ( k1_xboole_0 = C_137
      | ~ r2_hidden(C_137,k2_relat_1('#skF_7'(A_53)))
      | ~ v1_funct_1('#skF_7'(A_53))
      | ~ v1_relat_1('#skF_7'(A_53))
      | ~ r2_hidden('#skF_6'('#skF_7'(A_53),k2_relat_1('#skF_7'(A_53)),C_137),A_53) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_451])).

tff(c_477,plain,(
    ! [C_137,A_53] :
      ( k1_xboole_0 = C_137
      | ~ r2_hidden(C_137,k2_relat_1('#skF_7'(A_53)))
      | ~ r2_hidden('#skF_6'('#skF_7'(A_53),k2_relat_1('#skF_7'(A_53)),C_137),A_53) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_471])).

tff(c_1455,plain,(
    ! [C_249,A_250] :
      ( C_249 = '#skF_10'
      | ~ r2_hidden(C_249,k2_relat_1('#skF_7'(A_250)))
      | ~ r2_hidden('#skF_6'('#skF_7'(A_250),k2_relat_1('#skF_7'(A_250)),C_249),A_250) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_478,c_477])).

tff(c_1460,plain,(
    ! [C_251,A_252] :
      ( C_251 = '#skF_10'
      | ~ r2_hidden(C_251,k2_relat_1('#skF_7'(A_252))) ) ),
    inference(resolution,[status(thm)],[c_333,c_1455])).

tff(c_1605,plain,(
    ! [A_256,B_257] :
      ( '#skF_1'(k2_relat_1('#skF_7'(A_256)),B_257) = '#skF_10'
      | r1_tarski(k2_relat_1('#skF_7'(A_256)),B_257) ) ),
    inference(resolution,[status(thm)],[c_6,c_1460])).

tff(c_179,plain,(
    ! [C_99,B_100,A_101] :
      ( r2_hidden(C_99,B_100)
      | ~ r2_hidden(C_99,A_101)
      | ~ r1_tarski(A_101,B_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_879,plain,(
    ! [A_191,B_192,B_193] :
      ( r2_hidden('#skF_1'(A_191,B_192),B_193)
      | ~ r1_tarski(A_191,B_193)
      | r1_tarski(A_191,B_192) ) ),
    inference(resolution,[status(thm)],[c_6,c_179])).

tff(c_135,plain,(
    ! [B_95,A_96] :
      ( B_95 = A_96
      | ~ r1_tarski(B_95,A_96)
      | ~ r1_tarski(A_96,B_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_148,plain,(
    ! [A_97] :
      ( k1_xboole_0 = A_97
      | ~ r1_tarski(A_97,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_16,c_135])).

tff(c_161,plain,(
    ! [A_11] :
      ( k1_tarski(A_11) = k1_xboole_0
      | ~ r2_hidden(A_11,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_20,c_148])).

tff(c_493,plain,(
    ! [A_11] :
      ( k1_tarski(A_11) = '#skF_10'
      | ~ r2_hidden(A_11,'#skF_10') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_478,c_478,c_161])).

tff(c_946,plain,(
    ! [A_203,B_204] :
      ( k1_tarski('#skF_1'(A_203,B_204)) = '#skF_10'
      | ~ r1_tarski(A_203,'#skF_10')
      | r1_tarski(A_203,B_204) ) ),
    inference(resolution,[status(thm)],[c_879,c_493])).

tff(c_18,plain,(
    ! [A_11,B_12] :
      ( r2_hidden(A_11,B_12)
      | ~ r1_tarski(k1_tarski(A_11),B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_973,plain,(
    ! [A_203,B_204,B_12] :
      ( r2_hidden('#skF_1'(A_203,B_204),B_12)
      | ~ r1_tarski('#skF_10',B_12)
      | ~ r1_tarski(A_203,'#skF_10')
      | r1_tarski(A_203,B_204) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_946,c_18])).

tff(c_1007,plain,(
    ! [A_211,B_212,B_213] :
      ( r2_hidden('#skF_1'(A_211,B_212),B_213)
      | ~ r1_tarski(A_211,'#skF_10')
      | r1_tarski(A_211,B_212) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_503,c_973])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1023,plain,(
    ! [A_211,B_213] :
      ( ~ r1_tarski(A_211,'#skF_10')
      | r1_tarski(A_211,B_213) ) ),
    inference(resolution,[status(thm)],[c_1007,c_4])).

tff(c_1865,plain,(
    ! [A_266,B_267] :
      ( r1_tarski(k2_relat_1('#skF_7'(A_266)),B_267)
      | '#skF_1'(k2_relat_1('#skF_7'(A_266)),'#skF_10') = '#skF_10' ) ),
    inference(resolution,[status(thm)],[c_1605,c_1023])).

tff(c_14,plain,(
    ! [B_9] : r1_tarski(B_9,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_88,plain,(
    ! [A_80,B_81] :
      ( r2_hidden(A_80,B_81)
      | ~ r1_tarski(k1_tarski(A_80),B_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_93,plain,(
    ! [A_80] : r2_hidden(A_80,k1_tarski(A_80)) ),
    inference(resolution,[status(thm)],[c_14,c_88])).

tff(c_210,plain,(
    ! [A_106,C_107] :
      ( r2_hidden(k1_xboole_0,k2_relat_1('#skF_7'(A_106)))
      | ~ r2_hidden(C_107,A_106) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_206])).

tff(c_226,plain,(
    ! [A_108] : r2_hidden(k1_xboole_0,k2_relat_1('#skF_7'(k1_tarski(A_108)))) ),
    inference(resolution,[status(thm)],[c_93,c_210])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_232,plain,(
    ! [B_2,A_108] :
      ( r2_hidden(k1_xboole_0,B_2)
      | ~ r1_tarski(k2_relat_1('#skF_7'(k1_tarski(A_108))),B_2) ) ),
    inference(resolution,[status(thm)],[c_226,c_2])).

tff(c_486,plain,(
    ! [B_2,A_108] :
      ( r2_hidden('#skF_10',B_2)
      | ~ r1_tarski(k2_relat_1('#skF_7'(k1_tarski(A_108))),B_2) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_478,c_232])).

tff(c_1922,plain,(
    ! [B_267,A_108] :
      ( r2_hidden('#skF_10',B_267)
      | '#skF_1'(k2_relat_1('#skF_7'(k1_tarski(A_108))),'#skF_10') = '#skF_10' ) ),
    inference(resolution,[status(thm)],[c_1865,c_486])).

tff(c_1976,plain,(
    ! [A_269] : '#skF_1'(k2_relat_1('#skF_7'(k1_tarski(A_269))),'#skF_10') = '#skF_10' ),
    inference(splitLeft,[status(thm)],[c_1922])).

tff(c_1996,plain,(
    ! [A_269] :
      ( ~ r2_hidden('#skF_10','#skF_10')
      | r1_tarski(k2_relat_1('#skF_7'(k1_tarski(A_269))),'#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1976,c_4])).

tff(c_2026,plain,(
    ~ r2_hidden('#skF_10','#skF_10') ),
    inference(splitLeft,[status(thm)],[c_1996])).

tff(c_1459,plain,(
    ! [C_121,A_53] :
      ( C_121 = '#skF_10'
      | ~ r2_hidden(C_121,k2_relat_1('#skF_7'(A_53))) ) ),
    inference(resolution,[status(thm)],[c_333,c_1455])).

tff(c_27368,plain,(
    ! [C_121,A_4256] :
      ( C_121 = '#skF_10'
      | ~ r2_hidden(C_121,'#skF_10')
      | r2_hidden('#skF_10',k2_relat_1('#skF_7'(A_4256))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_27275,c_1459])).

tff(c_28476,plain,(
    ! [A_4256] : r2_hidden('#skF_10',k2_relat_1('#skF_7'(A_4256))) ),
    inference(splitLeft,[status(thm)],[c_27368])).

tff(c_29216,plain,(
    ! [C_4384] :
      ( k1_tarski('#skF_6'('#skF_7'('#skF_10'),k2_relat_1('#skF_7'('#skF_10')),C_4384)) = '#skF_10'
      | ~ r2_hidden(C_4384,k2_relat_1('#skF_7'('#skF_10'))) ) ),
    inference(resolution,[status(thm)],[c_1230,c_493])).

tff(c_29260,plain,(
    ! [C_4384,B_12] :
      ( r2_hidden('#skF_6'('#skF_7'('#skF_10'),k2_relat_1('#skF_7'('#skF_10')),C_4384),B_12)
      | ~ r1_tarski('#skF_10',B_12)
      | ~ r2_hidden(C_4384,k2_relat_1('#skF_7'('#skF_10'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_29216,c_18])).

tff(c_29286,plain,(
    ! [C_4388,B_4389] :
      ( r2_hidden('#skF_6'('#skF_7'('#skF_10'),k2_relat_1('#skF_7'('#skF_10')),C_4388),B_4389)
      | ~ r2_hidden(C_4388,k2_relat_1('#skF_7'('#skF_10'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_503,c_29260])).

tff(c_29323,plain,(
    ! [C_4390] :
      ( '#skF_6'('#skF_7'('#skF_10'),k2_relat_1('#skF_7'('#skF_10')),C_4390) = '#skF_10'
      | ~ r2_hidden(C_4390,k2_relat_1('#skF_7'('#skF_10'))) ) ),
    inference(resolution,[status(thm)],[c_29286,c_1459])).

tff(c_26,plain,(
    ! [A_13,C_49] :
      ( r2_hidden('#skF_6'(A_13,k2_relat_1(A_13),C_49),k1_relat_1(A_13))
      | ~ r2_hidden(C_49,k2_relat_1(A_13))
      | ~ v1_funct_1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_29344,plain,(
    ! [C_4390] :
      ( r2_hidden('#skF_10',k1_relat_1('#skF_7'('#skF_10')))
      | ~ r2_hidden(C_4390,k2_relat_1('#skF_7'('#skF_10')))
      | ~ v1_funct_1('#skF_7'('#skF_10'))
      | ~ v1_relat_1('#skF_7'('#skF_10'))
      | ~ r2_hidden(C_4390,k2_relat_1('#skF_7'('#skF_10'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_29323,c_26])).

tff(c_29356,plain,(
    ! [C_4390] :
      ( r2_hidden('#skF_10','#skF_10')
      | ~ r2_hidden(C_4390,k2_relat_1('#skF_7'('#skF_10'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_29344])).

tff(c_29359,plain,(
    ! [C_4391] : ~ r2_hidden(C_4391,k2_relat_1('#skF_7'('#skF_10'))) ),
    inference(negUnitSimplification,[status(thm)],[c_2026,c_29356])).

tff(c_29454,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_28476,c_29359])).

tff(c_29456,plain,(
    ! [C_4392] :
      ( C_4392 = '#skF_10'
      | ~ r2_hidden(C_4392,'#skF_10') ) ),
    inference(splitRight,[status(thm)],[c_27368])).

tff(c_30662,plain,(
    ! [C_4551] :
      ( '#skF_6'('#skF_7'('#skF_10'),k2_relat_1('#skF_7'('#skF_10')),C_4551) = '#skF_10'
      | ~ r2_hidden(C_4551,k2_relat_1('#skF_7'('#skF_10'))) ) ),
    inference(resolution,[status(thm)],[c_333,c_29456])).

tff(c_30677,plain,(
    ! [C_4551] :
      ( r2_hidden('#skF_10',k1_relat_1('#skF_7'('#skF_10')))
      | ~ r2_hidden(C_4551,k2_relat_1('#skF_7'('#skF_10')))
      | ~ v1_funct_1('#skF_7'('#skF_10'))
      | ~ v1_relat_1('#skF_7'('#skF_10'))
      | ~ r2_hidden(C_4551,k2_relat_1('#skF_7'('#skF_10'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30662,c_26])).

tff(c_30688,plain,(
    ! [C_4551] :
      ( r2_hidden('#skF_10','#skF_10')
      | ~ r2_hidden(C_4551,k2_relat_1('#skF_7'('#skF_10'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_30677])).

tff(c_30691,plain,(
    ! [C_4552] : ~ r2_hidden(C_4552,k2_relat_1('#skF_7'('#skF_10'))) ),
    inference(negUnitSimplification,[status(thm)],[c_2026,c_30688])).

tff(c_30772,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_29661,c_30691])).

tff(c_30774,plain,(
    r2_hidden('#skF_10','#skF_10') ),
    inference(splitRight,[status(thm)],[c_1996])).

tff(c_1024,plain,(
    ! [A_214,B_215] :
      ( ~ r1_tarski(A_214,'#skF_10')
      | r1_tarski(A_214,B_215) ) ),
    inference(resolution,[status(thm)],[c_1007,c_4])).

tff(c_1050,plain,(
    ! [A_219,B_220] :
      ( r1_tarski(k1_tarski(A_219),B_220)
      | ~ r2_hidden(A_219,'#skF_10') ) ),
    inference(resolution,[status(thm)],[c_20,c_1024])).

tff(c_1084,plain,(
    ! [A_219,B_220] :
      ( r2_hidden(A_219,B_220)
      | ~ r2_hidden(A_219,'#skF_10') ) ),
    inference(resolution,[status(thm)],[c_1050,c_18])).

tff(c_30790,plain,(
    ! [B_220] : r2_hidden('#skF_10',B_220) ),
    inference(resolution,[status(thm)],[c_30774,c_1084])).

tff(c_1651,plain,(
    ! [A_256] :
      ( k1_relat_1('#skF_7'(A_256)) != '#skF_10'
      | ~ v1_funct_1('#skF_7'(A_256))
      | ~ v1_relat_1('#skF_7'(A_256))
      | '#skF_1'(k2_relat_1('#skF_7'(A_256)),'#skF_9') = '#skF_10' ) ),
    inference(resolution,[status(thm)],[c_1605,c_56])).

tff(c_1670,plain,(
    ! [A_258] :
      ( A_258 != '#skF_10'
      | '#skF_1'(k2_relat_1('#skF_7'(A_258)),'#skF_9') = '#skF_10' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_1651])).

tff(c_1679,plain,(
    ! [A_258] :
      ( ~ r2_hidden('#skF_10','#skF_9')
      | r1_tarski(k2_relat_1('#skF_7'(A_258)),'#skF_9')
      | A_258 != '#skF_10' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1670,c_4])).

tff(c_1745,plain,(
    ~ r2_hidden('#skF_10','#skF_9') ),
    inference(splitLeft,[status(thm)],[c_1679])).

tff(c_30821,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30790,c_1745])).

tff(c_30982,plain,(
    ! [A_4558] :
      ( r1_tarski(k2_relat_1('#skF_7'(A_4558)),'#skF_9')
      | A_4558 != '#skF_10' ) ),
    inference(splitRight,[status(thm)],[c_1679])).

tff(c_31008,plain,(
    ! [A_4558] :
      ( k1_relat_1('#skF_7'(A_4558)) != '#skF_10'
      | ~ v1_funct_1('#skF_7'(A_4558))
      | ~ v1_relat_1('#skF_7'(A_4558))
      | A_4558 != '#skF_10' ) ),
    inference(resolution,[status(thm)],[c_30982,c_56])).

tff(c_31027,plain,(
    ! [A_4558] : A_4558 != '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_31008])).

tff(c_147,plain,(
    ! [A_10] :
      ( k1_xboole_0 = A_10
      | ~ r1_tarski(A_10,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_16,c_135])).

tff(c_494,plain,(
    ! [A_10] :
      ( A_10 = '#skF_10'
      | ~ r1_tarski(A_10,'#skF_10') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_478,c_478,c_147])).

tff(c_1663,plain,(
    ! [A_256] :
      ( k2_relat_1('#skF_7'(A_256)) = '#skF_10'
      | '#skF_1'(k2_relat_1('#skF_7'(A_256)),'#skF_10') = '#skF_10' ) ),
    inference(resolution,[status(thm)],[c_1605,c_494])).

tff(c_31054,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_31027,c_31027,c_1663])).

tff(c_31056,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_31077,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'(A_6),A_6)
      | A_6 = '#skF_9' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_31056,c_8])).

tff(c_31317,plain,(
    ! [A_4606,C_4607] :
      ( r2_hidden('#skF_6'(A_4606,k2_relat_1(A_4606),C_4607),k1_relat_1(A_4606))
      | ~ r2_hidden(C_4607,k2_relat_1(A_4606))
      | ~ v1_funct_1(A_4606)
      | ~ v1_relat_1(A_4606) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_31330,plain,(
    ! [A_53,C_4607] :
      ( r2_hidden('#skF_6'('#skF_7'(A_53),k2_relat_1('#skF_7'(A_53)),C_4607),A_53)
      | ~ r2_hidden(C_4607,k2_relat_1('#skF_7'(A_53)))
      | ~ v1_funct_1('#skF_7'(A_53))
      | ~ v1_relat_1('#skF_7'(A_53)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_31317])).

tff(c_69584,plain,(
    ! [A_9721,C_9722] :
      ( r2_hidden('#skF_6'('#skF_7'(A_9721),k2_relat_1('#skF_7'(A_9721)),C_9722),A_9721)
      | ~ r2_hidden(C_9722,k2_relat_1('#skF_7'(A_9721))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_31330])).

tff(c_31156,plain,(
    ! [A_53,C_58] :
      ( k1_funct_1('#skF_7'(A_53),C_58) = '#skF_9'
      | ~ r2_hidden(C_58,A_53) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_31056,c_40])).

tff(c_31199,plain,(
    ! [A_4590,D_4591] :
      ( r2_hidden(k1_funct_1(A_4590,D_4591),k2_relat_1(A_4590))
      | ~ r2_hidden(D_4591,k1_relat_1(A_4590))
      | ~ v1_funct_1(A_4590)
      | ~ v1_relat_1(A_4590) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_31207,plain,(
    ! [A_53,C_58] :
      ( r2_hidden('#skF_9',k2_relat_1('#skF_7'(A_53)))
      | ~ r2_hidden(C_58,k1_relat_1('#skF_7'(A_53)))
      | ~ v1_funct_1('#skF_7'(A_53))
      | ~ v1_relat_1('#skF_7'(A_53))
      | ~ r2_hidden(C_58,A_53) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_31156,c_31199])).

tff(c_31210,plain,(
    ! [A_53,C_58] :
      ( r2_hidden('#skF_9',k2_relat_1('#skF_7'(A_53)))
      | ~ r2_hidden(C_58,A_53) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_31207])).

tff(c_70160,plain,(
    ! [A_9763,C_9764] :
      ( r2_hidden('#skF_9',k2_relat_1('#skF_7'(A_9763)))
      | ~ r2_hidden(C_9764,k2_relat_1('#skF_7'(A_9763))) ) ),
    inference(resolution,[status(thm)],[c_69584,c_31210])).

tff(c_70361,plain,(
    ! [A_9763] :
      ( r2_hidden('#skF_9',k2_relat_1('#skF_7'(A_9763)))
      | k2_relat_1('#skF_7'(A_9763)) = '#skF_9' ) ),
    inference(resolution,[status(thm)],[c_31077,c_70160])).

tff(c_31334,plain,(
    ! [A_53,C_4607] :
      ( r2_hidden('#skF_6'('#skF_7'(A_53),k2_relat_1('#skF_7'(A_53)),C_4607),A_53)
      | ~ r2_hidden(C_4607,k2_relat_1('#skF_7'(A_53))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_31330])).

tff(c_71597,plain,(
    ! [A_9930,C_9931] :
      ( r2_hidden('#skF_9',k2_relat_1('#skF_7'(A_9930)))
      | ~ r2_hidden(C_9931,k2_relat_1('#skF_7'(k2_relat_1('#skF_7'(A_9930))))) ) ),
    inference(resolution,[status(thm)],[c_31334,c_70160])).

tff(c_71813,plain,(
    ! [A_9930] :
      ( r2_hidden('#skF_9',k2_relat_1('#skF_7'(A_9930)))
      | k2_relat_1('#skF_7'(k2_relat_1('#skF_7'(A_9930)))) = '#skF_9' ) ),
    inference(resolution,[status(thm)],[c_70361,c_71597])).

tff(c_31055,plain,(
    k1_xboole_0 = '#skF_10' ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_31062,plain,(
    '#skF_10' = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_31056,c_31055])).

tff(c_31057,plain,(
    ! [A_10] : r1_tarski('#skF_10',A_10) ),
    inference(demodulation,[status(thm),theory(equality)],[c_31055,c_16])).

tff(c_31071,plain,(
    ! [A_10] : r1_tarski('#skF_9',A_10) ),
    inference(demodulation,[status(thm),theory(equality)],[c_31062,c_31057])).

tff(c_72161,plain,(
    ! [A_10013] :
      ( r2_hidden('#skF_9',k2_relat_1('#skF_7'(A_10013)))
      | k2_relat_1('#skF_7'(k2_relat_1('#skF_7'(A_10013)))) = '#skF_9' ) ),
    inference(resolution,[status(thm)],[c_70361,c_71597])).

tff(c_31075,plain,(
    ! [C_66] :
      ( ~ r1_tarski(k2_relat_1(C_66),'#skF_9')
      | k1_relat_1(C_66) != '#skF_9'
      | ~ v1_funct_1(C_66)
      | ~ v1_relat_1(C_66) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_31062,c_56])).

tff(c_72336,plain,(
    ! [A_10013] :
      ( ~ r1_tarski('#skF_9','#skF_9')
      | k1_relat_1('#skF_7'(k2_relat_1('#skF_7'(A_10013)))) != '#skF_9'
      | ~ v1_funct_1('#skF_7'(k2_relat_1('#skF_7'(A_10013))))
      | ~ v1_relat_1('#skF_7'(k2_relat_1('#skF_7'(A_10013))))
      | r2_hidden('#skF_9',k2_relat_1('#skF_7'(A_10013))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_72161,c_31075])).

tff(c_73837,plain,(
    ! [A_10179] :
      ( k2_relat_1('#skF_7'(A_10179)) != '#skF_9'
      | r2_hidden('#skF_9',k2_relat_1('#skF_7'(A_10179))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_31071,c_72336])).

tff(c_70328,plain,(
    ! [A_9763,C_4607] :
      ( r2_hidden('#skF_9',k2_relat_1('#skF_7'(A_9763)))
      | ~ r2_hidden(C_4607,k2_relat_1('#skF_7'(k2_relat_1('#skF_7'(A_9763))))) ) ),
    inference(resolution,[status(thm)],[c_31334,c_70160])).

tff(c_74161,plain,(
    ! [A_10220] :
      ( r2_hidden('#skF_9',k2_relat_1('#skF_7'(A_10220)))
      | k2_relat_1('#skF_7'(k2_relat_1('#skF_7'(A_10220)))) != '#skF_9' ) ),
    inference(resolution,[status(thm)],[c_73837,c_70328])).

tff(c_74282,plain,(
    ! [A_9930] : r2_hidden('#skF_9',k2_relat_1('#skF_7'(A_9930))) ),
    inference(superposition,[status(thm),theory(equality)],[c_71813,c_74161])).

tff(c_31474,plain,(
    ! [A_4628,C_4629] :
      ( k1_funct_1(A_4628,'#skF_6'(A_4628,k2_relat_1(A_4628),C_4629)) = C_4629
      | ~ r2_hidden(C_4629,k2_relat_1(A_4628))
      | ~ v1_funct_1(A_4628)
      | ~ v1_relat_1(A_4628) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_31484,plain,(
    ! [C_4629,A_53] :
      ( C_4629 = '#skF_9'
      | ~ r2_hidden('#skF_6'('#skF_7'(A_53),k2_relat_1('#skF_7'(A_53)),C_4629),A_53)
      | ~ r2_hidden(C_4629,k2_relat_1('#skF_7'(A_53)))
      | ~ v1_funct_1('#skF_7'(A_53))
      | ~ v1_relat_1('#skF_7'(A_53)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_31474,c_31156])).

tff(c_73033,plain,(
    ! [C_10054,A_10055] :
      ( C_10054 = '#skF_9'
      | ~ r2_hidden('#skF_6'('#skF_7'(A_10055),k2_relat_1('#skF_7'(A_10055)),C_10054),A_10055)
      | ~ r2_hidden(C_10054,k2_relat_1('#skF_7'(A_10055))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_31484])).

tff(c_73095,plain,(
    ! [C_10096,A_10097] :
      ( C_10096 = '#skF_9'
      | ~ r2_hidden(C_10096,k2_relat_1('#skF_7'(A_10097))) ) ),
    inference(resolution,[status(thm)],[c_31334,c_73033])).

tff(c_74357,plain,(
    ! [A_10266,B_10267] :
      ( '#skF_1'(k2_relat_1('#skF_7'(A_10266)),B_10267) = '#skF_9'
      | r1_tarski(k2_relat_1('#skF_7'(A_10266)),B_10267) ) ),
    inference(resolution,[status(thm)],[c_6,c_73095])).

tff(c_74393,plain,(
    ! [A_10266] :
      ( k1_relat_1('#skF_7'(A_10266)) != '#skF_9'
      | ~ v1_funct_1('#skF_7'(A_10266))
      | ~ v1_relat_1('#skF_7'(A_10266))
      | '#skF_1'(k2_relat_1('#skF_7'(A_10266)),'#skF_9') = '#skF_9' ) ),
    inference(resolution,[status(thm)],[c_74357,c_31075])).

tff(c_74408,plain,(
    ! [A_10268] :
      ( A_10268 != '#skF_9'
      | '#skF_1'(k2_relat_1('#skF_7'(A_10268)),'#skF_9') = '#skF_9' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_74393])).

tff(c_74420,plain,(
    ! [A_10268] :
      ( ~ r2_hidden('#skF_9','#skF_9')
      | r1_tarski(k2_relat_1('#skF_7'(A_10268)),'#skF_9')
      | A_10268 != '#skF_9' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_74408,c_4])).

tff(c_74491,plain,(
    ~ r2_hidden('#skF_9','#skF_9') ),
    inference(splitLeft,[status(thm)],[c_74420])).

tff(c_31104,plain,(
    ! [B_4573,A_4574] :
      ( B_4573 = A_4574
      | ~ r1_tarski(B_4573,A_4574)
      | ~ r1_tarski(A_4574,B_4573) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_31117,plain,(
    ! [A_4575] :
      ( A_4575 = '#skF_9'
      | ~ r1_tarski(A_4575,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_31071,c_31104])).

tff(c_31130,plain,(
    ! [A_11] :
      ( k1_tarski(A_11) = '#skF_9'
      | ~ r2_hidden(A_11,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_20,c_31117])).

tff(c_74901,plain,(
    ! [C_10292] :
      ( k1_tarski('#skF_6'('#skF_7'('#skF_9'),k2_relat_1('#skF_7'('#skF_9')),C_10292)) = '#skF_9'
      | ~ r2_hidden(C_10292,k2_relat_1('#skF_7'('#skF_9'))) ) ),
    inference(resolution,[status(thm)],[c_69584,c_31130])).

tff(c_74936,plain,(
    ! [C_10292,B_12] :
      ( r2_hidden('#skF_6'('#skF_7'('#skF_9'),k2_relat_1('#skF_7'('#skF_9')),C_10292),B_12)
      | ~ r1_tarski('#skF_9',B_12)
      | ~ r2_hidden(C_10292,k2_relat_1('#skF_7'('#skF_9'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_74901,c_18])).

tff(c_74993,plain,(
    ! [C_10296,B_10297] :
      ( r2_hidden('#skF_6'('#skF_7'('#skF_9'),k2_relat_1('#skF_7'('#skF_9')),C_10296),B_10297)
      | ~ r2_hidden(C_10296,k2_relat_1('#skF_7'('#skF_9'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_31071,c_74936])).

tff(c_73094,plain,(
    ! [C_4607,A_53] :
      ( C_4607 = '#skF_9'
      | ~ r2_hidden(C_4607,k2_relat_1('#skF_7'(A_53))) ) ),
    inference(resolution,[status(thm)],[c_31334,c_73033])).

tff(c_75032,plain,(
    ! [C_10298] :
      ( '#skF_6'('#skF_7'('#skF_9'),k2_relat_1('#skF_7'('#skF_9')),C_10298) = '#skF_9'
      | ~ r2_hidden(C_10298,k2_relat_1('#skF_7'('#skF_9'))) ) ),
    inference(resolution,[status(thm)],[c_74993,c_73094])).

tff(c_75053,plain,(
    ! [C_10298] :
      ( r2_hidden('#skF_9',k1_relat_1('#skF_7'('#skF_9')))
      | ~ r2_hidden(C_10298,k2_relat_1('#skF_7'('#skF_9')))
      | ~ v1_funct_1('#skF_7'('#skF_9'))
      | ~ v1_relat_1('#skF_7'('#skF_9'))
      | ~ r2_hidden(C_10298,k2_relat_1('#skF_7'('#skF_9'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_75032,c_26])).

tff(c_75065,plain,(
    ! [C_10298] :
      ( r2_hidden('#skF_9','#skF_9')
      | ~ r2_hidden(C_10298,k2_relat_1('#skF_7'('#skF_9'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_75053])).

tff(c_75069,plain,(
    ! [C_10299] : ~ r2_hidden(C_10299,k2_relat_1('#skF_7'('#skF_9'))) ),
    inference(negUnitSimplification,[status(thm)],[c_74491,c_75065])).

tff(c_75130,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_74282,c_75069])).

tff(c_75300,plain,(
    ! [A_10303] :
      ( r1_tarski(k2_relat_1('#skF_7'(A_10303)),'#skF_9')
      | A_10303 != '#skF_9' ) ),
    inference(splitRight,[status(thm)],[c_74420])).

tff(c_75312,plain,(
    ! [A_10303] :
      ( k1_relat_1('#skF_7'(A_10303)) != '#skF_9'
      | ~ v1_funct_1('#skF_7'(A_10303))
      | ~ v1_relat_1('#skF_7'(A_10303))
      | A_10303 != '#skF_9' ) ),
    inference(resolution,[status(thm)],[c_75300,c_31075])).

tff(c_75321,plain,(
    ! [A_10303] : A_10303 != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_75312])).

tff(c_75132,plain,(
    r2_hidden('#skF_9','#skF_9') ),
    inference(splitRight,[status(thm)],[c_74420])).

tff(c_75147,plain,(
    k1_tarski('#skF_9') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_75132,c_31130])).

tff(c_75346,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_75321,c_75147])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.32  % Computer   : n002.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % DateTime   : Tue Dec  1 16:21:22 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 14.02/6.08  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.02/6.10  
% 14.02/6.10  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.02/6.10  %$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_2 > #skF_6 > #skF_3 > #skF_10 > #skF_8 > #skF_9 > #skF_1 > #skF_5 > #skF_4
% 14.02/6.10  
% 14.02/6.10  %Foreground sorts:
% 14.02/6.10  
% 14.02/6.10  
% 14.02/6.10  %Background operators:
% 14.02/6.10  
% 14.02/6.10  
% 14.02/6.10  %Foreground operators:
% 14.02/6.10  tff('#skF_7', type, '#skF_7': $i > $i).
% 14.02/6.10  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 14.02/6.10  tff('#skF_2', type, '#skF_2': $i > $i).
% 14.02/6.10  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 14.02/6.10  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 14.02/6.10  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 14.02/6.10  tff(k1_tarski, type, k1_tarski: $i > $i).
% 14.02/6.10  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 14.02/6.10  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 14.02/6.10  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 14.02/6.10  tff('#skF_10', type, '#skF_10': $i).
% 14.02/6.10  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 14.02/6.10  tff('#skF_8', type, '#skF_8': ($i * $i) > $i).
% 14.02/6.10  tff('#skF_9', type, '#skF_9': $i).
% 14.02/6.10  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 14.02/6.10  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 14.02/6.10  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 14.02/6.10  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 14.02/6.10  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 14.02/6.10  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 14.02/6.10  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 14.02/6.10  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 14.02/6.10  
% 14.28/6.13  tff(f_79, axiom, (![A]: (?[B]: (((v1_relat_1(B) & v1_funct_1(B)) & (k1_relat_1(B) = A)) & (![C]: (r2_hidden(C, A) => (k1_funct_1(B, C) = k1_xboole_0)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', s3_funct_1__e2_25__funct_1)).
% 14.28/6.13  tff(f_110, negated_conjecture, ~(![A, B]: ~(~((A = k1_xboole_0) & ~(B = k1_xboole_0)) & (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => ~((B = k1_relat_1(C)) & r1_tarski(k2_relat_1(C), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_funct_1)).
% 14.28/6.13  tff(f_40, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 14.28/6.13  tff(f_92, axiom, (![A]: (~(A = k1_xboole_0) => (![B]: (?[C]: (((v1_relat_1(C) & v1_funct_1(C)) & (k1_relat_1(C) = A)) & (k2_relat_1(C) = k1_tarski(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t15_funct_1)).
% 14.28/6.13  tff(f_52, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 14.28/6.13  tff(f_67, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_funct_1)).
% 14.28/6.13  tff(f_48, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 14.28/6.13  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 14.28/6.13  tff(f_46, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 14.28/6.13  tff(c_46, plain, (![A_53]: (v1_relat_1('#skF_7'(A_53)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 14.28/6.13  tff(c_44, plain, (![A_53]: (v1_funct_1('#skF_7'(A_53)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 14.28/6.13  tff(c_42, plain, (![A_53]: (k1_relat_1('#skF_7'(A_53))=A_53)), inference(cnfTransformation, [status(thm)], [f_79])).
% 14.28/6.13  tff(c_58, plain, (k1_xboole_0='#skF_10' | k1_xboole_0!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_110])).
% 14.28/6.13  tff(c_73, plain, (k1_xboole_0!='#skF_9'), inference(splitLeft, [status(thm)], [c_58])).
% 14.28/6.13  tff(c_8, plain, (![A_6]: (r2_hidden('#skF_2'(A_6), A_6) | k1_xboole_0=A_6)), inference(cnfTransformation, [status(thm)], [f_40])).
% 14.28/6.13  tff(c_50, plain, (![A_59, B_63]: (k1_relat_1('#skF_8'(A_59, B_63))=A_59 | k1_xboole_0=A_59)), inference(cnfTransformation, [status(thm)], [f_92])).
% 14.28/6.13  tff(c_52, plain, (![A_59, B_63]: (v1_funct_1('#skF_8'(A_59, B_63)) | k1_xboole_0=A_59)), inference(cnfTransformation, [status(thm)], [f_92])).
% 14.28/6.13  tff(c_54, plain, (![A_59, B_63]: (v1_relat_1('#skF_8'(A_59, B_63)) | k1_xboole_0=A_59)), inference(cnfTransformation, [status(thm)], [f_92])).
% 14.28/6.13  tff(c_20, plain, (![A_11, B_12]: (r1_tarski(k1_tarski(A_11), B_12) | ~r2_hidden(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_52])).
% 14.28/6.13  tff(c_111, plain, (![A_89, B_90]: (k2_relat_1('#skF_8'(A_89, B_90))=k1_tarski(B_90) | k1_xboole_0=A_89)), inference(cnfTransformation, [status(thm)], [f_92])).
% 14.28/6.13  tff(c_56, plain, (![C_66]: (~r1_tarski(k2_relat_1(C_66), '#skF_9') | k1_relat_1(C_66)!='#skF_10' | ~v1_funct_1(C_66) | ~v1_relat_1(C_66))), inference(cnfTransformation, [status(thm)], [f_110])).
% 14.28/6.13  tff(c_130, plain, (![B_93, A_94]: (~r1_tarski(k1_tarski(B_93), '#skF_9') | k1_relat_1('#skF_8'(A_94, B_93))!='#skF_10' | ~v1_funct_1('#skF_8'(A_94, B_93)) | ~v1_relat_1('#skF_8'(A_94, B_93)) | k1_xboole_0=A_94)), inference(superposition, [status(thm), theory('equality')], [c_111, c_56])).
% 14.28/6.13  tff(c_240, plain, (![A_110, A_111]: (k1_relat_1('#skF_8'(A_110, A_111))!='#skF_10' | ~v1_funct_1('#skF_8'(A_110, A_111)) | ~v1_relat_1('#skF_8'(A_110, A_111)) | k1_xboole_0=A_110 | ~r2_hidden(A_111, '#skF_9'))), inference(resolution, [status(thm)], [c_20, c_130])).
% 14.28/6.13  tff(c_373, plain, (![A_128, B_129]: (k1_relat_1('#skF_8'(A_128, B_129))!='#skF_10' | ~v1_funct_1('#skF_8'(A_128, B_129)) | ~r2_hidden(B_129, '#skF_9') | k1_xboole_0=A_128)), inference(resolution, [status(thm)], [c_54, c_240])).
% 14.28/6.13  tff(c_426, plain, (![A_133, B_134]: (k1_relat_1('#skF_8'(A_133, B_134))!='#skF_10' | ~r2_hidden(B_134, '#skF_9') | k1_xboole_0=A_133)), inference(resolution, [status(thm)], [c_52, c_373])).
% 14.28/6.13  tff(c_429, plain, (![A_59, B_63]: (A_59!='#skF_10' | ~r2_hidden(B_63, '#skF_9') | k1_xboole_0=A_59 | k1_xboole_0=A_59)), inference(superposition, [status(thm), theory('equality')], [c_50, c_426])).
% 14.28/6.13  tff(c_431, plain, (![B_135]: (~r2_hidden(B_135, '#skF_9'))), inference(splitLeft, [status(thm)], [c_429])).
% 14.28/6.13  tff(c_443, plain, (k1_xboole_0='#skF_9'), inference(resolution, [status(thm)], [c_8, c_431])).
% 14.28/6.13  tff(c_449, plain, $false, inference(negUnitSimplification, [status(thm)], [c_73, c_443])).
% 14.28/6.13  tff(c_478, plain, (k1_xboole_0='#skF_10'), inference(splitRight, [status(thm)], [c_429])).
% 14.28/6.13  tff(c_500, plain, (![A_6]: (r2_hidden('#skF_2'(A_6), A_6) | A_6='#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_478, c_8])).
% 14.28/6.13  tff(c_316, plain, (![A_120, C_121]: (r2_hidden('#skF_6'(A_120, k2_relat_1(A_120), C_121), k1_relat_1(A_120)) | ~r2_hidden(C_121, k2_relat_1(A_120)) | ~v1_funct_1(A_120) | ~v1_relat_1(A_120))), inference(cnfTransformation, [status(thm)], [f_67])).
% 14.28/6.13  tff(c_329, plain, (![A_53, C_121]: (r2_hidden('#skF_6'('#skF_7'(A_53), k2_relat_1('#skF_7'(A_53)), C_121), A_53) | ~r2_hidden(C_121, k2_relat_1('#skF_7'(A_53))) | ~v1_funct_1('#skF_7'(A_53)) | ~v1_relat_1('#skF_7'(A_53)))), inference(superposition, [status(thm), theory('equality')], [c_42, c_316])).
% 14.28/6.13  tff(c_333, plain, (![A_53, C_121]: (r2_hidden('#skF_6'('#skF_7'(A_53), k2_relat_1('#skF_7'(A_53)), C_121), A_53) | ~r2_hidden(C_121, k2_relat_1('#skF_7'(A_53))))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_329])).
% 14.28/6.13  tff(c_1230, plain, (![A_233, C_234]: (r2_hidden('#skF_6'('#skF_7'(A_233), k2_relat_1('#skF_7'(A_233)), C_234), A_233) | ~r2_hidden(C_234, k2_relat_1('#skF_7'(A_233))))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_329])).
% 14.28/6.13  tff(c_40, plain, (![A_53, C_58]: (k1_funct_1('#skF_7'(A_53), C_58)=k1_xboole_0 | ~r2_hidden(C_58, A_53))), inference(cnfTransformation, [status(thm)], [f_79])).
% 14.28/6.13  tff(c_198, plain, (![A_104, D_105]: (r2_hidden(k1_funct_1(A_104, D_105), k2_relat_1(A_104)) | ~r2_hidden(D_105, k1_relat_1(A_104)) | ~v1_funct_1(A_104) | ~v1_relat_1(A_104))), inference(cnfTransformation, [status(thm)], [f_67])).
% 14.28/6.13  tff(c_206, plain, (![A_53, C_58]: (r2_hidden(k1_xboole_0, k2_relat_1('#skF_7'(A_53))) | ~r2_hidden(C_58, k1_relat_1('#skF_7'(A_53))) | ~v1_funct_1('#skF_7'(A_53)) | ~v1_relat_1('#skF_7'(A_53)) | ~r2_hidden(C_58, A_53))), inference(superposition, [status(thm), theory('equality')], [c_40, c_198])).
% 14.28/6.13  tff(c_209, plain, (![A_53, C_58]: (r2_hidden(k1_xboole_0, k2_relat_1('#skF_7'(A_53))) | ~r2_hidden(C_58, A_53))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_206])).
% 14.28/6.13  tff(c_491, plain, (![A_53, C_58]: (r2_hidden('#skF_10', k2_relat_1('#skF_7'(A_53))) | ~r2_hidden(C_58, A_53))), inference(demodulation, [status(thm), theory('equality')], [c_478, c_209])).
% 14.28/6.13  tff(c_1259, plain, (![A_235, C_236]: (r2_hidden('#skF_10', k2_relat_1('#skF_7'(A_235))) | ~r2_hidden(C_236, k2_relat_1('#skF_7'(A_235))))), inference(resolution, [status(thm)], [c_1230, c_491])).
% 14.28/6.13  tff(c_26708, plain, (![A_4173, C_4174]: (r2_hidden('#skF_10', k2_relat_1('#skF_7'(A_4173))) | ~r2_hidden(C_4174, k2_relat_1('#skF_7'(k2_relat_1('#skF_7'(A_4173))))))), inference(resolution, [status(thm)], [c_333, c_1259])).
% 14.28/6.13  tff(c_26950, plain, (![A_4173]: (r2_hidden('#skF_10', k2_relat_1('#skF_7'(A_4173))) | k2_relat_1('#skF_7'(k2_relat_1('#skF_7'(A_4173))))='#skF_10')), inference(resolution, [status(thm)], [c_500, c_26708])).
% 14.28/6.13  tff(c_16, plain, (![A_10]: (r1_tarski(k1_xboole_0, A_10))), inference(cnfTransformation, [status(thm)], [f_48])).
% 14.28/6.13  tff(c_503, plain, (![A_10]: (r1_tarski('#skF_10', A_10))), inference(demodulation, [status(thm), theory('equality')], [c_478, c_16])).
% 14.28/6.13  tff(c_27275, plain, (![A_4256]: (r2_hidden('#skF_10', k2_relat_1('#skF_7'(A_4256))) | k2_relat_1('#skF_7'(k2_relat_1('#skF_7'(A_4256))))='#skF_10')), inference(resolution, [status(thm)], [c_500, c_26708])).
% 14.28/6.13  tff(c_27438, plain, (![A_4256]: (~r1_tarski('#skF_10', '#skF_9') | k1_relat_1('#skF_7'(k2_relat_1('#skF_7'(A_4256))))!='#skF_10' | ~v1_funct_1('#skF_7'(k2_relat_1('#skF_7'(A_4256)))) | ~v1_relat_1('#skF_7'(k2_relat_1('#skF_7'(A_4256)))) | r2_hidden('#skF_10', k2_relat_1('#skF_7'(A_4256))))), inference(superposition, [status(thm), theory('equality')], [c_27275, c_56])).
% 14.28/6.13  tff(c_28152, plain, (![A_4297]: (k2_relat_1('#skF_7'(A_4297))!='#skF_10' | r2_hidden('#skF_10', k2_relat_1('#skF_7'(A_4297))))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_503, c_27438])).
% 14.28/6.13  tff(c_1300, plain, (![A_235, C_121]: (r2_hidden('#skF_10', k2_relat_1('#skF_7'(A_235))) | ~r2_hidden(C_121, k2_relat_1('#skF_7'(k2_relat_1('#skF_7'(A_235))))))), inference(resolution, [status(thm)], [c_333, c_1259])).
% 14.28/6.13  tff(c_29540, plain, (![A_4433]: (r2_hidden('#skF_10', k2_relat_1('#skF_7'(A_4433))) | k2_relat_1('#skF_7'(k2_relat_1('#skF_7'(A_4433))))!='#skF_10')), inference(resolution, [status(thm)], [c_28152, c_1300])).
% 14.28/6.13  tff(c_29661, plain, (![A_4173]: (r2_hidden('#skF_10', k2_relat_1('#skF_7'(A_4173))))), inference(superposition, [status(thm), theory('equality')], [c_26950, c_29540])).
% 14.28/6.13  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 14.28/6.13  tff(c_451, plain, (![A_136, C_137]: (k1_funct_1(A_136, '#skF_6'(A_136, k2_relat_1(A_136), C_137))=C_137 | ~r2_hidden(C_137, k2_relat_1(A_136)) | ~v1_funct_1(A_136) | ~v1_relat_1(A_136))), inference(cnfTransformation, [status(thm)], [f_67])).
% 14.28/6.13  tff(c_471, plain, (![C_137, A_53]: (k1_xboole_0=C_137 | ~r2_hidden(C_137, k2_relat_1('#skF_7'(A_53))) | ~v1_funct_1('#skF_7'(A_53)) | ~v1_relat_1('#skF_7'(A_53)) | ~r2_hidden('#skF_6'('#skF_7'(A_53), k2_relat_1('#skF_7'(A_53)), C_137), A_53))), inference(superposition, [status(thm), theory('equality')], [c_40, c_451])).
% 14.28/6.13  tff(c_477, plain, (![C_137, A_53]: (k1_xboole_0=C_137 | ~r2_hidden(C_137, k2_relat_1('#skF_7'(A_53))) | ~r2_hidden('#skF_6'('#skF_7'(A_53), k2_relat_1('#skF_7'(A_53)), C_137), A_53))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_471])).
% 14.28/6.13  tff(c_1455, plain, (![C_249, A_250]: (C_249='#skF_10' | ~r2_hidden(C_249, k2_relat_1('#skF_7'(A_250))) | ~r2_hidden('#skF_6'('#skF_7'(A_250), k2_relat_1('#skF_7'(A_250)), C_249), A_250))), inference(demodulation, [status(thm), theory('equality')], [c_478, c_477])).
% 14.28/6.13  tff(c_1460, plain, (![C_251, A_252]: (C_251='#skF_10' | ~r2_hidden(C_251, k2_relat_1('#skF_7'(A_252))))), inference(resolution, [status(thm)], [c_333, c_1455])).
% 14.28/6.13  tff(c_1605, plain, (![A_256, B_257]: ('#skF_1'(k2_relat_1('#skF_7'(A_256)), B_257)='#skF_10' | r1_tarski(k2_relat_1('#skF_7'(A_256)), B_257))), inference(resolution, [status(thm)], [c_6, c_1460])).
% 14.28/6.13  tff(c_179, plain, (![C_99, B_100, A_101]: (r2_hidden(C_99, B_100) | ~r2_hidden(C_99, A_101) | ~r1_tarski(A_101, B_100))), inference(cnfTransformation, [status(thm)], [f_32])).
% 14.28/6.13  tff(c_879, plain, (![A_191, B_192, B_193]: (r2_hidden('#skF_1'(A_191, B_192), B_193) | ~r1_tarski(A_191, B_193) | r1_tarski(A_191, B_192))), inference(resolution, [status(thm)], [c_6, c_179])).
% 14.28/6.13  tff(c_135, plain, (![B_95, A_96]: (B_95=A_96 | ~r1_tarski(B_95, A_96) | ~r1_tarski(A_96, B_95))), inference(cnfTransformation, [status(thm)], [f_46])).
% 14.28/6.13  tff(c_148, plain, (![A_97]: (k1_xboole_0=A_97 | ~r1_tarski(A_97, k1_xboole_0))), inference(resolution, [status(thm)], [c_16, c_135])).
% 14.28/6.13  tff(c_161, plain, (![A_11]: (k1_tarski(A_11)=k1_xboole_0 | ~r2_hidden(A_11, k1_xboole_0))), inference(resolution, [status(thm)], [c_20, c_148])).
% 14.28/6.13  tff(c_493, plain, (![A_11]: (k1_tarski(A_11)='#skF_10' | ~r2_hidden(A_11, '#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_478, c_478, c_161])).
% 14.28/6.13  tff(c_946, plain, (![A_203, B_204]: (k1_tarski('#skF_1'(A_203, B_204))='#skF_10' | ~r1_tarski(A_203, '#skF_10') | r1_tarski(A_203, B_204))), inference(resolution, [status(thm)], [c_879, c_493])).
% 14.28/6.13  tff(c_18, plain, (![A_11, B_12]: (r2_hidden(A_11, B_12) | ~r1_tarski(k1_tarski(A_11), B_12))), inference(cnfTransformation, [status(thm)], [f_52])).
% 14.28/6.13  tff(c_973, plain, (![A_203, B_204, B_12]: (r2_hidden('#skF_1'(A_203, B_204), B_12) | ~r1_tarski('#skF_10', B_12) | ~r1_tarski(A_203, '#skF_10') | r1_tarski(A_203, B_204))), inference(superposition, [status(thm), theory('equality')], [c_946, c_18])).
% 14.28/6.13  tff(c_1007, plain, (![A_211, B_212, B_213]: (r2_hidden('#skF_1'(A_211, B_212), B_213) | ~r1_tarski(A_211, '#skF_10') | r1_tarski(A_211, B_212))), inference(demodulation, [status(thm), theory('equality')], [c_503, c_973])).
% 14.28/6.13  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 14.28/6.13  tff(c_1023, plain, (![A_211, B_213]: (~r1_tarski(A_211, '#skF_10') | r1_tarski(A_211, B_213))), inference(resolution, [status(thm)], [c_1007, c_4])).
% 14.28/6.13  tff(c_1865, plain, (![A_266, B_267]: (r1_tarski(k2_relat_1('#skF_7'(A_266)), B_267) | '#skF_1'(k2_relat_1('#skF_7'(A_266)), '#skF_10')='#skF_10')), inference(resolution, [status(thm)], [c_1605, c_1023])).
% 14.28/6.13  tff(c_14, plain, (![B_9]: (r1_tarski(B_9, B_9))), inference(cnfTransformation, [status(thm)], [f_46])).
% 14.28/6.13  tff(c_88, plain, (![A_80, B_81]: (r2_hidden(A_80, B_81) | ~r1_tarski(k1_tarski(A_80), B_81))), inference(cnfTransformation, [status(thm)], [f_52])).
% 14.28/6.13  tff(c_93, plain, (![A_80]: (r2_hidden(A_80, k1_tarski(A_80)))), inference(resolution, [status(thm)], [c_14, c_88])).
% 14.28/6.13  tff(c_210, plain, (![A_106, C_107]: (r2_hidden(k1_xboole_0, k2_relat_1('#skF_7'(A_106))) | ~r2_hidden(C_107, A_106))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_206])).
% 14.28/6.13  tff(c_226, plain, (![A_108]: (r2_hidden(k1_xboole_0, k2_relat_1('#skF_7'(k1_tarski(A_108)))))), inference(resolution, [status(thm)], [c_93, c_210])).
% 14.28/6.13  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 14.28/6.13  tff(c_232, plain, (![B_2, A_108]: (r2_hidden(k1_xboole_0, B_2) | ~r1_tarski(k2_relat_1('#skF_7'(k1_tarski(A_108))), B_2))), inference(resolution, [status(thm)], [c_226, c_2])).
% 14.28/6.13  tff(c_486, plain, (![B_2, A_108]: (r2_hidden('#skF_10', B_2) | ~r1_tarski(k2_relat_1('#skF_7'(k1_tarski(A_108))), B_2))), inference(demodulation, [status(thm), theory('equality')], [c_478, c_232])).
% 14.28/6.13  tff(c_1922, plain, (![B_267, A_108]: (r2_hidden('#skF_10', B_267) | '#skF_1'(k2_relat_1('#skF_7'(k1_tarski(A_108))), '#skF_10')='#skF_10')), inference(resolution, [status(thm)], [c_1865, c_486])).
% 14.28/6.13  tff(c_1976, plain, (![A_269]: ('#skF_1'(k2_relat_1('#skF_7'(k1_tarski(A_269))), '#skF_10')='#skF_10')), inference(splitLeft, [status(thm)], [c_1922])).
% 14.28/6.13  tff(c_1996, plain, (![A_269]: (~r2_hidden('#skF_10', '#skF_10') | r1_tarski(k2_relat_1('#skF_7'(k1_tarski(A_269))), '#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_1976, c_4])).
% 14.28/6.13  tff(c_2026, plain, (~r2_hidden('#skF_10', '#skF_10')), inference(splitLeft, [status(thm)], [c_1996])).
% 14.28/6.13  tff(c_1459, plain, (![C_121, A_53]: (C_121='#skF_10' | ~r2_hidden(C_121, k2_relat_1('#skF_7'(A_53))))), inference(resolution, [status(thm)], [c_333, c_1455])).
% 14.28/6.13  tff(c_27368, plain, (![C_121, A_4256]: (C_121='#skF_10' | ~r2_hidden(C_121, '#skF_10') | r2_hidden('#skF_10', k2_relat_1('#skF_7'(A_4256))))), inference(superposition, [status(thm), theory('equality')], [c_27275, c_1459])).
% 14.28/6.13  tff(c_28476, plain, (![A_4256]: (r2_hidden('#skF_10', k2_relat_1('#skF_7'(A_4256))))), inference(splitLeft, [status(thm)], [c_27368])).
% 14.28/6.13  tff(c_29216, plain, (![C_4384]: (k1_tarski('#skF_6'('#skF_7'('#skF_10'), k2_relat_1('#skF_7'('#skF_10')), C_4384))='#skF_10' | ~r2_hidden(C_4384, k2_relat_1('#skF_7'('#skF_10'))))), inference(resolution, [status(thm)], [c_1230, c_493])).
% 14.28/6.13  tff(c_29260, plain, (![C_4384, B_12]: (r2_hidden('#skF_6'('#skF_7'('#skF_10'), k2_relat_1('#skF_7'('#skF_10')), C_4384), B_12) | ~r1_tarski('#skF_10', B_12) | ~r2_hidden(C_4384, k2_relat_1('#skF_7'('#skF_10'))))), inference(superposition, [status(thm), theory('equality')], [c_29216, c_18])).
% 14.28/6.13  tff(c_29286, plain, (![C_4388, B_4389]: (r2_hidden('#skF_6'('#skF_7'('#skF_10'), k2_relat_1('#skF_7'('#skF_10')), C_4388), B_4389) | ~r2_hidden(C_4388, k2_relat_1('#skF_7'('#skF_10'))))), inference(demodulation, [status(thm), theory('equality')], [c_503, c_29260])).
% 14.28/6.13  tff(c_29323, plain, (![C_4390]: ('#skF_6'('#skF_7'('#skF_10'), k2_relat_1('#skF_7'('#skF_10')), C_4390)='#skF_10' | ~r2_hidden(C_4390, k2_relat_1('#skF_7'('#skF_10'))))), inference(resolution, [status(thm)], [c_29286, c_1459])).
% 14.28/6.13  tff(c_26, plain, (![A_13, C_49]: (r2_hidden('#skF_6'(A_13, k2_relat_1(A_13), C_49), k1_relat_1(A_13)) | ~r2_hidden(C_49, k2_relat_1(A_13)) | ~v1_funct_1(A_13) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_67])).
% 14.28/6.13  tff(c_29344, plain, (![C_4390]: (r2_hidden('#skF_10', k1_relat_1('#skF_7'('#skF_10'))) | ~r2_hidden(C_4390, k2_relat_1('#skF_7'('#skF_10'))) | ~v1_funct_1('#skF_7'('#skF_10')) | ~v1_relat_1('#skF_7'('#skF_10')) | ~r2_hidden(C_4390, k2_relat_1('#skF_7'('#skF_10'))))), inference(superposition, [status(thm), theory('equality')], [c_29323, c_26])).
% 14.28/6.13  tff(c_29356, plain, (![C_4390]: (r2_hidden('#skF_10', '#skF_10') | ~r2_hidden(C_4390, k2_relat_1('#skF_7'('#skF_10'))))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_29344])).
% 14.28/6.13  tff(c_29359, plain, (![C_4391]: (~r2_hidden(C_4391, k2_relat_1('#skF_7'('#skF_10'))))), inference(negUnitSimplification, [status(thm)], [c_2026, c_29356])).
% 14.28/6.13  tff(c_29454, plain, $false, inference(resolution, [status(thm)], [c_28476, c_29359])).
% 14.28/6.13  tff(c_29456, plain, (![C_4392]: (C_4392='#skF_10' | ~r2_hidden(C_4392, '#skF_10'))), inference(splitRight, [status(thm)], [c_27368])).
% 14.28/6.13  tff(c_30662, plain, (![C_4551]: ('#skF_6'('#skF_7'('#skF_10'), k2_relat_1('#skF_7'('#skF_10')), C_4551)='#skF_10' | ~r2_hidden(C_4551, k2_relat_1('#skF_7'('#skF_10'))))), inference(resolution, [status(thm)], [c_333, c_29456])).
% 14.28/6.13  tff(c_30677, plain, (![C_4551]: (r2_hidden('#skF_10', k1_relat_1('#skF_7'('#skF_10'))) | ~r2_hidden(C_4551, k2_relat_1('#skF_7'('#skF_10'))) | ~v1_funct_1('#skF_7'('#skF_10')) | ~v1_relat_1('#skF_7'('#skF_10')) | ~r2_hidden(C_4551, k2_relat_1('#skF_7'('#skF_10'))))), inference(superposition, [status(thm), theory('equality')], [c_30662, c_26])).
% 14.28/6.13  tff(c_30688, plain, (![C_4551]: (r2_hidden('#skF_10', '#skF_10') | ~r2_hidden(C_4551, k2_relat_1('#skF_7'('#skF_10'))))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_30677])).
% 14.28/6.13  tff(c_30691, plain, (![C_4552]: (~r2_hidden(C_4552, k2_relat_1('#skF_7'('#skF_10'))))), inference(negUnitSimplification, [status(thm)], [c_2026, c_30688])).
% 14.28/6.13  tff(c_30772, plain, $false, inference(resolution, [status(thm)], [c_29661, c_30691])).
% 14.28/6.13  tff(c_30774, plain, (r2_hidden('#skF_10', '#skF_10')), inference(splitRight, [status(thm)], [c_1996])).
% 14.28/6.13  tff(c_1024, plain, (![A_214, B_215]: (~r1_tarski(A_214, '#skF_10') | r1_tarski(A_214, B_215))), inference(resolution, [status(thm)], [c_1007, c_4])).
% 14.28/6.13  tff(c_1050, plain, (![A_219, B_220]: (r1_tarski(k1_tarski(A_219), B_220) | ~r2_hidden(A_219, '#skF_10'))), inference(resolution, [status(thm)], [c_20, c_1024])).
% 14.28/6.13  tff(c_1084, plain, (![A_219, B_220]: (r2_hidden(A_219, B_220) | ~r2_hidden(A_219, '#skF_10'))), inference(resolution, [status(thm)], [c_1050, c_18])).
% 14.28/6.13  tff(c_30790, plain, (![B_220]: (r2_hidden('#skF_10', B_220))), inference(resolution, [status(thm)], [c_30774, c_1084])).
% 14.28/6.13  tff(c_1651, plain, (![A_256]: (k1_relat_1('#skF_7'(A_256))!='#skF_10' | ~v1_funct_1('#skF_7'(A_256)) | ~v1_relat_1('#skF_7'(A_256)) | '#skF_1'(k2_relat_1('#skF_7'(A_256)), '#skF_9')='#skF_10')), inference(resolution, [status(thm)], [c_1605, c_56])).
% 14.28/6.13  tff(c_1670, plain, (![A_258]: (A_258!='#skF_10' | '#skF_1'(k2_relat_1('#skF_7'(A_258)), '#skF_9')='#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_1651])).
% 14.28/6.13  tff(c_1679, plain, (![A_258]: (~r2_hidden('#skF_10', '#skF_9') | r1_tarski(k2_relat_1('#skF_7'(A_258)), '#skF_9') | A_258!='#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_1670, c_4])).
% 14.28/6.13  tff(c_1745, plain, (~r2_hidden('#skF_10', '#skF_9')), inference(splitLeft, [status(thm)], [c_1679])).
% 14.28/6.14  tff(c_30821, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30790, c_1745])).
% 14.28/6.14  tff(c_30982, plain, (![A_4558]: (r1_tarski(k2_relat_1('#skF_7'(A_4558)), '#skF_9') | A_4558!='#skF_10')), inference(splitRight, [status(thm)], [c_1679])).
% 14.28/6.14  tff(c_31008, plain, (![A_4558]: (k1_relat_1('#skF_7'(A_4558))!='#skF_10' | ~v1_funct_1('#skF_7'(A_4558)) | ~v1_relat_1('#skF_7'(A_4558)) | A_4558!='#skF_10')), inference(resolution, [status(thm)], [c_30982, c_56])).
% 14.28/6.14  tff(c_31027, plain, (![A_4558]: (A_4558!='#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_31008])).
% 14.28/6.14  tff(c_147, plain, (![A_10]: (k1_xboole_0=A_10 | ~r1_tarski(A_10, k1_xboole_0))), inference(resolution, [status(thm)], [c_16, c_135])).
% 14.28/6.14  tff(c_494, plain, (![A_10]: (A_10='#skF_10' | ~r1_tarski(A_10, '#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_478, c_478, c_147])).
% 14.28/6.14  tff(c_1663, plain, (![A_256]: (k2_relat_1('#skF_7'(A_256))='#skF_10' | '#skF_1'(k2_relat_1('#skF_7'(A_256)), '#skF_10')='#skF_10')), inference(resolution, [status(thm)], [c_1605, c_494])).
% 14.28/6.14  tff(c_31054, plain, $false, inference(negUnitSimplification, [status(thm)], [c_31027, c_31027, c_1663])).
% 14.28/6.14  tff(c_31056, plain, (k1_xboole_0='#skF_9'), inference(splitRight, [status(thm)], [c_58])).
% 14.28/6.14  tff(c_31077, plain, (![A_6]: (r2_hidden('#skF_2'(A_6), A_6) | A_6='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_31056, c_8])).
% 14.28/6.14  tff(c_31317, plain, (![A_4606, C_4607]: (r2_hidden('#skF_6'(A_4606, k2_relat_1(A_4606), C_4607), k1_relat_1(A_4606)) | ~r2_hidden(C_4607, k2_relat_1(A_4606)) | ~v1_funct_1(A_4606) | ~v1_relat_1(A_4606))), inference(cnfTransformation, [status(thm)], [f_67])).
% 14.28/6.14  tff(c_31330, plain, (![A_53, C_4607]: (r2_hidden('#skF_6'('#skF_7'(A_53), k2_relat_1('#skF_7'(A_53)), C_4607), A_53) | ~r2_hidden(C_4607, k2_relat_1('#skF_7'(A_53))) | ~v1_funct_1('#skF_7'(A_53)) | ~v1_relat_1('#skF_7'(A_53)))), inference(superposition, [status(thm), theory('equality')], [c_42, c_31317])).
% 14.28/6.14  tff(c_69584, plain, (![A_9721, C_9722]: (r2_hidden('#skF_6'('#skF_7'(A_9721), k2_relat_1('#skF_7'(A_9721)), C_9722), A_9721) | ~r2_hidden(C_9722, k2_relat_1('#skF_7'(A_9721))))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_31330])).
% 14.28/6.14  tff(c_31156, plain, (![A_53, C_58]: (k1_funct_1('#skF_7'(A_53), C_58)='#skF_9' | ~r2_hidden(C_58, A_53))), inference(demodulation, [status(thm), theory('equality')], [c_31056, c_40])).
% 14.28/6.14  tff(c_31199, plain, (![A_4590, D_4591]: (r2_hidden(k1_funct_1(A_4590, D_4591), k2_relat_1(A_4590)) | ~r2_hidden(D_4591, k1_relat_1(A_4590)) | ~v1_funct_1(A_4590) | ~v1_relat_1(A_4590))), inference(cnfTransformation, [status(thm)], [f_67])).
% 14.28/6.14  tff(c_31207, plain, (![A_53, C_58]: (r2_hidden('#skF_9', k2_relat_1('#skF_7'(A_53))) | ~r2_hidden(C_58, k1_relat_1('#skF_7'(A_53))) | ~v1_funct_1('#skF_7'(A_53)) | ~v1_relat_1('#skF_7'(A_53)) | ~r2_hidden(C_58, A_53))), inference(superposition, [status(thm), theory('equality')], [c_31156, c_31199])).
% 14.28/6.14  tff(c_31210, plain, (![A_53, C_58]: (r2_hidden('#skF_9', k2_relat_1('#skF_7'(A_53))) | ~r2_hidden(C_58, A_53))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_31207])).
% 14.28/6.14  tff(c_70160, plain, (![A_9763, C_9764]: (r2_hidden('#skF_9', k2_relat_1('#skF_7'(A_9763))) | ~r2_hidden(C_9764, k2_relat_1('#skF_7'(A_9763))))), inference(resolution, [status(thm)], [c_69584, c_31210])).
% 14.28/6.14  tff(c_70361, plain, (![A_9763]: (r2_hidden('#skF_9', k2_relat_1('#skF_7'(A_9763))) | k2_relat_1('#skF_7'(A_9763))='#skF_9')), inference(resolution, [status(thm)], [c_31077, c_70160])).
% 14.28/6.14  tff(c_31334, plain, (![A_53, C_4607]: (r2_hidden('#skF_6'('#skF_7'(A_53), k2_relat_1('#skF_7'(A_53)), C_4607), A_53) | ~r2_hidden(C_4607, k2_relat_1('#skF_7'(A_53))))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_31330])).
% 14.28/6.14  tff(c_71597, plain, (![A_9930, C_9931]: (r2_hidden('#skF_9', k2_relat_1('#skF_7'(A_9930))) | ~r2_hidden(C_9931, k2_relat_1('#skF_7'(k2_relat_1('#skF_7'(A_9930))))))), inference(resolution, [status(thm)], [c_31334, c_70160])).
% 14.28/6.14  tff(c_71813, plain, (![A_9930]: (r2_hidden('#skF_9', k2_relat_1('#skF_7'(A_9930))) | k2_relat_1('#skF_7'(k2_relat_1('#skF_7'(A_9930))))='#skF_9')), inference(resolution, [status(thm)], [c_70361, c_71597])).
% 14.28/6.14  tff(c_31055, plain, (k1_xboole_0='#skF_10'), inference(splitRight, [status(thm)], [c_58])).
% 14.28/6.14  tff(c_31062, plain, ('#skF_10'='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_31056, c_31055])).
% 14.28/6.14  tff(c_31057, plain, (![A_10]: (r1_tarski('#skF_10', A_10))), inference(demodulation, [status(thm), theory('equality')], [c_31055, c_16])).
% 14.28/6.14  tff(c_31071, plain, (![A_10]: (r1_tarski('#skF_9', A_10))), inference(demodulation, [status(thm), theory('equality')], [c_31062, c_31057])).
% 14.28/6.14  tff(c_72161, plain, (![A_10013]: (r2_hidden('#skF_9', k2_relat_1('#skF_7'(A_10013))) | k2_relat_1('#skF_7'(k2_relat_1('#skF_7'(A_10013))))='#skF_9')), inference(resolution, [status(thm)], [c_70361, c_71597])).
% 14.28/6.14  tff(c_31075, plain, (![C_66]: (~r1_tarski(k2_relat_1(C_66), '#skF_9') | k1_relat_1(C_66)!='#skF_9' | ~v1_funct_1(C_66) | ~v1_relat_1(C_66))), inference(demodulation, [status(thm), theory('equality')], [c_31062, c_56])).
% 14.28/6.14  tff(c_72336, plain, (![A_10013]: (~r1_tarski('#skF_9', '#skF_9') | k1_relat_1('#skF_7'(k2_relat_1('#skF_7'(A_10013))))!='#skF_9' | ~v1_funct_1('#skF_7'(k2_relat_1('#skF_7'(A_10013)))) | ~v1_relat_1('#skF_7'(k2_relat_1('#skF_7'(A_10013)))) | r2_hidden('#skF_9', k2_relat_1('#skF_7'(A_10013))))), inference(superposition, [status(thm), theory('equality')], [c_72161, c_31075])).
% 14.28/6.14  tff(c_73837, plain, (![A_10179]: (k2_relat_1('#skF_7'(A_10179))!='#skF_9' | r2_hidden('#skF_9', k2_relat_1('#skF_7'(A_10179))))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_31071, c_72336])).
% 14.28/6.14  tff(c_70328, plain, (![A_9763, C_4607]: (r2_hidden('#skF_9', k2_relat_1('#skF_7'(A_9763))) | ~r2_hidden(C_4607, k2_relat_1('#skF_7'(k2_relat_1('#skF_7'(A_9763))))))), inference(resolution, [status(thm)], [c_31334, c_70160])).
% 14.28/6.14  tff(c_74161, plain, (![A_10220]: (r2_hidden('#skF_9', k2_relat_1('#skF_7'(A_10220))) | k2_relat_1('#skF_7'(k2_relat_1('#skF_7'(A_10220))))!='#skF_9')), inference(resolution, [status(thm)], [c_73837, c_70328])).
% 14.28/6.14  tff(c_74282, plain, (![A_9930]: (r2_hidden('#skF_9', k2_relat_1('#skF_7'(A_9930))))), inference(superposition, [status(thm), theory('equality')], [c_71813, c_74161])).
% 14.28/6.14  tff(c_31474, plain, (![A_4628, C_4629]: (k1_funct_1(A_4628, '#skF_6'(A_4628, k2_relat_1(A_4628), C_4629))=C_4629 | ~r2_hidden(C_4629, k2_relat_1(A_4628)) | ~v1_funct_1(A_4628) | ~v1_relat_1(A_4628))), inference(cnfTransformation, [status(thm)], [f_67])).
% 14.28/6.14  tff(c_31484, plain, (![C_4629, A_53]: (C_4629='#skF_9' | ~r2_hidden('#skF_6'('#skF_7'(A_53), k2_relat_1('#skF_7'(A_53)), C_4629), A_53) | ~r2_hidden(C_4629, k2_relat_1('#skF_7'(A_53))) | ~v1_funct_1('#skF_7'(A_53)) | ~v1_relat_1('#skF_7'(A_53)))), inference(superposition, [status(thm), theory('equality')], [c_31474, c_31156])).
% 14.28/6.14  tff(c_73033, plain, (![C_10054, A_10055]: (C_10054='#skF_9' | ~r2_hidden('#skF_6'('#skF_7'(A_10055), k2_relat_1('#skF_7'(A_10055)), C_10054), A_10055) | ~r2_hidden(C_10054, k2_relat_1('#skF_7'(A_10055))))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_31484])).
% 14.28/6.14  tff(c_73095, plain, (![C_10096, A_10097]: (C_10096='#skF_9' | ~r2_hidden(C_10096, k2_relat_1('#skF_7'(A_10097))))), inference(resolution, [status(thm)], [c_31334, c_73033])).
% 14.28/6.14  tff(c_74357, plain, (![A_10266, B_10267]: ('#skF_1'(k2_relat_1('#skF_7'(A_10266)), B_10267)='#skF_9' | r1_tarski(k2_relat_1('#skF_7'(A_10266)), B_10267))), inference(resolution, [status(thm)], [c_6, c_73095])).
% 14.28/6.14  tff(c_74393, plain, (![A_10266]: (k1_relat_1('#skF_7'(A_10266))!='#skF_9' | ~v1_funct_1('#skF_7'(A_10266)) | ~v1_relat_1('#skF_7'(A_10266)) | '#skF_1'(k2_relat_1('#skF_7'(A_10266)), '#skF_9')='#skF_9')), inference(resolution, [status(thm)], [c_74357, c_31075])).
% 14.28/6.14  tff(c_74408, plain, (![A_10268]: (A_10268!='#skF_9' | '#skF_1'(k2_relat_1('#skF_7'(A_10268)), '#skF_9')='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_74393])).
% 14.28/6.14  tff(c_74420, plain, (![A_10268]: (~r2_hidden('#skF_9', '#skF_9') | r1_tarski(k2_relat_1('#skF_7'(A_10268)), '#skF_9') | A_10268!='#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_74408, c_4])).
% 14.28/6.14  tff(c_74491, plain, (~r2_hidden('#skF_9', '#skF_9')), inference(splitLeft, [status(thm)], [c_74420])).
% 14.28/6.14  tff(c_31104, plain, (![B_4573, A_4574]: (B_4573=A_4574 | ~r1_tarski(B_4573, A_4574) | ~r1_tarski(A_4574, B_4573))), inference(cnfTransformation, [status(thm)], [f_46])).
% 14.28/6.14  tff(c_31117, plain, (![A_4575]: (A_4575='#skF_9' | ~r1_tarski(A_4575, '#skF_9'))), inference(resolution, [status(thm)], [c_31071, c_31104])).
% 14.28/6.14  tff(c_31130, plain, (![A_11]: (k1_tarski(A_11)='#skF_9' | ~r2_hidden(A_11, '#skF_9'))), inference(resolution, [status(thm)], [c_20, c_31117])).
% 14.28/6.14  tff(c_74901, plain, (![C_10292]: (k1_tarski('#skF_6'('#skF_7'('#skF_9'), k2_relat_1('#skF_7'('#skF_9')), C_10292))='#skF_9' | ~r2_hidden(C_10292, k2_relat_1('#skF_7'('#skF_9'))))), inference(resolution, [status(thm)], [c_69584, c_31130])).
% 14.28/6.14  tff(c_74936, plain, (![C_10292, B_12]: (r2_hidden('#skF_6'('#skF_7'('#skF_9'), k2_relat_1('#skF_7'('#skF_9')), C_10292), B_12) | ~r1_tarski('#skF_9', B_12) | ~r2_hidden(C_10292, k2_relat_1('#skF_7'('#skF_9'))))), inference(superposition, [status(thm), theory('equality')], [c_74901, c_18])).
% 14.28/6.14  tff(c_74993, plain, (![C_10296, B_10297]: (r2_hidden('#skF_6'('#skF_7'('#skF_9'), k2_relat_1('#skF_7'('#skF_9')), C_10296), B_10297) | ~r2_hidden(C_10296, k2_relat_1('#skF_7'('#skF_9'))))), inference(demodulation, [status(thm), theory('equality')], [c_31071, c_74936])).
% 14.28/6.14  tff(c_73094, plain, (![C_4607, A_53]: (C_4607='#skF_9' | ~r2_hidden(C_4607, k2_relat_1('#skF_7'(A_53))))), inference(resolution, [status(thm)], [c_31334, c_73033])).
% 14.28/6.14  tff(c_75032, plain, (![C_10298]: ('#skF_6'('#skF_7'('#skF_9'), k2_relat_1('#skF_7'('#skF_9')), C_10298)='#skF_9' | ~r2_hidden(C_10298, k2_relat_1('#skF_7'('#skF_9'))))), inference(resolution, [status(thm)], [c_74993, c_73094])).
% 14.28/6.14  tff(c_75053, plain, (![C_10298]: (r2_hidden('#skF_9', k1_relat_1('#skF_7'('#skF_9'))) | ~r2_hidden(C_10298, k2_relat_1('#skF_7'('#skF_9'))) | ~v1_funct_1('#skF_7'('#skF_9')) | ~v1_relat_1('#skF_7'('#skF_9')) | ~r2_hidden(C_10298, k2_relat_1('#skF_7'('#skF_9'))))), inference(superposition, [status(thm), theory('equality')], [c_75032, c_26])).
% 14.28/6.14  tff(c_75065, plain, (![C_10298]: (r2_hidden('#skF_9', '#skF_9') | ~r2_hidden(C_10298, k2_relat_1('#skF_7'('#skF_9'))))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_75053])).
% 14.28/6.14  tff(c_75069, plain, (![C_10299]: (~r2_hidden(C_10299, k2_relat_1('#skF_7'('#skF_9'))))), inference(negUnitSimplification, [status(thm)], [c_74491, c_75065])).
% 14.28/6.14  tff(c_75130, plain, $false, inference(resolution, [status(thm)], [c_74282, c_75069])).
% 14.28/6.14  tff(c_75300, plain, (![A_10303]: (r1_tarski(k2_relat_1('#skF_7'(A_10303)), '#skF_9') | A_10303!='#skF_9')), inference(splitRight, [status(thm)], [c_74420])).
% 14.28/6.14  tff(c_75312, plain, (![A_10303]: (k1_relat_1('#skF_7'(A_10303))!='#skF_9' | ~v1_funct_1('#skF_7'(A_10303)) | ~v1_relat_1('#skF_7'(A_10303)) | A_10303!='#skF_9')), inference(resolution, [status(thm)], [c_75300, c_31075])).
% 14.28/6.14  tff(c_75321, plain, (![A_10303]: (A_10303!='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_75312])).
% 14.28/6.14  tff(c_75132, plain, (r2_hidden('#skF_9', '#skF_9')), inference(splitRight, [status(thm)], [c_74420])).
% 14.28/6.14  tff(c_75147, plain, (k1_tarski('#skF_9')='#skF_9'), inference(resolution, [status(thm)], [c_75132, c_31130])).
% 14.28/6.14  tff(c_75346, plain, $false, inference(negUnitSimplification, [status(thm)], [c_75321, c_75147])).
% 14.28/6.14  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.28/6.14  
% 14.28/6.14  Inference rules
% 14.28/6.14  ----------------------
% 14.28/6.14  #Ref     : 3
% 14.28/6.14  #Sup     : 11936
% 14.28/6.14  #Fact    : 4
% 14.28/6.14  #Define  : 0
% 14.28/6.14  #Split   : 23
% 14.28/6.14  #Chain   : 0
% 14.28/6.14  #Close   : 0
% 14.28/6.14  
% 14.28/6.14  Ordering : KBO
% 14.28/6.14  
% 14.28/6.14  Simplification rules
% 14.28/6.14  ----------------------
% 14.28/6.14  #Subsume      : 3223
% 14.28/6.14  #Demod        : 2991
% 14.28/6.14  #Tautology    : 2308
% 14.28/6.14  #SimpNegUnit  : 154
% 14.28/6.14  #BackRed      : 92
% 14.28/6.14  
% 14.28/6.14  #Partial instantiations: 7140
% 14.28/6.14  #Strategies tried      : 1
% 14.28/6.14  
% 14.28/6.14  Timing (in seconds)
% 14.28/6.14  ----------------------
% 14.28/6.14  Preprocessing        : 0.34
% 14.28/6.14  Parsing              : 0.17
% 14.28/6.14  CNF conversion       : 0.03
% 14.28/6.14  Main loop            : 4.99
% 14.28/6.14  Inferencing          : 1.23
% 14.28/6.14  Reduction            : 1.48
% 14.28/6.14  Demodulation         : 1.15
% 14.28/6.14  BG Simplification    : 0.21
% 14.28/6.14  Subsumption          : 1.72
% 14.28/6.14  Abstraction          : 0.20
% 14.28/6.14  MUC search           : 0.00
% 14.28/6.14  Cooper               : 0.00
% 14.28/6.14  Total                : 5.39
% 14.28/6.14  Index Insertion      : 0.00
% 14.28/6.14  Index Deletion       : 0.00
% 14.28/6.14  Index Matching       : 0.00
% 14.28/6.14  BG Taut test         : 0.00
%------------------------------------------------------------------------------
