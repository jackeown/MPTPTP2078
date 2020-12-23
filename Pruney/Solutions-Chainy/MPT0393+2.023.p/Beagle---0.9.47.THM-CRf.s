%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:20 EST 2020

% Result     : Theorem 17.69s
% Output     : CNFRefutation 17.78s
% Verified   : 
% Statistics : Number of formulae       :  114 (1996 expanded)
%              Number of leaves         :   27 ( 666 expanded)
%              Depth                    :   31
%              Number of atoms          :  201 (4680 expanded)
%              Number of equality atoms :   73 (1197 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_6 > #skF_4 > #skF_7 > #skF_3 > #skF_5 > #skF_2 > #skF_1

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_89,negated_conjecture,(
    ~ ! [A] : k1_setfam_1(k1_tarski(A)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_setfam_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k4_xboole_0(B,k1_tarski(C)))
    <=> ( r2_hidden(A,B)
        & A != C ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_66,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_86,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
         => r1_tarski(B,C) )
     => ( A = k1_xboole_0
        | r1_tarski(B,k1_setfam_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_setfam_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(k1_setfam_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_setfam_1)).

tff(c_68,plain,(
    k1_setfam_1(k1_tarski('#skF_7')) != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_16,plain,(
    ! [C_12] : r2_hidden(C_12,k1_tarski(C_12)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_173,plain,(
    ! [A_63,B_64,C_65] :
      ( r2_hidden(A_63,B_64)
      | ~ r2_hidden(A_63,k4_xboole_0(B_64,k1_tarski(C_65))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_7330,plain,(
    ! [B_11236,C_11237,B_11238] :
      ( r2_hidden('#skF_1'(k4_xboole_0(B_11236,k1_tarski(C_11237)),B_11238),B_11236)
      | r1_tarski(k4_xboole_0(B_11236,k1_tarski(C_11237)),B_11238) ) ),
    inference(resolution,[status(thm)],[c_6,c_173])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_7424,plain,(
    ! [B_11320,C_11321] : r1_tarski(k4_xboole_0(B_11320,k1_tarski(C_11321)),B_11320) ),
    inference(resolution,[status(thm)],[c_7330,c_4])).

tff(c_12,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_54,plain,(
    ! [B_26] : r1_tarski(k1_xboole_0,k1_tarski(B_26)) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_179,plain,(
    ! [C_66,B_67,A_68] :
      ( r2_hidden(C_66,B_67)
      | ~ r2_hidden(C_66,A_68)
      | ~ r1_tarski(A_68,B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_436,plain,(
    ! [A_103,B_104,B_105] :
      ( r2_hidden('#skF_1'(A_103,B_104),B_105)
      | ~ r1_tarski(A_103,B_105)
      | r1_tarski(A_103,B_104) ) ),
    inference(resolution,[status(thm)],[c_6,c_179])).

tff(c_14,plain,(
    ! [C_12,A_8] :
      ( C_12 = A_8
      | ~ r2_hidden(C_12,k1_tarski(A_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_559,plain,(
    ! [A_114,A_115,B_116] :
      ( A_114 = '#skF_1'(A_115,B_116)
      | ~ r1_tarski(A_115,k1_tarski(A_114))
      | r1_tarski(A_115,B_116) ) ),
    inference(resolution,[status(thm)],[c_436,c_14])).

tff(c_577,plain,(
    ! [B_117,B_118] :
      ( B_117 = '#skF_1'(k1_xboole_0,B_118)
      | r1_tarski(k1_xboole_0,B_118) ) ),
    inference(resolution,[status(thm)],[c_54,c_559])).

tff(c_125,plain,(
    ! [A_56,B_57] :
      ( r2_hidden('#skF_1'(A_56,B_57),A_56)
      | r1_tarski(A_56,B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_228,plain,(
    ! [A_80,B_81] :
      ( '#skF_1'(k1_tarski(A_80),B_81) = A_80
      | r1_tarski(k1_tarski(A_80),B_81) ) ),
    inference(resolution,[status(thm)],[c_125,c_14])).

tff(c_111,plain,(
    ! [B_53,A_54] :
      ( B_53 = A_54
      | ~ r1_tarski(B_53,A_54)
      | ~ r1_tarski(A_54,B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_119,plain,(
    ! [B_26] :
      ( k1_tarski(B_26) = k1_xboole_0
      | ~ r1_tarski(k1_tarski(B_26),k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_54,c_111])).

tff(c_264,plain,(
    ! [A_86] :
      ( k1_tarski(A_86) = k1_xboole_0
      | '#skF_1'(k1_tarski(A_86),k1_xboole_0) = A_86 ) ),
    inference(resolution,[status(thm)],[c_228,c_119])).

tff(c_306,plain,(
    ! [A_89] :
      ( ~ r2_hidden(A_89,k1_xboole_0)
      | r1_tarski(k1_tarski(A_89),k1_xboole_0)
      | k1_tarski(A_89) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_264,c_4])).

tff(c_339,plain,(
    ! [A_92] :
      ( ~ r2_hidden(A_92,k1_xboole_0)
      | k1_tarski(A_92) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_306,c_119])).

tff(c_351,plain,(
    ! [B_93] :
      ( k1_tarski('#skF_1'(k1_xboole_0,B_93)) = k1_xboole_0
      | r1_tarski(k1_xboole_0,B_93) ) ),
    inference(resolution,[status(thm)],[c_6,c_339])).

tff(c_58,plain,(
    ! [C_29,B_28] : ~ r2_hidden(C_29,k4_xboole_0(B_28,k1_tarski(C_29))) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_380,plain,(
    ! [B_93,B_28] :
      ( ~ r2_hidden('#skF_1'(k1_xboole_0,B_93),k4_xboole_0(B_28,k1_xboole_0))
      | r1_tarski(k1_xboole_0,B_93) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_351,c_58])).

tff(c_476,plain,(
    ! [B_28,B_104] :
      ( ~ r1_tarski(k1_xboole_0,k4_xboole_0(B_28,k1_xboole_0))
      | r1_tarski(k1_xboole_0,B_104) ) ),
    inference(resolution,[status(thm)],[c_436,c_380])).

tff(c_485,plain,(
    ! [B_28] : ~ r1_tarski(k1_xboole_0,k4_xboole_0(B_28,k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_476])).

tff(c_1098,plain,(
    ! [B_1323] : '#skF_1'(k1_xboole_0,k4_xboole_0(B_1323,k1_xboole_0)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_577,c_485])).

tff(c_1083,plain,(
    ! [B_117,B_28] : B_117 = '#skF_1'(k1_xboole_0,k4_xboole_0(B_28,k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_577,c_485])).

tff(c_1796,plain,(
    ! [B_2539] : k1_xboole_0 = B_2539 ),
    inference(superposition,[status(thm),theory(equality)],[c_1098,c_1083])).

tff(c_1829,plain,(
    ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1796,c_485])).

tff(c_1907,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_1829])).

tff(c_1913,plain,(
    ! [B_3593] : r1_tarski(k1_xboole_0,B_3593) ),
    inference(splitRight,[status(thm)],[c_476])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( B_7 = A_6
      | ~ r1_tarski(B_7,A_6)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_1932,plain,(
    ! [B_3593] :
      ( k1_xboole_0 = B_3593
      | ~ r1_tarski(B_3593,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_1913,c_8])).

tff(c_7504,plain,(
    ! [C_11403] : k4_xboole_0(k1_xboole_0,k1_tarski(C_11403)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_7424,c_1932])).

tff(c_7533,plain,(
    ! [C_11403] : ~ r2_hidden(C_11403,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_7504,c_58])).

tff(c_136,plain,(
    ! [A_8,B_57] :
      ( '#skF_1'(k1_tarski(A_8),B_57) = A_8
      | r1_tarski(k1_tarski(A_8),B_57) ) ),
    inference(resolution,[status(thm)],[c_125,c_14])).

tff(c_1908,plain,(
    ! [B_104] : r1_tarski(k1_xboole_0,B_104) ),
    inference(splitRight,[status(thm)],[c_476])).

tff(c_316,plain,(
    ! [A_89] :
      ( ~ r2_hidden(A_89,k1_xboole_0)
      | k1_tarski(A_89) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_306,c_119])).

tff(c_2194,plain,(
    ! [A_3614,B_3615] :
      ( k1_tarski('#skF_1'(A_3614,B_3615)) = k1_xboole_0
      | ~ r1_tarski(A_3614,k1_xboole_0)
      | r1_tarski(A_3614,B_3615) ) ),
    inference(resolution,[status(thm)],[c_436,c_316])).

tff(c_191,plain,(
    ! [C_12,B_67] :
      ( r2_hidden(C_12,B_67)
      | ~ r1_tarski(k1_tarski(C_12),B_67) ) ),
    inference(resolution,[status(thm)],[c_16,c_179])).

tff(c_2226,plain,(
    ! [A_3614,B_3615,B_67] :
      ( r2_hidden('#skF_1'(A_3614,B_3615),B_67)
      | ~ r1_tarski(k1_xboole_0,B_67)
      | ~ r1_tarski(A_3614,k1_xboole_0)
      | r1_tarski(A_3614,B_3615) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2194,c_191])).

tff(c_2266,plain,(
    ! [A_3619,B_3620,B_3621] :
      ( r2_hidden('#skF_1'(A_3619,B_3620),B_3621)
      | ~ r1_tarski(A_3619,k1_xboole_0)
      | r1_tarski(A_3619,B_3620) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1908,c_2226])).

tff(c_2305,plain,(
    ! [A_3622,B_3623] :
      ( ~ r1_tarski(A_3622,k1_xboole_0)
      | r1_tarski(A_3622,B_3623) ) ),
    inference(resolution,[status(thm)],[c_2266,c_4])).

tff(c_2388,plain,(
    ! [A_3629,B_3630] :
      ( r1_tarski(k1_tarski(A_3629),B_3630)
      | '#skF_1'(k1_tarski(A_3629),k1_xboole_0) = A_3629 ) ),
    inference(resolution,[status(thm)],[c_136,c_2305])).

tff(c_2428,plain,(
    ! [A_3631,B_3632] :
      ( r2_hidden(A_3631,B_3632)
      | '#skF_1'(k1_tarski(A_3631),k1_xboole_0) = A_3631 ) ),
    inference(resolution,[status(thm)],[c_2388,c_191])).

tff(c_2513,plain,(
    ! [A_3631] : '#skF_1'(k1_tarski(A_3631),k1_xboole_0) = A_3631 ),
    inference(resolution,[status(thm)],[c_2428,c_58])).

tff(c_50,plain,(
    ! [B_26,A_25] :
      ( k1_tarski(B_26) = A_25
      | k1_xboole_0 = A_25
      | ~ r1_tarski(A_25,k1_tarski(B_26)) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_7502,plain,(
    ! [B_26,C_11321] :
      ( k4_xboole_0(k1_tarski(B_26),k1_tarski(C_11321)) = k1_tarski(B_26)
      | k4_xboole_0(k1_tarski(B_26),k1_tarski(C_11321)) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_7424,c_50])).

tff(c_14504,plain,(
    ! [B_16222,C_16223] :
      ( k4_xboole_0(k1_tarski(B_16222),k1_tarski(C_16223)) = k1_xboole_0
      | k1_tarski(B_16222) != k1_xboole_0 ) ),
    inference(factorization,[status(thm),theory(equality)],[c_7502])).

tff(c_56,plain,(
    ! [A_27,B_28,C_29] :
      ( r2_hidden(A_27,k4_xboole_0(B_28,k1_tarski(C_29)))
      | C_29 = A_27
      | ~ r2_hidden(A_27,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_14539,plain,(
    ! [A_27,C_16223,B_16222] :
      ( r2_hidden(A_27,k1_xboole_0)
      | C_16223 = A_27
      | ~ r2_hidden(A_27,k1_tarski(B_16222))
      | k1_tarski(B_16222) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14504,c_56])).

tff(c_14635,plain,(
    ! [C_16305,A_16306,B_16307] :
      ( C_16305 = A_16306
      | ~ r2_hidden(A_16306,k1_tarski(B_16307))
      | k1_tarski(B_16307) != k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_7533,c_14539])).

tff(c_15096,plain,(
    ! [C_16722,B_16723,B_16724] :
      ( C_16722 = '#skF_1'(k1_tarski(B_16723),B_16724)
      | k1_tarski(B_16723) != k1_xboole_0
      | r1_tarski(k1_tarski(B_16723),B_16724) ) ),
    inference(resolution,[status(thm)],[c_6,c_14635])).

tff(c_16571,plain,(
    ! [B_20586,B_20587,C_20588] :
      ( r2_hidden(B_20586,B_20587)
      | C_20588 = '#skF_1'(k1_tarski(B_20586),B_20587)
      | k1_tarski(B_20586) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_15096,c_191])).

tff(c_7422,plain,(
    ! [B_11236,C_11237] : r1_tarski(k4_xboole_0(B_11236,k1_tarski(C_11237)),B_11236) ),
    inference(resolution,[status(thm)],[c_7330,c_4])).

tff(c_25585,plain,(
    ! [B_31219,B_31220,B_31221] :
      ( r1_tarski('#skF_1'(k1_tarski(B_31219),B_31220),B_31221)
      | r2_hidden(B_31219,B_31220)
      | k1_tarski(B_31219) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16571,c_7422])).

tff(c_25840,plain,(
    ! [A_3631,B_31221] :
      ( r1_tarski(A_3631,B_31221)
      | r2_hidden(A_3631,k1_xboole_0)
      | k1_tarski(A_3631) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2513,c_25585])).

tff(c_25866,plain,(
    ! [A_31357,B_31358] :
      ( r1_tarski(A_31357,B_31358)
      | k1_tarski(A_31357) != k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_7533,c_25840])).

tff(c_18337,plain,(
    ! [C_24914,B_24915,B_24916] :
      ( r2_hidden(C_24914,'#skF_1'(k1_tarski(B_24915),B_24916))
      | r2_hidden(B_24915,B_24916)
      | k1_tarski(B_24915) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16571,c_16])).

tff(c_18608,plain,(
    ! [C_24914,A_3631] :
      ( r2_hidden(C_24914,A_3631)
      | r2_hidden(A_3631,k1_xboole_0)
      | k1_tarski(A_3631) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2513,c_18337])).

tff(c_18649,plain,(
    ! [C_25052,A_25053] :
      ( r2_hidden(C_25052,A_25053)
      | k1_tarski(A_25053) != k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_7533,c_18608])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_18790,plain,(
    ! [C_25052,B_2,A_25053] :
      ( r2_hidden(C_25052,B_2)
      | ~ r1_tarski(A_25053,B_2)
      | k1_tarski(A_25053) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_18649,c_2])).

tff(c_25963,plain,(
    ! [C_25052,B_31358,A_31357] :
      ( r2_hidden(C_25052,B_31358)
      | k1_tarski(A_31357) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_25866,c_18790])).

tff(c_26259,plain,(
    ! [A_31357] : k1_tarski(A_31357) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_25963])).

tff(c_320,plain,(
    ! [A_90,B_91] :
      ( r2_hidden('#skF_6'(A_90,B_91),A_90)
      | r1_tarski(B_91,k1_setfam_1(A_90))
      | k1_xboole_0 = A_90 ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_338,plain,(
    ! [A_8,B_91] :
      ( '#skF_6'(k1_tarski(A_8),B_91) = A_8
      | r1_tarski(B_91,k1_setfam_1(k1_tarski(A_8)))
      | k1_tarski(A_8) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_320,c_14])).

tff(c_26268,plain,(
    ! [A_31713,B_31714] :
      ( '#skF_6'(k1_tarski(A_31713),B_31714) = A_31713
      | r1_tarski(B_31714,k1_setfam_1(k1_tarski(A_31713))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_26259,c_338])).

tff(c_62,plain,(
    ! [B_31,A_30] :
      ( r1_tarski(k1_setfam_1(B_31),A_30)
      | ~ r2_hidden(A_30,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_118,plain,(
    ! [B_31,A_30] :
      ( k1_setfam_1(B_31) = A_30
      | ~ r1_tarski(A_30,k1_setfam_1(B_31))
      | ~ r2_hidden(A_30,B_31) ) ),
    inference(resolution,[status(thm)],[c_62,c_111])).

tff(c_108561,plain,(
    ! [A_59559,B_59560] :
      ( k1_setfam_1(k1_tarski(A_59559)) = B_59560
      | ~ r2_hidden(B_59560,k1_tarski(A_59559))
      | '#skF_6'(k1_tarski(A_59559),B_59560) = A_59559 ) ),
    inference(resolution,[status(thm)],[c_26268,c_118])).

tff(c_108814,plain,(
    ! [C_59723] :
      ( k1_setfam_1(k1_tarski(C_59723)) = C_59723
      | '#skF_6'(k1_tarski(C_59723),C_59723) = C_59723 ) ),
    inference(resolution,[status(thm)],[c_16,c_108561])).

tff(c_109805,plain,(
    '#skF_6'(k1_tarski('#skF_7'),'#skF_7') = '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_108814,c_68])).

tff(c_64,plain,(
    ! [B_33,A_32] :
      ( ~ r1_tarski(B_33,'#skF_6'(A_32,B_33))
      | r1_tarski(B_33,k1_setfam_1(A_32))
      | k1_xboole_0 = A_32 ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_109905,plain,
    ( ~ r1_tarski('#skF_7','#skF_7')
    | r1_tarski('#skF_7',k1_setfam_1(k1_tarski('#skF_7')))
    | k1_tarski('#skF_7') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_109805,c_64])).

tff(c_110162,plain,
    ( r1_tarski('#skF_7',k1_setfam_1(k1_tarski('#skF_7')))
    | k1_tarski('#skF_7') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_109905])).

tff(c_110163,plain,(
    r1_tarski('#skF_7',k1_setfam_1(k1_tarski('#skF_7'))) ),
    inference(negUnitSimplification,[status(thm)],[c_26259,c_110162])).

tff(c_110399,plain,
    ( k1_setfam_1(k1_tarski('#skF_7')) = '#skF_7'
    | ~ r2_hidden('#skF_7',k1_tarski('#skF_7')) ),
    inference(resolution,[status(thm)],[c_110163,c_118])).

tff(c_110646,plain,(
    k1_setfam_1(k1_tarski('#skF_7')) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_110399])).

tff(c_110648,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_110646])).

tff(c_110649,plain,(
    ! [C_25052,B_31358] : r2_hidden(C_25052,B_31358) ),
    inference(splitRight,[status(thm)],[c_25963])).

tff(c_2330,plain,(
    ! [B_3627,B_3628] :
      ( r1_tarski(k1_setfam_1(B_3627),B_3628)
      | ~ r2_hidden(k1_xboole_0,B_3627) ) ),
    inference(resolution,[status(thm)],[c_62,c_2305])).

tff(c_2380,plain,(
    ! [B_3627,B_3628] :
      ( k1_setfam_1(B_3627) = B_3628
      | ~ r1_tarski(B_3628,k1_setfam_1(B_3627))
      | ~ r2_hidden(k1_xboole_0,B_3627) ) ),
    inference(resolution,[status(thm)],[c_2330,c_8])).

tff(c_7621,plain,(
    ! [B_11567,C_11568] :
      ( k4_xboole_0(k1_setfam_1(B_11567),k1_tarski(C_11568)) = k1_setfam_1(B_11567)
      | ~ r2_hidden(k1_xboole_0,B_11567) ) ),
    inference(resolution,[status(thm)],[c_7424,c_2380])).

tff(c_7651,plain,(
    ! [C_11568,B_11567] :
      ( ~ r2_hidden(C_11568,k1_setfam_1(B_11567))
      | ~ r2_hidden(k1_xboole_0,B_11567) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7621,c_58])).

tff(c_110806,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_110649,c_110649,c_7651])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:05:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 17.69/8.83  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 17.75/8.84  
% 17.75/8.84  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 17.78/8.84  %$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_6 > #skF_4 > #skF_7 > #skF_3 > #skF_5 > #skF_2 > #skF_1
% 17.78/8.84  
% 17.78/8.84  %Foreground sorts:
% 17.78/8.84  
% 17.78/8.84  
% 17.78/8.84  %Background operators:
% 17.78/8.84  
% 17.78/8.84  
% 17.78/8.84  %Foreground operators:
% 17.78/8.84  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 17.78/8.84  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 17.78/8.84  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 17.78/8.84  tff(k1_tarski, type, k1_tarski: $i > $i).
% 17.78/8.84  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 17.78/8.84  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 17.78/8.84  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 17.78/8.84  tff('#skF_7', type, '#skF_7': $i).
% 17.78/8.84  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 17.78/8.84  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 17.78/8.84  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 17.78/8.84  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 17.78/8.84  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 17.78/8.84  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 17.78/8.84  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 17.78/8.84  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 17.78/8.84  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 17.78/8.84  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 17.78/8.84  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 17.78/8.84  
% 17.78/8.86  tff(f_89, negated_conjecture, ~(![A]: (k1_setfam_1(k1_tarski(A)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_setfam_1)).
% 17.78/8.86  tff(f_45, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 17.78/8.86  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 17.78/8.86  tff(f_73, axiom, (![A, B, C]: (r2_hidden(A, k4_xboole_0(B, k1_tarski(C))) <=> (r2_hidden(A, B) & ~(A = C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 17.78/8.86  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 17.78/8.86  tff(f_66, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 17.78/8.86  tff(f_86, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) => r1_tarski(B, C))) => ((A = k1_xboole_0) | r1_tarski(B, k1_setfam_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_setfam_1)).
% 17.78/8.86  tff(f_77, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(k1_setfam_1(B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_setfam_1)).
% 17.78/8.86  tff(c_68, plain, (k1_setfam_1(k1_tarski('#skF_7'))!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_89])).
% 17.78/8.86  tff(c_16, plain, (![C_12]: (r2_hidden(C_12, k1_tarski(C_12)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 17.78/8.86  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 17.78/8.86  tff(c_173, plain, (![A_63, B_64, C_65]: (r2_hidden(A_63, B_64) | ~r2_hidden(A_63, k4_xboole_0(B_64, k1_tarski(C_65))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 17.78/8.86  tff(c_7330, plain, (![B_11236, C_11237, B_11238]: (r2_hidden('#skF_1'(k4_xboole_0(B_11236, k1_tarski(C_11237)), B_11238), B_11236) | r1_tarski(k4_xboole_0(B_11236, k1_tarski(C_11237)), B_11238))), inference(resolution, [status(thm)], [c_6, c_173])).
% 17.78/8.86  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 17.78/8.86  tff(c_7424, plain, (![B_11320, C_11321]: (r1_tarski(k4_xboole_0(B_11320, k1_tarski(C_11321)), B_11320))), inference(resolution, [status(thm)], [c_7330, c_4])).
% 17.78/8.86  tff(c_12, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 17.78/8.86  tff(c_54, plain, (![B_26]: (r1_tarski(k1_xboole_0, k1_tarski(B_26)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 17.78/8.86  tff(c_179, plain, (![C_66, B_67, A_68]: (r2_hidden(C_66, B_67) | ~r2_hidden(C_66, A_68) | ~r1_tarski(A_68, B_67))), inference(cnfTransformation, [status(thm)], [f_32])).
% 17.78/8.86  tff(c_436, plain, (![A_103, B_104, B_105]: (r2_hidden('#skF_1'(A_103, B_104), B_105) | ~r1_tarski(A_103, B_105) | r1_tarski(A_103, B_104))), inference(resolution, [status(thm)], [c_6, c_179])).
% 17.78/8.86  tff(c_14, plain, (![C_12, A_8]: (C_12=A_8 | ~r2_hidden(C_12, k1_tarski(A_8)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 17.78/8.86  tff(c_559, plain, (![A_114, A_115, B_116]: (A_114='#skF_1'(A_115, B_116) | ~r1_tarski(A_115, k1_tarski(A_114)) | r1_tarski(A_115, B_116))), inference(resolution, [status(thm)], [c_436, c_14])).
% 17.78/8.86  tff(c_577, plain, (![B_117, B_118]: (B_117='#skF_1'(k1_xboole_0, B_118) | r1_tarski(k1_xboole_0, B_118))), inference(resolution, [status(thm)], [c_54, c_559])).
% 17.78/8.86  tff(c_125, plain, (![A_56, B_57]: (r2_hidden('#skF_1'(A_56, B_57), A_56) | r1_tarski(A_56, B_57))), inference(cnfTransformation, [status(thm)], [f_32])).
% 17.78/8.86  tff(c_228, plain, (![A_80, B_81]: ('#skF_1'(k1_tarski(A_80), B_81)=A_80 | r1_tarski(k1_tarski(A_80), B_81))), inference(resolution, [status(thm)], [c_125, c_14])).
% 17.78/8.86  tff(c_111, plain, (![B_53, A_54]: (B_53=A_54 | ~r1_tarski(B_53, A_54) | ~r1_tarski(A_54, B_53))), inference(cnfTransformation, [status(thm)], [f_38])).
% 17.78/8.86  tff(c_119, plain, (![B_26]: (k1_tarski(B_26)=k1_xboole_0 | ~r1_tarski(k1_tarski(B_26), k1_xboole_0))), inference(resolution, [status(thm)], [c_54, c_111])).
% 17.78/8.86  tff(c_264, plain, (![A_86]: (k1_tarski(A_86)=k1_xboole_0 | '#skF_1'(k1_tarski(A_86), k1_xboole_0)=A_86)), inference(resolution, [status(thm)], [c_228, c_119])).
% 17.78/8.86  tff(c_306, plain, (![A_89]: (~r2_hidden(A_89, k1_xboole_0) | r1_tarski(k1_tarski(A_89), k1_xboole_0) | k1_tarski(A_89)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_264, c_4])).
% 17.78/8.86  tff(c_339, plain, (![A_92]: (~r2_hidden(A_92, k1_xboole_0) | k1_tarski(A_92)=k1_xboole_0)), inference(resolution, [status(thm)], [c_306, c_119])).
% 17.78/8.86  tff(c_351, plain, (![B_93]: (k1_tarski('#skF_1'(k1_xboole_0, B_93))=k1_xboole_0 | r1_tarski(k1_xboole_0, B_93))), inference(resolution, [status(thm)], [c_6, c_339])).
% 17.78/8.86  tff(c_58, plain, (![C_29, B_28]: (~r2_hidden(C_29, k4_xboole_0(B_28, k1_tarski(C_29))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 17.78/8.86  tff(c_380, plain, (![B_93, B_28]: (~r2_hidden('#skF_1'(k1_xboole_0, B_93), k4_xboole_0(B_28, k1_xboole_0)) | r1_tarski(k1_xboole_0, B_93))), inference(superposition, [status(thm), theory('equality')], [c_351, c_58])).
% 17.78/8.86  tff(c_476, plain, (![B_28, B_104]: (~r1_tarski(k1_xboole_0, k4_xboole_0(B_28, k1_xboole_0)) | r1_tarski(k1_xboole_0, B_104))), inference(resolution, [status(thm)], [c_436, c_380])).
% 17.78/8.86  tff(c_485, plain, (![B_28]: (~r1_tarski(k1_xboole_0, k4_xboole_0(B_28, k1_xboole_0)))), inference(splitLeft, [status(thm)], [c_476])).
% 17.78/8.86  tff(c_1098, plain, (![B_1323]: ('#skF_1'(k1_xboole_0, k4_xboole_0(B_1323, k1_xboole_0))=k1_xboole_0)), inference(resolution, [status(thm)], [c_577, c_485])).
% 17.78/8.86  tff(c_1083, plain, (![B_117, B_28]: (B_117='#skF_1'(k1_xboole_0, k4_xboole_0(B_28, k1_xboole_0)))), inference(resolution, [status(thm)], [c_577, c_485])).
% 17.78/8.86  tff(c_1796, plain, (![B_2539]: (k1_xboole_0=B_2539)), inference(superposition, [status(thm), theory('equality')], [c_1098, c_1083])).
% 17.78/8.86  tff(c_1829, plain, (~r1_tarski(k1_xboole_0, k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1796, c_485])).
% 17.78/8.86  tff(c_1907, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_1829])).
% 17.78/8.86  tff(c_1913, plain, (![B_3593]: (r1_tarski(k1_xboole_0, B_3593))), inference(splitRight, [status(thm)], [c_476])).
% 17.78/8.86  tff(c_8, plain, (![B_7, A_6]: (B_7=A_6 | ~r1_tarski(B_7, A_6) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 17.78/8.86  tff(c_1932, plain, (![B_3593]: (k1_xboole_0=B_3593 | ~r1_tarski(B_3593, k1_xboole_0))), inference(resolution, [status(thm)], [c_1913, c_8])).
% 17.78/8.86  tff(c_7504, plain, (![C_11403]: (k4_xboole_0(k1_xboole_0, k1_tarski(C_11403))=k1_xboole_0)), inference(resolution, [status(thm)], [c_7424, c_1932])).
% 17.78/8.86  tff(c_7533, plain, (![C_11403]: (~r2_hidden(C_11403, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_7504, c_58])).
% 17.78/8.86  tff(c_136, plain, (![A_8, B_57]: ('#skF_1'(k1_tarski(A_8), B_57)=A_8 | r1_tarski(k1_tarski(A_8), B_57))), inference(resolution, [status(thm)], [c_125, c_14])).
% 17.78/8.86  tff(c_1908, plain, (![B_104]: (r1_tarski(k1_xboole_0, B_104))), inference(splitRight, [status(thm)], [c_476])).
% 17.78/8.86  tff(c_316, plain, (![A_89]: (~r2_hidden(A_89, k1_xboole_0) | k1_tarski(A_89)=k1_xboole_0)), inference(resolution, [status(thm)], [c_306, c_119])).
% 17.78/8.86  tff(c_2194, plain, (![A_3614, B_3615]: (k1_tarski('#skF_1'(A_3614, B_3615))=k1_xboole_0 | ~r1_tarski(A_3614, k1_xboole_0) | r1_tarski(A_3614, B_3615))), inference(resolution, [status(thm)], [c_436, c_316])).
% 17.78/8.86  tff(c_191, plain, (![C_12, B_67]: (r2_hidden(C_12, B_67) | ~r1_tarski(k1_tarski(C_12), B_67))), inference(resolution, [status(thm)], [c_16, c_179])).
% 17.78/8.86  tff(c_2226, plain, (![A_3614, B_3615, B_67]: (r2_hidden('#skF_1'(A_3614, B_3615), B_67) | ~r1_tarski(k1_xboole_0, B_67) | ~r1_tarski(A_3614, k1_xboole_0) | r1_tarski(A_3614, B_3615))), inference(superposition, [status(thm), theory('equality')], [c_2194, c_191])).
% 17.78/8.86  tff(c_2266, plain, (![A_3619, B_3620, B_3621]: (r2_hidden('#skF_1'(A_3619, B_3620), B_3621) | ~r1_tarski(A_3619, k1_xboole_0) | r1_tarski(A_3619, B_3620))), inference(demodulation, [status(thm), theory('equality')], [c_1908, c_2226])).
% 17.78/8.86  tff(c_2305, plain, (![A_3622, B_3623]: (~r1_tarski(A_3622, k1_xboole_0) | r1_tarski(A_3622, B_3623))), inference(resolution, [status(thm)], [c_2266, c_4])).
% 17.78/8.86  tff(c_2388, plain, (![A_3629, B_3630]: (r1_tarski(k1_tarski(A_3629), B_3630) | '#skF_1'(k1_tarski(A_3629), k1_xboole_0)=A_3629)), inference(resolution, [status(thm)], [c_136, c_2305])).
% 17.78/8.86  tff(c_2428, plain, (![A_3631, B_3632]: (r2_hidden(A_3631, B_3632) | '#skF_1'(k1_tarski(A_3631), k1_xboole_0)=A_3631)), inference(resolution, [status(thm)], [c_2388, c_191])).
% 17.78/8.86  tff(c_2513, plain, (![A_3631]: ('#skF_1'(k1_tarski(A_3631), k1_xboole_0)=A_3631)), inference(resolution, [status(thm)], [c_2428, c_58])).
% 17.78/8.86  tff(c_50, plain, (![B_26, A_25]: (k1_tarski(B_26)=A_25 | k1_xboole_0=A_25 | ~r1_tarski(A_25, k1_tarski(B_26)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 17.78/8.86  tff(c_7502, plain, (![B_26, C_11321]: (k4_xboole_0(k1_tarski(B_26), k1_tarski(C_11321))=k1_tarski(B_26) | k4_xboole_0(k1_tarski(B_26), k1_tarski(C_11321))=k1_xboole_0)), inference(resolution, [status(thm)], [c_7424, c_50])).
% 17.78/8.86  tff(c_14504, plain, (![B_16222, C_16223]: (k4_xboole_0(k1_tarski(B_16222), k1_tarski(C_16223))=k1_xboole_0 | k1_tarski(B_16222)!=k1_xboole_0)), inference(factorization, [status(thm), theory('equality')], [c_7502])).
% 17.78/8.86  tff(c_56, plain, (![A_27, B_28, C_29]: (r2_hidden(A_27, k4_xboole_0(B_28, k1_tarski(C_29))) | C_29=A_27 | ~r2_hidden(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_73])).
% 17.78/8.86  tff(c_14539, plain, (![A_27, C_16223, B_16222]: (r2_hidden(A_27, k1_xboole_0) | C_16223=A_27 | ~r2_hidden(A_27, k1_tarski(B_16222)) | k1_tarski(B_16222)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_14504, c_56])).
% 17.78/8.86  tff(c_14635, plain, (![C_16305, A_16306, B_16307]: (C_16305=A_16306 | ~r2_hidden(A_16306, k1_tarski(B_16307)) | k1_tarski(B_16307)!=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_7533, c_14539])).
% 17.78/8.86  tff(c_15096, plain, (![C_16722, B_16723, B_16724]: (C_16722='#skF_1'(k1_tarski(B_16723), B_16724) | k1_tarski(B_16723)!=k1_xboole_0 | r1_tarski(k1_tarski(B_16723), B_16724))), inference(resolution, [status(thm)], [c_6, c_14635])).
% 17.78/8.86  tff(c_16571, plain, (![B_20586, B_20587, C_20588]: (r2_hidden(B_20586, B_20587) | C_20588='#skF_1'(k1_tarski(B_20586), B_20587) | k1_tarski(B_20586)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_15096, c_191])).
% 17.78/8.86  tff(c_7422, plain, (![B_11236, C_11237]: (r1_tarski(k4_xboole_0(B_11236, k1_tarski(C_11237)), B_11236))), inference(resolution, [status(thm)], [c_7330, c_4])).
% 17.78/8.86  tff(c_25585, plain, (![B_31219, B_31220, B_31221]: (r1_tarski('#skF_1'(k1_tarski(B_31219), B_31220), B_31221) | r2_hidden(B_31219, B_31220) | k1_tarski(B_31219)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_16571, c_7422])).
% 17.78/8.86  tff(c_25840, plain, (![A_3631, B_31221]: (r1_tarski(A_3631, B_31221) | r2_hidden(A_3631, k1_xboole_0) | k1_tarski(A_3631)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2513, c_25585])).
% 17.78/8.86  tff(c_25866, plain, (![A_31357, B_31358]: (r1_tarski(A_31357, B_31358) | k1_tarski(A_31357)!=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_7533, c_25840])).
% 17.78/8.86  tff(c_18337, plain, (![C_24914, B_24915, B_24916]: (r2_hidden(C_24914, '#skF_1'(k1_tarski(B_24915), B_24916)) | r2_hidden(B_24915, B_24916) | k1_tarski(B_24915)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_16571, c_16])).
% 17.78/8.86  tff(c_18608, plain, (![C_24914, A_3631]: (r2_hidden(C_24914, A_3631) | r2_hidden(A_3631, k1_xboole_0) | k1_tarski(A_3631)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2513, c_18337])).
% 17.78/8.86  tff(c_18649, plain, (![C_25052, A_25053]: (r2_hidden(C_25052, A_25053) | k1_tarski(A_25053)!=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_7533, c_18608])).
% 17.78/8.86  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 17.78/8.86  tff(c_18790, plain, (![C_25052, B_2, A_25053]: (r2_hidden(C_25052, B_2) | ~r1_tarski(A_25053, B_2) | k1_tarski(A_25053)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_18649, c_2])).
% 17.78/8.86  tff(c_25963, plain, (![C_25052, B_31358, A_31357]: (r2_hidden(C_25052, B_31358) | k1_tarski(A_31357)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_25866, c_18790])).
% 17.78/8.86  tff(c_26259, plain, (![A_31357]: (k1_tarski(A_31357)!=k1_xboole_0)), inference(splitLeft, [status(thm)], [c_25963])).
% 17.78/8.86  tff(c_320, plain, (![A_90, B_91]: (r2_hidden('#skF_6'(A_90, B_91), A_90) | r1_tarski(B_91, k1_setfam_1(A_90)) | k1_xboole_0=A_90)), inference(cnfTransformation, [status(thm)], [f_86])).
% 17.78/8.86  tff(c_338, plain, (![A_8, B_91]: ('#skF_6'(k1_tarski(A_8), B_91)=A_8 | r1_tarski(B_91, k1_setfam_1(k1_tarski(A_8))) | k1_tarski(A_8)=k1_xboole_0)), inference(resolution, [status(thm)], [c_320, c_14])).
% 17.78/8.86  tff(c_26268, plain, (![A_31713, B_31714]: ('#skF_6'(k1_tarski(A_31713), B_31714)=A_31713 | r1_tarski(B_31714, k1_setfam_1(k1_tarski(A_31713))))), inference(negUnitSimplification, [status(thm)], [c_26259, c_338])).
% 17.78/8.86  tff(c_62, plain, (![B_31, A_30]: (r1_tarski(k1_setfam_1(B_31), A_30) | ~r2_hidden(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_77])).
% 17.78/8.86  tff(c_118, plain, (![B_31, A_30]: (k1_setfam_1(B_31)=A_30 | ~r1_tarski(A_30, k1_setfam_1(B_31)) | ~r2_hidden(A_30, B_31))), inference(resolution, [status(thm)], [c_62, c_111])).
% 17.78/8.86  tff(c_108561, plain, (![A_59559, B_59560]: (k1_setfam_1(k1_tarski(A_59559))=B_59560 | ~r2_hidden(B_59560, k1_tarski(A_59559)) | '#skF_6'(k1_tarski(A_59559), B_59560)=A_59559)), inference(resolution, [status(thm)], [c_26268, c_118])).
% 17.78/8.86  tff(c_108814, plain, (![C_59723]: (k1_setfam_1(k1_tarski(C_59723))=C_59723 | '#skF_6'(k1_tarski(C_59723), C_59723)=C_59723)), inference(resolution, [status(thm)], [c_16, c_108561])).
% 17.78/8.86  tff(c_109805, plain, ('#skF_6'(k1_tarski('#skF_7'), '#skF_7')='#skF_7'), inference(superposition, [status(thm), theory('equality')], [c_108814, c_68])).
% 17.78/8.86  tff(c_64, plain, (![B_33, A_32]: (~r1_tarski(B_33, '#skF_6'(A_32, B_33)) | r1_tarski(B_33, k1_setfam_1(A_32)) | k1_xboole_0=A_32)), inference(cnfTransformation, [status(thm)], [f_86])).
% 17.78/8.86  tff(c_109905, plain, (~r1_tarski('#skF_7', '#skF_7') | r1_tarski('#skF_7', k1_setfam_1(k1_tarski('#skF_7'))) | k1_tarski('#skF_7')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_109805, c_64])).
% 17.78/8.86  tff(c_110162, plain, (r1_tarski('#skF_7', k1_setfam_1(k1_tarski('#skF_7'))) | k1_tarski('#skF_7')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_12, c_109905])).
% 17.78/8.86  tff(c_110163, plain, (r1_tarski('#skF_7', k1_setfam_1(k1_tarski('#skF_7')))), inference(negUnitSimplification, [status(thm)], [c_26259, c_110162])).
% 17.78/8.86  tff(c_110399, plain, (k1_setfam_1(k1_tarski('#skF_7'))='#skF_7' | ~r2_hidden('#skF_7', k1_tarski('#skF_7'))), inference(resolution, [status(thm)], [c_110163, c_118])).
% 17.78/8.86  tff(c_110646, plain, (k1_setfam_1(k1_tarski('#skF_7'))='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_16, c_110399])).
% 17.78/8.86  tff(c_110648, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_110646])).
% 17.78/8.86  tff(c_110649, plain, (![C_25052, B_31358]: (r2_hidden(C_25052, B_31358))), inference(splitRight, [status(thm)], [c_25963])).
% 17.78/8.86  tff(c_2330, plain, (![B_3627, B_3628]: (r1_tarski(k1_setfam_1(B_3627), B_3628) | ~r2_hidden(k1_xboole_0, B_3627))), inference(resolution, [status(thm)], [c_62, c_2305])).
% 17.78/8.86  tff(c_2380, plain, (![B_3627, B_3628]: (k1_setfam_1(B_3627)=B_3628 | ~r1_tarski(B_3628, k1_setfam_1(B_3627)) | ~r2_hidden(k1_xboole_0, B_3627))), inference(resolution, [status(thm)], [c_2330, c_8])).
% 17.78/8.86  tff(c_7621, plain, (![B_11567, C_11568]: (k4_xboole_0(k1_setfam_1(B_11567), k1_tarski(C_11568))=k1_setfam_1(B_11567) | ~r2_hidden(k1_xboole_0, B_11567))), inference(resolution, [status(thm)], [c_7424, c_2380])).
% 17.78/8.86  tff(c_7651, plain, (![C_11568, B_11567]: (~r2_hidden(C_11568, k1_setfam_1(B_11567)) | ~r2_hidden(k1_xboole_0, B_11567))), inference(superposition, [status(thm), theory('equality')], [c_7621, c_58])).
% 17.78/8.86  tff(c_110806, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_110649, c_110649, c_7651])).
% 17.78/8.86  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 17.78/8.86  
% 17.78/8.86  Inference rules
% 17.78/8.86  ----------------------
% 17.78/8.86  #Ref     : 2
% 17.78/8.86  #Sup     : 16472
% 17.78/8.86  #Fact    : 27
% 17.78/8.86  #Define  : 0
% 17.78/8.86  #Split   : 18
% 17.78/8.86  #Chain   : 0
% 17.78/8.86  #Close   : 0
% 17.78/8.86  
% 17.78/8.86  Ordering : KBO
% 17.78/8.86  
% 17.78/8.86  Simplification rules
% 17.78/8.86  ----------------------
% 17.78/8.86  #Subsume      : 4884
% 17.78/8.86  #Demod        : 6767
% 17.78/8.86  #Tautology    : 5645
% 17.78/8.86  #SimpNegUnit  : 797
% 17.78/8.86  #BackRed      : 70
% 17.78/8.86  
% 17.78/8.86  #Partial instantiations: 30459
% 17.78/8.86  #Strategies tried      : 1
% 17.78/8.86  
% 17.78/8.86  Timing (in seconds)
% 17.78/8.86  ----------------------
% 17.78/8.87  Preprocessing        : 0.31
% 17.78/8.87  Parsing              : 0.16
% 17.78/8.87  CNF conversion       : 0.02
% 17.78/8.87  Main loop            : 7.76
% 17.78/8.87  Inferencing          : 2.15
% 17.78/8.87  Reduction            : 2.03
% 17.78/8.87  Demodulation         : 1.30
% 17.78/8.87  BG Simplification    : 0.23
% 17.78/8.87  Subsumption          : 2.94
% 17.78/8.87  Abstraction          : 0.34
% 17.78/8.87  MUC search           : 0.00
% 17.78/8.87  Cooper               : 0.00
% 17.78/8.87  Total                : 8.11
% 17.78/8.87  Index Insertion      : 0.00
% 17.78/8.87  Index Deletion       : 0.00
% 17.78/8.87  Index Matching       : 0.00
% 17.78/8.87  BG Taut test         : 0.00
%------------------------------------------------------------------------------
