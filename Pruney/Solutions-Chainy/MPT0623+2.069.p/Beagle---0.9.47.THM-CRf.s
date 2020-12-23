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
% DateTime   : Thu Dec  3 10:03:15 EST 2020

% Result     : Theorem 2.34s
% Output     : CNFRefutation 2.34s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 427 expanded)
%              Number of leaves         :   25 ( 141 expanded)
%              Depth                    :   11
%              Number of atoms          :  165 (1061 expanded)
%              Number of equality atoms :   91 ( 628 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_3 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_93,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( ~ ( A = k1_xboole_0
              & B != k1_xboole_0 )
          & ! [C] :
              ( ( v1_relat_1(C)
                & v1_funct_1(C) )
             => ~ ( B = k1_relat_1(C)
                  & r1_tarski(k2_relat_1(C),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_funct_1)).

tff(f_33,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_75,axiom,(
    ! [A] :
      ( A != k1_xboole_0
     => ! [B] :
        ? [C] :
          ( v1_relat_1(C)
          & v1_funct_1(C)
          & k1_relat_1(C) = A
          & k2_relat_1(C) = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_funct_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_42,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_35,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_62,axiom,(
    ! [A] :
    ? [B] :
      ( v1_relat_1(B)
      & v1_funct_1(B)
      & k1_relat_1(B) = A
      & ! [C] :
          ( r2_hidden(C,A)
         => k1_funct_1(B,C) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e2_25__funct_1)).

tff(f_50,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

tff(c_36,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_57,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_2,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),A_1)
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_28,plain,(
    ! [A_13,B_17] :
      ( k1_relat_1('#skF_3'(A_13,B_17)) = A_13
      | k1_xboole_0 = A_13 ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_30,plain,(
    ! [A_13,B_17] :
      ( v1_funct_1('#skF_3'(A_13,B_17))
      | k1_xboole_0 = A_13 ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_32,plain,(
    ! [A_13,B_17] :
      ( v1_relat_1('#skF_3'(A_13,B_17))
      | k1_xboole_0 = A_13 ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_8,plain,(
    ! [A_4,B_5] :
      ( r1_tarski(k1_tarski(A_4),B_5)
      | ~ r2_hidden(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_217,plain,(
    ! [A_46,B_47] :
      ( k2_relat_1('#skF_3'(A_46,B_47)) = k1_tarski(B_47)
      | k1_xboole_0 = A_46 ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_34,plain,(
    ! [C_20] :
      ( ~ r1_tarski(k2_relat_1(C_20),'#skF_4')
      | k1_relat_1(C_20) != '#skF_5'
      | ~ v1_funct_1(C_20)
      | ~ v1_relat_1(C_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_244,plain,(
    ! [B_56,A_57] :
      ( ~ r1_tarski(k1_tarski(B_56),'#skF_4')
      | k1_relat_1('#skF_3'(A_57,B_56)) != '#skF_5'
      | ~ v1_funct_1('#skF_3'(A_57,B_56))
      | ~ v1_relat_1('#skF_3'(A_57,B_56))
      | k1_xboole_0 = A_57 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_217,c_34])).

tff(c_249,plain,(
    ! [A_58,A_59] :
      ( k1_relat_1('#skF_3'(A_58,A_59)) != '#skF_5'
      | ~ v1_funct_1('#skF_3'(A_58,A_59))
      | ~ v1_relat_1('#skF_3'(A_58,A_59))
      | k1_xboole_0 = A_58
      | ~ r2_hidden(A_59,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_8,c_244])).

tff(c_254,plain,(
    ! [A_60,B_61] :
      ( k1_relat_1('#skF_3'(A_60,B_61)) != '#skF_5'
      | ~ v1_funct_1('#skF_3'(A_60,B_61))
      | ~ r2_hidden(B_61,'#skF_4')
      | k1_xboole_0 = A_60 ) ),
    inference(resolution,[status(thm)],[c_32,c_249])).

tff(c_259,plain,(
    ! [A_62,B_63] :
      ( k1_relat_1('#skF_3'(A_62,B_63)) != '#skF_5'
      | ~ r2_hidden(B_63,'#skF_4')
      | k1_xboole_0 = A_62 ) ),
    inference(resolution,[status(thm)],[c_30,c_254])).

tff(c_262,plain,(
    ! [A_13,B_17] :
      ( A_13 != '#skF_5'
      | ~ r2_hidden(B_17,'#skF_4')
      | k1_xboole_0 = A_13
      | k1_xboole_0 = A_13 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_259])).

tff(c_264,plain,(
    ! [B_64] : ~ r2_hidden(B_64,'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_262])).

tff(c_268,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_2,c_264])).

tff(c_272,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_57,c_268])).

tff(c_274,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_262])).

tff(c_12,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_4,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_10,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_59,plain,(
    ! [C_26] :
      ( ~ r1_tarski(k2_relat_1(C_26),'#skF_4')
      | k1_relat_1(C_26) != '#skF_5'
      | ~ v1_funct_1(C_26)
      | ~ v1_relat_1(C_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_62,plain,
    ( ~ r1_tarski(k1_xboole_0,'#skF_4')
    | k1_relat_1(k1_xboole_0) != '#skF_5'
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_59])).

tff(c_64,plain,
    ( k1_xboole_0 != '#skF_5'
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_4,c_62])).

tff(c_67,plain,(
    ~ v1_relat_1(k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_20,plain,(
    ! [A_7] : k1_relat_1('#skF_2'(A_7)) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_24,plain,(
    ! [A_7] : v1_relat_1('#skF_2'(A_7)) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_68,plain,(
    ! [A_31] :
      ( k1_relat_1(A_31) != k1_xboole_0
      | k1_xboole_0 = A_31
      | ~ v1_relat_1(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_74,plain,(
    ! [A_7] :
      ( k1_relat_1('#skF_2'(A_7)) != k1_xboole_0
      | '#skF_2'(A_7) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_24,c_68])).

tff(c_88,plain,(
    ! [A_33] :
      ( k1_xboole_0 != A_33
      | '#skF_2'(A_33) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_74])).

tff(c_98,plain,(
    ! [A_33] :
      ( v1_relat_1(k1_xboole_0)
      | k1_xboole_0 != A_33 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_24])).

tff(c_104,plain,(
    ! [A_33] : k1_xboole_0 != A_33 ),
    inference(negUnitSimplification,[status(thm)],[c_67,c_98])).

tff(c_114,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_104,c_10])).

tff(c_115,plain,
    ( ~ v1_funct_1(k1_xboole_0)
    | k1_xboole_0 != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_117,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_115])).

tff(c_299,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_274,c_117])).

tff(c_301,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_115])).

tff(c_300,plain,(
    ~ v1_funct_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_115])).

tff(c_303,plain,(
    ~ v1_funct_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_301,c_300])).

tff(c_16,plain,(
    ! [A_6] :
      ( k1_relat_1(A_6) != k1_xboole_0
      | k1_xboole_0 = A_6
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_333,plain,(
    ! [A_71] :
      ( k1_relat_1(A_71) != '#skF_5'
      | A_71 = '#skF_5'
      | ~ v1_relat_1(A_71) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_301,c_301,c_16])).

tff(c_342,plain,(
    ! [A_7] :
      ( k1_relat_1('#skF_2'(A_7)) != '#skF_5'
      | '#skF_2'(A_7) = '#skF_5' ) ),
    inference(resolution,[status(thm)],[c_24,c_333])).

tff(c_351,plain,(
    ! [A_72] :
      ( A_72 != '#skF_5'
      | '#skF_2'(A_72) = '#skF_5' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_342])).

tff(c_22,plain,(
    ! [A_7] : v1_funct_1('#skF_2'(A_7)) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_359,plain,(
    ! [A_72] :
      ( v1_funct_1('#skF_5')
      | A_72 != '#skF_5' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_351,c_22])).

tff(c_367,plain,(
    ! [A_72] : A_72 != '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_303,c_359])).

tff(c_309,plain,(
    k2_relat_1('#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_301,c_301,c_10])).

tff(c_377,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_367,c_309])).

tff(c_379,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_378,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_388,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_379,c_378])).

tff(c_381,plain,(
    k1_relat_1('#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_378,c_378,c_12])).

tff(c_400,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_388,c_388,c_381])).

tff(c_382,plain,(
    ! [A_3] : r1_tarski('#skF_5',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_378,c_4])).

tff(c_398,plain,(
    ! [A_3] : r1_tarski('#skF_4',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_388,c_382])).

tff(c_380,plain,(
    k2_relat_1('#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_378,c_378,c_10])).

tff(c_405,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_388,c_388,c_380])).

tff(c_426,plain,(
    ! [C_81] :
      ( ~ r1_tarski(k2_relat_1(C_81),'#skF_4')
      | k1_relat_1(C_81) != '#skF_4'
      | ~ v1_funct_1(C_81)
      | ~ v1_relat_1(C_81) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_388,c_34])).

tff(c_429,plain,
    ( ~ r1_tarski('#skF_4','#skF_4')
    | k1_relat_1('#skF_4') != '#skF_4'
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_405,c_426])).

tff(c_431,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_400,c_398,c_429])).

tff(c_432,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_431])).

tff(c_451,plain,(
    ! [A_88] :
      ( k1_relat_1(A_88) != '#skF_4'
      | A_88 = '#skF_4'
      | ~ v1_relat_1(A_88) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_379,c_379,c_16])).

tff(c_457,plain,(
    ! [A_7] :
      ( k1_relat_1('#skF_2'(A_7)) != '#skF_4'
      | '#skF_2'(A_7) = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_24,c_451])).

tff(c_462,plain,(
    ! [A_89] :
      ( A_89 != '#skF_4'
      | '#skF_2'(A_89) = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_457])).

tff(c_472,plain,(
    ! [A_89] :
      ( v1_relat_1('#skF_4')
      | A_89 != '#skF_4' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_462,c_24])).

tff(c_478,plain,(
    ! [A_89] : A_89 != '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_432,c_472])).

tff(c_491,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_478,c_405])).

tff(c_492,plain,(
    ~ v1_funct_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_431])).

tff(c_502,plain,(
    ! [A_90] :
      ( k1_relat_1(A_90) != '#skF_4'
      | A_90 = '#skF_4'
      | ~ v1_relat_1(A_90) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_379,c_379,c_16])).

tff(c_511,plain,(
    ! [A_7] :
      ( k1_relat_1('#skF_2'(A_7)) != '#skF_4'
      | '#skF_2'(A_7) = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_24,c_502])).

tff(c_520,plain,(
    ! [A_91] :
      ( A_91 != '#skF_4'
      | '#skF_2'(A_91) = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_511])).

tff(c_528,plain,(
    ! [A_91] :
      ( v1_funct_1('#skF_4')
      | A_91 != '#skF_4' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_520,c_22])).

tff(c_536,plain,(
    ! [A_91] : A_91 != '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_492,c_528])).

tff(c_549,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_536,c_405])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:26:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.34/1.28  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.34/1.29  
% 2.34/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.34/1.30  %$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_3 > #skF_5 > #skF_4
% 2.34/1.30  
% 2.34/1.30  %Foreground sorts:
% 2.34/1.30  
% 2.34/1.30  
% 2.34/1.30  %Background operators:
% 2.34/1.30  
% 2.34/1.30  
% 2.34/1.30  %Foreground operators:
% 2.34/1.30  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.34/1.30  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.34/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.34/1.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.34/1.30  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.34/1.30  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.34/1.30  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.34/1.30  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.34/1.30  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.34/1.30  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.34/1.30  tff('#skF_5', type, '#skF_5': $i).
% 2.34/1.30  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.34/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.34/1.30  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.34/1.30  tff('#skF_4', type, '#skF_4': $i).
% 2.34/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.34/1.30  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.34/1.30  
% 2.34/1.31  tff(f_93, negated_conjecture, ~(![A, B]: ~(~((A = k1_xboole_0) & ~(B = k1_xboole_0)) & (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => ~((B = k1_relat_1(C)) & r1_tarski(k2_relat_1(C), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_funct_1)).
% 2.34/1.31  tff(f_33, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.34/1.31  tff(f_75, axiom, (![A]: (~(A = k1_xboole_0) => (![B]: (?[C]: (((v1_relat_1(C) & v1_funct_1(C)) & (k1_relat_1(C) = A)) & (k2_relat_1(C) = k1_tarski(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t15_funct_1)).
% 2.34/1.31  tff(f_39, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 2.34/1.31  tff(f_42, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 2.34/1.31  tff(f_35, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.34/1.31  tff(f_62, axiom, (![A]: (?[B]: (((v1_relat_1(B) & v1_funct_1(B)) & (k1_relat_1(B) = A)) & (![C]: (r2_hidden(C, A) => (k1_funct_1(B, C) = k1_xboole_0)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', s3_funct_1__e2_25__funct_1)).
% 2.34/1.31  tff(f_50, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 2.34/1.31  tff(c_36, plain, (k1_xboole_0='#skF_5' | k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.34/1.31  tff(c_57, plain, (k1_xboole_0!='#skF_4'), inference(splitLeft, [status(thm)], [c_36])).
% 2.34/1.31  tff(c_2, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | k1_xboole_0=A_1)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.34/1.31  tff(c_28, plain, (![A_13, B_17]: (k1_relat_1('#skF_3'(A_13, B_17))=A_13 | k1_xboole_0=A_13)), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.34/1.31  tff(c_30, plain, (![A_13, B_17]: (v1_funct_1('#skF_3'(A_13, B_17)) | k1_xboole_0=A_13)), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.34/1.31  tff(c_32, plain, (![A_13, B_17]: (v1_relat_1('#skF_3'(A_13, B_17)) | k1_xboole_0=A_13)), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.34/1.31  tff(c_8, plain, (![A_4, B_5]: (r1_tarski(k1_tarski(A_4), B_5) | ~r2_hidden(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.34/1.31  tff(c_217, plain, (![A_46, B_47]: (k2_relat_1('#skF_3'(A_46, B_47))=k1_tarski(B_47) | k1_xboole_0=A_46)), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.34/1.31  tff(c_34, plain, (![C_20]: (~r1_tarski(k2_relat_1(C_20), '#skF_4') | k1_relat_1(C_20)!='#skF_5' | ~v1_funct_1(C_20) | ~v1_relat_1(C_20))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.34/1.31  tff(c_244, plain, (![B_56, A_57]: (~r1_tarski(k1_tarski(B_56), '#skF_4') | k1_relat_1('#skF_3'(A_57, B_56))!='#skF_5' | ~v1_funct_1('#skF_3'(A_57, B_56)) | ~v1_relat_1('#skF_3'(A_57, B_56)) | k1_xboole_0=A_57)), inference(superposition, [status(thm), theory('equality')], [c_217, c_34])).
% 2.34/1.31  tff(c_249, plain, (![A_58, A_59]: (k1_relat_1('#skF_3'(A_58, A_59))!='#skF_5' | ~v1_funct_1('#skF_3'(A_58, A_59)) | ~v1_relat_1('#skF_3'(A_58, A_59)) | k1_xboole_0=A_58 | ~r2_hidden(A_59, '#skF_4'))), inference(resolution, [status(thm)], [c_8, c_244])).
% 2.34/1.31  tff(c_254, plain, (![A_60, B_61]: (k1_relat_1('#skF_3'(A_60, B_61))!='#skF_5' | ~v1_funct_1('#skF_3'(A_60, B_61)) | ~r2_hidden(B_61, '#skF_4') | k1_xboole_0=A_60)), inference(resolution, [status(thm)], [c_32, c_249])).
% 2.34/1.31  tff(c_259, plain, (![A_62, B_63]: (k1_relat_1('#skF_3'(A_62, B_63))!='#skF_5' | ~r2_hidden(B_63, '#skF_4') | k1_xboole_0=A_62)), inference(resolution, [status(thm)], [c_30, c_254])).
% 2.34/1.31  tff(c_262, plain, (![A_13, B_17]: (A_13!='#skF_5' | ~r2_hidden(B_17, '#skF_4') | k1_xboole_0=A_13 | k1_xboole_0=A_13)), inference(superposition, [status(thm), theory('equality')], [c_28, c_259])).
% 2.34/1.31  tff(c_264, plain, (![B_64]: (~r2_hidden(B_64, '#skF_4'))), inference(splitLeft, [status(thm)], [c_262])).
% 2.34/1.31  tff(c_268, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_2, c_264])).
% 2.34/1.31  tff(c_272, plain, $false, inference(negUnitSimplification, [status(thm)], [c_57, c_268])).
% 2.34/1.31  tff(c_274, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_262])).
% 2.34/1.31  tff(c_12, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.34/1.31  tff(c_4, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.34/1.31  tff(c_10, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.34/1.31  tff(c_59, plain, (![C_26]: (~r1_tarski(k2_relat_1(C_26), '#skF_4') | k1_relat_1(C_26)!='#skF_5' | ~v1_funct_1(C_26) | ~v1_relat_1(C_26))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.34/1.31  tff(c_62, plain, (~r1_tarski(k1_xboole_0, '#skF_4') | k1_relat_1(k1_xboole_0)!='#skF_5' | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_10, c_59])).
% 2.34/1.31  tff(c_64, plain, (k1_xboole_0!='#skF_5' | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_4, c_62])).
% 2.34/1.31  tff(c_67, plain, (~v1_relat_1(k1_xboole_0)), inference(splitLeft, [status(thm)], [c_64])).
% 2.34/1.31  tff(c_20, plain, (![A_7]: (k1_relat_1('#skF_2'(A_7))=A_7)), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.34/1.31  tff(c_24, plain, (![A_7]: (v1_relat_1('#skF_2'(A_7)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.34/1.31  tff(c_68, plain, (![A_31]: (k1_relat_1(A_31)!=k1_xboole_0 | k1_xboole_0=A_31 | ~v1_relat_1(A_31))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.34/1.31  tff(c_74, plain, (![A_7]: (k1_relat_1('#skF_2'(A_7))!=k1_xboole_0 | '#skF_2'(A_7)=k1_xboole_0)), inference(resolution, [status(thm)], [c_24, c_68])).
% 2.34/1.31  tff(c_88, plain, (![A_33]: (k1_xboole_0!=A_33 | '#skF_2'(A_33)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_74])).
% 2.34/1.31  tff(c_98, plain, (![A_33]: (v1_relat_1(k1_xboole_0) | k1_xboole_0!=A_33)), inference(superposition, [status(thm), theory('equality')], [c_88, c_24])).
% 2.34/1.31  tff(c_104, plain, (![A_33]: (k1_xboole_0!=A_33)), inference(negUnitSimplification, [status(thm)], [c_67, c_98])).
% 2.34/1.31  tff(c_114, plain, $false, inference(negUnitSimplification, [status(thm)], [c_104, c_10])).
% 2.34/1.31  tff(c_115, plain, (~v1_funct_1(k1_xboole_0) | k1_xboole_0!='#skF_5'), inference(splitRight, [status(thm)], [c_64])).
% 2.34/1.31  tff(c_117, plain, (k1_xboole_0!='#skF_5'), inference(splitLeft, [status(thm)], [c_115])).
% 2.34/1.31  tff(c_299, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_274, c_117])).
% 2.34/1.31  tff(c_301, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_115])).
% 2.34/1.31  tff(c_300, plain, (~v1_funct_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_115])).
% 2.34/1.31  tff(c_303, plain, (~v1_funct_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_301, c_300])).
% 2.34/1.31  tff(c_16, plain, (![A_6]: (k1_relat_1(A_6)!=k1_xboole_0 | k1_xboole_0=A_6 | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.34/1.31  tff(c_333, plain, (![A_71]: (k1_relat_1(A_71)!='#skF_5' | A_71='#skF_5' | ~v1_relat_1(A_71))), inference(demodulation, [status(thm), theory('equality')], [c_301, c_301, c_16])).
% 2.34/1.31  tff(c_342, plain, (![A_7]: (k1_relat_1('#skF_2'(A_7))!='#skF_5' | '#skF_2'(A_7)='#skF_5')), inference(resolution, [status(thm)], [c_24, c_333])).
% 2.34/1.31  tff(c_351, plain, (![A_72]: (A_72!='#skF_5' | '#skF_2'(A_72)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_342])).
% 2.34/1.31  tff(c_22, plain, (![A_7]: (v1_funct_1('#skF_2'(A_7)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.34/1.31  tff(c_359, plain, (![A_72]: (v1_funct_1('#skF_5') | A_72!='#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_351, c_22])).
% 2.34/1.31  tff(c_367, plain, (![A_72]: (A_72!='#skF_5')), inference(negUnitSimplification, [status(thm)], [c_303, c_359])).
% 2.34/1.31  tff(c_309, plain, (k2_relat_1('#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_301, c_301, c_10])).
% 2.34/1.31  tff(c_377, plain, $false, inference(negUnitSimplification, [status(thm)], [c_367, c_309])).
% 2.34/1.31  tff(c_379, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_36])).
% 2.34/1.31  tff(c_378, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_36])).
% 2.34/1.31  tff(c_388, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_379, c_378])).
% 2.34/1.31  tff(c_381, plain, (k1_relat_1('#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_378, c_378, c_12])).
% 2.34/1.31  tff(c_400, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_388, c_388, c_381])).
% 2.34/1.31  tff(c_382, plain, (![A_3]: (r1_tarski('#skF_5', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_378, c_4])).
% 2.34/1.31  tff(c_398, plain, (![A_3]: (r1_tarski('#skF_4', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_388, c_382])).
% 2.34/1.31  tff(c_380, plain, (k2_relat_1('#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_378, c_378, c_10])).
% 2.34/1.31  tff(c_405, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_388, c_388, c_380])).
% 2.34/1.31  tff(c_426, plain, (![C_81]: (~r1_tarski(k2_relat_1(C_81), '#skF_4') | k1_relat_1(C_81)!='#skF_4' | ~v1_funct_1(C_81) | ~v1_relat_1(C_81))), inference(demodulation, [status(thm), theory('equality')], [c_388, c_34])).
% 2.34/1.31  tff(c_429, plain, (~r1_tarski('#skF_4', '#skF_4') | k1_relat_1('#skF_4')!='#skF_4' | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_405, c_426])).
% 2.34/1.31  tff(c_431, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_400, c_398, c_429])).
% 2.34/1.31  tff(c_432, plain, (~v1_relat_1('#skF_4')), inference(splitLeft, [status(thm)], [c_431])).
% 2.34/1.31  tff(c_451, plain, (![A_88]: (k1_relat_1(A_88)!='#skF_4' | A_88='#skF_4' | ~v1_relat_1(A_88))), inference(demodulation, [status(thm), theory('equality')], [c_379, c_379, c_16])).
% 2.34/1.31  tff(c_457, plain, (![A_7]: (k1_relat_1('#skF_2'(A_7))!='#skF_4' | '#skF_2'(A_7)='#skF_4')), inference(resolution, [status(thm)], [c_24, c_451])).
% 2.34/1.31  tff(c_462, plain, (![A_89]: (A_89!='#skF_4' | '#skF_2'(A_89)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_457])).
% 2.34/1.31  tff(c_472, plain, (![A_89]: (v1_relat_1('#skF_4') | A_89!='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_462, c_24])).
% 2.34/1.31  tff(c_478, plain, (![A_89]: (A_89!='#skF_4')), inference(negUnitSimplification, [status(thm)], [c_432, c_472])).
% 2.34/1.31  tff(c_491, plain, $false, inference(negUnitSimplification, [status(thm)], [c_478, c_405])).
% 2.34/1.31  tff(c_492, plain, (~v1_funct_1('#skF_4')), inference(splitRight, [status(thm)], [c_431])).
% 2.34/1.31  tff(c_502, plain, (![A_90]: (k1_relat_1(A_90)!='#skF_4' | A_90='#skF_4' | ~v1_relat_1(A_90))), inference(demodulation, [status(thm), theory('equality')], [c_379, c_379, c_16])).
% 2.34/1.31  tff(c_511, plain, (![A_7]: (k1_relat_1('#skF_2'(A_7))!='#skF_4' | '#skF_2'(A_7)='#skF_4')), inference(resolution, [status(thm)], [c_24, c_502])).
% 2.34/1.31  tff(c_520, plain, (![A_91]: (A_91!='#skF_4' | '#skF_2'(A_91)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_511])).
% 2.34/1.31  tff(c_528, plain, (![A_91]: (v1_funct_1('#skF_4') | A_91!='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_520, c_22])).
% 2.34/1.31  tff(c_536, plain, (![A_91]: (A_91!='#skF_4')), inference(negUnitSimplification, [status(thm)], [c_492, c_528])).
% 2.34/1.31  tff(c_549, plain, $false, inference(negUnitSimplification, [status(thm)], [c_536, c_405])).
% 2.34/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.34/1.31  
% 2.34/1.31  Inference rules
% 2.34/1.31  ----------------------
% 2.34/1.31  #Ref     : 0
% 2.34/1.31  #Sup     : 92
% 2.34/1.31  #Fact    : 0
% 2.34/1.31  #Define  : 0
% 2.34/1.31  #Split   : 6
% 2.34/1.31  #Chain   : 0
% 2.34/1.31  #Close   : 0
% 2.34/1.31  
% 2.34/1.31  Ordering : KBO
% 2.34/1.31  
% 2.34/1.31  Simplification rules
% 2.34/1.31  ----------------------
% 2.34/1.31  #Subsume      : 26
% 2.34/1.31  #Demod        : 98
% 2.34/1.31  #Tautology    : 57
% 2.34/1.31  #SimpNegUnit  : 50
% 2.34/1.31  #BackRed      : 68
% 2.34/1.31  
% 2.34/1.31  #Partial instantiations: 0
% 2.34/1.31  #Strategies tried      : 1
% 2.34/1.32  
% 2.34/1.32  Timing (in seconds)
% 2.34/1.32  ----------------------
% 2.34/1.32  Preprocessing        : 0.29
% 2.34/1.32  Parsing              : 0.15
% 2.34/1.32  CNF conversion       : 0.02
% 2.34/1.32  Main loop            : 0.26
% 2.34/1.32  Inferencing          : 0.10
% 2.34/1.32  Reduction            : 0.08
% 2.34/1.32  Demodulation         : 0.05
% 2.34/1.32  BG Simplification    : 0.02
% 2.34/1.32  Subsumption          : 0.04
% 2.34/1.32  Abstraction          : 0.01
% 2.34/1.32  MUC search           : 0.00
% 2.34/1.32  Cooper               : 0.00
% 2.34/1.32  Total                : 0.58
% 2.34/1.32  Index Insertion      : 0.00
% 2.34/1.32  Index Deletion       : 0.00
% 2.34/1.32  Index Matching       : 0.00
% 2.34/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
