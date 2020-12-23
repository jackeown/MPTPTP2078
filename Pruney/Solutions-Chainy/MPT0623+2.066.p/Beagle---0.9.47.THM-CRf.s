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
% DateTime   : Thu Dec  3 10:03:15 EST 2020

% Result     : Theorem 2.31s
% Output     : CNFRefutation 2.63s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 331 expanded)
%              Number of leaves         :   29 ( 117 expanded)
%              Depth                    :   11
%              Number of atoms          :  178 ( 808 expanded)
%              Number of equality atoms :   96 ( 449 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_101,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( ~ ( A = k1_xboole_0
              & B != k1_xboole_0 )
          & ! [C] :
              ( ( v1_relat_1(C)
                & v1_funct_1(C) )
             => ~ ( B = k1_relat_1(C)
                  & r1_tarski(k2_relat_1(C),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_funct_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
        <=> r2_hidden(C,B) )
     => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).

tff(f_44,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_47,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(f_83,axiom,(
    ! [A] :
      ( A != k1_xboole_0
     => ! [B] :
        ? [C] :
          ( v1_relat_1(C)
          & v1_funct_1(C)
          & k1_relat_1(C) = A
          & k2_relat_1(C) = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_funct_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_50,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_34,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_70,axiom,(
    ! [A] :
    ? [B] :
      ( v1_relat_1(B)
      & v1_funct_1(B)
      & k1_relat_1(B) = A
      & ! [C] :
          ( r2_hidden(C,A)
         => k1_funct_1(B,C) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e2_25__funct_1)).

tff(f_58,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

tff(c_50,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_71,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_330,plain,(
    ! [A_79,B_80] :
      ( r2_hidden('#skF_1'(A_79,B_80),B_80)
      | r2_hidden('#skF_2'(A_79,B_80),A_79)
      | B_80 = A_79 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_18,plain,(
    ! [A_7] : k2_zfmisc_1(A_7,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_100,plain,(
    ! [A_33,B_34] : ~ r2_hidden(A_33,k2_zfmisc_1(A_33,B_34)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_106,plain,(
    ! [A_7] : ~ r2_hidden(A_7,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_100])).

tff(c_352,plain,(
    ! [B_80] :
      ( r2_hidden('#skF_1'(k1_xboole_0,B_80),B_80)
      | k1_xboole_0 = B_80 ) ),
    inference(resolution,[status(thm)],[c_330,c_106])).

tff(c_42,plain,(
    ! [A_18,B_22] :
      ( k1_relat_1('#skF_4'(A_18,B_22)) = A_18
      | k1_xboole_0 = A_18 ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_44,plain,(
    ! [A_18,B_22] :
      ( v1_funct_1('#skF_4'(A_18,B_22))
      | k1_xboole_0 = A_18 ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_46,plain,(
    ! [A_18,B_22] :
      ( v1_relat_1('#skF_4'(A_18,B_22))
      | k1_xboole_0 = A_18 ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_14,plain,(
    ! [A_5,B_6] :
      ( r1_tarski(k1_tarski(A_5),B_6)
      | ~ r2_hidden(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_261,plain,(
    ! [A_57,B_58] :
      ( k2_relat_1('#skF_4'(A_57,B_58)) = k1_tarski(B_58)
      | k1_xboole_0 = A_57 ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_48,plain,(
    ! [C_25] :
      ( ~ r1_tarski(k2_relat_1(C_25),'#skF_5')
      | k1_relat_1(C_25) != '#skF_6'
      | ~ v1_funct_1(C_25)
      | ~ v1_relat_1(C_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_284,plain,(
    ! [B_61,A_62] :
      ( ~ r1_tarski(k1_tarski(B_61),'#skF_5')
      | k1_relat_1('#skF_4'(A_62,B_61)) != '#skF_6'
      | ~ v1_funct_1('#skF_4'(A_62,B_61))
      | ~ v1_relat_1('#skF_4'(A_62,B_61))
      | k1_xboole_0 = A_62 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_261,c_48])).

tff(c_353,plain,(
    ! [A_81,A_82] :
      ( k1_relat_1('#skF_4'(A_81,A_82)) != '#skF_6'
      | ~ v1_funct_1('#skF_4'(A_81,A_82))
      | ~ v1_relat_1('#skF_4'(A_81,A_82))
      | k1_xboole_0 = A_81
      | ~ r2_hidden(A_82,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_14,c_284])).

tff(c_373,plain,(
    ! [A_84,B_85] :
      ( k1_relat_1('#skF_4'(A_84,B_85)) != '#skF_6'
      | ~ v1_funct_1('#skF_4'(A_84,B_85))
      | ~ r2_hidden(B_85,'#skF_5')
      | k1_xboole_0 = A_84 ) ),
    inference(resolution,[status(thm)],[c_46,c_353])).

tff(c_378,plain,(
    ! [A_86,B_87] :
      ( k1_relat_1('#skF_4'(A_86,B_87)) != '#skF_6'
      | ~ r2_hidden(B_87,'#skF_5')
      | k1_xboole_0 = A_86 ) ),
    inference(resolution,[status(thm)],[c_44,c_373])).

tff(c_381,plain,(
    ! [A_18,B_22] :
      ( A_18 != '#skF_6'
      | ~ r2_hidden(B_22,'#skF_5')
      | k1_xboole_0 = A_18
      | k1_xboole_0 = A_18 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_378])).

tff(c_383,plain,(
    ! [B_88] : ~ r2_hidden(B_88,'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_381])).

tff(c_387,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_352,c_383])).

tff(c_401,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_71,c_387])).

tff(c_420,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_381])).

tff(c_26,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_10,plain,(
    ! [A_4] : r1_tarski(k1_xboole_0,A_4) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_24,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_79,plain,(
    ! [C_31] :
      ( ~ r1_tarski(k2_relat_1(C_31),'#skF_5')
      | k1_relat_1(C_31) != '#skF_6'
      | ~ v1_funct_1(C_31)
      | ~ v1_relat_1(C_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_82,plain,
    ( ~ r1_tarski(k1_xboole_0,'#skF_5')
    | k1_relat_1(k1_xboole_0) != '#skF_6'
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_79])).

tff(c_84,plain,
    ( k1_xboole_0 != '#skF_6'
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_10,c_82])).

tff(c_110,plain,(
    ~ v1_relat_1(k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_84])).

tff(c_34,plain,(
    ! [A_12] : k1_relat_1('#skF_3'(A_12)) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_38,plain,(
    ! [A_12] : v1_relat_1('#skF_3'(A_12)) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_131,plain,(
    ! [A_45] :
      ( k1_relat_1(A_45) != k1_xboole_0
      | k1_xboole_0 = A_45
      | ~ v1_relat_1(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_137,plain,(
    ! [A_12] :
      ( k1_relat_1('#skF_3'(A_12)) != k1_xboole_0
      | '#skF_3'(A_12) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_38,c_131])).

tff(c_142,plain,(
    ! [A_46] :
      ( k1_xboole_0 != A_46
      | '#skF_3'(A_46) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_137])).

tff(c_152,plain,(
    ! [A_46] :
      ( v1_relat_1(k1_xboole_0)
      | k1_xboole_0 != A_46 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_142,c_38])).

tff(c_158,plain,(
    ! [A_46] : k1_xboole_0 != A_46 ),
    inference(negUnitSimplification,[status(thm)],[c_110,c_152])).

tff(c_20,plain,(
    ! [B_8] : k2_zfmisc_1(k1_xboole_0,B_8) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_170,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_158,c_20])).

tff(c_171,plain,
    ( ~ v1_funct_1(k1_xboole_0)
    | k1_xboole_0 != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_183,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_171])).

tff(c_450,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_420,c_183])).

tff(c_452,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_171])).

tff(c_451,plain,(
    ~ v1_funct_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_171])).

tff(c_453,plain,(
    ~ v1_funct_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_452,c_451])).

tff(c_30,plain,(
    ! [A_11] :
      ( k1_relat_1(A_11) != k1_xboole_0
      | k1_xboole_0 = A_11
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_531,plain,(
    ! [A_102] :
      ( k1_relat_1(A_102) != '#skF_6'
      | A_102 = '#skF_6'
      | ~ v1_relat_1(A_102) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_452,c_452,c_30])).

tff(c_540,plain,(
    ! [A_12] :
      ( k1_relat_1('#skF_3'(A_12)) != '#skF_6'
      | '#skF_3'(A_12) = '#skF_6' ) ),
    inference(resolution,[status(thm)],[c_38,c_531])).

tff(c_549,plain,(
    ! [A_103] :
      ( A_103 != '#skF_6'
      | '#skF_3'(A_103) = '#skF_6' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_540])).

tff(c_36,plain,(
    ! [A_12] : v1_funct_1('#skF_3'(A_12)) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_557,plain,(
    ! [A_103] :
      ( v1_funct_1('#skF_6')
      | A_103 != '#skF_6' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_549,c_36])).

tff(c_565,plain,(
    ! [A_103] : A_103 != '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_453,c_557])).

tff(c_459,plain,(
    ! [B_8] : k2_zfmisc_1('#skF_6',B_8) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_452,c_452,c_20])).

tff(c_578,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_565,c_459])).

tff(c_579,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_583,plain,(
    ! [A_4] : r1_tarski('#skF_6',A_4) ),
    inference(demodulation,[status(thm),theory(equality)],[c_579,c_10])).

tff(c_582,plain,(
    k1_relat_1('#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_579,c_579,c_26])).

tff(c_581,plain,(
    k2_relat_1('#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_579,c_579,c_24])).

tff(c_580,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_588,plain,(
    '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_579,c_580])).

tff(c_602,plain,(
    ! [C_104] :
      ( ~ r1_tarski(k2_relat_1(C_104),'#skF_6')
      | k1_relat_1(C_104) != '#skF_6'
      | ~ v1_funct_1(C_104)
      | ~ v1_relat_1(C_104) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_588,c_48])).

tff(c_605,plain,
    ( ~ r1_tarski('#skF_6','#skF_6')
    | k1_relat_1('#skF_6') != '#skF_6'
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_581,c_602])).

tff(c_607,plain,
    ( ~ r1_tarski('#skF_6','#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_582,c_605])).

tff(c_647,plain,
    ( ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_583,c_607])).

tff(c_648,plain,(
    ~ v1_relat_1('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_647])).

tff(c_671,plain,(
    ! [A_120] :
      ( k1_relat_1(A_120) != '#skF_6'
      | A_120 = '#skF_6'
      | ~ v1_relat_1(A_120) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_579,c_579,c_30])).

tff(c_677,plain,(
    ! [A_12] :
      ( k1_relat_1('#skF_3'(A_12)) != '#skF_6'
      | '#skF_3'(A_12) = '#skF_6' ) ),
    inference(resolution,[status(thm)],[c_38,c_671])).

tff(c_682,plain,(
    ! [A_121] :
      ( A_121 != '#skF_6'
      | '#skF_3'(A_121) = '#skF_6' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_677])).

tff(c_692,plain,(
    ! [A_121] :
      ( v1_relat_1('#skF_6')
      | A_121 != '#skF_6' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_682,c_38])).

tff(c_698,plain,(
    ! [A_121] : A_121 != '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_648,c_692])).

tff(c_617,plain,(
    ! [A_7] : k2_zfmisc_1(A_7,'#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_579,c_579,c_18])).

tff(c_717,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_698,c_617])).

tff(c_718,plain,(
    ~ v1_funct_1('#skF_6') ),
    inference(splitRight,[status(thm)],[c_647])).

tff(c_737,plain,(
    ! [A_128] :
      ( k1_relat_1(A_128) != '#skF_6'
      | A_128 = '#skF_6'
      | ~ v1_relat_1(A_128) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_579,c_579,c_30])).

tff(c_746,plain,(
    ! [A_12] :
      ( k1_relat_1('#skF_3'(A_12)) != '#skF_6'
      | '#skF_3'(A_12) = '#skF_6' ) ),
    inference(resolution,[status(thm)],[c_38,c_737])).

tff(c_755,plain,(
    ! [A_129] :
      ( A_129 != '#skF_6'
      | '#skF_3'(A_129) = '#skF_6' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_746])).

tff(c_763,plain,(
    ! [A_129] :
      ( v1_funct_1('#skF_6')
      | A_129 != '#skF_6' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_755,c_36])).

tff(c_771,plain,(
    ! [A_129] : A_129 != '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_718,c_763])).

tff(c_785,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_771,c_617])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:49:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.31/1.32  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.63/1.33  
% 2.63/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.63/1.33  %$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_1 > #skF_4
% 2.63/1.33  
% 2.63/1.33  %Foreground sorts:
% 2.63/1.33  
% 2.63/1.33  
% 2.63/1.33  %Background operators:
% 2.63/1.33  
% 2.63/1.33  
% 2.63/1.33  %Foreground operators:
% 2.63/1.33  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.63/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.63/1.33  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.63/1.33  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.63/1.33  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.63/1.33  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.63/1.33  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.63/1.33  tff('#skF_5', type, '#skF_5': $i).
% 2.63/1.33  tff('#skF_6', type, '#skF_6': $i).
% 2.63/1.33  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.63/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.63/1.33  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.63/1.33  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.63/1.33  tff('#skF_3', type, '#skF_3': $i > $i).
% 2.63/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.63/1.33  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.63/1.33  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.63/1.33  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.63/1.33  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.63/1.33  
% 2.63/1.35  tff(f_101, negated_conjecture, ~(![A, B]: ~(~((A = k1_xboole_0) & ~(B = k1_xboole_0)) & (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => ~((B = k1_relat_1(C)) & r1_tarski(k2_relat_1(C), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_funct_1)).
% 2.63/1.35  tff(f_32, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) <=> r2_hidden(C, B))) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tarski)).
% 2.63/1.35  tff(f_44, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.63/1.35  tff(f_47, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 2.63/1.35  tff(f_83, axiom, (![A]: (~(A = k1_xboole_0) => (![B]: (?[C]: (((v1_relat_1(C) & v1_funct_1(C)) & (k1_relat_1(C) = A)) & (k2_relat_1(C) = k1_tarski(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t15_funct_1)).
% 2.63/1.35  tff(f_38, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 2.63/1.35  tff(f_50, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 2.63/1.35  tff(f_34, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.63/1.35  tff(f_70, axiom, (![A]: (?[B]: (((v1_relat_1(B) & v1_funct_1(B)) & (k1_relat_1(B) = A)) & (![C]: (r2_hidden(C, A) => (k1_funct_1(B, C) = k1_xboole_0)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', s3_funct_1__e2_25__funct_1)).
% 2.63/1.35  tff(f_58, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 2.63/1.35  tff(c_50, plain, (k1_xboole_0='#skF_6' | k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.63/1.35  tff(c_71, plain, (k1_xboole_0!='#skF_5'), inference(splitLeft, [status(thm)], [c_50])).
% 2.63/1.35  tff(c_330, plain, (![A_79, B_80]: (r2_hidden('#skF_1'(A_79, B_80), B_80) | r2_hidden('#skF_2'(A_79, B_80), A_79) | B_80=A_79)), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.63/1.35  tff(c_18, plain, (![A_7]: (k2_zfmisc_1(A_7, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.63/1.35  tff(c_100, plain, (![A_33, B_34]: (~r2_hidden(A_33, k2_zfmisc_1(A_33, B_34)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.63/1.35  tff(c_106, plain, (![A_7]: (~r2_hidden(A_7, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_18, c_100])).
% 2.63/1.35  tff(c_352, plain, (![B_80]: (r2_hidden('#skF_1'(k1_xboole_0, B_80), B_80) | k1_xboole_0=B_80)), inference(resolution, [status(thm)], [c_330, c_106])).
% 2.63/1.35  tff(c_42, plain, (![A_18, B_22]: (k1_relat_1('#skF_4'(A_18, B_22))=A_18 | k1_xboole_0=A_18)), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.63/1.35  tff(c_44, plain, (![A_18, B_22]: (v1_funct_1('#skF_4'(A_18, B_22)) | k1_xboole_0=A_18)), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.63/1.35  tff(c_46, plain, (![A_18, B_22]: (v1_relat_1('#skF_4'(A_18, B_22)) | k1_xboole_0=A_18)), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.63/1.35  tff(c_14, plain, (![A_5, B_6]: (r1_tarski(k1_tarski(A_5), B_6) | ~r2_hidden(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.63/1.35  tff(c_261, plain, (![A_57, B_58]: (k2_relat_1('#skF_4'(A_57, B_58))=k1_tarski(B_58) | k1_xboole_0=A_57)), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.63/1.35  tff(c_48, plain, (![C_25]: (~r1_tarski(k2_relat_1(C_25), '#skF_5') | k1_relat_1(C_25)!='#skF_6' | ~v1_funct_1(C_25) | ~v1_relat_1(C_25))), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.63/1.35  tff(c_284, plain, (![B_61, A_62]: (~r1_tarski(k1_tarski(B_61), '#skF_5') | k1_relat_1('#skF_4'(A_62, B_61))!='#skF_6' | ~v1_funct_1('#skF_4'(A_62, B_61)) | ~v1_relat_1('#skF_4'(A_62, B_61)) | k1_xboole_0=A_62)), inference(superposition, [status(thm), theory('equality')], [c_261, c_48])).
% 2.63/1.35  tff(c_353, plain, (![A_81, A_82]: (k1_relat_1('#skF_4'(A_81, A_82))!='#skF_6' | ~v1_funct_1('#skF_4'(A_81, A_82)) | ~v1_relat_1('#skF_4'(A_81, A_82)) | k1_xboole_0=A_81 | ~r2_hidden(A_82, '#skF_5'))), inference(resolution, [status(thm)], [c_14, c_284])).
% 2.63/1.35  tff(c_373, plain, (![A_84, B_85]: (k1_relat_1('#skF_4'(A_84, B_85))!='#skF_6' | ~v1_funct_1('#skF_4'(A_84, B_85)) | ~r2_hidden(B_85, '#skF_5') | k1_xboole_0=A_84)), inference(resolution, [status(thm)], [c_46, c_353])).
% 2.63/1.35  tff(c_378, plain, (![A_86, B_87]: (k1_relat_1('#skF_4'(A_86, B_87))!='#skF_6' | ~r2_hidden(B_87, '#skF_5') | k1_xboole_0=A_86)), inference(resolution, [status(thm)], [c_44, c_373])).
% 2.63/1.35  tff(c_381, plain, (![A_18, B_22]: (A_18!='#skF_6' | ~r2_hidden(B_22, '#skF_5') | k1_xboole_0=A_18 | k1_xboole_0=A_18)), inference(superposition, [status(thm), theory('equality')], [c_42, c_378])).
% 2.63/1.35  tff(c_383, plain, (![B_88]: (~r2_hidden(B_88, '#skF_5'))), inference(splitLeft, [status(thm)], [c_381])).
% 2.63/1.35  tff(c_387, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_352, c_383])).
% 2.63/1.35  tff(c_401, plain, $false, inference(negUnitSimplification, [status(thm)], [c_71, c_387])).
% 2.63/1.35  tff(c_420, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_381])).
% 2.63/1.35  tff(c_26, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.63/1.35  tff(c_10, plain, (![A_4]: (r1_tarski(k1_xboole_0, A_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.63/1.35  tff(c_24, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.63/1.35  tff(c_79, plain, (![C_31]: (~r1_tarski(k2_relat_1(C_31), '#skF_5') | k1_relat_1(C_31)!='#skF_6' | ~v1_funct_1(C_31) | ~v1_relat_1(C_31))), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.63/1.35  tff(c_82, plain, (~r1_tarski(k1_xboole_0, '#skF_5') | k1_relat_1(k1_xboole_0)!='#skF_6' | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_24, c_79])).
% 2.63/1.35  tff(c_84, plain, (k1_xboole_0!='#skF_6' | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_26, c_10, c_82])).
% 2.63/1.35  tff(c_110, plain, (~v1_relat_1(k1_xboole_0)), inference(splitLeft, [status(thm)], [c_84])).
% 2.63/1.35  tff(c_34, plain, (![A_12]: (k1_relat_1('#skF_3'(A_12))=A_12)), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.63/1.35  tff(c_38, plain, (![A_12]: (v1_relat_1('#skF_3'(A_12)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.63/1.35  tff(c_131, plain, (![A_45]: (k1_relat_1(A_45)!=k1_xboole_0 | k1_xboole_0=A_45 | ~v1_relat_1(A_45))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.63/1.35  tff(c_137, plain, (![A_12]: (k1_relat_1('#skF_3'(A_12))!=k1_xboole_0 | '#skF_3'(A_12)=k1_xboole_0)), inference(resolution, [status(thm)], [c_38, c_131])).
% 2.63/1.35  tff(c_142, plain, (![A_46]: (k1_xboole_0!=A_46 | '#skF_3'(A_46)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_34, c_137])).
% 2.63/1.35  tff(c_152, plain, (![A_46]: (v1_relat_1(k1_xboole_0) | k1_xboole_0!=A_46)), inference(superposition, [status(thm), theory('equality')], [c_142, c_38])).
% 2.63/1.35  tff(c_158, plain, (![A_46]: (k1_xboole_0!=A_46)), inference(negUnitSimplification, [status(thm)], [c_110, c_152])).
% 2.63/1.35  tff(c_20, plain, (![B_8]: (k2_zfmisc_1(k1_xboole_0, B_8)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.63/1.35  tff(c_170, plain, $false, inference(negUnitSimplification, [status(thm)], [c_158, c_20])).
% 2.63/1.35  tff(c_171, plain, (~v1_funct_1(k1_xboole_0) | k1_xboole_0!='#skF_6'), inference(splitRight, [status(thm)], [c_84])).
% 2.63/1.35  tff(c_183, plain, (k1_xboole_0!='#skF_6'), inference(splitLeft, [status(thm)], [c_171])).
% 2.63/1.35  tff(c_450, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_420, c_183])).
% 2.63/1.35  tff(c_452, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_171])).
% 2.63/1.35  tff(c_451, plain, (~v1_funct_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_171])).
% 2.63/1.35  tff(c_453, plain, (~v1_funct_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_452, c_451])).
% 2.63/1.35  tff(c_30, plain, (![A_11]: (k1_relat_1(A_11)!=k1_xboole_0 | k1_xboole_0=A_11 | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.63/1.35  tff(c_531, plain, (![A_102]: (k1_relat_1(A_102)!='#skF_6' | A_102='#skF_6' | ~v1_relat_1(A_102))), inference(demodulation, [status(thm), theory('equality')], [c_452, c_452, c_30])).
% 2.63/1.35  tff(c_540, plain, (![A_12]: (k1_relat_1('#skF_3'(A_12))!='#skF_6' | '#skF_3'(A_12)='#skF_6')), inference(resolution, [status(thm)], [c_38, c_531])).
% 2.63/1.35  tff(c_549, plain, (![A_103]: (A_103!='#skF_6' | '#skF_3'(A_103)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_540])).
% 2.63/1.35  tff(c_36, plain, (![A_12]: (v1_funct_1('#skF_3'(A_12)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.63/1.35  tff(c_557, plain, (![A_103]: (v1_funct_1('#skF_6') | A_103!='#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_549, c_36])).
% 2.63/1.35  tff(c_565, plain, (![A_103]: (A_103!='#skF_6')), inference(negUnitSimplification, [status(thm)], [c_453, c_557])).
% 2.63/1.35  tff(c_459, plain, (![B_8]: (k2_zfmisc_1('#skF_6', B_8)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_452, c_452, c_20])).
% 2.63/1.35  tff(c_578, plain, $false, inference(negUnitSimplification, [status(thm)], [c_565, c_459])).
% 2.63/1.35  tff(c_579, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_50])).
% 2.63/1.35  tff(c_583, plain, (![A_4]: (r1_tarski('#skF_6', A_4))), inference(demodulation, [status(thm), theory('equality')], [c_579, c_10])).
% 2.63/1.35  tff(c_582, plain, (k1_relat_1('#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_579, c_579, c_26])).
% 2.63/1.35  tff(c_581, plain, (k2_relat_1('#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_579, c_579, c_24])).
% 2.63/1.35  tff(c_580, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_50])).
% 2.63/1.35  tff(c_588, plain, ('#skF_5'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_579, c_580])).
% 2.63/1.35  tff(c_602, plain, (![C_104]: (~r1_tarski(k2_relat_1(C_104), '#skF_6') | k1_relat_1(C_104)!='#skF_6' | ~v1_funct_1(C_104) | ~v1_relat_1(C_104))), inference(demodulation, [status(thm), theory('equality')], [c_588, c_48])).
% 2.63/1.35  tff(c_605, plain, (~r1_tarski('#skF_6', '#skF_6') | k1_relat_1('#skF_6')!='#skF_6' | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_581, c_602])).
% 2.63/1.35  tff(c_607, plain, (~r1_tarski('#skF_6', '#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_582, c_605])).
% 2.63/1.35  tff(c_647, plain, (~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_583, c_607])).
% 2.63/1.35  tff(c_648, plain, (~v1_relat_1('#skF_6')), inference(splitLeft, [status(thm)], [c_647])).
% 2.63/1.35  tff(c_671, plain, (![A_120]: (k1_relat_1(A_120)!='#skF_6' | A_120='#skF_6' | ~v1_relat_1(A_120))), inference(demodulation, [status(thm), theory('equality')], [c_579, c_579, c_30])).
% 2.63/1.35  tff(c_677, plain, (![A_12]: (k1_relat_1('#skF_3'(A_12))!='#skF_6' | '#skF_3'(A_12)='#skF_6')), inference(resolution, [status(thm)], [c_38, c_671])).
% 2.63/1.35  tff(c_682, plain, (![A_121]: (A_121!='#skF_6' | '#skF_3'(A_121)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_677])).
% 2.63/1.35  tff(c_692, plain, (![A_121]: (v1_relat_1('#skF_6') | A_121!='#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_682, c_38])).
% 2.63/1.35  tff(c_698, plain, (![A_121]: (A_121!='#skF_6')), inference(negUnitSimplification, [status(thm)], [c_648, c_692])).
% 2.63/1.35  tff(c_617, plain, (![A_7]: (k2_zfmisc_1(A_7, '#skF_6')='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_579, c_579, c_18])).
% 2.63/1.35  tff(c_717, plain, $false, inference(negUnitSimplification, [status(thm)], [c_698, c_617])).
% 2.63/1.35  tff(c_718, plain, (~v1_funct_1('#skF_6')), inference(splitRight, [status(thm)], [c_647])).
% 2.63/1.35  tff(c_737, plain, (![A_128]: (k1_relat_1(A_128)!='#skF_6' | A_128='#skF_6' | ~v1_relat_1(A_128))), inference(demodulation, [status(thm), theory('equality')], [c_579, c_579, c_30])).
% 2.63/1.35  tff(c_746, plain, (![A_12]: (k1_relat_1('#skF_3'(A_12))!='#skF_6' | '#skF_3'(A_12)='#skF_6')), inference(resolution, [status(thm)], [c_38, c_737])).
% 2.63/1.35  tff(c_755, plain, (![A_129]: (A_129!='#skF_6' | '#skF_3'(A_129)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_746])).
% 2.63/1.35  tff(c_763, plain, (![A_129]: (v1_funct_1('#skF_6') | A_129!='#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_755, c_36])).
% 2.63/1.35  tff(c_771, plain, (![A_129]: (A_129!='#skF_6')), inference(negUnitSimplification, [status(thm)], [c_718, c_763])).
% 2.63/1.35  tff(c_785, plain, $false, inference(negUnitSimplification, [status(thm)], [c_771, c_617])).
% 2.63/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.63/1.35  
% 2.63/1.35  Inference rules
% 2.63/1.35  ----------------------
% 2.63/1.35  #Ref     : 0
% 2.63/1.35  #Sup     : 137
% 2.63/1.35  #Fact    : 0
% 2.63/1.35  #Define  : 0
% 2.63/1.35  #Split   : 6
% 2.63/1.35  #Chain   : 0
% 2.63/1.35  #Close   : 0
% 2.63/1.35  
% 2.63/1.35  Ordering : KBO
% 2.63/1.35  
% 2.63/1.35  Simplification rules
% 2.63/1.35  ----------------------
% 2.63/1.35  #Subsume      : 31
% 2.63/1.35  #Demod        : 116
% 2.63/1.35  #Tautology    : 85
% 2.63/1.35  #SimpNegUnit  : 57
% 2.63/1.35  #BackRed      : 82
% 2.63/1.35  
% 2.63/1.35  #Partial instantiations: 0
% 2.63/1.35  #Strategies tried      : 1
% 2.63/1.35  
% 2.63/1.35  Timing (in seconds)
% 2.63/1.35  ----------------------
% 2.63/1.36  Preprocessing        : 0.30
% 2.63/1.36  Parsing              : 0.15
% 2.63/1.36  CNF conversion       : 0.02
% 2.63/1.36  Main loop            : 0.30
% 2.63/1.36  Inferencing          : 0.11
% 2.63/1.36  Reduction            : 0.09
% 2.63/1.36  Demodulation         : 0.06
% 2.63/1.36  BG Simplification    : 0.02
% 2.63/1.36  Subsumption          : 0.05
% 2.63/1.36  Abstraction          : 0.01
% 2.63/1.36  MUC search           : 0.00
% 2.63/1.36  Cooper               : 0.00
% 2.63/1.36  Total                : 0.63
% 2.63/1.36  Index Insertion      : 0.00
% 2.63/1.36  Index Deletion       : 0.00
% 2.63/1.36  Index Matching       : 0.00
% 2.63/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
