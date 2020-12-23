%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:12 EST 2020

% Result     : Theorem 7.94s
% Output     : CNFRefutation 7.94s
% Verified   : 
% Statistics : Number of formulae       :  129 ( 590 expanded)
%              Number of leaves         :   30 ( 196 expanded)
%              Depth                    :   15
%              Number of atoms          :  237 (1525 expanded)
%              Number of equality atoms :  125 ( 838 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_3 > #skF_9 > #skF_8 > #skF_2 > #skF_7 > #skF_1 > #skF_5 > #skF_6 > #skF_4

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_6',type,(
    '#skF_6': $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_102,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( ~ ( A = k1_xboole_0
              & B != k1_xboole_0 )
          & ! [C] :
              ( ( v1_relat_1(C)
                & v1_funct_1(C) )
             => ~ ( B = k1_relat_1(C)
                  & r1_tarski(k2_relat_1(C),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_funct_1)).

tff(f_41,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
        <=> r2_hidden(C,B) )
     => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_48,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_84,axiom,(
    ! [A] :
      ( A != k1_xboole_0
     => ! [B] :
        ? [C] :
          ( v1_relat_1(C)
          & v1_funct_1(C)
          & k1_relat_1(C) = A
          & k2_relat_1(C) = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_funct_1)).

tff(f_51,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_71,axiom,(
    ! [A] :
    ? [B] :
      ( v1_relat_1(B)
      & v1_funct_1(B)
      & k1_relat_1(B) = A
      & ! [C] :
          ( r2_hidden(C,A)
         => k1_funct_1(B,C) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e2_25__funct_1)).

tff(f_59,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(c_56,plain,
    ( k1_xboole_0 = '#skF_9'
    | k1_xboole_0 != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_77,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_16,plain,(
    ! [A_9] : r1_tarski(k1_xboole_0,A_9) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_440,plain,(
    ! [A_103,B_104] :
      ( r2_hidden('#skF_2'(A_103,B_104),B_104)
      | r2_hidden('#skF_3'(A_103,B_104),A_103)
      | B_104 = A_103 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_8265,plain,(
    ! [A_2272,B_2273,B_2274] :
      ( r2_hidden('#skF_3'(A_2272,B_2273),B_2274)
      | ~ r1_tarski(A_2272,B_2274)
      | r2_hidden('#skF_2'(A_2272,B_2273),B_2273)
      | B_2273 = A_2272 ) ),
    inference(resolution,[status(thm)],[c_440,c_2])).

tff(c_18,plain,(
    ! [C_14,A_10] :
      ( C_14 = A_10
      | ~ r2_hidden(C_14,k1_tarski(A_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_9438,plain,(
    ! [A_3600,A_3601,B_3602] :
      ( A_3600 = '#skF_3'(A_3601,B_3602)
      | ~ r1_tarski(A_3601,k1_tarski(A_3600))
      | r2_hidden('#skF_2'(A_3601,B_3602),B_3602)
      | B_3602 = A_3601 ) ),
    inference(resolution,[status(thm)],[c_8265,c_18])).

tff(c_9791,plain,(
    ! [XT_3862,B_3604] :
      ( k1_relat_1(XT_3862) = '#skF_3'(k1_xboole_0,B_3604)
      | r2_hidden('#skF_2'(k1_xboole_0,B_3604),B_3604)
      | k1_xboole_0 = B_3604 ) ),
    inference(resolution,[status(thm)],[c_16,c_9438])).

tff(c_470,plain,(
    ! [A_103,B_104,B_2] :
      ( r2_hidden('#skF_3'(A_103,B_104),B_2)
      | ~ r1_tarski(A_103,B_2)
      | r2_hidden('#skF_2'(A_103,B_104),B_104)
      | B_104 = A_103 ) ),
    inference(resolution,[status(thm)],[c_440,c_2])).

tff(c_9794,plain,(
    ! [XT_3862,B_2,B_3604] :
      ( r2_hidden(k1_relat_1(XT_3862),B_2)
      | ~ r1_tarski(k1_xboole_0,B_2)
      | r2_hidden('#skF_2'(k1_xboole_0,B_3604),B_3604)
      | k1_xboole_0 = B_3604
      | r2_hidden('#skF_2'(k1_xboole_0,B_3604),B_3604)
      | k1_xboole_0 = B_3604 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9791,c_470])).

tff(c_10349,plain,(
    ! [XT_3862,B_2,B_3604] :
      ( r2_hidden(k1_relat_1(XT_3862),B_2)
      | r2_hidden('#skF_2'(k1_xboole_0,B_3604),B_3604)
      | k1_xboole_0 = B_3604 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_9794])).

tff(c_10438,plain,(
    ! [B_3604] :
      ( r2_hidden('#skF_2'(k1_xboole_0,B_3604),B_3604)
      | k1_xboole_0 = B_3604 ) ),
    inference(splitLeft,[status(thm)],[c_10349])).

tff(c_48,plain,(
    ! [A_22,B_26] :
      ( k1_relat_1('#skF_7'(A_22,B_26)) = A_22
      | k1_xboole_0 = A_22 ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_50,plain,(
    ! [A_22,B_26] :
      ( v1_funct_1('#skF_7'(A_22,B_26))
      | k1_xboole_0 = A_22 ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_52,plain,(
    ! [A_22,B_26] :
      ( v1_relat_1('#skF_7'(A_22,B_26))
      | k1_xboole_0 = A_22 ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_249,plain,(
    ! [A_54,B_55] :
      ( r2_hidden('#skF_1'(A_54,B_55),A_54)
      | r1_tarski(A_54,B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_254,plain,(
    ! [A_10,B_55] :
      ( '#skF_1'(k1_tarski(A_10),B_55) = A_10
      | r1_tarski(k1_tarski(A_10),B_55) ) ),
    inference(resolution,[status(thm)],[c_249,c_18])).

tff(c_256,plain,(
    ! [A_56,B_57] :
      ( k2_relat_1('#skF_7'(A_56,B_57)) = k1_tarski(B_57)
      | k1_xboole_0 = A_56 ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_54,plain,(
    ! [C_29] :
      ( ~ r1_tarski(k2_relat_1(C_29),'#skF_8')
      | k1_relat_1(C_29) != '#skF_9'
      | ~ v1_funct_1(C_29)
      | ~ v1_relat_1(C_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_294,plain,(
    ! [B_68,A_69] :
      ( ~ r1_tarski(k1_tarski(B_68),'#skF_8')
      | k1_relat_1('#skF_7'(A_69,B_68)) != '#skF_9'
      | ~ v1_funct_1('#skF_7'(A_69,B_68))
      | ~ v1_relat_1('#skF_7'(A_69,B_68))
      | k1_xboole_0 = A_69 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_256,c_54])).

tff(c_391,plain,(
    ! [A_89,A_90] :
      ( k1_relat_1('#skF_7'(A_89,A_90)) != '#skF_9'
      | ~ v1_funct_1('#skF_7'(A_89,A_90))
      | ~ v1_relat_1('#skF_7'(A_89,A_90))
      | k1_xboole_0 = A_89
      | '#skF_1'(k1_tarski(A_90),'#skF_8') = A_90 ) ),
    inference(resolution,[status(thm)],[c_254,c_294])).

tff(c_508,plain,(
    ! [A_109,B_110] :
      ( k1_relat_1('#skF_7'(A_109,B_110)) != '#skF_9'
      | ~ v1_funct_1('#skF_7'(A_109,B_110))
      | '#skF_1'(k1_tarski(B_110),'#skF_8') = B_110
      | k1_xboole_0 = A_109 ) ),
    inference(resolution,[status(thm)],[c_52,c_391])).

tff(c_513,plain,(
    ! [A_111,B_112] :
      ( k1_relat_1('#skF_7'(A_111,B_112)) != '#skF_9'
      | '#skF_1'(k1_tarski(B_112),'#skF_8') = B_112
      | k1_xboole_0 = A_111 ) ),
    inference(resolution,[status(thm)],[c_50,c_508])).

tff(c_516,plain,(
    ! [A_22,B_26] :
      ( A_22 != '#skF_9'
      | '#skF_1'(k1_tarski(B_26),'#skF_8') = B_26
      | k1_xboole_0 = A_22
      | k1_xboole_0 = A_22 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_513])).

tff(c_518,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_516])).

tff(c_32,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_30,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_79,plain,(
    ! [C_35] :
      ( ~ r1_tarski(k2_relat_1(C_35),'#skF_8')
      | k1_relat_1(C_35) != '#skF_9'
      | ~ v1_funct_1(C_35)
      | ~ v1_relat_1(C_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_82,plain,
    ( ~ r1_tarski(k1_xboole_0,'#skF_8')
    | k1_relat_1(k1_xboole_0) != '#skF_9'
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_79])).

tff(c_84,plain,
    ( k1_xboole_0 != '#skF_9'
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_16,c_82])).

tff(c_93,plain,(
    ~ v1_relat_1(k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_84])).

tff(c_40,plain,(
    ! [A_16] : k1_relat_1('#skF_6'(A_16)) = A_16 ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_44,plain,(
    ! [A_16] : v1_relat_1('#skF_6'(A_16)) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_103,plain,(
    ! [A_43] :
      ( k1_relat_1(A_43) != k1_xboole_0
      | k1_xboole_0 = A_43
      | ~ v1_relat_1(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_109,plain,(
    ! [A_16] :
      ( k1_relat_1('#skF_6'(A_16)) != k1_xboole_0
      | '#skF_6'(A_16) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_44,c_103])).

tff(c_114,plain,(
    ! [A_44] :
      ( k1_xboole_0 != A_44
      | '#skF_6'(A_44) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_109])).

tff(c_124,plain,(
    ! [A_44] :
      ( v1_relat_1(k1_xboole_0)
      | k1_xboole_0 != A_44 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_114,c_44])).

tff(c_130,plain,(
    ! [A_44] : k1_xboole_0 != A_44 ),
    inference(negUnitSimplification,[status(thm)],[c_93,c_124])).

tff(c_139,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_130,c_30])).

tff(c_140,plain,
    ( ~ v1_funct_1(k1_xboole_0)
    | k1_xboole_0 != '#skF_9' ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_142,plain,(
    k1_xboole_0 != '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_140])).

tff(c_544,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_518,c_142])).

tff(c_547,plain,(
    ! [B_113] : '#skF_1'(k1_tarski(B_113),'#skF_8') = B_113 ),
    inference(splitRight,[status(thm)],[c_516])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_578,plain,(
    ! [B_114] :
      ( ~ r2_hidden(B_114,'#skF_8')
      | r1_tarski(k1_tarski(B_114),'#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_547,c_4])).

tff(c_262,plain,(
    ! [B_57,A_56] :
      ( ~ r1_tarski(k1_tarski(B_57),'#skF_8')
      | k1_relat_1('#skF_7'(A_56,B_57)) != '#skF_9'
      | ~ v1_funct_1('#skF_7'(A_56,B_57))
      | ~ v1_relat_1('#skF_7'(A_56,B_57))
      | k1_xboole_0 = A_56 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_256,c_54])).

tff(c_659,plain,(
    ! [A_126,B_127] :
      ( k1_relat_1('#skF_7'(A_126,B_127)) != '#skF_9'
      | ~ v1_funct_1('#skF_7'(A_126,B_127))
      | ~ v1_relat_1('#skF_7'(A_126,B_127))
      | k1_xboole_0 = A_126
      | ~ r2_hidden(B_127,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_578,c_262])).

tff(c_22527,plain,(
    ! [A_9558,B_9559] :
      ( k1_relat_1('#skF_7'(A_9558,B_9559)) != '#skF_9'
      | ~ v1_funct_1('#skF_7'(A_9558,B_9559))
      | ~ r2_hidden(B_9559,'#skF_8')
      | k1_xboole_0 = A_9558 ) ),
    inference(resolution,[status(thm)],[c_52,c_659])).

tff(c_22532,plain,(
    ! [A_9560,B_9561] :
      ( k1_relat_1('#skF_7'(A_9560,B_9561)) != '#skF_9'
      | ~ r2_hidden(B_9561,'#skF_8')
      | k1_xboole_0 = A_9560 ) ),
    inference(resolution,[status(thm)],[c_50,c_22527])).

tff(c_22535,plain,(
    ! [A_22,B_26] :
      ( A_22 != '#skF_9'
      | ~ r2_hidden(B_26,'#skF_8')
      | k1_xboole_0 = A_22
      | k1_xboole_0 = A_22 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_22532])).

tff(c_22537,plain,(
    ! [B_9562] : ~ r2_hidden(B_9562,'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_22535])).

tff(c_22559,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(resolution,[status(thm)],[c_10438,c_22537])).

tff(c_22629,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_77,c_22559])).

tff(c_22631,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_22535])).

tff(c_22674,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22631,c_142])).

tff(c_22676,plain,(
    ! [XT_9563,B_9564] : r2_hidden(k1_relat_1(XT_9563),B_9564) ),
    inference(splitRight,[status(thm)],[c_10349])).

tff(c_22770,plain,(
    ! [XT_9604] : k1_relat_1(XT_9604) = '#skF_9' ),
    inference(resolution,[status(thm)],[c_22676,c_18])).

tff(c_22707,plain,(
    ! [XT_9563,A_10] : k1_relat_1(XT_9563) = A_10 ),
    inference(resolution,[status(thm)],[c_22676,c_18])).

tff(c_23260,plain,(
    ! [A_11965] : A_11965 = '#skF_9' ),
    inference(superposition,[status(thm),theory(equality)],[c_22770,c_22707])).

tff(c_23392,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_23260,c_142])).

tff(c_23394,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_140])).

tff(c_23393,plain,(
    ~ v1_funct_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_140])).

tff(c_23395,plain,(
    ~ v1_funct_1('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_23394,c_23393])).

tff(c_36,plain,(
    ! [A_15] :
      ( k1_relat_1(A_15) != k1_xboole_0
      | k1_xboole_0 = A_15
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_23452,plain,(
    ! [A_12964] :
      ( k1_relat_1(A_12964) != '#skF_9'
      | A_12964 = '#skF_9'
      | ~ v1_relat_1(A_12964) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_23394,c_23394,c_36])).

tff(c_23461,plain,(
    ! [A_16] :
      ( k1_relat_1('#skF_6'(A_16)) != '#skF_9'
      | '#skF_6'(A_16) = '#skF_9' ) ),
    inference(resolution,[status(thm)],[c_44,c_23452])).

tff(c_23470,plain,(
    ! [A_12965] :
      ( A_12965 != '#skF_9'
      | '#skF_6'(A_12965) = '#skF_9' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_23461])).

tff(c_42,plain,(
    ! [A_16] : v1_funct_1('#skF_6'(A_16)) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_23478,plain,(
    ! [A_12965] :
      ( v1_funct_1('#skF_9')
      | A_12965 != '#skF_9' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_23470,c_42])).

tff(c_23486,plain,(
    ! [A_12965] : A_12965 != '#skF_9' ),
    inference(negUnitSimplification,[status(thm)],[c_23395,c_23478])).

tff(c_23401,plain,(
    k1_relat_1('#skF_9') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_23394,c_23394,c_32])).

tff(c_23498,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_23486,c_23401])).

tff(c_23500,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_23499,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_23508,plain,(
    '#skF_9' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_23500,c_23499])).

tff(c_23502,plain,(
    k1_relat_1('#skF_9') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_23499,c_23499,c_32])).

tff(c_23517,plain,(
    k1_relat_1('#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_23508,c_23508,c_23502])).

tff(c_23503,plain,(
    ! [A_9] : r1_tarski('#skF_9',A_9) ),
    inference(demodulation,[status(thm),theory(equality)],[c_23499,c_16])).

tff(c_23522,plain,(
    ! [A_9] : r1_tarski('#skF_8',A_9) ),
    inference(demodulation,[status(thm),theory(equality)],[c_23508,c_23503])).

tff(c_23501,plain,(
    k2_relat_1('#skF_9') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_23499,c_23499,c_30])).

tff(c_23526,plain,(
    k2_relat_1('#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_23508,c_23508,c_23501])).

tff(c_23524,plain,(
    ! [C_29] :
      ( ~ r1_tarski(k2_relat_1(C_29),'#skF_8')
      | k1_relat_1(C_29) != '#skF_8'
      | ~ v1_funct_1(C_29)
      | ~ v1_relat_1(C_29) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_23508,c_54])).

tff(c_23530,plain,
    ( ~ r1_tarski('#skF_8','#skF_8')
    | k1_relat_1('#skF_8') != '#skF_8'
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_23526,c_23524])).

tff(c_23534,plain,
    ( ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_23517,c_23522,c_23530])).

tff(c_23537,plain,(
    ~ v1_relat_1('#skF_8') ),
    inference(splitLeft,[status(thm)],[c_23534])).

tff(c_23559,plain,(
    ! [A_12976] :
      ( k1_relat_1(A_12976) != '#skF_8'
      | A_12976 = '#skF_8'
      | ~ v1_relat_1(A_12976) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_23500,c_23500,c_36])).

tff(c_23565,plain,(
    ! [A_16] :
      ( k1_relat_1('#skF_6'(A_16)) != '#skF_8'
      | '#skF_6'(A_16) = '#skF_8' ) ),
    inference(resolution,[status(thm)],[c_44,c_23559])).

tff(c_23581,plain,(
    ! [A_12979] :
      ( A_12979 != '#skF_8'
      | '#skF_6'(A_12979) = '#skF_8' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_23565])).

tff(c_23591,plain,(
    ! [A_12979] :
      ( v1_relat_1('#skF_8')
      | A_12979 != '#skF_8' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_23581,c_44])).

tff(c_23597,plain,(
    ! [A_12979] : A_12979 != '#skF_8' ),
    inference(negUnitSimplification,[status(thm)],[c_23537,c_23591])).

tff(c_23609,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_23597,c_23526])).

tff(c_23610,plain,(
    ~ v1_funct_1('#skF_8') ),
    inference(splitRight,[status(thm)],[c_23534])).

tff(c_23640,plain,(
    ! [A_12987] :
      ( k1_relat_1(A_12987) != '#skF_8'
      | A_12987 = '#skF_8'
      | ~ v1_relat_1(A_12987) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_23500,c_23500,c_36])).

tff(c_23649,plain,(
    ! [A_16] :
      ( k1_relat_1('#skF_6'(A_16)) != '#skF_8'
      | '#skF_6'(A_16) = '#skF_8' ) ),
    inference(resolution,[status(thm)],[c_44,c_23640])).

tff(c_23669,plain,(
    ! [A_12990] :
      ( A_12990 != '#skF_8'
      | '#skF_6'(A_12990) = '#skF_8' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_23649])).

tff(c_23677,plain,(
    ! [A_12990] :
      ( v1_funct_1('#skF_8')
      | A_12990 != '#skF_8' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_23669,c_42])).

tff(c_23685,plain,(
    ! [A_12990] : A_12990 != '#skF_8' ),
    inference(negUnitSimplification,[status(thm)],[c_23610,c_23677])).

tff(c_23698,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_23685,c_23526])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 16:06:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.94/2.75  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.94/2.76  
% 7.94/2.76  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.94/2.76  %$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_3 > #skF_9 > #skF_8 > #skF_2 > #skF_7 > #skF_1 > #skF_5 > #skF_6 > #skF_4
% 7.94/2.76  
% 7.94/2.76  %Foreground sorts:
% 7.94/2.76  
% 7.94/2.76  
% 7.94/2.76  %Background operators:
% 7.94/2.76  
% 7.94/2.76  
% 7.94/2.76  %Foreground operators:
% 7.94/2.76  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.94/2.76  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.94/2.76  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.94/2.76  tff(k1_tarski, type, k1_tarski: $i > $i).
% 7.94/2.76  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.94/2.76  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 7.94/2.76  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.94/2.76  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.94/2.76  tff('#skF_9', type, '#skF_9': $i).
% 7.94/2.76  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 7.94/2.76  tff('#skF_8', type, '#skF_8': $i).
% 7.94/2.76  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.94/2.76  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.94/2.76  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.94/2.76  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 7.94/2.76  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 7.94/2.76  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 7.94/2.76  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 7.94/2.76  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.94/2.76  tff('#skF_6', type, '#skF_6': $i > $i).
% 7.94/2.76  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 7.94/2.76  
% 7.94/2.78  tff(f_102, negated_conjecture, ~(![A, B]: ~(~((A = k1_xboole_0) & ~(B = k1_xboole_0)) & (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => ~((B = k1_relat_1(C)) & r1_tarski(k2_relat_1(C), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_funct_1)).
% 7.94/2.78  tff(f_41, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 7.94/2.78  tff(f_39, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) <=> r2_hidden(C, B))) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tarski)).
% 7.94/2.78  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 7.94/2.78  tff(f_48, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 7.94/2.78  tff(f_84, axiom, (![A]: (~(A = k1_xboole_0) => (![B]: (?[C]: (((v1_relat_1(C) & v1_funct_1(C)) & (k1_relat_1(C) = A)) & (k2_relat_1(C) = k1_tarski(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_funct_1)).
% 7.94/2.78  tff(f_51, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 7.94/2.78  tff(f_71, axiom, (![A]: (?[B]: (((v1_relat_1(B) & v1_funct_1(B)) & (k1_relat_1(B) = A)) & (![C]: (r2_hidden(C, A) => (k1_funct_1(B, C) = k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', s3_funct_1__e2_25__funct_1)).
% 7.94/2.78  tff(f_59, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 7.94/2.78  tff(c_56, plain, (k1_xboole_0='#skF_9' | k1_xboole_0!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_102])).
% 7.94/2.78  tff(c_77, plain, (k1_xboole_0!='#skF_8'), inference(splitLeft, [status(thm)], [c_56])).
% 7.94/2.78  tff(c_16, plain, (![A_9]: (r1_tarski(k1_xboole_0, A_9))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.94/2.78  tff(c_440, plain, (![A_103, B_104]: (r2_hidden('#skF_2'(A_103, B_104), B_104) | r2_hidden('#skF_3'(A_103, B_104), A_103) | B_104=A_103)), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.94/2.78  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.94/2.78  tff(c_8265, plain, (![A_2272, B_2273, B_2274]: (r2_hidden('#skF_3'(A_2272, B_2273), B_2274) | ~r1_tarski(A_2272, B_2274) | r2_hidden('#skF_2'(A_2272, B_2273), B_2273) | B_2273=A_2272)), inference(resolution, [status(thm)], [c_440, c_2])).
% 7.94/2.78  tff(c_18, plain, (![C_14, A_10]: (C_14=A_10 | ~r2_hidden(C_14, k1_tarski(A_10)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 7.94/2.78  tff(c_9438, plain, (![A_3600, A_3601, B_3602]: (A_3600='#skF_3'(A_3601, B_3602) | ~r1_tarski(A_3601, k1_tarski(A_3600)) | r2_hidden('#skF_2'(A_3601, B_3602), B_3602) | B_3602=A_3601)), inference(resolution, [status(thm)], [c_8265, c_18])).
% 7.94/2.78  tff(c_9791, plain, (![XT_3862, B_3604]: (k1_relat_1(XT_3862)='#skF_3'(k1_xboole_0, B_3604) | r2_hidden('#skF_2'(k1_xboole_0, B_3604), B_3604) | k1_xboole_0=B_3604)), inference(resolution, [status(thm)], [c_16, c_9438])).
% 7.94/2.78  tff(c_470, plain, (![A_103, B_104, B_2]: (r2_hidden('#skF_3'(A_103, B_104), B_2) | ~r1_tarski(A_103, B_2) | r2_hidden('#skF_2'(A_103, B_104), B_104) | B_104=A_103)), inference(resolution, [status(thm)], [c_440, c_2])).
% 7.94/2.78  tff(c_9794, plain, (![XT_3862, B_2, B_3604]: (r2_hidden(k1_relat_1(XT_3862), B_2) | ~r1_tarski(k1_xboole_0, B_2) | r2_hidden('#skF_2'(k1_xboole_0, B_3604), B_3604) | k1_xboole_0=B_3604 | r2_hidden('#skF_2'(k1_xboole_0, B_3604), B_3604) | k1_xboole_0=B_3604)), inference(superposition, [status(thm), theory('equality')], [c_9791, c_470])).
% 7.94/2.78  tff(c_10349, plain, (![XT_3862, B_2, B_3604]: (r2_hidden(k1_relat_1(XT_3862), B_2) | r2_hidden('#skF_2'(k1_xboole_0, B_3604), B_3604) | k1_xboole_0=B_3604)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_9794])).
% 7.94/2.78  tff(c_10438, plain, (![B_3604]: (r2_hidden('#skF_2'(k1_xboole_0, B_3604), B_3604) | k1_xboole_0=B_3604)), inference(splitLeft, [status(thm)], [c_10349])).
% 7.94/2.78  tff(c_48, plain, (![A_22, B_26]: (k1_relat_1('#skF_7'(A_22, B_26))=A_22 | k1_xboole_0=A_22)), inference(cnfTransformation, [status(thm)], [f_84])).
% 7.94/2.78  tff(c_50, plain, (![A_22, B_26]: (v1_funct_1('#skF_7'(A_22, B_26)) | k1_xboole_0=A_22)), inference(cnfTransformation, [status(thm)], [f_84])).
% 7.94/2.78  tff(c_52, plain, (![A_22, B_26]: (v1_relat_1('#skF_7'(A_22, B_26)) | k1_xboole_0=A_22)), inference(cnfTransformation, [status(thm)], [f_84])).
% 7.94/2.78  tff(c_249, plain, (![A_54, B_55]: (r2_hidden('#skF_1'(A_54, B_55), A_54) | r1_tarski(A_54, B_55))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.94/2.78  tff(c_254, plain, (![A_10, B_55]: ('#skF_1'(k1_tarski(A_10), B_55)=A_10 | r1_tarski(k1_tarski(A_10), B_55))), inference(resolution, [status(thm)], [c_249, c_18])).
% 7.94/2.78  tff(c_256, plain, (![A_56, B_57]: (k2_relat_1('#skF_7'(A_56, B_57))=k1_tarski(B_57) | k1_xboole_0=A_56)), inference(cnfTransformation, [status(thm)], [f_84])).
% 7.94/2.78  tff(c_54, plain, (![C_29]: (~r1_tarski(k2_relat_1(C_29), '#skF_8') | k1_relat_1(C_29)!='#skF_9' | ~v1_funct_1(C_29) | ~v1_relat_1(C_29))), inference(cnfTransformation, [status(thm)], [f_102])).
% 7.94/2.78  tff(c_294, plain, (![B_68, A_69]: (~r1_tarski(k1_tarski(B_68), '#skF_8') | k1_relat_1('#skF_7'(A_69, B_68))!='#skF_9' | ~v1_funct_1('#skF_7'(A_69, B_68)) | ~v1_relat_1('#skF_7'(A_69, B_68)) | k1_xboole_0=A_69)), inference(superposition, [status(thm), theory('equality')], [c_256, c_54])).
% 7.94/2.78  tff(c_391, plain, (![A_89, A_90]: (k1_relat_1('#skF_7'(A_89, A_90))!='#skF_9' | ~v1_funct_1('#skF_7'(A_89, A_90)) | ~v1_relat_1('#skF_7'(A_89, A_90)) | k1_xboole_0=A_89 | '#skF_1'(k1_tarski(A_90), '#skF_8')=A_90)), inference(resolution, [status(thm)], [c_254, c_294])).
% 7.94/2.78  tff(c_508, plain, (![A_109, B_110]: (k1_relat_1('#skF_7'(A_109, B_110))!='#skF_9' | ~v1_funct_1('#skF_7'(A_109, B_110)) | '#skF_1'(k1_tarski(B_110), '#skF_8')=B_110 | k1_xboole_0=A_109)), inference(resolution, [status(thm)], [c_52, c_391])).
% 7.94/2.78  tff(c_513, plain, (![A_111, B_112]: (k1_relat_1('#skF_7'(A_111, B_112))!='#skF_9' | '#skF_1'(k1_tarski(B_112), '#skF_8')=B_112 | k1_xboole_0=A_111)), inference(resolution, [status(thm)], [c_50, c_508])).
% 7.94/2.78  tff(c_516, plain, (![A_22, B_26]: (A_22!='#skF_9' | '#skF_1'(k1_tarski(B_26), '#skF_8')=B_26 | k1_xboole_0=A_22 | k1_xboole_0=A_22)), inference(superposition, [status(thm), theory('equality')], [c_48, c_513])).
% 7.94/2.78  tff(c_518, plain, (k1_xboole_0='#skF_9'), inference(splitLeft, [status(thm)], [c_516])).
% 7.94/2.78  tff(c_32, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_51])).
% 7.94/2.78  tff(c_30, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_51])).
% 7.94/2.78  tff(c_79, plain, (![C_35]: (~r1_tarski(k2_relat_1(C_35), '#skF_8') | k1_relat_1(C_35)!='#skF_9' | ~v1_funct_1(C_35) | ~v1_relat_1(C_35))), inference(cnfTransformation, [status(thm)], [f_102])).
% 7.94/2.78  tff(c_82, plain, (~r1_tarski(k1_xboole_0, '#skF_8') | k1_relat_1(k1_xboole_0)!='#skF_9' | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_30, c_79])).
% 7.94/2.78  tff(c_84, plain, (k1_xboole_0!='#skF_9' | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_32, c_16, c_82])).
% 7.94/2.78  tff(c_93, plain, (~v1_relat_1(k1_xboole_0)), inference(splitLeft, [status(thm)], [c_84])).
% 7.94/2.78  tff(c_40, plain, (![A_16]: (k1_relat_1('#skF_6'(A_16))=A_16)), inference(cnfTransformation, [status(thm)], [f_71])).
% 7.94/2.78  tff(c_44, plain, (![A_16]: (v1_relat_1('#skF_6'(A_16)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 7.94/2.78  tff(c_103, plain, (![A_43]: (k1_relat_1(A_43)!=k1_xboole_0 | k1_xboole_0=A_43 | ~v1_relat_1(A_43))), inference(cnfTransformation, [status(thm)], [f_59])).
% 7.94/2.78  tff(c_109, plain, (![A_16]: (k1_relat_1('#skF_6'(A_16))!=k1_xboole_0 | '#skF_6'(A_16)=k1_xboole_0)), inference(resolution, [status(thm)], [c_44, c_103])).
% 7.94/2.78  tff(c_114, plain, (![A_44]: (k1_xboole_0!=A_44 | '#skF_6'(A_44)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_40, c_109])).
% 7.94/2.78  tff(c_124, plain, (![A_44]: (v1_relat_1(k1_xboole_0) | k1_xboole_0!=A_44)), inference(superposition, [status(thm), theory('equality')], [c_114, c_44])).
% 7.94/2.78  tff(c_130, plain, (![A_44]: (k1_xboole_0!=A_44)), inference(negUnitSimplification, [status(thm)], [c_93, c_124])).
% 7.94/2.78  tff(c_139, plain, $false, inference(negUnitSimplification, [status(thm)], [c_130, c_30])).
% 7.94/2.78  tff(c_140, plain, (~v1_funct_1(k1_xboole_0) | k1_xboole_0!='#skF_9'), inference(splitRight, [status(thm)], [c_84])).
% 7.94/2.78  tff(c_142, plain, (k1_xboole_0!='#skF_9'), inference(splitLeft, [status(thm)], [c_140])).
% 7.94/2.78  tff(c_544, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_518, c_142])).
% 7.94/2.78  tff(c_547, plain, (![B_113]: ('#skF_1'(k1_tarski(B_113), '#skF_8')=B_113)), inference(splitRight, [status(thm)], [c_516])).
% 7.94/2.78  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.94/2.78  tff(c_578, plain, (![B_114]: (~r2_hidden(B_114, '#skF_8') | r1_tarski(k1_tarski(B_114), '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_547, c_4])).
% 7.94/2.78  tff(c_262, plain, (![B_57, A_56]: (~r1_tarski(k1_tarski(B_57), '#skF_8') | k1_relat_1('#skF_7'(A_56, B_57))!='#skF_9' | ~v1_funct_1('#skF_7'(A_56, B_57)) | ~v1_relat_1('#skF_7'(A_56, B_57)) | k1_xboole_0=A_56)), inference(superposition, [status(thm), theory('equality')], [c_256, c_54])).
% 7.94/2.78  tff(c_659, plain, (![A_126, B_127]: (k1_relat_1('#skF_7'(A_126, B_127))!='#skF_9' | ~v1_funct_1('#skF_7'(A_126, B_127)) | ~v1_relat_1('#skF_7'(A_126, B_127)) | k1_xboole_0=A_126 | ~r2_hidden(B_127, '#skF_8'))), inference(resolution, [status(thm)], [c_578, c_262])).
% 7.94/2.78  tff(c_22527, plain, (![A_9558, B_9559]: (k1_relat_1('#skF_7'(A_9558, B_9559))!='#skF_9' | ~v1_funct_1('#skF_7'(A_9558, B_9559)) | ~r2_hidden(B_9559, '#skF_8') | k1_xboole_0=A_9558)), inference(resolution, [status(thm)], [c_52, c_659])).
% 7.94/2.78  tff(c_22532, plain, (![A_9560, B_9561]: (k1_relat_1('#skF_7'(A_9560, B_9561))!='#skF_9' | ~r2_hidden(B_9561, '#skF_8') | k1_xboole_0=A_9560)), inference(resolution, [status(thm)], [c_50, c_22527])).
% 7.94/2.78  tff(c_22535, plain, (![A_22, B_26]: (A_22!='#skF_9' | ~r2_hidden(B_26, '#skF_8') | k1_xboole_0=A_22 | k1_xboole_0=A_22)), inference(superposition, [status(thm), theory('equality')], [c_48, c_22532])).
% 7.94/2.78  tff(c_22537, plain, (![B_9562]: (~r2_hidden(B_9562, '#skF_8'))), inference(splitLeft, [status(thm)], [c_22535])).
% 7.94/2.78  tff(c_22559, plain, (k1_xboole_0='#skF_8'), inference(resolution, [status(thm)], [c_10438, c_22537])).
% 7.94/2.78  tff(c_22629, plain, $false, inference(negUnitSimplification, [status(thm)], [c_77, c_22559])).
% 7.94/2.78  tff(c_22631, plain, (k1_xboole_0='#skF_9'), inference(splitRight, [status(thm)], [c_22535])).
% 7.94/2.78  tff(c_22674, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22631, c_142])).
% 7.94/2.78  tff(c_22676, plain, (![XT_9563, B_9564]: (r2_hidden(k1_relat_1(XT_9563), B_9564))), inference(splitRight, [status(thm)], [c_10349])).
% 7.94/2.78  tff(c_22770, plain, (![XT_9604]: (k1_relat_1(XT_9604)='#skF_9')), inference(resolution, [status(thm)], [c_22676, c_18])).
% 7.94/2.78  tff(c_22707, plain, (![XT_9563, A_10]: (k1_relat_1(XT_9563)=A_10)), inference(resolution, [status(thm)], [c_22676, c_18])).
% 7.94/2.78  tff(c_23260, plain, (![A_11965]: (A_11965='#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_22770, c_22707])).
% 7.94/2.78  tff(c_23392, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_23260, c_142])).
% 7.94/2.78  tff(c_23394, plain, (k1_xboole_0='#skF_9'), inference(splitRight, [status(thm)], [c_140])).
% 7.94/2.78  tff(c_23393, plain, (~v1_funct_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_140])).
% 7.94/2.78  tff(c_23395, plain, (~v1_funct_1('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_23394, c_23393])).
% 7.94/2.78  tff(c_36, plain, (![A_15]: (k1_relat_1(A_15)!=k1_xboole_0 | k1_xboole_0=A_15 | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_59])).
% 7.94/2.78  tff(c_23452, plain, (![A_12964]: (k1_relat_1(A_12964)!='#skF_9' | A_12964='#skF_9' | ~v1_relat_1(A_12964))), inference(demodulation, [status(thm), theory('equality')], [c_23394, c_23394, c_36])).
% 7.94/2.78  tff(c_23461, plain, (![A_16]: (k1_relat_1('#skF_6'(A_16))!='#skF_9' | '#skF_6'(A_16)='#skF_9')), inference(resolution, [status(thm)], [c_44, c_23452])).
% 7.94/2.78  tff(c_23470, plain, (![A_12965]: (A_12965!='#skF_9' | '#skF_6'(A_12965)='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_23461])).
% 7.94/2.78  tff(c_42, plain, (![A_16]: (v1_funct_1('#skF_6'(A_16)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 7.94/2.78  tff(c_23478, plain, (![A_12965]: (v1_funct_1('#skF_9') | A_12965!='#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_23470, c_42])).
% 7.94/2.78  tff(c_23486, plain, (![A_12965]: (A_12965!='#skF_9')), inference(negUnitSimplification, [status(thm)], [c_23395, c_23478])).
% 7.94/2.78  tff(c_23401, plain, (k1_relat_1('#skF_9')='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_23394, c_23394, c_32])).
% 7.94/2.78  tff(c_23498, plain, $false, inference(negUnitSimplification, [status(thm)], [c_23486, c_23401])).
% 7.94/2.78  tff(c_23500, plain, (k1_xboole_0='#skF_8'), inference(splitRight, [status(thm)], [c_56])).
% 7.94/2.78  tff(c_23499, plain, (k1_xboole_0='#skF_9'), inference(splitRight, [status(thm)], [c_56])).
% 7.94/2.78  tff(c_23508, plain, ('#skF_9'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_23500, c_23499])).
% 7.94/2.78  tff(c_23502, plain, (k1_relat_1('#skF_9')='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_23499, c_23499, c_32])).
% 7.94/2.78  tff(c_23517, plain, (k1_relat_1('#skF_8')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_23508, c_23508, c_23502])).
% 7.94/2.78  tff(c_23503, plain, (![A_9]: (r1_tarski('#skF_9', A_9))), inference(demodulation, [status(thm), theory('equality')], [c_23499, c_16])).
% 7.94/2.78  tff(c_23522, plain, (![A_9]: (r1_tarski('#skF_8', A_9))), inference(demodulation, [status(thm), theory('equality')], [c_23508, c_23503])).
% 7.94/2.78  tff(c_23501, plain, (k2_relat_1('#skF_9')='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_23499, c_23499, c_30])).
% 7.94/2.78  tff(c_23526, plain, (k2_relat_1('#skF_8')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_23508, c_23508, c_23501])).
% 7.94/2.78  tff(c_23524, plain, (![C_29]: (~r1_tarski(k2_relat_1(C_29), '#skF_8') | k1_relat_1(C_29)!='#skF_8' | ~v1_funct_1(C_29) | ~v1_relat_1(C_29))), inference(demodulation, [status(thm), theory('equality')], [c_23508, c_54])).
% 7.94/2.78  tff(c_23530, plain, (~r1_tarski('#skF_8', '#skF_8') | k1_relat_1('#skF_8')!='#skF_8' | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_23526, c_23524])).
% 7.94/2.78  tff(c_23534, plain, (~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_23517, c_23522, c_23530])).
% 7.94/2.78  tff(c_23537, plain, (~v1_relat_1('#skF_8')), inference(splitLeft, [status(thm)], [c_23534])).
% 7.94/2.78  tff(c_23559, plain, (![A_12976]: (k1_relat_1(A_12976)!='#skF_8' | A_12976='#skF_8' | ~v1_relat_1(A_12976))), inference(demodulation, [status(thm), theory('equality')], [c_23500, c_23500, c_36])).
% 7.94/2.78  tff(c_23565, plain, (![A_16]: (k1_relat_1('#skF_6'(A_16))!='#skF_8' | '#skF_6'(A_16)='#skF_8')), inference(resolution, [status(thm)], [c_44, c_23559])).
% 7.94/2.78  tff(c_23581, plain, (![A_12979]: (A_12979!='#skF_8' | '#skF_6'(A_12979)='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_23565])).
% 7.94/2.78  tff(c_23591, plain, (![A_12979]: (v1_relat_1('#skF_8') | A_12979!='#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_23581, c_44])).
% 7.94/2.78  tff(c_23597, plain, (![A_12979]: (A_12979!='#skF_8')), inference(negUnitSimplification, [status(thm)], [c_23537, c_23591])).
% 7.94/2.78  tff(c_23609, plain, $false, inference(negUnitSimplification, [status(thm)], [c_23597, c_23526])).
% 7.94/2.78  tff(c_23610, plain, (~v1_funct_1('#skF_8')), inference(splitRight, [status(thm)], [c_23534])).
% 7.94/2.78  tff(c_23640, plain, (![A_12987]: (k1_relat_1(A_12987)!='#skF_8' | A_12987='#skF_8' | ~v1_relat_1(A_12987))), inference(demodulation, [status(thm), theory('equality')], [c_23500, c_23500, c_36])).
% 7.94/2.78  tff(c_23649, plain, (![A_16]: (k1_relat_1('#skF_6'(A_16))!='#skF_8' | '#skF_6'(A_16)='#skF_8')), inference(resolution, [status(thm)], [c_44, c_23640])).
% 7.94/2.78  tff(c_23669, plain, (![A_12990]: (A_12990!='#skF_8' | '#skF_6'(A_12990)='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_23649])).
% 7.94/2.78  tff(c_23677, plain, (![A_12990]: (v1_funct_1('#skF_8') | A_12990!='#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_23669, c_42])).
% 7.94/2.78  tff(c_23685, plain, (![A_12990]: (A_12990!='#skF_8')), inference(negUnitSimplification, [status(thm)], [c_23610, c_23677])).
% 7.94/2.78  tff(c_23698, plain, $false, inference(negUnitSimplification, [status(thm)], [c_23685, c_23526])).
% 7.94/2.78  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.94/2.78  
% 7.94/2.78  Inference rules
% 7.94/2.78  ----------------------
% 7.94/2.78  #Ref     : 1
% 7.94/2.78  #Sup     : 4010
% 7.94/2.78  #Fact    : 5
% 7.94/2.78  #Define  : 0
% 7.94/2.78  #Split   : 10
% 7.94/2.78  #Chain   : 0
% 7.94/2.78  #Close   : 0
% 7.94/2.78  
% 7.94/2.78  Ordering : KBO
% 7.94/2.78  
% 7.94/2.78  Simplification rules
% 7.94/2.78  ----------------------
% 7.94/2.78  #Subsume      : 1283
% 7.94/2.78  #Demod        : 734
% 7.94/2.78  #Tautology    : 437
% 7.94/2.78  #SimpNegUnit  : 70
% 7.94/2.78  #BackRed      : 105
% 7.94/2.78  
% 7.94/2.78  #Partial instantiations: 8531
% 7.94/2.78  #Strategies tried      : 1
% 7.94/2.78  
% 7.94/2.78  Timing (in seconds)
% 7.94/2.78  ----------------------
% 7.94/2.78  Preprocessing        : 0.30
% 7.94/2.78  Parsing              : 0.16
% 7.94/2.78  CNF conversion       : 0.02
% 7.94/2.78  Main loop            : 1.70
% 7.94/2.78  Inferencing          : 0.62
% 7.94/2.78  Reduction            : 0.43
% 7.94/2.78  Demodulation         : 0.28
% 7.94/2.78  BG Simplification    : 0.08
% 7.94/2.78  Subsumption          : 0.42
% 7.94/2.78  Abstraction          : 0.11
% 7.94/2.78  MUC search           : 0.00
% 7.94/2.78  Cooper               : 0.00
% 7.94/2.78  Total                : 2.04
% 7.94/2.78  Index Insertion      : 0.00
% 7.94/2.78  Index Deletion       : 0.00
% 7.94/2.78  Index Matching       : 0.00
% 7.94/2.78  BG Taut test         : 0.00
%------------------------------------------------------------------------------
