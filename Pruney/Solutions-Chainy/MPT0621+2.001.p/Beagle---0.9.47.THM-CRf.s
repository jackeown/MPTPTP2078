%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:58 EST 2020

% Result     : Theorem 23.61s
% Output     : CNFRefutation 23.68s
% Verified   : 
% Statistics : Number of formulae       :  179 (1086 expanded)
%              Number of leaves         :   43 ( 394 expanded)
%              Depth                    :   17
%              Number of atoms          :  333 (3064 expanded)
%              Number of equality atoms :  106 ( 997 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_enumset1 > k4_tarski > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > np__1 > k1_xboole_0 > #skF_13 > #skF_9 > #skF_11 > #skF_16 > #skF_6 > #skF_17 > #skF_1 > #skF_8 > #skF_14 > #skF_15 > #skF_12 > #skF_10 > #skF_2 > #skF_7 > #skF_3 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_13',type,(
    '#skF_13': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i > $i )).

tff('#skF_11',type,(
    '#skF_11': ( $i * $i ) > $i )).

tff(np__1,type,(
    np__1: $i )).

tff('#skF_16',type,(
    '#skF_16': $i > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff('#skF_17',type,(
    '#skF_17': $i )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_8',type,(
    '#skF_8': $i > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_14',type,(
    '#skF_14': ( $i * $i ) > $i )).

tff('#skF_15',type,(
    '#skF_15': $i > $i )).

tff('#skF_12',type,(
    '#skF_12': ( $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i ) > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_93,axiom,(
    ! [A,B] :
    ? [C] :
      ( v1_relat_1(C)
      & v1_funct_1(C)
      & k1_relat_1(C) = A
      & ! [D] :
          ( r2_hidden(D,A)
         => k1_funct_1(C,D) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e2_24__funct_1)).

tff(f_117,axiom,(
    ! [A] :
    ? [B] :
      ( v1_relat_1(B)
      & v1_funct_1(B)
      & k1_relat_1(B) = A
      & ! [C] :
          ( r2_hidden(C,A)
         => k1_funct_1(B,C) = np__1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e7_25__funct_1)).

tff(f_136,negated_conjecture,(
    ~ ! [A] :
        ( ! [B] :
            ( ( v1_relat_1(B)
              & v1_funct_1(B) )
           => ! [C] :
                ( ( v1_relat_1(C)
                  & v1_funct_1(C) )
               => ( ( k1_relat_1(B) = A
                    & k1_relat_1(C) = A )
                 => B = C ) ) )
       => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_funct_1)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_81,axiom,(
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

tff(f_45,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(f_30,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

tff(f_105,axiom,(
    ! [A] :
    ? [B] :
      ( v1_relat_1(B)
      & v1_funct_1(B)
      & k1_relat_1(B) = A
      & ! [C] :
          ( r2_hidden(C,A)
         => k1_funct_1(B,C) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e2_25__funct_1)).

tff(f_66,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_63,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ! [B,C] : ~ r2_hidden(k4_tarski(B,C),A)
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_relat_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

tff(c_68,plain,(
    ! [A_77,B_78] : v1_funct_1('#skF_14'(A_77,B_78)) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_66,plain,(
    ! [A_77,B_78] : k1_relat_1('#skF_14'(A_77,B_78)) = A_77 ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_70,plain,(
    ! [A_77,B_78] : v1_relat_1('#skF_14'(A_77,B_78)) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_82,plain,(
    ! [A_90] : k1_relat_1('#skF_16'(A_90)) = A_90 ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_84,plain,(
    ! [A_90] : v1_funct_1('#skF_16'(A_90)) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_86,plain,(
    ! [A_90] : v1_relat_1('#skF_16'(A_90)) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_105,plain,(
    ! [C_110,B_111] :
      ( C_110 = B_111
      | k1_relat_1(C_110) != '#skF_17'
      | k1_relat_1(B_111) != '#skF_17'
      | ~ v1_funct_1(C_110)
      | ~ v1_relat_1(C_110)
      | ~ v1_funct_1(B_111)
      | ~ v1_relat_1(B_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_111,plain,(
    ! [B_111,A_90] :
      ( B_111 = '#skF_16'(A_90)
      | k1_relat_1('#skF_16'(A_90)) != '#skF_17'
      | k1_relat_1(B_111) != '#skF_17'
      | ~ v1_funct_1('#skF_16'(A_90))
      | ~ v1_funct_1(B_111)
      | ~ v1_relat_1(B_111) ) ),
    inference(resolution,[status(thm)],[c_86,c_105])).

tff(c_120,plain,(
    ! [B_111,A_90] :
      ( B_111 = '#skF_16'(A_90)
      | k1_relat_1('#skF_16'(A_90)) != '#skF_17'
      | k1_relat_1(B_111) != '#skF_17'
      | ~ v1_funct_1(B_111)
      | ~ v1_relat_1(B_111) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_111])).

tff(c_177,plain,(
    ! [B_127,A_128] :
      ( B_127 = '#skF_16'(A_128)
      | A_128 != '#skF_17'
      | k1_relat_1(B_127) != '#skF_17'
      | ~ v1_funct_1(B_127)
      | ~ v1_relat_1(B_127) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_120])).

tff(c_179,plain,(
    ! [A_128,A_77,B_78] :
      ( '#skF_16'(A_128) = '#skF_14'(A_77,B_78)
      | A_128 != '#skF_17'
      | k1_relat_1('#skF_14'(A_77,B_78)) != '#skF_17'
      | ~ v1_funct_1('#skF_14'(A_77,B_78)) ) ),
    inference(resolution,[status(thm)],[c_70,c_177])).

tff(c_186,plain,(
    ! [A_128,A_77,B_78] :
      ( '#skF_16'(A_128) = '#skF_14'(A_77,B_78)
      | A_128 != '#skF_17'
      | A_77 != '#skF_17' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_179])).

tff(c_6,plain,(
    ! [A_3] :
      ( v1_xboole_0(A_3)
      | r2_hidden('#skF_1'(A_3),A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_64,plain,(
    ! [A_77,B_78,D_83] :
      ( k1_funct_1('#skF_14'(A_77,B_78),D_83) = B_78
      | ~ r2_hidden(D_83,A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_1253,plain,(
    ! [A_223,D_224] :
      ( r2_hidden(k1_funct_1(A_223,D_224),k2_relat_1(A_223))
      | ~ r2_hidden(D_224,k1_relat_1(A_223))
      | ~ v1_funct_1(A_223)
      | ~ v1_relat_1(A_223) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_1261,plain,(
    ! [B_78,A_77,D_83] :
      ( r2_hidden(B_78,k2_relat_1('#skF_14'(A_77,B_78)))
      | ~ r2_hidden(D_83,k1_relat_1('#skF_14'(A_77,B_78)))
      | ~ v1_funct_1('#skF_14'(A_77,B_78))
      | ~ v1_relat_1('#skF_14'(A_77,B_78))
      | ~ r2_hidden(D_83,A_77) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_1253])).

tff(c_76755,plain,(
    ! [B_94334,A_94335,D_94336] :
      ( r2_hidden(B_94334,k2_relat_1('#skF_14'(A_94335,B_94334)))
      | ~ r2_hidden(D_94336,A_94335) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_1261])).

tff(c_77350,plain,(
    ! [B_95192,A_95193] :
      ( r2_hidden(B_95192,k2_relat_1('#skF_14'(A_95193,B_95192)))
      | v1_xboole_0(A_95193) ) ),
    inference(resolution,[status(thm)],[c_6,c_76755])).

tff(c_77384,plain,(
    ! [B_78,A_128,A_77] :
      ( r2_hidden(B_78,k2_relat_1('#skF_16'(A_128)))
      | v1_xboole_0(A_77)
      | A_128 != '#skF_17'
      | A_77 != '#skF_17' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_186,c_77350])).

tff(c_120552,plain,(
    ! [A_135303] :
      ( v1_xboole_0(A_135303)
      | A_135303 != '#skF_17' ) ),
    inference(splitLeft,[status(thm)],[c_77384])).

tff(c_15719,plain,(
    ! [A_29391,C_29392] :
      ( r2_hidden('#skF_13'(A_29391,k2_relat_1(A_29391),C_29392),k1_relat_1(A_29391))
      | ~ r2_hidden(C_29392,k2_relat_1(A_29391))
      | ~ v1_funct_1(A_29391)
      | ~ v1_relat_1(A_29391) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_15743,plain,(
    ! [A_90,C_29392] :
      ( r2_hidden('#skF_13'('#skF_16'(A_90),k2_relat_1('#skF_16'(A_90)),C_29392),A_90)
      | ~ r2_hidden(C_29392,k2_relat_1('#skF_16'(A_90)))
      | ~ v1_funct_1('#skF_16'(A_90))
      | ~ v1_relat_1('#skF_16'(A_90)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_15719])).

tff(c_84257,plain,(
    ! [A_110958,C_110959] :
      ( r2_hidden('#skF_13'('#skF_16'(A_110958),k2_relat_1('#skF_16'(A_110958)),C_110959),A_110958)
      | ~ r2_hidden(C_110959,k2_relat_1('#skF_16'(A_110958))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_15743])).

tff(c_4,plain,(
    ! [B_6,A_3] :
      ( ~ r2_hidden(B_6,A_3)
      | ~ v1_xboole_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_84411,plain,(
    ! [A_111086,C_111087] :
      ( ~ v1_xboole_0(A_111086)
      | ~ r2_hidden(C_111087,k2_relat_1('#skF_16'(A_111086))) ) ),
    inference(resolution,[status(thm)],[c_84257,c_4])).

tff(c_84562,plain,(
    ! [A_111214] :
      ( ~ v1_xboole_0(A_111214)
      | v1_xboole_0(k2_relat_1('#skF_16'(A_111214))) ) ),
    inference(resolution,[status(thm)],[c_6,c_84411])).

tff(c_77398,plain,(
    ! [A_95278,B_95279] :
      ( ~ v1_xboole_0(k2_relat_1('#skF_14'(A_95278,B_95279)))
      | v1_xboole_0(A_95278) ) ),
    inference(resolution,[status(thm)],[c_77350,c_4])).

tff(c_77417,plain,(
    ! [A_128,A_77] :
      ( ~ v1_xboole_0(k2_relat_1('#skF_16'(A_128)))
      | v1_xboole_0(A_77)
      | A_128 != '#skF_17'
      | A_77 != '#skF_17' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_186,c_77398])).

tff(c_77425,plain,(
    ! [A_128] :
      ( ~ v1_xboole_0(k2_relat_1('#skF_16'(A_128)))
      | A_128 != '#skF_17' ) ),
    inference(splitLeft,[status(thm)],[c_77417])).

tff(c_84643,plain,(
    ! [A_111214] :
      ( A_111214 != '#skF_17'
      | ~ v1_xboole_0(A_111214) ) ),
    inference(resolution,[status(thm)],[c_84562,c_77425])).

tff(c_120958,plain,(
    ! [A_135303] : A_135303 != '#skF_17' ),
    inference(resolution,[status(thm)],[c_120552,c_84643])).

tff(c_121056,plain,(
    $false ),
    inference(reflexivity,[status(thm),theory(equality)],[c_120958])).

tff(c_121059,plain,(
    ! [B_135430,A_135431] :
      ( r2_hidden(B_135430,k2_relat_1('#skF_16'(A_135431)))
      | A_135431 != '#skF_17' ) ),
    inference(splitRight,[status(thm)],[c_77384])).

tff(c_12,plain,(
    ! [D_12,B_8] : r2_hidden(D_12,k2_tarski(D_12,B_8)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_77081,plain,(
    ! [B_94846,D_94847,B_94848] : r2_hidden(B_94846,k2_relat_1('#skF_14'(k2_tarski(D_94847,B_94848),B_94846))) ),
    inference(resolution,[status(thm)],[c_12,c_76755])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( ~ r2_hidden(B_2,A_1)
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_77235,plain,(
    ! [D_94847,B_94848,B_94846] : ~ r2_hidden(k2_relat_1('#skF_14'(k2_tarski(D_94847,B_94848),B_94846)),B_94846) ),
    inference(resolution,[status(thm)],[c_77081,c_2])).

tff(c_121260,plain,(
    ! [A_135431] : A_135431 != '#skF_17' ),
    inference(resolution,[status(thm)],[c_121059,c_77235])).

tff(c_121319,plain,(
    $false ),
    inference(reflexivity,[status(thm),theory(equality)],[c_121260])).

tff(c_121322,plain,(
    ! [A_135558] :
      ( v1_xboole_0(A_135558)
      | A_135558 != '#skF_17' ) ),
    inference(splitRight,[status(thm)],[c_77417])).

tff(c_78,plain,(
    ! [A_84] : v1_relat_1('#skF_15'(A_84)) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_76,plain,(
    ! [A_84] : v1_funct_1('#skF_15'(A_84)) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_74,plain,(
    ! [A_84] : k1_relat_1('#skF_15'(A_84)) = A_84 ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_44,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_622,plain,(
    ! [A_186] :
      ( k1_xboole_0 = A_186
      | r2_hidden(k4_tarski('#skF_8'(A_186),'#skF_9'(A_186)),A_186)
      | ~ v1_relat_1(A_186) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_30,plain,(
    ! [C_30,A_15,D_33] :
      ( r2_hidden(C_30,k1_relat_1(A_15))
      | ~ r2_hidden(k4_tarski(C_30,D_33),A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_640,plain,(
    ! [A_188] :
      ( r2_hidden('#skF_8'(A_188),k1_relat_1(A_188))
      | k1_xboole_0 = A_188
      | ~ v1_relat_1(A_188) ) ),
    inference(resolution,[status(thm)],[c_622,c_30])).

tff(c_651,plain,(
    ! [A_84] :
      ( r2_hidden('#skF_8'('#skF_15'(A_84)),A_84)
      | '#skF_15'(A_84) = k1_xboole_0
      | ~ v1_relat_1('#skF_15'(A_84)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_640])).

tff(c_663,plain,(
    ! [A_84] :
      ( r2_hidden('#skF_8'('#skF_15'(A_84)),A_84)
      | '#skF_15'(A_84) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_651])).

tff(c_3305,plain,(
    ! [A_359,C_360] :
      ( r2_hidden('#skF_13'(A_359,k2_relat_1(A_359),C_360),k1_relat_1(A_359))
      | ~ r2_hidden(C_360,k2_relat_1(A_359))
      | ~ v1_funct_1(A_359)
      | ~ v1_relat_1(A_359) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_3326,plain,(
    ! [A_84,C_360] :
      ( r2_hidden('#skF_13'('#skF_15'(A_84),k2_relat_1('#skF_15'(A_84)),C_360),A_84)
      | ~ r2_hidden(C_360,k2_relat_1('#skF_15'(A_84)))
      | ~ v1_funct_1('#skF_15'(A_84))
      | ~ v1_relat_1('#skF_15'(A_84)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_3305])).

tff(c_12560,plain,(
    ! [A_23100,C_23101] :
      ( r2_hidden('#skF_13'('#skF_15'(A_23100),k2_relat_1('#skF_15'(A_23100)),C_23101),A_23100)
      | ~ r2_hidden(C_23101,k2_relat_1('#skF_15'(A_23100))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_3326])).

tff(c_12687,plain,(
    ! [A_23186,C_23187] :
      ( ~ v1_xboole_0(A_23186)
      | ~ r2_hidden(C_23187,k2_relat_1('#skF_15'(A_23186))) ) ),
    inference(resolution,[status(thm)],[c_12560,c_4])).

tff(c_13005,plain,(
    ! [A_23612] :
      ( ~ v1_xboole_0(A_23612)
      | '#skF_15'(k2_relat_1('#skF_15'(A_23612))) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_663,c_12687])).

tff(c_13173,plain,(
    ! [A_23612] :
      ( k2_relat_1('#skF_15'(A_23612)) = k1_relat_1(k1_xboole_0)
      | ~ v1_xboole_0(A_23612) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13005,c_74])).

tff(c_13251,plain,(
    ! [A_23697] :
      ( k2_relat_1('#skF_15'(A_23697)) = k1_xboole_0
      | ~ v1_xboole_0(A_23697) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_13173])).

tff(c_3339,plain,(
    ! [A_359,C_360] :
      ( ~ v1_xboole_0(k1_relat_1(A_359))
      | ~ r2_hidden(C_360,k2_relat_1(A_359))
      | ~ v1_funct_1(A_359)
      | ~ v1_relat_1(A_359) ) ),
    inference(resolution,[status(thm)],[c_3305,c_4])).

tff(c_13295,plain,(
    ! [A_23697,C_360] :
      ( ~ v1_xboole_0(k1_relat_1('#skF_15'(A_23697)))
      | ~ r2_hidden(C_360,k1_xboole_0)
      | ~ v1_funct_1('#skF_15'(A_23697))
      | ~ v1_relat_1('#skF_15'(A_23697))
      | ~ v1_xboole_0(A_23697) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13251,c_3339])).

tff(c_13361,plain,(
    ! [C_360,A_23697] :
      ( ~ r2_hidden(C_360,k1_xboole_0)
      | ~ v1_xboole_0(A_23697) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_74,c_13295])).

tff(c_13373,plain,(
    ! [A_23697] : ~ v1_xboole_0(A_23697) ),
    inference(splitLeft,[status(thm)],[c_13361])).

tff(c_8188,plain,(
    ! [B_16259,A_16260,D_16261] :
      ( r2_hidden(B_16259,k2_relat_1('#skF_14'(A_16260,B_16259)))
      | ~ r2_hidden(D_16261,A_16260) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_1261])).

tff(c_8258,plain,(
    ! [B_16259,A_3] :
      ( r2_hidden(B_16259,k2_relat_1('#skF_14'(A_3,B_16259)))
      | v1_xboole_0(A_3) ) ),
    inference(resolution,[status(thm)],[c_6,c_8188])).

tff(c_14992,plain,(
    ! [B_28623,A_28624] : r2_hidden(B_28623,k2_relat_1('#skF_14'(A_28624,B_28623))) ),
    inference(negUnitSimplification,[status(thm)],[c_13373,c_8258])).

tff(c_15013,plain,(
    ! [B_78,A_128,A_77] :
      ( r2_hidden(B_78,k2_relat_1('#skF_16'(A_128)))
      | A_128 != '#skF_17'
      | A_77 != '#skF_17' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_186,c_14992])).

tff(c_15063,plain,(
    ! [A_77] : A_77 != '#skF_17' ),
    inference(splitLeft,[status(thm)],[c_15013])).

tff(c_15067,plain,(
    $false ),
    inference(reflexivity,[status(thm),theory(equality)],[c_15063])).

tff(c_15071,plain,(
    ! [B_29006,A_29007] :
      ( r2_hidden(B_29006,k2_relat_1('#skF_16'(A_29007)))
      | A_29007 != '#skF_17' ) ),
    inference(splitRight,[status(thm)],[c_15013])).

tff(c_8284,plain,(
    ! [B_16432,A_16433] :
      ( r2_hidden(B_16432,k2_relat_1('#skF_14'(A_16433,B_16432)))
      | v1_xboole_0(A_16433) ) ),
    inference(resolution,[status(thm)],[c_6,c_8188])).

tff(c_8323,plain,(
    ! [A_16433,B_16432] :
      ( ~ r2_hidden(k2_relat_1('#skF_14'(A_16433,B_16432)),B_16432)
      | v1_xboole_0(A_16433) ) ),
    inference(resolution,[status(thm)],[c_8284,c_2])).

tff(c_13530,plain,(
    ! [A_16433,B_16432] : ~ r2_hidden(k2_relat_1('#skF_14'(A_16433,B_16432)),B_16432) ),
    inference(negUnitSimplification,[status(thm)],[c_13373,c_8323])).

tff(c_15136,plain,(
    ! [A_29007] : A_29007 != '#skF_17' ),
    inference(resolution,[status(thm)],[c_15071,c_13530])).

tff(c_15153,plain,(
    $false ),
    inference(reflexivity,[status(thm),theory(equality)],[c_15136])).

tff(c_15157,plain,(
    ! [C_29134] : ~ r2_hidden(C_29134,k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_13361])).

tff(c_15229,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_6,c_15157])).

tff(c_991,plain,(
    ! [C_210,A_211] :
      ( r2_hidden(k4_tarski(C_210,'#skF_7'(A_211,k1_relat_1(A_211),C_210)),A_211)
      | ~ r2_hidden(C_210,k1_relat_1(A_211)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1024,plain,(
    ! [A_212,C_213] :
      ( ~ v1_xboole_0(A_212)
      | ~ r2_hidden(C_213,k1_relat_1(A_212)) ) ),
    inference(resolution,[status(thm)],[c_991,c_4])).

tff(c_1083,plain,(
    ! [A_212] :
      ( ~ v1_xboole_0(A_212)
      | v1_xboole_0(k1_relat_1(A_212)) ) ),
    inference(resolution,[status(thm)],[c_6,c_1024])).

tff(c_1183,plain,(
    ! [A_222] :
      ( ~ v1_xboole_0(A_222)
      | '#skF_15'(k1_relat_1(A_222)) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_663,c_1024])).

tff(c_1218,plain,(
    ! [A_222] :
      ( k1_relat_1(k1_xboole_0) = k1_relat_1(A_222)
      | ~ v1_xboole_0(A_222) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1183,c_74])).

tff(c_2315,plain,(
    ! [A_305] :
      ( k1_relat_1(A_305) = k1_xboole_0
      | ~ v1_xboole_0(A_305) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_1218])).

tff(c_2319,plain,(
    ! [A_212] :
      ( k1_relat_1(k1_relat_1(A_212)) = k1_xboole_0
      | ~ v1_xboole_0(A_212) ) ),
    inference(resolution,[status(thm)],[c_1083,c_2315])).

tff(c_28,plain,(
    ! [C_30,A_15] :
      ( r2_hidden(k4_tarski(C_30,'#skF_7'(A_15,k1_relat_1(A_15),C_30)),A_15)
      | ~ r2_hidden(C_30,k1_relat_1(A_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_2581,plain,(
    ! [A_326,C_327] :
      ( ~ v1_xboole_0(A_326)
      | ~ r2_hidden(C_327,k1_relat_1(k1_relat_1(A_326))) ) ),
    inference(resolution,[status(thm)],[c_28,c_1024])).

tff(c_2642,plain,(
    ! [A_328] :
      ( ~ v1_xboole_0(A_328)
      | v1_xboole_0(k1_relat_1(k1_relat_1(A_328))) ) ),
    inference(resolution,[status(thm)],[c_6,c_2581])).

tff(c_2665,plain,(
    ! [A_212] :
      ( ~ v1_xboole_0(A_212)
      | v1_xboole_0(k1_xboole_0)
      | ~ v1_xboole_0(A_212) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2319,c_2642])).

tff(c_2893,plain,(
    ! [A_212] :
      ( ~ v1_xboole_0(A_212)
      | ~ v1_xboole_0(A_212) ) ),
    inference(splitLeft,[status(thm)],[c_2665])).

tff(c_15401,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_15229,c_2893])).

tff(c_15425,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_15229,c_15401])).

tff(c_15426,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_2665])).

tff(c_667,plain,(
    ! [A_189] :
      ( ~ v1_xboole_0(k1_relat_1(A_189))
      | k1_xboole_0 = A_189
      | ~ v1_relat_1(A_189) ) ),
    inference(resolution,[status(thm)],[c_640,c_4])).

tff(c_676,plain,(
    ! [A_90] :
      ( ~ v1_xboole_0(A_90)
      | '#skF_16'(A_90) = k1_xboole_0
      | ~ v1_relat_1('#skF_16'(A_90)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_667])).

tff(c_685,plain,(
    ! [A_90] :
      ( ~ v1_xboole_0(A_90)
      | '#skF_16'(A_90) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_676])).

tff(c_15444,plain,(
    '#skF_16'(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_15426,c_685])).

tff(c_1070,plain,(
    ! [A_90,C_213] :
      ( ~ v1_xboole_0('#skF_16'(A_90))
      | ~ r2_hidden(C_213,A_90) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_1024])).

tff(c_15470,plain,(
    ! [C_213] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(C_213,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_15444,c_1070])).

tff(c_15528,plain,(
    ! [C_213] : ~ r2_hidden(C_213,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15426,c_15470])).

tff(c_109,plain,(
    ! [B_111,A_84] :
      ( B_111 = '#skF_15'(A_84)
      | k1_relat_1('#skF_15'(A_84)) != '#skF_17'
      | k1_relat_1(B_111) != '#skF_17'
      | ~ v1_funct_1('#skF_15'(A_84))
      | ~ v1_funct_1(B_111)
      | ~ v1_relat_1(B_111) ) ),
    inference(resolution,[status(thm)],[c_78,c_105])).

tff(c_117,plain,(
    ! [B_111,A_84] :
      ( B_111 = '#skF_15'(A_84)
      | k1_relat_1('#skF_15'(A_84)) != '#skF_17'
      | k1_relat_1(B_111) != '#skF_17'
      | ~ v1_funct_1(B_111)
      | ~ v1_relat_1(B_111) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_109])).

tff(c_282,plain,(
    ! [B_144,A_145] :
      ( B_144 = '#skF_15'(A_145)
      | A_145 != '#skF_17'
      | k1_relat_1(B_144) != '#skF_17'
      | ~ v1_funct_1(B_144)
      | ~ v1_relat_1(B_144) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_117])).

tff(c_284,plain,(
    ! [A_145,A_77,B_78] :
      ( '#skF_15'(A_145) = '#skF_14'(A_77,B_78)
      | A_145 != '#skF_17'
      | k1_relat_1('#skF_14'(A_77,B_78)) != '#skF_17'
      | ~ v1_funct_1('#skF_14'(A_77,B_78)) ) ),
    inference(resolution,[status(thm)],[c_70,c_282])).

tff(c_291,plain,(
    ! [A_145,A_77,B_78] :
      ( '#skF_15'(A_145) = '#skF_14'(A_77,B_78)
      | A_145 != '#skF_17'
      | A_77 != '#skF_17' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_284])).

tff(c_1220,plain,(
    ! [A_222] :
      ( v1_relat_1(k1_xboole_0)
      | ~ v1_xboole_0(A_222) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1183,c_78])).

tff(c_1280,plain,(
    ! [A_222] : ~ v1_xboole_0(A_222) ),
    inference(splitLeft,[status(thm)],[c_1220])).

tff(c_1285,plain,(
    ! [A_3] : r2_hidden('#skF_1'(A_3),A_3) ),
    inference(negUnitSimplification,[status(thm)],[c_1280,c_6])).

tff(c_1620,plain,(
    ! [B_253,A_254,D_255] :
      ( r2_hidden(B_253,k2_relat_1('#skF_14'(A_254,B_253)))
      | ~ r2_hidden(D_255,A_254) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_1261])).

tff(c_1677,plain,(
    ! [B_256,A_257] : r2_hidden(B_256,k2_relat_1('#skF_14'(A_257,B_256))) ),
    inference(resolution,[status(thm)],[c_1285,c_1620])).

tff(c_1695,plain,(
    ! [B_78,A_145,A_77] :
      ( r2_hidden(B_78,k2_relat_1('#skF_15'(A_145)))
      | A_145 != '#skF_17'
      | A_77 != '#skF_17' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_291,c_1677])).

tff(c_1718,plain,(
    ! [A_77] : A_77 != '#skF_17' ),
    inference(splitLeft,[status(thm)],[c_1695])).

tff(c_1722,plain,(
    $false ),
    inference(reflexivity,[status(thm),theory(equality)],[c_1718])).

tff(c_1725,plain,(
    ! [B_263,A_264] :
      ( r2_hidden(B_263,k2_relat_1('#skF_15'(A_264)))
      | A_264 != '#skF_17' ) ),
    inference(splitRight,[status(thm)],[c_1695])).

tff(c_1697,plain,(
    ! [A_257,B_256] : ~ r2_hidden(k2_relat_1('#skF_14'(A_257,B_256)),B_256) ),
    inference(resolution,[status(thm)],[c_1677,c_2])).

tff(c_1775,plain,(
    ! [A_264] : A_264 != '#skF_17' ),
    inference(resolution,[status(thm)],[c_1725,c_1697])).

tff(c_1788,plain,(
    $false ),
    inference(reflexivity,[status(thm),theory(equality)],[c_1775])).

tff(c_1789,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_1220])).

tff(c_1222,plain,(
    ! [A_222] :
      ( v1_funct_1(k1_xboole_0)
      | ~ v1_xboole_0(A_222) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1183,c_76])).

tff(c_1806,plain,(
    ! [A_222] : ~ v1_xboole_0(A_222) ),
    inference(splitLeft,[status(thm)],[c_1222])).

tff(c_1812,plain,(
    ! [A_3] : r2_hidden('#skF_1'(A_3),A_3) ),
    inference(negUnitSimplification,[status(thm)],[c_1806,c_6])).

tff(c_2153,plain,(
    ! [B_296,A_297,D_298] :
      ( r2_hidden(B_296,k2_relat_1('#skF_14'(A_297,B_296)))
      | ~ r2_hidden(D_298,A_297) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_1261])).

tff(c_2209,plain,(
    ! [B_299,A_300] : r2_hidden(B_299,k2_relat_1('#skF_14'(A_300,B_299))) ),
    inference(resolution,[status(thm)],[c_1812,c_2153])).

tff(c_2224,plain,(
    ! [B_78,A_128,A_77] :
      ( r2_hidden(B_78,k2_relat_1('#skF_16'(A_128)))
      | A_128 != '#skF_17'
      | A_77 != '#skF_17' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_186,c_2209])).

tff(c_2243,plain,(
    ! [A_77] : A_77 != '#skF_17' ),
    inference(splitLeft,[status(thm)],[c_2224])).

tff(c_2247,plain,(
    $false ),
    inference(reflexivity,[status(thm),theory(equality)],[c_2243])).

tff(c_2250,plain,(
    ! [B_303,A_304] :
      ( r2_hidden(B_303,k2_relat_1('#skF_16'(A_304)))
      | A_304 != '#skF_17' ) ),
    inference(splitRight,[status(thm)],[c_2224])).

tff(c_2229,plain,(
    ! [A_300,B_299] : ~ r2_hidden(k2_relat_1('#skF_14'(A_300,B_299)),B_299) ),
    inference(resolution,[status(thm)],[c_2209,c_2])).

tff(c_2299,plain,(
    ! [A_304] : A_304 != '#skF_17' ),
    inference(resolution,[status(thm)],[c_2250,c_2229])).

tff(c_2313,plain,(
    $false ),
    inference(reflexivity,[status(thm),theory(equality)],[c_2299])).

tff(c_2314,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_1222])).

tff(c_42,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_17084,plain,(
    ! [A_29452,B_29453] :
      ( r2_hidden('#skF_11'(A_29452,B_29453),k1_relat_1(A_29452))
      | r2_hidden('#skF_12'(A_29452,B_29453),B_29453)
      | k2_relat_1(A_29452) = B_29453
      | ~ v1_funct_1(A_29452)
      | ~ v1_relat_1(A_29452) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_17147,plain,(
    ! [B_29453] :
      ( r2_hidden('#skF_11'(k1_xboole_0,B_29453),k1_xboole_0)
      | r2_hidden('#skF_12'(k1_xboole_0,B_29453),B_29453)
      | k2_relat_1(k1_xboole_0) = B_29453
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_17084])).

tff(c_17170,plain,(
    ! [B_29453] :
      ( r2_hidden('#skF_11'(k1_xboole_0,B_29453),k1_xboole_0)
      | r2_hidden('#skF_12'(k1_xboole_0,B_29453),B_29453)
      | k1_xboole_0 = B_29453 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1789,c_2314,c_42,c_17147])).

tff(c_17172,plain,(
    ! [B_29454] :
      ( r2_hidden('#skF_12'(k1_xboole_0,B_29454),B_29454)
      | k1_xboole_0 = B_29454 ) ),
    inference(negUnitSimplification,[status(thm)],[c_15528,c_17170])).

tff(c_17210,plain,(
    ! [B_29454] :
      ( ~ v1_xboole_0(B_29454)
      | k1_xboole_0 = B_29454 ) ),
    inference(resolution,[status(thm)],[c_17172,c_4])).

tff(c_121612,plain,(
    k1_xboole_0 = '#skF_17' ),
    inference(resolution,[status(thm)],[c_121322,c_17210])).

tff(c_88,plain,(
    k1_xboole_0 != '#skF_17' ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_121679,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_121612,c_88])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:39:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 23.61/13.61  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 23.68/13.62  
% 23.68/13.62  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 23.68/13.62  %$ r2_hidden > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_enumset1 > k4_tarski > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > np__1 > k1_xboole_0 > #skF_13 > #skF_9 > #skF_11 > #skF_16 > #skF_6 > #skF_17 > #skF_1 > #skF_8 > #skF_14 > #skF_15 > #skF_12 > #skF_10 > #skF_2 > #skF_7 > #skF_3 > #skF_5 > #skF_4
% 23.68/13.62  
% 23.68/13.62  %Foreground sorts:
% 23.68/13.62  
% 23.68/13.62  
% 23.68/13.62  %Background operators:
% 23.68/13.62  
% 23.68/13.62  
% 23.68/13.62  %Foreground operators:
% 23.68/13.62  tff('#skF_13', type, '#skF_13': ($i * $i * $i) > $i).
% 23.68/13.62  tff('#skF_9', type, '#skF_9': $i > $i).
% 23.68/13.62  tff('#skF_11', type, '#skF_11': ($i * $i) > $i).
% 23.68/13.62  tff(np__1, type, np__1: $i).
% 23.68/13.62  tff('#skF_16', type, '#skF_16': $i > $i).
% 23.68/13.62  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 23.68/13.62  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 23.68/13.62  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 23.68/13.62  tff('#skF_17', type, '#skF_17': $i).
% 23.68/13.62  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 23.68/13.62  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 23.68/13.62  tff('#skF_1', type, '#skF_1': $i > $i).
% 23.68/13.62  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 23.68/13.62  tff('#skF_8', type, '#skF_8': $i > $i).
% 23.68/13.62  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 23.68/13.62  tff('#skF_14', type, '#skF_14': ($i * $i) > $i).
% 23.68/13.62  tff('#skF_15', type, '#skF_15': $i > $i).
% 23.68/13.62  tff('#skF_12', type, '#skF_12': ($i * $i) > $i).
% 23.68/13.62  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 23.68/13.62  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 23.68/13.62  tff('#skF_10', type, '#skF_10': ($i * $i) > $i).
% 23.68/13.62  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 23.68/13.62  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 23.68/13.62  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 23.68/13.62  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 23.68/13.62  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 23.68/13.62  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 23.68/13.62  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 23.68/13.62  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 23.68/13.62  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 23.68/13.62  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 23.68/13.62  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 23.68/13.62  
% 23.68/13.65  tff(f_93, axiom, (![A, B]: (?[C]: (((v1_relat_1(C) & v1_funct_1(C)) & (k1_relat_1(C) = A)) & (![D]: (r2_hidden(D, A) => (k1_funct_1(C, D) = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', s3_funct_1__e2_24__funct_1)).
% 23.68/13.65  tff(f_117, axiom, (![A]: (?[B]: (((v1_relat_1(B) & v1_funct_1(B)) & (k1_relat_1(B) = A)) & (![C]: (r2_hidden(C, A) => (k1_funct_1(B, C) = np__1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', s3_funct_1__e7_25__funct_1)).
% 23.68/13.65  tff(f_136, negated_conjecture, ~(![A]: ((![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (((k1_relat_1(B) = A) & (k1_relat_1(C) = A)) => (B = C)))))) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_funct_1)).
% 23.68/13.65  tff(f_36, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 23.68/13.65  tff(f_81, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_funct_1)).
% 23.68/13.65  tff(f_45, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 23.68/13.65  tff(f_30, axiom, (![A, B]: (r2_hidden(A, B) => ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', antisymmetry_r2_hidden)).
% 23.68/13.65  tff(f_105, axiom, (![A]: (?[B]: (((v1_relat_1(B) & v1_funct_1(B)) & (k1_relat_1(B) = A)) & (![C]: (r2_hidden(C, A) => (k1_funct_1(B, C) = k1_xboole_0)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', s3_funct_1__e2_25__funct_1)).
% 23.68/13.65  tff(f_66, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 23.68/13.65  tff(f_63, axiom, (![A]: (v1_relat_1(A) => ((![B, C]: ~r2_hidden(k4_tarski(B, C), A)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_relat_1)).
% 23.68/13.65  tff(f_55, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_relat_1)).
% 23.68/13.65  tff(c_68, plain, (![A_77, B_78]: (v1_funct_1('#skF_14'(A_77, B_78)))), inference(cnfTransformation, [status(thm)], [f_93])).
% 23.68/13.65  tff(c_66, plain, (![A_77, B_78]: (k1_relat_1('#skF_14'(A_77, B_78))=A_77)), inference(cnfTransformation, [status(thm)], [f_93])).
% 23.68/13.65  tff(c_70, plain, (![A_77, B_78]: (v1_relat_1('#skF_14'(A_77, B_78)))), inference(cnfTransformation, [status(thm)], [f_93])).
% 23.68/13.65  tff(c_82, plain, (![A_90]: (k1_relat_1('#skF_16'(A_90))=A_90)), inference(cnfTransformation, [status(thm)], [f_117])).
% 23.68/13.65  tff(c_84, plain, (![A_90]: (v1_funct_1('#skF_16'(A_90)))), inference(cnfTransformation, [status(thm)], [f_117])).
% 23.68/13.65  tff(c_86, plain, (![A_90]: (v1_relat_1('#skF_16'(A_90)))), inference(cnfTransformation, [status(thm)], [f_117])).
% 23.68/13.65  tff(c_105, plain, (![C_110, B_111]: (C_110=B_111 | k1_relat_1(C_110)!='#skF_17' | k1_relat_1(B_111)!='#skF_17' | ~v1_funct_1(C_110) | ~v1_relat_1(C_110) | ~v1_funct_1(B_111) | ~v1_relat_1(B_111))), inference(cnfTransformation, [status(thm)], [f_136])).
% 23.68/13.65  tff(c_111, plain, (![B_111, A_90]: (B_111='#skF_16'(A_90) | k1_relat_1('#skF_16'(A_90))!='#skF_17' | k1_relat_1(B_111)!='#skF_17' | ~v1_funct_1('#skF_16'(A_90)) | ~v1_funct_1(B_111) | ~v1_relat_1(B_111))), inference(resolution, [status(thm)], [c_86, c_105])).
% 23.68/13.65  tff(c_120, plain, (![B_111, A_90]: (B_111='#skF_16'(A_90) | k1_relat_1('#skF_16'(A_90))!='#skF_17' | k1_relat_1(B_111)!='#skF_17' | ~v1_funct_1(B_111) | ~v1_relat_1(B_111))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_111])).
% 23.68/13.65  tff(c_177, plain, (![B_127, A_128]: (B_127='#skF_16'(A_128) | A_128!='#skF_17' | k1_relat_1(B_127)!='#skF_17' | ~v1_funct_1(B_127) | ~v1_relat_1(B_127))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_120])).
% 23.68/13.65  tff(c_179, plain, (![A_128, A_77, B_78]: ('#skF_16'(A_128)='#skF_14'(A_77, B_78) | A_128!='#skF_17' | k1_relat_1('#skF_14'(A_77, B_78))!='#skF_17' | ~v1_funct_1('#skF_14'(A_77, B_78)))), inference(resolution, [status(thm)], [c_70, c_177])).
% 23.68/13.65  tff(c_186, plain, (![A_128, A_77, B_78]: ('#skF_16'(A_128)='#skF_14'(A_77, B_78) | A_128!='#skF_17' | A_77!='#skF_17')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_179])).
% 23.68/13.65  tff(c_6, plain, (![A_3]: (v1_xboole_0(A_3) | r2_hidden('#skF_1'(A_3), A_3))), inference(cnfTransformation, [status(thm)], [f_36])).
% 23.68/13.65  tff(c_64, plain, (![A_77, B_78, D_83]: (k1_funct_1('#skF_14'(A_77, B_78), D_83)=B_78 | ~r2_hidden(D_83, A_77))), inference(cnfTransformation, [status(thm)], [f_93])).
% 23.68/13.65  tff(c_1253, plain, (![A_223, D_224]: (r2_hidden(k1_funct_1(A_223, D_224), k2_relat_1(A_223)) | ~r2_hidden(D_224, k1_relat_1(A_223)) | ~v1_funct_1(A_223) | ~v1_relat_1(A_223))), inference(cnfTransformation, [status(thm)], [f_81])).
% 23.68/13.65  tff(c_1261, plain, (![B_78, A_77, D_83]: (r2_hidden(B_78, k2_relat_1('#skF_14'(A_77, B_78))) | ~r2_hidden(D_83, k1_relat_1('#skF_14'(A_77, B_78))) | ~v1_funct_1('#skF_14'(A_77, B_78)) | ~v1_relat_1('#skF_14'(A_77, B_78)) | ~r2_hidden(D_83, A_77))), inference(superposition, [status(thm), theory('equality')], [c_64, c_1253])).
% 23.68/13.65  tff(c_76755, plain, (![B_94334, A_94335, D_94336]: (r2_hidden(B_94334, k2_relat_1('#skF_14'(A_94335, B_94334))) | ~r2_hidden(D_94336, A_94335))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_1261])).
% 23.68/13.65  tff(c_77350, plain, (![B_95192, A_95193]: (r2_hidden(B_95192, k2_relat_1('#skF_14'(A_95193, B_95192))) | v1_xboole_0(A_95193))), inference(resolution, [status(thm)], [c_6, c_76755])).
% 23.68/13.65  tff(c_77384, plain, (![B_78, A_128, A_77]: (r2_hidden(B_78, k2_relat_1('#skF_16'(A_128))) | v1_xboole_0(A_77) | A_128!='#skF_17' | A_77!='#skF_17')), inference(superposition, [status(thm), theory('equality')], [c_186, c_77350])).
% 23.68/13.65  tff(c_120552, plain, (![A_135303]: (v1_xboole_0(A_135303) | A_135303!='#skF_17')), inference(splitLeft, [status(thm)], [c_77384])).
% 23.68/13.65  tff(c_15719, plain, (![A_29391, C_29392]: (r2_hidden('#skF_13'(A_29391, k2_relat_1(A_29391), C_29392), k1_relat_1(A_29391)) | ~r2_hidden(C_29392, k2_relat_1(A_29391)) | ~v1_funct_1(A_29391) | ~v1_relat_1(A_29391))), inference(cnfTransformation, [status(thm)], [f_81])).
% 23.68/13.65  tff(c_15743, plain, (![A_90, C_29392]: (r2_hidden('#skF_13'('#skF_16'(A_90), k2_relat_1('#skF_16'(A_90)), C_29392), A_90) | ~r2_hidden(C_29392, k2_relat_1('#skF_16'(A_90))) | ~v1_funct_1('#skF_16'(A_90)) | ~v1_relat_1('#skF_16'(A_90)))), inference(superposition, [status(thm), theory('equality')], [c_82, c_15719])).
% 23.68/13.65  tff(c_84257, plain, (![A_110958, C_110959]: (r2_hidden('#skF_13'('#skF_16'(A_110958), k2_relat_1('#skF_16'(A_110958)), C_110959), A_110958) | ~r2_hidden(C_110959, k2_relat_1('#skF_16'(A_110958))))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_84, c_15743])).
% 23.68/13.65  tff(c_4, plain, (![B_6, A_3]: (~r2_hidden(B_6, A_3) | ~v1_xboole_0(A_3))), inference(cnfTransformation, [status(thm)], [f_36])).
% 23.68/13.65  tff(c_84411, plain, (![A_111086, C_111087]: (~v1_xboole_0(A_111086) | ~r2_hidden(C_111087, k2_relat_1('#skF_16'(A_111086))))), inference(resolution, [status(thm)], [c_84257, c_4])).
% 23.68/13.65  tff(c_84562, plain, (![A_111214]: (~v1_xboole_0(A_111214) | v1_xboole_0(k2_relat_1('#skF_16'(A_111214))))), inference(resolution, [status(thm)], [c_6, c_84411])).
% 23.68/13.65  tff(c_77398, plain, (![A_95278, B_95279]: (~v1_xboole_0(k2_relat_1('#skF_14'(A_95278, B_95279))) | v1_xboole_0(A_95278))), inference(resolution, [status(thm)], [c_77350, c_4])).
% 23.68/13.65  tff(c_77417, plain, (![A_128, A_77]: (~v1_xboole_0(k2_relat_1('#skF_16'(A_128))) | v1_xboole_0(A_77) | A_128!='#skF_17' | A_77!='#skF_17')), inference(superposition, [status(thm), theory('equality')], [c_186, c_77398])).
% 23.68/13.65  tff(c_77425, plain, (![A_128]: (~v1_xboole_0(k2_relat_1('#skF_16'(A_128))) | A_128!='#skF_17')), inference(splitLeft, [status(thm)], [c_77417])).
% 23.68/13.65  tff(c_84643, plain, (![A_111214]: (A_111214!='#skF_17' | ~v1_xboole_0(A_111214))), inference(resolution, [status(thm)], [c_84562, c_77425])).
% 23.68/13.65  tff(c_120958, plain, (![A_135303]: (A_135303!='#skF_17')), inference(resolution, [status(thm)], [c_120552, c_84643])).
% 23.68/13.65  tff(c_121056, plain, $false, inference(reflexivity, [status(thm), theory('equality')], [c_120958])).
% 23.68/13.65  tff(c_121059, plain, (![B_135430, A_135431]: (r2_hidden(B_135430, k2_relat_1('#skF_16'(A_135431))) | A_135431!='#skF_17')), inference(splitRight, [status(thm)], [c_77384])).
% 23.68/13.65  tff(c_12, plain, (![D_12, B_8]: (r2_hidden(D_12, k2_tarski(D_12, B_8)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 23.68/13.65  tff(c_77081, plain, (![B_94846, D_94847, B_94848]: (r2_hidden(B_94846, k2_relat_1('#skF_14'(k2_tarski(D_94847, B_94848), B_94846))))), inference(resolution, [status(thm)], [c_12, c_76755])).
% 23.68/13.65  tff(c_2, plain, (![B_2, A_1]: (~r2_hidden(B_2, A_1) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_30])).
% 23.68/13.65  tff(c_77235, plain, (![D_94847, B_94848, B_94846]: (~r2_hidden(k2_relat_1('#skF_14'(k2_tarski(D_94847, B_94848), B_94846)), B_94846))), inference(resolution, [status(thm)], [c_77081, c_2])).
% 23.68/13.65  tff(c_121260, plain, (![A_135431]: (A_135431!='#skF_17')), inference(resolution, [status(thm)], [c_121059, c_77235])).
% 23.68/13.65  tff(c_121319, plain, $false, inference(reflexivity, [status(thm), theory('equality')], [c_121260])).
% 23.68/13.65  tff(c_121322, plain, (![A_135558]: (v1_xboole_0(A_135558) | A_135558!='#skF_17')), inference(splitRight, [status(thm)], [c_77417])).
% 23.68/13.65  tff(c_78, plain, (![A_84]: (v1_relat_1('#skF_15'(A_84)))), inference(cnfTransformation, [status(thm)], [f_105])).
% 23.68/13.65  tff(c_76, plain, (![A_84]: (v1_funct_1('#skF_15'(A_84)))), inference(cnfTransformation, [status(thm)], [f_105])).
% 23.68/13.65  tff(c_74, plain, (![A_84]: (k1_relat_1('#skF_15'(A_84))=A_84)), inference(cnfTransformation, [status(thm)], [f_105])).
% 23.68/13.65  tff(c_44, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_66])).
% 23.68/13.65  tff(c_622, plain, (![A_186]: (k1_xboole_0=A_186 | r2_hidden(k4_tarski('#skF_8'(A_186), '#skF_9'(A_186)), A_186) | ~v1_relat_1(A_186))), inference(cnfTransformation, [status(thm)], [f_63])).
% 23.68/13.65  tff(c_30, plain, (![C_30, A_15, D_33]: (r2_hidden(C_30, k1_relat_1(A_15)) | ~r2_hidden(k4_tarski(C_30, D_33), A_15))), inference(cnfTransformation, [status(thm)], [f_55])).
% 23.68/13.65  tff(c_640, plain, (![A_188]: (r2_hidden('#skF_8'(A_188), k1_relat_1(A_188)) | k1_xboole_0=A_188 | ~v1_relat_1(A_188))), inference(resolution, [status(thm)], [c_622, c_30])).
% 23.68/13.65  tff(c_651, plain, (![A_84]: (r2_hidden('#skF_8'('#skF_15'(A_84)), A_84) | '#skF_15'(A_84)=k1_xboole_0 | ~v1_relat_1('#skF_15'(A_84)))), inference(superposition, [status(thm), theory('equality')], [c_74, c_640])).
% 23.68/13.65  tff(c_663, plain, (![A_84]: (r2_hidden('#skF_8'('#skF_15'(A_84)), A_84) | '#skF_15'(A_84)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_78, c_651])).
% 23.68/13.65  tff(c_3305, plain, (![A_359, C_360]: (r2_hidden('#skF_13'(A_359, k2_relat_1(A_359), C_360), k1_relat_1(A_359)) | ~r2_hidden(C_360, k2_relat_1(A_359)) | ~v1_funct_1(A_359) | ~v1_relat_1(A_359))), inference(cnfTransformation, [status(thm)], [f_81])).
% 23.68/13.65  tff(c_3326, plain, (![A_84, C_360]: (r2_hidden('#skF_13'('#skF_15'(A_84), k2_relat_1('#skF_15'(A_84)), C_360), A_84) | ~r2_hidden(C_360, k2_relat_1('#skF_15'(A_84))) | ~v1_funct_1('#skF_15'(A_84)) | ~v1_relat_1('#skF_15'(A_84)))), inference(superposition, [status(thm), theory('equality')], [c_74, c_3305])).
% 23.68/13.65  tff(c_12560, plain, (![A_23100, C_23101]: (r2_hidden('#skF_13'('#skF_15'(A_23100), k2_relat_1('#skF_15'(A_23100)), C_23101), A_23100) | ~r2_hidden(C_23101, k2_relat_1('#skF_15'(A_23100))))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_3326])).
% 23.68/13.65  tff(c_12687, plain, (![A_23186, C_23187]: (~v1_xboole_0(A_23186) | ~r2_hidden(C_23187, k2_relat_1('#skF_15'(A_23186))))), inference(resolution, [status(thm)], [c_12560, c_4])).
% 23.68/13.65  tff(c_13005, plain, (![A_23612]: (~v1_xboole_0(A_23612) | '#skF_15'(k2_relat_1('#skF_15'(A_23612)))=k1_xboole_0)), inference(resolution, [status(thm)], [c_663, c_12687])).
% 23.68/13.65  tff(c_13173, plain, (![A_23612]: (k2_relat_1('#skF_15'(A_23612))=k1_relat_1(k1_xboole_0) | ~v1_xboole_0(A_23612))), inference(superposition, [status(thm), theory('equality')], [c_13005, c_74])).
% 23.68/13.65  tff(c_13251, plain, (![A_23697]: (k2_relat_1('#skF_15'(A_23697))=k1_xboole_0 | ~v1_xboole_0(A_23697))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_13173])).
% 23.68/13.65  tff(c_3339, plain, (![A_359, C_360]: (~v1_xboole_0(k1_relat_1(A_359)) | ~r2_hidden(C_360, k2_relat_1(A_359)) | ~v1_funct_1(A_359) | ~v1_relat_1(A_359))), inference(resolution, [status(thm)], [c_3305, c_4])).
% 23.68/13.65  tff(c_13295, plain, (![A_23697, C_360]: (~v1_xboole_0(k1_relat_1('#skF_15'(A_23697))) | ~r2_hidden(C_360, k1_xboole_0) | ~v1_funct_1('#skF_15'(A_23697)) | ~v1_relat_1('#skF_15'(A_23697)) | ~v1_xboole_0(A_23697))), inference(superposition, [status(thm), theory('equality')], [c_13251, c_3339])).
% 23.68/13.65  tff(c_13361, plain, (![C_360, A_23697]: (~r2_hidden(C_360, k1_xboole_0) | ~v1_xboole_0(A_23697))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_74, c_13295])).
% 23.68/13.65  tff(c_13373, plain, (![A_23697]: (~v1_xboole_0(A_23697))), inference(splitLeft, [status(thm)], [c_13361])).
% 23.68/13.65  tff(c_8188, plain, (![B_16259, A_16260, D_16261]: (r2_hidden(B_16259, k2_relat_1('#skF_14'(A_16260, B_16259))) | ~r2_hidden(D_16261, A_16260))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_1261])).
% 23.68/13.65  tff(c_8258, plain, (![B_16259, A_3]: (r2_hidden(B_16259, k2_relat_1('#skF_14'(A_3, B_16259))) | v1_xboole_0(A_3))), inference(resolution, [status(thm)], [c_6, c_8188])).
% 23.68/13.65  tff(c_14992, plain, (![B_28623, A_28624]: (r2_hidden(B_28623, k2_relat_1('#skF_14'(A_28624, B_28623))))), inference(negUnitSimplification, [status(thm)], [c_13373, c_8258])).
% 23.68/13.65  tff(c_15013, plain, (![B_78, A_128, A_77]: (r2_hidden(B_78, k2_relat_1('#skF_16'(A_128))) | A_128!='#skF_17' | A_77!='#skF_17')), inference(superposition, [status(thm), theory('equality')], [c_186, c_14992])).
% 23.68/13.65  tff(c_15063, plain, (![A_77]: (A_77!='#skF_17')), inference(splitLeft, [status(thm)], [c_15013])).
% 23.68/13.65  tff(c_15067, plain, $false, inference(reflexivity, [status(thm), theory('equality')], [c_15063])).
% 23.68/13.65  tff(c_15071, plain, (![B_29006, A_29007]: (r2_hidden(B_29006, k2_relat_1('#skF_16'(A_29007))) | A_29007!='#skF_17')), inference(splitRight, [status(thm)], [c_15013])).
% 23.68/13.65  tff(c_8284, plain, (![B_16432, A_16433]: (r2_hidden(B_16432, k2_relat_1('#skF_14'(A_16433, B_16432))) | v1_xboole_0(A_16433))), inference(resolution, [status(thm)], [c_6, c_8188])).
% 23.68/13.65  tff(c_8323, plain, (![A_16433, B_16432]: (~r2_hidden(k2_relat_1('#skF_14'(A_16433, B_16432)), B_16432) | v1_xboole_0(A_16433))), inference(resolution, [status(thm)], [c_8284, c_2])).
% 23.68/13.65  tff(c_13530, plain, (![A_16433, B_16432]: (~r2_hidden(k2_relat_1('#skF_14'(A_16433, B_16432)), B_16432))), inference(negUnitSimplification, [status(thm)], [c_13373, c_8323])).
% 23.68/13.65  tff(c_15136, plain, (![A_29007]: (A_29007!='#skF_17')), inference(resolution, [status(thm)], [c_15071, c_13530])).
% 23.68/13.65  tff(c_15153, plain, $false, inference(reflexivity, [status(thm), theory('equality')], [c_15136])).
% 23.68/13.65  tff(c_15157, plain, (![C_29134]: (~r2_hidden(C_29134, k1_xboole_0))), inference(splitRight, [status(thm)], [c_13361])).
% 23.68/13.65  tff(c_15229, plain, (v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_15157])).
% 23.68/13.65  tff(c_991, plain, (![C_210, A_211]: (r2_hidden(k4_tarski(C_210, '#skF_7'(A_211, k1_relat_1(A_211), C_210)), A_211) | ~r2_hidden(C_210, k1_relat_1(A_211)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 23.68/13.65  tff(c_1024, plain, (![A_212, C_213]: (~v1_xboole_0(A_212) | ~r2_hidden(C_213, k1_relat_1(A_212)))), inference(resolution, [status(thm)], [c_991, c_4])).
% 23.68/13.65  tff(c_1083, plain, (![A_212]: (~v1_xboole_0(A_212) | v1_xboole_0(k1_relat_1(A_212)))), inference(resolution, [status(thm)], [c_6, c_1024])).
% 23.68/13.65  tff(c_1183, plain, (![A_222]: (~v1_xboole_0(A_222) | '#skF_15'(k1_relat_1(A_222))=k1_xboole_0)), inference(resolution, [status(thm)], [c_663, c_1024])).
% 23.68/13.65  tff(c_1218, plain, (![A_222]: (k1_relat_1(k1_xboole_0)=k1_relat_1(A_222) | ~v1_xboole_0(A_222))), inference(superposition, [status(thm), theory('equality')], [c_1183, c_74])).
% 23.68/13.65  tff(c_2315, plain, (![A_305]: (k1_relat_1(A_305)=k1_xboole_0 | ~v1_xboole_0(A_305))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_1218])).
% 23.68/13.65  tff(c_2319, plain, (![A_212]: (k1_relat_1(k1_relat_1(A_212))=k1_xboole_0 | ~v1_xboole_0(A_212))), inference(resolution, [status(thm)], [c_1083, c_2315])).
% 23.68/13.65  tff(c_28, plain, (![C_30, A_15]: (r2_hidden(k4_tarski(C_30, '#skF_7'(A_15, k1_relat_1(A_15), C_30)), A_15) | ~r2_hidden(C_30, k1_relat_1(A_15)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 23.68/13.65  tff(c_2581, plain, (![A_326, C_327]: (~v1_xboole_0(A_326) | ~r2_hidden(C_327, k1_relat_1(k1_relat_1(A_326))))), inference(resolution, [status(thm)], [c_28, c_1024])).
% 23.68/13.65  tff(c_2642, plain, (![A_328]: (~v1_xboole_0(A_328) | v1_xboole_0(k1_relat_1(k1_relat_1(A_328))))), inference(resolution, [status(thm)], [c_6, c_2581])).
% 23.68/13.65  tff(c_2665, plain, (![A_212]: (~v1_xboole_0(A_212) | v1_xboole_0(k1_xboole_0) | ~v1_xboole_0(A_212))), inference(superposition, [status(thm), theory('equality')], [c_2319, c_2642])).
% 23.68/13.65  tff(c_2893, plain, (![A_212]: (~v1_xboole_0(A_212) | ~v1_xboole_0(A_212))), inference(splitLeft, [status(thm)], [c_2665])).
% 23.68/13.65  tff(c_15401, plain, (~v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_15229, c_2893])).
% 23.68/13.65  tff(c_15425, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_15229, c_15401])).
% 23.68/13.65  tff(c_15426, plain, (v1_xboole_0(k1_xboole_0)), inference(splitRight, [status(thm)], [c_2665])).
% 23.68/13.65  tff(c_667, plain, (![A_189]: (~v1_xboole_0(k1_relat_1(A_189)) | k1_xboole_0=A_189 | ~v1_relat_1(A_189))), inference(resolution, [status(thm)], [c_640, c_4])).
% 23.68/13.65  tff(c_676, plain, (![A_90]: (~v1_xboole_0(A_90) | '#skF_16'(A_90)=k1_xboole_0 | ~v1_relat_1('#skF_16'(A_90)))), inference(superposition, [status(thm), theory('equality')], [c_82, c_667])).
% 23.68/13.65  tff(c_685, plain, (![A_90]: (~v1_xboole_0(A_90) | '#skF_16'(A_90)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_86, c_676])).
% 23.68/13.65  tff(c_15444, plain, ('#skF_16'(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_15426, c_685])).
% 23.68/13.65  tff(c_1070, plain, (![A_90, C_213]: (~v1_xboole_0('#skF_16'(A_90)) | ~r2_hidden(C_213, A_90))), inference(superposition, [status(thm), theory('equality')], [c_82, c_1024])).
% 23.68/13.65  tff(c_15470, plain, (![C_213]: (~v1_xboole_0(k1_xboole_0) | ~r2_hidden(C_213, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_15444, c_1070])).
% 23.68/13.65  tff(c_15528, plain, (![C_213]: (~r2_hidden(C_213, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_15426, c_15470])).
% 23.68/13.65  tff(c_109, plain, (![B_111, A_84]: (B_111='#skF_15'(A_84) | k1_relat_1('#skF_15'(A_84))!='#skF_17' | k1_relat_1(B_111)!='#skF_17' | ~v1_funct_1('#skF_15'(A_84)) | ~v1_funct_1(B_111) | ~v1_relat_1(B_111))), inference(resolution, [status(thm)], [c_78, c_105])).
% 23.68/13.65  tff(c_117, plain, (![B_111, A_84]: (B_111='#skF_15'(A_84) | k1_relat_1('#skF_15'(A_84))!='#skF_17' | k1_relat_1(B_111)!='#skF_17' | ~v1_funct_1(B_111) | ~v1_relat_1(B_111))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_109])).
% 23.68/13.65  tff(c_282, plain, (![B_144, A_145]: (B_144='#skF_15'(A_145) | A_145!='#skF_17' | k1_relat_1(B_144)!='#skF_17' | ~v1_funct_1(B_144) | ~v1_relat_1(B_144))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_117])).
% 23.68/13.65  tff(c_284, plain, (![A_145, A_77, B_78]: ('#skF_15'(A_145)='#skF_14'(A_77, B_78) | A_145!='#skF_17' | k1_relat_1('#skF_14'(A_77, B_78))!='#skF_17' | ~v1_funct_1('#skF_14'(A_77, B_78)))), inference(resolution, [status(thm)], [c_70, c_282])).
% 23.68/13.65  tff(c_291, plain, (![A_145, A_77, B_78]: ('#skF_15'(A_145)='#skF_14'(A_77, B_78) | A_145!='#skF_17' | A_77!='#skF_17')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_284])).
% 23.68/13.65  tff(c_1220, plain, (![A_222]: (v1_relat_1(k1_xboole_0) | ~v1_xboole_0(A_222))), inference(superposition, [status(thm), theory('equality')], [c_1183, c_78])).
% 23.68/13.65  tff(c_1280, plain, (![A_222]: (~v1_xboole_0(A_222))), inference(splitLeft, [status(thm)], [c_1220])).
% 23.68/13.65  tff(c_1285, plain, (![A_3]: (r2_hidden('#skF_1'(A_3), A_3))), inference(negUnitSimplification, [status(thm)], [c_1280, c_6])).
% 23.68/13.65  tff(c_1620, plain, (![B_253, A_254, D_255]: (r2_hidden(B_253, k2_relat_1('#skF_14'(A_254, B_253))) | ~r2_hidden(D_255, A_254))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_1261])).
% 23.68/13.65  tff(c_1677, plain, (![B_256, A_257]: (r2_hidden(B_256, k2_relat_1('#skF_14'(A_257, B_256))))), inference(resolution, [status(thm)], [c_1285, c_1620])).
% 23.68/13.65  tff(c_1695, plain, (![B_78, A_145, A_77]: (r2_hidden(B_78, k2_relat_1('#skF_15'(A_145))) | A_145!='#skF_17' | A_77!='#skF_17')), inference(superposition, [status(thm), theory('equality')], [c_291, c_1677])).
% 23.68/13.65  tff(c_1718, plain, (![A_77]: (A_77!='#skF_17')), inference(splitLeft, [status(thm)], [c_1695])).
% 23.68/13.65  tff(c_1722, plain, $false, inference(reflexivity, [status(thm), theory('equality')], [c_1718])).
% 23.68/13.65  tff(c_1725, plain, (![B_263, A_264]: (r2_hidden(B_263, k2_relat_1('#skF_15'(A_264))) | A_264!='#skF_17')), inference(splitRight, [status(thm)], [c_1695])).
% 23.68/13.65  tff(c_1697, plain, (![A_257, B_256]: (~r2_hidden(k2_relat_1('#skF_14'(A_257, B_256)), B_256))), inference(resolution, [status(thm)], [c_1677, c_2])).
% 23.68/13.65  tff(c_1775, plain, (![A_264]: (A_264!='#skF_17')), inference(resolution, [status(thm)], [c_1725, c_1697])).
% 23.68/13.65  tff(c_1788, plain, $false, inference(reflexivity, [status(thm), theory('equality')], [c_1775])).
% 23.68/13.65  tff(c_1789, plain, (v1_relat_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_1220])).
% 23.68/13.65  tff(c_1222, plain, (![A_222]: (v1_funct_1(k1_xboole_0) | ~v1_xboole_0(A_222))), inference(superposition, [status(thm), theory('equality')], [c_1183, c_76])).
% 23.68/13.65  tff(c_1806, plain, (![A_222]: (~v1_xboole_0(A_222))), inference(splitLeft, [status(thm)], [c_1222])).
% 23.68/13.65  tff(c_1812, plain, (![A_3]: (r2_hidden('#skF_1'(A_3), A_3))), inference(negUnitSimplification, [status(thm)], [c_1806, c_6])).
% 23.68/13.65  tff(c_2153, plain, (![B_296, A_297, D_298]: (r2_hidden(B_296, k2_relat_1('#skF_14'(A_297, B_296))) | ~r2_hidden(D_298, A_297))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_1261])).
% 23.68/13.65  tff(c_2209, plain, (![B_299, A_300]: (r2_hidden(B_299, k2_relat_1('#skF_14'(A_300, B_299))))), inference(resolution, [status(thm)], [c_1812, c_2153])).
% 23.68/13.65  tff(c_2224, plain, (![B_78, A_128, A_77]: (r2_hidden(B_78, k2_relat_1('#skF_16'(A_128))) | A_128!='#skF_17' | A_77!='#skF_17')), inference(superposition, [status(thm), theory('equality')], [c_186, c_2209])).
% 23.68/13.65  tff(c_2243, plain, (![A_77]: (A_77!='#skF_17')), inference(splitLeft, [status(thm)], [c_2224])).
% 23.68/13.65  tff(c_2247, plain, $false, inference(reflexivity, [status(thm), theory('equality')], [c_2243])).
% 23.68/13.65  tff(c_2250, plain, (![B_303, A_304]: (r2_hidden(B_303, k2_relat_1('#skF_16'(A_304))) | A_304!='#skF_17')), inference(splitRight, [status(thm)], [c_2224])).
% 23.68/13.65  tff(c_2229, plain, (![A_300, B_299]: (~r2_hidden(k2_relat_1('#skF_14'(A_300, B_299)), B_299))), inference(resolution, [status(thm)], [c_2209, c_2])).
% 23.68/13.65  tff(c_2299, plain, (![A_304]: (A_304!='#skF_17')), inference(resolution, [status(thm)], [c_2250, c_2229])).
% 23.68/13.65  tff(c_2313, plain, $false, inference(reflexivity, [status(thm), theory('equality')], [c_2299])).
% 23.68/13.65  tff(c_2314, plain, (v1_funct_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_1222])).
% 23.68/13.65  tff(c_42, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_66])).
% 23.68/13.65  tff(c_17084, plain, (![A_29452, B_29453]: (r2_hidden('#skF_11'(A_29452, B_29453), k1_relat_1(A_29452)) | r2_hidden('#skF_12'(A_29452, B_29453), B_29453) | k2_relat_1(A_29452)=B_29453 | ~v1_funct_1(A_29452) | ~v1_relat_1(A_29452))), inference(cnfTransformation, [status(thm)], [f_81])).
% 23.68/13.65  tff(c_17147, plain, (![B_29453]: (r2_hidden('#skF_11'(k1_xboole_0, B_29453), k1_xboole_0) | r2_hidden('#skF_12'(k1_xboole_0, B_29453), B_29453) | k2_relat_1(k1_xboole_0)=B_29453 | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_44, c_17084])).
% 23.68/13.65  tff(c_17170, plain, (![B_29453]: (r2_hidden('#skF_11'(k1_xboole_0, B_29453), k1_xboole_0) | r2_hidden('#skF_12'(k1_xboole_0, B_29453), B_29453) | k1_xboole_0=B_29453)), inference(demodulation, [status(thm), theory('equality')], [c_1789, c_2314, c_42, c_17147])).
% 23.68/13.65  tff(c_17172, plain, (![B_29454]: (r2_hidden('#skF_12'(k1_xboole_0, B_29454), B_29454) | k1_xboole_0=B_29454)), inference(negUnitSimplification, [status(thm)], [c_15528, c_17170])).
% 23.68/13.65  tff(c_17210, plain, (![B_29454]: (~v1_xboole_0(B_29454) | k1_xboole_0=B_29454)), inference(resolution, [status(thm)], [c_17172, c_4])).
% 23.68/13.65  tff(c_121612, plain, (k1_xboole_0='#skF_17'), inference(resolution, [status(thm)], [c_121322, c_17210])).
% 23.68/13.65  tff(c_88, plain, (k1_xboole_0!='#skF_17'), inference(cnfTransformation, [status(thm)], [f_136])).
% 23.68/13.65  tff(c_121679, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_121612, c_88])).
% 23.68/13.65  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 23.68/13.65  
% 23.68/13.65  Inference rules
% 23.68/13.65  ----------------------
% 23.68/13.65  #Ref     : 25
% 23.68/13.65  #Sup     : 27296
% 23.68/13.65  #Fact    : 50
% 23.68/13.65  #Define  : 0
% 23.68/13.65  #Split   : 45
% 23.68/13.65  #Chain   : 0
% 23.68/13.65  #Close   : 0
% 23.68/13.65  
% 23.68/13.65  Ordering : KBO
% 23.68/13.65  
% 23.68/13.65  Simplification rules
% 23.68/13.65  ----------------------
% 23.68/13.65  #Subsume      : 12958
% 23.68/13.65  #Demod        : 23977
% 23.68/13.65  #Tautology    : 6718
% 23.68/13.65  #SimpNegUnit  : 1107
% 23.68/13.65  #BackRed      : 99
% 23.68/13.65  
% 23.68/13.65  #Partial instantiations: 79750
% 23.68/13.65  #Strategies tried      : 1
% 23.68/13.65  
% 23.68/13.65  Timing (in seconds)
% 23.68/13.65  ----------------------
% 23.68/13.65  Preprocessing        : 0.34
% 23.68/13.65  Parsing              : 0.17
% 23.68/13.65  CNF conversion       : 0.03
% 23.68/13.65  Main loop            : 12.53
% 23.68/13.65  Inferencing          : 2.90
% 23.68/13.65  Reduction            : 3.91
% 23.68/13.65  Demodulation         : 2.79
% 23.68/13.65  BG Simplification    : 0.24
% 23.68/13.65  Subsumption          : 4.73
% 23.68/13.65  Abstraction          : 0.42
% 23.68/13.65  MUC search           : 0.00
% 23.68/13.65  Cooper               : 0.00
% 23.68/13.65  Total                : 12.93
% 23.68/13.65  Index Insertion      : 0.00
% 23.68/13.65  Index Deletion       : 0.00
% 23.68/13.65  Index Matching       : 0.00
% 23.68/13.65  BG Taut test         : 0.00
%------------------------------------------------------------------------------
