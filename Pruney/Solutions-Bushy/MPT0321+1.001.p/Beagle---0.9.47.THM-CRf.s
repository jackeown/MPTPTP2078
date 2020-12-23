%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0321+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:06 EST 2020

% Result     : Theorem 2.71s
% Output     : CNFRefutation 2.71s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 508 expanded)
%              Number of leaves         :   20 ( 163 expanded)
%              Depth                    :   16
%              Number of atoms          :  182 (1215 expanded)
%              Number of equality atoms :   80 ( 719 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k4_tarski > k2_zfmisc_1 > #nlpp > o_0_0_xboole_0 > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_63,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( k2_zfmisc_1(A,B) = k2_zfmisc_1(C,D)
       => ( A = k1_xboole_0
          | B = k1_xboole_0
          | ( A = C
            & B = D ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t134_zfmisc_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
        <=> r2_hidden(C,B) )
     => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).

tff(f_52,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_31,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(c_26,plain,
    ( '#skF_7' != '#skF_5'
    | '#skF_6' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_37,plain,(
    '#skF_6' != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_26])).

tff(c_22,plain,(
    ! [A_7,B_8] :
      ( r2_hidden('#skF_1'(A_7,B_8),B_8)
      | r2_hidden('#skF_2'(A_7,B_8),A_7)
      | B_8 = A_7 ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_28,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_24,plain,(
    ! [A_10] :
      ( r2_hidden('#skF_3'(A_10),A_10)
      | k1_xboole_0 = A_10 ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_122,plain,(
    ! [A_45,B_46,C_47,D_48] :
      ( r2_hidden(k4_tarski(A_45,B_46),k2_zfmisc_1(C_47,D_48))
      | ~ r2_hidden(B_46,D_48)
      | ~ r2_hidden(A_45,C_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_32,plain,(
    k2_zfmisc_1('#skF_6','#skF_7') = k2_zfmisc_1('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_80,plain,(
    ! [A_17,C_18,B_19,D_20] :
      ( r2_hidden(A_17,C_18)
      | ~ r2_hidden(k4_tarski(A_17,B_19),k2_zfmisc_1(C_18,D_20)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_83,plain,(
    ! [A_17,B_19] :
      ( r2_hidden(A_17,'#skF_6')
      | ~ r2_hidden(k4_tarski(A_17,B_19),k2_zfmisc_1('#skF_4','#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_80])).

tff(c_147,plain,(
    ! [A_45,B_46] :
      ( r2_hidden(A_45,'#skF_6')
      | ~ r2_hidden(B_46,'#skF_5')
      | ~ r2_hidden(A_45,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_122,c_83])).

tff(c_223,plain,(
    ! [B_56] : ~ r2_hidden(B_56,'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_147])).

tff(c_237,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_24,c_223])).

tff(c_243,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_237])).

tff(c_245,plain,(
    ! [A_57] :
      ( r2_hidden(A_57,'#skF_6')
      | ~ r2_hidden(A_57,'#skF_4') ) ),
    inference(splitRight,[status(thm)],[c_147])).

tff(c_18,plain,(
    ! [A_7,B_8] :
      ( r2_hidden('#skF_1'(A_7,B_8),B_8)
      | ~ r2_hidden('#skF_2'(A_7,B_8),B_8)
      | B_8 = A_7 ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_925,plain,(
    ! [A_382] :
      ( r2_hidden('#skF_1'(A_382,'#skF_6'),'#skF_6')
      | A_382 = '#skF_6'
      | ~ r2_hidden('#skF_2'(A_382,'#skF_6'),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_245,c_18])).

tff(c_933,plain,
    ( r2_hidden('#skF_1'('#skF_4','#skF_6'),'#skF_6')
    | '#skF_6' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_22,c_925])).

tff(c_938,plain,(
    r2_hidden('#skF_1'('#skF_4','#skF_6'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_37,c_37,c_933])).

tff(c_202,plain,(
    ! [A_54,B_55] :
      ( r2_hidden(k4_tarski(A_54,B_55),k2_zfmisc_1('#skF_4','#skF_5'))
      | ~ r2_hidden(B_55,'#skF_7')
      | ~ r2_hidden(A_54,'#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_122])).

tff(c_6,plain,(
    ! [B_2,D_4,A_1,C_3] :
      ( r2_hidden(B_2,D_4)
      | ~ r2_hidden(k4_tarski(A_1,B_2),k2_zfmisc_1(C_3,D_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_220,plain,(
    ! [B_55,A_54] :
      ( r2_hidden(B_55,'#skF_5')
      | ~ r2_hidden(B_55,'#skF_7')
      | ~ r2_hidden(A_54,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_202,c_6])).

tff(c_261,plain,(
    ! [A_58] : ~ r2_hidden(A_58,'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_220])).

tff(c_278,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_24,c_261])).

tff(c_14,plain,(
    ! [B_6] : k2_zfmisc_1(k1_xboole_0,B_6) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_291,plain,(
    ! [B_6] : k2_zfmisc_1('#skF_6',B_6) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_278,c_278,c_14])).

tff(c_318,plain,(
    k2_zfmisc_1('#skF_4','#skF_5') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_291,c_32])).

tff(c_65,plain,(
    ! [B_15,A_16] :
      ( k1_xboole_0 = B_15
      | k1_xboole_0 = A_16
      | k2_zfmisc_1(A_16,B_15) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_68,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k2_zfmisc_1('#skF_4','#skF_5') != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_65])).

tff(c_79,plain,(
    k2_zfmisc_1('#skF_4','#skF_5') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_68])).

tff(c_288,plain,(
    k2_zfmisc_1('#skF_4','#skF_5') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_278,c_79])).

tff(c_380,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_318,c_288])).

tff(c_407,plain,(
    ! [B_67] :
      ( r2_hidden(B_67,'#skF_5')
      | ~ r2_hidden(B_67,'#skF_7') ) ),
    inference(splitRight,[status(thm)],[c_220])).

tff(c_428,plain,
    ( r2_hidden('#skF_3'('#skF_7'),'#skF_5')
    | k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_24,c_407])).

tff(c_429,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_428])).

tff(c_12,plain,(
    ! [A_5] : k2_zfmisc_1(A_5,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_438,plain,(
    ! [A_5] : k2_zfmisc_1(A_5,'#skF_7') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_429,c_429,c_12])).

tff(c_466,plain,(
    k2_zfmisc_1('#skF_4','#skF_5') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_438,c_32])).

tff(c_434,plain,(
    k2_zfmisc_1('#skF_4','#skF_5') != '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_429,c_79])).

tff(c_536,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_466,c_434])).

tff(c_538,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(splitRight,[status(thm)],[c_428])).

tff(c_8,plain,(
    ! [A_1,C_3,B_2,D_4] :
      ( r2_hidden(A_1,C_3)
      | ~ r2_hidden(k4_tarski(A_1,B_2),k2_zfmisc_1(C_3,D_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_221,plain,(
    ! [A_54,B_55] :
      ( r2_hidden(A_54,'#skF_4')
      | ~ r2_hidden(B_55,'#skF_7')
      | ~ r2_hidden(A_54,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_202,c_8])).

tff(c_542,plain,(
    ! [B_72] : ~ r2_hidden(B_72,'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_221])).

tff(c_556,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_24,c_542])).

tff(c_562,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_538,c_556])).

tff(c_563,plain,(
    ! [A_54] :
      ( r2_hidden(A_54,'#skF_4')
      | ~ r2_hidden(A_54,'#skF_6') ) ),
    inference(splitRight,[status(thm)],[c_221])).

tff(c_942,plain,(
    r2_hidden('#skF_1'('#skF_4','#skF_6'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_938,c_563])).

tff(c_20,plain,(
    ! [A_7,B_8] :
      ( ~ r2_hidden('#skF_1'(A_7,B_8),A_7)
      | r2_hidden('#skF_2'(A_7,B_8),A_7)
      | B_8 = A_7 ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_244,plain,(
    ! [A_45] :
      ( r2_hidden(A_45,'#skF_6')
      | ~ r2_hidden(A_45,'#skF_4') ) ),
    inference(splitRight,[status(thm)],[c_147])).

tff(c_16,plain,(
    ! [A_7,B_8] :
      ( ~ r2_hidden('#skF_1'(A_7,B_8),A_7)
      | ~ r2_hidden('#skF_2'(A_7,B_8),B_8)
      | B_8 = A_7 ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_944,plain,
    ( ~ r2_hidden('#skF_2'('#skF_4','#skF_6'),'#skF_6')
    | '#skF_6' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_942,c_16])).

tff(c_947,plain,(
    ~ r2_hidden('#skF_2'('#skF_4','#skF_6'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_37,c_944])).

tff(c_951,plain,(
    ~ r2_hidden('#skF_2'('#skF_4','#skF_6'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_244,c_947])).

tff(c_954,plain,
    ( ~ r2_hidden('#skF_1'('#skF_4','#skF_6'),'#skF_4')
    | '#skF_6' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_20,c_951])).

tff(c_960,plain,(
    '#skF_6' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_942,c_954])).

tff(c_962,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_37,c_960])).

tff(c_963,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_965,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_963])).

tff(c_30,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_972,plain,(
    '#skF_7' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_965,c_30])).

tff(c_970,plain,(
    '#skF_7' != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_965,c_28])).

tff(c_964,plain,(
    k2_zfmisc_1('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_985,plain,(
    k2_zfmisc_1('#skF_4','#skF_5') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_965,c_964])).

tff(c_10,plain,(
    ! [B_6,A_5] :
      ( k1_xboole_0 = B_6
      | k1_xboole_0 = A_5
      | k2_zfmisc_1(A_5,B_6) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1031,plain,(
    ! [B_390,A_391] :
      ( B_390 = '#skF_7'
      | A_391 = '#skF_7'
      | k2_zfmisc_1(A_391,B_390) != '#skF_7' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_965,c_965,c_965,c_10])).

tff(c_1040,plain,
    ( '#skF_7' = '#skF_5'
    | '#skF_7' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_985,c_1031])).

tff(c_1048,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_972,c_970,c_1040])).

tff(c_1049,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_963])).

tff(c_1055,plain,(
    '#skF_5' != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1049,c_28])).

tff(c_1072,plain,(
    k2_zfmisc_1('#skF_4','#skF_5') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1049,c_964])).

tff(c_1122,plain,(
    ! [B_405,A_406] :
      ( B_405 = '#skF_6'
      | A_406 = '#skF_6'
      | k2_zfmisc_1(A_406,B_405) != '#skF_6' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1049,c_1049,c_1049,c_10])).

tff(c_1131,plain,
    ( '#skF_5' = '#skF_6'
    | '#skF_6' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_1072,c_1122])).

tff(c_1139,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_37,c_1055,c_1131])).

tff(c_1140,plain,(
    '#skF_7' != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_1231,plain,(
    ! [A_438,B_439,C_440,D_441] :
      ( r2_hidden(k4_tarski(A_438,B_439),k2_zfmisc_1(C_440,D_441))
      | ~ r2_hidden(B_439,D_441)
      | ~ r2_hidden(A_438,C_440) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1141,plain,(
    '#skF_6' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_1146,plain,(
    k2_zfmisc_1('#skF_4','#skF_7') = k2_zfmisc_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1141,c_32])).

tff(c_1190,plain,(
    ! [B_412,D_413,A_414,C_415] :
      ( r2_hidden(B_412,D_413)
      | ~ r2_hidden(k4_tarski(A_414,B_412),k2_zfmisc_1(C_415,D_413)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1199,plain,(
    ! [B_412,A_414] :
      ( r2_hidden(B_412,'#skF_7')
      | ~ r2_hidden(k4_tarski(A_414,B_412),k2_zfmisc_1('#skF_4','#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1146,c_1190])).

tff(c_1252,plain,(
    ! [B_439,A_438] :
      ( r2_hidden(B_439,'#skF_7')
      | ~ r2_hidden(B_439,'#skF_5')
      | ~ r2_hidden(A_438,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1231,c_1199])).

tff(c_1268,plain,(
    ! [A_444] : ~ r2_hidden(A_444,'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1252])).

tff(c_1282,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_24,c_1268])).

tff(c_1288,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_1282])).

tff(c_1290,plain,(
    ! [B_445] :
      ( r2_hidden(B_445,'#skF_7')
      | ~ r2_hidden(B_445,'#skF_5') ) ),
    inference(splitRight,[status(thm)],[c_1252])).

tff(c_1652,plain,(
    ! [A_665] :
      ( r2_hidden('#skF_1'(A_665,'#skF_7'),'#skF_7')
      | A_665 = '#skF_7'
      | ~ r2_hidden('#skF_2'(A_665,'#skF_7'),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_1290,c_18])).

tff(c_1656,plain,
    ( r2_hidden('#skF_1'('#skF_5','#skF_7'),'#skF_7')
    | '#skF_7' = '#skF_5' ),
    inference(resolution,[status(thm)],[c_22,c_1652])).

tff(c_1663,plain,(
    r2_hidden('#skF_1'('#skF_5','#skF_7'),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_1140,c_1140,c_1656])).

tff(c_1351,plain,(
    ! [A_454,B_455] :
      ( r2_hidden(k4_tarski(A_454,B_455),k2_zfmisc_1('#skF_4','#skF_5'))
      | ~ r2_hidden(B_455,'#skF_7')
      | ~ r2_hidden(A_454,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1146,c_1231])).

tff(c_1369,plain,(
    ! [B_455,A_454] :
      ( r2_hidden(B_455,'#skF_5')
      | ~ r2_hidden(B_455,'#skF_7')
      | ~ r2_hidden(A_454,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1351,c_6])).

tff(c_1468,plain,(
    ! [A_657] : ~ r2_hidden(A_657,'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1369])).

tff(c_1482,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_24,c_1468])).

tff(c_1488,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_1482])).

tff(c_1489,plain,(
    ! [B_455] :
      ( r2_hidden(B_455,'#skF_5')
      | ~ r2_hidden(B_455,'#skF_7') ) ),
    inference(splitRight,[status(thm)],[c_1369])).

tff(c_1669,plain,(
    r2_hidden('#skF_1'('#skF_5','#skF_7'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_1663,c_1489])).

tff(c_1289,plain,(
    ! [B_439] :
      ( r2_hidden(B_439,'#skF_7')
      | ~ r2_hidden(B_439,'#skF_5') ) ),
    inference(splitRight,[status(thm)],[c_1252])).

tff(c_1671,plain,
    ( ~ r2_hidden('#skF_2'('#skF_5','#skF_7'),'#skF_7')
    | '#skF_7' = '#skF_5' ),
    inference(resolution,[status(thm)],[c_1669,c_16])).

tff(c_1674,plain,(
    ~ r2_hidden('#skF_2'('#skF_5','#skF_7'),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_1140,c_1671])).

tff(c_1679,plain,(
    ~ r2_hidden('#skF_2'('#skF_5','#skF_7'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_1289,c_1674])).

tff(c_1685,plain,
    ( ~ r2_hidden('#skF_1'('#skF_5','#skF_7'),'#skF_5')
    | '#skF_7' = '#skF_5' ),
    inference(resolution,[status(thm)],[c_20,c_1679])).

tff(c_1691,plain,(
    '#skF_7' = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1669,c_1685])).

tff(c_1693,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1140,c_1691])).

%------------------------------------------------------------------------------
