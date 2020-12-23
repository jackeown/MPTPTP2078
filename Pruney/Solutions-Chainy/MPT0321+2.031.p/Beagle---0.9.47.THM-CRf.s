%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:17 EST 2020

% Result     : Theorem 3.70s
% Output     : CNFRefutation 3.70s
% Verified   : 
% Statistics : Number of formulae       :  142 ( 619 expanded)
%              Number of leaves         :   25 ( 206 expanded)
%              Depth                    :   15
%              Number of atoms          :  216 (1422 expanded)
%              Number of equality atoms :   39 ( 386 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_xboole_0 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_6 > #skF_9 > #skF_8 > #skF_2 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

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

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

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

tff(f_82,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( k2_zfmisc_1(A,B) = k2_zfmisc_1(C,D)
       => ( A = k1_xboole_0
          | B = k1_xboole_0
          | ( A = C
            & B = D ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t134_zfmisc_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_58,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(f_39,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_52,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_46,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
        <=> r2_hidden(C,B) )
     => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).

tff(c_40,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_38,plain,
    ( '#skF_7' != '#skF_9'
    | '#skF_6' != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_47,plain,(
    '#skF_6' != '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_2'(A_5,B_6),A_5)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_306,plain,(
    ! [A_91,B_92,C_93,D_94] :
      ( r2_hidden(k4_tarski(A_91,B_92),k2_zfmisc_1(C_93,D_94))
      | ~ r2_hidden(B_92,D_94)
      | ~ r2_hidden(A_91,C_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_44,plain,(
    k2_zfmisc_1('#skF_6','#skF_7') = k2_zfmisc_1('#skF_8','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_137,plain,(
    ! [B_56,D_57,A_58,C_59] :
      ( r2_hidden(B_56,D_57)
      | ~ r2_hidden(k4_tarski(A_58,B_56),k2_zfmisc_1(C_59,D_57)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_140,plain,(
    ! [B_56,A_58] :
      ( r2_hidden(B_56,'#skF_7')
      | ~ r2_hidden(k4_tarski(A_58,B_56),k2_zfmisc_1('#skF_8','#skF_9')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_137])).

tff(c_329,plain,(
    ! [B_92,A_91] :
      ( r2_hidden(B_92,'#skF_7')
      | ~ r2_hidden(B_92,'#skF_9')
      | ~ r2_hidden(A_91,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_306,c_140])).

tff(c_336,plain,(
    ! [A_95] : ~ r2_hidden(A_95,'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_329])).

tff(c_388,plain,(
    v1_xboole_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_4,c_336])).

tff(c_12,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_70,plain,(
    ! [A_34,B_35] :
      ( r2_hidden('#skF_2'(A_34,B_35),A_34)
      | r1_tarski(A_34,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_74,plain,(
    ! [A_34,B_35] :
      ( ~ v1_xboole_0(A_34)
      | r1_tarski(A_34,B_35) ) ),
    inference(resolution,[status(thm)],[c_70,c_2])).

tff(c_75,plain,(
    ! [A_36,B_37] :
      ( ~ v1_xboole_0(A_36)
      | r1_tarski(A_36,B_37) ) ),
    inference(resolution,[status(thm)],[c_70,c_2])).

tff(c_22,plain,(
    ! [B_14,A_13] :
      ( B_14 = A_13
      | ~ r1_tarski(B_14,A_13)
      | ~ r1_tarski(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_79,plain,(
    ! [B_38,A_39] :
      ( B_38 = A_39
      | ~ r1_tarski(B_38,A_39)
      | ~ v1_xboole_0(A_39) ) ),
    inference(resolution,[status(thm)],[c_75,c_22])).

tff(c_89,plain,(
    ! [B_40,A_41] :
      ( B_40 = A_41
      | ~ v1_xboole_0(B_40)
      | ~ v1_xboole_0(A_41) ) ),
    inference(resolution,[status(thm)],[c_74,c_79])).

tff(c_92,plain,(
    ! [A_41] :
      ( k1_xboole_0 = A_41
      | ~ v1_xboole_0(A_41) ) ),
    inference(resolution,[status(thm)],[c_12,c_89])).

tff(c_394,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(resolution,[status(thm)],[c_388,c_92])).

tff(c_423,plain,(
    '#skF_7' != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_394,c_40])).

tff(c_335,plain,(
    ! [A_91] : ~ r2_hidden(A_91,'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_329])).

tff(c_396,plain,(
    ! [A_96,B_97] :
      ( r2_hidden(k4_tarski(A_96,B_97),k2_zfmisc_1('#skF_8','#skF_9'))
      | ~ r2_hidden(B_97,'#skF_7')
      | ~ r2_hidden(A_96,'#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_306])).

tff(c_32,plain,(
    ! [A_15,C_17,B_16,D_18] :
      ( r2_hidden(A_15,C_17)
      | ~ r2_hidden(k4_tarski(A_15,B_16),k2_zfmisc_1(C_17,D_18)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_408,plain,(
    ! [A_96,B_97] :
      ( r2_hidden(A_96,'#skF_8')
      | ~ r2_hidden(B_97,'#skF_7')
      | ~ r2_hidden(A_96,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_396,c_32])).

tff(c_419,plain,(
    ! [B_97,A_96] :
      ( ~ r2_hidden(B_97,'#skF_7')
      | ~ r2_hidden(A_96,'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_335,c_408])).

tff(c_499,plain,(
    ! [A_106] : ~ r2_hidden(A_106,'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_419])).

tff(c_551,plain,(
    v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_4,c_499])).

tff(c_228,plain,(
    ! [A_83,B_84] :
      ( r2_hidden('#skF_3'(A_83,B_84),B_84)
      | r2_hidden('#skF_4'(A_83,B_84),A_83)
      | B_84 = A_83 ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_254,plain,(
    ! [B_84,A_83] :
      ( ~ v1_xboole_0(B_84)
      | r2_hidden('#skF_4'(A_83,B_84),A_83)
      | B_84 = A_83 ) ),
    inference(resolution,[status(thm)],[c_228,c_2])).

tff(c_380,plain,(
    ! [B_84] :
      ( ~ v1_xboole_0(B_84)
      | B_84 = '#skF_8' ) ),
    inference(resolution,[status(thm)],[c_254,c_336])).

tff(c_560,plain,(
    '#skF_6' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_551,c_380])).

tff(c_566,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_47,c_560])).

tff(c_569,plain,(
    ! [B_109] : ~ r2_hidden(B_109,'#skF_7') ),
    inference(splitRight,[status(thm)],[c_419])).

tff(c_621,plain,(
    v1_xboole_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_4,c_569])).

tff(c_624,plain,(
    '#skF_7' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_621,c_380])).

tff(c_630,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_423,c_624])).

tff(c_656,plain,(
    ! [B_112] :
      ( r2_hidden(B_112,'#skF_7')
      | ~ r2_hidden(B_112,'#skF_9') ) ),
    inference(splitRight,[status(thm)],[c_329])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( ~ r2_hidden('#skF_2'(A_5,B_6),B_6)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_679,plain,(
    ! [A_113] :
      ( r1_tarski(A_113,'#skF_7')
      | ~ r2_hidden('#skF_2'(A_113,'#skF_7'),'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_656,c_8])).

tff(c_689,plain,(
    r1_tarski('#skF_9','#skF_7') ),
    inference(resolution,[status(thm)],[c_10,c_679])).

tff(c_706,plain,
    ( '#skF_7' = '#skF_9'
    | ~ r1_tarski('#skF_7','#skF_9') ),
    inference(resolution,[status(thm)],[c_689,c_22])).

tff(c_710,plain,(
    ~ r1_tarski('#skF_7','#skF_9') ),
    inference(splitLeft,[status(thm)],[c_706])).

tff(c_42,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_632,plain,(
    ! [A_110,B_111] :
      ( r2_hidden(k4_tarski(A_110,B_111),k2_zfmisc_1('#skF_8','#skF_9'))
      | ~ r2_hidden(B_111,'#skF_7')
      | ~ r2_hidden(A_110,'#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_306])).

tff(c_30,plain,(
    ! [B_16,D_18,A_15,C_17] :
      ( r2_hidden(B_16,D_18)
      | ~ r2_hidden(k4_tarski(A_15,B_16),k2_zfmisc_1(C_17,D_18)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_652,plain,(
    ! [B_111,A_110] :
      ( r2_hidden(B_111,'#skF_9')
      | ~ r2_hidden(B_111,'#skF_7')
      | ~ r2_hidden(A_110,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_632,c_30])).

tff(c_749,plain,(
    ! [A_120] : ~ r2_hidden(A_120,'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_652])).

tff(c_801,plain,(
    v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_4,c_749])).

tff(c_804,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_801,c_92])).

tff(c_810,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_804])).

tff(c_823,plain,(
    ! [B_123] :
      ( r2_hidden(B_123,'#skF_9')
      | ~ r2_hidden(B_123,'#skF_7') ) ),
    inference(splitRight,[status(thm)],[c_652])).

tff(c_1014,plain,(
    ! [B_131] :
      ( r2_hidden('#skF_2'('#skF_7',B_131),'#skF_9')
      | r1_tarski('#skF_7',B_131) ) ),
    inference(resolution,[status(thm)],[c_10,c_823])).

tff(c_1024,plain,(
    r1_tarski('#skF_7','#skF_9') ),
    inference(resolution,[status(thm)],[c_1014,c_8])).

tff(c_1034,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_710,c_710,c_1024])).

tff(c_1035,plain,(
    '#skF_7' = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_706])).

tff(c_677,plain,(
    ! [B_112] :
      ( ~ v1_xboole_0('#skF_7')
      | ~ r2_hidden(B_112,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_656,c_2])).

tff(c_678,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_677])).

tff(c_1040,plain,(
    ~ v1_xboole_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1035,c_678])).

tff(c_653,plain,(
    ! [A_110,B_111] :
      ( r2_hidden(A_110,'#skF_8')
      | ~ r2_hidden(B_111,'#skF_7')
      | ~ r2_hidden(A_110,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_632,c_32])).

tff(c_1074,plain,(
    ! [A_110,B_111] :
      ( r2_hidden(A_110,'#skF_8')
      | ~ r2_hidden(B_111,'#skF_9')
      | ~ r2_hidden(A_110,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1035,c_653])).

tff(c_1077,plain,(
    ! [B_134] : ~ r2_hidden(B_134,'#skF_9') ),
    inference(splitLeft,[status(thm)],[c_1074])).

tff(c_1119,plain,(
    v1_xboole_0('#skF_9') ),
    inference(resolution,[status(thm)],[c_4,c_1077])).

tff(c_1132,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1040,c_1119])).

tff(c_1134,plain,(
    ! [A_135] :
      ( r2_hidden(A_135,'#skF_8')
      | ~ r2_hidden(A_135,'#skF_6') ) ),
    inference(splitRight,[status(thm)],[c_1074])).

tff(c_1279,plain,(
    ! [B_141] :
      ( r2_hidden('#skF_2'('#skF_6',B_141),'#skF_8')
      | r1_tarski('#skF_6',B_141) ) ),
    inference(resolution,[status(thm)],[c_10,c_1134])).

tff(c_1290,plain,(
    r1_tarski('#skF_6','#skF_8') ),
    inference(resolution,[status(thm)],[c_1279,c_8])).

tff(c_1303,plain,
    ( '#skF_6' = '#skF_8'
    | ~ r1_tarski('#skF_8','#skF_6') ),
    inference(resolution,[status(thm)],[c_1290,c_22])).

tff(c_1312,plain,(
    ~ r1_tarski('#skF_8','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_47,c_1303])).

tff(c_124,plain,(
    ! [A_50,C_51,B_52,D_53] :
      ( r2_hidden(A_50,C_51)
      | ~ r2_hidden(k4_tarski(A_50,B_52),k2_zfmisc_1(C_51,D_53)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_127,plain,(
    ! [A_50,B_52] :
      ( r2_hidden(A_50,'#skF_6')
      | ~ r2_hidden(k4_tarski(A_50,B_52),k2_zfmisc_1('#skF_8','#skF_9')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_124])).

tff(c_330,plain,(
    ! [A_91,B_92] :
      ( r2_hidden(A_91,'#skF_6')
      | ~ r2_hidden(B_92,'#skF_9')
      | ~ r2_hidden(A_91,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_306,c_127])).

tff(c_1332,plain,(
    ! [B_146] : ~ r2_hidden(B_146,'#skF_9') ),
    inference(splitLeft,[status(thm)],[c_330])).

tff(c_1384,plain,(
    v1_xboole_0('#skF_9') ),
    inference(resolution,[status(thm)],[c_4,c_1332])).

tff(c_1399,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1040,c_1384])).

tff(c_1401,plain,(
    ! [A_147] :
      ( r2_hidden(A_147,'#skF_6')
      | ~ r2_hidden(A_147,'#skF_8') ) ),
    inference(splitRight,[status(thm)],[c_330])).

tff(c_1438,plain,(
    ! [A_148] :
      ( r1_tarski(A_148,'#skF_6')
      | ~ r2_hidden('#skF_2'(A_148,'#skF_6'),'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_1401,c_8])).

tff(c_1450,plain,(
    r1_tarski('#skF_8','#skF_6') ),
    inference(resolution,[status(thm)],[c_10,c_1438])).

tff(c_1457,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1312,c_1312,c_1450])).

tff(c_1459,plain,(
    v1_xboole_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_677])).

tff(c_1462,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_1459,c_92])).

tff(c_1468,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_1462])).

tff(c_1469,plain,(
    '#skF_7' != '#skF_9' ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_1470,plain,(
    '#skF_6' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_1471,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1470,c_42])).

tff(c_1754,plain,(
    ! [A_217,B_218,C_219,D_220] :
      ( r2_hidden(k4_tarski(A_217,B_218),k2_zfmisc_1(C_219,D_220))
      | ~ r2_hidden(B_218,D_220)
      | ~ r2_hidden(A_217,C_219) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1482,plain,(
    k2_zfmisc_1('#skF_8','#skF_7') = k2_zfmisc_1('#skF_8','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1470,c_44])).

tff(c_1562,plain,(
    ! [B_174,D_175,A_176,C_177] :
      ( r2_hidden(B_174,D_175)
      | ~ r2_hidden(k4_tarski(A_176,B_174),k2_zfmisc_1(C_177,D_175)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1565,plain,(
    ! [B_174,A_176] :
      ( r2_hidden(B_174,'#skF_7')
      | ~ r2_hidden(k4_tarski(A_176,B_174),k2_zfmisc_1('#skF_8','#skF_9')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1482,c_1562])).

tff(c_1773,plain,(
    ! [B_218,A_217] :
      ( r2_hidden(B_218,'#skF_7')
      | ~ r2_hidden(B_218,'#skF_9')
      | ~ r2_hidden(A_217,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_1754,c_1565])).

tff(c_1779,plain,(
    ! [A_221] : ~ r2_hidden(A_221,'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_1773])).

tff(c_1836,plain,(
    v1_xboole_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_4,c_1779])).

tff(c_1494,plain,(
    ! [A_154,B_155] :
      ( r2_hidden('#skF_2'(A_154,B_155),A_154)
      | r1_tarski(A_154,B_155) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_1498,plain,(
    ! [A_154,B_155] :
      ( ~ v1_xboole_0(A_154)
      | r1_tarski(A_154,B_155) ) ),
    inference(resolution,[status(thm)],[c_1494,c_2])).

tff(c_1499,plain,(
    ! [A_156,B_157] :
      ( ~ v1_xboole_0(A_156)
      | r1_tarski(A_156,B_157) ) ),
    inference(resolution,[status(thm)],[c_1494,c_2])).

tff(c_1503,plain,(
    ! [B_158,A_159] :
      ( B_158 = A_159
      | ~ r1_tarski(B_158,A_159)
      | ~ v1_xboole_0(A_159) ) ),
    inference(resolution,[status(thm)],[c_1499,c_22])).

tff(c_1513,plain,(
    ! [B_160,A_161] :
      ( B_160 = A_161
      | ~ v1_xboole_0(B_160)
      | ~ v1_xboole_0(A_161) ) ),
    inference(resolution,[status(thm)],[c_1498,c_1503])).

tff(c_1516,plain,(
    ! [A_161] :
      ( k1_xboole_0 = A_161
      | ~ v1_xboole_0(A_161) ) ),
    inference(resolution,[status(thm)],[c_12,c_1513])).

tff(c_1839,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(resolution,[status(thm)],[c_1836,c_1516])).

tff(c_1845,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1471,c_1839])).

tff(c_1867,plain,(
    ! [B_224] :
      ( r2_hidden(B_224,'#skF_7')
      | ~ r2_hidden(B_224,'#skF_9') ) ),
    inference(splitRight,[status(thm)],[c_1773])).

tff(c_1890,plain,(
    ! [A_225] :
      ( r1_tarski(A_225,'#skF_7')
      | ~ r2_hidden('#skF_2'(A_225,'#skF_7'),'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_1867,c_8])).

tff(c_1900,plain,(
    r1_tarski('#skF_9','#skF_7') ),
    inference(resolution,[status(thm)],[c_10,c_1890])).

tff(c_1914,plain,
    ( '#skF_7' = '#skF_9'
    | ~ r1_tarski('#skF_7','#skF_9') ),
    inference(resolution,[status(thm)],[c_1900,c_22])).

tff(c_1923,plain,(
    ~ r1_tarski('#skF_7','#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_1469,c_1914])).

tff(c_1847,plain,(
    ! [A_222,B_223] :
      ( r2_hidden(k4_tarski(A_222,B_223),k2_zfmisc_1('#skF_8','#skF_9'))
      | ~ r2_hidden(B_223,'#skF_7')
      | ~ r2_hidden(A_222,'#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1482,c_1754])).

tff(c_1864,plain,(
    ! [B_223,A_222] :
      ( r2_hidden(B_223,'#skF_9')
      | ~ r2_hidden(B_223,'#skF_7')
      | ~ r2_hidden(A_222,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_1847,c_30])).

tff(c_1967,plain,(
    ! [A_232] : ~ r2_hidden(A_232,'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_1864])).

tff(c_2024,plain,(
    v1_xboole_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_4,c_1967])).

tff(c_2027,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(resolution,[status(thm)],[c_2024,c_1516])).

tff(c_2033,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1471,c_2027])).

tff(c_2035,plain,(
    ! [B_233] :
      ( r2_hidden(B_233,'#skF_9')
      | ~ r2_hidden(B_233,'#skF_7') ) ),
    inference(splitRight,[status(thm)],[c_1864])).

tff(c_2159,plain,(
    ! [B_238] :
      ( r2_hidden('#skF_2'('#skF_7',B_238),'#skF_9')
      | r1_tarski('#skF_7',B_238) ) ),
    inference(resolution,[status(thm)],[c_10,c_2035])).

tff(c_2169,plain,(
    r1_tarski('#skF_7','#skF_9') ),
    inference(resolution,[status(thm)],[c_2159,c_8])).

tff(c_2179,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1923,c_1923,c_2169])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:43:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.70/1.56  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.70/1.57  
% 3.70/1.57  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.70/1.57  %$ r2_hidden > r1_tarski > v1_xboole_0 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_6 > #skF_9 > #skF_8 > #skF_2 > #skF_5 > #skF_4
% 3.70/1.57  
% 3.70/1.57  %Foreground sorts:
% 3.70/1.57  
% 3.70/1.57  
% 3.70/1.57  %Background operators:
% 3.70/1.57  
% 3.70/1.57  
% 3.70/1.57  %Foreground operators:
% 3.70/1.57  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.70/1.57  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.70/1.57  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.70/1.57  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.70/1.57  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.70/1.57  tff('#skF_7', type, '#skF_7': $i).
% 3.70/1.57  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.70/1.57  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.70/1.57  tff('#skF_6', type, '#skF_6': $i).
% 3.70/1.57  tff('#skF_9', type, '#skF_9': $i).
% 3.70/1.57  tff('#skF_8', type, '#skF_8': $i).
% 3.70/1.57  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.70/1.57  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.70/1.57  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.70/1.57  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.70/1.57  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.70/1.57  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 3.70/1.57  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.70/1.57  
% 3.70/1.59  tff(f_82, negated_conjecture, ~(![A, B, C, D]: ((k2_zfmisc_1(A, B) = k2_zfmisc_1(C, D)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | ((A = C) & (B = D))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t134_zfmisc_1)).
% 3.70/1.59  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 3.70/1.59  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.70/1.59  tff(f_58, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 3.70/1.59  tff(f_39, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.70/1.59  tff(f_52, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.70/1.59  tff(f_46, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) <=> r2_hidden(C, B))) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tarski)).
% 3.70/1.59  tff(c_40, plain, (k1_xboole_0!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.70/1.59  tff(c_38, plain, ('#skF_7'!='#skF_9' | '#skF_6'!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.70/1.59  tff(c_47, plain, ('#skF_6'!='#skF_8'), inference(splitLeft, [status(thm)], [c_38])).
% 3.70/1.59  tff(c_10, plain, (![A_5, B_6]: (r2_hidden('#skF_2'(A_5, B_6), A_5) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.70/1.59  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.70/1.59  tff(c_306, plain, (![A_91, B_92, C_93, D_94]: (r2_hidden(k4_tarski(A_91, B_92), k2_zfmisc_1(C_93, D_94)) | ~r2_hidden(B_92, D_94) | ~r2_hidden(A_91, C_93))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.70/1.59  tff(c_44, plain, (k2_zfmisc_1('#skF_6', '#skF_7')=k2_zfmisc_1('#skF_8', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.70/1.59  tff(c_137, plain, (![B_56, D_57, A_58, C_59]: (r2_hidden(B_56, D_57) | ~r2_hidden(k4_tarski(A_58, B_56), k2_zfmisc_1(C_59, D_57)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.70/1.59  tff(c_140, plain, (![B_56, A_58]: (r2_hidden(B_56, '#skF_7') | ~r2_hidden(k4_tarski(A_58, B_56), k2_zfmisc_1('#skF_8', '#skF_9')))), inference(superposition, [status(thm), theory('equality')], [c_44, c_137])).
% 3.70/1.59  tff(c_329, plain, (![B_92, A_91]: (r2_hidden(B_92, '#skF_7') | ~r2_hidden(B_92, '#skF_9') | ~r2_hidden(A_91, '#skF_8'))), inference(resolution, [status(thm)], [c_306, c_140])).
% 3.70/1.59  tff(c_336, plain, (![A_95]: (~r2_hidden(A_95, '#skF_8'))), inference(splitLeft, [status(thm)], [c_329])).
% 3.70/1.59  tff(c_388, plain, (v1_xboole_0('#skF_8')), inference(resolution, [status(thm)], [c_4, c_336])).
% 3.70/1.59  tff(c_12, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.70/1.59  tff(c_70, plain, (![A_34, B_35]: (r2_hidden('#skF_2'(A_34, B_35), A_34) | r1_tarski(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.70/1.59  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.70/1.59  tff(c_74, plain, (![A_34, B_35]: (~v1_xboole_0(A_34) | r1_tarski(A_34, B_35))), inference(resolution, [status(thm)], [c_70, c_2])).
% 3.70/1.59  tff(c_75, plain, (![A_36, B_37]: (~v1_xboole_0(A_36) | r1_tarski(A_36, B_37))), inference(resolution, [status(thm)], [c_70, c_2])).
% 3.70/1.59  tff(c_22, plain, (![B_14, A_13]: (B_14=A_13 | ~r1_tarski(B_14, A_13) | ~r1_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.70/1.59  tff(c_79, plain, (![B_38, A_39]: (B_38=A_39 | ~r1_tarski(B_38, A_39) | ~v1_xboole_0(A_39))), inference(resolution, [status(thm)], [c_75, c_22])).
% 3.70/1.59  tff(c_89, plain, (![B_40, A_41]: (B_40=A_41 | ~v1_xboole_0(B_40) | ~v1_xboole_0(A_41))), inference(resolution, [status(thm)], [c_74, c_79])).
% 3.70/1.59  tff(c_92, plain, (![A_41]: (k1_xboole_0=A_41 | ~v1_xboole_0(A_41))), inference(resolution, [status(thm)], [c_12, c_89])).
% 3.70/1.59  tff(c_394, plain, (k1_xboole_0='#skF_8'), inference(resolution, [status(thm)], [c_388, c_92])).
% 3.70/1.59  tff(c_423, plain, ('#skF_7'!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_394, c_40])).
% 3.70/1.59  tff(c_335, plain, (![A_91]: (~r2_hidden(A_91, '#skF_8'))), inference(splitLeft, [status(thm)], [c_329])).
% 3.70/1.59  tff(c_396, plain, (![A_96, B_97]: (r2_hidden(k4_tarski(A_96, B_97), k2_zfmisc_1('#skF_8', '#skF_9')) | ~r2_hidden(B_97, '#skF_7') | ~r2_hidden(A_96, '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_44, c_306])).
% 3.70/1.59  tff(c_32, plain, (![A_15, C_17, B_16, D_18]: (r2_hidden(A_15, C_17) | ~r2_hidden(k4_tarski(A_15, B_16), k2_zfmisc_1(C_17, D_18)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.70/1.59  tff(c_408, plain, (![A_96, B_97]: (r2_hidden(A_96, '#skF_8') | ~r2_hidden(B_97, '#skF_7') | ~r2_hidden(A_96, '#skF_6'))), inference(resolution, [status(thm)], [c_396, c_32])).
% 3.70/1.59  tff(c_419, plain, (![B_97, A_96]: (~r2_hidden(B_97, '#skF_7') | ~r2_hidden(A_96, '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_335, c_408])).
% 3.70/1.59  tff(c_499, plain, (![A_106]: (~r2_hidden(A_106, '#skF_6'))), inference(splitLeft, [status(thm)], [c_419])).
% 3.70/1.59  tff(c_551, plain, (v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_4, c_499])).
% 3.70/1.59  tff(c_228, plain, (![A_83, B_84]: (r2_hidden('#skF_3'(A_83, B_84), B_84) | r2_hidden('#skF_4'(A_83, B_84), A_83) | B_84=A_83)), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.70/1.59  tff(c_254, plain, (![B_84, A_83]: (~v1_xboole_0(B_84) | r2_hidden('#skF_4'(A_83, B_84), A_83) | B_84=A_83)), inference(resolution, [status(thm)], [c_228, c_2])).
% 3.70/1.59  tff(c_380, plain, (![B_84]: (~v1_xboole_0(B_84) | B_84='#skF_8')), inference(resolution, [status(thm)], [c_254, c_336])).
% 3.70/1.59  tff(c_560, plain, ('#skF_6'='#skF_8'), inference(resolution, [status(thm)], [c_551, c_380])).
% 3.70/1.59  tff(c_566, plain, $false, inference(negUnitSimplification, [status(thm)], [c_47, c_560])).
% 3.70/1.59  tff(c_569, plain, (![B_109]: (~r2_hidden(B_109, '#skF_7'))), inference(splitRight, [status(thm)], [c_419])).
% 3.70/1.59  tff(c_621, plain, (v1_xboole_0('#skF_7')), inference(resolution, [status(thm)], [c_4, c_569])).
% 3.70/1.59  tff(c_624, plain, ('#skF_7'='#skF_8'), inference(resolution, [status(thm)], [c_621, c_380])).
% 3.70/1.59  tff(c_630, plain, $false, inference(negUnitSimplification, [status(thm)], [c_423, c_624])).
% 3.70/1.59  tff(c_656, plain, (![B_112]: (r2_hidden(B_112, '#skF_7') | ~r2_hidden(B_112, '#skF_9'))), inference(splitRight, [status(thm)], [c_329])).
% 3.70/1.59  tff(c_8, plain, (![A_5, B_6]: (~r2_hidden('#skF_2'(A_5, B_6), B_6) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.70/1.59  tff(c_679, plain, (![A_113]: (r1_tarski(A_113, '#skF_7') | ~r2_hidden('#skF_2'(A_113, '#skF_7'), '#skF_9'))), inference(resolution, [status(thm)], [c_656, c_8])).
% 3.70/1.59  tff(c_689, plain, (r1_tarski('#skF_9', '#skF_7')), inference(resolution, [status(thm)], [c_10, c_679])).
% 3.70/1.59  tff(c_706, plain, ('#skF_7'='#skF_9' | ~r1_tarski('#skF_7', '#skF_9')), inference(resolution, [status(thm)], [c_689, c_22])).
% 3.70/1.59  tff(c_710, plain, (~r1_tarski('#skF_7', '#skF_9')), inference(splitLeft, [status(thm)], [c_706])).
% 3.70/1.59  tff(c_42, plain, (k1_xboole_0!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.70/1.59  tff(c_632, plain, (![A_110, B_111]: (r2_hidden(k4_tarski(A_110, B_111), k2_zfmisc_1('#skF_8', '#skF_9')) | ~r2_hidden(B_111, '#skF_7') | ~r2_hidden(A_110, '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_44, c_306])).
% 3.70/1.59  tff(c_30, plain, (![B_16, D_18, A_15, C_17]: (r2_hidden(B_16, D_18) | ~r2_hidden(k4_tarski(A_15, B_16), k2_zfmisc_1(C_17, D_18)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.70/1.59  tff(c_652, plain, (![B_111, A_110]: (r2_hidden(B_111, '#skF_9') | ~r2_hidden(B_111, '#skF_7') | ~r2_hidden(A_110, '#skF_6'))), inference(resolution, [status(thm)], [c_632, c_30])).
% 3.70/1.59  tff(c_749, plain, (![A_120]: (~r2_hidden(A_120, '#skF_6'))), inference(splitLeft, [status(thm)], [c_652])).
% 3.70/1.59  tff(c_801, plain, (v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_4, c_749])).
% 3.70/1.59  tff(c_804, plain, (k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_801, c_92])).
% 3.70/1.59  tff(c_810, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_804])).
% 3.70/1.59  tff(c_823, plain, (![B_123]: (r2_hidden(B_123, '#skF_9') | ~r2_hidden(B_123, '#skF_7'))), inference(splitRight, [status(thm)], [c_652])).
% 3.70/1.59  tff(c_1014, plain, (![B_131]: (r2_hidden('#skF_2'('#skF_7', B_131), '#skF_9') | r1_tarski('#skF_7', B_131))), inference(resolution, [status(thm)], [c_10, c_823])).
% 3.70/1.59  tff(c_1024, plain, (r1_tarski('#skF_7', '#skF_9')), inference(resolution, [status(thm)], [c_1014, c_8])).
% 3.70/1.59  tff(c_1034, plain, $false, inference(negUnitSimplification, [status(thm)], [c_710, c_710, c_1024])).
% 3.70/1.59  tff(c_1035, plain, ('#skF_7'='#skF_9'), inference(splitRight, [status(thm)], [c_706])).
% 3.70/1.59  tff(c_677, plain, (![B_112]: (~v1_xboole_0('#skF_7') | ~r2_hidden(B_112, '#skF_9'))), inference(resolution, [status(thm)], [c_656, c_2])).
% 3.70/1.59  tff(c_678, plain, (~v1_xboole_0('#skF_7')), inference(splitLeft, [status(thm)], [c_677])).
% 3.70/1.59  tff(c_1040, plain, (~v1_xboole_0('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_1035, c_678])).
% 3.70/1.59  tff(c_653, plain, (![A_110, B_111]: (r2_hidden(A_110, '#skF_8') | ~r2_hidden(B_111, '#skF_7') | ~r2_hidden(A_110, '#skF_6'))), inference(resolution, [status(thm)], [c_632, c_32])).
% 3.70/1.59  tff(c_1074, plain, (![A_110, B_111]: (r2_hidden(A_110, '#skF_8') | ~r2_hidden(B_111, '#skF_9') | ~r2_hidden(A_110, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_1035, c_653])).
% 3.70/1.59  tff(c_1077, plain, (![B_134]: (~r2_hidden(B_134, '#skF_9'))), inference(splitLeft, [status(thm)], [c_1074])).
% 3.70/1.59  tff(c_1119, plain, (v1_xboole_0('#skF_9')), inference(resolution, [status(thm)], [c_4, c_1077])).
% 3.70/1.59  tff(c_1132, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1040, c_1119])).
% 3.70/1.59  tff(c_1134, plain, (![A_135]: (r2_hidden(A_135, '#skF_8') | ~r2_hidden(A_135, '#skF_6'))), inference(splitRight, [status(thm)], [c_1074])).
% 3.70/1.59  tff(c_1279, plain, (![B_141]: (r2_hidden('#skF_2'('#skF_6', B_141), '#skF_8') | r1_tarski('#skF_6', B_141))), inference(resolution, [status(thm)], [c_10, c_1134])).
% 3.70/1.59  tff(c_1290, plain, (r1_tarski('#skF_6', '#skF_8')), inference(resolution, [status(thm)], [c_1279, c_8])).
% 3.70/1.59  tff(c_1303, plain, ('#skF_6'='#skF_8' | ~r1_tarski('#skF_8', '#skF_6')), inference(resolution, [status(thm)], [c_1290, c_22])).
% 3.70/1.59  tff(c_1312, plain, (~r1_tarski('#skF_8', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_47, c_1303])).
% 3.70/1.59  tff(c_124, plain, (![A_50, C_51, B_52, D_53]: (r2_hidden(A_50, C_51) | ~r2_hidden(k4_tarski(A_50, B_52), k2_zfmisc_1(C_51, D_53)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.70/1.59  tff(c_127, plain, (![A_50, B_52]: (r2_hidden(A_50, '#skF_6') | ~r2_hidden(k4_tarski(A_50, B_52), k2_zfmisc_1('#skF_8', '#skF_9')))), inference(superposition, [status(thm), theory('equality')], [c_44, c_124])).
% 3.70/1.59  tff(c_330, plain, (![A_91, B_92]: (r2_hidden(A_91, '#skF_6') | ~r2_hidden(B_92, '#skF_9') | ~r2_hidden(A_91, '#skF_8'))), inference(resolution, [status(thm)], [c_306, c_127])).
% 3.70/1.59  tff(c_1332, plain, (![B_146]: (~r2_hidden(B_146, '#skF_9'))), inference(splitLeft, [status(thm)], [c_330])).
% 3.70/1.59  tff(c_1384, plain, (v1_xboole_0('#skF_9')), inference(resolution, [status(thm)], [c_4, c_1332])).
% 3.70/1.59  tff(c_1399, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1040, c_1384])).
% 3.70/1.59  tff(c_1401, plain, (![A_147]: (r2_hidden(A_147, '#skF_6') | ~r2_hidden(A_147, '#skF_8'))), inference(splitRight, [status(thm)], [c_330])).
% 3.70/1.59  tff(c_1438, plain, (![A_148]: (r1_tarski(A_148, '#skF_6') | ~r2_hidden('#skF_2'(A_148, '#skF_6'), '#skF_8'))), inference(resolution, [status(thm)], [c_1401, c_8])).
% 3.70/1.59  tff(c_1450, plain, (r1_tarski('#skF_8', '#skF_6')), inference(resolution, [status(thm)], [c_10, c_1438])).
% 3.70/1.59  tff(c_1457, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1312, c_1312, c_1450])).
% 3.70/1.59  tff(c_1459, plain, (v1_xboole_0('#skF_7')), inference(splitRight, [status(thm)], [c_677])).
% 3.70/1.59  tff(c_1462, plain, (k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_1459, c_92])).
% 3.70/1.59  tff(c_1468, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_1462])).
% 3.70/1.59  tff(c_1469, plain, ('#skF_7'!='#skF_9'), inference(splitRight, [status(thm)], [c_38])).
% 3.70/1.59  tff(c_1470, plain, ('#skF_6'='#skF_8'), inference(splitRight, [status(thm)], [c_38])).
% 3.70/1.59  tff(c_1471, plain, (k1_xboole_0!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_1470, c_42])).
% 3.70/1.59  tff(c_1754, plain, (![A_217, B_218, C_219, D_220]: (r2_hidden(k4_tarski(A_217, B_218), k2_zfmisc_1(C_219, D_220)) | ~r2_hidden(B_218, D_220) | ~r2_hidden(A_217, C_219))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.70/1.59  tff(c_1482, plain, (k2_zfmisc_1('#skF_8', '#skF_7')=k2_zfmisc_1('#skF_8', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_1470, c_44])).
% 3.70/1.59  tff(c_1562, plain, (![B_174, D_175, A_176, C_177]: (r2_hidden(B_174, D_175) | ~r2_hidden(k4_tarski(A_176, B_174), k2_zfmisc_1(C_177, D_175)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.70/1.59  tff(c_1565, plain, (![B_174, A_176]: (r2_hidden(B_174, '#skF_7') | ~r2_hidden(k4_tarski(A_176, B_174), k2_zfmisc_1('#skF_8', '#skF_9')))), inference(superposition, [status(thm), theory('equality')], [c_1482, c_1562])).
% 3.70/1.59  tff(c_1773, plain, (![B_218, A_217]: (r2_hidden(B_218, '#skF_7') | ~r2_hidden(B_218, '#skF_9') | ~r2_hidden(A_217, '#skF_8'))), inference(resolution, [status(thm)], [c_1754, c_1565])).
% 3.70/1.59  tff(c_1779, plain, (![A_221]: (~r2_hidden(A_221, '#skF_8'))), inference(splitLeft, [status(thm)], [c_1773])).
% 3.70/1.59  tff(c_1836, plain, (v1_xboole_0('#skF_8')), inference(resolution, [status(thm)], [c_4, c_1779])).
% 3.70/1.59  tff(c_1494, plain, (![A_154, B_155]: (r2_hidden('#skF_2'(A_154, B_155), A_154) | r1_tarski(A_154, B_155))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.70/1.59  tff(c_1498, plain, (![A_154, B_155]: (~v1_xboole_0(A_154) | r1_tarski(A_154, B_155))), inference(resolution, [status(thm)], [c_1494, c_2])).
% 3.70/1.59  tff(c_1499, plain, (![A_156, B_157]: (~v1_xboole_0(A_156) | r1_tarski(A_156, B_157))), inference(resolution, [status(thm)], [c_1494, c_2])).
% 3.70/1.59  tff(c_1503, plain, (![B_158, A_159]: (B_158=A_159 | ~r1_tarski(B_158, A_159) | ~v1_xboole_0(A_159))), inference(resolution, [status(thm)], [c_1499, c_22])).
% 3.70/1.59  tff(c_1513, plain, (![B_160, A_161]: (B_160=A_161 | ~v1_xboole_0(B_160) | ~v1_xboole_0(A_161))), inference(resolution, [status(thm)], [c_1498, c_1503])).
% 3.70/1.59  tff(c_1516, plain, (![A_161]: (k1_xboole_0=A_161 | ~v1_xboole_0(A_161))), inference(resolution, [status(thm)], [c_12, c_1513])).
% 3.70/1.59  tff(c_1839, plain, (k1_xboole_0='#skF_8'), inference(resolution, [status(thm)], [c_1836, c_1516])).
% 3.70/1.59  tff(c_1845, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1471, c_1839])).
% 3.70/1.59  tff(c_1867, plain, (![B_224]: (r2_hidden(B_224, '#skF_7') | ~r2_hidden(B_224, '#skF_9'))), inference(splitRight, [status(thm)], [c_1773])).
% 3.70/1.59  tff(c_1890, plain, (![A_225]: (r1_tarski(A_225, '#skF_7') | ~r2_hidden('#skF_2'(A_225, '#skF_7'), '#skF_9'))), inference(resolution, [status(thm)], [c_1867, c_8])).
% 3.70/1.59  tff(c_1900, plain, (r1_tarski('#skF_9', '#skF_7')), inference(resolution, [status(thm)], [c_10, c_1890])).
% 3.70/1.59  tff(c_1914, plain, ('#skF_7'='#skF_9' | ~r1_tarski('#skF_7', '#skF_9')), inference(resolution, [status(thm)], [c_1900, c_22])).
% 3.70/1.59  tff(c_1923, plain, (~r1_tarski('#skF_7', '#skF_9')), inference(negUnitSimplification, [status(thm)], [c_1469, c_1914])).
% 3.70/1.59  tff(c_1847, plain, (![A_222, B_223]: (r2_hidden(k4_tarski(A_222, B_223), k2_zfmisc_1('#skF_8', '#skF_9')) | ~r2_hidden(B_223, '#skF_7') | ~r2_hidden(A_222, '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_1482, c_1754])).
% 3.70/1.59  tff(c_1864, plain, (![B_223, A_222]: (r2_hidden(B_223, '#skF_9') | ~r2_hidden(B_223, '#skF_7') | ~r2_hidden(A_222, '#skF_8'))), inference(resolution, [status(thm)], [c_1847, c_30])).
% 3.70/1.59  tff(c_1967, plain, (![A_232]: (~r2_hidden(A_232, '#skF_8'))), inference(splitLeft, [status(thm)], [c_1864])).
% 3.70/1.59  tff(c_2024, plain, (v1_xboole_0('#skF_8')), inference(resolution, [status(thm)], [c_4, c_1967])).
% 3.70/1.59  tff(c_2027, plain, (k1_xboole_0='#skF_8'), inference(resolution, [status(thm)], [c_2024, c_1516])).
% 3.70/1.59  tff(c_2033, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1471, c_2027])).
% 3.70/1.59  tff(c_2035, plain, (![B_233]: (r2_hidden(B_233, '#skF_9') | ~r2_hidden(B_233, '#skF_7'))), inference(splitRight, [status(thm)], [c_1864])).
% 3.70/1.59  tff(c_2159, plain, (![B_238]: (r2_hidden('#skF_2'('#skF_7', B_238), '#skF_9') | r1_tarski('#skF_7', B_238))), inference(resolution, [status(thm)], [c_10, c_2035])).
% 3.70/1.59  tff(c_2169, plain, (r1_tarski('#skF_7', '#skF_9')), inference(resolution, [status(thm)], [c_2159, c_8])).
% 3.70/1.59  tff(c_2179, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1923, c_1923, c_2169])).
% 3.70/1.59  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.70/1.59  
% 3.70/1.59  Inference rules
% 3.70/1.59  ----------------------
% 3.70/1.59  #Ref     : 0
% 3.70/1.59  #Sup     : 444
% 3.70/1.59  #Fact    : 0
% 3.70/1.59  #Define  : 0
% 3.70/1.59  #Split   : 18
% 3.70/1.59  #Chain   : 0
% 3.70/1.59  #Close   : 0
% 3.70/1.59  
% 3.70/1.59  Ordering : KBO
% 3.70/1.59  
% 3.70/1.59  Simplification rules
% 3.70/1.59  ----------------------
% 3.70/1.59  #Subsume      : 108
% 3.70/1.59  #Demod        : 43
% 3.70/1.59  #Tautology    : 73
% 3.70/1.59  #SimpNegUnit  : 25
% 3.70/1.59  #BackRed      : 17
% 3.70/1.59  
% 3.70/1.59  #Partial instantiations: 0
% 3.70/1.59  #Strategies tried      : 1
% 3.70/1.59  
% 3.70/1.59  Timing (in seconds)
% 3.70/1.59  ----------------------
% 3.70/1.60  Preprocessing        : 0.29
% 3.70/1.60  Parsing              : 0.15
% 3.70/1.60  CNF conversion       : 0.02
% 3.70/1.60  Main loop            : 0.52
% 3.70/1.60  Inferencing          : 0.20
% 3.70/1.60  Reduction            : 0.12
% 3.70/1.60  Demodulation         : 0.08
% 3.70/1.60  BG Simplification    : 0.03
% 3.70/1.60  Subsumption          : 0.12
% 3.70/1.60  Abstraction          : 0.02
% 3.70/1.60  MUC search           : 0.00
% 3.70/1.60  Cooper               : 0.00
% 3.70/1.60  Total                : 0.86
% 3.70/1.60  Index Insertion      : 0.00
% 3.70/1.60  Index Deletion       : 0.00
% 3.70/1.60  Index Matching       : 0.00
% 3.70/1.60  BG Taut test         : 0.00
%------------------------------------------------------------------------------
