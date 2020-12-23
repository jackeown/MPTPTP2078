%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0077+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:35:41 EST 2020

% Result     : Theorem 3.84s
% Output     : CNFRefutation 3.96s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 218 expanded)
%              Number of leaves         :   19 (  76 expanded)
%              Depth                    :    8
%              Number of atoms          :  152 ( 601 expanded)
%              Number of equality atoms :    1 (   7 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k2_xboole_0 > #nlpp > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_9 > #skF_8 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_72,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
            & r1_xboole_0(A,B)
            & r1_xboole_0(A,C) )
        & ~ ( ~ ( r1_xboole_0(A,B)
                & r1_xboole_0(A,C) )
            & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(c_38,plain,
    ( ~ r1_xboole_0('#skF_4','#skF_6')
    | ~ r1_xboole_0('#skF_4','#skF_5')
    | ~ r1_xboole_0('#skF_7',k2_xboole_0('#skF_8','#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_971,plain,(
    ~ r1_xboole_0('#skF_7',k2_xboole_0('#skF_8','#skF_9')) ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_36,plain,
    ( r1_xboole_0('#skF_4',k2_xboole_0('#skF_5','#skF_6'))
    | ~ r1_xboole_0('#skF_7',k2_xboole_0('#skF_8','#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_86,plain,(
    ~ r1_xboole_0('#skF_7',k2_xboole_0('#skF_8','#skF_9')) ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_26,plain,(
    ! [A_9,B_10] :
      ( r2_hidden('#skF_3'(A_9,B_10),A_9)
      | r1_xboole_0(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_126,plain,(
    ! [D_35,B_36,A_37] :
      ( r2_hidden(D_35,B_36)
      | r2_hidden(D_35,A_37)
      | ~ r2_hidden(D_35,k2_xboole_0(A_37,B_36)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_863,plain,(
    ! [A_90,B_91,B_92] :
      ( r2_hidden('#skF_3'(k2_xboole_0(A_90,B_91),B_92),B_91)
      | r2_hidden('#skF_3'(k2_xboole_0(A_90,B_91),B_92),A_90)
      | r1_xboole_0(k2_xboole_0(A_90,B_91),B_92) ) ),
    inference(resolution,[status(thm)],[c_26,c_126])).

tff(c_24,plain,(
    ! [A_9,B_10] :
      ( r2_hidden('#skF_3'(A_9,B_10),B_10)
      | r1_xboole_0(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_28,plain,
    ( r1_xboole_0('#skF_4',k2_xboole_0('#skF_5','#skF_6'))
    | r1_xboole_0('#skF_7','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_51,plain,(
    r1_xboole_0('#skF_7','#skF_9') ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_62,plain,(
    ! [A_26,B_27,C_28] :
      ( ~ r1_xboole_0(A_26,B_27)
      | ~ r2_hidden(C_28,B_27)
      | ~ r2_hidden(C_28,A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_75,plain,(
    ! [C_29] :
      ( ~ r2_hidden(C_29,'#skF_9')
      | ~ r2_hidden(C_29,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_51,c_62])).

tff(c_84,plain,(
    ! [A_9] :
      ( ~ r2_hidden('#skF_3'(A_9,'#skF_7'),'#skF_9')
      | r1_xboole_0(A_9,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_24,c_75])).

tff(c_922,plain,(
    ! [A_93] :
      ( r2_hidden('#skF_3'(k2_xboole_0(A_93,'#skF_9'),'#skF_7'),A_93)
      | r1_xboole_0(k2_xboole_0(A_93,'#skF_9'),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_863,c_84])).

tff(c_32,plain,
    ( r1_xboole_0('#skF_4',k2_xboole_0('#skF_5','#skF_6'))
    | r1_xboole_0('#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_40,plain,(
    r1_xboole_0('#skF_7','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_87,plain,(
    ! [C_30] :
      ( ~ r2_hidden(C_30,'#skF_8')
      | ~ r2_hidden(C_30,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_40,c_62])).

tff(c_96,plain,(
    ! [A_9] :
      ( ~ r2_hidden('#skF_3'(A_9,'#skF_7'),'#skF_8')
      | r1_xboole_0(A_9,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_24,c_87])).

tff(c_950,plain,(
    r1_xboole_0(k2_xboole_0('#skF_8','#skF_9'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_922,c_96])).

tff(c_20,plain,(
    ! [B_8,A_7] :
      ( r1_xboole_0(B_8,A_7)
      | ~ r1_xboole_0(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_957,plain,(
    r1_xboole_0('#skF_7',k2_xboole_0('#skF_8','#skF_9')) ),
    inference(resolution,[status(thm)],[c_950,c_20])).

tff(c_962,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_957])).

tff(c_964,plain,(
    r1_xboole_0('#skF_7',k2_xboole_0('#skF_8','#skF_9')) ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_972,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_971,c_964])).

tff(c_973,plain,
    ( ~ r1_xboole_0('#skF_4','#skF_5')
    | ~ r1_xboole_0('#skF_4','#skF_6') ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_989,plain,(
    ~ r1_xboole_0('#skF_4','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_973])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( ~ r2_hidden(D_6,B_2)
      | r2_hidden(D_6,k2_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_963,plain,(
    r1_xboole_0('#skF_4',k2_xboole_0('#skF_5','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_22,plain,(
    ! [A_9,B_10,C_13] :
      ( ~ r1_xboole_0(A_9,B_10)
      | ~ r2_hidden(C_13,B_10)
      | ~ r2_hidden(C_13,A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1029,plain,(
    ! [C_96] :
      ( ~ r2_hidden(C_96,k2_xboole_0('#skF_5','#skF_6'))
      | ~ r2_hidden(C_96,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_963,c_22])).

tff(c_1050,plain,(
    ! [D_97] :
      ( ~ r2_hidden(D_97,'#skF_4')
      | ~ r2_hidden(D_97,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_4,c_1029])).

tff(c_1119,plain,(
    ! [A_106] :
      ( ~ r2_hidden('#skF_3'(A_106,'#skF_6'),'#skF_4')
      | r1_xboole_0(A_106,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_24,c_1050])).

tff(c_1123,plain,(
    r1_xboole_0('#skF_4','#skF_6') ),
    inference(resolution,[status(thm)],[c_26,c_1119])).

tff(c_1127,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_989,c_989,c_1123])).

tff(c_1128,plain,(
    ~ r1_xboole_0('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_973])).

tff(c_6,plain,(
    ! [D_6,A_1,B_2] :
      ( ~ r2_hidden(D_6,A_1)
      | r2_hidden(D_6,k2_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1180,plain,(
    ! [C_111] :
      ( ~ r2_hidden(C_111,k2_xboole_0('#skF_5','#skF_6'))
      | ~ r2_hidden(C_111,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_963,c_22])).

tff(c_1221,plain,(
    ! [D_116] :
      ( ~ r2_hidden(D_116,'#skF_4')
      | ~ r2_hidden(D_116,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_6,c_1180])).

tff(c_1304,plain,(
    ! [A_127] :
      ( ~ r2_hidden('#skF_3'(A_127,'#skF_5'),'#skF_4')
      | r1_xboole_0(A_127,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_24,c_1221])).

tff(c_1308,plain,(
    r1_xboole_0('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_26,c_1304])).

tff(c_1312,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1128,c_1128,c_1308])).

tff(c_1314,plain,(
    ~ r1_xboole_0('#skF_7','#skF_9') ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_30,plain,
    ( ~ r1_xboole_0('#skF_4','#skF_6')
    | ~ r1_xboole_0('#skF_4','#skF_5')
    | r1_xboole_0('#skF_7','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_1315,plain,
    ( ~ r1_xboole_0('#skF_4','#skF_6')
    | ~ r1_xboole_0('#skF_4','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_1314,c_30])).

tff(c_1316,plain,(
    ~ r1_xboole_0('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_1315])).

tff(c_1313,plain,(
    r1_xboole_0('#skF_4',k2_xboole_0('#skF_5','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_1326,plain,(
    ! [A_130,B_131,C_132] :
      ( ~ r1_xboole_0(A_130,B_131)
      | ~ r2_hidden(C_132,B_131)
      | ~ r2_hidden(C_132,A_130) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1350,plain,(
    ! [C_134] :
      ( ~ r2_hidden(C_134,k2_xboole_0('#skF_5','#skF_6'))
      | ~ r2_hidden(C_134,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1313,c_1326])).

tff(c_1383,plain,(
    ! [D_136] :
      ( ~ r2_hidden(D_136,'#skF_4')
      | ~ r2_hidden(D_136,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_6,c_1350])).

tff(c_1448,plain,(
    ! [B_143] :
      ( ~ r2_hidden('#skF_3'('#skF_5',B_143),'#skF_4')
      | r1_xboole_0('#skF_5',B_143) ) ),
    inference(resolution,[status(thm)],[c_26,c_1383])).

tff(c_1453,plain,(
    r1_xboole_0('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_24,c_1448])).

tff(c_1457,plain,(
    r1_xboole_0('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_1453,c_20])).

tff(c_1462,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1316,c_1457])).

tff(c_1463,plain,(
    ~ r1_xboole_0('#skF_4','#skF_6') ),
    inference(splitRight,[status(thm)],[c_1315])).

tff(c_1483,plain,(
    ! [A_146,B_147,C_148] :
      ( ~ r1_xboole_0(A_146,B_147)
      | ~ r2_hidden(C_148,B_147)
      | ~ r2_hidden(C_148,A_146) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1543,plain,(
    ! [C_154] :
      ( ~ r2_hidden(C_154,k2_xboole_0('#skF_5','#skF_6'))
      | ~ r2_hidden(C_154,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1313,c_1483])).

tff(c_1564,plain,(
    ! [D_155] :
      ( ~ r2_hidden(D_155,'#skF_4')
      | ~ r2_hidden(D_155,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_4,c_1543])).

tff(c_1605,plain,(
    ! [A_160] :
      ( ~ r2_hidden('#skF_3'(A_160,'#skF_6'),'#skF_4')
      | r1_xboole_0(A_160,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_24,c_1564])).

tff(c_1609,plain,(
    r1_xboole_0('#skF_4','#skF_6') ),
    inference(resolution,[status(thm)],[c_26,c_1605])).

tff(c_1613,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1463,c_1463,c_1609])).

tff(c_1615,plain,(
    ~ r1_xboole_0('#skF_7','#skF_8') ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_1656,plain,(
    ~ r1_xboole_0('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_1614,plain,(
    r1_xboole_0('#skF_4',k2_xboole_0('#skF_5','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_1628,plain,(
    ! [A_171,B_172,C_173] :
      ( ~ r1_xboole_0(A_171,B_172)
      | ~ r2_hidden(C_173,B_172)
      | ~ r2_hidden(C_173,A_171) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1635,plain,(
    ! [C_174] :
      ( ~ r2_hidden(C_174,k2_xboole_0('#skF_5','#skF_6'))
      | ~ r2_hidden(C_174,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1614,c_1628])).

tff(c_1657,plain,(
    ! [D_175] :
      ( ~ r2_hidden(D_175,'#skF_4')
      | ~ r2_hidden(D_175,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_6,c_1635])).

tff(c_1680,plain,(
    ! [B_177] :
      ( ~ r2_hidden('#skF_3'('#skF_5',B_177),'#skF_4')
      | r1_xboole_0('#skF_5',B_177) ) ),
    inference(resolution,[status(thm)],[c_26,c_1657])).

tff(c_1685,plain,(
    r1_xboole_0('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_24,c_1680])).

tff(c_1689,plain,(
    r1_xboole_0('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_1685,c_20])).

tff(c_1694,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1656,c_1689])).

tff(c_1696,plain,(
    r1_xboole_0('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_1695,plain,
    ( ~ r1_xboole_0('#skF_4','#skF_6')
    | r1_xboole_0('#skF_7','#skF_9') ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_1710,plain,(
    ~ r1_xboole_0('#skF_4','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_1695])).

tff(c_1722,plain,(
    ! [D_179] :
      ( ~ r2_hidden(D_179,'#skF_4')
      | ~ r2_hidden(D_179,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_4,c_1635])).

tff(c_1751,plain,(
    ! [A_182] :
      ( ~ r2_hidden('#skF_3'(A_182,'#skF_6'),'#skF_4')
      | r1_xboole_0(A_182,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_24,c_1722])).

tff(c_1755,plain,(
    r1_xboole_0('#skF_4','#skF_6') ),
    inference(resolution,[status(thm)],[c_26,c_1751])).

tff(c_1759,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1710,c_1710,c_1755])).

tff(c_1761,plain,(
    r1_xboole_0('#skF_4','#skF_6') ),
    inference(splitRight,[status(thm)],[c_1695])).

tff(c_34,plain,
    ( ~ r1_xboole_0('#skF_4','#skF_6')
    | ~ r1_xboole_0('#skF_4','#skF_5')
    | r1_xboole_0('#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_1775,plain,(
    r1_xboole_0('#skF_7','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1696,c_1761,c_34])).

tff(c_1776,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1615,c_1775])).

%------------------------------------------------------------------------------
