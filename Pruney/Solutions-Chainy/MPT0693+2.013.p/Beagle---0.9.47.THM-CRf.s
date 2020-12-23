%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:52 EST 2020

% Result     : Theorem 40.00s
% Output     : CNFRefutation 40.00s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 180 expanded)
%              Number of leaves         :   26 (  75 expanded)
%              Depth                    :   10
%              Number of atoms          :  170 ( 488 expanded)
%              Number of equality atoms :   55 ( 139 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_1 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_65,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => k9_relat_1(B,k10_relat_1(B,A)) = k3_xboole_0(A,k9_relat_1(B,k1_relat_1(B))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_funct_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k10_relat_1(B,A) = k10_relat_1(B,k3_xboole_0(k2_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t168_relat_1)).

tff(f_36,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(A,k2_relat_1(B))
       => k9_relat_1(B,k10_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_funct_1)).

tff(f_46,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

tff(c_106,plain,(
    ! [A_44,B_45,C_46] :
      ( r2_hidden('#skF_1'(A_44,B_45,C_46),B_45)
      | r2_hidden('#skF_2'(A_44,B_45,C_46),C_46)
      | k3_xboole_0(A_44,B_45) = C_46 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,k3_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_125,plain,(
    ! [A_44,B_45,A_1,B_2] :
      ( r2_hidden('#skF_2'(A_44,B_45,k3_xboole_0(A_1,B_2)),B_2)
      | r2_hidden('#skF_1'(A_44,B_45,k3_xboole_0(A_1,B_2)),B_45)
      | k3_xboole_0(A_44,B_45) = k3_xboole_0(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_106,c_4])).

tff(c_127,plain,(
    ! [A_47,B_48,C_49] :
      ( r2_hidden('#skF_1'(A_47,B_48,C_49),A_47)
      | r2_hidden('#skF_2'(A_47,B_48,C_49),C_49)
      | k3_xboole_0(A_47,B_48) = C_49 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_146,plain,(
    ! [A_47,B_48,A_1,B_2] :
      ( r2_hidden('#skF_2'(A_47,B_48,k3_xboole_0(A_1,B_2)),B_2)
      | r2_hidden('#skF_1'(A_47,B_48,k3_xboole_0(A_1,B_2)),A_47)
      | k3_xboole_0(A_47,B_48) = k3_xboole_0(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_127,c_4])).

tff(c_2,plain,(
    ! [D_6,A_1,B_2] :
      ( r2_hidden(D_6,k3_xboole_0(A_1,B_2))
      | ~ r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_148,plain,(
    ! [A_50,B_51,C_52] :
      ( ~ r2_hidden('#skF_1'(A_50,B_51,C_52),C_52)
      | r2_hidden('#skF_2'(A_50,B_51,C_52),C_52)
      | k3_xboole_0(A_50,B_51) = C_52 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_1852,plain,(
    ! [A_168,B_169,A_170,B_171] :
      ( r2_hidden('#skF_2'(A_168,B_169,k3_xboole_0(A_170,B_171)),k3_xboole_0(A_170,B_171))
      | k3_xboole_0(A_170,B_171) = k3_xboole_0(A_168,B_169)
      | ~ r2_hidden('#skF_1'(A_168,B_169,k3_xboole_0(A_170,B_171)),B_171)
      | ~ r2_hidden('#skF_1'(A_168,B_169,k3_xboole_0(A_170,B_171)),A_170) ) ),
    inference(resolution,[status(thm)],[c_2,c_148])).

tff(c_10642,plain,(
    ! [A_561,B_562,A_563,B_564] :
      ( r2_hidden('#skF_2'(A_561,B_562,k3_xboole_0(A_563,B_564)),B_564)
      | k3_xboole_0(A_563,B_564) = k3_xboole_0(A_561,B_562)
      | ~ r2_hidden('#skF_1'(A_561,B_562,k3_xboole_0(A_563,B_564)),B_564)
      | ~ r2_hidden('#skF_1'(A_561,B_562,k3_xboole_0(A_563,B_564)),A_563) ) ),
    inference(resolution,[status(thm)],[c_1852,c_4])).

tff(c_10793,plain,(
    ! [A_565,B_566,A_567] :
      ( ~ r2_hidden('#skF_1'(A_565,B_566,k3_xboole_0(A_567,A_565)),A_567)
      | r2_hidden('#skF_2'(A_565,B_566,k3_xboole_0(A_567,A_565)),A_565)
      | k3_xboole_0(A_567,A_565) = k3_xboole_0(A_565,B_566) ) ),
    inference(resolution,[status(thm)],[c_146,c_10642])).

tff(c_10937,plain,(
    ! [B_2,B_45] :
      ( r2_hidden('#skF_2'(B_2,B_45,k3_xboole_0(B_45,B_2)),B_2)
      | k3_xboole_0(B_45,B_2) = k3_xboole_0(B_2,B_45) ) ),
    inference(resolution,[status(thm)],[c_125,c_10793])).

tff(c_16,plain,(
    ! [A_1,B_2,C_3] :
      ( r2_hidden('#skF_1'(A_1,B_2,C_3),B_2)
      | r2_hidden('#skF_2'(A_1,B_2,C_3),C_3)
      | k3_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_162,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_2'(A_1,B_2,B_2),B_2)
      | k3_xboole_0(A_1,B_2) = B_2 ) ),
    inference(resolution,[status(thm)],[c_16,c_148])).

tff(c_18,plain,(
    ! [A_1,B_2,C_3] :
      ( r2_hidden('#skF_1'(A_1,B_2,C_3),A_1)
      | r2_hidden('#skF_2'(A_1,B_2,C_3),C_3)
      | k3_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_257,plain,(
    ! [A_70,B_71,C_72] :
      ( r2_hidden('#skF_1'(A_70,B_71,C_72),A_70)
      | ~ r2_hidden('#skF_2'(A_70,B_71,C_72),B_71)
      | ~ r2_hidden('#skF_2'(A_70,B_71,C_72),A_70)
      | k3_xboole_0(A_70,B_71) = C_72 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_282,plain,(
    ! [A_73,C_74] :
      ( ~ r2_hidden('#skF_2'(A_73,C_74,C_74),A_73)
      | r2_hidden('#skF_1'(A_73,C_74,C_74),A_73)
      | k3_xboole_0(A_73,C_74) = C_74 ) ),
    inference(resolution,[status(thm)],[c_18,c_257])).

tff(c_8,plain,(
    ! [A_1,B_2,C_3] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2,C_3),C_3)
      | ~ r2_hidden('#skF_2'(A_1,B_2,C_3),B_2)
      | ~ r2_hidden('#skF_2'(A_1,B_2,C_3),A_1)
      | k3_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_302,plain,(
    ! [A_75] :
      ( ~ r2_hidden('#skF_2'(A_75,A_75,A_75),A_75)
      | k3_xboole_0(A_75,A_75) = A_75 ) ),
    inference(resolution,[status(thm)],[c_282,c_8])).

tff(c_319,plain,(
    ! [B_2] : k3_xboole_0(B_2,B_2) = B_2 ),
    inference(resolution,[status(thm)],[c_162,c_302])).

tff(c_6,plain,(
    ! [D_6,A_1,B_2] :
      ( r2_hidden(D_6,A_1)
      | ~ r2_hidden(D_6,k3_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_1511,plain,(
    ! [A_144,B_145,A_146,B_147] :
      ( r2_hidden('#skF_2'(A_144,B_145,k3_xboole_0(A_146,B_147)),A_146)
      | r2_hidden('#skF_1'(A_144,B_145,k3_xboole_0(A_146,B_147)),B_145)
      | k3_xboole_0(A_146,B_147) = k3_xboole_0(A_144,B_145) ) ),
    inference(resolution,[status(thm)],[c_106,c_6])).

tff(c_1583,plain,(
    ! [B_2,A_1,B_147,A_144,A_146] :
      ( r2_hidden('#skF_1'(A_144,k3_xboole_0(A_1,B_2),k3_xboole_0(A_146,B_147)),A_1)
      | r2_hidden('#skF_2'(A_144,k3_xboole_0(A_1,B_2),k3_xboole_0(A_146,B_147)),A_146)
      | k3_xboole_0(A_146,B_147) = k3_xboole_0(A_144,k3_xboole_0(A_1,B_2)) ) ),
    inference(resolution,[status(thm)],[c_1511,c_6])).

tff(c_677,plain,(
    ! [A_103,B_104,A_105,B_106] :
      ( r2_hidden('#skF_2'(A_103,B_104,k3_xboole_0(A_105,B_106)),B_106)
      | r2_hidden('#skF_1'(A_103,B_104,k3_xboole_0(A_105,B_106)),B_104)
      | k3_xboole_0(A_105,B_106) = k3_xboole_0(A_103,B_104) ) ),
    inference(resolution,[status(thm)],[c_106,c_4])).

tff(c_10,plain,(
    ! [A_1,B_2,C_3] :
      ( r2_hidden('#skF_1'(A_1,B_2,C_3),B_2)
      | ~ r2_hidden('#skF_2'(A_1,B_2,C_3),B_2)
      | ~ r2_hidden('#skF_2'(A_1,B_2,C_3),A_1)
      | k3_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_1586,plain,(
    ! [B_148,B_149,A_150] :
      ( ~ r2_hidden('#skF_2'(B_148,B_149,k3_xboole_0(A_150,B_148)),B_149)
      | r2_hidden('#skF_1'(B_148,B_149,k3_xboole_0(A_150,B_148)),B_149)
      | k3_xboole_0(B_148,B_149) = k3_xboole_0(A_150,B_148) ) ),
    inference(resolution,[status(thm)],[c_677,c_10])).

tff(c_43841,plain,(
    ! [B_1091,A_1092,B_1093,A_1094] :
      ( r2_hidden('#skF_1'(B_1091,k3_xboole_0(A_1092,B_1093),k3_xboole_0(A_1094,B_1091)),A_1092)
      | ~ r2_hidden('#skF_2'(B_1091,k3_xboole_0(A_1092,B_1093),k3_xboole_0(A_1094,B_1091)),k3_xboole_0(A_1092,B_1093))
      | k3_xboole_0(B_1091,k3_xboole_0(A_1092,B_1093)) = k3_xboole_0(A_1094,B_1091) ) ),
    inference(resolution,[status(thm)],[c_1586,c_6])).

tff(c_44625,plain,(
    ! [B_1105,A_1106,B_1107] :
      ( r2_hidden('#skF_1'(B_1105,k3_xboole_0(A_1106,B_1107),k3_xboole_0(k3_xboole_0(A_1106,B_1107),B_1105)),A_1106)
      | k3_xboole_0(k3_xboole_0(A_1106,B_1107),B_1105) = k3_xboole_0(B_1105,k3_xboole_0(A_1106,B_1107)) ) ),
    inference(resolution,[status(thm)],[c_1583,c_43841])).

tff(c_44719,plain,(
    ! [B_1105,B_2] :
      ( r2_hidden('#skF_1'(B_1105,B_2,k3_xboole_0(k3_xboole_0(B_2,B_2),B_1105)),B_2)
      | k3_xboole_0(k3_xboole_0(B_2,B_2),B_1105) = k3_xboole_0(B_1105,k3_xboole_0(B_2,B_2)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_319,c_44625])).

tff(c_44742,plain,(
    ! [B_1105,B_2] :
      ( r2_hidden('#skF_1'(B_1105,B_2,k3_xboole_0(B_2,B_1105)),B_2)
      | k3_xboole_0(B_2,B_1105) = k3_xboole_0(B_1105,B_2) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_319,c_319,c_319,c_44719])).

tff(c_1436,plain,(
    ! [A_140,B_141,A_142,B_143] :
      ( r2_hidden('#skF_2'(A_140,B_141,k3_xboole_0(A_142,B_143)),A_142)
      | r2_hidden('#skF_1'(A_140,B_141,k3_xboole_0(A_142,B_143)),A_140)
      | k3_xboole_0(A_142,B_143) = k3_xboole_0(A_140,B_141) ) ),
    inference(resolution,[status(thm)],[c_127,c_6])).

tff(c_12,plain,(
    ! [A_1,B_2,C_3] :
      ( r2_hidden('#skF_1'(A_1,B_2,C_3),A_1)
      | ~ r2_hidden('#skF_2'(A_1,B_2,C_3),B_2)
      | ~ r2_hidden('#skF_2'(A_1,B_2,C_3),A_1)
      | k3_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_1500,plain,(
    ! [A_140,A_142,B_143] :
      ( ~ r2_hidden('#skF_2'(A_140,A_142,k3_xboole_0(A_142,B_143)),A_140)
      | r2_hidden('#skF_1'(A_140,A_142,k3_xboole_0(A_142,B_143)),A_140)
      | k3_xboole_0(A_142,B_143) = k3_xboole_0(A_140,A_142) ) ),
    inference(resolution,[status(thm)],[c_1436,c_12])).

tff(c_126,plain,(
    ! [A_44,B_45,A_1,B_2] :
      ( r2_hidden('#skF_2'(A_44,B_45,k3_xboole_0(A_1,B_2)),A_1)
      | r2_hidden('#skF_1'(A_44,B_45,k3_xboole_0(A_1,B_2)),B_45)
      | k3_xboole_0(A_44,B_45) = k3_xboole_0(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_106,c_6])).

tff(c_147,plain,(
    ! [A_47,B_48,A_1,B_2] :
      ( r2_hidden('#skF_2'(A_47,B_48,k3_xboole_0(A_1,B_2)),A_1)
      | r2_hidden('#skF_1'(A_47,B_48,k3_xboole_0(A_1,B_2)),A_47)
      | k3_xboole_0(A_47,B_48) = k3_xboole_0(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_127,c_6])).

tff(c_8931,plain,(
    ! [A_505,B_506,A_507,B_508] :
      ( r2_hidden('#skF_2'(A_505,B_506,k3_xboole_0(A_507,B_508)),A_507)
      | k3_xboole_0(A_507,B_508) = k3_xboole_0(A_505,B_506)
      | ~ r2_hidden('#skF_1'(A_505,B_506,k3_xboole_0(A_507,B_508)),B_508)
      | ~ r2_hidden('#skF_1'(A_505,B_506,k3_xboole_0(A_507,B_508)),A_507) ) ),
    inference(resolution,[status(thm)],[c_1852,c_6])).

tff(c_9523,plain,(
    ! [A_522,B_523,A_524] :
      ( ~ r2_hidden('#skF_1'(A_522,B_523,k3_xboole_0(A_524,A_522)),A_524)
      | r2_hidden('#skF_2'(A_522,B_523,k3_xboole_0(A_524,A_522)),A_524)
      | k3_xboole_0(A_524,A_522) = k3_xboole_0(A_522,B_523) ) ),
    inference(resolution,[status(thm)],[c_147,c_8931])).

tff(c_9720,plain,(
    ! [B_525,B_526] :
      ( r2_hidden('#skF_2'(B_525,B_526,k3_xboole_0(B_526,B_525)),B_526)
      | k3_xboole_0(B_526,B_525) = k3_xboole_0(B_525,B_526) ) ),
    inference(resolution,[status(thm)],[c_126,c_9523])).

tff(c_186,plain,(
    ! [A_57,B_58,C_59] :
      ( ~ r2_hidden('#skF_1'(A_57,B_58,C_59),C_59)
      | ~ r2_hidden('#skF_2'(A_57,B_58,C_59),B_58)
      | ~ r2_hidden('#skF_2'(A_57,B_58,C_59),A_57)
      | k3_xboole_0(A_57,B_58) = C_59 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_198,plain,(
    ! [A_57,B_58,A_1,B_2] :
      ( ~ r2_hidden('#skF_2'(A_57,B_58,k3_xboole_0(A_1,B_2)),B_58)
      | ~ r2_hidden('#skF_2'(A_57,B_58,k3_xboole_0(A_1,B_2)),A_57)
      | k3_xboole_0(A_57,B_58) = k3_xboole_0(A_1,B_2)
      | ~ r2_hidden('#skF_1'(A_57,B_58,k3_xboole_0(A_1,B_2)),B_2)
      | ~ r2_hidden('#skF_1'(A_57,B_58,k3_xboole_0(A_1,B_2)),A_1) ) ),
    inference(resolution,[status(thm)],[c_2,c_186])).

tff(c_91162,plain,(
    ! [B_1552,B_1553] :
      ( ~ r2_hidden('#skF_2'(B_1552,B_1553,k3_xboole_0(B_1553,B_1552)),B_1552)
      | ~ r2_hidden('#skF_1'(B_1552,B_1553,k3_xboole_0(B_1553,B_1552)),B_1552)
      | ~ r2_hidden('#skF_1'(B_1552,B_1553,k3_xboole_0(B_1553,B_1552)),B_1553)
      | k3_xboole_0(B_1553,B_1552) = k3_xboole_0(B_1552,B_1553) ) ),
    inference(resolution,[status(thm)],[c_9720,c_198])).

tff(c_91658,plain,(
    ! [B_1559,A_1560] :
      ( ~ r2_hidden('#skF_1'(B_1559,A_1560,k3_xboole_0(A_1560,B_1559)),A_1560)
      | ~ r2_hidden('#skF_2'(B_1559,A_1560,k3_xboole_0(A_1560,B_1559)),B_1559)
      | k3_xboole_0(B_1559,A_1560) = k3_xboole_0(A_1560,B_1559) ) ),
    inference(resolution,[status(thm)],[c_1500,c_91162])).

tff(c_91851,plain,(
    ! [B_1561,B_1562] :
      ( ~ r2_hidden('#skF_2'(B_1561,B_1562,k3_xboole_0(B_1562,B_1561)),B_1561)
      | k3_xboole_0(B_1562,B_1561) = k3_xboole_0(B_1561,B_1562) ) ),
    inference(resolution,[status(thm)],[c_44742,c_91658])).

tff(c_91998,plain,(
    ! [B_45,B_2] : k3_xboole_0(B_45,B_2) = k3_xboole_0(B_2,B_45) ),
    inference(resolution,[status(thm)],[c_10937,c_91851])).

tff(c_38,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_36,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_30,plain,(
    ! [B_18,A_17] :
      ( k10_relat_1(B_18,k3_xboole_0(k2_relat_1(B_18),A_17)) = k10_relat_1(B_18,A_17)
      | ~ v1_relat_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_20,plain,(
    ! [A_7,B_8] : r1_tarski(k3_xboole_0(A_7,B_8),A_7) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_101,plain,(
    ! [B_42,A_43] :
      ( k9_relat_1(B_42,k10_relat_1(B_42,A_43)) = A_43
      | ~ r1_tarski(A_43,k2_relat_1(B_42))
      | ~ v1_funct_1(B_42)
      | ~ v1_relat_1(B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_199,plain,(
    ! [B_60,B_61] :
      ( k9_relat_1(B_60,k10_relat_1(B_60,k3_xboole_0(k2_relat_1(B_60),B_61))) = k3_xboole_0(k2_relat_1(B_60),B_61)
      | ~ v1_funct_1(B_60)
      | ~ v1_relat_1(B_60) ) ),
    inference(resolution,[status(thm)],[c_20,c_101])).

tff(c_211,plain,(
    ! [B_62,A_63] :
      ( k9_relat_1(B_62,k10_relat_1(B_62,A_63)) = k3_xboole_0(k2_relat_1(B_62),A_63)
      | ~ v1_funct_1(B_62)
      | ~ v1_relat_1(B_62)
      | ~ v1_relat_1(B_62) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_199])).

tff(c_28,plain,(
    ! [A_16] :
      ( k9_relat_1(A_16,k1_relat_1(A_16)) = k2_relat_1(A_16)
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_34,plain,(
    k3_xboole_0('#skF_3',k9_relat_1('#skF_4',k1_relat_1('#skF_4'))) != k9_relat_1('#skF_4',k10_relat_1('#skF_4','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_80,plain,
    ( k9_relat_1('#skF_4',k10_relat_1('#skF_4','#skF_3')) != k3_xboole_0('#skF_3',k2_relat_1('#skF_4'))
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_34])).

tff(c_82,plain,(
    k9_relat_1('#skF_4',k10_relat_1('#skF_4','#skF_3')) != k3_xboole_0('#skF_3',k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_80])).

tff(c_221,plain,
    ( k3_xboole_0(k2_relat_1('#skF_4'),'#skF_3') != k3_xboole_0('#skF_3',k2_relat_1('#skF_4'))
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_211,c_82])).

tff(c_233,plain,(
    k3_xboole_0(k2_relat_1('#skF_4'),'#skF_3') != k3_xboole_0('#skF_3',k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_38,c_36,c_221])).

tff(c_92025,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_91998,c_233])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n006.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:02:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 40.00/29.01  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 40.00/29.02  
% 40.00/29.02  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 40.00/29.02  %$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_1 > #skF_3 > #skF_2 > #skF_4
% 40.00/29.02  
% 40.00/29.02  %Foreground sorts:
% 40.00/29.02  
% 40.00/29.02  
% 40.00/29.02  %Background operators:
% 40.00/29.02  
% 40.00/29.02  
% 40.00/29.02  %Foreground operators:
% 40.00/29.02  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 40.00/29.02  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 40.00/29.02  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 40.00/29.02  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 40.00/29.02  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 40.00/29.02  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 40.00/29.02  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 40.00/29.02  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 40.00/29.02  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 40.00/29.02  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 40.00/29.02  tff('#skF_3', type, '#skF_3': $i).
% 40.00/29.02  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 40.00/29.02  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 40.00/29.02  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 40.00/29.02  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 40.00/29.02  tff('#skF_4', type, '#skF_4': $i).
% 40.00/29.02  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 40.00/29.02  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 40.00/29.02  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 40.00/29.02  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 40.00/29.02  
% 40.00/29.04  tff(f_34, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 40.00/29.04  tff(f_65, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (k9_relat_1(B, k10_relat_1(B, A)) = k3_xboole_0(A, k9_relat_1(B, k1_relat_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_funct_1)).
% 40.00/29.04  tff(f_50, axiom, (![A, B]: (v1_relat_1(B) => (k10_relat_1(B, A) = k10_relat_1(B, k3_xboole_0(k2_relat_1(B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t168_relat_1)).
% 40.00/29.04  tff(f_36, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 40.00/29.04  tff(f_58, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(A, k2_relat_1(B)) => (k9_relat_1(B, k10_relat_1(B, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t147_funct_1)).
% 40.00/29.04  tff(f_46, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_relat_1)).
% 40.00/29.04  tff(c_106, plain, (![A_44, B_45, C_46]: (r2_hidden('#skF_1'(A_44, B_45, C_46), B_45) | r2_hidden('#skF_2'(A_44, B_45, C_46), C_46) | k3_xboole_0(A_44, B_45)=C_46)), inference(cnfTransformation, [status(thm)], [f_34])).
% 40.00/29.04  tff(c_4, plain, (![D_6, B_2, A_1]: (r2_hidden(D_6, B_2) | ~r2_hidden(D_6, k3_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 40.00/29.04  tff(c_125, plain, (![A_44, B_45, A_1, B_2]: (r2_hidden('#skF_2'(A_44, B_45, k3_xboole_0(A_1, B_2)), B_2) | r2_hidden('#skF_1'(A_44, B_45, k3_xboole_0(A_1, B_2)), B_45) | k3_xboole_0(A_44, B_45)=k3_xboole_0(A_1, B_2))), inference(resolution, [status(thm)], [c_106, c_4])).
% 40.00/29.04  tff(c_127, plain, (![A_47, B_48, C_49]: (r2_hidden('#skF_1'(A_47, B_48, C_49), A_47) | r2_hidden('#skF_2'(A_47, B_48, C_49), C_49) | k3_xboole_0(A_47, B_48)=C_49)), inference(cnfTransformation, [status(thm)], [f_34])).
% 40.00/29.04  tff(c_146, plain, (![A_47, B_48, A_1, B_2]: (r2_hidden('#skF_2'(A_47, B_48, k3_xboole_0(A_1, B_2)), B_2) | r2_hidden('#skF_1'(A_47, B_48, k3_xboole_0(A_1, B_2)), A_47) | k3_xboole_0(A_47, B_48)=k3_xboole_0(A_1, B_2))), inference(resolution, [status(thm)], [c_127, c_4])).
% 40.00/29.04  tff(c_2, plain, (![D_6, A_1, B_2]: (r2_hidden(D_6, k3_xboole_0(A_1, B_2)) | ~r2_hidden(D_6, B_2) | ~r2_hidden(D_6, A_1))), inference(cnfTransformation, [status(thm)], [f_34])).
% 40.00/29.04  tff(c_148, plain, (![A_50, B_51, C_52]: (~r2_hidden('#skF_1'(A_50, B_51, C_52), C_52) | r2_hidden('#skF_2'(A_50, B_51, C_52), C_52) | k3_xboole_0(A_50, B_51)=C_52)), inference(cnfTransformation, [status(thm)], [f_34])).
% 40.00/29.04  tff(c_1852, plain, (![A_168, B_169, A_170, B_171]: (r2_hidden('#skF_2'(A_168, B_169, k3_xboole_0(A_170, B_171)), k3_xboole_0(A_170, B_171)) | k3_xboole_0(A_170, B_171)=k3_xboole_0(A_168, B_169) | ~r2_hidden('#skF_1'(A_168, B_169, k3_xboole_0(A_170, B_171)), B_171) | ~r2_hidden('#skF_1'(A_168, B_169, k3_xboole_0(A_170, B_171)), A_170))), inference(resolution, [status(thm)], [c_2, c_148])).
% 40.00/29.04  tff(c_10642, plain, (![A_561, B_562, A_563, B_564]: (r2_hidden('#skF_2'(A_561, B_562, k3_xboole_0(A_563, B_564)), B_564) | k3_xboole_0(A_563, B_564)=k3_xboole_0(A_561, B_562) | ~r2_hidden('#skF_1'(A_561, B_562, k3_xboole_0(A_563, B_564)), B_564) | ~r2_hidden('#skF_1'(A_561, B_562, k3_xboole_0(A_563, B_564)), A_563))), inference(resolution, [status(thm)], [c_1852, c_4])).
% 40.00/29.04  tff(c_10793, plain, (![A_565, B_566, A_567]: (~r2_hidden('#skF_1'(A_565, B_566, k3_xboole_0(A_567, A_565)), A_567) | r2_hidden('#skF_2'(A_565, B_566, k3_xboole_0(A_567, A_565)), A_565) | k3_xboole_0(A_567, A_565)=k3_xboole_0(A_565, B_566))), inference(resolution, [status(thm)], [c_146, c_10642])).
% 40.00/29.04  tff(c_10937, plain, (![B_2, B_45]: (r2_hidden('#skF_2'(B_2, B_45, k3_xboole_0(B_45, B_2)), B_2) | k3_xboole_0(B_45, B_2)=k3_xboole_0(B_2, B_45))), inference(resolution, [status(thm)], [c_125, c_10793])).
% 40.00/29.04  tff(c_16, plain, (![A_1, B_2, C_3]: (r2_hidden('#skF_1'(A_1, B_2, C_3), B_2) | r2_hidden('#skF_2'(A_1, B_2, C_3), C_3) | k3_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_34])).
% 40.00/29.04  tff(c_162, plain, (![A_1, B_2]: (r2_hidden('#skF_2'(A_1, B_2, B_2), B_2) | k3_xboole_0(A_1, B_2)=B_2)), inference(resolution, [status(thm)], [c_16, c_148])).
% 40.00/29.04  tff(c_18, plain, (![A_1, B_2, C_3]: (r2_hidden('#skF_1'(A_1, B_2, C_3), A_1) | r2_hidden('#skF_2'(A_1, B_2, C_3), C_3) | k3_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_34])).
% 40.00/29.04  tff(c_257, plain, (![A_70, B_71, C_72]: (r2_hidden('#skF_1'(A_70, B_71, C_72), A_70) | ~r2_hidden('#skF_2'(A_70, B_71, C_72), B_71) | ~r2_hidden('#skF_2'(A_70, B_71, C_72), A_70) | k3_xboole_0(A_70, B_71)=C_72)), inference(cnfTransformation, [status(thm)], [f_34])).
% 40.00/29.04  tff(c_282, plain, (![A_73, C_74]: (~r2_hidden('#skF_2'(A_73, C_74, C_74), A_73) | r2_hidden('#skF_1'(A_73, C_74, C_74), A_73) | k3_xboole_0(A_73, C_74)=C_74)), inference(resolution, [status(thm)], [c_18, c_257])).
% 40.00/29.04  tff(c_8, plain, (![A_1, B_2, C_3]: (~r2_hidden('#skF_1'(A_1, B_2, C_3), C_3) | ~r2_hidden('#skF_2'(A_1, B_2, C_3), B_2) | ~r2_hidden('#skF_2'(A_1, B_2, C_3), A_1) | k3_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_34])).
% 40.00/29.04  tff(c_302, plain, (![A_75]: (~r2_hidden('#skF_2'(A_75, A_75, A_75), A_75) | k3_xboole_0(A_75, A_75)=A_75)), inference(resolution, [status(thm)], [c_282, c_8])).
% 40.00/29.04  tff(c_319, plain, (![B_2]: (k3_xboole_0(B_2, B_2)=B_2)), inference(resolution, [status(thm)], [c_162, c_302])).
% 40.00/29.04  tff(c_6, plain, (![D_6, A_1, B_2]: (r2_hidden(D_6, A_1) | ~r2_hidden(D_6, k3_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 40.00/29.04  tff(c_1511, plain, (![A_144, B_145, A_146, B_147]: (r2_hidden('#skF_2'(A_144, B_145, k3_xboole_0(A_146, B_147)), A_146) | r2_hidden('#skF_1'(A_144, B_145, k3_xboole_0(A_146, B_147)), B_145) | k3_xboole_0(A_146, B_147)=k3_xboole_0(A_144, B_145))), inference(resolution, [status(thm)], [c_106, c_6])).
% 40.00/29.04  tff(c_1583, plain, (![B_2, A_1, B_147, A_144, A_146]: (r2_hidden('#skF_1'(A_144, k3_xboole_0(A_1, B_2), k3_xboole_0(A_146, B_147)), A_1) | r2_hidden('#skF_2'(A_144, k3_xboole_0(A_1, B_2), k3_xboole_0(A_146, B_147)), A_146) | k3_xboole_0(A_146, B_147)=k3_xboole_0(A_144, k3_xboole_0(A_1, B_2)))), inference(resolution, [status(thm)], [c_1511, c_6])).
% 40.00/29.04  tff(c_677, plain, (![A_103, B_104, A_105, B_106]: (r2_hidden('#skF_2'(A_103, B_104, k3_xboole_0(A_105, B_106)), B_106) | r2_hidden('#skF_1'(A_103, B_104, k3_xboole_0(A_105, B_106)), B_104) | k3_xboole_0(A_105, B_106)=k3_xboole_0(A_103, B_104))), inference(resolution, [status(thm)], [c_106, c_4])).
% 40.00/29.04  tff(c_10, plain, (![A_1, B_2, C_3]: (r2_hidden('#skF_1'(A_1, B_2, C_3), B_2) | ~r2_hidden('#skF_2'(A_1, B_2, C_3), B_2) | ~r2_hidden('#skF_2'(A_1, B_2, C_3), A_1) | k3_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_34])).
% 40.00/29.04  tff(c_1586, plain, (![B_148, B_149, A_150]: (~r2_hidden('#skF_2'(B_148, B_149, k3_xboole_0(A_150, B_148)), B_149) | r2_hidden('#skF_1'(B_148, B_149, k3_xboole_0(A_150, B_148)), B_149) | k3_xboole_0(B_148, B_149)=k3_xboole_0(A_150, B_148))), inference(resolution, [status(thm)], [c_677, c_10])).
% 40.00/29.04  tff(c_43841, plain, (![B_1091, A_1092, B_1093, A_1094]: (r2_hidden('#skF_1'(B_1091, k3_xboole_0(A_1092, B_1093), k3_xboole_0(A_1094, B_1091)), A_1092) | ~r2_hidden('#skF_2'(B_1091, k3_xboole_0(A_1092, B_1093), k3_xboole_0(A_1094, B_1091)), k3_xboole_0(A_1092, B_1093)) | k3_xboole_0(B_1091, k3_xboole_0(A_1092, B_1093))=k3_xboole_0(A_1094, B_1091))), inference(resolution, [status(thm)], [c_1586, c_6])).
% 40.00/29.04  tff(c_44625, plain, (![B_1105, A_1106, B_1107]: (r2_hidden('#skF_1'(B_1105, k3_xboole_0(A_1106, B_1107), k3_xboole_0(k3_xboole_0(A_1106, B_1107), B_1105)), A_1106) | k3_xboole_0(k3_xboole_0(A_1106, B_1107), B_1105)=k3_xboole_0(B_1105, k3_xboole_0(A_1106, B_1107)))), inference(resolution, [status(thm)], [c_1583, c_43841])).
% 40.00/29.04  tff(c_44719, plain, (![B_1105, B_2]: (r2_hidden('#skF_1'(B_1105, B_2, k3_xboole_0(k3_xboole_0(B_2, B_2), B_1105)), B_2) | k3_xboole_0(k3_xboole_0(B_2, B_2), B_1105)=k3_xboole_0(B_1105, k3_xboole_0(B_2, B_2)))), inference(superposition, [status(thm), theory('equality')], [c_319, c_44625])).
% 40.00/29.04  tff(c_44742, plain, (![B_1105, B_2]: (r2_hidden('#skF_1'(B_1105, B_2, k3_xboole_0(B_2, B_1105)), B_2) | k3_xboole_0(B_2, B_1105)=k3_xboole_0(B_1105, B_2))), inference(demodulation, [status(thm), theory('equality')], [c_319, c_319, c_319, c_44719])).
% 40.00/29.04  tff(c_1436, plain, (![A_140, B_141, A_142, B_143]: (r2_hidden('#skF_2'(A_140, B_141, k3_xboole_0(A_142, B_143)), A_142) | r2_hidden('#skF_1'(A_140, B_141, k3_xboole_0(A_142, B_143)), A_140) | k3_xboole_0(A_142, B_143)=k3_xboole_0(A_140, B_141))), inference(resolution, [status(thm)], [c_127, c_6])).
% 40.00/29.04  tff(c_12, plain, (![A_1, B_2, C_3]: (r2_hidden('#skF_1'(A_1, B_2, C_3), A_1) | ~r2_hidden('#skF_2'(A_1, B_2, C_3), B_2) | ~r2_hidden('#skF_2'(A_1, B_2, C_3), A_1) | k3_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_34])).
% 40.00/29.04  tff(c_1500, plain, (![A_140, A_142, B_143]: (~r2_hidden('#skF_2'(A_140, A_142, k3_xboole_0(A_142, B_143)), A_140) | r2_hidden('#skF_1'(A_140, A_142, k3_xboole_0(A_142, B_143)), A_140) | k3_xboole_0(A_142, B_143)=k3_xboole_0(A_140, A_142))), inference(resolution, [status(thm)], [c_1436, c_12])).
% 40.00/29.04  tff(c_126, plain, (![A_44, B_45, A_1, B_2]: (r2_hidden('#skF_2'(A_44, B_45, k3_xboole_0(A_1, B_2)), A_1) | r2_hidden('#skF_1'(A_44, B_45, k3_xboole_0(A_1, B_2)), B_45) | k3_xboole_0(A_44, B_45)=k3_xboole_0(A_1, B_2))), inference(resolution, [status(thm)], [c_106, c_6])).
% 40.00/29.04  tff(c_147, plain, (![A_47, B_48, A_1, B_2]: (r2_hidden('#skF_2'(A_47, B_48, k3_xboole_0(A_1, B_2)), A_1) | r2_hidden('#skF_1'(A_47, B_48, k3_xboole_0(A_1, B_2)), A_47) | k3_xboole_0(A_47, B_48)=k3_xboole_0(A_1, B_2))), inference(resolution, [status(thm)], [c_127, c_6])).
% 40.00/29.04  tff(c_8931, plain, (![A_505, B_506, A_507, B_508]: (r2_hidden('#skF_2'(A_505, B_506, k3_xboole_0(A_507, B_508)), A_507) | k3_xboole_0(A_507, B_508)=k3_xboole_0(A_505, B_506) | ~r2_hidden('#skF_1'(A_505, B_506, k3_xboole_0(A_507, B_508)), B_508) | ~r2_hidden('#skF_1'(A_505, B_506, k3_xboole_0(A_507, B_508)), A_507))), inference(resolution, [status(thm)], [c_1852, c_6])).
% 40.00/29.04  tff(c_9523, plain, (![A_522, B_523, A_524]: (~r2_hidden('#skF_1'(A_522, B_523, k3_xboole_0(A_524, A_522)), A_524) | r2_hidden('#skF_2'(A_522, B_523, k3_xboole_0(A_524, A_522)), A_524) | k3_xboole_0(A_524, A_522)=k3_xboole_0(A_522, B_523))), inference(resolution, [status(thm)], [c_147, c_8931])).
% 40.00/29.04  tff(c_9720, plain, (![B_525, B_526]: (r2_hidden('#skF_2'(B_525, B_526, k3_xboole_0(B_526, B_525)), B_526) | k3_xboole_0(B_526, B_525)=k3_xboole_0(B_525, B_526))), inference(resolution, [status(thm)], [c_126, c_9523])).
% 40.00/29.04  tff(c_186, plain, (![A_57, B_58, C_59]: (~r2_hidden('#skF_1'(A_57, B_58, C_59), C_59) | ~r2_hidden('#skF_2'(A_57, B_58, C_59), B_58) | ~r2_hidden('#skF_2'(A_57, B_58, C_59), A_57) | k3_xboole_0(A_57, B_58)=C_59)), inference(cnfTransformation, [status(thm)], [f_34])).
% 40.00/29.04  tff(c_198, plain, (![A_57, B_58, A_1, B_2]: (~r2_hidden('#skF_2'(A_57, B_58, k3_xboole_0(A_1, B_2)), B_58) | ~r2_hidden('#skF_2'(A_57, B_58, k3_xboole_0(A_1, B_2)), A_57) | k3_xboole_0(A_57, B_58)=k3_xboole_0(A_1, B_2) | ~r2_hidden('#skF_1'(A_57, B_58, k3_xboole_0(A_1, B_2)), B_2) | ~r2_hidden('#skF_1'(A_57, B_58, k3_xboole_0(A_1, B_2)), A_1))), inference(resolution, [status(thm)], [c_2, c_186])).
% 40.00/29.04  tff(c_91162, plain, (![B_1552, B_1553]: (~r2_hidden('#skF_2'(B_1552, B_1553, k3_xboole_0(B_1553, B_1552)), B_1552) | ~r2_hidden('#skF_1'(B_1552, B_1553, k3_xboole_0(B_1553, B_1552)), B_1552) | ~r2_hidden('#skF_1'(B_1552, B_1553, k3_xboole_0(B_1553, B_1552)), B_1553) | k3_xboole_0(B_1553, B_1552)=k3_xboole_0(B_1552, B_1553))), inference(resolution, [status(thm)], [c_9720, c_198])).
% 40.00/29.04  tff(c_91658, plain, (![B_1559, A_1560]: (~r2_hidden('#skF_1'(B_1559, A_1560, k3_xboole_0(A_1560, B_1559)), A_1560) | ~r2_hidden('#skF_2'(B_1559, A_1560, k3_xboole_0(A_1560, B_1559)), B_1559) | k3_xboole_0(B_1559, A_1560)=k3_xboole_0(A_1560, B_1559))), inference(resolution, [status(thm)], [c_1500, c_91162])).
% 40.00/29.04  tff(c_91851, plain, (![B_1561, B_1562]: (~r2_hidden('#skF_2'(B_1561, B_1562, k3_xboole_0(B_1562, B_1561)), B_1561) | k3_xboole_0(B_1562, B_1561)=k3_xboole_0(B_1561, B_1562))), inference(resolution, [status(thm)], [c_44742, c_91658])).
% 40.00/29.04  tff(c_91998, plain, (![B_45, B_2]: (k3_xboole_0(B_45, B_2)=k3_xboole_0(B_2, B_45))), inference(resolution, [status(thm)], [c_10937, c_91851])).
% 40.00/29.04  tff(c_38, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_65])).
% 40.00/29.04  tff(c_36, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_65])).
% 40.00/29.04  tff(c_30, plain, (![B_18, A_17]: (k10_relat_1(B_18, k3_xboole_0(k2_relat_1(B_18), A_17))=k10_relat_1(B_18, A_17) | ~v1_relat_1(B_18))), inference(cnfTransformation, [status(thm)], [f_50])).
% 40.00/29.04  tff(c_20, plain, (![A_7, B_8]: (r1_tarski(k3_xboole_0(A_7, B_8), A_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 40.00/29.04  tff(c_101, plain, (![B_42, A_43]: (k9_relat_1(B_42, k10_relat_1(B_42, A_43))=A_43 | ~r1_tarski(A_43, k2_relat_1(B_42)) | ~v1_funct_1(B_42) | ~v1_relat_1(B_42))), inference(cnfTransformation, [status(thm)], [f_58])).
% 40.00/29.04  tff(c_199, plain, (![B_60, B_61]: (k9_relat_1(B_60, k10_relat_1(B_60, k3_xboole_0(k2_relat_1(B_60), B_61)))=k3_xboole_0(k2_relat_1(B_60), B_61) | ~v1_funct_1(B_60) | ~v1_relat_1(B_60))), inference(resolution, [status(thm)], [c_20, c_101])).
% 40.00/29.04  tff(c_211, plain, (![B_62, A_63]: (k9_relat_1(B_62, k10_relat_1(B_62, A_63))=k3_xboole_0(k2_relat_1(B_62), A_63) | ~v1_funct_1(B_62) | ~v1_relat_1(B_62) | ~v1_relat_1(B_62))), inference(superposition, [status(thm), theory('equality')], [c_30, c_199])).
% 40.00/29.04  tff(c_28, plain, (![A_16]: (k9_relat_1(A_16, k1_relat_1(A_16))=k2_relat_1(A_16) | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_46])).
% 40.00/29.04  tff(c_34, plain, (k3_xboole_0('#skF_3', k9_relat_1('#skF_4', k1_relat_1('#skF_4')))!=k9_relat_1('#skF_4', k10_relat_1('#skF_4', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_65])).
% 40.00/29.04  tff(c_80, plain, (k9_relat_1('#skF_4', k10_relat_1('#skF_4', '#skF_3'))!=k3_xboole_0('#skF_3', k2_relat_1('#skF_4')) | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_28, c_34])).
% 40.00/29.04  tff(c_82, plain, (k9_relat_1('#skF_4', k10_relat_1('#skF_4', '#skF_3'))!=k3_xboole_0('#skF_3', k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_80])).
% 40.00/29.04  tff(c_221, plain, (k3_xboole_0(k2_relat_1('#skF_4'), '#skF_3')!=k3_xboole_0('#skF_3', k2_relat_1('#skF_4')) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_211, c_82])).
% 40.00/29.04  tff(c_233, plain, (k3_xboole_0(k2_relat_1('#skF_4'), '#skF_3')!=k3_xboole_0('#skF_3', k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_38, c_36, c_221])).
% 40.00/29.04  tff(c_92025, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_91998, c_233])).
% 40.00/29.04  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 40.00/29.04  
% 40.00/29.04  Inference rules
% 40.00/29.04  ----------------------
% 40.00/29.04  #Ref     : 0
% 40.00/29.04  #Sup     : 23358
% 40.00/29.04  #Fact    : 0
% 40.00/29.04  #Define  : 0
% 40.00/29.04  #Split   : 0
% 40.00/29.04  #Chain   : 0
% 40.00/29.04  #Close   : 0
% 40.00/29.04  
% 40.00/29.04  Ordering : KBO
% 40.00/29.04  
% 40.00/29.04  Simplification rules
% 40.00/29.04  ----------------------
% 40.00/29.04  #Subsume      : 6766
% 40.00/29.04  #Demod        : 25820
% 40.00/29.04  #Tautology    : 2562
% 40.00/29.04  #SimpNegUnit  : 0
% 40.00/29.04  #BackRed      : 22
% 40.00/29.04  
% 40.00/29.04  #Partial instantiations: 0
% 40.00/29.04  #Strategies tried      : 1
% 40.00/29.04  
% 40.00/29.04  Timing (in seconds)
% 40.00/29.04  ----------------------
% 40.00/29.05  Preprocessing        : 0.29
% 40.00/29.05  Parsing              : 0.15
% 40.00/29.05  CNF conversion       : 0.02
% 40.00/29.05  Main loop            : 27.99
% 40.00/29.05  Inferencing          : 3.96
% 40.00/29.05  Reduction            : 4.30
% 40.00/29.05  Demodulation         : 3.29
% 40.00/29.05  BG Simplification    : 0.62
% 40.00/29.05  Subsumption          : 18.18
% 40.00/29.05  Abstraction          : 1.16
% 40.00/29.05  MUC search           : 0.00
% 40.00/29.05  Cooper               : 0.00
% 40.00/29.05  Total                : 28.32
% 40.00/29.05  Index Insertion      : 0.00
% 40.00/29.05  Index Deletion       : 0.00
% 40.00/29.05  Index Matching       : 0.00
% 40.00/29.05  BG Taut test         : 0.00
%------------------------------------------------------------------------------
