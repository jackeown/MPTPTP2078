%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0687+1.003 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:42 EST 2020

% Result     : Theorem 17.37s
% Output     : CNFRefutation 17.37s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 346 expanded)
%              Number of leaves         :   31 ( 133 expanded)
%              Depth                    :   13
%              Number of atoms          :  114 ( 583 expanded)
%              Number of equality atoms :   29 ( 154 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_xboole_0 > v1_relat_1 > k4_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > o_0_0_xboole_0 > k1_xboole_0 > #skF_6 > #skF_1 > #skF_11 > #skF_2 > #skF_8 > #skF_4 > #skF_3 > #skF_7 > #skF_9 > #skF_5 > #skF_12 > #skF_10

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff('#skF_10',type,(
    '#skF_10': ( $i * $i * $i ) > $i )).

tff(f_53,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

tff(f_57,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_boole)).

tff(f_70,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r2_hidden(A,k2_relat_1(B))
        <=> k10_relat_1(B,k1_tarski(A)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t142_funct_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_boole)).

tff(f_37,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( C = k10_relat_1(A,B)
        <=> ! [D] :
              ( r2_hidden(D,C)
            <=> ? [E] :
                  ( r2_hidden(k4_tarski(D,E),A)
                  & r2_hidden(E,B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d14_relat_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(c_44,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_59,plain,(
    ! [A_70] :
      ( k1_xboole_0 = A_70
      | ~ v1_xboole_0(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_63,plain,(
    o_0_0_xboole_0 = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_44,c_59])).

tff(c_64,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_44])).

tff(c_52,plain,
    ( k10_relat_1('#skF_12',k1_tarski('#skF_11')) = k1_xboole_0
    | ~ r2_hidden('#skF_11',k2_relat_1('#skF_12')) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_87,plain,(
    ~ r2_hidden('#skF_11',k2_relat_1('#skF_12')) ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_58,plain,
    ( r2_hidden('#skF_11',k2_relat_1('#skF_12'))
    | k10_relat_1('#skF_12',k1_tarski('#skF_11')) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_88,plain,(
    k10_relat_1('#skF_12',k1_tarski('#skF_11')) != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_87,c_58])).

tff(c_668,plain,(
    ! [A_168,B_169] :
      ( r2_hidden(k4_tarski('#skF_8'(A_168,B_169),'#skF_7'(A_168,B_169)),A_168)
      | r2_hidden('#skF_9'(A_168,B_169),B_169)
      | k2_relat_1(A_168) = B_169 ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_48,plain,(
    ! [B_69,A_68] :
      ( ~ v1_xboole_0(B_69)
      | ~ r2_hidden(A_68,B_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_755,plain,(
    ! [A_170,B_171] :
      ( ~ v1_xboole_0(A_170)
      | r2_hidden('#skF_9'(A_170,B_171),B_171)
      | k2_relat_1(A_170) = B_171 ) ),
    inference(resolution,[status(thm)],[c_668,c_48])).

tff(c_838,plain,(
    ! [B_172,A_173] :
      ( ~ v1_xboole_0(B_172)
      | ~ v1_xboole_0(A_173)
      | k2_relat_1(A_173) = B_172 ) ),
    inference(resolution,[status(thm)],[c_755,c_48])).

tff(c_842,plain,(
    ! [A_174] :
      ( ~ v1_xboole_0(A_174)
      | k2_relat_1(A_174) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_64,c_838])).

tff(c_846,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_64,c_842])).

tff(c_32,plain,(
    ! [A_48,C_63] :
      ( r2_hidden(k4_tarski('#skF_10'(A_48,k2_relat_1(A_48),C_63),C_63),A_48)
      | ~ r2_hidden(C_63,k2_relat_1(A_48)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_208,plain,(
    ! [A_103,C_104] :
      ( r2_hidden(k4_tarski('#skF_10'(A_103,k2_relat_1(A_103),C_104),C_104),A_103)
      | ~ r2_hidden(C_104,k2_relat_1(A_103)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_227,plain,(
    ! [A_105,C_106] :
      ( ~ v1_xboole_0(A_105)
      | ~ r2_hidden(C_106,k2_relat_1(A_105)) ) ),
    inference(resolution,[status(thm)],[c_208,c_48])).

tff(c_251,plain,(
    ! [A_107,C_108] :
      ( ~ v1_xboole_0(A_107)
      | ~ r2_hidden(C_108,k2_relat_1(k2_relat_1(A_107))) ) ),
    inference(resolution,[status(thm)],[c_32,c_227])).

tff(c_271,plain,(
    ! [A_109,C_110] :
      ( ~ v1_xboole_0(A_109)
      | ~ r2_hidden(C_110,k2_relat_1(k2_relat_1(k2_relat_1(A_109)))) ) ),
    inference(resolution,[status(thm)],[c_32,c_251])).

tff(c_284,plain,(
    ! [A_109,C_63] :
      ( ~ v1_xboole_0(A_109)
      | ~ r2_hidden(C_63,k2_relat_1(k2_relat_1(k2_relat_1(k2_relat_1(A_109))))) ) ),
    inference(resolution,[status(thm)],[c_32,c_271])).

tff(c_1039,plain,(
    ! [C_63] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(C_63,k2_relat_1(k2_relat_1(k2_relat_1(k1_xboole_0)))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_846,c_284])).

tff(c_1073,plain,(
    ! [C_63] : ~ r2_hidden(C_63,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_846,c_846,c_846,c_64,c_1039])).

tff(c_50,plain,(
    v1_relat_1('#skF_12') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_847,plain,(
    ! [A_175,B_176,C_177] :
      ( r2_hidden('#skF_2'(A_175,B_176,C_177),B_176)
      | r2_hidden('#skF_3'(A_175,B_176,C_177),C_177)
      | k10_relat_1(A_175,B_176) = C_177
      | ~ v1_relat_1(A_175) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_20,plain,(
    ! [C_47,A_43] :
      ( C_47 = A_43
      | ~ r2_hidden(C_47,k1_tarski(A_43)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_12109,plain,(
    ! [A_439,A_440,C_441] :
      ( '#skF_2'(A_439,k1_tarski(A_440),C_441) = A_440
      | r2_hidden('#skF_3'(A_439,k1_tarski(A_440),C_441),C_441)
      | k10_relat_1(A_439,k1_tarski(A_440)) = C_441
      | ~ v1_relat_1(A_439) ) ),
    inference(resolution,[status(thm)],[c_847,c_20])).

tff(c_40921,plain,(
    ! [A_778,A_779] :
      ( '#skF_2'(A_778,k1_tarski(A_779),k1_xboole_0) = A_779
      | k10_relat_1(A_778,k1_tarski(A_779)) = k1_xboole_0
      | ~ v1_relat_1(A_778) ) ),
    inference(resolution,[status(thm)],[c_12109,c_1073])).

tff(c_41075,plain,
    ( '#skF_2'('#skF_12',k1_tarski('#skF_11'),k1_xboole_0) = '#skF_11'
    | ~ v1_relat_1('#skF_12') ),
    inference(superposition,[status(thm),theory(equality)],[c_40921,c_88])).

tff(c_41112,plain,(
    '#skF_2'('#skF_12',k1_tarski('#skF_11'),k1_xboole_0) = '#skF_11' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_41075])).

tff(c_2009,plain,(
    ! [A_206,B_207,C_208] :
      ( r2_hidden(k4_tarski('#skF_1'(A_206,B_207,C_208),'#skF_2'(A_206,B_207,C_208)),A_206)
      | r2_hidden('#skF_3'(A_206,B_207,C_208),C_208)
      | k10_relat_1(A_206,B_207) = C_208
      | ~ v1_relat_1(A_206) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_34,plain,(
    ! [C_63,A_48,D_66] :
      ( r2_hidden(C_63,k2_relat_1(A_48))
      | ~ r2_hidden(k4_tarski(D_66,C_63),A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_2103,plain,(
    ! [A_206,B_207,C_208] :
      ( r2_hidden('#skF_2'(A_206,B_207,C_208),k2_relat_1(A_206))
      | r2_hidden('#skF_3'(A_206,B_207,C_208),C_208)
      | k10_relat_1(A_206,B_207) = C_208
      | ~ v1_relat_1(A_206) ) ),
    inference(resolution,[status(thm)],[c_2009,c_34])).

tff(c_41168,plain,
    ( r2_hidden('#skF_11',k2_relat_1('#skF_12'))
    | r2_hidden('#skF_3'('#skF_12',k1_tarski('#skF_11'),k1_xboole_0),k1_xboole_0)
    | k10_relat_1('#skF_12',k1_tarski('#skF_11')) = k1_xboole_0
    | ~ v1_relat_1('#skF_12') ),
    inference(superposition,[status(thm),theory(equality)],[c_41112,c_2103])).

tff(c_41187,plain,
    ( r2_hidden('#skF_11',k2_relat_1('#skF_12'))
    | r2_hidden('#skF_3'('#skF_12',k1_tarski('#skF_11'),k1_xboole_0),k1_xboole_0)
    | k10_relat_1('#skF_12',k1_tarski('#skF_11')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_41168])).

tff(c_41189,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_1073,c_87,c_41187])).

tff(c_41191,plain,(
    r2_hidden('#skF_11',k2_relat_1('#skF_12')) ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_41190,plain,(
    k10_relat_1('#skF_12',k1_tarski('#skF_11')) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_22,plain,(
    ! [C_47] : r2_hidden(C_47,k1_tarski(C_47)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_41405,plain,(
    ! [D_820,A_821,B_822,E_823] :
      ( r2_hidden(D_820,k10_relat_1(A_821,B_822))
      | ~ r2_hidden(E_823,B_822)
      | ~ r2_hidden(k4_tarski(D_820,E_823),A_821)
      | ~ v1_relat_1(A_821) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_41528,plain,(
    ! [D_838,A_839,C_840] :
      ( r2_hidden(D_838,k10_relat_1(A_839,k1_tarski(C_840)))
      | ~ r2_hidden(k4_tarski(D_838,C_840),A_839)
      | ~ v1_relat_1(A_839) ) ),
    inference(resolution,[status(thm)],[c_22,c_41405])).

tff(c_41548,plain,(
    ! [D_838] :
      ( r2_hidden(D_838,k1_xboole_0)
      | ~ r2_hidden(k4_tarski(D_838,'#skF_11'),'#skF_12')
      | ~ v1_relat_1('#skF_12') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_41190,c_41528])).

tff(c_41556,plain,(
    ! [D_841] :
      ( r2_hidden(D_841,k1_xboole_0)
      | ~ r2_hidden(k4_tarski(D_841,'#skF_11'),'#skF_12') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_41548])).

tff(c_41560,plain,
    ( r2_hidden('#skF_10'('#skF_12',k2_relat_1('#skF_12'),'#skF_11'),k1_xboole_0)
    | ~ r2_hidden('#skF_11',k2_relat_1('#skF_12')) ),
    inference(resolution,[status(thm)],[c_32,c_41556])).

tff(c_41563,plain,(
    r2_hidden('#skF_10'('#skF_12',k2_relat_1('#skF_12'),'#skF_11'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_41191,c_41560])).

tff(c_41580,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_41563,c_48])).

tff(c_41586,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_41580])).

%------------------------------------------------------------------------------
