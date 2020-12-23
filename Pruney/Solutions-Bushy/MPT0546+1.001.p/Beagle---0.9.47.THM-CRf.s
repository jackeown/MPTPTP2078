%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0546+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:28 EST 2020

% Result     : Theorem 16.32s
% Output     : CNFRefutation 16.37s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 166 expanded)
%              Number of leaves         :   28 (  71 expanded)
%              Depth                    :   15
%              Number of atoms          :  152 ( 526 expanded)
%              Number of equality atoms :   23 (  74 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > k9_relat_1 > k7_relat_1 > k4_tarski > #nlpp > k2_relat_1 > #skF_11 > #skF_1 > #skF_6 > #skF_12 > #skF_4 > #skF_8 > #skF_14 > #skF_13 > #skF_5 > #skF_10 > #skF_2 > #skF_7 > #skF_3 > #skF_9

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_11',type,(
    '#skF_11': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_12',type,(
    '#skF_12': ( $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i * $i * $i ) > $i )).

tff('#skF_14',type,(
    '#skF_14': $i )).

tff('#skF_13',type,(
    '#skF_13': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i ) > $i )).

tff(f_68,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( v1_relat_1(C)
         => ( C = k7_relat_1(A,B)
          <=> ! [D,E] :
                ( r2_hidden(k4_tarski(D,E),C)
              <=> ( r2_hidden(D,B)
                  & r2_hidden(k4_tarski(D,E),A) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_relat_1)).

tff(f_51,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( C = k9_relat_1(A,B)
        <=> ! [D] :
              ( r2_hidden(D,C)
            <=> ? [E] :
                  ( r2_hidden(k4_tarski(E,D),A)
                  & r2_hidden(E,B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_relat_1)).

tff(c_54,plain,(
    v1_relat_1('#skF_14') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_50,plain,(
    ! [A_81,B_82] :
      ( v1_relat_1(k7_relat_1(A_81,B_82))
      | ~ v1_relat_1(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_81,plain,(
    ! [A_106,B_107] :
      ( r2_hidden(k4_tarski('#skF_10'(A_106,B_107),'#skF_9'(A_106,B_107)),A_106)
      | r2_hidden('#skF_11'(A_106,B_107),B_107)
      | k2_relat_1(A_106) = B_107 ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_40,plain,(
    ! [C_77,A_62,D_80] :
      ( r2_hidden(C_77,k2_relat_1(A_62))
      | ~ r2_hidden(k4_tarski(D_80,C_77),A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_93,plain,(
    ! [A_106,B_107] :
      ( r2_hidden('#skF_9'(A_106,B_107),k2_relat_1(A_106))
      | r2_hidden('#skF_11'(A_106,B_107),B_107)
      | k2_relat_1(A_106) = B_107 ) ),
    inference(resolution,[status(thm)],[c_81,c_40])).

tff(c_38,plain,(
    ! [A_62,C_77] :
      ( r2_hidden(k4_tarski('#skF_12'(A_62,k2_relat_1(A_62),C_77),C_77),A_62)
      | ~ r2_hidden(C_77,k2_relat_1(A_62)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_102,plain,(
    ! [D_110,E_111,A_112,B_113] :
      ( r2_hidden(k4_tarski(D_110,E_111),A_112)
      | ~ r2_hidden(k4_tarski(D_110,E_111),k7_relat_1(A_112,B_113))
      | ~ v1_relat_1(k7_relat_1(A_112,B_113))
      | ~ v1_relat_1(A_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_112,plain,(
    ! [A_112,B_113,C_77] :
      ( r2_hidden(k4_tarski('#skF_12'(k7_relat_1(A_112,B_113),k2_relat_1(k7_relat_1(A_112,B_113)),C_77),C_77),A_112)
      | ~ v1_relat_1(k7_relat_1(A_112,B_113))
      | ~ v1_relat_1(A_112)
      | ~ r2_hidden(C_77,k2_relat_1(k7_relat_1(A_112,B_113))) ) ),
    inference(resolution,[status(thm)],[c_38,c_102])).

tff(c_71,plain,(
    ! [D_99,B_100,E_101,A_102] :
      ( r2_hidden(D_99,B_100)
      | ~ r2_hidden(k4_tarski(D_99,E_101),k7_relat_1(A_102,B_100))
      | ~ v1_relat_1(k7_relat_1(A_102,B_100))
      | ~ v1_relat_1(A_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_441,plain,(
    ! [A_174,B_175,C_176] :
      ( r2_hidden('#skF_12'(k7_relat_1(A_174,B_175),k2_relat_1(k7_relat_1(A_174,B_175)),C_176),B_175)
      | ~ v1_relat_1(k7_relat_1(A_174,B_175))
      | ~ v1_relat_1(A_174)
      | ~ r2_hidden(C_176,k2_relat_1(k7_relat_1(A_174,B_175))) ) ),
    inference(resolution,[status(thm)],[c_38,c_71])).

tff(c_20,plain,(
    ! [D_58,A_20,B_43,E_61] :
      ( r2_hidden(D_58,k9_relat_1(A_20,B_43))
      | ~ r2_hidden(E_61,B_43)
      | ~ r2_hidden(k4_tarski(E_61,D_58),A_20)
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_17078,plain,(
    ! [A_856,C_857,A_858,D_855,B_859] :
      ( r2_hidden(D_855,k9_relat_1(A_858,B_859))
      | ~ r2_hidden(k4_tarski('#skF_12'(k7_relat_1(A_856,B_859),k2_relat_1(k7_relat_1(A_856,B_859)),C_857),D_855),A_858)
      | ~ v1_relat_1(A_858)
      | ~ v1_relat_1(k7_relat_1(A_856,B_859))
      | ~ v1_relat_1(A_856)
      | ~ r2_hidden(C_857,k2_relat_1(k7_relat_1(A_856,B_859))) ) ),
    inference(resolution,[status(thm)],[c_441,c_20])).

tff(c_17165,plain,(
    ! [C_860,A_861,B_862] :
      ( r2_hidden(C_860,k9_relat_1(A_861,B_862))
      | ~ v1_relat_1(k7_relat_1(A_861,B_862))
      | ~ v1_relat_1(A_861)
      | ~ r2_hidden(C_860,k2_relat_1(k7_relat_1(A_861,B_862))) ) ),
    inference(resolution,[status(thm)],[c_112,c_17078])).

tff(c_17694,plain,(
    ! [A_861,B_862,B_107] :
      ( r2_hidden('#skF_9'(k7_relat_1(A_861,B_862),B_107),k9_relat_1(A_861,B_862))
      | ~ v1_relat_1(k7_relat_1(A_861,B_862))
      | ~ v1_relat_1(A_861)
      | r2_hidden('#skF_11'(k7_relat_1(A_861,B_862),B_107),B_107)
      | k2_relat_1(k7_relat_1(A_861,B_862)) = B_107 ) ),
    inference(resolution,[status(thm)],[c_93,c_17165])).

tff(c_22,plain,(
    ! [A_20,B_43,D_58] :
      ( r2_hidden('#skF_8'(A_20,B_43,k9_relat_1(A_20,B_43),D_58),B_43)
      | ~ r2_hidden(D_58,k9_relat_1(A_20,B_43))
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_24,plain,(
    ! [A_20,B_43,D_58] :
      ( r2_hidden(k4_tarski('#skF_8'(A_20,B_43,k9_relat_1(A_20,B_43),D_58),D_58),A_20)
      | ~ r2_hidden(D_58,k9_relat_1(A_20,B_43))
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_212,plain,(
    ! [D_131,E_132,A_133,B_134] :
      ( r2_hidden(k4_tarski(D_131,E_132),k7_relat_1(A_133,B_134))
      | ~ r2_hidden(k4_tarski(D_131,E_132),A_133)
      | ~ r2_hidden(D_131,B_134)
      | ~ v1_relat_1(k7_relat_1(A_133,B_134))
      | ~ v1_relat_1(A_133) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_245,plain,(
    ! [E_137,A_138,B_139,D_140] :
      ( r2_hidden(E_137,k2_relat_1(k7_relat_1(A_138,B_139)))
      | ~ r2_hidden(k4_tarski(D_140,E_137),A_138)
      | ~ r2_hidden(D_140,B_139)
      | ~ v1_relat_1(k7_relat_1(A_138,B_139))
      | ~ v1_relat_1(A_138) ) ),
    inference(resolution,[status(thm)],[c_212,c_40])).

tff(c_1391,plain,(
    ! [D_306,A_307,B_308,B_309] :
      ( r2_hidden(D_306,k2_relat_1(k7_relat_1(A_307,B_308)))
      | ~ r2_hidden('#skF_8'(A_307,B_309,k9_relat_1(A_307,B_309),D_306),B_308)
      | ~ v1_relat_1(k7_relat_1(A_307,B_308))
      | ~ r2_hidden(D_306,k9_relat_1(A_307,B_309))
      | ~ v1_relat_1(A_307) ) ),
    inference(resolution,[status(thm)],[c_24,c_245])).

tff(c_1404,plain,(
    ! [D_310,A_311,B_312] :
      ( r2_hidden(D_310,k2_relat_1(k7_relat_1(A_311,B_312)))
      | ~ v1_relat_1(k7_relat_1(A_311,B_312))
      | ~ r2_hidden(D_310,k9_relat_1(A_311,B_312))
      | ~ v1_relat_1(A_311) ) ),
    inference(resolution,[status(thm)],[c_22,c_1391])).

tff(c_180,plain,(
    ! [A_126,B_127,D_128] :
      ( r2_hidden(k4_tarski('#skF_10'(A_126,B_127),'#skF_9'(A_126,B_127)),A_126)
      | ~ r2_hidden(k4_tarski(D_128,'#skF_11'(A_126,B_127)),A_126)
      | k2_relat_1(A_126) = B_127 ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_189,plain,(
    ! [A_129,B_130] :
      ( r2_hidden(k4_tarski('#skF_10'(A_129,B_130),'#skF_9'(A_129,B_130)),A_129)
      | k2_relat_1(A_129) = B_130
      | ~ r2_hidden('#skF_11'(A_129,B_130),k2_relat_1(A_129)) ) ),
    inference(resolution,[status(thm)],[c_38,c_180])).

tff(c_211,plain,(
    ! [A_129,B_130] :
      ( r2_hidden('#skF_9'(A_129,B_130),k2_relat_1(A_129))
      | k2_relat_1(A_129) = B_130
      | ~ r2_hidden('#skF_11'(A_129,B_130),k2_relat_1(A_129)) ) ),
    inference(resolution,[status(thm)],[c_189,c_40])).

tff(c_1532,plain,(
    ! [A_311,B_312,B_130] :
      ( r2_hidden('#skF_9'(k7_relat_1(A_311,B_312),B_130),k2_relat_1(k7_relat_1(A_311,B_312)))
      | k2_relat_1(k7_relat_1(A_311,B_312)) = B_130
      | ~ v1_relat_1(k7_relat_1(A_311,B_312))
      | ~ r2_hidden('#skF_11'(k7_relat_1(A_311,B_312),B_130),k9_relat_1(A_311,B_312))
      | ~ v1_relat_1(A_311) ) ),
    inference(resolution,[status(thm)],[c_1404,c_211])).

tff(c_26536,plain,(
    ! [A_1013,B_1014,B_1015] :
      ( r2_hidden('#skF_9'(k7_relat_1(A_1013,B_1014),B_1015),k9_relat_1(A_1013,B_1014))
      | k2_relat_1(k7_relat_1(A_1013,B_1014)) = B_1015
      | ~ v1_relat_1(k7_relat_1(A_1013,B_1014))
      | ~ r2_hidden('#skF_11'(k7_relat_1(A_1013,B_1014),B_1015),k9_relat_1(A_1013,B_1014))
      | ~ v1_relat_1(A_1013) ) ),
    inference(resolution,[status(thm)],[c_1532,c_17165])).

tff(c_26569,plain,(
    ! [A_861,B_862] :
      ( r2_hidden('#skF_9'(k7_relat_1(A_861,B_862),k9_relat_1(A_861,B_862)),k9_relat_1(A_861,B_862))
      | ~ v1_relat_1(k7_relat_1(A_861,B_862))
      | ~ v1_relat_1(A_861)
      | k2_relat_1(k7_relat_1(A_861,B_862)) = k9_relat_1(A_861,B_862) ) ),
    inference(resolution,[status(thm)],[c_17694,c_26536])).

tff(c_46,plain,(
    ! [A_62,B_63] :
      ( ~ r2_hidden('#skF_9'(A_62,B_63),B_63)
      | r2_hidden('#skF_11'(A_62,B_63),B_63)
      | k2_relat_1(A_62) = B_63 ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1403,plain,(
    ! [D_58,A_20,B_43] :
      ( r2_hidden(D_58,k2_relat_1(k7_relat_1(A_20,B_43)))
      | ~ v1_relat_1(k7_relat_1(A_20,B_43))
      | ~ r2_hidden(D_58,k9_relat_1(A_20,B_43))
      | ~ v1_relat_1(A_20) ) ),
    inference(resolution,[status(thm)],[c_22,c_1391])).

tff(c_26663,plain,(
    ! [A_1021,B_1022] :
      ( r2_hidden('#skF_9'(k7_relat_1(A_1021,B_1022),k9_relat_1(A_1021,B_1022)),k9_relat_1(A_1021,B_1022))
      | ~ v1_relat_1(k7_relat_1(A_1021,B_1022))
      | ~ v1_relat_1(A_1021)
      | k2_relat_1(k7_relat_1(A_1021,B_1022)) = k9_relat_1(A_1021,B_1022) ) ),
    inference(resolution,[status(thm)],[c_17694,c_26536])).

tff(c_42,plain,(
    ! [A_62,B_63,D_76] :
      ( ~ r2_hidden('#skF_9'(A_62,B_63),B_63)
      | ~ r2_hidden(k4_tarski(D_76,'#skF_11'(A_62,B_63)),A_62)
      | k2_relat_1(A_62) = B_63 ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_26842,plain,(
    ! [D_1025,A_1026,B_1027] :
      ( ~ r2_hidden(k4_tarski(D_1025,'#skF_11'(k7_relat_1(A_1026,B_1027),k9_relat_1(A_1026,B_1027))),k7_relat_1(A_1026,B_1027))
      | ~ v1_relat_1(k7_relat_1(A_1026,B_1027))
      | ~ v1_relat_1(A_1026)
      | k2_relat_1(k7_relat_1(A_1026,B_1027)) = k9_relat_1(A_1026,B_1027) ) ),
    inference(resolution,[status(thm)],[c_26663,c_42])).

tff(c_26880,plain,(
    ! [A_1028,B_1029] :
      ( ~ v1_relat_1(k7_relat_1(A_1028,B_1029))
      | ~ v1_relat_1(A_1028)
      | k2_relat_1(k7_relat_1(A_1028,B_1029)) = k9_relat_1(A_1028,B_1029)
      | ~ r2_hidden('#skF_11'(k7_relat_1(A_1028,B_1029),k9_relat_1(A_1028,B_1029)),k2_relat_1(k7_relat_1(A_1028,B_1029))) ) ),
    inference(resolution,[status(thm)],[c_38,c_26842])).

tff(c_26903,plain,(
    ! [A_1030,B_1031] :
      ( k2_relat_1(k7_relat_1(A_1030,B_1031)) = k9_relat_1(A_1030,B_1031)
      | ~ v1_relat_1(k7_relat_1(A_1030,B_1031))
      | ~ r2_hidden('#skF_11'(k7_relat_1(A_1030,B_1031),k9_relat_1(A_1030,B_1031)),k9_relat_1(A_1030,B_1031))
      | ~ v1_relat_1(A_1030) ) ),
    inference(resolution,[status(thm)],[c_1403,c_26880])).

tff(c_26937,plain,(
    ! [A_1032,B_1033] :
      ( ~ v1_relat_1(k7_relat_1(A_1032,B_1033))
      | ~ v1_relat_1(A_1032)
      | ~ r2_hidden('#skF_9'(k7_relat_1(A_1032,B_1033),k9_relat_1(A_1032,B_1033)),k9_relat_1(A_1032,B_1033))
      | k2_relat_1(k7_relat_1(A_1032,B_1033)) = k9_relat_1(A_1032,B_1033) ) ),
    inference(resolution,[status(thm)],[c_46,c_26903])).

tff(c_26955,plain,(
    ! [A_1034,B_1035] :
      ( ~ v1_relat_1(k7_relat_1(A_1034,B_1035))
      | ~ v1_relat_1(A_1034)
      | k2_relat_1(k7_relat_1(A_1034,B_1035)) = k9_relat_1(A_1034,B_1035) ) ),
    inference(resolution,[status(thm)],[c_26569,c_26937])).

tff(c_26966,plain,(
    ! [A_1036,B_1037] :
      ( k2_relat_1(k7_relat_1(A_1036,B_1037)) = k9_relat_1(A_1036,B_1037)
      | ~ v1_relat_1(A_1036) ) ),
    inference(resolution,[status(thm)],[c_50,c_26955])).

tff(c_52,plain,(
    k2_relat_1(k7_relat_1('#skF_14','#skF_13')) != k9_relat_1('#skF_14','#skF_13') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_27354,plain,(
    ~ v1_relat_1('#skF_14') ),
    inference(superposition,[status(thm),theory(equality)],[c_26966,c_52])).

tff(c_27368,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_27354])).

%------------------------------------------------------------------------------
