%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:02 EST 2020

% Result     : Theorem 13.23s
% Output     : CNFRefutation 13.32s
% Verified   : 
% Statistics : Number of formulae       :  165 (5780 expanded)
%              Number of leaves         :   28 (2166 expanded)
%              Depth                    :   31
%              Number of atoms          :  457 (30169 expanded)
%              Number of equality atoms :  135 (11024 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > v1_funct_1 > k5_relat_1 > k4_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_6 > #skF_11 > #skF_3 > #skF_10 > #skF_9 > #skF_2 > #skF_8 > #skF_7 > #skF_1 > #skF_5 > #skF_12 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_100,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ! [C] :
            ( ( v1_relat_1(C)
              & v1_funct_1(C) )
           => ! [D] :
                ( ( v1_relat_1(D)
                  & v1_funct_1(D) )
               => ( ( A = k2_relat_1(B)
                    & k1_relat_1(C) = A
                    & k1_relat_1(D) = A
                    & k5_relat_1(B,C) = k5_relat_1(B,D) )
                 => C = D ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t156_funct_1)).

tff(f_37,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( A = B
          <=> ! [C,D] :
                ( r2_hidden(k4_tarski(C,D),A)
              <=> r2_hidden(k4_tarski(C,D),B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_relat_1)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

tff(f_52,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ! [C] :
          ( ( v1_relat_1(C)
            & v1_funct_1(C) )
         => ( r2_hidden(A,k1_relat_1(B))
           => k1_funct_1(k5_relat_1(B,C),A) = k1_funct_1(C,k1_funct_1(B,A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_funct_1)).

tff(c_40,plain,(
    '#skF_11' != '#skF_12' ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_56,plain,(
    v1_relat_1('#skF_11') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_52,plain,(
    v1_relat_1('#skF_12') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_50,plain,(
    v1_funct_1('#skF_12') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_44,plain,(
    k1_relat_1('#skF_12') = '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_54,plain,(
    v1_funct_1('#skF_11') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_46,plain,(
    k1_relat_1('#skF_11') = '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_809,plain,(
    ! [A_142,B_143] :
      ( r2_hidden(k4_tarski('#skF_1'(A_142,B_143),'#skF_2'(A_142,B_143)),B_143)
      | r2_hidden(k4_tarski('#skF_3'(A_142,B_143),'#skF_4'(A_142,B_143)),A_142)
      | B_143 = A_142
      | ~ v1_relat_1(B_143)
      | ~ v1_relat_1(A_142) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_38,plain,(
    ! [A_62,C_64,B_63] :
      ( r2_hidden(A_62,k1_relat_1(C_64))
      | ~ r2_hidden(k4_tarski(A_62,B_63),C_64)
      | ~ v1_funct_1(C_64)
      | ~ v1_relat_1(C_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_910,plain,(
    ! [A_149,B_150] :
      ( r2_hidden('#skF_3'(A_149,B_150),k1_relat_1(A_149))
      | ~ v1_funct_1(A_149)
      | r2_hidden(k4_tarski('#skF_1'(A_149,B_150),'#skF_2'(A_149,B_150)),B_150)
      | B_150 = A_149
      | ~ v1_relat_1(B_150)
      | ~ v1_relat_1(A_149) ) ),
    inference(resolution,[status(thm)],[c_809,c_38])).

tff(c_942,plain,(
    ! [A_151,B_152] :
      ( r2_hidden('#skF_1'(A_151,B_152),k1_relat_1(B_152))
      | ~ v1_funct_1(B_152)
      | r2_hidden('#skF_3'(A_151,B_152),k1_relat_1(A_151))
      | ~ v1_funct_1(A_151)
      | B_152 = A_151
      | ~ v1_relat_1(B_152)
      | ~ v1_relat_1(A_151) ) ),
    inference(resolution,[status(thm)],[c_910,c_38])).

tff(c_956,plain,(
    ! [B_152] :
      ( r2_hidden('#skF_1'('#skF_11',B_152),k1_relat_1(B_152))
      | ~ v1_funct_1(B_152)
      | r2_hidden('#skF_3'('#skF_11',B_152),'#skF_9')
      | ~ v1_funct_1('#skF_11')
      | B_152 = '#skF_11'
      | ~ v1_relat_1(B_152)
      | ~ v1_relat_1('#skF_11') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_942])).

tff(c_1007,plain,(
    ! [B_156] :
      ( r2_hidden('#skF_1'('#skF_11',B_156),k1_relat_1(B_156))
      | ~ v1_funct_1(B_156)
      | r2_hidden('#skF_3'('#skF_11',B_156),'#skF_9')
      | B_156 = '#skF_11'
      | ~ v1_relat_1(B_156) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_956])).

tff(c_1019,plain,
    ( r2_hidden('#skF_1'('#skF_11','#skF_12'),'#skF_9')
    | ~ v1_funct_1('#skF_12')
    | r2_hidden('#skF_3'('#skF_11','#skF_12'),'#skF_9')
    | '#skF_11' = '#skF_12'
    | ~ v1_relat_1('#skF_12') ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_1007])).

tff(c_1028,plain,
    ( r2_hidden('#skF_1'('#skF_11','#skF_12'),'#skF_9')
    | r2_hidden('#skF_3'('#skF_11','#skF_12'),'#skF_9')
    | '#skF_11' = '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_1019])).

tff(c_1029,plain,
    ( r2_hidden('#skF_1'('#skF_11','#skF_12'),'#skF_9')
    | r2_hidden('#skF_3'('#skF_11','#skF_12'),'#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_1028])).

tff(c_1030,plain,(
    r2_hidden('#skF_3'('#skF_11','#skF_12'),'#skF_9') ),
    inference(splitLeft,[status(thm)],[c_1029])).

tff(c_60,plain,(
    v1_relat_1('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_58,plain,(
    v1_funct_1('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_48,plain,(
    k2_relat_1('#skF_10') = '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_115,plain,(
    ! [A_85,C_86] :
      ( k1_funct_1(A_85,'#skF_8'(A_85,k2_relat_1(A_85),C_86)) = C_86
      | ~ r2_hidden(C_86,k2_relat_1(A_85))
      | ~ v1_funct_1(A_85)
      | ~ v1_relat_1(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_134,plain,(
    ! [C_86] :
      ( k1_funct_1('#skF_10','#skF_8'('#skF_10','#skF_9',C_86)) = C_86
      | ~ r2_hidden(C_86,k2_relat_1('#skF_10'))
      | ~ v1_funct_1('#skF_10')
      | ~ v1_relat_1('#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_115])).

tff(c_140,plain,(
    ! [C_86] :
      ( k1_funct_1('#skF_10','#skF_8'('#skF_10','#skF_9',C_86)) = C_86
      | ~ r2_hidden(C_86,'#skF_9') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_48,c_134])).

tff(c_42,plain,(
    k5_relat_1('#skF_10','#skF_11') = k5_relat_1('#skF_10','#skF_12') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_96,plain,(
    ! [A_80,C_81] :
      ( r2_hidden('#skF_8'(A_80,k2_relat_1(A_80),C_81),k1_relat_1(A_80))
      | ~ r2_hidden(C_81,k2_relat_1(A_80))
      | ~ v1_funct_1(A_80)
      | ~ v1_relat_1(A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_105,plain,(
    ! [C_81] :
      ( r2_hidden('#skF_8'('#skF_10','#skF_9',C_81),k1_relat_1('#skF_10'))
      | ~ r2_hidden(C_81,k2_relat_1('#skF_10'))
      | ~ v1_funct_1('#skF_10')
      | ~ v1_relat_1('#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_96])).

tff(c_111,plain,(
    ! [C_81] :
      ( r2_hidden('#skF_8'('#skF_10','#skF_9',C_81),k1_relat_1('#skF_10'))
      | ~ r2_hidden(C_81,'#skF_9') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_48,c_105])).

tff(c_207,plain,(
    ! [B_97,C_98,A_99] :
      ( k1_funct_1(k5_relat_1(B_97,C_98),A_99) = k1_funct_1(C_98,k1_funct_1(B_97,A_99))
      | ~ r2_hidden(A_99,k1_relat_1(B_97))
      | ~ v1_funct_1(C_98)
      | ~ v1_relat_1(C_98)
      | ~ v1_funct_1(B_97)
      | ~ v1_relat_1(B_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_226,plain,(
    ! [C_98,C_81] :
      ( k1_funct_1(k5_relat_1('#skF_10',C_98),'#skF_8'('#skF_10','#skF_9',C_81)) = k1_funct_1(C_98,k1_funct_1('#skF_10','#skF_8'('#skF_10','#skF_9',C_81)))
      | ~ v1_funct_1(C_98)
      | ~ v1_relat_1(C_98)
      | ~ v1_funct_1('#skF_10')
      | ~ v1_relat_1('#skF_10')
      | ~ r2_hidden(C_81,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_111,c_207])).

tff(c_357,plain,(
    ! [C_118,C_119] :
      ( k1_funct_1(k5_relat_1('#skF_10',C_118),'#skF_8'('#skF_10','#skF_9',C_119)) = k1_funct_1(C_118,k1_funct_1('#skF_10','#skF_8'('#skF_10','#skF_9',C_119)))
      | ~ v1_funct_1(C_118)
      | ~ v1_relat_1(C_118)
      | ~ r2_hidden(C_119,'#skF_9') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_226])).

tff(c_374,plain,(
    ! [C_119] :
      ( k1_funct_1(k5_relat_1('#skF_10','#skF_12'),'#skF_8'('#skF_10','#skF_9',C_119)) = k1_funct_1('#skF_11',k1_funct_1('#skF_10','#skF_8'('#skF_10','#skF_9',C_119)))
      | ~ v1_funct_1('#skF_11')
      | ~ v1_relat_1('#skF_11')
      | ~ r2_hidden(C_119,'#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_357])).

tff(c_379,plain,(
    ! [C_120] :
      ( k1_funct_1(k5_relat_1('#skF_10','#skF_12'),'#skF_8'('#skF_10','#skF_9',C_120)) = k1_funct_1('#skF_11',k1_funct_1('#skF_10','#skF_8'('#skF_10','#skF_9',C_120)))
      | ~ r2_hidden(C_120,'#skF_9') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_374])).

tff(c_244,plain,(
    ! [C_98,C_81] :
      ( k1_funct_1(k5_relat_1('#skF_10',C_98),'#skF_8'('#skF_10','#skF_9',C_81)) = k1_funct_1(C_98,k1_funct_1('#skF_10','#skF_8'('#skF_10','#skF_9',C_81)))
      | ~ v1_funct_1(C_98)
      | ~ v1_relat_1(C_98)
      | ~ r2_hidden(C_81,'#skF_9') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_226])).

tff(c_385,plain,(
    ! [C_120] :
      ( k1_funct_1('#skF_11',k1_funct_1('#skF_10','#skF_8'('#skF_10','#skF_9',C_120))) = k1_funct_1('#skF_12',k1_funct_1('#skF_10','#skF_8'('#skF_10','#skF_9',C_120)))
      | ~ v1_funct_1('#skF_12')
      | ~ v1_relat_1('#skF_12')
      | ~ r2_hidden(C_120,'#skF_9')
      | ~ r2_hidden(C_120,'#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_379,c_244])).

tff(c_407,plain,(
    ! [C_121] :
      ( k1_funct_1('#skF_11',k1_funct_1('#skF_10','#skF_8'('#skF_10','#skF_9',C_121))) = k1_funct_1('#skF_12',k1_funct_1('#skF_10','#skF_8'('#skF_10','#skF_9',C_121)))
      | ~ r2_hidden(C_121,'#skF_9') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_385])).

tff(c_433,plain,(
    ! [C_122] :
      ( k1_funct_1('#skF_12',k1_funct_1('#skF_10','#skF_8'('#skF_10','#skF_9',C_122))) = k1_funct_1('#skF_11',C_122)
      | ~ r2_hidden(C_122,'#skF_9')
      | ~ r2_hidden(C_122,'#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_140,c_407])).

tff(c_450,plain,(
    ! [C_86] :
      ( k1_funct_1('#skF_11',C_86) = k1_funct_1('#skF_12',C_86)
      | ~ r2_hidden(C_86,'#skF_9')
      | ~ r2_hidden(C_86,'#skF_9')
      | ~ r2_hidden(C_86,'#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_140,c_433])).

tff(c_1032,plain,
    ( k1_funct_1('#skF_11','#skF_3'('#skF_11','#skF_12')) = k1_funct_1('#skF_12','#skF_3'('#skF_11','#skF_12'))
    | ~ r2_hidden('#skF_3'('#skF_11','#skF_12'),'#skF_9') ),
    inference(resolution,[status(thm)],[c_1030,c_450])).

tff(c_1035,plain,(
    k1_funct_1('#skF_11','#skF_3'('#skF_11','#skF_12')) = k1_funct_1('#skF_12','#skF_3'('#skF_11','#skF_12')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1030,c_1032])).

tff(c_36,plain,(
    ! [C_64,A_62,B_63] :
      ( k1_funct_1(C_64,A_62) = B_63
      | ~ r2_hidden(k4_tarski(A_62,B_63),C_64)
      | ~ v1_funct_1(C_64)
      | ~ v1_relat_1(C_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_1199,plain,(
    ! [A_164,B_165] :
      ( k1_funct_1(A_164,'#skF_3'(A_164,B_165)) = '#skF_4'(A_164,B_165)
      | ~ v1_funct_1(A_164)
      | r2_hidden(k4_tarski('#skF_1'(A_164,B_165),'#skF_2'(A_164,B_165)),B_165)
      | B_165 = A_164
      | ~ v1_relat_1(B_165)
      | ~ v1_relat_1(A_164) ) ),
    inference(resolution,[status(thm)],[c_809,c_36])).

tff(c_17993,plain,(
    ! [B_618,A_619] :
      ( k1_funct_1(B_618,'#skF_1'(A_619,B_618)) = '#skF_2'(A_619,B_618)
      | ~ v1_funct_1(B_618)
      | k1_funct_1(A_619,'#skF_3'(A_619,B_618)) = '#skF_4'(A_619,B_618)
      | ~ v1_funct_1(A_619)
      | B_618 = A_619
      | ~ v1_relat_1(B_618)
      | ~ v1_relat_1(A_619) ) ),
    inference(resolution,[status(thm)],[c_1199,c_36])).

tff(c_18205,plain,
    ( k1_funct_1('#skF_12','#skF_1'('#skF_11','#skF_12')) = '#skF_2'('#skF_11','#skF_12')
    | ~ v1_funct_1('#skF_12')
    | k1_funct_1('#skF_12','#skF_3'('#skF_11','#skF_12')) = '#skF_4'('#skF_11','#skF_12')
    | ~ v1_funct_1('#skF_11')
    | '#skF_11' = '#skF_12'
    | ~ v1_relat_1('#skF_12')
    | ~ v1_relat_1('#skF_11') ),
    inference(superposition,[status(thm),theory(equality)],[c_1035,c_17993])).

tff(c_18294,plain,
    ( k1_funct_1('#skF_12','#skF_1'('#skF_11','#skF_12')) = '#skF_2'('#skF_11','#skF_12')
    | k1_funct_1('#skF_12','#skF_3'('#skF_11','#skF_12')) = '#skF_4'('#skF_11','#skF_12')
    | '#skF_11' = '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_54,c_50,c_18205])).

tff(c_18295,plain,
    ( k1_funct_1('#skF_12','#skF_1'('#skF_11','#skF_12')) = '#skF_2'('#skF_11','#skF_12')
    | k1_funct_1('#skF_12','#skF_3'('#skF_11','#skF_12')) = '#skF_4'('#skF_11','#skF_12') ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_18294])).

tff(c_18298,plain,(
    k1_funct_1('#skF_12','#skF_3'('#skF_11','#skF_12')) = '#skF_4'('#skF_11','#skF_12') ),
    inference(splitLeft,[status(thm)],[c_18295])).

tff(c_34,plain,(
    ! [A_62,C_64] :
      ( r2_hidden(k4_tarski(A_62,k1_funct_1(C_64,A_62)),C_64)
      | ~ r2_hidden(A_62,k1_relat_1(C_64))
      | ~ v1_funct_1(C_64)
      | ~ v1_relat_1(C_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_18358,plain,
    ( r2_hidden(k4_tarski('#skF_3'('#skF_11','#skF_12'),'#skF_4'('#skF_11','#skF_12')),'#skF_12')
    | ~ r2_hidden('#skF_3'('#skF_11','#skF_12'),k1_relat_1('#skF_12'))
    | ~ v1_funct_1('#skF_12')
    | ~ v1_relat_1('#skF_12') ),
    inference(superposition,[status(thm),theory(equality)],[c_18298,c_34])).

tff(c_18373,plain,(
    r2_hidden(k4_tarski('#skF_3'('#skF_11','#skF_12'),'#skF_4'('#skF_11','#skF_12')),'#skF_12') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_1030,c_44,c_18358])).

tff(c_4,plain,(
    ! [A_1,B_11] :
      ( r2_hidden(k4_tarski('#skF_1'(A_1,B_11),'#skF_2'(A_1,B_11)),B_11)
      | ~ r2_hidden(k4_tarski('#skF_3'(A_1,B_11),'#skF_4'(A_1,B_11)),B_11)
      | B_11 = A_1
      | ~ v1_relat_1(B_11)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_18507,plain,
    ( r2_hidden(k4_tarski('#skF_1'('#skF_11','#skF_12'),'#skF_2'('#skF_11','#skF_12')),'#skF_12')
    | '#skF_11' = '#skF_12'
    | ~ v1_relat_1('#skF_12')
    | ~ v1_relat_1('#skF_11') ),
    inference(resolution,[status(thm)],[c_18373,c_4])).

tff(c_18516,plain,
    ( r2_hidden(k4_tarski('#skF_1'('#skF_11','#skF_12'),'#skF_2'('#skF_11','#skF_12')),'#skF_12')
    | '#skF_11' = '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_18507])).

tff(c_18517,plain,(
    r2_hidden(k4_tarski('#skF_1'('#skF_11','#skF_12'),'#skF_2'('#skF_11','#skF_12')),'#skF_12') ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_18516])).

tff(c_18530,plain,
    ( r2_hidden('#skF_1'('#skF_11','#skF_12'),k1_relat_1('#skF_12'))
    | ~ v1_funct_1('#skF_12')
    | ~ v1_relat_1('#skF_12') ),
    inference(resolution,[status(thm)],[c_18517,c_38])).

tff(c_18536,plain,(
    r2_hidden('#skF_1'('#skF_11','#skF_12'),'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_44,c_18530])).

tff(c_18141,plain,
    ( k1_funct_1('#skF_12','#skF_3'('#skF_11','#skF_12')) = '#skF_4'('#skF_11','#skF_12')
    | k1_funct_1('#skF_12','#skF_1'('#skF_11','#skF_12')) = '#skF_2'('#skF_11','#skF_12')
    | ~ v1_funct_1('#skF_12')
    | ~ v1_funct_1('#skF_11')
    | '#skF_11' = '#skF_12'
    | ~ v1_relat_1('#skF_12')
    | ~ v1_relat_1('#skF_11') ),
    inference(superposition,[status(thm),theory(equality)],[c_17993,c_1035])).

tff(c_18272,plain,
    ( k1_funct_1('#skF_12','#skF_3'('#skF_11','#skF_12')) = '#skF_4'('#skF_11','#skF_12')
    | k1_funct_1('#skF_12','#skF_1'('#skF_11','#skF_12')) = '#skF_2'('#skF_11','#skF_12')
    | '#skF_11' = '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_54,c_50,c_18141])).

tff(c_18273,plain,
    ( k1_funct_1('#skF_12','#skF_3'('#skF_11','#skF_12')) = '#skF_4'('#skF_11','#skF_12')
    | k1_funct_1('#skF_12','#skF_1'('#skF_11','#skF_12')) = '#skF_2'('#skF_11','#skF_12') ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_18272])).

tff(c_18297,plain,(
    k1_funct_1('#skF_12','#skF_1'('#skF_11','#skF_12')) = '#skF_2'('#skF_11','#skF_12') ),
    inference(splitLeft,[status(thm)],[c_18273])).

tff(c_18538,plain,
    ( k1_funct_1('#skF_11','#skF_1'('#skF_11','#skF_12')) = k1_funct_1('#skF_12','#skF_1'('#skF_11','#skF_12'))
    | ~ r2_hidden('#skF_1'('#skF_11','#skF_12'),'#skF_9') ),
    inference(resolution,[status(thm)],[c_18536,c_450])).

tff(c_18541,plain,(
    k1_funct_1('#skF_11','#skF_1'('#skF_11','#skF_12')) = '#skF_2'('#skF_11','#skF_12') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18536,c_18297,c_18538])).

tff(c_18555,plain,
    ( r2_hidden(k4_tarski('#skF_1'('#skF_11','#skF_12'),'#skF_2'('#skF_11','#skF_12')),'#skF_11')
    | ~ r2_hidden('#skF_1'('#skF_11','#skF_12'),k1_relat_1('#skF_11'))
    | ~ v1_funct_1('#skF_11')
    | ~ v1_relat_1('#skF_11') ),
    inference(superposition,[status(thm),theory(equality)],[c_18541,c_34])).

tff(c_18570,plain,(
    r2_hidden(k4_tarski('#skF_1'('#skF_11','#skF_12'),'#skF_2'('#skF_11','#skF_12')),'#skF_11') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_18536,c_46,c_18555])).

tff(c_2,plain,(
    ! [A_1,B_11] :
      ( ~ r2_hidden(k4_tarski('#skF_1'(A_1,B_11),'#skF_2'(A_1,B_11)),A_1)
      | ~ r2_hidden(k4_tarski('#skF_3'(A_1,B_11),'#skF_4'(A_1,B_11)),B_11)
      | B_11 = A_1
      | ~ v1_relat_1(B_11)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_18584,plain,
    ( ~ r2_hidden(k4_tarski('#skF_3'('#skF_11','#skF_12'),'#skF_4'('#skF_11','#skF_12')),'#skF_12')
    | '#skF_11' = '#skF_12'
    | ~ v1_relat_1('#skF_12')
    | ~ v1_relat_1('#skF_11') ),
    inference(resolution,[status(thm)],[c_18570,c_2])).

tff(c_18600,plain,(
    '#skF_11' = '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_18373,c_18584])).

tff(c_18602,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_18600])).

tff(c_18604,plain,(
    k1_funct_1('#skF_12','#skF_3'('#skF_11','#skF_12')) != '#skF_4'('#skF_11','#skF_12') ),
    inference(splitRight,[status(thm)],[c_18295])).

tff(c_17559,plain,(
    ! [A_614,B_615] :
      ( r2_hidden('#skF_1'(A_614,B_615),k1_relat_1(B_615))
      | ~ v1_funct_1(B_615)
      | k1_funct_1(A_614,'#skF_3'(A_614,B_615)) = '#skF_4'(A_614,B_615)
      | ~ v1_funct_1(A_614)
      | B_615 = A_614
      | ~ v1_relat_1(B_615)
      | ~ v1_relat_1(A_614) ) ),
    inference(resolution,[status(thm)],[c_1199,c_38])).

tff(c_17649,plain,(
    ! [A_614] :
      ( r2_hidden('#skF_1'(A_614,'#skF_12'),'#skF_9')
      | ~ v1_funct_1('#skF_12')
      | k1_funct_1(A_614,'#skF_3'(A_614,'#skF_12')) = '#skF_4'(A_614,'#skF_12')
      | ~ v1_funct_1(A_614)
      | A_614 = '#skF_12'
      | ~ v1_relat_1('#skF_12')
      | ~ v1_relat_1(A_614) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_17559])).

tff(c_17658,plain,(
    ! [A_614] :
      ( r2_hidden('#skF_1'(A_614,'#skF_12'),'#skF_9')
      | k1_funct_1(A_614,'#skF_3'(A_614,'#skF_12')) = '#skF_4'(A_614,'#skF_12')
      | ~ v1_funct_1(A_614)
      | A_614 = '#skF_12'
      | ~ v1_relat_1(A_614) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_17649])).

tff(c_30,plain,(
    ! [A_18,B_40] :
      ( r2_hidden('#skF_6'(A_18,B_40),k1_relat_1(A_18))
      | r2_hidden('#skF_7'(A_18,B_40),B_40)
      | k2_relat_1(A_18) = B_40
      | ~ v1_funct_1(A_18)
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_176,plain,(
    ! [A_93,B_94] :
      ( k1_funct_1(A_93,'#skF_6'(A_93,B_94)) = '#skF_5'(A_93,B_94)
      | r2_hidden('#skF_7'(A_93,B_94),B_94)
      | k2_relat_1(A_93) = B_94
      | ~ v1_funct_1(A_93)
      | ~ v1_relat_1(A_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_14,plain,(
    ! [A_18,D_57] :
      ( r2_hidden(k1_funct_1(A_18,D_57),k2_relat_1(A_18))
      | ~ r2_hidden(D_57,k1_relat_1(A_18))
      | ~ v1_funct_1(A_18)
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_13477,plain,(
    ! [A_483,B_484] :
      ( r2_hidden('#skF_5'(A_483,B_484),k2_relat_1(A_483))
      | ~ r2_hidden('#skF_6'(A_483,B_484),k1_relat_1(A_483))
      | ~ v1_funct_1(A_483)
      | ~ v1_relat_1(A_483)
      | r2_hidden('#skF_7'(A_483,B_484),B_484)
      | k2_relat_1(A_483) = B_484
      | ~ v1_funct_1(A_483)
      | ~ v1_relat_1(A_483) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_176,c_14])).

tff(c_13612,plain,(
    ! [A_490,B_491] :
      ( r2_hidden('#skF_5'(A_490,B_491),k2_relat_1(A_490))
      | r2_hidden('#skF_7'(A_490,B_491),B_491)
      | k2_relat_1(A_490) = B_491
      | ~ v1_funct_1(A_490)
      | ~ v1_relat_1(A_490) ) ),
    inference(resolution,[status(thm)],[c_30,c_13477])).

tff(c_13628,plain,(
    ! [B_491] :
      ( r2_hidden('#skF_5'('#skF_10',B_491),'#skF_9')
      | r2_hidden('#skF_7'('#skF_10',B_491),B_491)
      | k2_relat_1('#skF_10') = B_491
      | ~ v1_funct_1('#skF_10')
      | ~ v1_relat_1('#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_13612])).

tff(c_13635,plain,(
    ! [B_492] :
      ( r2_hidden('#skF_5'('#skF_10',B_492),'#skF_9')
      | r2_hidden('#skF_7'('#skF_10',B_492),B_492)
      | B_492 = '#skF_9' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_48,c_13628])).

tff(c_79,plain,(
    ! [A_75,D_76] :
      ( r2_hidden(k1_funct_1(A_75,D_76),k2_relat_1(A_75))
      | ~ r2_hidden(D_76,k1_relat_1(A_75))
      | ~ v1_funct_1(A_75)
      | ~ v1_relat_1(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_82,plain,(
    ! [D_76] :
      ( r2_hidden(k1_funct_1('#skF_10',D_76),'#skF_9')
      | ~ r2_hidden(D_76,k1_relat_1('#skF_10'))
      | ~ v1_funct_1('#skF_10')
      | ~ v1_relat_1('#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_79])).

tff(c_84,plain,(
    ! [D_76] :
      ( r2_hidden(k1_funct_1('#skF_10',D_76),'#skF_9')
      | ~ r2_hidden(D_76,k1_relat_1('#skF_10')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_82])).

tff(c_459,plain,(
    ! [C_123] :
      ( k1_funct_1('#skF_11',C_123) = k1_funct_1('#skF_12',C_123)
      | ~ r2_hidden(C_123,'#skF_9')
      | ~ r2_hidden(C_123,'#skF_9')
      | ~ r2_hidden(C_123,'#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_140,c_433])).

tff(c_642,plain,(
    ! [D_136] :
      ( k1_funct_1('#skF_11',k1_funct_1('#skF_10',D_136)) = k1_funct_1('#skF_12',k1_funct_1('#skF_10',D_136))
      | ~ r2_hidden(k1_funct_1('#skF_10',D_136),'#skF_9')
      | ~ r2_hidden(D_136,k1_relat_1('#skF_10')) ) ),
    inference(resolution,[status(thm)],[c_84,c_459])).

tff(c_657,plain,(
    ! [D_76] :
      ( k1_funct_1('#skF_11',k1_funct_1('#skF_10',D_76)) = k1_funct_1('#skF_12',k1_funct_1('#skF_10',D_76))
      | ~ r2_hidden(D_76,k1_relat_1('#skF_10')) ) ),
    inference(resolution,[status(thm)],[c_84,c_642])).

tff(c_13646,plain,
    ( k1_funct_1('#skF_11',k1_funct_1('#skF_10','#skF_7'('#skF_10',k1_relat_1('#skF_10')))) = k1_funct_1('#skF_12',k1_funct_1('#skF_10','#skF_7'('#skF_10',k1_relat_1('#skF_10'))))
    | r2_hidden('#skF_5'('#skF_10',k1_relat_1('#skF_10')),'#skF_9')
    | k1_relat_1('#skF_10') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_13635,c_657])).

tff(c_14013,plain,(
    k1_relat_1('#skF_10') = '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_13646])).

tff(c_164,plain,(
    ! [A_90,B_91] :
      ( r2_hidden('#skF_6'(A_90,B_91),k1_relat_1(A_90))
      | r2_hidden('#skF_7'(A_90,B_91),B_91)
      | k2_relat_1(A_90) = B_91
      | ~ v1_funct_1(A_90)
      | ~ v1_relat_1(A_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_170,plain,(
    ! [B_91] :
      ( r2_hidden('#skF_6'('#skF_12',B_91),'#skF_9')
      | r2_hidden('#skF_7'('#skF_12',B_91),B_91)
      | k2_relat_1('#skF_12') = B_91
      | ~ v1_funct_1('#skF_12')
      | ~ v1_relat_1('#skF_12') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_164])).

tff(c_174,plain,(
    ! [B_91] :
      ( r2_hidden('#skF_6'('#skF_12',B_91),'#skF_9')
      | r2_hidden('#skF_7'('#skF_12',B_91),B_91)
      | k2_relat_1('#skF_12') = B_91 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_170])).

tff(c_658,plain,(
    ! [D_137] :
      ( k1_funct_1('#skF_11',k1_funct_1('#skF_10',D_137)) = k1_funct_1('#skF_12',k1_funct_1('#skF_10',D_137))
      | ~ r2_hidden(D_137,k1_relat_1('#skF_10')) ) ),
    inference(resolution,[status(thm)],[c_84,c_642])).

tff(c_702,plain,
    ( k1_funct_1('#skF_11',k1_funct_1('#skF_10','#skF_7'('#skF_12',k1_relat_1('#skF_10')))) = k1_funct_1('#skF_12',k1_funct_1('#skF_10','#skF_7'('#skF_12',k1_relat_1('#skF_10'))))
    | r2_hidden('#skF_6'('#skF_12',k1_relat_1('#skF_10')),'#skF_9')
    | k2_relat_1('#skF_12') = k1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_174,c_658])).

tff(c_14120,plain,
    ( k1_funct_1('#skF_11',k1_funct_1('#skF_10','#skF_7'('#skF_12','#skF_9'))) = k1_funct_1('#skF_12',k1_funct_1('#skF_10','#skF_7'('#skF_12','#skF_9')))
    | r2_hidden('#skF_6'('#skF_12','#skF_9'),'#skF_9')
    | k2_relat_1('#skF_12') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14013,c_14013,c_14013,c_14013,c_702])).

tff(c_14121,plain,(
    k2_relat_1('#skF_12') = '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_14120])).

tff(c_18624,plain,
    ( r2_hidden('#skF_2'('#skF_11','#skF_12'),k2_relat_1('#skF_12'))
    | ~ r2_hidden('#skF_1'('#skF_11','#skF_12'),k1_relat_1('#skF_12'))
    | ~ v1_funct_1('#skF_12')
    | ~ v1_relat_1('#skF_12') ),
    inference(superposition,[status(thm),theory(equality)],[c_18297,c_14])).

tff(c_18638,plain,
    ( r2_hidden('#skF_2'('#skF_11','#skF_12'),'#skF_9')
    | ~ r2_hidden('#skF_1'('#skF_11','#skF_12'),'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_44,c_14121,c_18624])).

tff(c_18641,plain,(
    ~ r2_hidden('#skF_1'('#skF_11','#skF_12'),'#skF_9') ),
    inference(splitLeft,[status(thm)],[c_18638])).

tff(c_18644,plain,
    ( k1_funct_1('#skF_11','#skF_3'('#skF_11','#skF_12')) = '#skF_4'('#skF_11','#skF_12')
    | ~ v1_funct_1('#skF_11')
    | '#skF_11' = '#skF_12'
    | ~ v1_relat_1('#skF_11') ),
    inference(resolution,[status(thm)],[c_17658,c_18641])).

tff(c_18647,plain,
    ( k1_funct_1('#skF_12','#skF_3'('#skF_11','#skF_12')) = '#skF_4'('#skF_11','#skF_12')
    | '#skF_11' = '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_1035,c_18644])).

tff(c_18649,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_18604,c_18647])).

tff(c_18651,plain,(
    r2_hidden('#skF_1'('#skF_11','#skF_12'),'#skF_9') ),
    inference(splitRight,[status(thm)],[c_18638])).

tff(c_18653,plain,
    ( k1_funct_1('#skF_11','#skF_1'('#skF_11','#skF_12')) = k1_funct_1('#skF_12','#skF_1'('#skF_11','#skF_12'))
    | ~ r2_hidden('#skF_1'('#skF_11','#skF_12'),'#skF_9') ),
    inference(resolution,[status(thm)],[c_18651,c_450])).

tff(c_18656,plain,(
    k1_funct_1('#skF_11','#skF_1'('#skF_11','#skF_12')) = '#skF_2'('#skF_11','#skF_12') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18651,c_18297,c_18653])).

tff(c_18675,plain,
    ( r2_hidden(k4_tarski('#skF_1'('#skF_11','#skF_12'),'#skF_2'('#skF_11','#skF_12')),'#skF_11')
    | ~ r2_hidden('#skF_1'('#skF_11','#skF_12'),k1_relat_1('#skF_11'))
    | ~ v1_funct_1('#skF_11')
    | ~ v1_relat_1('#skF_11') ),
    inference(superposition,[status(thm),theory(equality)],[c_18656,c_34])).

tff(c_18690,plain,(
    r2_hidden(k4_tarski('#skF_1'('#skF_11','#skF_12'),'#skF_2'('#skF_11','#skF_12')),'#skF_11') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_18651,c_46,c_18675])).

tff(c_337,plain,(
    ! [A_113,B_114] :
      ( ~ r2_hidden(k4_tarski('#skF_1'(A_113,B_114),'#skF_2'(A_113,B_114)),A_113)
      | r2_hidden(k4_tarski('#skF_3'(A_113,B_114),'#skF_4'(A_113,B_114)),A_113)
      | B_114 = A_113
      | ~ v1_relat_1(B_114)
      | ~ v1_relat_1(A_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_348,plain,(
    ! [A_113,B_114] :
      ( k1_funct_1(A_113,'#skF_3'(A_113,B_114)) = '#skF_4'(A_113,B_114)
      | ~ v1_funct_1(A_113)
      | ~ r2_hidden(k4_tarski('#skF_1'(A_113,B_114),'#skF_2'(A_113,B_114)),A_113)
      | B_114 = A_113
      | ~ v1_relat_1(B_114)
      | ~ v1_relat_1(A_113) ) ),
    inference(resolution,[status(thm)],[c_337,c_36])).

tff(c_18696,plain,
    ( k1_funct_1('#skF_11','#skF_3'('#skF_11','#skF_12')) = '#skF_4'('#skF_11','#skF_12')
    | ~ v1_funct_1('#skF_11')
    | '#skF_11' = '#skF_12'
    | ~ v1_relat_1('#skF_12')
    | ~ v1_relat_1('#skF_11') ),
    inference(resolution,[status(thm)],[c_18690,c_348])).

tff(c_18710,plain,
    ( k1_funct_1('#skF_12','#skF_3'('#skF_11','#skF_12')) = '#skF_4'('#skF_11','#skF_12')
    | '#skF_11' = '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_54,c_1035,c_18696])).

tff(c_18712,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_18604,c_18710])).

tff(c_18714,plain,(
    k1_funct_1('#skF_12','#skF_1'('#skF_11','#skF_12')) != '#skF_2'('#skF_11','#skF_12') ),
    inference(splitRight,[status(thm)],[c_18273])).

tff(c_18713,plain,(
    k1_funct_1('#skF_12','#skF_3'('#skF_11','#skF_12')) = '#skF_4'('#skF_11','#skF_12') ),
    inference(splitRight,[status(thm)],[c_18273])).

tff(c_18740,plain,
    ( r2_hidden(k4_tarski('#skF_3'('#skF_11','#skF_12'),'#skF_4'('#skF_11','#skF_12')),'#skF_12')
    | ~ r2_hidden('#skF_3'('#skF_11','#skF_12'),k1_relat_1('#skF_12'))
    | ~ v1_funct_1('#skF_12')
    | ~ v1_relat_1('#skF_12') ),
    inference(superposition,[status(thm),theory(equality)],[c_18713,c_34])).

tff(c_18755,plain,(
    r2_hidden(k4_tarski('#skF_3'('#skF_11','#skF_12'),'#skF_4'('#skF_11','#skF_12')),'#skF_12') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_1030,c_44,c_18740])).

tff(c_18893,plain,
    ( r2_hidden(k4_tarski('#skF_1'('#skF_11','#skF_12'),'#skF_2'('#skF_11','#skF_12')),'#skF_12')
    | '#skF_11' = '#skF_12'
    | ~ v1_relat_1('#skF_12')
    | ~ v1_relat_1('#skF_11') ),
    inference(resolution,[status(thm)],[c_18755,c_4])).

tff(c_18902,plain,
    ( r2_hidden(k4_tarski('#skF_1'('#skF_11','#skF_12'),'#skF_2'('#skF_11','#skF_12')),'#skF_12')
    | '#skF_11' = '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_18893])).

tff(c_18903,plain,(
    r2_hidden(k4_tarski('#skF_1'('#skF_11','#skF_12'),'#skF_2'('#skF_11','#skF_12')),'#skF_12') ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_18902])).

tff(c_18913,plain,
    ( k1_funct_1('#skF_12','#skF_1'('#skF_11','#skF_12')) = '#skF_2'('#skF_11','#skF_12')
    | ~ v1_funct_1('#skF_12')
    | ~ v1_relat_1('#skF_12') ),
    inference(resolution,[status(thm)],[c_18903,c_36])).

tff(c_18919,plain,(
    k1_funct_1('#skF_12','#skF_1'('#skF_11','#skF_12')) = '#skF_2'('#skF_11','#skF_12') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_18913])).

tff(c_18921,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18714,c_18919])).

tff(c_18923,plain,(
    ~ r2_hidden('#skF_3'('#skF_11','#skF_12'),'#skF_9') ),
    inference(splitRight,[status(thm)],[c_1029])).

tff(c_19198,plain,(
    ! [B_635,A_636] :
      ( k1_funct_1(B_635,'#skF_1'(A_636,B_635)) = '#skF_2'(A_636,B_635)
      | ~ v1_funct_1(B_635)
      | r2_hidden(k4_tarski('#skF_3'(A_636,B_635),'#skF_4'(A_636,B_635)),A_636)
      | B_635 = A_636
      | ~ v1_relat_1(B_635)
      | ~ v1_relat_1(A_636) ) ),
    inference(resolution,[status(thm)],[c_809,c_36])).

tff(c_26111,plain,(
    ! [A_885,B_886] :
      ( r2_hidden('#skF_3'(A_885,B_886),k1_relat_1(A_885))
      | ~ v1_funct_1(A_885)
      | k1_funct_1(B_886,'#skF_1'(A_885,B_886)) = '#skF_2'(A_885,B_886)
      | ~ v1_funct_1(B_886)
      | B_886 = A_885
      | ~ v1_relat_1(B_886)
      | ~ v1_relat_1(A_885) ) ),
    inference(resolution,[status(thm)],[c_19198,c_38])).

tff(c_26185,plain,(
    ! [B_886] :
      ( r2_hidden('#skF_3'('#skF_11',B_886),'#skF_9')
      | ~ v1_funct_1('#skF_11')
      | k1_funct_1(B_886,'#skF_1'('#skF_11',B_886)) = '#skF_2'('#skF_11',B_886)
      | ~ v1_funct_1(B_886)
      | B_886 = '#skF_11'
      | ~ v1_relat_1(B_886)
      | ~ v1_relat_1('#skF_11') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_26111])).

tff(c_26387,plain,(
    ! [B_890] :
      ( r2_hidden('#skF_3'('#skF_11',B_890),'#skF_9')
      | k1_funct_1(B_890,'#skF_1'('#skF_11',B_890)) = '#skF_2'('#skF_11',B_890)
      | ~ v1_funct_1(B_890)
      | B_890 = '#skF_11'
      | ~ v1_relat_1(B_890) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_26185])).

tff(c_26390,plain,
    ( k1_funct_1('#skF_12','#skF_1'('#skF_11','#skF_12')) = '#skF_2'('#skF_11','#skF_12')
    | ~ v1_funct_1('#skF_12')
    | '#skF_11' = '#skF_12'
    | ~ v1_relat_1('#skF_12') ),
    inference(resolution,[status(thm)],[c_26387,c_18923])).

tff(c_26473,plain,
    ( k1_funct_1('#skF_12','#skF_1'('#skF_11','#skF_12')) = '#skF_2'('#skF_11','#skF_12')
    | '#skF_11' = '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_26390])).

tff(c_26474,plain,(
    k1_funct_1('#skF_12','#skF_1'('#skF_11','#skF_12')) = '#skF_2'('#skF_11','#skF_12') ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_26473])).

tff(c_18922,plain,(
    r2_hidden('#skF_1'('#skF_11','#skF_12'),'#skF_9') ),
    inference(splitRight,[status(thm)],[c_1029])).

tff(c_18925,plain,
    ( k1_funct_1('#skF_11','#skF_1'('#skF_11','#skF_12')) = k1_funct_1('#skF_12','#skF_1'('#skF_11','#skF_12'))
    | ~ r2_hidden('#skF_1'('#skF_11','#skF_12'),'#skF_9') ),
    inference(resolution,[status(thm)],[c_18922,c_450])).

tff(c_18928,plain,(
    k1_funct_1('#skF_11','#skF_1'('#skF_11','#skF_12')) = k1_funct_1('#skF_12','#skF_1'('#skF_11','#skF_12')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18922,c_18925])).

tff(c_18967,plain,
    ( r2_hidden(k4_tarski('#skF_1'('#skF_11','#skF_12'),k1_funct_1('#skF_12','#skF_1'('#skF_11','#skF_12'))),'#skF_11')
    | ~ r2_hidden('#skF_1'('#skF_11','#skF_12'),k1_relat_1('#skF_11'))
    | ~ v1_funct_1('#skF_11')
    | ~ v1_relat_1('#skF_11') ),
    inference(superposition,[status(thm),theory(equality)],[c_18928,c_34])).

tff(c_18980,plain,(
    r2_hidden(k4_tarski('#skF_1'('#skF_11','#skF_12'),k1_funct_1('#skF_12','#skF_1'('#skF_11','#skF_12'))),'#skF_11') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_18922,c_46,c_18967])).

tff(c_26491,plain,(
    r2_hidden(k4_tarski('#skF_1'('#skF_11','#skF_12'),'#skF_2'('#skF_11','#skF_12')),'#skF_11') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26474,c_18980])).

tff(c_349,plain,(
    ! [A_113,B_114] :
      ( r2_hidden('#skF_3'(A_113,B_114),k1_relat_1(A_113))
      | ~ v1_funct_1(A_113)
      | ~ r2_hidden(k4_tarski('#skF_1'(A_113,B_114),'#skF_2'(A_113,B_114)),A_113)
      | B_114 = A_113
      | ~ v1_relat_1(B_114)
      | ~ v1_relat_1(A_113) ) ),
    inference(resolution,[status(thm)],[c_337,c_38])).

tff(c_26599,plain,
    ( r2_hidden('#skF_3'('#skF_11','#skF_12'),k1_relat_1('#skF_11'))
    | ~ v1_funct_1('#skF_11')
    | '#skF_11' = '#skF_12'
    | ~ v1_relat_1('#skF_12')
    | ~ v1_relat_1('#skF_11') ),
    inference(resolution,[status(thm)],[c_26491,c_349])).

tff(c_26616,plain,
    ( r2_hidden('#skF_3'('#skF_11','#skF_12'),'#skF_9')
    | '#skF_11' = '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_54,c_46,c_26599])).

tff(c_26618,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_18923,c_26616])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:30:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 13.23/5.71  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.32/5.72  
% 13.32/5.72  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.32/5.73  %$ r2_hidden > v1_relat_1 > v1_funct_1 > k5_relat_1 > k4_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_6 > #skF_11 > #skF_3 > #skF_10 > #skF_9 > #skF_2 > #skF_8 > #skF_7 > #skF_1 > #skF_5 > #skF_12 > #skF_4
% 13.32/5.73  
% 13.32/5.73  %Foreground sorts:
% 13.32/5.73  
% 13.32/5.73  
% 13.32/5.73  %Background operators:
% 13.32/5.73  
% 13.32/5.73  
% 13.32/5.73  %Foreground operators:
% 13.32/5.73  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 13.32/5.73  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 13.32/5.73  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 13.32/5.73  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 13.32/5.73  tff('#skF_11', type, '#skF_11': $i).
% 13.32/5.73  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 13.32/5.73  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 13.32/5.73  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 13.32/5.73  tff('#skF_10', type, '#skF_10': $i).
% 13.32/5.73  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 13.32/5.73  tff('#skF_9', type, '#skF_9': $i).
% 13.32/5.73  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 13.32/5.73  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 13.32/5.73  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 13.32/5.73  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 13.32/5.73  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 13.32/5.73  tff('#skF_8', type, '#skF_8': ($i * $i * $i) > $i).
% 13.32/5.73  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 13.32/5.73  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 13.32/5.73  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 13.32/5.73  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 13.32/5.73  tff('#skF_12', type, '#skF_12': $i).
% 13.32/5.73  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 13.32/5.73  
% 13.32/5.75  tff(f_100, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (![D]: ((v1_relat_1(D) & v1_funct_1(D)) => (((((A = k2_relat_1(B)) & (k1_relat_1(C) = A)) & (k1_relat_1(D) = A)) & (k5_relat_1(B, C) = k5_relat_1(B, D))) => (C = D)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t156_funct_1)).
% 13.32/5.75  tff(f_37, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => ((A = B) <=> (![C, D]: (r2_hidden(k4_tarski(C, D), A) <=> r2_hidden(k4_tarski(C, D), B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_relat_1)).
% 13.32/5.75  tff(f_75, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_1)).
% 13.32/5.75  tff(f_52, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_funct_1)).
% 13.32/5.75  tff(f_65, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(B)) => (k1_funct_1(k5_relat_1(B, C), A) = k1_funct_1(C, k1_funct_1(B, A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_funct_1)).
% 13.32/5.75  tff(c_40, plain, ('#skF_11'!='#skF_12'), inference(cnfTransformation, [status(thm)], [f_100])).
% 13.32/5.75  tff(c_56, plain, (v1_relat_1('#skF_11')), inference(cnfTransformation, [status(thm)], [f_100])).
% 13.32/5.75  tff(c_52, plain, (v1_relat_1('#skF_12')), inference(cnfTransformation, [status(thm)], [f_100])).
% 13.32/5.75  tff(c_50, plain, (v1_funct_1('#skF_12')), inference(cnfTransformation, [status(thm)], [f_100])).
% 13.32/5.75  tff(c_44, plain, (k1_relat_1('#skF_12')='#skF_9'), inference(cnfTransformation, [status(thm)], [f_100])).
% 13.32/5.75  tff(c_54, plain, (v1_funct_1('#skF_11')), inference(cnfTransformation, [status(thm)], [f_100])).
% 13.32/5.75  tff(c_46, plain, (k1_relat_1('#skF_11')='#skF_9'), inference(cnfTransformation, [status(thm)], [f_100])).
% 13.32/5.75  tff(c_809, plain, (![A_142, B_143]: (r2_hidden(k4_tarski('#skF_1'(A_142, B_143), '#skF_2'(A_142, B_143)), B_143) | r2_hidden(k4_tarski('#skF_3'(A_142, B_143), '#skF_4'(A_142, B_143)), A_142) | B_143=A_142 | ~v1_relat_1(B_143) | ~v1_relat_1(A_142))), inference(cnfTransformation, [status(thm)], [f_37])).
% 13.32/5.75  tff(c_38, plain, (![A_62, C_64, B_63]: (r2_hidden(A_62, k1_relat_1(C_64)) | ~r2_hidden(k4_tarski(A_62, B_63), C_64) | ~v1_funct_1(C_64) | ~v1_relat_1(C_64))), inference(cnfTransformation, [status(thm)], [f_75])).
% 13.32/5.75  tff(c_910, plain, (![A_149, B_150]: (r2_hidden('#skF_3'(A_149, B_150), k1_relat_1(A_149)) | ~v1_funct_1(A_149) | r2_hidden(k4_tarski('#skF_1'(A_149, B_150), '#skF_2'(A_149, B_150)), B_150) | B_150=A_149 | ~v1_relat_1(B_150) | ~v1_relat_1(A_149))), inference(resolution, [status(thm)], [c_809, c_38])).
% 13.32/5.75  tff(c_942, plain, (![A_151, B_152]: (r2_hidden('#skF_1'(A_151, B_152), k1_relat_1(B_152)) | ~v1_funct_1(B_152) | r2_hidden('#skF_3'(A_151, B_152), k1_relat_1(A_151)) | ~v1_funct_1(A_151) | B_152=A_151 | ~v1_relat_1(B_152) | ~v1_relat_1(A_151))), inference(resolution, [status(thm)], [c_910, c_38])).
% 13.32/5.75  tff(c_956, plain, (![B_152]: (r2_hidden('#skF_1'('#skF_11', B_152), k1_relat_1(B_152)) | ~v1_funct_1(B_152) | r2_hidden('#skF_3'('#skF_11', B_152), '#skF_9') | ~v1_funct_1('#skF_11') | B_152='#skF_11' | ~v1_relat_1(B_152) | ~v1_relat_1('#skF_11'))), inference(superposition, [status(thm), theory('equality')], [c_46, c_942])).
% 13.32/5.75  tff(c_1007, plain, (![B_156]: (r2_hidden('#skF_1'('#skF_11', B_156), k1_relat_1(B_156)) | ~v1_funct_1(B_156) | r2_hidden('#skF_3'('#skF_11', B_156), '#skF_9') | B_156='#skF_11' | ~v1_relat_1(B_156))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_956])).
% 13.32/5.75  tff(c_1019, plain, (r2_hidden('#skF_1'('#skF_11', '#skF_12'), '#skF_9') | ~v1_funct_1('#skF_12') | r2_hidden('#skF_3'('#skF_11', '#skF_12'), '#skF_9') | '#skF_11'='#skF_12' | ~v1_relat_1('#skF_12')), inference(superposition, [status(thm), theory('equality')], [c_44, c_1007])).
% 13.32/5.75  tff(c_1028, plain, (r2_hidden('#skF_1'('#skF_11', '#skF_12'), '#skF_9') | r2_hidden('#skF_3'('#skF_11', '#skF_12'), '#skF_9') | '#skF_11'='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_1019])).
% 13.32/5.75  tff(c_1029, plain, (r2_hidden('#skF_1'('#skF_11', '#skF_12'), '#skF_9') | r2_hidden('#skF_3'('#skF_11', '#skF_12'), '#skF_9')), inference(negUnitSimplification, [status(thm)], [c_40, c_1028])).
% 13.32/5.75  tff(c_1030, plain, (r2_hidden('#skF_3'('#skF_11', '#skF_12'), '#skF_9')), inference(splitLeft, [status(thm)], [c_1029])).
% 13.32/5.75  tff(c_60, plain, (v1_relat_1('#skF_10')), inference(cnfTransformation, [status(thm)], [f_100])).
% 13.32/5.75  tff(c_58, plain, (v1_funct_1('#skF_10')), inference(cnfTransformation, [status(thm)], [f_100])).
% 13.32/5.75  tff(c_48, plain, (k2_relat_1('#skF_10')='#skF_9'), inference(cnfTransformation, [status(thm)], [f_100])).
% 13.32/5.75  tff(c_115, plain, (![A_85, C_86]: (k1_funct_1(A_85, '#skF_8'(A_85, k2_relat_1(A_85), C_86))=C_86 | ~r2_hidden(C_86, k2_relat_1(A_85)) | ~v1_funct_1(A_85) | ~v1_relat_1(A_85))), inference(cnfTransformation, [status(thm)], [f_52])).
% 13.32/5.75  tff(c_134, plain, (![C_86]: (k1_funct_1('#skF_10', '#skF_8'('#skF_10', '#skF_9', C_86))=C_86 | ~r2_hidden(C_86, k2_relat_1('#skF_10')) | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_48, c_115])).
% 13.32/5.75  tff(c_140, plain, (![C_86]: (k1_funct_1('#skF_10', '#skF_8'('#skF_10', '#skF_9', C_86))=C_86 | ~r2_hidden(C_86, '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_48, c_134])).
% 13.32/5.75  tff(c_42, plain, (k5_relat_1('#skF_10', '#skF_11')=k5_relat_1('#skF_10', '#skF_12')), inference(cnfTransformation, [status(thm)], [f_100])).
% 13.32/5.75  tff(c_96, plain, (![A_80, C_81]: (r2_hidden('#skF_8'(A_80, k2_relat_1(A_80), C_81), k1_relat_1(A_80)) | ~r2_hidden(C_81, k2_relat_1(A_80)) | ~v1_funct_1(A_80) | ~v1_relat_1(A_80))), inference(cnfTransformation, [status(thm)], [f_52])).
% 13.32/5.75  tff(c_105, plain, (![C_81]: (r2_hidden('#skF_8'('#skF_10', '#skF_9', C_81), k1_relat_1('#skF_10')) | ~r2_hidden(C_81, k2_relat_1('#skF_10')) | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_48, c_96])).
% 13.32/5.75  tff(c_111, plain, (![C_81]: (r2_hidden('#skF_8'('#skF_10', '#skF_9', C_81), k1_relat_1('#skF_10')) | ~r2_hidden(C_81, '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_48, c_105])).
% 13.32/5.75  tff(c_207, plain, (![B_97, C_98, A_99]: (k1_funct_1(k5_relat_1(B_97, C_98), A_99)=k1_funct_1(C_98, k1_funct_1(B_97, A_99)) | ~r2_hidden(A_99, k1_relat_1(B_97)) | ~v1_funct_1(C_98) | ~v1_relat_1(C_98) | ~v1_funct_1(B_97) | ~v1_relat_1(B_97))), inference(cnfTransformation, [status(thm)], [f_65])).
% 13.32/5.75  tff(c_226, plain, (![C_98, C_81]: (k1_funct_1(k5_relat_1('#skF_10', C_98), '#skF_8'('#skF_10', '#skF_9', C_81))=k1_funct_1(C_98, k1_funct_1('#skF_10', '#skF_8'('#skF_10', '#skF_9', C_81))) | ~v1_funct_1(C_98) | ~v1_relat_1(C_98) | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10') | ~r2_hidden(C_81, '#skF_9'))), inference(resolution, [status(thm)], [c_111, c_207])).
% 13.32/5.75  tff(c_357, plain, (![C_118, C_119]: (k1_funct_1(k5_relat_1('#skF_10', C_118), '#skF_8'('#skF_10', '#skF_9', C_119))=k1_funct_1(C_118, k1_funct_1('#skF_10', '#skF_8'('#skF_10', '#skF_9', C_119))) | ~v1_funct_1(C_118) | ~v1_relat_1(C_118) | ~r2_hidden(C_119, '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_226])).
% 13.32/5.75  tff(c_374, plain, (![C_119]: (k1_funct_1(k5_relat_1('#skF_10', '#skF_12'), '#skF_8'('#skF_10', '#skF_9', C_119))=k1_funct_1('#skF_11', k1_funct_1('#skF_10', '#skF_8'('#skF_10', '#skF_9', C_119))) | ~v1_funct_1('#skF_11') | ~v1_relat_1('#skF_11') | ~r2_hidden(C_119, '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_42, c_357])).
% 13.32/5.75  tff(c_379, plain, (![C_120]: (k1_funct_1(k5_relat_1('#skF_10', '#skF_12'), '#skF_8'('#skF_10', '#skF_9', C_120))=k1_funct_1('#skF_11', k1_funct_1('#skF_10', '#skF_8'('#skF_10', '#skF_9', C_120))) | ~r2_hidden(C_120, '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_374])).
% 13.32/5.75  tff(c_244, plain, (![C_98, C_81]: (k1_funct_1(k5_relat_1('#skF_10', C_98), '#skF_8'('#skF_10', '#skF_9', C_81))=k1_funct_1(C_98, k1_funct_1('#skF_10', '#skF_8'('#skF_10', '#skF_9', C_81))) | ~v1_funct_1(C_98) | ~v1_relat_1(C_98) | ~r2_hidden(C_81, '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_226])).
% 13.32/5.75  tff(c_385, plain, (![C_120]: (k1_funct_1('#skF_11', k1_funct_1('#skF_10', '#skF_8'('#skF_10', '#skF_9', C_120)))=k1_funct_1('#skF_12', k1_funct_1('#skF_10', '#skF_8'('#skF_10', '#skF_9', C_120))) | ~v1_funct_1('#skF_12') | ~v1_relat_1('#skF_12') | ~r2_hidden(C_120, '#skF_9') | ~r2_hidden(C_120, '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_379, c_244])).
% 13.32/5.75  tff(c_407, plain, (![C_121]: (k1_funct_1('#skF_11', k1_funct_1('#skF_10', '#skF_8'('#skF_10', '#skF_9', C_121)))=k1_funct_1('#skF_12', k1_funct_1('#skF_10', '#skF_8'('#skF_10', '#skF_9', C_121))) | ~r2_hidden(C_121, '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_385])).
% 13.32/5.75  tff(c_433, plain, (![C_122]: (k1_funct_1('#skF_12', k1_funct_1('#skF_10', '#skF_8'('#skF_10', '#skF_9', C_122)))=k1_funct_1('#skF_11', C_122) | ~r2_hidden(C_122, '#skF_9') | ~r2_hidden(C_122, '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_140, c_407])).
% 13.32/5.75  tff(c_450, plain, (![C_86]: (k1_funct_1('#skF_11', C_86)=k1_funct_1('#skF_12', C_86) | ~r2_hidden(C_86, '#skF_9') | ~r2_hidden(C_86, '#skF_9') | ~r2_hidden(C_86, '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_140, c_433])).
% 13.32/5.75  tff(c_1032, plain, (k1_funct_1('#skF_11', '#skF_3'('#skF_11', '#skF_12'))=k1_funct_1('#skF_12', '#skF_3'('#skF_11', '#skF_12')) | ~r2_hidden('#skF_3'('#skF_11', '#skF_12'), '#skF_9')), inference(resolution, [status(thm)], [c_1030, c_450])).
% 13.32/5.75  tff(c_1035, plain, (k1_funct_1('#skF_11', '#skF_3'('#skF_11', '#skF_12'))=k1_funct_1('#skF_12', '#skF_3'('#skF_11', '#skF_12'))), inference(demodulation, [status(thm), theory('equality')], [c_1030, c_1032])).
% 13.32/5.75  tff(c_36, plain, (![C_64, A_62, B_63]: (k1_funct_1(C_64, A_62)=B_63 | ~r2_hidden(k4_tarski(A_62, B_63), C_64) | ~v1_funct_1(C_64) | ~v1_relat_1(C_64))), inference(cnfTransformation, [status(thm)], [f_75])).
% 13.32/5.75  tff(c_1199, plain, (![A_164, B_165]: (k1_funct_1(A_164, '#skF_3'(A_164, B_165))='#skF_4'(A_164, B_165) | ~v1_funct_1(A_164) | r2_hidden(k4_tarski('#skF_1'(A_164, B_165), '#skF_2'(A_164, B_165)), B_165) | B_165=A_164 | ~v1_relat_1(B_165) | ~v1_relat_1(A_164))), inference(resolution, [status(thm)], [c_809, c_36])).
% 13.32/5.75  tff(c_17993, plain, (![B_618, A_619]: (k1_funct_1(B_618, '#skF_1'(A_619, B_618))='#skF_2'(A_619, B_618) | ~v1_funct_1(B_618) | k1_funct_1(A_619, '#skF_3'(A_619, B_618))='#skF_4'(A_619, B_618) | ~v1_funct_1(A_619) | B_618=A_619 | ~v1_relat_1(B_618) | ~v1_relat_1(A_619))), inference(resolution, [status(thm)], [c_1199, c_36])).
% 13.32/5.75  tff(c_18205, plain, (k1_funct_1('#skF_12', '#skF_1'('#skF_11', '#skF_12'))='#skF_2'('#skF_11', '#skF_12') | ~v1_funct_1('#skF_12') | k1_funct_1('#skF_12', '#skF_3'('#skF_11', '#skF_12'))='#skF_4'('#skF_11', '#skF_12') | ~v1_funct_1('#skF_11') | '#skF_11'='#skF_12' | ~v1_relat_1('#skF_12') | ~v1_relat_1('#skF_11')), inference(superposition, [status(thm), theory('equality')], [c_1035, c_17993])).
% 13.32/5.75  tff(c_18294, plain, (k1_funct_1('#skF_12', '#skF_1'('#skF_11', '#skF_12'))='#skF_2'('#skF_11', '#skF_12') | k1_funct_1('#skF_12', '#skF_3'('#skF_11', '#skF_12'))='#skF_4'('#skF_11', '#skF_12') | '#skF_11'='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_52, c_54, c_50, c_18205])).
% 13.32/5.75  tff(c_18295, plain, (k1_funct_1('#skF_12', '#skF_1'('#skF_11', '#skF_12'))='#skF_2'('#skF_11', '#skF_12') | k1_funct_1('#skF_12', '#skF_3'('#skF_11', '#skF_12'))='#skF_4'('#skF_11', '#skF_12')), inference(negUnitSimplification, [status(thm)], [c_40, c_18294])).
% 13.32/5.75  tff(c_18298, plain, (k1_funct_1('#skF_12', '#skF_3'('#skF_11', '#skF_12'))='#skF_4'('#skF_11', '#skF_12')), inference(splitLeft, [status(thm)], [c_18295])).
% 13.32/5.75  tff(c_34, plain, (![A_62, C_64]: (r2_hidden(k4_tarski(A_62, k1_funct_1(C_64, A_62)), C_64) | ~r2_hidden(A_62, k1_relat_1(C_64)) | ~v1_funct_1(C_64) | ~v1_relat_1(C_64))), inference(cnfTransformation, [status(thm)], [f_75])).
% 13.32/5.75  tff(c_18358, plain, (r2_hidden(k4_tarski('#skF_3'('#skF_11', '#skF_12'), '#skF_4'('#skF_11', '#skF_12')), '#skF_12') | ~r2_hidden('#skF_3'('#skF_11', '#skF_12'), k1_relat_1('#skF_12')) | ~v1_funct_1('#skF_12') | ~v1_relat_1('#skF_12')), inference(superposition, [status(thm), theory('equality')], [c_18298, c_34])).
% 13.32/5.75  tff(c_18373, plain, (r2_hidden(k4_tarski('#skF_3'('#skF_11', '#skF_12'), '#skF_4'('#skF_11', '#skF_12')), '#skF_12')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_1030, c_44, c_18358])).
% 13.32/5.75  tff(c_4, plain, (![A_1, B_11]: (r2_hidden(k4_tarski('#skF_1'(A_1, B_11), '#skF_2'(A_1, B_11)), B_11) | ~r2_hidden(k4_tarski('#skF_3'(A_1, B_11), '#skF_4'(A_1, B_11)), B_11) | B_11=A_1 | ~v1_relat_1(B_11) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_37])).
% 13.32/5.75  tff(c_18507, plain, (r2_hidden(k4_tarski('#skF_1'('#skF_11', '#skF_12'), '#skF_2'('#skF_11', '#skF_12')), '#skF_12') | '#skF_11'='#skF_12' | ~v1_relat_1('#skF_12') | ~v1_relat_1('#skF_11')), inference(resolution, [status(thm)], [c_18373, c_4])).
% 13.32/5.75  tff(c_18516, plain, (r2_hidden(k4_tarski('#skF_1'('#skF_11', '#skF_12'), '#skF_2'('#skF_11', '#skF_12')), '#skF_12') | '#skF_11'='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_52, c_18507])).
% 13.32/5.75  tff(c_18517, plain, (r2_hidden(k4_tarski('#skF_1'('#skF_11', '#skF_12'), '#skF_2'('#skF_11', '#skF_12')), '#skF_12')), inference(negUnitSimplification, [status(thm)], [c_40, c_18516])).
% 13.32/5.75  tff(c_18530, plain, (r2_hidden('#skF_1'('#skF_11', '#skF_12'), k1_relat_1('#skF_12')) | ~v1_funct_1('#skF_12') | ~v1_relat_1('#skF_12')), inference(resolution, [status(thm)], [c_18517, c_38])).
% 13.32/5.75  tff(c_18536, plain, (r2_hidden('#skF_1'('#skF_11', '#skF_12'), '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_44, c_18530])).
% 13.32/5.75  tff(c_18141, plain, (k1_funct_1('#skF_12', '#skF_3'('#skF_11', '#skF_12'))='#skF_4'('#skF_11', '#skF_12') | k1_funct_1('#skF_12', '#skF_1'('#skF_11', '#skF_12'))='#skF_2'('#skF_11', '#skF_12') | ~v1_funct_1('#skF_12') | ~v1_funct_1('#skF_11') | '#skF_11'='#skF_12' | ~v1_relat_1('#skF_12') | ~v1_relat_1('#skF_11')), inference(superposition, [status(thm), theory('equality')], [c_17993, c_1035])).
% 13.32/5.75  tff(c_18272, plain, (k1_funct_1('#skF_12', '#skF_3'('#skF_11', '#skF_12'))='#skF_4'('#skF_11', '#skF_12') | k1_funct_1('#skF_12', '#skF_1'('#skF_11', '#skF_12'))='#skF_2'('#skF_11', '#skF_12') | '#skF_11'='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_52, c_54, c_50, c_18141])).
% 13.32/5.75  tff(c_18273, plain, (k1_funct_1('#skF_12', '#skF_3'('#skF_11', '#skF_12'))='#skF_4'('#skF_11', '#skF_12') | k1_funct_1('#skF_12', '#skF_1'('#skF_11', '#skF_12'))='#skF_2'('#skF_11', '#skF_12')), inference(negUnitSimplification, [status(thm)], [c_40, c_18272])).
% 13.32/5.75  tff(c_18297, plain, (k1_funct_1('#skF_12', '#skF_1'('#skF_11', '#skF_12'))='#skF_2'('#skF_11', '#skF_12')), inference(splitLeft, [status(thm)], [c_18273])).
% 13.32/5.75  tff(c_18538, plain, (k1_funct_1('#skF_11', '#skF_1'('#skF_11', '#skF_12'))=k1_funct_1('#skF_12', '#skF_1'('#skF_11', '#skF_12')) | ~r2_hidden('#skF_1'('#skF_11', '#skF_12'), '#skF_9')), inference(resolution, [status(thm)], [c_18536, c_450])).
% 13.32/5.75  tff(c_18541, plain, (k1_funct_1('#skF_11', '#skF_1'('#skF_11', '#skF_12'))='#skF_2'('#skF_11', '#skF_12')), inference(demodulation, [status(thm), theory('equality')], [c_18536, c_18297, c_18538])).
% 13.32/5.75  tff(c_18555, plain, (r2_hidden(k4_tarski('#skF_1'('#skF_11', '#skF_12'), '#skF_2'('#skF_11', '#skF_12')), '#skF_11') | ~r2_hidden('#skF_1'('#skF_11', '#skF_12'), k1_relat_1('#skF_11')) | ~v1_funct_1('#skF_11') | ~v1_relat_1('#skF_11')), inference(superposition, [status(thm), theory('equality')], [c_18541, c_34])).
% 13.32/5.75  tff(c_18570, plain, (r2_hidden(k4_tarski('#skF_1'('#skF_11', '#skF_12'), '#skF_2'('#skF_11', '#skF_12')), '#skF_11')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_18536, c_46, c_18555])).
% 13.32/5.75  tff(c_2, plain, (![A_1, B_11]: (~r2_hidden(k4_tarski('#skF_1'(A_1, B_11), '#skF_2'(A_1, B_11)), A_1) | ~r2_hidden(k4_tarski('#skF_3'(A_1, B_11), '#skF_4'(A_1, B_11)), B_11) | B_11=A_1 | ~v1_relat_1(B_11) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_37])).
% 13.32/5.75  tff(c_18584, plain, (~r2_hidden(k4_tarski('#skF_3'('#skF_11', '#skF_12'), '#skF_4'('#skF_11', '#skF_12')), '#skF_12') | '#skF_11'='#skF_12' | ~v1_relat_1('#skF_12') | ~v1_relat_1('#skF_11')), inference(resolution, [status(thm)], [c_18570, c_2])).
% 13.32/5.75  tff(c_18600, plain, ('#skF_11'='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_52, c_18373, c_18584])).
% 13.32/5.75  tff(c_18602, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_18600])).
% 13.32/5.75  tff(c_18604, plain, (k1_funct_1('#skF_12', '#skF_3'('#skF_11', '#skF_12'))!='#skF_4'('#skF_11', '#skF_12')), inference(splitRight, [status(thm)], [c_18295])).
% 13.32/5.75  tff(c_17559, plain, (![A_614, B_615]: (r2_hidden('#skF_1'(A_614, B_615), k1_relat_1(B_615)) | ~v1_funct_1(B_615) | k1_funct_1(A_614, '#skF_3'(A_614, B_615))='#skF_4'(A_614, B_615) | ~v1_funct_1(A_614) | B_615=A_614 | ~v1_relat_1(B_615) | ~v1_relat_1(A_614))), inference(resolution, [status(thm)], [c_1199, c_38])).
% 13.32/5.75  tff(c_17649, plain, (![A_614]: (r2_hidden('#skF_1'(A_614, '#skF_12'), '#skF_9') | ~v1_funct_1('#skF_12') | k1_funct_1(A_614, '#skF_3'(A_614, '#skF_12'))='#skF_4'(A_614, '#skF_12') | ~v1_funct_1(A_614) | A_614='#skF_12' | ~v1_relat_1('#skF_12') | ~v1_relat_1(A_614))), inference(superposition, [status(thm), theory('equality')], [c_44, c_17559])).
% 13.32/5.75  tff(c_17658, plain, (![A_614]: (r2_hidden('#skF_1'(A_614, '#skF_12'), '#skF_9') | k1_funct_1(A_614, '#skF_3'(A_614, '#skF_12'))='#skF_4'(A_614, '#skF_12') | ~v1_funct_1(A_614) | A_614='#skF_12' | ~v1_relat_1(A_614))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_17649])).
% 13.32/5.75  tff(c_30, plain, (![A_18, B_40]: (r2_hidden('#skF_6'(A_18, B_40), k1_relat_1(A_18)) | r2_hidden('#skF_7'(A_18, B_40), B_40) | k2_relat_1(A_18)=B_40 | ~v1_funct_1(A_18) | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_52])).
% 13.32/5.75  tff(c_176, plain, (![A_93, B_94]: (k1_funct_1(A_93, '#skF_6'(A_93, B_94))='#skF_5'(A_93, B_94) | r2_hidden('#skF_7'(A_93, B_94), B_94) | k2_relat_1(A_93)=B_94 | ~v1_funct_1(A_93) | ~v1_relat_1(A_93))), inference(cnfTransformation, [status(thm)], [f_52])).
% 13.32/5.75  tff(c_14, plain, (![A_18, D_57]: (r2_hidden(k1_funct_1(A_18, D_57), k2_relat_1(A_18)) | ~r2_hidden(D_57, k1_relat_1(A_18)) | ~v1_funct_1(A_18) | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_52])).
% 13.32/5.75  tff(c_13477, plain, (![A_483, B_484]: (r2_hidden('#skF_5'(A_483, B_484), k2_relat_1(A_483)) | ~r2_hidden('#skF_6'(A_483, B_484), k1_relat_1(A_483)) | ~v1_funct_1(A_483) | ~v1_relat_1(A_483) | r2_hidden('#skF_7'(A_483, B_484), B_484) | k2_relat_1(A_483)=B_484 | ~v1_funct_1(A_483) | ~v1_relat_1(A_483))), inference(superposition, [status(thm), theory('equality')], [c_176, c_14])).
% 13.32/5.75  tff(c_13612, plain, (![A_490, B_491]: (r2_hidden('#skF_5'(A_490, B_491), k2_relat_1(A_490)) | r2_hidden('#skF_7'(A_490, B_491), B_491) | k2_relat_1(A_490)=B_491 | ~v1_funct_1(A_490) | ~v1_relat_1(A_490))), inference(resolution, [status(thm)], [c_30, c_13477])).
% 13.32/5.75  tff(c_13628, plain, (![B_491]: (r2_hidden('#skF_5'('#skF_10', B_491), '#skF_9') | r2_hidden('#skF_7'('#skF_10', B_491), B_491) | k2_relat_1('#skF_10')=B_491 | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_48, c_13612])).
% 13.32/5.75  tff(c_13635, plain, (![B_492]: (r2_hidden('#skF_5'('#skF_10', B_492), '#skF_9') | r2_hidden('#skF_7'('#skF_10', B_492), B_492) | B_492='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_48, c_13628])).
% 13.32/5.75  tff(c_79, plain, (![A_75, D_76]: (r2_hidden(k1_funct_1(A_75, D_76), k2_relat_1(A_75)) | ~r2_hidden(D_76, k1_relat_1(A_75)) | ~v1_funct_1(A_75) | ~v1_relat_1(A_75))), inference(cnfTransformation, [status(thm)], [f_52])).
% 13.32/5.75  tff(c_82, plain, (![D_76]: (r2_hidden(k1_funct_1('#skF_10', D_76), '#skF_9') | ~r2_hidden(D_76, k1_relat_1('#skF_10')) | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_48, c_79])).
% 13.32/5.75  tff(c_84, plain, (![D_76]: (r2_hidden(k1_funct_1('#skF_10', D_76), '#skF_9') | ~r2_hidden(D_76, k1_relat_1('#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_82])).
% 13.32/5.75  tff(c_459, plain, (![C_123]: (k1_funct_1('#skF_11', C_123)=k1_funct_1('#skF_12', C_123) | ~r2_hidden(C_123, '#skF_9') | ~r2_hidden(C_123, '#skF_9') | ~r2_hidden(C_123, '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_140, c_433])).
% 13.32/5.75  tff(c_642, plain, (![D_136]: (k1_funct_1('#skF_11', k1_funct_1('#skF_10', D_136))=k1_funct_1('#skF_12', k1_funct_1('#skF_10', D_136)) | ~r2_hidden(k1_funct_1('#skF_10', D_136), '#skF_9') | ~r2_hidden(D_136, k1_relat_1('#skF_10')))), inference(resolution, [status(thm)], [c_84, c_459])).
% 13.32/5.75  tff(c_657, plain, (![D_76]: (k1_funct_1('#skF_11', k1_funct_1('#skF_10', D_76))=k1_funct_1('#skF_12', k1_funct_1('#skF_10', D_76)) | ~r2_hidden(D_76, k1_relat_1('#skF_10')))), inference(resolution, [status(thm)], [c_84, c_642])).
% 13.32/5.75  tff(c_13646, plain, (k1_funct_1('#skF_11', k1_funct_1('#skF_10', '#skF_7'('#skF_10', k1_relat_1('#skF_10'))))=k1_funct_1('#skF_12', k1_funct_1('#skF_10', '#skF_7'('#skF_10', k1_relat_1('#skF_10')))) | r2_hidden('#skF_5'('#skF_10', k1_relat_1('#skF_10')), '#skF_9') | k1_relat_1('#skF_10')='#skF_9'), inference(resolution, [status(thm)], [c_13635, c_657])).
% 13.32/5.75  tff(c_14013, plain, (k1_relat_1('#skF_10')='#skF_9'), inference(splitLeft, [status(thm)], [c_13646])).
% 13.32/5.75  tff(c_164, plain, (![A_90, B_91]: (r2_hidden('#skF_6'(A_90, B_91), k1_relat_1(A_90)) | r2_hidden('#skF_7'(A_90, B_91), B_91) | k2_relat_1(A_90)=B_91 | ~v1_funct_1(A_90) | ~v1_relat_1(A_90))), inference(cnfTransformation, [status(thm)], [f_52])).
% 13.32/5.75  tff(c_170, plain, (![B_91]: (r2_hidden('#skF_6'('#skF_12', B_91), '#skF_9') | r2_hidden('#skF_7'('#skF_12', B_91), B_91) | k2_relat_1('#skF_12')=B_91 | ~v1_funct_1('#skF_12') | ~v1_relat_1('#skF_12'))), inference(superposition, [status(thm), theory('equality')], [c_44, c_164])).
% 13.32/5.75  tff(c_174, plain, (![B_91]: (r2_hidden('#skF_6'('#skF_12', B_91), '#skF_9') | r2_hidden('#skF_7'('#skF_12', B_91), B_91) | k2_relat_1('#skF_12')=B_91)), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_170])).
% 13.32/5.75  tff(c_658, plain, (![D_137]: (k1_funct_1('#skF_11', k1_funct_1('#skF_10', D_137))=k1_funct_1('#skF_12', k1_funct_1('#skF_10', D_137)) | ~r2_hidden(D_137, k1_relat_1('#skF_10')))), inference(resolution, [status(thm)], [c_84, c_642])).
% 13.32/5.75  tff(c_702, plain, (k1_funct_1('#skF_11', k1_funct_1('#skF_10', '#skF_7'('#skF_12', k1_relat_1('#skF_10'))))=k1_funct_1('#skF_12', k1_funct_1('#skF_10', '#skF_7'('#skF_12', k1_relat_1('#skF_10')))) | r2_hidden('#skF_6'('#skF_12', k1_relat_1('#skF_10')), '#skF_9') | k2_relat_1('#skF_12')=k1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_174, c_658])).
% 13.32/5.75  tff(c_14120, plain, (k1_funct_1('#skF_11', k1_funct_1('#skF_10', '#skF_7'('#skF_12', '#skF_9')))=k1_funct_1('#skF_12', k1_funct_1('#skF_10', '#skF_7'('#skF_12', '#skF_9'))) | r2_hidden('#skF_6'('#skF_12', '#skF_9'), '#skF_9') | k2_relat_1('#skF_12')='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_14013, c_14013, c_14013, c_14013, c_702])).
% 13.32/5.75  tff(c_14121, plain, (k2_relat_1('#skF_12')='#skF_9'), inference(splitLeft, [status(thm)], [c_14120])).
% 13.32/5.75  tff(c_18624, plain, (r2_hidden('#skF_2'('#skF_11', '#skF_12'), k2_relat_1('#skF_12')) | ~r2_hidden('#skF_1'('#skF_11', '#skF_12'), k1_relat_1('#skF_12')) | ~v1_funct_1('#skF_12') | ~v1_relat_1('#skF_12')), inference(superposition, [status(thm), theory('equality')], [c_18297, c_14])).
% 13.32/5.75  tff(c_18638, plain, (r2_hidden('#skF_2'('#skF_11', '#skF_12'), '#skF_9') | ~r2_hidden('#skF_1'('#skF_11', '#skF_12'), '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_44, c_14121, c_18624])).
% 13.32/5.75  tff(c_18641, plain, (~r2_hidden('#skF_1'('#skF_11', '#skF_12'), '#skF_9')), inference(splitLeft, [status(thm)], [c_18638])).
% 13.32/5.75  tff(c_18644, plain, (k1_funct_1('#skF_11', '#skF_3'('#skF_11', '#skF_12'))='#skF_4'('#skF_11', '#skF_12') | ~v1_funct_1('#skF_11') | '#skF_11'='#skF_12' | ~v1_relat_1('#skF_11')), inference(resolution, [status(thm)], [c_17658, c_18641])).
% 13.32/5.75  tff(c_18647, plain, (k1_funct_1('#skF_12', '#skF_3'('#skF_11', '#skF_12'))='#skF_4'('#skF_11', '#skF_12') | '#skF_11'='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_1035, c_18644])).
% 13.32/5.75  tff(c_18649, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_18604, c_18647])).
% 13.32/5.75  tff(c_18651, plain, (r2_hidden('#skF_1'('#skF_11', '#skF_12'), '#skF_9')), inference(splitRight, [status(thm)], [c_18638])).
% 13.32/5.75  tff(c_18653, plain, (k1_funct_1('#skF_11', '#skF_1'('#skF_11', '#skF_12'))=k1_funct_1('#skF_12', '#skF_1'('#skF_11', '#skF_12')) | ~r2_hidden('#skF_1'('#skF_11', '#skF_12'), '#skF_9')), inference(resolution, [status(thm)], [c_18651, c_450])).
% 13.32/5.75  tff(c_18656, plain, (k1_funct_1('#skF_11', '#skF_1'('#skF_11', '#skF_12'))='#skF_2'('#skF_11', '#skF_12')), inference(demodulation, [status(thm), theory('equality')], [c_18651, c_18297, c_18653])).
% 13.32/5.75  tff(c_18675, plain, (r2_hidden(k4_tarski('#skF_1'('#skF_11', '#skF_12'), '#skF_2'('#skF_11', '#skF_12')), '#skF_11') | ~r2_hidden('#skF_1'('#skF_11', '#skF_12'), k1_relat_1('#skF_11')) | ~v1_funct_1('#skF_11') | ~v1_relat_1('#skF_11')), inference(superposition, [status(thm), theory('equality')], [c_18656, c_34])).
% 13.32/5.75  tff(c_18690, plain, (r2_hidden(k4_tarski('#skF_1'('#skF_11', '#skF_12'), '#skF_2'('#skF_11', '#skF_12')), '#skF_11')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_18651, c_46, c_18675])).
% 13.32/5.75  tff(c_337, plain, (![A_113, B_114]: (~r2_hidden(k4_tarski('#skF_1'(A_113, B_114), '#skF_2'(A_113, B_114)), A_113) | r2_hidden(k4_tarski('#skF_3'(A_113, B_114), '#skF_4'(A_113, B_114)), A_113) | B_114=A_113 | ~v1_relat_1(B_114) | ~v1_relat_1(A_113))), inference(cnfTransformation, [status(thm)], [f_37])).
% 13.32/5.75  tff(c_348, plain, (![A_113, B_114]: (k1_funct_1(A_113, '#skF_3'(A_113, B_114))='#skF_4'(A_113, B_114) | ~v1_funct_1(A_113) | ~r2_hidden(k4_tarski('#skF_1'(A_113, B_114), '#skF_2'(A_113, B_114)), A_113) | B_114=A_113 | ~v1_relat_1(B_114) | ~v1_relat_1(A_113))), inference(resolution, [status(thm)], [c_337, c_36])).
% 13.32/5.75  tff(c_18696, plain, (k1_funct_1('#skF_11', '#skF_3'('#skF_11', '#skF_12'))='#skF_4'('#skF_11', '#skF_12') | ~v1_funct_1('#skF_11') | '#skF_11'='#skF_12' | ~v1_relat_1('#skF_12') | ~v1_relat_1('#skF_11')), inference(resolution, [status(thm)], [c_18690, c_348])).
% 13.32/5.75  tff(c_18710, plain, (k1_funct_1('#skF_12', '#skF_3'('#skF_11', '#skF_12'))='#skF_4'('#skF_11', '#skF_12') | '#skF_11'='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_52, c_54, c_1035, c_18696])).
% 13.32/5.75  tff(c_18712, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_18604, c_18710])).
% 13.32/5.75  tff(c_18714, plain, (k1_funct_1('#skF_12', '#skF_1'('#skF_11', '#skF_12'))!='#skF_2'('#skF_11', '#skF_12')), inference(splitRight, [status(thm)], [c_18273])).
% 13.32/5.75  tff(c_18713, plain, (k1_funct_1('#skF_12', '#skF_3'('#skF_11', '#skF_12'))='#skF_4'('#skF_11', '#skF_12')), inference(splitRight, [status(thm)], [c_18273])).
% 13.32/5.75  tff(c_18740, plain, (r2_hidden(k4_tarski('#skF_3'('#skF_11', '#skF_12'), '#skF_4'('#skF_11', '#skF_12')), '#skF_12') | ~r2_hidden('#skF_3'('#skF_11', '#skF_12'), k1_relat_1('#skF_12')) | ~v1_funct_1('#skF_12') | ~v1_relat_1('#skF_12')), inference(superposition, [status(thm), theory('equality')], [c_18713, c_34])).
% 13.32/5.75  tff(c_18755, plain, (r2_hidden(k4_tarski('#skF_3'('#skF_11', '#skF_12'), '#skF_4'('#skF_11', '#skF_12')), '#skF_12')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_1030, c_44, c_18740])).
% 13.32/5.75  tff(c_18893, plain, (r2_hidden(k4_tarski('#skF_1'('#skF_11', '#skF_12'), '#skF_2'('#skF_11', '#skF_12')), '#skF_12') | '#skF_11'='#skF_12' | ~v1_relat_1('#skF_12') | ~v1_relat_1('#skF_11')), inference(resolution, [status(thm)], [c_18755, c_4])).
% 13.32/5.75  tff(c_18902, plain, (r2_hidden(k4_tarski('#skF_1'('#skF_11', '#skF_12'), '#skF_2'('#skF_11', '#skF_12')), '#skF_12') | '#skF_11'='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_52, c_18893])).
% 13.32/5.75  tff(c_18903, plain, (r2_hidden(k4_tarski('#skF_1'('#skF_11', '#skF_12'), '#skF_2'('#skF_11', '#skF_12')), '#skF_12')), inference(negUnitSimplification, [status(thm)], [c_40, c_18902])).
% 13.32/5.75  tff(c_18913, plain, (k1_funct_1('#skF_12', '#skF_1'('#skF_11', '#skF_12'))='#skF_2'('#skF_11', '#skF_12') | ~v1_funct_1('#skF_12') | ~v1_relat_1('#skF_12')), inference(resolution, [status(thm)], [c_18903, c_36])).
% 13.32/5.75  tff(c_18919, plain, (k1_funct_1('#skF_12', '#skF_1'('#skF_11', '#skF_12'))='#skF_2'('#skF_11', '#skF_12')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_18913])).
% 13.32/5.75  tff(c_18921, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18714, c_18919])).
% 13.32/5.75  tff(c_18923, plain, (~r2_hidden('#skF_3'('#skF_11', '#skF_12'), '#skF_9')), inference(splitRight, [status(thm)], [c_1029])).
% 13.32/5.75  tff(c_19198, plain, (![B_635, A_636]: (k1_funct_1(B_635, '#skF_1'(A_636, B_635))='#skF_2'(A_636, B_635) | ~v1_funct_1(B_635) | r2_hidden(k4_tarski('#skF_3'(A_636, B_635), '#skF_4'(A_636, B_635)), A_636) | B_635=A_636 | ~v1_relat_1(B_635) | ~v1_relat_1(A_636))), inference(resolution, [status(thm)], [c_809, c_36])).
% 13.32/5.75  tff(c_26111, plain, (![A_885, B_886]: (r2_hidden('#skF_3'(A_885, B_886), k1_relat_1(A_885)) | ~v1_funct_1(A_885) | k1_funct_1(B_886, '#skF_1'(A_885, B_886))='#skF_2'(A_885, B_886) | ~v1_funct_1(B_886) | B_886=A_885 | ~v1_relat_1(B_886) | ~v1_relat_1(A_885))), inference(resolution, [status(thm)], [c_19198, c_38])).
% 13.32/5.75  tff(c_26185, plain, (![B_886]: (r2_hidden('#skF_3'('#skF_11', B_886), '#skF_9') | ~v1_funct_1('#skF_11') | k1_funct_1(B_886, '#skF_1'('#skF_11', B_886))='#skF_2'('#skF_11', B_886) | ~v1_funct_1(B_886) | B_886='#skF_11' | ~v1_relat_1(B_886) | ~v1_relat_1('#skF_11'))), inference(superposition, [status(thm), theory('equality')], [c_46, c_26111])).
% 13.32/5.75  tff(c_26387, plain, (![B_890]: (r2_hidden('#skF_3'('#skF_11', B_890), '#skF_9') | k1_funct_1(B_890, '#skF_1'('#skF_11', B_890))='#skF_2'('#skF_11', B_890) | ~v1_funct_1(B_890) | B_890='#skF_11' | ~v1_relat_1(B_890))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_26185])).
% 13.32/5.75  tff(c_26390, plain, (k1_funct_1('#skF_12', '#skF_1'('#skF_11', '#skF_12'))='#skF_2'('#skF_11', '#skF_12') | ~v1_funct_1('#skF_12') | '#skF_11'='#skF_12' | ~v1_relat_1('#skF_12')), inference(resolution, [status(thm)], [c_26387, c_18923])).
% 13.32/5.75  tff(c_26473, plain, (k1_funct_1('#skF_12', '#skF_1'('#skF_11', '#skF_12'))='#skF_2'('#skF_11', '#skF_12') | '#skF_11'='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_26390])).
% 13.32/5.75  tff(c_26474, plain, (k1_funct_1('#skF_12', '#skF_1'('#skF_11', '#skF_12'))='#skF_2'('#skF_11', '#skF_12')), inference(negUnitSimplification, [status(thm)], [c_40, c_26473])).
% 13.32/5.75  tff(c_18922, plain, (r2_hidden('#skF_1'('#skF_11', '#skF_12'), '#skF_9')), inference(splitRight, [status(thm)], [c_1029])).
% 13.32/5.75  tff(c_18925, plain, (k1_funct_1('#skF_11', '#skF_1'('#skF_11', '#skF_12'))=k1_funct_1('#skF_12', '#skF_1'('#skF_11', '#skF_12')) | ~r2_hidden('#skF_1'('#skF_11', '#skF_12'), '#skF_9')), inference(resolution, [status(thm)], [c_18922, c_450])).
% 13.32/5.75  tff(c_18928, plain, (k1_funct_1('#skF_11', '#skF_1'('#skF_11', '#skF_12'))=k1_funct_1('#skF_12', '#skF_1'('#skF_11', '#skF_12'))), inference(demodulation, [status(thm), theory('equality')], [c_18922, c_18925])).
% 13.32/5.75  tff(c_18967, plain, (r2_hidden(k4_tarski('#skF_1'('#skF_11', '#skF_12'), k1_funct_1('#skF_12', '#skF_1'('#skF_11', '#skF_12'))), '#skF_11') | ~r2_hidden('#skF_1'('#skF_11', '#skF_12'), k1_relat_1('#skF_11')) | ~v1_funct_1('#skF_11') | ~v1_relat_1('#skF_11')), inference(superposition, [status(thm), theory('equality')], [c_18928, c_34])).
% 13.32/5.75  tff(c_18980, plain, (r2_hidden(k4_tarski('#skF_1'('#skF_11', '#skF_12'), k1_funct_1('#skF_12', '#skF_1'('#skF_11', '#skF_12'))), '#skF_11')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_18922, c_46, c_18967])).
% 13.32/5.75  tff(c_26491, plain, (r2_hidden(k4_tarski('#skF_1'('#skF_11', '#skF_12'), '#skF_2'('#skF_11', '#skF_12')), '#skF_11')), inference(demodulation, [status(thm), theory('equality')], [c_26474, c_18980])).
% 13.32/5.75  tff(c_349, plain, (![A_113, B_114]: (r2_hidden('#skF_3'(A_113, B_114), k1_relat_1(A_113)) | ~v1_funct_1(A_113) | ~r2_hidden(k4_tarski('#skF_1'(A_113, B_114), '#skF_2'(A_113, B_114)), A_113) | B_114=A_113 | ~v1_relat_1(B_114) | ~v1_relat_1(A_113))), inference(resolution, [status(thm)], [c_337, c_38])).
% 13.32/5.75  tff(c_26599, plain, (r2_hidden('#skF_3'('#skF_11', '#skF_12'), k1_relat_1('#skF_11')) | ~v1_funct_1('#skF_11') | '#skF_11'='#skF_12' | ~v1_relat_1('#skF_12') | ~v1_relat_1('#skF_11')), inference(resolution, [status(thm)], [c_26491, c_349])).
% 13.32/5.75  tff(c_26616, plain, (r2_hidden('#skF_3'('#skF_11', '#skF_12'), '#skF_9') | '#skF_11'='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_52, c_54, c_46, c_26599])).
% 13.32/5.75  tff(c_26618, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_18923, c_26616])).
% 13.32/5.75  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.32/5.75  
% 13.32/5.75  Inference rules
% 13.32/5.75  ----------------------
% 13.32/5.75  #Ref     : 26
% 13.32/5.75  #Sup     : 5562
% 13.32/5.75  #Fact    : 0
% 13.32/5.75  #Define  : 0
% 13.32/5.75  #Split   : 41
% 13.32/5.75  #Chain   : 0
% 13.32/5.75  #Close   : 0
% 13.32/5.75  
% 13.32/5.75  Ordering : KBO
% 13.32/5.75  
% 13.32/5.75  Simplification rules
% 13.32/5.75  ----------------------
% 13.32/5.75  #Subsume      : 928
% 13.32/5.75  #Demod        : 11910
% 13.32/5.75  #Tautology    : 1847
% 13.32/5.75  #SimpNegUnit  : 99
% 13.32/5.75  #BackRed      : 444
% 13.32/5.75  
% 13.32/5.75  #Partial instantiations: 0
% 13.32/5.75  #Strategies tried      : 1
% 13.32/5.75  
% 13.32/5.75  Timing (in seconds)
% 13.32/5.75  ----------------------
% 13.32/5.76  Preprocessing        : 0.32
% 13.32/5.76  Parsing              : 0.16
% 13.32/5.76  CNF conversion       : 0.03
% 13.32/5.76  Main loop            : 4.61
% 13.32/5.76  Inferencing          : 1.54
% 13.32/5.76  Reduction            : 1.70
% 13.32/5.76  Demodulation         : 1.28
% 13.32/5.76  BG Simplification    : 0.18
% 13.32/5.76  Subsumption          : 0.92
% 13.32/5.76  Abstraction          : 0.24
% 13.32/5.76  MUC search           : 0.00
% 13.32/5.76  Cooper               : 0.00
% 13.32/5.76  Total                : 4.98
% 13.32/5.76  Index Insertion      : 0.00
% 13.32/5.76  Index Deletion       : 0.00
% 13.32/5.76  Index Matching       : 0.00
% 13.32/5.76  BG Taut test         : 0.00
%------------------------------------------------------------------------------
