%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:50 EST 2020

% Result     : Theorem 5.47s
% Output     : CNFRefutation 5.90s
% Verified   : 
% Statistics : Number of formulae       :  160 (1706 expanded)
%              Number of leaves         :   23 ( 594 expanded)
%              Depth                    :   26
%              Number of atoms          :  384 (6795 expanded)
%              Number of equality atoms :  141 (2377 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > v1_funct_1 > k4_tarski > k1_funct_1 > #nlpp > k1_relat_1 > #skF_6 > #skF_3 > #skF_10 > #skF_9 > #skF_2 > #skF_8 > #skF_7 > #skF_1 > #skF_5 > #skF_4

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

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_74,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ! [B] :
            ( ( v1_relat_1(B)
              & v1_funct_1(B) )
           => ( ( k1_relat_1(A) = k1_relat_1(B)
                & ! [C] :
                    ( r2_hidden(C,k1_relat_1(A))
                   => k1_funct_1(A,C) = k1_funct_1(B,C) ) )
             => A = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_funct_1)).

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

tff(f_45,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

tff(c_44,plain,(
    v1_relat_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_42,plain,(
    v1_funct_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_32,plain,(
    '#skF_10' != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_40,plain,(
    v1_relat_1('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_38,plain,(
    v1_funct_1('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_36,plain,(
    k1_relat_1('#skF_10') = k1_relat_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_335,plain,(
    ! [A_80,B_81] :
      ( r2_hidden(k4_tarski('#skF_1'(A_80,B_81),'#skF_2'(A_80,B_81)),B_81)
      | r2_hidden(k4_tarski('#skF_3'(A_80,B_81),'#skF_4'(A_80,B_81)),A_80)
      | B_81 = A_80
      | ~ v1_relat_1(B_81)
      | ~ v1_relat_1(A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_16,plain,(
    ! [C_33,A_18,D_36] :
      ( r2_hidden(C_33,k1_relat_1(A_18))
      | ~ r2_hidden(k4_tarski(C_33,D_36),A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_651,plain,(
    ! [A_91,B_92] :
      ( r2_hidden('#skF_3'(A_91,B_92),k1_relat_1(A_91))
      | r2_hidden(k4_tarski('#skF_1'(A_91,B_92),'#skF_2'(A_91,B_92)),B_92)
      | B_92 = A_91
      | ~ v1_relat_1(B_92)
      | ~ v1_relat_1(A_91) ) ),
    inference(resolution,[status(thm)],[c_335,c_16])).

tff(c_697,plain,(
    ! [A_95,B_96] :
      ( r2_hidden('#skF_1'(A_95,B_96),k1_relat_1(B_96))
      | r2_hidden('#skF_3'(A_95,B_96),k1_relat_1(A_95))
      | B_96 = A_95
      | ~ v1_relat_1(B_96)
      | ~ v1_relat_1(A_95) ) ),
    inference(resolution,[status(thm)],[c_651,c_16])).

tff(c_717,plain,(
    ! [B_96] :
      ( r2_hidden('#skF_1'('#skF_10',B_96),k1_relat_1(B_96))
      | r2_hidden('#skF_3'('#skF_10',B_96),k1_relat_1('#skF_9'))
      | B_96 = '#skF_10'
      | ~ v1_relat_1(B_96)
      | ~ v1_relat_1('#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_697])).

tff(c_728,plain,(
    ! [B_97] :
      ( r2_hidden('#skF_1'('#skF_10',B_97),k1_relat_1(B_97))
      | r2_hidden('#skF_3'('#skF_10',B_97),k1_relat_1('#skF_9'))
      | B_97 = '#skF_10'
      | ~ v1_relat_1(B_97) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_717])).

tff(c_34,plain,(
    ! [C_44] :
      ( k1_funct_1('#skF_10',C_44) = k1_funct_1('#skF_9',C_44)
      | ~ r2_hidden(C_44,k1_relat_1('#skF_9')) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_847,plain,(
    ! [B_101] :
      ( k1_funct_1('#skF_10','#skF_3'('#skF_10',B_101)) = k1_funct_1('#skF_9','#skF_3'('#skF_10',B_101))
      | r2_hidden('#skF_1'('#skF_10',B_101),k1_relat_1(B_101))
      | B_101 = '#skF_10'
      | ~ v1_relat_1(B_101) ) ),
    inference(resolution,[status(thm)],[c_728,c_34])).

tff(c_857,plain,
    ( k1_funct_1('#skF_10','#skF_1'('#skF_10','#skF_9')) = k1_funct_1('#skF_9','#skF_1'('#skF_10','#skF_9'))
    | k1_funct_1('#skF_10','#skF_3'('#skF_10','#skF_9')) = k1_funct_1('#skF_9','#skF_3'('#skF_10','#skF_9'))
    | '#skF_10' = '#skF_9'
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_847,c_34])).

tff(c_868,plain,
    ( k1_funct_1('#skF_10','#skF_1'('#skF_10','#skF_9')) = k1_funct_1('#skF_9','#skF_1'('#skF_10','#skF_9'))
    | k1_funct_1('#skF_10','#skF_3'('#skF_10','#skF_9')) = k1_funct_1('#skF_9','#skF_3'('#skF_10','#skF_9'))
    | '#skF_10' = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_857])).

tff(c_869,plain,
    ( k1_funct_1('#skF_10','#skF_1'('#skF_10','#skF_9')) = k1_funct_1('#skF_9','#skF_1'('#skF_10','#skF_9'))
    | k1_funct_1('#skF_10','#skF_3'('#skF_10','#skF_9')) = k1_funct_1('#skF_9','#skF_3'('#skF_10','#skF_9')) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_868])).

tff(c_873,plain,(
    k1_funct_1('#skF_10','#skF_3'('#skF_10','#skF_9')) = k1_funct_1('#skF_9','#skF_3'('#skF_10','#skF_9')) ),
    inference(splitLeft,[status(thm)],[c_869])).

tff(c_26,plain,(
    ! [A_37,C_39] :
      ( r2_hidden(k4_tarski(A_37,k1_funct_1(C_39,A_37)),C_39)
      | ~ r2_hidden(A_37,k1_relat_1(C_39))
      | ~ v1_funct_1(C_39)
      | ~ v1_relat_1(C_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_878,plain,
    ( r2_hidden(k4_tarski('#skF_3'('#skF_10','#skF_9'),k1_funct_1('#skF_9','#skF_3'('#skF_10','#skF_9'))),'#skF_10')
    | ~ r2_hidden('#skF_3'('#skF_10','#skF_9'),k1_relat_1('#skF_10'))
    | ~ v1_funct_1('#skF_10')
    | ~ v1_relat_1('#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_873,c_26])).

tff(c_882,plain,
    ( r2_hidden(k4_tarski('#skF_3'('#skF_10','#skF_9'),k1_funct_1('#skF_9','#skF_3'('#skF_10','#skF_9'))),'#skF_10')
    | ~ r2_hidden('#skF_3'('#skF_10','#skF_9'),k1_relat_1('#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_36,c_878])).

tff(c_885,plain,(
    ~ r2_hidden('#skF_3'('#skF_10','#skF_9'),k1_relat_1('#skF_9')) ),
    inference(splitLeft,[status(thm)],[c_882])).

tff(c_727,plain,(
    ! [B_96] :
      ( r2_hidden('#skF_1'('#skF_10',B_96),k1_relat_1(B_96))
      | r2_hidden('#skF_3'('#skF_10',B_96),k1_relat_1('#skF_9'))
      | B_96 = '#skF_10'
      | ~ v1_relat_1(B_96) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_717])).

tff(c_888,plain,
    ( r2_hidden('#skF_1'('#skF_10','#skF_9'),k1_relat_1('#skF_9'))
    | '#skF_10' = '#skF_9'
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_727,c_885])).

tff(c_891,plain,
    ( r2_hidden('#skF_1'('#skF_10','#skF_9'),k1_relat_1('#skF_9'))
    | '#skF_10' = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_888])).

tff(c_892,plain,(
    r2_hidden('#skF_1'('#skF_10','#skF_9'),k1_relat_1('#skF_9')) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_891])).

tff(c_28,plain,(
    ! [C_39,A_37,B_38] :
      ( k1_funct_1(C_39,A_37) = B_38
      | ~ r2_hidden(k4_tarski(A_37,B_38),C_39)
      | ~ v1_funct_1(C_39)
      | ~ v1_relat_1(C_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1211,plain,(
    ! [B_114,A_115] :
      ( k1_funct_1(B_114,'#skF_1'(A_115,B_114)) = '#skF_2'(A_115,B_114)
      | ~ v1_funct_1(B_114)
      | r2_hidden('#skF_3'(A_115,B_114),k1_relat_1(A_115))
      | B_114 = A_115
      | ~ v1_relat_1(B_114)
      | ~ v1_relat_1(A_115) ) ),
    inference(resolution,[status(thm)],[c_651,c_28])).

tff(c_1240,plain,(
    ! [B_114] :
      ( k1_funct_1(B_114,'#skF_1'('#skF_10',B_114)) = '#skF_2'('#skF_10',B_114)
      | ~ v1_funct_1(B_114)
      | r2_hidden('#skF_3'('#skF_10',B_114),k1_relat_1('#skF_9'))
      | B_114 = '#skF_10'
      | ~ v1_relat_1(B_114)
      | ~ v1_relat_1('#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_1211])).

tff(c_1252,plain,(
    ! [B_116] :
      ( k1_funct_1(B_116,'#skF_1'('#skF_10',B_116)) = '#skF_2'('#skF_10',B_116)
      | ~ v1_funct_1(B_116)
      | r2_hidden('#skF_3'('#skF_10',B_116),k1_relat_1('#skF_9'))
      | B_116 = '#skF_10'
      | ~ v1_relat_1(B_116) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_1240])).

tff(c_1267,plain,
    ( k1_funct_1('#skF_9','#skF_1'('#skF_10','#skF_9')) = '#skF_2'('#skF_10','#skF_9')
    | ~ v1_funct_1('#skF_9')
    | '#skF_10' = '#skF_9'
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_1252,c_885])).

tff(c_1290,plain,
    ( k1_funct_1('#skF_9','#skF_1'('#skF_10','#skF_9')) = '#skF_2'('#skF_10','#skF_9')
    | '#skF_10' = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_1267])).

tff(c_1291,plain,(
    k1_funct_1('#skF_9','#skF_1'('#skF_10','#skF_9')) = '#skF_2'('#skF_10','#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_1290])).

tff(c_905,plain,(
    k1_funct_1('#skF_10','#skF_1'('#skF_10','#skF_9')) = k1_funct_1('#skF_9','#skF_1'('#skF_10','#skF_9')) ),
    inference(resolution,[status(thm)],[c_892,c_34])).

tff(c_1305,plain,(
    k1_funct_1('#skF_10','#skF_1'('#skF_10','#skF_9')) = '#skF_2'('#skF_10','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1291,c_905])).

tff(c_1322,plain,
    ( r2_hidden(k4_tarski('#skF_1'('#skF_10','#skF_9'),'#skF_2'('#skF_10','#skF_9')),'#skF_10')
    | ~ r2_hidden('#skF_1'('#skF_10','#skF_9'),k1_relat_1('#skF_10'))
    | ~ v1_funct_1('#skF_10')
    | ~ v1_relat_1('#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_1305,c_26])).

tff(c_1326,plain,(
    r2_hidden(k4_tarski('#skF_1'('#skF_10','#skF_9'),'#skF_2'('#skF_10','#skF_9')),'#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_892,c_36,c_1322])).

tff(c_674,plain,(
    ! [A_93,B_94] :
      ( ~ r2_hidden(k4_tarski('#skF_1'(A_93,B_94),'#skF_2'(A_93,B_94)),A_93)
      | r2_hidden(k4_tarski('#skF_3'(A_93,B_94),'#skF_4'(A_93,B_94)),A_93)
      | B_94 = A_93
      | ~ v1_relat_1(B_94)
      | ~ v1_relat_1(A_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_696,plain,(
    ! [A_93,B_94] :
      ( r2_hidden('#skF_3'(A_93,B_94),k1_relat_1(A_93))
      | ~ r2_hidden(k4_tarski('#skF_1'(A_93,B_94),'#skF_2'(A_93,B_94)),A_93)
      | B_94 = A_93
      | ~ v1_relat_1(B_94)
      | ~ v1_relat_1(A_93) ) ),
    inference(resolution,[status(thm)],[c_674,c_16])).

tff(c_1371,plain,
    ( r2_hidden('#skF_3'('#skF_10','#skF_9'),k1_relat_1('#skF_10'))
    | '#skF_10' = '#skF_9'
    | ~ v1_relat_1('#skF_9')
    | ~ v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_1326,c_696])).

tff(c_1382,plain,
    ( r2_hidden('#skF_3'('#skF_10','#skF_9'),k1_relat_1('#skF_9'))
    | '#skF_10' = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_44,c_36,c_1371])).

tff(c_1384,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_885,c_1382])).

tff(c_1386,plain,(
    r2_hidden('#skF_3'('#skF_10','#skF_9'),k1_relat_1('#skF_9')) ),
    inference(splitRight,[status(thm)],[c_882])).

tff(c_2421,plain,(
    ! [A_150,B_151] :
      ( k1_funct_1(A_150,'#skF_3'(A_150,B_151)) = '#skF_4'(A_150,B_151)
      | ~ v1_funct_1(A_150)
      | r2_hidden(k4_tarski('#skF_1'(A_150,B_151),'#skF_2'(A_150,B_151)),B_151)
      | B_151 = A_150
      | ~ v1_relat_1(B_151)
      | ~ v1_relat_1(A_150) ) ),
    inference(resolution,[status(thm)],[c_335,c_28])).

tff(c_2592,plain,(
    ! [B_158,A_159] :
      ( k1_funct_1(B_158,'#skF_1'(A_159,B_158)) = '#skF_2'(A_159,B_158)
      | ~ v1_funct_1(B_158)
      | k1_funct_1(A_159,'#skF_3'(A_159,B_158)) = '#skF_4'(A_159,B_158)
      | ~ v1_funct_1(A_159)
      | B_158 = A_159
      | ~ v1_relat_1(B_158)
      | ~ v1_relat_1(A_159) ) ),
    inference(resolution,[status(thm)],[c_2421,c_28])).

tff(c_2647,plain,
    ( k1_funct_1('#skF_9','#skF_3'('#skF_10','#skF_9')) = '#skF_4'('#skF_10','#skF_9')
    | k1_funct_1('#skF_9','#skF_1'('#skF_10','#skF_9')) = '#skF_2'('#skF_10','#skF_9')
    | ~ v1_funct_1('#skF_9')
    | ~ v1_funct_1('#skF_10')
    | '#skF_10' = '#skF_9'
    | ~ v1_relat_1('#skF_9')
    | ~ v1_relat_1('#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_2592,c_873])).

tff(c_2723,plain,
    ( k1_funct_1('#skF_9','#skF_3'('#skF_10','#skF_9')) = '#skF_4'('#skF_10','#skF_9')
    | k1_funct_1('#skF_9','#skF_1'('#skF_10','#skF_9')) = '#skF_2'('#skF_10','#skF_9')
    | '#skF_10' = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_44,c_38,c_42,c_2647])).

tff(c_2724,plain,
    ( k1_funct_1('#skF_9','#skF_3'('#skF_10','#skF_9')) = '#skF_4'('#skF_10','#skF_9')
    | k1_funct_1('#skF_9','#skF_1'('#skF_10','#skF_9')) = '#skF_2'('#skF_10','#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_2723])).

tff(c_3125,plain,(
    k1_funct_1('#skF_9','#skF_1'('#skF_10','#skF_9')) = '#skF_2'('#skF_10','#skF_9') ),
    inference(splitLeft,[status(thm)],[c_2724])).

tff(c_1457,plain,(
    ! [A_121,B_122] :
      ( r2_hidden('#skF_1'(A_121,B_122),k1_relat_1(B_122))
      | r2_hidden(k4_tarski('#skF_3'(A_121,B_122),'#skF_4'(A_121,B_122)),A_121)
      | B_122 = A_121
      | ~ v1_relat_1(B_122)
      | ~ v1_relat_1(A_121) ) ),
    inference(resolution,[status(thm)],[c_335,c_16])).

tff(c_1577,plain,(
    ! [A_128,B_129] :
      ( k1_funct_1(A_128,'#skF_3'(A_128,B_129)) = '#skF_4'(A_128,B_129)
      | ~ v1_funct_1(A_128)
      | r2_hidden('#skF_1'(A_128,B_129),k1_relat_1(B_129))
      | B_129 = A_128
      | ~ v1_relat_1(B_129)
      | ~ v1_relat_1(A_128) ) ),
    inference(resolution,[status(thm)],[c_1457,c_28])).

tff(c_1594,plain,(
    ! [A_128] :
      ( k1_funct_1('#skF_10','#skF_1'(A_128,'#skF_9')) = k1_funct_1('#skF_9','#skF_1'(A_128,'#skF_9'))
      | k1_funct_1(A_128,'#skF_3'(A_128,'#skF_9')) = '#skF_4'(A_128,'#skF_9')
      | ~ v1_funct_1(A_128)
      | A_128 = '#skF_9'
      | ~ v1_relat_1('#skF_9')
      | ~ v1_relat_1(A_128) ) ),
    inference(resolution,[status(thm)],[c_1577,c_34])).

tff(c_2003,plain,(
    ! [A_143] :
      ( k1_funct_1('#skF_10','#skF_1'(A_143,'#skF_9')) = k1_funct_1('#skF_9','#skF_1'(A_143,'#skF_9'))
      | k1_funct_1(A_143,'#skF_3'(A_143,'#skF_9')) = '#skF_4'(A_143,'#skF_9')
      | ~ v1_funct_1(A_143)
      | A_143 = '#skF_9'
      | ~ v1_relat_1(A_143) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_1594])).

tff(c_2018,plain,
    ( k1_funct_1('#skF_9','#skF_3'('#skF_10','#skF_9')) = '#skF_4'('#skF_10','#skF_9')
    | k1_funct_1('#skF_10','#skF_1'('#skF_10','#skF_9')) = k1_funct_1('#skF_9','#skF_1'('#skF_10','#skF_9'))
    | ~ v1_funct_1('#skF_10')
    | '#skF_10' = '#skF_9'
    | ~ v1_relat_1('#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_2003,c_873])).

tff(c_2043,plain,
    ( k1_funct_1('#skF_9','#skF_3'('#skF_10','#skF_9')) = '#skF_4'('#skF_10','#skF_9')
    | k1_funct_1('#skF_10','#skF_1'('#skF_10','#skF_9')) = k1_funct_1('#skF_9','#skF_1'('#skF_10','#skF_9'))
    | '#skF_10' = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_2018])).

tff(c_2044,plain,
    ( k1_funct_1('#skF_9','#skF_3'('#skF_10','#skF_9')) = '#skF_4'('#skF_10','#skF_9')
    | k1_funct_1('#skF_10','#skF_1'('#skF_10','#skF_9')) = k1_funct_1('#skF_9','#skF_1'('#skF_10','#skF_9')) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_2043])).

tff(c_2053,plain,(
    k1_funct_1('#skF_10','#skF_1'('#skF_10','#skF_9')) = k1_funct_1('#skF_9','#skF_1'('#skF_10','#skF_9')) ),
    inference(splitLeft,[status(thm)],[c_2044])).

tff(c_2058,plain,
    ( r2_hidden(k4_tarski('#skF_1'('#skF_10','#skF_9'),k1_funct_1('#skF_9','#skF_1'('#skF_10','#skF_9'))),'#skF_10')
    | ~ r2_hidden('#skF_1'('#skF_10','#skF_9'),k1_relat_1('#skF_10'))
    | ~ v1_funct_1('#skF_10')
    | ~ v1_relat_1('#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_2053,c_26])).

tff(c_2063,plain,
    ( r2_hidden(k4_tarski('#skF_1'('#skF_10','#skF_9'),k1_funct_1('#skF_9','#skF_1'('#skF_10','#skF_9'))),'#skF_10')
    | ~ r2_hidden('#skF_1'('#skF_10','#skF_9'),k1_relat_1('#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_36,c_2058])).

tff(c_2074,plain,(
    ~ r2_hidden('#skF_1'('#skF_10','#skF_9'),k1_relat_1('#skF_9')) ),
    inference(splitLeft,[status(thm)],[c_2063])).

tff(c_1483,plain,(
    ! [A_121,B_122] :
      ( k1_funct_1(A_121,'#skF_3'(A_121,B_122)) = '#skF_4'(A_121,B_122)
      | ~ v1_funct_1(A_121)
      | r2_hidden('#skF_1'(A_121,B_122),k1_relat_1(B_122))
      | B_122 = A_121
      | ~ v1_relat_1(B_122)
      | ~ v1_relat_1(A_121) ) ),
    inference(resolution,[status(thm)],[c_1457,c_28])).

tff(c_2083,plain,
    ( k1_funct_1('#skF_10','#skF_3'('#skF_10','#skF_9')) = '#skF_4'('#skF_10','#skF_9')
    | ~ v1_funct_1('#skF_10')
    | '#skF_10' = '#skF_9'
    | ~ v1_relat_1('#skF_9')
    | ~ v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_1483,c_2074])).

tff(c_2099,plain,
    ( k1_funct_1('#skF_9','#skF_3'('#skF_10','#skF_9')) = '#skF_4'('#skF_10','#skF_9')
    | '#skF_10' = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_44,c_38,c_873,c_2083])).

tff(c_2100,plain,(
    k1_funct_1('#skF_9','#skF_3'('#skF_10','#skF_9')) = '#skF_4'('#skF_10','#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_2099])).

tff(c_59,plain,(
    ! [C_55,A_56] :
      ( r2_hidden(k4_tarski(C_55,'#skF_8'(A_56,k1_relat_1(A_56),C_55)),A_56)
      | ~ r2_hidden(C_55,k1_relat_1(A_56)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_73,plain,(
    ! [A_56,C_55] :
      ( '#skF_8'(A_56,k1_relat_1(A_56),C_55) = k1_funct_1(A_56,C_55)
      | ~ v1_funct_1(A_56)
      | ~ v1_relat_1(A_56)
      | ~ r2_hidden(C_55,k1_relat_1(A_56)) ) ),
    inference(resolution,[status(thm)],[c_59,c_28])).

tff(c_1388,plain,
    ( '#skF_8'('#skF_9',k1_relat_1('#skF_9'),'#skF_3'('#skF_10','#skF_9')) = k1_funct_1('#skF_9','#skF_3'('#skF_10','#skF_9'))
    | ~ v1_funct_1('#skF_9')
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_1386,c_73])).

tff(c_1397,plain,(
    '#skF_8'('#skF_9',k1_relat_1('#skF_9'),'#skF_3'('#skF_10','#skF_9')) = k1_funct_1('#skF_9','#skF_3'('#skF_10','#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_1388])).

tff(c_14,plain,(
    ! [C_33,A_18] :
      ( r2_hidden(k4_tarski(C_33,'#skF_8'(A_18,k1_relat_1(A_18),C_33)),A_18)
      | ~ r2_hidden(C_33,k1_relat_1(A_18)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1417,plain,
    ( r2_hidden(k4_tarski('#skF_3'('#skF_10','#skF_9'),k1_funct_1('#skF_9','#skF_3'('#skF_10','#skF_9'))),'#skF_9')
    | ~ r2_hidden('#skF_3'('#skF_10','#skF_9'),k1_relat_1('#skF_9')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1397,c_14])).

tff(c_1421,plain,(
    r2_hidden(k4_tarski('#skF_3'('#skF_10','#skF_9'),k1_funct_1('#skF_9','#skF_3'('#skF_10','#skF_9'))),'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1386,c_1417])).

tff(c_2106,plain,(
    r2_hidden(k4_tarski('#skF_3'('#skF_10','#skF_9'),'#skF_4'('#skF_10','#skF_9')),'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2100,c_1421])).

tff(c_4,plain,(
    ! [A_1,B_11] :
      ( r2_hidden(k4_tarski('#skF_1'(A_1,B_11),'#skF_2'(A_1,B_11)),B_11)
      | ~ r2_hidden(k4_tarski('#skF_3'(A_1,B_11),'#skF_4'(A_1,B_11)),B_11)
      | B_11 = A_1
      | ~ v1_relat_1(B_11)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2158,plain,
    ( r2_hidden(k4_tarski('#skF_1'('#skF_10','#skF_9'),'#skF_2'('#skF_10','#skF_9')),'#skF_9')
    | '#skF_10' = '#skF_9'
    | ~ v1_relat_1('#skF_9')
    | ~ v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_2106,c_4])).

tff(c_2167,plain,
    ( r2_hidden(k4_tarski('#skF_1'('#skF_10','#skF_9'),'#skF_2'('#skF_10','#skF_9')),'#skF_9')
    | '#skF_10' = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_44,c_2158])).

tff(c_2168,plain,(
    r2_hidden(k4_tarski('#skF_1'('#skF_10','#skF_9'),'#skF_2'('#skF_10','#skF_9')),'#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_2167])).

tff(c_2220,plain,(
    r2_hidden('#skF_1'('#skF_10','#skF_9'),k1_relat_1('#skF_9')) ),
    inference(resolution,[status(thm)],[c_2168,c_16])).

tff(c_2227,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2074,c_2220])).

tff(c_2228,plain,(
    r2_hidden(k4_tarski('#skF_1'('#skF_10','#skF_9'),k1_funct_1('#skF_9','#skF_1'('#skF_10','#skF_9'))),'#skF_10') ),
    inference(splitRight,[status(thm)],[c_2063])).

tff(c_3129,plain,(
    r2_hidden(k4_tarski('#skF_1'('#skF_10','#skF_9'),'#skF_2'('#skF_10','#skF_9')),'#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3125,c_2228])).

tff(c_2,plain,(
    ! [A_1,B_11] :
      ( ~ r2_hidden(k4_tarski('#skF_1'(A_1,B_11),'#skF_2'(A_1,B_11)),A_1)
      | ~ r2_hidden(k4_tarski('#skF_3'(A_1,B_11),'#skF_4'(A_1,B_11)),B_11)
      | B_11 = A_1
      | ~ v1_relat_1(B_11)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_3216,plain,
    ( ~ r2_hidden(k4_tarski('#skF_3'('#skF_10','#skF_9'),'#skF_4'('#skF_10','#skF_9')),'#skF_9')
    | '#skF_10' = '#skF_9'
    | ~ v1_relat_1('#skF_9')
    | ~ v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_3129,c_2])).

tff(c_3233,plain,
    ( ~ r2_hidden(k4_tarski('#skF_3'('#skF_10','#skF_9'),'#skF_4'('#skF_10','#skF_9')),'#skF_9')
    | '#skF_10' = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_44,c_3216])).

tff(c_3234,plain,(
    ~ r2_hidden(k4_tarski('#skF_3'('#skF_10','#skF_9'),'#skF_4'('#skF_10','#skF_9')),'#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_3233])).

tff(c_694,plain,(
    ! [A_93,B_94] :
      ( k1_funct_1(A_93,'#skF_3'(A_93,B_94)) = '#skF_4'(A_93,B_94)
      | ~ v1_funct_1(A_93)
      | ~ r2_hidden(k4_tarski('#skF_1'(A_93,B_94),'#skF_2'(A_93,B_94)),A_93)
      | B_94 = A_93
      | ~ v1_relat_1(B_94)
      | ~ v1_relat_1(A_93) ) ),
    inference(resolution,[status(thm)],[c_674,c_28])).

tff(c_3211,plain,
    ( k1_funct_1('#skF_10','#skF_3'('#skF_10','#skF_9')) = '#skF_4'('#skF_10','#skF_9')
    | ~ v1_funct_1('#skF_10')
    | '#skF_10' = '#skF_9'
    | ~ v1_relat_1('#skF_9')
    | ~ v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_3129,c_694])).

tff(c_3225,plain,
    ( k1_funct_1('#skF_9','#skF_3'('#skF_10','#skF_9')) = '#skF_4'('#skF_10','#skF_9')
    | '#skF_10' = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_44,c_38,c_873,c_3211])).

tff(c_3226,plain,(
    k1_funct_1('#skF_9','#skF_3'('#skF_10','#skF_9')) = '#skF_4'('#skF_10','#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_3225])).

tff(c_3241,plain,(
    r2_hidden(k4_tarski('#skF_3'('#skF_10','#skF_9'),'#skF_4'('#skF_10','#skF_9')),'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3226,c_1421])).

tff(c_3317,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3234,c_3241])).

tff(c_3319,plain,(
    k1_funct_1('#skF_9','#skF_1'('#skF_10','#skF_9')) != '#skF_2'('#skF_10','#skF_9') ),
    inference(splitRight,[status(thm)],[c_2724])).

tff(c_3318,plain,(
    k1_funct_1('#skF_9','#skF_3'('#skF_10','#skF_9')) = '#skF_4'('#skF_10','#skF_9') ),
    inference(splitRight,[status(thm)],[c_2724])).

tff(c_3328,plain,
    ( r2_hidden(k4_tarski('#skF_3'('#skF_10','#skF_9'),'#skF_4'('#skF_10','#skF_9')),'#skF_9')
    | ~ r2_hidden('#skF_3'('#skF_10','#skF_9'),k1_relat_1('#skF_9'))
    | ~ v1_funct_1('#skF_9')
    | ~ v1_relat_1('#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_3318,c_26])).

tff(c_3332,plain,(
    r2_hidden(k4_tarski('#skF_3'('#skF_10','#skF_9'),'#skF_4'('#skF_10','#skF_9')),'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_1386,c_3328])).

tff(c_3443,plain,
    ( r2_hidden(k4_tarski('#skF_1'('#skF_10','#skF_9'),'#skF_2'('#skF_10','#skF_9')),'#skF_9')
    | '#skF_10' = '#skF_9'
    | ~ v1_relat_1('#skF_9')
    | ~ v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_3332,c_4])).

tff(c_3452,plain,
    ( r2_hidden(k4_tarski('#skF_1'('#skF_10','#skF_9'),'#skF_2'('#skF_10','#skF_9')),'#skF_9')
    | '#skF_10' = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_44,c_3443])).

tff(c_3453,plain,(
    r2_hidden(k4_tarski('#skF_1'('#skF_10','#skF_9'),'#skF_2'('#skF_10','#skF_9')),'#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_3452])).

tff(c_3462,plain,
    ( k1_funct_1('#skF_9','#skF_1'('#skF_10','#skF_9')) = '#skF_2'('#skF_10','#skF_9')
    | ~ v1_funct_1('#skF_9')
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_3453,c_28])).

tff(c_3468,plain,(
    k1_funct_1('#skF_9','#skF_1'('#skF_10','#skF_9')) = '#skF_2'('#skF_10','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_3462])).

tff(c_3470,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3319,c_3468])).

tff(c_3471,plain,(
    k1_funct_1('#skF_9','#skF_3'('#skF_10','#skF_9')) = '#skF_4'('#skF_10','#skF_9') ),
    inference(splitRight,[status(thm)],[c_2044])).

tff(c_3481,plain,
    ( r2_hidden(k4_tarski('#skF_3'('#skF_10','#skF_9'),'#skF_4'('#skF_10','#skF_9')),'#skF_9')
    | ~ r2_hidden('#skF_3'('#skF_10','#skF_9'),k1_relat_1('#skF_9'))
    | ~ v1_funct_1('#skF_9')
    | ~ v1_relat_1('#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_3471,c_26])).

tff(c_3485,plain,(
    r2_hidden(k4_tarski('#skF_3'('#skF_10','#skF_9'),'#skF_4'('#skF_10','#skF_9')),'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_1386,c_3481])).

tff(c_3535,plain,
    ( r2_hidden(k4_tarski('#skF_1'('#skF_10','#skF_9'),'#skF_2'('#skF_10','#skF_9')),'#skF_9')
    | '#skF_10' = '#skF_9'
    | ~ v1_relat_1('#skF_9')
    | ~ v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_3485,c_4])).

tff(c_3544,plain,
    ( r2_hidden(k4_tarski('#skF_1'('#skF_10','#skF_9'),'#skF_2'('#skF_10','#skF_9')),'#skF_9')
    | '#skF_10' = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_44,c_3535])).

tff(c_3545,plain,(
    r2_hidden(k4_tarski('#skF_1'('#skF_10','#skF_9'),'#skF_2'('#skF_10','#skF_9')),'#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_3544])).

tff(c_3553,plain,
    ( k1_funct_1('#skF_9','#skF_1'('#skF_10','#skF_9')) = '#skF_2'('#skF_10','#skF_9')
    | ~ v1_funct_1('#skF_9')
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_3545,c_28])).

tff(c_3559,plain,(
    k1_funct_1('#skF_9','#skF_1'('#skF_10','#skF_9')) = '#skF_2'('#skF_10','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_3553])).

tff(c_3472,plain,(
    k1_funct_1('#skF_10','#skF_1'('#skF_10','#skF_9')) != k1_funct_1('#skF_9','#skF_1'('#skF_10','#skF_9')) ),
    inference(splitRight,[status(thm)],[c_2044])).

tff(c_3588,plain,(
    k1_funct_1('#skF_10','#skF_1'('#skF_10','#skF_9')) != '#skF_2'('#skF_10','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3559,c_3472])).

tff(c_3560,plain,(
    r2_hidden('#skF_1'('#skF_10','#skF_9'),k1_relat_1('#skF_9')) ),
    inference(resolution,[status(thm)],[c_3545,c_16])).

tff(c_3573,plain,(
    k1_funct_1('#skF_10','#skF_1'('#skF_10','#skF_9')) = k1_funct_1('#skF_9','#skF_1'('#skF_10','#skF_9')) ),
    inference(resolution,[status(thm)],[c_3560,c_34])).

tff(c_3647,plain,(
    k1_funct_1('#skF_10','#skF_1'('#skF_10','#skF_9')) = '#skF_2'('#skF_10','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3559,c_3573])).

tff(c_3648,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3588,c_3647])).

tff(c_3650,plain,(
    k1_funct_1('#skF_10','#skF_3'('#skF_10','#skF_9')) != k1_funct_1('#skF_9','#skF_3'('#skF_10','#skF_9')) ),
    inference(splitRight,[status(thm)],[c_869])).

tff(c_3868,plain,(
    ! [B_174,A_175] :
      ( k1_funct_1(B_174,'#skF_1'(A_175,B_174)) = '#skF_2'(A_175,B_174)
      | ~ v1_funct_1(B_174)
      | r2_hidden('#skF_3'(A_175,B_174),k1_relat_1(A_175))
      | B_174 = A_175
      | ~ v1_relat_1(B_174)
      | ~ v1_relat_1(A_175) ) ),
    inference(resolution,[status(thm)],[c_651,c_28])).

tff(c_3894,plain,(
    ! [B_174] :
      ( k1_funct_1(B_174,'#skF_1'('#skF_10',B_174)) = '#skF_2'('#skF_10',B_174)
      | ~ v1_funct_1(B_174)
      | r2_hidden('#skF_3'('#skF_10',B_174),k1_relat_1('#skF_9'))
      | B_174 = '#skF_10'
      | ~ v1_relat_1(B_174)
      | ~ v1_relat_1('#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_3868])).

tff(c_3906,plain,(
    ! [B_176] :
      ( k1_funct_1(B_176,'#skF_1'('#skF_10',B_176)) = '#skF_2'('#skF_10',B_176)
      | ~ v1_funct_1(B_176)
      | r2_hidden('#skF_3'('#skF_10',B_176),k1_relat_1('#skF_9'))
      | B_176 = '#skF_10'
      | ~ v1_relat_1(B_176) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_3894])).

tff(c_4169,plain,(
    ! [B_187] :
      ( k1_funct_1('#skF_10','#skF_3'('#skF_10',B_187)) = k1_funct_1('#skF_9','#skF_3'('#skF_10',B_187))
      | k1_funct_1(B_187,'#skF_1'('#skF_10',B_187)) = '#skF_2'('#skF_10',B_187)
      | ~ v1_funct_1(B_187)
      | B_187 = '#skF_10'
      | ~ v1_relat_1(B_187) ) ),
    inference(resolution,[status(thm)],[c_3906,c_34])).

tff(c_4177,plain,
    ( k1_funct_1('#skF_9','#skF_1'('#skF_10','#skF_9')) = '#skF_2'('#skF_10','#skF_9')
    | ~ v1_funct_1('#skF_9')
    | '#skF_10' = '#skF_9'
    | ~ v1_relat_1('#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_4169,c_3650])).

tff(c_4215,plain,
    ( k1_funct_1('#skF_9','#skF_1'('#skF_10','#skF_9')) = '#skF_2'('#skF_10','#skF_9')
    | '#skF_10' = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_4177])).

tff(c_4216,plain,(
    k1_funct_1('#skF_9','#skF_1'('#skF_10','#skF_9')) = '#skF_2'('#skF_10','#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_4215])).

tff(c_749,plain,(
    ! [B_97] :
      ( k1_funct_1('#skF_10','#skF_3'('#skF_10',B_97)) = k1_funct_1('#skF_9','#skF_3'('#skF_10',B_97))
      | r2_hidden('#skF_1'('#skF_10',B_97),k1_relat_1(B_97))
      | B_97 = '#skF_10'
      | ~ v1_relat_1(B_97) ) ),
    inference(resolution,[status(thm)],[c_728,c_34])).

tff(c_3649,plain,(
    k1_funct_1('#skF_10','#skF_1'('#skF_10','#skF_9')) = k1_funct_1('#skF_9','#skF_1'('#skF_10','#skF_9')) ),
    inference(splitRight,[status(thm)],[c_869])).

tff(c_3654,plain,
    ( r2_hidden(k4_tarski('#skF_1'('#skF_10','#skF_9'),k1_funct_1('#skF_9','#skF_1'('#skF_10','#skF_9'))),'#skF_10')
    | ~ r2_hidden('#skF_1'('#skF_10','#skF_9'),k1_relat_1('#skF_10'))
    | ~ v1_funct_1('#skF_10')
    | ~ v1_relat_1('#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_3649,c_26])).

tff(c_3658,plain,
    ( r2_hidden(k4_tarski('#skF_1'('#skF_10','#skF_9'),k1_funct_1('#skF_9','#skF_1'('#skF_10','#skF_9'))),'#skF_10')
    | ~ r2_hidden('#skF_1'('#skF_10','#skF_9'),k1_relat_1('#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_36,c_3654])).

tff(c_3685,plain,(
    ~ r2_hidden('#skF_1'('#skF_10','#skF_9'),k1_relat_1('#skF_9')) ),
    inference(splitLeft,[status(thm)],[c_3658])).

tff(c_3688,plain,
    ( k1_funct_1('#skF_10','#skF_3'('#skF_10','#skF_9')) = k1_funct_1('#skF_9','#skF_3'('#skF_10','#skF_9'))
    | '#skF_10' = '#skF_9'
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_749,c_3685])).

tff(c_3693,plain,
    ( k1_funct_1('#skF_10','#skF_3'('#skF_10','#skF_9')) = k1_funct_1('#skF_9','#skF_3'('#skF_10','#skF_9'))
    | '#skF_10' = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_3688])).

tff(c_3695,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_3650,c_3693])).

tff(c_3696,plain,(
    r2_hidden(k4_tarski('#skF_1'('#skF_10','#skF_9'),k1_funct_1('#skF_9','#skF_1'('#skF_10','#skF_9'))),'#skF_10') ),
    inference(splitRight,[status(thm)],[c_3658])).

tff(c_4232,plain,(
    r2_hidden(k4_tarski('#skF_1'('#skF_10','#skF_9'),'#skF_2'('#skF_10','#skF_9')),'#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4216,c_3696])).

tff(c_4264,plain,
    ( r2_hidden('#skF_3'('#skF_10','#skF_9'),k1_relat_1('#skF_10'))
    | '#skF_10' = '#skF_9'
    | ~ v1_relat_1('#skF_9')
    | ~ v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_4232,c_696])).

tff(c_4279,plain,
    ( r2_hidden('#skF_3'('#skF_10','#skF_9'),k1_relat_1('#skF_9'))
    | '#skF_10' = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_44,c_36,c_4264])).

tff(c_4280,plain,(
    r2_hidden('#skF_3'('#skF_10','#skF_9'),k1_relat_1('#skF_9')) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_4279])).

tff(c_4297,plain,(
    k1_funct_1('#skF_10','#skF_3'('#skF_10','#skF_9')) = k1_funct_1('#skF_9','#skF_3'('#skF_10','#skF_9')) ),
    inference(resolution,[status(thm)],[c_4280,c_34])).

tff(c_4305,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3650,c_4297])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:56:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.47/2.04  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.47/2.05  
% 5.47/2.05  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.47/2.05  %$ r2_hidden > v1_relat_1 > v1_funct_1 > k4_tarski > k1_funct_1 > #nlpp > k1_relat_1 > #skF_6 > #skF_3 > #skF_10 > #skF_9 > #skF_2 > #skF_8 > #skF_7 > #skF_1 > #skF_5 > #skF_4
% 5.47/2.05  
% 5.47/2.05  %Foreground sorts:
% 5.47/2.05  
% 5.47/2.05  
% 5.47/2.05  %Background operators:
% 5.47/2.05  
% 5.47/2.05  
% 5.47/2.05  %Foreground operators:
% 5.47/2.05  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 5.47/2.05  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.47/2.05  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.47/2.05  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.47/2.05  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 5.47/2.05  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 5.47/2.05  tff('#skF_10', type, '#skF_10': $i).
% 5.47/2.05  tff('#skF_9', type, '#skF_9': $i).
% 5.47/2.05  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 5.47/2.05  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.47/2.05  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.47/2.05  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.47/2.05  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 5.47/2.05  tff('#skF_8', type, '#skF_8': ($i * $i * $i) > $i).
% 5.47/2.05  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 5.47/2.05  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.47/2.05  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 5.47/2.05  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.47/2.05  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 5.47/2.05  
% 5.90/2.08  tff(f_74, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((k1_relat_1(A) = k1_relat_1(B)) & (![C]: (r2_hidden(C, k1_relat_1(A)) => (k1_funct_1(A, C) = k1_funct_1(B, C))))) => (A = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_funct_1)).
% 5.90/2.08  tff(f_37, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => ((A = B) <=> (![C, D]: (r2_hidden(k4_tarski(C, D), A) <=> r2_hidden(k4_tarski(C, D), B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_relat_1)).
% 5.90/2.08  tff(f_45, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_relat_1)).
% 5.90/2.08  tff(f_55, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_1)).
% 5.90/2.08  tff(c_44, plain, (v1_relat_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_74])).
% 5.90/2.08  tff(c_42, plain, (v1_funct_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_74])).
% 5.90/2.08  tff(c_32, plain, ('#skF_10'!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_74])).
% 5.90/2.08  tff(c_40, plain, (v1_relat_1('#skF_10')), inference(cnfTransformation, [status(thm)], [f_74])).
% 5.90/2.08  tff(c_38, plain, (v1_funct_1('#skF_10')), inference(cnfTransformation, [status(thm)], [f_74])).
% 5.90/2.08  tff(c_36, plain, (k1_relat_1('#skF_10')=k1_relat_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_74])).
% 5.90/2.08  tff(c_335, plain, (![A_80, B_81]: (r2_hidden(k4_tarski('#skF_1'(A_80, B_81), '#skF_2'(A_80, B_81)), B_81) | r2_hidden(k4_tarski('#skF_3'(A_80, B_81), '#skF_4'(A_80, B_81)), A_80) | B_81=A_80 | ~v1_relat_1(B_81) | ~v1_relat_1(A_80))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.90/2.08  tff(c_16, plain, (![C_33, A_18, D_36]: (r2_hidden(C_33, k1_relat_1(A_18)) | ~r2_hidden(k4_tarski(C_33, D_36), A_18))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.90/2.08  tff(c_651, plain, (![A_91, B_92]: (r2_hidden('#skF_3'(A_91, B_92), k1_relat_1(A_91)) | r2_hidden(k4_tarski('#skF_1'(A_91, B_92), '#skF_2'(A_91, B_92)), B_92) | B_92=A_91 | ~v1_relat_1(B_92) | ~v1_relat_1(A_91))), inference(resolution, [status(thm)], [c_335, c_16])).
% 5.90/2.08  tff(c_697, plain, (![A_95, B_96]: (r2_hidden('#skF_1'(A_95, B_96), k1_relat_1(B_96)) | r2_hidden('#skF_3'(A_95, B_96), k1_relat_1(A_95)) | B_96=A_95 | ~v1_relat_1(B_96) | ~v1_relat_1(A_95))), inference(resolution, [status(thm)], [c_651, c_16])).
% 5.90/2.08  tff(c_717, plain, (![B_96]: (r2_hidden('#skF_1'('#skF_10', B_96), k1_relat_1(B_96)) | r2_hidden('#skF_3'('#skF_10', B_96), k1_relat_1('#skF_9')) | B_96='#skF_10' | ~v1_relat_1(B_96) | ~v1_relat_1('#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_36, c_697])).
% 5.90/2.08  tff(c_728, plain, (![B_97]: (r2_hidden('#skF_1'('#skF_10', B_97), k1_relat_1(B_97)) | r2_hidden('#skF_3'('#skF_10', B_97), k1_relat_1('#skF_9')) | B_97='#skF_10' | ~v1_relat_1(B_97))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_717])).
% 5.90/2.08  tff(c_34, plain, (![C_44]: (k1_funct_1('#skF_10', C_44)=k1_funct_1('#skF_9', C_44) | ~r2_hidden(C_44, k1_relat_1('#skF_9')))), inference(cnfTransformation, [status(thm)], [f_74])).
% 5.90/2.08  tff(c_847, plain, (![B_101]: (k1_funct_1('#skF_10', '#skF_3'('#skF_10', B_101))=k1_funct_1('#skF_9', '#skF_3'('#skF_10', B_101)) | r2_hidden('#skF_1'('#skF_10', B_101), k1_relat_1(B_101)) | B_101='#skF_10' | ~v1_relat_1(B_101))), inference(resolution, [status(thm)], [c_728, c_34])).
% 5.90/2.08  tff(c_857, plain, (k1_funct_1('#skF_10', '#skF_1'('#skF_10', '#skF_9'))=k1_funct_1('#skF_9', '#skF_1'('#skF_10', '#skF_9')) | k1_funct_1('#skF_10', '#skF_3'('#skF_10', '#skF_9'))=k1_funct_1('#skF_9', '#skF_3'('#skF_10', '#skF_9')) | '#skF_10'='#skF_9' | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_847, c_34])).
% 5.90/2.08  tff(c_868, plain, (k1_funct_1('#skF_10', '#skF_1'('#skF_10', '#skF_9'))=k1_funct_1('#skF_9', '#skF_1'('#skF_10', '#skF_9')) | k1_funct_1('#skF_10', '#skF_3'('#skF_10', '#skF_9'))=k1_funct_1('#skF_9', '#skF_3'('#skF_10', '#skF_9')) | '#skF_10'='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_44, c_857])).
% 5.90/2.08  tff(c_869, plain, (k1_funct_1('#skF_10', '#skF_1'('#skF_10', '#skF_9'))=k1_funct_1('#skF_9', '#skF_1'('#skF_10', '#skF_9')) | k1_funct_1('#skF_10', '#skF_3'('#skF_10', '#skF_9'))=k1_funct_1('#skF_9', '#skF_3'('#skF_10', '#skF_9'))), inference(negUnitSimplification, [status(thm)], [c_32, c_868])).
% 5.90/2.08  tff(c_873, plain, (k1_funct_1('#skF_10', '#skF_3'('#skF_10', '#skF_9'))=k1_funct_1('#skF_9', '#skF_3'('#skF_10', '#skF_9'))), inference(splitLeft, [status(thm)], [c_869])).
% 5.90/2.08  tff(c_26, plain, (![A_37, C_39]: (r2_hidden(k4_tarski(A_37, k1_funct_1(C_39, A_37)), C_39) | ~r2_hidden(A_37, k1_relat_1(C_39)) | ~v1_funct_1(C_39) | ~v1_relat_1(C_39))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.90/2.08  tff(c_878, plain, (r2_hidden(k4_tarski('#skF_3'('#skF_10', '#skF_9'), k1_funct_1('#skF_9', '#skF_3'('#skF_10', '#skF_9'))), '#skF_10') | ~r2_hidden('#skF_3'('#skF_10', '#skF_9'), k1_relat_1('#skF_10')) | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_873, c_26])).
% 5.90/2.08  tff(c_882, plain, (r2_hidden(k4_tarski('#skF_3'('#skF_10', '#skF_9'), k1_funct_1('#skF_9', '#skF_3'('#skF_10', '#skF_9'))), '#skF_10') | ~r2_hidden('#skF_3'('#skF_10', '#skF_9'), k1_relat_1('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_36, c_878])).
% 5.90/2.08  tff(c_885, plain, (~r2_hidden('#skF_3'('#skF_10', '#skF_9'), k1_relat_1('#skF_9'))), inference(splitLeft, [status(thm)], [c_882])).
% 5.90/2.08  tff(c_727, plain, (![B_96]: (r2_hidden('#skF_1'('#skF_10', B_96), k1_relat_1(B_96)) | r2_hidden('#skF_3'('#skF_10', B_96), k1_relat_1('#skF_9')) | B_96='#skF_10' | ~v1_relat_1(B_96))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_717])).
% 5.90/2.08  tff(c_888, plain, (r2_hidden('#skF_1'('#skF_10', '#skF_9'), k1_relat_1('#skF_9')) | '#skF_10'='#skF_9' | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_727, c_885])).
% 5.90/2.08  tff(c_891, plain, (r2_hidden('#skF_1'('#skF_10', '#skF_9'), k1_relat_1('#skF_9')) | '#skF_10'='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_44, c_888])).
% 5.90/2.08  tff(c_892, plain, (r2_hidden('#skF_1'('#skF_10', '#skF_9'), k1_relat_1('#skF_9'))), inference(negUnitSimplification, [status(thm)], [c_32, c_891])).
% 5.90/2.08  tff(c_28, plain, (![C_39, A_37, B_38]: (k1_funct_1(C_39, A_37)=B_38 | ~r2_hidden(k4_tarski(A_37, B_38), C_39) | ~v1_funct_1(C_39) | ~v1_relat_1(C_39))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.90/2.08  tff(c_1211, plain, (![B_114, A_115]: (k1_funct_1(B_114, '#skF_1'(A_115, B_114))='#skF_2'(A_115, B_114) | ~v1_funct_1(B_114) | r2_hidden('#skF_3'(A_115, B_114), k1_relat_1(A_115)) | B_114=A_115 | ~v1_relat_1(B_114) | ~v1_relat_1(A_115))), inference(resolution, [status(thm)], [c_651, c_28])).
% 5.90/2.08  tff(c_1240, plain, (![B_114]: (k1_funct_1(B_114, '#skF_1'('#skF_10', B_114))='#skF_2'('#skF_10', B_114) | ~v1_funct_1(B_114) | r2_hidden('#skF_3'('#skF_10', B_114), k1_relat_1('#skF_9')) | B_114='#skF_10' | ~v1_relat_1(B_114) | ~v1_relat_1('#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_36, c_1211])).
% 5.90/2.08  tff(c_1252, plain, (![B_116]: (k1_funct_1(B_116, '#skF_1'('#skF_10', B_116))='#skF_2'('#skF_10', B_116) | ~v1_funct_1(B_116) | r2_hidden('#skF_3'('#skF_10', B_116), k1_relat_1('#skF_9')) | B_116='#skF_10' | ~v1_relat_1(B_116))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_1240])).
% 5.90/2.08  tff(c_1267, plain, (k1_funct_1('#skF_9', '#skF_1'('#skF_10', '#skF_9'))='#skF_2'('#skF_10', '#skF_9') | ~v1_funct_1('#skF_9') | '#skF_10'='#skF_9' | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_1252, c_885])).
% 5.90/2.08  tff(c_1290, plain, (k1_funct_1('#skF_9', '#skF_1'('#skF_10', '#skF_9'))='#skF_2'('#skF_10', '#skF_9') | '#skF_10'='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_1267])).
% 5.90/2.08  tff(c_1291, plain, (k1_funct_1('#skF_9', '#skF_1'('#skF_10', '#skF_9'))='#skF_2'('#skF_10', '#skF_9')), inference(negUnitSimplification, [status(thm)], [c_32, c_1290])).
% 5.90/2.08  tff(c_905, plain, (k1_funct_1('#skF_10', '#skF_1'('#skF_10', '#skF_9'))=k1_funct_1('#skF_9', '#skF_1'('#skF_10', '#skF_9'))), inference(resolution, [status(thm)], [c_892, c_34])).
% 5.90/2.08  tff(c_1305, plain, (k1_funct_1('#skF_10', '#skF_1'('#skF_10', '#skF_9'))='#skF_2'('#skF_10', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_1291, c_905])).
% 5.90/2.08  tff(c_1322, plain, (r2_hidden(k4_tarski('#skF_1'('#skF_10', '#skF_9'), '#skF_2'('#skF_10', '#skF_9')), '#skF_10') | ~r2_hidden('#skF_1'('#skF_10', '#skF_9'), k1_relat_1('#skF_10')) | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_1305, c_26])).
% 5.90/2.08  tff(c_1326, plain, (r2_hidden(k4_tarski('#skF_1'('#skF_10', '#skF_9'), '#skF_2'('#skF_10', '#skF_9')), '#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_892, c_36, c_1322])).
% 5.90/2.08  tff(c_674, plain, (![A_93, B_94]: (~r2_hidden(k4_tarski('#skF_1'(A_93, B_94), '#skF_2'(A_93, B_94)), A_93) | r2_hidden(k4_tarski('#skF_3'(A_93, B_94), '#skF_4'(A_93, B_94)), A_93) | B_94=A_93 | ~v1_relat_1(B_94) | ~v1_relat_1(A_93))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.90/2.08  tff(c_696, plain, (![A_93, B_94]: (r2_hidden('#skF_3'(A_93, B_94), k1_relat_1(A_93)) | ~r2_hidden(k4_tarski('#skF_1'(A_93, B_94), '#skF_2'(A_93, B_94)), A_93) | B_94=A_93 | ~v1_relat_1(B_94) | ~v1_relat_1(A_93))), inference(resolution, [status(thm)], [c_674, c_16])).
% 5.90/2.08  tff(c_1371, plain, (r2_hidden('#skF_3'('#skF_10', '#skF_9'), k1_relat_1('#skF_10')) | '#skF_10'='#skF_9' | ~v1_relat_1('#skF_9') | ~v1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_1326, c_696])).
% 5.90/2.08  tff(c_1382, plain, (r2_hidden('#skF_3'('#skF_10', '#skF_9'), k1_relat_1('#skF_9')) | '#skF_10'='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_44, c_36, c_1371])).
% 5.90/2.08  tff(c_1384, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_885, c_1382])).
% 5.90/2.08  tff(c_1386, plain, (r2_hidden('#skF_3'('#skF_10', '#skF_9'), k1_relat_1('#skF_9'))), inference(splitRight, [status(thm)], [c_882])).
% 5.90/2.08  tff(c_2421, plain, (![A_150, B_151]: (k1_funct_1(A_150, '#skF_3'(A_150, B_151))='#skF_4'(A_150, B_151) | ~v1_funct_1(A_150) | r2_hidden(k4_tarski('#skF_1'(A_150, B_151), '#skF_2'(A_150, B_151)), B_151) | B_151=A_150 | ~v1_relat_1(B_151) | ~v1_relat_1(A_150))), inference(resolution, [status(thm)], [c_335, c_28])).
% 5.90/2.08  tff(c_2592, plain, (![B_158, A_159]: (k1_funct_1(B_158, '#skF_1'(A_159, B_158))='#skF_2'(A_159, B_158) | ~v1_funct_1(B_158) | k1_funct_1(A_159, '#skF_3'(A_159, B_158))='#skF_4'(A_159, B_158) | ~v1_funct_1(A_159) | B_158=A_159 | ~v1_relat_1(B_158) | ~v1_relat_1(A_159))), inference(resolution, [status(thm)], [c_2421, c_28])).
% 5.90/2.08  tff(c_2647, plain, (k1_funct_1('#skF_9', '#skF_3'('#skF_10', '#skF_9'))='#skF_4'('#skF_10', '#skF_9') | k1_funct_1('#skF_9', '#skF_1'('#skF_10', '#skF_9'))='#skF_2'('#skF_10', '#skF_9') | ~v1_funct_1('#skF_9') | ~v1_funct_1('#skF_10') | '#skF_10'='#skF_9' | ~v1_relat_1('#skF_9') | ~v1_relat_1('#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_2592, c_873])).
% 5.90/2.08  tff(c_2723, plain, (k1_funct_1('#skF_9', '#skF_3'('#skF_10', '#skF_9'))='#skF_4'('#skF_10', '#skF_9') | k1_funct_1('#skF_9', '#skF_1'('#skF_10', '#skF_9'))='#skF_2'('#skF_10', '#skF_9') | '#skF_10'='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_44, c_38, c_42, c_2647])).
% 5.90/2.08  tff(c_2724, plain, (k1_funct_1('#skF_9', '#skF_3'('#skF_10', '#skF_9'))='#skF_4'('#skF_10', '#skF_9') | k1_funct_1('#skF_9', '#skF_1'('#skF_10', '#skF_9'))='#skF_2'('#skF_10', '#skF_9')), inference(negUnitSimplification, [status(thm)], [c_32, c_2723])).
% 5.90/2.08  tff(c_3125, plain, (k1_funct_1('#skF_9', '#skF_1'('#skF_10', '#skF_9'))='#skF_2'('#skF_10', '#skF_9')), inference(splitLeft, [status(thm)], [c_2724])).
% 5.90/2.08  tff(c_1457, plain, (![A_121, B_122]: (r2_hidden('#skF_1'(A_121, B_122), k1_relat_1(B_122)) | r2_hidden(k4_tarski('#skF_3'(A_121, B_122), '#skF_4'(A_121, B_122)), A_121) | B_122=A_121 | ~v1_relat_1(B_122) | ~v1_relat_1(A_121))), inference(resolution, [status(thm)], [c_335, c_16])).
% 5.90/2.08  tff(c_1577, plain, (![A_128, B_129]: (k1_funct_1(A_128, '#skF_3'(A_128, B_129))='#skF_4'(A_128, B_129) | ~v1_funct_1(A_128) | r2_hidden('#skF_1'(A_128, B_129), k1_relat_1(B_129)) | B_129=A_128 | ~v1_relat_1(B_129) | ~v1_relat_1(A_128))), inference(resolution, [status(thm)], [c_1457, c_28])).
% 5.90/2.08  tff(c_1594, plain, (![A_128]: (k1_funct_1('#skF_10', '#skF_1'(A_128, '#skF_9'))=k1_funct_1('#skF_9', '#skF_1'(A_128, '#skF_9')) | k1_funct_1(A_128, '#skF_3'(A_128, '#skF_9'))='#skF_4'(A_128, '#skF_9') | ~v1_funct_1(A_128) | A_128='#skF_9' | ~v1_relat_1('#skF_9') | ~v1_relat_1(A_128))), inference(resolution, [status(thm)], [c_1577, c_34])).
% 5.90/2.08  tff(c_2003, plain, (![A_143]: (k1_funct_1('#skF_10', '#skF_1'(A_143, '#skF_9'))=k1_funct_1('#skF_9', '#skF_1'(A_143, '#skF_9')) | k1_funct_1(A_143, '#skF_3'(A_143, '#skF_9'))='#skF_4'(A_143, '#skF_9') | ~v1_funct_1(A_143) | A_143='#skF_9' | ~v1_relat_1(A_143))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_1594])).
% 5.90/2.08  tff(c_2018, plain, (k1_funct_1('#skF_9', '#skF_3'('#skF_10', '#skF_9'))='#skF_4'('#skF_10', '#skF_9') | k1_funct_1('#skF_10', '#skF_1'('#skF_10', '#skF_9'))=k1_funct_1('#skF_9', '#skF_1'('#skF_10', '#skF_9')) | ~v1_funct_1('#skF_10') | '#skF_10'='#skF_9' | ~v1_relat_1('#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_2003, c_873])).
% 5.90/2.08  tff(c_2043, plain, (k1_funct_1('#skF_9', '#skF_3'('#skF_10', '#skF_9'))='#skF_4'('#skF_10', '#skF_9') | k1_funct_1('#skF_10', '#skF_1'('#skF_10', '#skF_9'))=k1_funct_1('#skF_9', '#skF_1'('#skF_10', '#skF_9')) | '#skF_10'='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_2018])).
% 5.90/2.08  tff(c_2044, plain, (k1_funct_1('#skF_9', '#skF_3'('#skF_10', '#skF_9'))='#skF_4'('#skF_10', '#skF_9') | k1_funct_1('#skF_10', '#skF_1'('#skF_10', '#skF_9'))=k1_funct_1('#skF_9', '#skF_1'('#skF_10', '#skF_9'))), inference(negUnitSimplification, [status(thm)], [c_32, c_2043])).
% 5.90/2.08  tff(c_2053, plain, (k1_funct_1('#skF_10', '#skF_1'('#skF_10', '#skF_9'))=k1_funct_1('#skF_9', '#skF_1'('#skF_10', '#skF_9'))), inference(splitLeft, [status(thm)], [c_2044])).
% 5.90/2.08  tff(c_2058, plain, (r2_hidden(k4_tarski('#skF_1'('#skF_10', '#skF_9'), k1_funct_1('#skF_9', '#skF_1'('#skF_10', '#skF_9'))), '#skF_10') | ~r2_hidden('#skF_1'('#skF_10', '#skF_9'), k1_relat_1('#skF_10')) | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_2053, c_26])).
% 5.90/2.08  tff(c_2063, plain, (r2_hidden(k4_tarski('#skF_1'('#skF_10', '#skF_9'), k1_funct_1('#skF_9', '#skF_1'('#skF_10', '#skF_9'))), '#skF_10') | ~r2_hidden('#skF_1'('#skF_10', '#skF_9'), k1_relat_1('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_36, c_2058])).
% 5.90/2.08  tff(c_2074, plain, (~r2_hidden('#skF_1'('#skF_10', '#skF_9'), k1_relat_1('#skF_9'))), inference(splitLeft, [status(thm)], [c_2063])).
% 5.90/2.08  tff(c_1483, plain, (![A_121, B_122]: (k1_funct_1(A_121, '#skF_3'(A_121, B_122))='#skF_4'(A_121, B_122) | ~v1_funct_1(A_121) | r2_hidden('#skF_1'(A_121, B_122), k1_relat_1(B_122)) | B_122=A_121 | ~v1_relat_1(B_122) | ~v1_relat_1(A_121))), inference(resolution, [status(thm)], [c_1457, c_28])).
% 5.90/2.08  tff(c_2083, plain, (k1_funct_1('#skF_10', '#skF_3'('#skF_10', '#skF_9'))='#skF_4'('#skF_10', '#skF_9') | ~v1_funct_1('#skF_10') | '#skF_10'='#skF_9' | ~v1_relat_1('#skF_9') | ~v1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_1483, c_2074])).
% 5.90/2.08  tff(c_2099, plain, (k1_funct_1('#skF_9', '#skF_3'('#skF_10', '#skF_9'))='#skF_4'('#skF_10', '#skF_9') | '#skF_10'='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_44, c_38, c_873, c_2083])).
% 5.90/2.08  tff(c_2100, plain, (k1_funct_1('#skF_9', '#skF_3'('#skF_10', '#skF_9'))='#skF_4'('#skF_10', '#skF_9')), inference(negUnitSimplification, [status(thm)], [c_32, c_2099])).
% 5.90/2.08  tff(c_59, plain, (![C_55, A_56]: (r2_hidden(k4_tarski(C_55, '#skF_8'(A_56, k1_relat_1(A_56), C_55)), A_56) | ~r2_hidden(C_55, k1_relat_1(A_56)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.90/2.08  tff(c_73, plain, (![A_56, C_55]: ('#skF_8'(A_56, k1_relat_1(A_56), C_55)=k1_funct_1(A_56, C_55) | ~v1_funct_1(A_56) | ~v1_relat_1(A_56) | ~r2_hidden(C_55, k1_relat_1(A_56)))), inference(resolution, [status(thm)], [c_59, c_28])).
% 5.90/2.08  tff(c_1388, plain, ('#skF_8'('#skF_9', k1_relat_1('#skF_9'), '#skF_3'('#skF_10', '#skF_9'))=k1_funct_1('#skF_9', '#skF_3'('#skF_10', '#skF_9')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_1386, c_73])).
% 5.90/2.08  tff(c_1397, plain, ('#skF_8'('#skF_9', k1_relat_1('#skF_9'), '#skF_3'('#skF_10', '#skF_9'))=k1_funct_1('#skF_9', '#skF_3'('#skF_10', '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_1388])).
% 5.90/2.08  tff(c_14, plain, (![C_33, A_18]: (r2_hidden(k4_tarski(C_33, '#skF_8'(A_18, k1_relat_1(A_18), C_33)), A_18) | ~r2_hidden(C_33, k1_relat_1(A_18)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.90/2.08  tff(c_1417, plain, (r2_hidden(k4_tarski('#skF_3'('#skF_10', '#skF_9'), k1_funct_1('#skF_9', '#skF_3'('#skF_10', '#skF_9'))), '#skF_9') | ~r2_hidden('#skF_3'('#skF_10', '#skF_9'), k1_relat_1('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_1397, c_14])).
% 5.90/2.08  tff(c_1421, plain, (r2_hidden(k4_tarski('#skF_3'('#skF_10', '#skF_9'), k1_funct_1('#skF_9', '#skF_3'('#skF_10', '#skF_9'))), '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_1386, c_1417])).
% 5.90/2.08  tff(c_2106, plain, (r2_hidden(k4_tarski('#skF_3'('#skF_10', '#skF_9'), '#skF_4'('#skF_10', '#skF_9')), '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_2100, c_1421])).
% 5.90/2.08  tff(c_4, plain, (![A_1, B_11]: (r2_hidden(k4_tarski('#skF_1'(A_1, B_11), '#skF_2'(A_1, B_11)), B_11) | ~r2_hidden(k4_tarski('#skF_3'(A_1, B_11), '#skF_4'(A_1, B_11)), B_11) | B_11=A_1 | ~v1_relat_1(B_11) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.90/2.08  tff(c_2158, plain, (r2_hidden(k4_tarski('#skF_1'('#skF_10', '#skF_9'), '#skF_2'('#skF_10', '#skF_9')), '#skF_9') | '#skF_10'='#skF_9' | ~v1_relat_1('#skF_9') | ~v1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_2106, c_4])).
% 5.90/2.08  tff(c_2167, plain, (r2_hidden(k4_tarski('#skF_1'('#skF_10', '#skF_9'), '#skF_2'('#skF_10', '#skF_9')), '#skF_9') | '#skF_10'='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_44, c_2158])).
% 5.90/2.08  tff(c_2168, plain, (r2_hidden(k4_tarski('#skF_1'('#skF_10', '#skF_9'), '#skF_2'('#skF_10', '#skF_9')), '#skF_9')), inference(negUnitSimplification, [status(thm)], [c_32, c_2167])).
% 5.90/2.08  tff(c_2220, plain, (r2_hidden('#skF_1'('#skF_10', '#skF_9'), k1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_2168, c_16])).
% 5.90/2.08  tff(c_2227, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2074, c_2220])).
% 5.90/2.08  tff(c_2228, plain, (r2_hidden(k4_tarski('#skF_1'('#skF_10', '#skF_9'), k1_funct_1('#skF_9', '#skF_1'('#skF_10', '#skF_9'))), '#skF_10')), inference(splitRight, [status(thm)], [c_2063])).
% 5.90/2.08  tff(c_3129, plain, (r2_hidden(k4_tarski('#skF_1'('#skF_10', '#skF_9'), '#skF_2'('#skF_10', '#skF_9')), '#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_3125, c_2228])).
% 5.90/2.08  tff(c_2, plain, (![A_1, B_11]: (~r2_hidden(k4_tarski('#skF_1'(A_1, B_11), '#skF_2'(A_1, B_11)), A_1) | ~r2_hidden(k4_tarski('#skF_3'(A_1, B_11), '#skF_4'(A_1, B_11)), B_11) | B_11=A_1 | ~v1_relat_1(B_11) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.90/2.08  tff(c_3216, plain, (~r2_hidden(k4_tarski('#skF_3'('#skF_10', '#skF_9'), '#skF_4'('#skF_10', '#skF_9')), '#skF_9') | '#skF_10'='#skF_9' | ~v1_relat_1('#skF_9') | ~v1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_3129, c_2])).
% 5.90/2.08  tff(c_3233, plain, (~r2_hidden(k4_tarski('#skF_3'('#skF_10', '#skF_9'), '#skF_4'('#skF_10', '#skF_9')), '#skF_9') | '#skF_10'='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_44, c_3216])).
% 5.90/2.08  tff(c_3234, plain, (~r2_hidden(k4_tarski('#skF_3'('#skF_10', '#skF_9'), '#skF_4'('#skF_10', '#skF_9')), '#skF_9')), inference(negUnitSimplification, [status(thm)], [c_32, c_3233])).
% 5.90/2.08  tff(c_694, plain, (![A_93, B_94]: (k1_funct_1(A_93, '#skF_3'(A_93, B_94))='#skF_4'(A_93, B_94) | ~v1_funct_1(A_93) | ~r2_hidden(k4_tarski('#skF_1'(A_93, B_94), '#skF_2'(A_93, B_94)), A_93) | B_94=A_93 | ~v1_relat_1(B_94) | ~v1_relat_1(A_93))), inference(resolution, [status(thm)], [c_674, c_28])).
% 5.90/2.08  tff(c_3211, plain, (k1_funct_1('#skF_10', '#skF_3'('#skF_10', '#skF_9'))='#skF_4'('#skF_10', '#skF_9') | ~v1_funct_1('#skF_10') | '#skF_10'='#skF_9' | ~v1_relat_1('#skF_9') | ~v1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_3129, c_694])).
% 5.90/2.08  tff(c_3225, plain, (k1_funct_1('#skF_9', '#skF_3'('#skF_10', '#skF_9'))='#skF_4'('#skF_10', '#skF_9') | '#skF_10'='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_44, c_38, c_873, c_3211])).
% 5.90/2.08  tff(c_3226, plain, (k1_funct_1('#skF_9', '#skF_3'('#skF_10', '#skF_9'))='#skF_4'('#skF_10', '#skF_9')), inference(negUnitSimplification, [status(thm)], [c_32, c_3225])).
% 5.90/2.08  tff(c_3241, plain, (r2_hidden(k4_tarski('#skF_3'('#skF_10', '#skF_9'), '#skF_4'('#skF_10', '#skF_9')), '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_3226, c_1421])).
% 5.90/2.08  tff(c_3317, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3234, c_3241])).
% 5.90/2.08  tff(c_3319, plain, (k1_funct_1('#skF_9', '#skF_1'('#skF_10', '#skF_9'))!='#skF_2'('#skF_10', '#skF_9')), inference(splitRight, [status(thm)], [c_2724])).
% 5.90/2.08  tff(c_3318, plain, (k1_funct_1('#skF_9', '#skF_3'('#skF_10', '#skF_9'))='#skF_4'('#skF_10', '#skF_9')), inference(splitRight, [status(thm)], [c_2724])).
% 5.90/2.08  tff(c_3328, plain, (r2_hidden(k4_tarski('#skF_3'('#skF_10', '#skF_9'), '#skF_4'('#skF_10', '#skF_9')), '#skF_9') | ~r2_hidden('#skF_3'('#skF_10', '#skF_9'), k1_relat_1('#skF_9')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_3318, c_26])).
% 5.90/2.08  tff(c_3332, plain, (r2_hidden(k4_tarski('#skF_3'('#skF_10', '#skF_9'), '#skF_4'('#skF_10', '#skF_9')), '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_1386, c_3328])).
% 5.90/2.08  tff(c_3443, plain, (r2_hidden(k4_tarski('#skF_1'('#skF_10', '#skF_9'), '#skF_2'('#skF_10', '#skF_9')), '#skF_9') | '#skF_10'='#skF_9' | ~v1_relat_1('#skF_9') | ~v1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_3332, c_4])).
% 5.90/2.08  tff(c_3452, plain, (r2_hidden(k4_tarski('#skF_1'('#skF_10', '#skF_9'), '#skF_2'('#skF_10', '#skF_9')), '#skF_9') | '#skF_10'='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_44, c_3443])).
% 5.90/2.08  tff(c_3453, plain, (r2_hidden(k4_tarski('#skF_1'('#skF_10', '#skF_9'), '#skF_2'('#skF_10', '#skF_9')), '#skF_9')), inference(negUnitSimplification, [status(thm)], [c_32, c_3452])).
% 5.90/2.08  tff(c_3462, plain, (k1_funct_1('#skF_9', '#skF_1'('#skF_10', '#skF_9'))='#skF_2'('#skF_10', '#skF_9') | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_3453, c_28])).
% 5.90/2.08  tff(c_3468, plain, (k1_funct_1('#skF_9', '#skF_1'('#skF_10', '#skF_9'))='#skF_2'('#skF_10', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_3462])).
% 5.90/2.08  tff(c_3470, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3319, c_3468])).
% 5.90/2.08  tff(c_3471, plain, (k1_funct_1('#skF_9', '#skF_3'('#skF_10', '#skF_9'))='#skF_4'('#skF_10', '#skF_9')), inference(splitRight, [status(thm)], [c_2044])).
% 5.90/2.08  tff(c_3481, plain, (r2_hidden(k4_tarski('#skF_3'('#skF_10', '#skF_9'), '#skF_4'('#skF_10', '#skF_9')), '#skF_9') | ~r2_hidden('#skF_3'('#skF_10', '#skF_9'), k1_relat_1('#skF_9')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_3471, c_26])).
% 5.90/2.08  tff(c_3485, plain, (r2_hidden(k4_tarski('#skF_3'('#skF_10', '#skF_9'), '#skF_4'('#skF_10', '#skF_9')), '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_1386, c_3481])).
% 5.90/2.08  tff(c_3535, plain, (r2_hidden(k4_tarski('#skF_1'('#skF_10', '#skF_9'), '#skF_2'('#skF_10', '#skF_9')), '#skF_9') | '#skF_10'='#skF_9' | ~v1_relat_1('#skF_9') | ~v1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_3485, c_4])).
% 5.90/2.08  tff(c_3544, plain, (r2_hidden(k4_tarski('#skF_1'('#skF_10', '#skF_9'), '#skF_2'('#skF_10', '#skF_9')), '#skF_9') | '#skF_10'='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_44, c_3535])).
% 5.90/2.08  tff(c_3545, plain, (r2_hidden(k4_tarski('#skF_1'('#skF_10', '#skF_9'), '#skF_2'('#skF_10', '#skF_9')), '#skF_9')), inference(negUnitSimplification, [status(thm)], [c_32, c_3544])).
% 5.90/2.08  tff(c_3553, plain, (k1_funct_1('#skF_9', '#skF_1'('#skF_10', '#skF_9'))='#skF_2'('#skF_10', '#skF_9') | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_3545, c_28])).
% 5.90/2.08  tff(c_3559, plain, (k1_funct_1('#skF_9', '#skF_1'('#skF_10', '#skF_9'))='#skF_2'('#skF_10', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_3553])).
% 5.90/2.08  tff(c_3472, plain, (k1_funct_1('#skF_10', '#skF_1'('#skF_10', '#skF_9'))!=k1_funct_1('#skF_9', '#skF_1'('#skF_10', '#skF_9'))), inference(splitRight, [status(thm)], [c_2044])).
% 5.90/2.08  tff(c_3588, plain, (k1_funct_1('#skF_10', '#skF_1'('#skF_10', '#skF_9'))!='#skF_2'('#skF_10', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_3559, c_3472])).
% 5.90/2.08  tff(c_3560, plain, (r2_hidden('#skF_1'('#skF_10', '#skF_9'), k1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_3545, c_16])).
% 5.90/2.08  tff(c_3573, plain, (k1_funct_1('#skF_10', '#skF_1'('#skF_10', '#skF_9'))=k1_funct_1('#skF_9', '#skF_1'('#skF_10', '#skF_9'))), inference(resolution, [status(thm)], [c_3560, c_34])).
% 5.90/2.08  tff(c_3647, plain, (k1_funct_1('#skF_10', '#skF_1'('#skF_10', '#skF_9'))='#skF_2'('#skF_10', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_3559, c_3573])).
% 5.90/2.08  tff(c_3648, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3588, c_3647])).
% 5.90/2.08  tff(c_3650, plain, (k1_funct_1('#skF_10', '#skF_3'('#skF_10', '#skF_9'))!=k1_funct_1('#skF_9', '#skF_3'('#skF_10', '#skF_9'))), inference(splitRight, [status(thm)], [c_869])).
% 5.90/2.08  tff(c_3868, plain, (![B_174, A_175]: (k1_funct_1(B_174, '#skF_1'(A_175, B_174))='#skF_2'(A_175, B_174) | ~v1_funct_1(B_174) | r2_hidden('#skF_3'(A_175, B_174), k1_relat_1(A_175)) | B_174=A_175 | ~v1_relat_1(B_174) | ~v1_relat_1(A_175))), inference(resolution, [status(thm)], [c_651, c_28])).
% 5.90/2.08  tff(c_3894, plain, (![B_174]: (k1_funct_1(B_174, '#skF_1'('#skF_10', B_174))='#skF_2'('#skF_10', B_174) | ~v1_funct_1(B_174) | r2_hidden('#skF_3'('#skF_10', B_174), k1_relat_1('#skF_9')) | B_174='#skF_10' | ~v1_relat_1(B_174) | ~v1_relat_1('#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_36, c_3868])).
% 5.90/2.08  tff(c_3906, plain, (![B_176]: (k1_funct_1(B_176, '#skF_1'('#skF_10', B_176))='#skF_2'('#skF_10', B_176) | ~v1_funct_1(B_176) | r2_hidden('#skF_3'('#skF_10', B_176), k1_relat_1('#skF_9')) | B_176='#skF_10' | ~v1_relat_1(B_176))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_3894])).
% 5.90/2.08  tff(c_4169, plain, (![B_187]: (k1_funct_1('#skF_10', '#skF_3'('#skF_10', B_187))=k1_funct_1('#skF_9', '#skF_3'('#skF_10', B_187)) | k1_funct_1(B_187, '#skF_1'('#skF_10', B_187))='#skF_2'('#skF_10', B_187) | ~v1_funct_1(B_187) | B_187='#skF_10' | ~v1_relat_1(B_187))), inference(resolution, [status(thm)], [c_3906, c_34])).
% 5.90/2.08  tff(c_4177, plain, (k1_funct_1('#skF_9', '#skF_1'('#skF_10', '#skF_9'))='#skF_2'('#skF_10', '#skF_9') | ~v1_funct_1('#skF_9') | '#skF_10'='#skF_9' | ~v1_relat_1('#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_4169, c_3650])).
% 5.90/2.08  tff(c_4215, plain, (k1_funct_1('#skF_9', '#skF_1'('#skF_10', '#skF_9'))='#skF_2'('#skF_10', '#skF_9') | '#skF_10'='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_4177])).
% 5.90/2.08  tff(c_4216, plain, (k1_funct_1('#skF_9', '#skF_1'('#skF_10', '#skF_9'))='#skF_2'('#skF_10', '#skF_9')), inference(negUnitSimplification, [status(thm)], [c_32, c_4215])).
% 5.90/2.08  tff(c_749, plain, (![B_97]: (k1_funct_1('#skF_10', '#skF_3'('#skF_10', B_97))=k1_funct_1('#skF_9', '#skF_3'('#skF_10', B_97)) | r2_hidden('#skF_1'('#skF_10', B_97), k1_relat_1(B_97)) | B_97='#skF_10' | ~v1_relat_1(B_97))), inference(resolution, [status(thm)], [c_728, c_34])).
% 5.90/2.08  tff(c_3649, plain, (k1_funct_1('#skF_10', '#skF_1'('#skF_10', '#skF_9'))=k1_funct_1('#skF_9', '#skF_1'('#skF_10', '#skF_9'))), inference(splitRight, [status(thm)], [c_869])).
% 5.90/2.08  tff(c_3654, plain, (r2_hidden(k4_tarski('#skF_1'('#skF_10', '#skF_9'), k1_funct_1('#skF_9', '#skF_1'('#skF_10', '#skF_9'))), '#skF_10') | ~r2_hidden('#skF_1'('#skF_10', '#skF_9'), k1_relat_1('#skF_10')) | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_3649, c_26])).
% 5.90/2.08  tff(c_3658, plain, (r2_hidden(k4_tarski('#skF_1'('#skF_10', '#skF_9'), k1_funct_1('#skF_9', '#skF_1'('#skF_10', '#skF_9'))), '#skF_10') | ~r2_hidden('#skF_1'('#skF_10', '#skF_9'), k1_relat_1('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_36, c_3654])).
% 5.90/2.08  tff(c_3685, plain, (~r2_hidden('#skF_1'('#skF_10', '#skF_9'), k1_relat_1('#skF_9'))), inference(splitLeft, [status(thm)], [c_3658])).
% 5.90/2.08  tff(c_3688, plain, (k1_funct_1('#skF_10', '#skF_3'('#skF_10', '#skF_9'))=k1_funct_1('#skF_9', '#skF_3'('#skF_10', '#skF_9')) | '#skF_10'='#skF_9' | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_749, c_3685])).
% 5.90/2.08  tff(c_3693, plain, (k1_funct_1('#skF_10', '#skF_3'('#skF_10', '#skF_9'))=k1_funct_1('#skF_9', '#skF_3'('#skF_10', '#skF_9')) | '#skF_10'='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_44, c_3688])).
% 5.90/2.08  tff(c_3695, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_3650, c_3693])).
% 5.90/2.08  tff(c_3696, plain, (r2_hidden(k4_tarski('#skF_1'('#skF_10', '#skF_9'), k1_funct_1('#skF_9', '#skF_1'('#skF_10', '#skF_9'))), '#skF_10')), inference(splitRight, [status(thm)], [c_3658])).
% 5.90/2.08  tff(c_4232, plain, (r2_hidden(k4_tarski('#skF_1'('#skF_10', '#skF_9'), '#skF_2'('#skF_10', '#skF_9')), '#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_4216, c_3696])).
% 5.90/2.08  tff(c_4264, plain, (r2_hidden('#skF_3'('#skF_10', '#skF_9'), k1_relat_1('#skF_10')) | '#skF_10'='#skF_9' | ~v1_relat_1('#skF_9') | ~v1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_4232, c_696])).
% 5.90/2.08  tff(c_4279, plain, (r2_hidden('#skF_3'('#skF_10', '#skF_9'), k1_relat_1('#skF_9')) | '#skF_10'='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_44, c_36, c_4264])).
% 5.90/2.08  tff(c_4280, plain, (r2_hidden('#skF_3'('#skF_10', '#skF_9'), k1_relat_1('#skF_9'))), inference(negUnitSimplification, [status(thm)], [c_32, c_4279])).
% 5.90/2.08  tff(c_4297, plain, (k1_funct_1('#skF_10', '#skF_3'('#skF_10', '#skF_9'))=k1_funct_1('#skF_9', '#skF_3'('#skF_10', '#skF_9'))), inference(resolution, [status(thm)], [c_4280, c_34])).
% 5.90/2.08  tff(c_4305, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3650, c_4297])).
% 5.90/2.08  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.90/2.08  
% 5.90/2.08  Inference rules
% 5.90/2.08  ----------------------
% 5.90/2.08  #Ref     : 0
% 5.90/2.08  #Sup     : 797
% 5.90/2.08  #Fact    : 0
% 5.90/2.08  #Define  : 0
% 5.90/2.08  #Split   : 15
% 5.90/2.08  #Chain   : 0
% 5.90/2.08  #Close   : 0
% 5.90/2.08  
% 5.90/2.08  Ordering : KBO
% 5.90/2.08  
% 5.90/2.08  Simplification rules
% 5.90/2.08  ----------------------
% 5.90/2.08  #Subsume      : 64
% 5.90/2.08  #Demod        : 1017
% 5.90/2.08  #Tautology    : 484
% 5.90/2.08  #SimpNegUnit  : 97
% 5.90/2.08  #BackRed      : 55
% 5.90/2.08  
% 5.90/2.08  #Partial instantiations: 0
% 5.90/2.08  #Strategies tried      : 1
% 5.90/2.08  
% 5.90/2.08  Timing (in seconds)
% 5.90/2.08  ----------------------
% 5.90/2.08  Preprocessing        : 0.30
% 5.90/2.08  Parsing              : 0.15
% 5.90/2.08  CNF conversion       : 0.03
% 5.90/2.08  Main loop            : 1.00
% 5.90/2.08  Inferencing          : 0.39
% 5.90/2.08  Reduction            : 0.31
% 5.90/2.08  Demodulation         : 0.21
% 5.90/2.08  BG Simplification    : 0.05
% 5.90/2.08  Subsumption          : 0.19
% 5.90/2.08  Abstraction          : 0.06
% 5.90/2.08  MUC search           : 0.00
% 5.90/2.08  Cooper               : 0.00
% 5.90/2.08  Total                : 1.35
% 5.90/2.08  Index Insertion      : 0.00
% 5.90/2.08  Index Deletion       : 0.00
% 5.90/2.08  Index Matching       : 0.00
% 5.90/2.08  BG Taut test         : 0.00
%------------------------------------------------------------------------------
