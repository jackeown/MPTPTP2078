%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0702+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:43 EST 2020

% Result     : Theorem 17.39s
% Output     : CNFRefutation 17.39s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 118 expanded)
%              Number of leaves         :   25 (  55 expanded)
%              Depth                    :   16
%              Number of atoms          :  171 ( 362 expanded)
%              Number of equality atoms :   14 (  22 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k1_funct_1 > #nlpp > k1_relat_1 > #skF_7 > #skF_1 > #skF_10 > #skF_2 > #skF_9 > #skF_4 > #skF_8 > #skF_3 > #skF_5 > #skF_6

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_7',type,(
    '#skF_7': $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_6',type,(
    '#skF_6': $i > $i )).

tff(f_76,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( ( r1_tarski(k9_relat_1(C,A),k9_relat_1(C,B))
            & r1_tarski(A,k1_relat_1(C))
            & v2_funct_1(C) )
         => r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t157_funct_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_41,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B,C] :
          ( C = k9_relat_1(A,B)
        <=> ! [D] :
              ( r2_hidden(D,C)
            <=> ? [E] :
                  ( r2_hidden(E,k1_relat_1(A))
                  & r2_hidden(E,B)
                  & D = k1_funct_1(A,E) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_funct_1)).

tff(f_63,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
      <=> ! [B,C] :
            ( ( r2_hidden(B,k1_relat_1(A))
              & r2_hidden(C,k1_relat_1(A))
              & k1_funct_1(A,B) = k1_funct_1(A,C) )
           => B = C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_funct_1)).

tff(c_42,plain,(
    ~ r1_tarski('#skF_8','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_54,plain,(
    ! [A_57,B_58] :
      ( r2_hidden('#skF_5'(A_57,B_58),A_57)
      | r1_tarski(A_57,B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_28,plain,(
    ! [A_43,B_44] :
      ( ~ r2_hidden('#skF_5'(A_43,B_44),B_44)
      | r1_tarski(A_43,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_59,plain,(
    ! [A_57] : r1_tarski(A_57,A_57) ),
    inference(resolution,[status(thm)],[c_54,c_28])).

tff(c_30,plain,(
    ! [A_43,B_44] :
      ( r2_hidden('#skF_5'(A_43,B_44),A_43)
      | r1_tarski(A_43,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_46,plain,(
    r1_tarski('#skF_8',k1_relat_1('#skF_10')) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_61,plain,(
    ! [C_60,B_61,A_62] :
      ( r2_hidden(C_60,B_61)
      | ~ r2_hidden(C_60,A_62)
      | ~ r1_tarski(A_62,B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_74,plain,(
    ! [A_66,B_67,B_68] :
      ( r2_hidden('#skF_5'(A_66,B_67),B_68)
      | ~ r1_tarski(A_66,B_68)
      | r1_tarski(A_66,B_67) ) ),
    inference(resolution,[status(thm)],[c_30,c_61])).

tff(c_26,plain,(
    ! [C_47,B_44,A_43] :
      ( r2_hidden(C_47,B_44)
      | ~ r2_hidden(C_47,A_43)
      | ~ r1_tarski(A_43,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_104,plain,(
    ! [A_77,B_78,B_79,B_80] :
      ( r2_hidden('#skF_5'(A_77,B_78),B_79)
      | ~ r1_tarski(B_80,B_79)
      | ~ r1_tarski(A_77,B_80)
      | r1_tarski(A_77,B_78) ) ),
    inference(resolution,[status(thm)],[c_74,c_26])).

tff(c_113,plain,(
    ! [A_77,B_78] :
      ( r2_hidden('#skF_5'(A_77,B_78),k1_relat_1('#skF_10'))
      | ~ r1_tarski(A_77,'#skF_8')
      | r1_tarski(A_77,B_78) ) ),
    inference(resolution,[status(thm)],[c_46,c_104])).

tff(c_52,plain,(
    v1_relat_1('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_50,plain,(
    v1_funct_1('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_48,plain,(
    r1_tarski(k9_relat_1('#skF_10','#skF_8'),k9_relat_1('#skF_10','#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_162,plain,(
    ! [A_92,E_93,B_94] :
      ( r2_hidden(k1_funct_1(A_92,E_93),k9_relat_1(A_92,B_94))
      | ~ r2_hidden(E_93,B_94)
      | ~ r2_hidden(E_93,k1_relat_1(A_92))
      | ~ v1_funct_1(A_92)
      | ~ v1_relat_1(A_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_373,plain,(
    ! [A_150,E_151,B_152,B_153] :
      ( r2_hidden(k1_funct_1(A_150,E_151),B_152)
      | ~ r1_tarski(k9_relat_1(A_150,B_153),B_152)
      | ~ r2_hidden(E_151,B_153)
      | ~ r2_hidden(E_151,k1_relat_1(A_150))
      | ~ v1_funct_1(A_150)
      | ~ v1_relat_1(A_150) ) ),
    inference(resolution,[status(thm)],[c_162,c_26])).

tff(c_384,plain,(
    ! [E_151] :
      ( r2_hidden(k1_funct_1('#skF_10',E_151),k9_relat_1('#skF_10','#skF_9'))
      | ~ r2_hidden(E_151,'#skF_8')
      | ~ r2_hidden(E_151,k1_relat_1('#skF_10'))
      | ~ v1_funct_1('#skF_10')
      | ~ v1_relat_1('#skF_10') ) ),
    inference(resolution,[status(thm)],[c_48,c_373])).

tff(c_391,plain,(
    ! [E_154] :
      ( r2_hidden(k1_funct_1('#skF_10',E_154),k9_relat_1('#skF_10','#skF_9'))
      | ~ r2_hidden(E_154,'#skF_8')
      | ~ r2_hidden(E_154,k1_relat_1('#skF_10')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_384])).

tff(c_402,plain,(
    ! [E_154,B_44] :
      ( r2_hidden(k1_funct_1('#skF_10',E_154),B_44)
      | ~ r1_tarski(k9_relat_1('#skF_10','#skF_9'),B_44)
      | ~ r2_hidden(E_154,'#skF_8')
      | ~ r2_hidden(E_154,k1_relat_1('#skF_10')) ) ),
    inference(resolution,[status(thm)],[c_391,c_26])).

tff(c_44,plain,(
    v2_funct_1('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_390,plain,(
    ! [E_151] :
      ( r2_hidden(k1_funct_1('#skF_10',E_151),k9_relat_1('#skF_10','#skF_9'))
      | ~ r2_hidden(E_151,'#skF_8')
      | ~ r2_hidden(E_151,k1_relat_1('#skF_10')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_384])).

tff(c_227,plain,(
    ! [A_106,B_107,D_108] :
      ( r2_hidden('#skF_4'(A_106,B_107,k9_relat_1(A_106,B_107),D_108),k1_relat_1(A_106))
      | ~ r2_hidden(D_108,k9_relat_1(A_106,B_107))
      | ~ v1_funct_1(A_106)
      | ~ v1_relat_1(A_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_230,plain,(
    ! [A_106,B_107,D_108,B_44] :
      ( r2_hidden('#skF_4'(A_106,B_107,k9_relat_1(A_106,B_107),D_108),B_44)
      | ~ r1_tarski(k1_relat_1(A_106),B_44)
      | ~ r2_hidden(D_108,k9_relat_1(A_106,B_107))
      | ~ v1_funct_1(A_106)
      | ~ v1_relat_1(A_106) ) ),
    inference(resolution,[status(thm)],[c_227,c_26])).

tff(c_4,plain,(
    ! [A_1,B_24,D_39] :
      ( k1_funct_1(A_1,'#skF_4'(A_1,B_24,k9_relat_1(A_1,B_24),D_39)) = D_39
      | ~ r2_hidden(D_39,k9_relat_1(A_1,B_24))
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_360,plain,(
    ! [C_143,B_144,A_145] :
      ( C_143 = B_144
      | k1_funct_1(A_145,C_143) != k1_funct_1(A_145,B_144)
      | ~ r2_hidden(C_143,k1_relat_1(A_145))
      | ~ r2_hidden(B_144,k1_relat_1(A_145))
      | ~ v2_funct_1(A_145)
      | ~ v1_funct_1(A_145)
      | ~ v1_relat_1(A_145) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_362,plain,(
    ! [B_144,A_1,B_24,D_39] :
      ( B_144 = '#skF_4'(A_1,B_24,k9_relat_1(A_1,B_24),D_39)
      | k1_funct_1(A_1,B_144) != D_39
      | ~ r2_hidden('#skF_4'(A_1,B_24,k9_relat_1(A_1,B_24),D_39),k1_relat_1(A_1))
      | ~ r2_hidden(B_144,k1_relat_1(A_1))
      | ~ v2_funct_1(A_1)
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1)
      | ~ r2_hidden(D_39,k9_relat_1(A_1,B_24))
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_360])).

tff(c_14867,plain,(
    ! [A_782,B_783,B_784] :
      ( '#skF_4'(A_782,B_783,k9_relat_1(A_782,B_783),k1_funct_1(A_782,B_784)) = B_784
      | ~ r2_hidden('#skF_4'(A_782,B_783,k9_relat_1(A_782,B_783),k1_funct_1(A_782,B_784)),k1_relat_1(A_782))
      | ~ r2_hidden(B_784,k1_relat_1(A_782))
      | ~ v2_funct_1(A_782)
      | ~ v1_funct_1(A_782)
      | ~ v1_relat_1(A_782)
      | ~ r2_hidden(k1_funct_1(A_782,B_784),k9_relat_1(A_782,B_783))
      | ~ v1_funct_1(A_782)
      | ~ v1_relat_1(A_782) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_362])).

tff(c_14900,plain,(
    ! [A_106,B_107,B_784] :
      ( '#skF_4'(A_106,B_107,k9_relat_1(A_106,B_107),k1_funct_1(A_106,B_784)) = B_784
      | ~ r2_hidden(B_784,k1_relat_1(A_106))
      | ~ v2_funct_1(A_106)
      | ~ r1_tarski(k1_relat_1(A_106),k1_relat_1(A_106))
      | ~ r2_hidden(k1_funct_1(A_106,B_784),k9_relat_1(A_106,B_107))
      | ~ v1_funct_1(A_106)
      | ~ v1_relat_1(A_106) ) ),
    inference(resolution,[status(thm)],[c_230,c_14867])).

tff(c_26714,plain,(
    ! [A_1079,B_1080,B_1081] :
      ( '#skF_4'(A_1079,B_1080,k9_relat_1(A_1079,B_1080),k1_funct_1(A_1079,B_1081)) = B_1081
      | ~ r2_hidden(B_1081,k1_relat_1(A_1079))
      | ~ v2_funct_1(A_1079)
      | ~ r2_hidden(k1_funct_1(A_1079,B_1081),k9_relat_1(A_1079,B_1080))
      | ~ v1_funct_1(A_1079)
      | ~ v1_relat_1(A_1079) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_14900])).

tff(c_26802,plain,(
    ! [E_151] :
      ( '#skF_4'('#skF_10','#skF_9',k9_relat_1('#skF_10','#skF_9'),k1_funct_1('#skF_10',E_151)) = E_151
      | ~ v2_funct_1('#skF_10')
      | ~ v1_funct_1('#skF_10')
      | ~ v1_relat_1('#skF_10')
      | ~ r2_hidden(E_151,'#skF_8')
      | ~ r2_hidden(E_151,k1_relat_1('#skF_10')) ) ),
    inference(resolution,[status(thm)],[c_390,c_26714])).

tff(c_26868,plain,(
    ! [E_1082] :
      ( '#skF_4'('#skF_10','#skF_9',k9_relat_1('#skF_10','#skF_9'),k1_funct_1('#skF_10',E_1082)) = E_1082
      | ~ r2_hidden(E_1082,'#skF_8')
      | ~ r2_hidden(E_1082,k1_relat_1('#skF_10')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_44,c_26802])).

tff(c_6,plain,(
    ! [A_1,B_24,D_39] :
      ( r2_hidden('#skF_4'(A_1,B_24,k9_relat_1(A_1,B_24),D_39),B_24)
      | ~ r2_hidden(D_39,k9_relat_1(A_1,B_24))
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_26920,plain,(
    ! [E_1082] :
      ( r2_hidden(E_1082,'#skF_9')
      | ~ r2_hidden(k1_funct_1('#skF_10',E_1082),k9_relat_1('#skF_10','#skF_9'))
      | ~ v1_funct_1('#skF_10')
      | ~ v1_relat_1('#skF_10')
      | ~ r2_hidden(E_1082,'#skF_8')
      | ~ r2_hidden(E_1082,k1_relat_1('#skF_10')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26868,c_6])).

tff(c_26983,plain,(
    ! [E_1083] :
      ( r2_hidden(E_1083,'#skF_9')
      | ~ r2_hidden(k1_funct_1('#skF_10',E_1083),k9_relat_1('#skF_10','#skF_9'))
      | ~ r2_hidden(E_1083,'#skF_8')
      | ~ r2_hidden(E_1083,k1_relat_1('#skF_10')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_26920])).

tff(c_27027,plain,(
    ! [E_154] :
      ( r2_hidden(E_154,'#skF_9')
      | ~ r1_tarski(k9_relat_1('#skF_10','#skF_9'),k9_relat_1('#skF_10','#skF_9'))
      | ~ r2_hidden(E_154,'#skF_8')
      | ~ r2_hidden(E_154,k1_relat_1('#skF_10')) ) ),
    inference(resolution,[status(thm)],[c_402,c_26983])).

tff(c_27072,plain,(
    ! [E_1084] :
      ( r2_hidden(E_1084,'#skF_9')
      | ~ r2_hidden(E_1084,'#skF_8')
      | ~ r2_hidden(E_1084,k1_relat_1('#skF_10')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_27027])).

tff(c_27465,plain,(
    ! [A_1085,B_1086] :
      ( r2_hidden('#skF_5'(A_1085,B_1086),'#skF_9')
      | ~ r2_hidden('#skF_5'(A_1085,B_1086),'#skF_8')
      | ~ r1_tarski(A_1085,'#skF_8')
      | r1_tarski(A_1085,B_1086) ) ),
    inference(resolution,[status(thm)],[c_113,c_27072])).

tff(c_27501,plain,(
    ! [A_1087] :
      ( ~ r2_hidden('#skF_5'(A_1087,'#skF_9'),'#skF_8')
      | ~ r1_tarski(A_1087,'#skF_8')
      | r1_tarski(A_1087,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_27465,c_28])).

tff(c_27529,plain,
    ( ~ r1_tarski('#skF_8','#skF_8')
    | r1_tarski('#skF_8','#skF_9') ),
    inference(resolution,[status(thm)],[c_30,c_27501])).

tff(c_27538,plain,(
    r1_tarski('#skF_8','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_27529])).

tff(c_27540,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_27538])).

%------------------------------------------------------------------------------
