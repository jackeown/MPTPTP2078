%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:46 EST 2020

% Result     : Theorem 6.86s
% Output     : CNFRefutation 7.24s
% Verified   : 
% Statistics : Number of formulae       :  131 (1298 expanded)
%              Number of leaves         :   33 ( 483 expanded)
%              Depth                    :   19
%              Number of atoms          :  257 (3971 expanded)
%              Number of equality atoms :   39 (1012 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > k4_tarski > k1_funct_1 > #nlpp > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_6 > #skF_4 > #skF_3 > #skF_10 > #skF_8 > #skF_9 > #skF_2 > #skF_7 > #skF_1 > #skF_5

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i ) > $i )).

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

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff(f_109,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ( ( v2_funct_1(B)
            & r2_hidden(A,k2_relat_1(B)) )
         => ( A = k1_funct_1(B,k1_funct_1(k2_funct_1(B),A))
            & A = k1_funct_1(k5_relat_1(k2_funct_1(B),B),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_funct_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

tff(f_73,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_65,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(A) = k4_relat_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).

tff(f_49,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => v1_relat_1(k4_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_relat_1)).

tff(f_45,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( B = k4_relat_1(A)
          <=> ! [C,D] :
                ( r2_hidden(k4_tarski(C,D),B)
              <=> r2_hidden(k4_tarski(D,C),A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_relat_1)).

tff(f_96,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
       => ( r2_hidden(A,k1_relat_1(C))
          & r2_hidden(B,k2_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_relat_1)).

tff(f_86,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ! [C] :
          ( ( v1_relat_1(C)
            & v1_funct_1(C) )
         => ( r2_hidden(A,k1_relat_1(B))
           => k1_funct_1(k5_relat_1(B,C),A) = k1_funct_1(C,k1_funct_1(B,A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_funct_1)).

tff(c_54,plain,(
    v1_relat_1('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_52,plain,(
    v1_funct_1('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_48,plain,(
    r2_hidden('#skF_9',k2_relat_1('#skF_10')) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_2,plain,(
    ! [A_1,C_16] :
      ( r2_hidden(k4_tarski('#skF_4'(A_1,k2_relat_1(A_1),C_16),C_16),A_1)
      | ~ r2_hidden(C_16,k2_relat_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_34,plain,(
    ! [A_42] :
      ( v1_funct_1(k2_funct_1(A_42))
      | ~ v1_funct_1(A_42)
      | ~ v1_relat_1(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_50,plain,(
    v2_funct_1('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_59,plain,(
    ! [A_56] :
      ( k4_relat_1(A_56) = k2_funct_1(A_56)
      | ~ v2_funct_1(A_56)
      | ~ v1_funct_1(A_56)
      | ~ v1_relat_1(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_62,plain,
    ( k4_relat_1('#skF_10') = k2_funct_1('#skF_10')
    | ~ v1_funct_1('#skF_10')
    | ~ v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_50,c_59])).

tff(c_65,plain,(
    k4_relat_1('#skF_10') = k2_funct_1('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_62])).

tff(c_26,plain,(
    ! [A_37] :
      ( v1_relat_1(k4_relat_1(A_37))
      | ~ v1_relat_1(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_853,plain,
    ( v1_relat_1(k2_funct_1('#skF_10'))
    | ~ v1_relat_1('#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_65,c_26])).

tff(c_857,plain,(
    v1_relat_1(k2_funct_1('#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_853])).

tff(c_1404,plain,(
    ! [C_181,D_182,A_183] :
      ( r2_hidden(k4_tarski(C_181,D_182),k4_relat_1(A_183))
      | ~ r2_hidden(k4_tarski(D_182,C_181),A_183)
      | ~ v1_relat_1(k4_relat_1(A_183))
      | ~ v1_relat_1(A_183) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1419,plain,(
    ! [C_181,D_182] :
      ( r2_hidden(k4_tarski(C_181,D_182),k2_funct_1('#skF_10'))
      | ~ r2_hidden(k4_tarski(D_182,C_181),'#skF_10')
      | ~ v1_relat_1(k4_relat_1('#skF_10'))
      | ~ v1_relat_1('#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_65,c_1404])).

tff(c_1426,plain,(
    ! [C_184,D_185] :
      ( r2_hidden(k4_tarski(C_184,D_185),k2_funct_1('#skF_10'))
      | ~ r2_hidden(k4_tarski(D_185,C_184),'#skF_10') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_857,c_65,c_1419])).

tff(c_42,plain,(
    ! [C_49,A_47,B_48] :
      ( k1_funct_1(C_49,A_47) = B_48
      | ~ r2_hidden(k4_tarski(A_47,B_48),C_49)
      | ~ v1_funct_1(C_49)
      | ~ v1_relat_1(C_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_1432,plain,(
    ! [C_184,D_185] :
      ( k1_funct_1(k2_funct_1('#skF_10'),C_184) = D_185
      | ~ v1_funct_1(k2_funct_1('#skF_10'))
      | ~ v1_relat_1(k2_funct_1('#skF_10'))
      | ~ r2_hidden(k4_tarski(D_185,C_184),'#skF_10') ) ),
    inference(resolution,[status(thm)],[c_1426,c_42])).

tff(c_1442,plain,(
    ! [C_184,D_185] :
      ( k1_funct_1(k2_funct_1('#skF_10'),C_184) = D_185
      | ~ v1_funct_1(k2_funct_1('#skF_10'))
      | ~ r2_hidden(k4_tarski(D_185,C_184),'#skF_10') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_857,c_1432])).

tff(c_1678,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_10')) ),
    inference(splitLeft,[status(thm)],[c_1442])).

tff(c_1681,plain,
    ( ~ v1_funct_1('#skF_10')
    | ~ v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_34,c_1678])).

tff(c_1685,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_1681])).

tff(c_1688,plain,(
    ! [C_203,D_204] :
      ( k1_funct_1(k2_funct_1('#skF_10'),C_203) = D_204
      | ~ r2_hidden(k4_tarski(D_204,C_203),'#skF_10') ) ),
    inference(splitRight,[status(thm)],[c_1442])).

tff(c_1769,plain,(
    ! [C_209] :
      ( k1_funct_1(k2_funct_1('#skF_10'),C_209) = '#skF_4'('#skF_10',k2_relat_1('#skF_10'),C_209)
      | ~ r2_hidden(C_209,k2_relat_1('#skF_10')) ) ),
    inference(resolution,[status(thm)],[c_2,c_1688])).

tff(c_1800,plain,(
    k1_funct_1(k2_funct_1('#skF_10'),'#skF_9') = '#skF_4'('#skF_10',k2_relat_1('#skF_10'),'#skF_9') ),
    inference(resolution,[status(thm)],[c_48,c_1769])).

tff(c_70,plain,
    ( v1_relat_1(k2_funct_1('#skF_10'))
    | ~ v1_relat_1('#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_65,c_26])).

tff(c_74,plain,(
    v1_relat_1(k2_funct_1('#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_70])).

tff(c_138,plain,(
    ! [C_81,D_82,A_83] :
      ( r2_hidden(k4_tarski(C_81,D_82),k4_relat_1(A_83))
      | ~ r2_hidden(k4_tarski(D_82,C_81),A_83)
      | ~ v1_relat_1(k4_relat_1(A_83))
      | ~ v1_relat_1(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_153,plain,(
    ! [C_81,D_82] :
      ( r2_hidden(k4_tarski(C_81,D_82),k2_funct_1('#skF_10'))
      | ~ r2_hidden(k4_tarski(D_82,C_81),'#skF_10')
      | ~ v1_relat_1(k4_relat_1('#skF_10'))
      | ~ v1_relat_1('#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_65,c_138])).

tff(c_160,plain,(
    ! [C_84,D_85] :
      ( r2_hidden(k4_tarski(C_84,D_85),k2_funct_1('#skF_10'))
      | ~ r2_hidden(k4_tarski(D_85,C_84),'#skF_10') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_74,c_65,c_153])).

tff(c_166,plain,(
    ! [C_84,D_85] :
      ( k1_funct_1(k2_funct_1('#skF_10'),C_84) = D_85
      | ~ v1_funct_1(k2_funct_1('#skF_10'))
      | ~ v1_relat_1(k2_funct_1('#skF_10'))
      | ~ r2_hidden(k4_tarski(D_85,C_84),'#skF_10') ) ),
    inference(resolution,[status(thm)],[c_160,c_42])).

tff(c_176,plain,(
    ! [C_84,D_85] :
      ( k1_funct_1(k2_funct_1('#skF_10'),C_84) = D_85
      | ~ v1_funct_1(k2_funct_1('#skF_10'))
      | ~ r2_hidden(k4_tarski(D_85,C_84),'#skF_10') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_166])).

tff(c_425,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_10')) ),
    inference(splitLeft,[status(thm)],[c_176])).

tff(c_451,plain,
    ( ~ v1_funct_1('#skF_10')
    | ~ v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_34,c_425])).

tff(c_455,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_451])).

tff(c_458,plain,(
    ! [C_107,D_108] :
      ( k1_funct_1(k2_funct_1('#skF_10'),C_107) = D_108
      | ~ r2_hidden(k4_tarski(D_108,C_107),'#skF_10') ) ),
    inference(splitRight,[status(thm)],[c_176])).

tff(c_540,plain,(
    ! [C_115] :
      ( k1_funct_1(k2_funct_1('#skF_10'),C_115) = '#skF_4'('#skF_10',k2_relat_1('#skF_10'),C_115)
      | ~ r2_hidden(C_115,k2_relat_1('#skF_10')) ) ),
    inference(resolution,[status(thm)],[c_2,c_458])).

tff(c_571,plain,(
    k1_funct_1(k2_funct_1('#skF_10'),'#skF_9') = '#skF_4'('#skF_10',k2_relat_1('#skF_10'),'#skF_9') ),
    inference(resolution,[status(thm)],[c_48,c_540])).

tff(c_46,plain,
    ( k1_funct_1(k5_relat_1(k2_funct_1('#skF_10'),'#skF_10'),'#skF_9') != '#skF_9'
    | k1_funct_1('#skF_10',k1_funct_1(k2_funct_1('#skF_10'),'#skF_9')) != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_66,plain,(
    k1_funct_1('#skF_10',k1_funct_1(k2_funct_1('#skF_10'),'#skF_9')) != '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_572,plain,(
    k1_funct_1('#skF_10','#skF_4'('#skF_10',k2_relat_1('#skF_10'),'#skF_9')) != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_571,c_66])).

tff(c_30,plain,(
    ! [A_38,C_40,B_39] :
      ( r2_hidden(A_38,k1_relat_1(C_40))
      | ~ r2_hidden(k4_tarski(A_38,B_39),C_40)
      | ~ v1_relat_1(C_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_169,plain,(
    ! [C_84,D_85] :
      ( r2_hidden(C_84,k1_relat_1(k2_funct_1('#skF_10')))
      | ~ v1_relat_1(k2_funct_1('#skF_10'))
      | ~ r2_hidden(k4_tarski(D_85,C_84),'#skF_10') ) ),
    inference(resolution,[status(thm)],[c_160,c_30])).

tff(c_204,plain,(
    ! [C_88,D_89] :
      ( r2_hidden(C_88,k1_relat_1(k2_funct_1('#skF_10')))
      | ~ r2_hidden(k4_tarski(D_89,C_88),'#skF_10') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_169])).

tff(c_218,plain,(
    ! [C_16] :
      ( r2_hidden(C_16,k1_relat_1(k2_funct_1('#skF_10')))
      | ~ r2_hidden(C_16,k2_relat_1('#skF_10')) ) ),
    inference(resolution,[status(thm)],[c_2,c_204])).

tff(c_457,plain,(
    v1_funct_1(k2_funct_1('#skF_10')) ),
    inference(splitRight,[status(thm)],[c_176])).

tff(c_93,plain,(
    ! [A_69,C_70] :
      ( r2_hidden(k4_tarski(A_69,k1_funct_1(C_70,A_69)),C_70)
      | ~ r2_hidden(A_69,k1_relat_1(C_70))
      | ~ v1_funct_1(C_70)
      | ~ v1_relat_1(C_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_4,plain,(
    ! [C_16,A_1,D_19] :
      ( r2_hidden(C_16,k2_relat_1(A_1))
      | ~ r2_hidden(k4_tarski(D_19,C_16),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_106,plain,(
    ! [C_70,A_69] :
      ( r2_hidden(k1_funct_1(C_70,A_69),k2_relat_1(C_70))
      | ~ r2_hidden(A_69,k1_relat_1(C_70))
      | ~ v1_funct_1(C_70)
      | ~ v1_relat_1(C_70) ) ),
    inference(resolution,[status(thm)],[c_93,c_4])).

tff(c_576,plain,
    ( r2_hidden('#skF_4'('#skF_10',k2_relat_1('#skF_10'),'#skF_9'),k2_relat_1(k2_funct_1('#skF_10')))
    | ~ r2_hidden('#skF_9',k1_relat_1(k2_funct_1('#skF_10')))
    | ~ v1_funct_1(k2_funct_1('#skF_10'))
    | ~ v1_relat_1(k2_funct_1('#skF_10')) ),
    inference(superposition,[status(thm),theory(equality)],[c_571,c_106])).

tff(c_583,plain,
    ( r2_hidden('#skF_4'('#skF_10',k2_relat_1('#skF_10'),'#skF_9'),k2_relat_1(k2_funct_1('#skF_10')))
    | ~ r2_hidden('#skF_9',k1_relat_1(k2_funct_1('#skF_10'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_457,c_576])).

tff(c_613,plain,(
    ~ r2_hidden('#skF_9',k1_relat_1(k2_funct_1('#skF_10'))) ),
    inference(splitLeft,[status(thm)],[c_583])).

tff(c_616,plain,(
    ~ r2_hidden('#skF_9',k2_relat_1('#skF_10')) ),
    inference(resolution,[status(thm)],[c_218,c_613])).

tff(c_620,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_616])).

tff(c_622,plain,(
    r2_hidden('#skF_9',k1_relat_1(k2_funct_1('#skF_10'))) ),
    inference(splitRight,[status(thm)],[c_583])).

tff(c_40,plain,(
    ! [A_47,C_49] :
      ( r2_hidden(k4_tarski(A_47,k1_funct_1(C_49,A_47)),C_49)
      | ~ r2_hidden(A_47,k1_relat_1(C_49))
      | ~ v1_funct_1(C_49)
      | ~ v1_relat_1(C_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_579,plain,
    ( r2_hidden(k4_tarski('#skF_9','#skF_4'('#skF_10',k2_relat_1('#skF_10'),'#skF_9')),k2_funct_1('#skF_10'))
    | ~ r2_hidden('#skF_9',k1_relat_1(k2_funct_1('#skF_10')))
    | ~ v1_funct_1(k2_funct_1('#skF_10'))
    | ~ v1_relat_1(k2_funct_1('#skF_10')) ),
    inference(superposition,[status(thm),theory(equality)],[c_571,c_40])).

tff(c_585,plain,
    ( r2_hidden(k4_tarski('#skF_9','#skF_4'('#skF_10',k2_relat_1('#skF_10'),'#skF_9')),k2_funct_1('#skF_10'))
    | ~ r2_hidden('#skF_9',k1_relat_1(k2_funct_1('#skF_10'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_457,c_579])).

tff(c_799,plain,(
    r2_hidden(k4_tarski('#skF_9','#skF_4'('#skF_10',k2_relat_1('#skF_10'),'#skF_9')),k2_funct_1('#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_622,c_585])).

tff(c_109,plain,(
    ! [D_76,C_77,A_78] :
      ( r2_hidden(k4_tarski(D_76,C_77),A_78)
      | ~ r2_hidden(k4_tarski(C_77,D_76),k4_relat_1(A_78))
      | ~ v1_relat_1(k4_relat_1(A_78))
      | ~ v1_relat_1(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_120,plain,(
    ! [D_76,C_77] :
      ( r2_hidden(k4_tarski(D_76,C_77),'#skF_10')
      | ~ r2_hidden(k4_tarski(C_77,D_76),k2_funct_1('#skF_10'))
      | ~ v1_relat_1(k4_relat_1('#skF_10'))
      | ~ v1_relat_1('#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_65,c_109])).

tff(c_124,plain,(
    ! [D_76,C_77] :
      ( r2_hidden(k4_tarski(D_76,C_77),'#skF_10')
      | ~ r2_hidden(k4_tarski(C_77,D_76),k2_funct_1('#skF_10')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_74,c_65,c_120])).

tff(c_812,plain,(
    r2_hidden(k4_tarski('#skF_4'('#skF_10',k2_relat_1('#skF_10'),'#skF_9'),'#skF_9'),'#skF_10') ),
    inference(resolution,[status(thm)],[c_799,c_124])).

tff(c_830,plain,
    ( k1_funct_1('#skF_10','#skF_4'('#skF_10',k2_relat_1('#skF_10'),'#skF_9')) = '#skF_9'
    | ~ v1_funct_1('#skF_10')
    | ~ v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_812,c_42])).

tff(c_845,plain,(
    k1_funct_1('#skF_10','#skF_4'('#skF_10',k2_relat_1('#skF_10'),'#skF_9')) = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_830])).

tff(c_847,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_572,c_845])).

tff(c_849,plain,(
    k1_funct_1('#skF_10',k1_funct_1(k2_funct_1('#skF_10'),'#skF_9')) = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_1804,plain,(
    k1_funct_1('#skF_10','#skF_4'('#skF_10',k2_relat_1('#skF_10'),'#skF_9')) = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1800,c_849])).

tff(c_1687,plain,(
    v1_funct_1(k2_funct_1('#skF_10')) ),
    inference(splitRight,[status(thm)],[c_1442])).

tff(c_865,plain,(
    ! [A_128,C_129] :
      ( r2_hidden(k4_tarski('#skF_4'(A_128,k2_relat_1(A_128),C_129),C_129),A_128)
      | ~ r2_hidden(C_129,k2_relat_1(A_128)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_872,plain,(
    ! [A_128,C_129] :
      ( r2_hidden('#skF_4'(A_128,k2_relat_1(A_128),C_129),k1_relat_1(A_128))
      | ~ v1_relat_1(A_128)
      | ~ r2_hidden(C_129,k2_relat_1(A_128)) ) ),
    inference(resolution,[status(thm)],[c_865,c_30])).

tff(c_936,plain,(
    ! [C_147,D_148,A_149] :
      ( r2_hidden(k4_tarski(C_147,D_148),k4_relat_1(A_149))
      | ~ r2_hidden(k4_tarski(D_148,C_147),A_149)
      | ~ v1_relat_1(k4_relat_1(A_149))
      | ~ v1_relat_1(A_149) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_951,plain,(
    ! [C_147,D_148] :
      ( r2_hidden(k4_tarski(C_147,D_148),k2_funct_1('#skF_10'))
      | ~ r2_hidden(k4_tarski(D_148,C_147),'#skF_10')
      | ~ v1_relat_1(k4_relat_1('#skF_10'))
      | ~ v1_relat_1('#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_65,c_936])).

tff(c_958,plain,(
    ! [C_150,D_151] :
      ( r2_hidden(k4_tarski(C_150,D_151),k2_funct_1('#skF_10'))
      | ~ r2_hidden(k4_tarski(D_151,C_150),'#skF_10') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_857,c_65,c_951])).

tff(c_964,plain,(
    ! [C_150,D_151] :
      ( k1_funct_1(k2_funct_1('#skF_10'),C_150) = D_151
      | ~ v1_funct_1(k2_funct_1('#skF_10'))
      | ~ v1_relat_1(k2_funct_1('#skF_10'))
      | ~ r2_hidden(k4_tarski(D_151,C_150),'#skF_10') ) ),
    inference(resolution,[status(thm)],[c_958,c_42])).

tff(c_974,plain,(
    ! [C_150,D_151] :
      ( k1_funct_1(k2_funct_1('#skF_10'),C_150) = D_151
      | ~ v1_funct_1(k2_funct_1('#skF_10'))
      | ~ r2_hidden(k4_tarski(D_151,C_150),'#skF_10') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_857,c_964])).

tff(c_1197,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_10')) ),
    inference(splitLeft,[status(thm)],[c_974])).

tff(c_1200,plain,
    ( ~ v1_funct_1('#skF_10')
    | ~ v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_34,c_1197])).

tff(c_1204,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_1200])).

tff(c_1207,plain,(
    ! [C_169,D_170] :
      ( k1_funct_1(k2_funct_1('#skF_10'),C_169) = D_170
      | ~ r2_hidden(k4_tarski(D_170,C_169),'#skF_10') ) ),
    inference(splitRight,[status(thm)],[c_974])).

tff(c_1280,plain,(
    ! [C_175] :
      ( k1_funct_1(k2_funct_1('#skF_10'),C_175) = '#skF_4'('#skF_10',k2_relat_1('#skF_10'),C_175)
      | ~ r2_hidden(C_175,k2_relat_1('#skF_10')) ) ),
    inference(resolution,[status(thm)],[c_2,c_1207])).

tff(c_1311,plain,(
    k1_funct_1(k2_funct_1('#skF_10'),'#skF_9') = '#skF_4'('#skF_10',k2_relat_1('#skF_10'),'#skF_9') ),
    inference(resolution,[status(thm)],[c_48,c_1280])).

tff(c_879,plain,(
    ! [A_133,C_134] :
      ( r2_hidden(k4_tarski(A_133,k1_funct_1(C_134,A_133)),C_134)
      | ~ r2_hidden(A_133,k1_relat_1(C_134))
      | ~ v1_funct_1(C_134)
      | ~ v1_relat_1(C_134) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_891,plain,
    ( r2_hidden(k4_tarski(k1_funct_1(k2_funct_1('#skF_10'),'#skF_9'),'#skF_9'),'#skF_10')
    | ~ r2_hidden(k1_funct_1(k2_funct_1('#skF_10'),'#skF_9'),k1_relat_1('#skF_10'))
    | ~ v1_funct_1('#skF_10')
    | ~ v1_relat_1('#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_849,c_879])).

tff(c_897,plain,
    ( r2_hidden(k4_tarski(k1_funct_1(k2_funct_1('#skF_10'),'#skF_9'),'#skF_9'),'#skF_10')
    | ~ r2_hidden(k1_funct_1(k2_funct_1('#skF_10'),'#skF_9'),k1_relat_1('#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_891])).

tff(c_906,plain,(
    ~ r2_hidden(k1_funct_1(k2_funct_1('#skF_10'),'#skF_9'),k1_relat_1('#skF_10')) ),
    inference(splitLeft,[status(thm)],[c_897])).

tff(c_1312,plain,(
    ~ r2_hidden('#skF_4'('#skF_10',k2_relat_1('#skF_10'),'#skF_9'),k1_relat_1('#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1311,c_906])).

tff(c_1351,plain,
    ( ~ v1_relat_1('#skF_10')
    | ~ r2_hidden('#skF_9',k2_relat_1('#skF_10')) ),
    inference(resolution,[status(thm)],[c_872,c_1312])).

tff(c_1355,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_54,c_1351])).

tff(c_1356,plain,(
    r2_hidden(k4_tarski(k1_funct_1(k2_funct_1('#skF_10'),'#skF_9'),'#skF_9'),'#skF_10') ),
    inference(splitRight,[status(thm)],[c_897])).

tff(c_1435,plain,(
    ! [C_184,D_185] :
      ( r2_hidden(C_184,k1_relat_1(k2_funct_1('#skF_10')))
      | ~ v1_relat_1(k2_funct_1('#skF_10'))
      | ~ r2_hidden(k4_tarski(D_185,C_184),'#skF_10') ) ),
    inference(resolution,[status(thm)],[c_1426,c_30])).

tff(c_1447,plain,(
    ! [C_186,D_187] :
      ( r2_hidden(C_186,k1_relat_1(k2_funct_1('#skF_10')))
      | ~ r2_hidden(k4_tarski(D_187,C_186),'#skF_10') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_857,c_1435])).

tff(c_1456,plain,(
    r2_hidden('#skF_9',k1_relat_1(k2_funct_1('#skF_10'))) ),
    inference(resolution,[status(thm)],[c_1356,c_1447])).

tff(c_1877,plain,(
    ! [B_210,C_211,A_212] :
      ( k1_funct_1(k5_relat_1(B_210,C_211),A_212) = k1_funct_1(C_211,k1_funct_1(B_210,A_212))
      | ~ r2_hidden(A_212,k1_relat_1(B_210))
      | ~ v1_funct_1(C_211)
      | ~ v1_relat_1(C_211)
      | ~ v1_funct_1(B_210)
      | ~ v1_relat_1(B_210) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_1888,plain,(
    ! [C_211] :
      ( k1_funct_1(k5_relat_1(k2_funct_1('#skF_10'),C_211),'#skF_9') = k1_funct_1(C_211,k1_funct_1(k2_funct_1('#skF_10'),'#skF_9'))
      | ~ v1_funct_1(C_211)
      | ~ v1_relat_1(C_211)
      | ~ v1_funct_1(k2_funct_1('#skF_10'))
      | ~ v1_relat_1(k2_funct_1('#skF_10')) ) ),
    inference(resolution,[status(thm)],[c_1456,c_1877])).

tff(c_6504,plain,(
    ! [C_346] :
      ( k1_funct_1(k5_relat_1(k2_funct_1('#skF_10'),C_346),'#skF_9') = k1_funct_1(C_346,'#skF_4'('#skF_10',k2_relat_1('#skF_10'),'#skF_9'))
      | ~ v1_funct_1(C_346)
      | ~ v1_relat_1(C_346) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_857,c_1687,c_1800,c_1888])).

tff(c_848,plain,(
    k1_funct_1(k5_relat_1(k2_funct_1('#skF_10'),'#skF_10'),'#skF_9') != '#skF_9' ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_6516,plain,
    ( k1_funct_1('#skF_10','#skF_4'('#skF_10',k2_relat_1('#skF_10'),'#skF_9')) != '#skF_9'
    | ~ v1_funct_1('#skF_10')
    | ~ v1_relat_1('#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_6504,c_848])).

tff(c_6523,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_1804,c_6516])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 21:00:34 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.86/2.44  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.86/2.45  
% 6.86/2.45  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.86/2.46  %$ r2_hidden > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > k4_tarski > k1_funct_1 > #nlpp > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_6 > #skF_4 > #skF_3 > #skF_10 > #skF_8 > #skF_9 > #skF_2 > #skF_7 > #skF_1 > #skF_5
% 6.86/2.46  
% 6.86/2.46  %Foreground sorts:
% 6.86/2.46  
% 6.86/2.46  
% 6.86/2.46  %Background operators:
% 6.86/2.46  
% 6.86/2.46  
% 6.86/2.46  %Foreground operators:
% 6.86/2.46  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 6.86/2.46  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.86/2.46  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 6.86/2.46  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 6.86/2.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.86/2.46  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.86/2.46  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 6.86/2.46  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 6.86/2.46  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 6.86/2.46  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 6.86/2.46  tff('#skF_10', type, '#skF_10': $i).
% 6.86/2.46  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.86/2.46  tff('#skF_8', type, '#skF_8': ($i * $i) > $i).
% 6.86/2.46  tff('#skF_9', type, '#skF_9': $i).
% 6.86/2.46  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 6.86/2.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.86/2.46  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.86/2.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.86/2.46  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 6.86/2.46  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 6.86/2.46  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 6.86/2.46  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 6.86/2.46  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.86/2.46  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 6.86/2.46  
% 7.24/2.48  tff(f_109, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v2_funct_1(B) & r2_hidden(A, k2_relat_1(B))) => ((A = k1_funct_1(B, k1_funct_1(k2_funct_1(B), A))) & (A = k1_funct_1(k5_relat_1(k2_funct_1(B), B), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t57_funct_1)).
% 7.24/2.48  tff(f_33, axiom, (![A, B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(D, C), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_relat_1)).
% 7.24/2.48  tff(f_73, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 7.24/2.48  tff(f_65, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(A) = k4_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_funct_1)).
% 7.24/2.48  tff(f_49, axiom, (![A]: (v1_relat_1(A) => v1_relat_1(k4_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_relat_1)).
% 7.24/2.48  tff(f_45, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => ((B = k4_relat_1(A)) <=> (![C, D]: (r2_hidden(k4_tarski(C, D), B) <=> r2_hidden(k4_tarski(D, C), A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_relat_1)).
% 7.24/2.48  tff(f_96, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_1)).
% 7.24/2.48  tff(f_57, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) => (r2_hidden(A, k1_relat_1(C)) & r2_hidden(B, k2_relat_1(C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_relat_1)).
% 7.24/2.48  tff(f_86, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(B)) => (k1_funct_1(k5_relat_1(B, C), A) = k1_funct_1(C, k1_funct_1(B, A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_funct_1)).
% 7.24/2.48  tff(c_54, plain, (v1_relat_1('#skF_10')), inference(cnfTransformation, [status(thm)], [f_109])).
% 7.24/2.48  tff(c_52, plain, (v1_funct_1('#skF_10')), inference(cnfTransformation, [status(thm)], [f_109])).
% 7.24/2.48  tff(c_48, plain, (r2_hidden('#skF_9', k2_relat_1('#skF_10'))), inference(cnfTransformation, [status(thm)], [f_109])).
% 7.24/2.48  tff(c_2, plain, (![A_1, C_16]: (r2_hidden(k4_tarski('#skF_4'(A_1, k2_relat_1(A_1), C_16), C_16), A_1) | ~r2_hidden(C_16, k2_relat_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 7.24/2.48  tff(c_34, plain, (![A_42]: (v1_funct_1(k2_funct_1(A_42)) | ~v1_funct_1(A_42) | ~v1_relat_1(A_42))), inference(cnfTransformation, [status(thm)], [f_73])).
% 7.24/2.48  tff(c_50, plain, (v2_funct_1('#skF_10')), inference(cnfTransformation, [status(thm)], [f_109])).
% 7.24/2.48  tff(c_59, plain, (![A_56]: (k4_relat_1(A_56)=k2_funct_1(A_56) | ~v2_funct_1(A_56) | ~v1_funct_1(A_56) | ~v1_relat_1(A_56))), inference(cnfTransformation, [status(thm)], [f_65])).
% 7.24/2.48  tff(c_62, plain, (k4_relat_1('#skF_10')=k2_funct_1('#skF_10') | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_50, c_59])).
% 7.24/2.48  tff(c_65, plain, (k4_relat_1('#skF_10')=k2_funct_1('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_62])).
% 7.24/2.48  tff(c_26, plain, (![A_37]: (v1_relat_1(k4_relat_1(A_37)) | ~v1_relat_1(A_37))), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.24/2.48  tff(c_853, plain, (v1_relat_1(k2_funct_1('#skF_10')) | ~v1_relat_1('#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_65, c_26])).
% 7.24/2.48  tff(c_857, plain, (v1_relat_1(k2_funct_1('#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_853])).
% 7.24/2.48  tff(c_1404, plain, (![C_181, D_182, A_183]: (r2_hidden(k4_tarski(C_181, D_182), k4_relat_1(A_183)) | ~r2_hidden(k4_tarski(D_182, C_181), A_183) | ~v1_relat_1(k4_relat_1(A_183)) | ~v1_relat_1(A_183))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.24/2.48  tff(c_1419, plain, (![C_181, D_182]: (r2_hidden(k4_tarski(C_181, D_182), k2_funct_1('#skF_10')) | ~r2_hidden(k4_tarski(D_182, C_181), '#skF_10') | ~v1_relat_1(k4_relat_1('#skF_10')) | ~v1_relat_1('#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_65, c_1404])).
% 7.24/2.48  tff(c_1426, plain, (![C_184, D_185]: (r2_hidden(k4_tarski(C_184, D_185), k2_funct_1('#skF_10')) | ~r2_hidden(k4_tarski(D_185, C_184), '#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_857, c_65, c_1419])).
% 7.24/2.48  tff(c_42, plain, (![C_49, A_47, B_48]: (k1_funct_1(C_49, A_47)=B_48 | ~r2_hidden(k4_tarski(A_47, B_48), C_49) | ~v1_funct_1(C_49) | ~v1_relat_1(C_49))), inference(cnfTransformation, [status(thm)], [f_96])).
% 7.24/2.48  tff(c_1432, plain, (![C_184, D_185]: (k1_funct_1(k2_funct_1('#skF_10'), C_184)=D_185 | ~v1_funct_1(k2_funct_1('#skF_10')) | ~v1_relat_1(k2_funct_1('#skF_10')) | ~r2_hidden(k4_tarski(D_185, C_184), '#skF_10'))), inference(resolution, [status(thm)], [c_1426, c_42])).
% 7.24/2.48  tff(c_1442, plain, (![C_184, D_185]: (k1_funct_1(k2_funct_1('#skF_10'), C_184)=D_185 | ~v1_funct_1(k2_funct_1('#skF_10')) | ~r2_hidden(k4_tarski(D_185, C_184), '#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_857, c_1432])).
% 7.24/2.48  tff(c_1678, plain, (~v1_funct_1(k2_funct_1('#skF_10'))), inference(splitLeft, [status(thm)], [c_1442])).
% 7.24/2.48  tff(c_1681, plain, (~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_34, c_1678])).
% 7.24/2.48  tff(c_1685, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_1681])).
% 7.24/2.48  tff(c_1688, plain, (![C_203, D_204]: (k1_funct_1(k2_funct_1('#skF_10'), C_203)=D_204 | ~r2_hidden(k4_tarski(D_204, C_203), '#skF_10'))), inference(splitRight, [status(thm)], [c_1442])).
% 7.24/2.48  tff(c_1769, plain, (![C_209]: (k1_funct_1(k2_funct_1('#skF_10'), C_209)='#skF_4'('#skF_10', k2_relat_1('#skF_10'), C_209) | ~r2_hidden(C_209, k2_relat_1('#skF_10')))), inference(resolution, [status(thm)], [c_2, c_1688])).
% 7.24/2.48  tff(c_1800, plain, (k1_funct_1(k2_funct_1('#skF_10'), '#skF_9')='#skF_4'('#skF_10', k2_relat_1('#skF_10'), '#skF_9')), inference(resolution, [status(thm)], [c_48, c_1769])).
% 7.24/2.48  tff(c_70, plain, (v1_relat_1(k2_funct_1('#skF_10')) | ~v1_relat_1('#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_65, c_26])).
% 7.24/2.48  tff(c_74, plain, (v1_relat_1(k2_funct_1('#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_70])).
% 7.24/2.48  tff(c_138, plain, (![C_81, D_82, A_83]: (r2_hidden(k4_tarski(C_81, D_82), k4_relat_1(A_83)) | ~r2_hidden(k4_tarski(D_82, C_81), A_83) | ~v1_relat_1(k4_relat_1(A_83)) | ~v1_relat_1(A_83))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.24/2.48  tff(c_153, plain, (![C_81, D_82]: (r2_hidden(k4_tarski(C_81, D_82), k2_funct_1('#skF_10')) | ~r2_hidden(k4_tarski(D_82, C_81), '#skF_10') | ~v1_relat_1(k4_relat_1('#skF_10')) | ~v1_relat_1('#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_65, c_138])).
% 7.24/2.48  tff(c_160, plain, (![C_84, D_85]: (r2_hidden(k4_tarski(C_84, D_85), k2_funct_1('#skF_10')) | ~r2_hidden(k4_tarski(D_85, C_84), '#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_74, c_65, c_153])).
% 7.24/2.48  tff(c_166, plain, (![C_84, D_85]: (k1_funct_1(k2_funct_1('#skF_10'), C_84)=D_85 | ~v1_funct_1(k2_funct_1('#skF_10')) | ~v1_relat_1(k2_funct_1('#skF_10')) | ~r2_hidden(k4_tarski(D_85, C_84), '#skF_10'))), inference(resolution, [status(thm)], [c_160, c_42])).
% 7.24/2.48  tff(c_176, plain, (![C_84, D_85]: (k1_funct_1(k2_funct_1('#skF_10'), C_84)=D_85 | ~v1_funct_1(k2_funct_1('#skF_10')) | ~r2_hidden(k4_tarski(D_85, C_84), '#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_166])).
% 7.24/2.48  tff(c_425, plain, (~v1_funct_1(k2_funct_1('#skF_10'))), inference(splitLeft, [status(thm)], [c_176])).
% 7.24/2.48  tff(c_451, plain, (~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_34, c_425])).
% 7.24/2.48  tff(c_455, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_451])).
% 7.24/2.48  tff(c_458, plain, (![C_107, D_108]: (k1_funct_1(k2_funct_1('#skF_10'), C_107)=D_108 | ~r2_hidden(k4_tarski(D_108, C_107), '#skF_10'))), inference(splitRight, [status(thm)], [c_176])).
% 7.24/2.48  tff(c_540, plain, (![C_115]: (k1_funct_1(k2_funct_1('#skF_10'), C_115)='#skF_4'('#skF_10', k2_relat_1('#skF_10'), C_115) | ~r2_hidden(C_115, k2_relat_1('#skF_10')))), inference(resolution, [status(thm)], [c_2, c_458])).
% 7.24/2.48  tff(c_571, plain, (k1_funct_1(k2_funct_1('#skF_10'), '#skF_9')='#skF_4'('#skF_10', k2_relat_1('#skF_10'), '#skF_9')), inference(resolution, [status(thm)], [c_48, c_540])).
% 7.24/2.48  tff(c_46, plain, (k1_funct_1(k5_relat_1(k2_funct_1('#skF_10'), '#skF_10'), '#skF_9')!='#skF_9' | k1_funct_1('#skF_10', k1_funct_1(k2_funct_1('#skF_10'), '#skF_9'))!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_109])).
% 7.24/2.48  tff(c_66, plain, (k1_funct_1('#skF_10', k1_funct_1(k2_funct_1('#skF_10'), '#skF_9'))!='#skF_9'), inference(splitLeft, [status(thm)], [c_46])).
% 7.24/2.48  tff(c_572, plain, (k1_funct_1('#skF_10', '#skF_4'('#skF_10', k2_relat_1('#skF_10'), '#skF_9'))!='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_571, c_66])).
% 7.24/2.48  tff(c_30, plain, (![A_38, C_40, B_39]: (r2_hidden(A_38, k1_relat_1(C_40)) | ~r2_hidden(k4_tarski(A_38, B_39), C_40) | ~v1_relat_1(C_40))), inference(cnfTransformation, [status(thm)], [f_57])).
% 7.24/2.48  tff(c_169, plain, (![C_84, D_85]: (r2_hidden(C_84, k1_relat_1(k2_funct_1('#skF_10'))) | ~v1_relat_1(k2_funct_1('#skF_10')) | ~r2_hidden(k4_tarski(D_85, C_84), '#skF_10'))), inference(resolution, [status(thm)], [c_160, c_30])).
% 7.24/2.48  tff(c_204, plain, (![C_88, D_89]: (r2_hidden(C_88, k1_relat_1(k2_funct_1('#skF_10'))) | ~r2_hidden(k4_tarski(D_89, C_88), '#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_169])).
% 7.24/2.48  tff(c_218, plain, (![C_16]: (r2_hidden(C_16, k1_relat_1(k2_funct_1('#skF_10'))) | ~r2_hidden(C_16, k2_relat_1('#skF_10')))), inference(resolution, [status(thm)], [c_2, c_204])).
% 7.24/2.48  tff(c_457, plain, (v1_funct_1(k2_funct_1('#skF_10'))), inference(splitRight, [status(thm)], [c_176])).
% 7.24/2.48  tff(c_93, plain, (![A_69, C_70]: (r2_hidden(k4_tarski(A_69, k1_funct_1(C_70, A_69)), C_70) | ~r2_hidden(A_69, k1_relat_1(C_70)) | ~v1_funct_1(C_70) | ~v1_relat_1(C_70))), inference(cnfTransformation, [status(thm)], [f_96])).
% 7.24/2.48  tff(c_4, plain, (![C_16, A_1, D_19]: (r2_hidden(C_16, k2_relat_1(A_1)) | ~r2_hidden(k4_tarski(D_19, C_16), A_1))), inference(cnfTransformation, [status(thm)], [f_33])).
% 7.24/2.48  tff(c_106, plain, (![C_70, A_69]: (r2_hidden(k1_funct_1(C_70, A_69), k2_relat_1(C_70)) | ~r2_hidden(A_69, k1_relat_1(C_70)) | ~v1_funct_1(C_70) | ~v1_relat_1(C_70))), inference(resolution, [status(thm)], [c_93, c_4])).
% 7.24/2.48  tff(c_576, plain, (r2_hidden('#skF_4'('#skF_10', k2_relat_1('#skF_10'), '#skF_9'), k2_relat_1(k2_funct_1('#skF_10'))) | ~r2_hidden('#skF_9', k1_relat_1(k2_funct_1('#skF_10'))) | ~v1_funct_1(k2_funct_1('#skF_10')) | ~v1_relat_1(k2_funct_1('#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_571, c_106])).
% 7.24/2.48  tff(c_583, plain, (r2_hidden('#skF_4'('#skF_10', k2_relat_1('#skF_10'), '#skF_9'), k2_relat_1(k2_funct_1('#skF_10'))) | ~r2_hidden('#skF_9', k1_relat_1(k2_funct_1('#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_457, c_576])).
% 7.24/2.48  tff(c_613, plain, (~r2_hidden('#skF_9', k1_relat_1(k2_funct_1('#skF_10')))), inference(splitLeft, [status(thm)], [c_583])).
% 7.24/2.48  tff(c_616, plain, (~r2_hidden('#skF_9', k2_relat_1('#skF_10'))), inference(resolution, [status(thm)], [c_218, c_613])).
% 7.24/2.48  tff(c_620, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_616])).
% 7.24/2.48  tff(c_622, plain, (r2_hidden('#skF_9', k1_relat_1(k2_funct_1('#skF_10')))), inference(splitRight, [status(thm)], [c_583])).
% 7.24/2.48  tff(c_40, plain, (![A_47, C_49]: (r2_hidden(k4_tarski(A_47, k1_funct_1(C_49, A_47)), C_49) | ~r2_hidden(A_47, k1_relat_1(C_49)) | ~v1_funct_1(C_49) | ~v1_relat_1(C_49))), inference(cnfTransformation, [status(thm)], [f_96])).
% 7.24/2.48  tff(c_579, plain, (r2_hidden(k4_tarski('#skF_9', '#skF_4'('#skF_10', k2_relat_1('#skF_10'), '#skF_9')), k2_funct_1('#skF_10')) | ~r2_hidden('#skF_9', k1_relat_1(k2_funct_1('#skF_10'))) | ~v1_funct_1(k2_funct_1('#skF_10')) | ~v1_relat_1(k2_funct_1('#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_571, c_40])).
% 7.24/2.48  tff(c_585, plain, (r2_hidden(k4_tarski('#skF_9', '#skF_4'('#skF_10', k2_relat_1('#skF_10'), '#skF_9')), k2_funct_1('#skF_10')) | ~r2_hidden('#skF_9', k1_relat_1(k2_funct_1('#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_457, c_579])).
% 7.24/2.48  tff(c_799, plain, (r2_hidden(k4_tarski('#skF_9', '#skF_4'('#skF_10', k2_relat_1('#skF_10'), '#skF_9')), k2_funct_1('#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_622, c_585])).
% 7.24/2.48  tff(c_109, plain, (![D_76, C_77, A_78]: (r2_hidden(k4_tarski(D_76, C_77), A_78) | ~r2_hidden(k4_tarski(C_77, D_76), k4_relat_1(A_78)) | ~v1_relat_1(k4_relat_1(A_78)) | ~v1_relat_1(A_78))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.24/2.48  tff(c_120, plain, (![D_76, C_77]: (r2_hidden(k4_tarski(D_76, C_77), '#skF_10') | ~r2_hidden(k4_tarski(C_77, D_76), k2_funct_1('#skF_10')) | ~v1_relat_1(k4_relat_1('#skF_10')) | ~v1_relat_1('#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_65, c_109])).
% 7.24/2.48  tff(c_124, plain, (![D_76, C_77]: (r2_hidden(k4_tarski(D_76, C_77), '#skF_10') | ~r2_hidden(k4_tarski(C_77, D_76), k2_funct_1('#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_74, c_65, c_120])).
% 7.24/2.48  tff(c_812, plain, (r2_hidden(k4_tarski('#skF_4'('#skF_10', k2_relat_1('#skF_10'), '#skF_9'), '#skF_9'), '#skF_10')), inference(resolution, [status(thm)], [c_799, c_124])).
% 7.24/2.48  tff(c_830, plain, (k1_funct_1('#skF_10', '#skF_4'('#skF_10', k2_relat_1('#skF_10'), '#skF_9'))='#skF_9' | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_812, c_42])).
% 7.24/2.48  tff(c_845, plain, (k1_funct_1('#skF_10', '#skF_4'('#skF_10', k2_relat_1('#skF_10'), '#skF_9'))='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_830])).
% 7.24/2.48  tff(c_847, plain, $false, inference(negUnitSimplification, [status(thm)], [c_572, c_845])).
% 7.24/2.48  tff(c_849, plain, (k1_funct_1('#skF_10', k1_funct_1(k2_funct_1('#skF_10'), '#skF_9'))='#skF_9'), inference(splitRight, [status(thm)], [c_46])).
% 7.24/2.48  tff(c_1804, plain, (k1_funct_1('#skF_10', '#skF_4'('#skF_10', k2_relat_1('#skF_10'), '#skF_9'))='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_1800, c_849])).
% 7.24/2.48  tff(c_1687, plain, (v1_funct_1(k2_funct_1('#skF_10'))), inference(splitRight, [status(thm)], [c_1442])).
% 7.24/2.48  tff(c_865, plain, (![A_128, C_129]: (r2_hidden(k4_tarski('#skF_4'(A_128, k2_relat_1(A_128), C_129), C_129), A_128) | ~r2_hidden(C_129, k2_relat_1(A_128)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 7.24/2.48  tff(c_872, plain, (![A_128, C_129]: (r2_hidden('#skF_4'(A_128, k2_relat_1(A_128), C_129), k1_relat_1(A_128)) | ~v1_relat_1(A_128) | ~r2_hidden(C_129, k2_relat_1(A_128)))), inference(resolution, [status(thm)], [c_865, c_30])).
% 7.24/2.48  tff(c_936, plain, (![C_147, D_148, A_149]: (r2_hidden(k4_tarski(C_147, D_148), k4_relat_1(A_149)) | ~r2_hidden(k4_tarski(D_148, C_147), A_149) | ~v1_relat_1(k4_relat_1(A_149)) | ~v1_relat_1(A_149))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.24/2.48  tff(c_951, plain, (![C_147, D_148]: (r2_hidden(k4_tarski(C_147, D_148), k2_funct_1('#skF_10')) | ~r2_hidden(k4_tarski(D_148, C_147), '#skF_10') | ~v1_relat_1(k4_relat_1('#skF_10')) | ~v1_relat_1('#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_65, c_936])).
% 7.24/2.48  tff(c_958, plain, (![C_150, D_151]: (r2_hidden(k4_tarski(C_150, D_151), k2_funct_1('#skF_10')) | ~r2_hidden(k4_tarski(D_151, C_150), '#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_857, c_65, c_951])).
% 7.24/2.48  tff(c_964, plain, (![C_150, D_151]: (k1_funct_1(k2_funct_1('#skF_10'), C_150)=D_151 | ~v1_funct_1(k2_funct_1('#skF_10')) | ~v1_relat_1(k2_funct_1('#skF_10')) | ~r2_hidden(k4_tarski(D_151, C_150), '#skF_10'))), inference(resolution, [status(thm)], [c_958, c_42])).
% 7.24/2.48  tff(c_974, plain, (![C_150, D_151]: (k1_funct_1(k2_funct_1('#skF_10'), C_150)=D_151 | ~v1_funct_1(k2_funct_1('#skF_10')) | ~r2_hidden(k4_tarski(D_151, C_150), '#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_857, c_964])).
% 7.24/2.48  tff(c_1197, plain, (~v1_funct_1(k2_funct_1('#skF_10'))), inference(splitLeft, [status(thm)], [c_974])).
% 7.24/2.48  tff(c_1200, plain, (~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_34, c_1197])).
% 7.24/2.48  tff(c_1204, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_1200])).
% 7.24/2.48  tff(c_1207, plain, (![C_169, D_170]: (k1_funct_1(k2_funct_1('#skF_10'), C_169)=D_170 | ~r2_hidden(k4_tarski(D_170, C_169), '#skF_10'))), inference(splitRight, [status(thm)], [c_974])).
% 7.24/2.48  tff(c_1280, plain, (![C_175]: (k1_funct_1(k2_funct_1('#skF_10'), C_175)='#skF_4'('#skF_10', k2_relat_1('#skF_10'), C_175) | ~r2_hidden(C_175, k2_relat_1('#skF_10')))), inference(resolution, [status(thm)], [c_2, c_1207])).
% 7.24/2.48  tff(c_1311, plain, (k1_funct_1(k2_funct_1('#skF_10'), '#skF_9')='#skF_4'('#skF_10', k2_relat_1('#skF_10'), '#skF_9')), inference(resolution, [status(thm)], [c_48, c_1280])).
% 7.24/2.48  tff(c_879, plain, (![A_133, C_134]: (r2_hidden(k4_tarski(A_133, k1_funct_1(C_134, A_133)), C_134) | ~r2_hidden(A_133, k1_relat_1(C_134)) | ~v1_funct_1(C_134) | ~v1_relat_1(C_134))), inference(cnfTransformation, [status(thm)], [f_96])).
% 7.24/2.48  tff(c_891, plain, (r2_hidden(k4_tarski(k1_funct_1(k2_funct_1('#skF_10'), '#skF_9'), '#skF_9'), '#skF_10') | ~r2_hidden(k1_funct_1(k2_funct_1('#skF_10'), '#skF_9'), k1_relat_1('#skF_10')) | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_849, c_879])).
% 7.24/2.48  tff(c_897, plain, (r2_hidden(k4_tarski(k1_funct_1(k2_funct_1('#skF_10'), '#skF_9'), '#skF_9'), '#skF_10') | ~r2_hidden(k1_funct_1(k2_funct_1('#skF_10'), '#skF_9'), k1_relat_1('#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_891])).
% 7.24/2.48  tff(c_906, plain, (~r2_hidden(k1_funct_1(k2_funct_1('#skF_10'), '#skF_9'), k1_relat_1('#skF_10'))), inference(splitLeft, [status(thm)], [c_897])).
% 7.24/2.48  tff(c_1312, plain, (~r2_hidden('#skF_4'('#skF_10', k2_relat_1('#skF_10'), '#skF_9'), k1_relat_1('#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_1311, c_906])).
% 7.24/2.48  tff(c_1351, plain, (~v1_relat_1('#skF_10') | ~r2_hidden('#skF_9', k2_relat_1('#skF_10'))), inference(resolution, [status(thm)], [c_872, c_1312])).
% 7.24/2.48  tff(c_1355, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_54, c_1351])).
% 7.24/2.48  tff(c_1356, plain, (r2_hidden(k4_tarski(k1_funct_1(k2_funct_1('#skF_10'), '#skF_9'), '#skF_9'), '#skF_10')), inference(splitRight, [status(thm)], [c_897])).
% 7.24/2.48  tff(c_1435, plain, (![C_184, D_185]: (r2_hidden(C_184, k1_relat_1(k2_funct_1('#skF_10'))) | ~v1_relat_1(k2_funct_1('#skF_10')) | ~r2_hidden(k4_tarski(D_185, C_184), '#skF_10'))), inference(resolution, [status(thm)], [c_1426, c_30])).
% 7.24/2.48  tff(c_1447, plain, (![C_186, D_187]: (r2_hidden(C_186, k1_relat_1(k2_funct_1('#skF_10'))) | ~r2_hidden(k4_tarski(D_187, C_186), '#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_857, c_1435])).
% 7.24/2.48  tff(c_1456, plain, (r2_hidden('#skF_9', k1_relat_1(k2_funct_1('#skF_10')))), inference(resolution, [status(thm)], [c_1356, c_1447])).
% 7.24/2.48  tff(c_1877, plain, (![B_210, C_211, A_212]: (k1_funct_1(k5_relat_1(B_210, C_211), A_212)=k1_funct_1(C_211, k1_funct_1(B_210, A_212)) | ~r2_hidden(A_212, k1_relat_1(B_210)) | ~v1_funct_1(C_211) | ~v1_relat_1(C_211) | ~v1_funct_1(B_210) | ~v1_relat_1(B_210))), inference(cnfTransformation, [status(thm)], [f_86])).
% 7.24/2.48  tff(c_1888, plain, (![C_211]: (k1_funct_1(k5_relat_1(k2_funct_1('#skF_10'), C_211), '#skF_9')=k1_funct_1(C_211, k1_funct_1(k2_funct_1('#skF_10'), '#skF_9')) | ~v1_funct_1(C_211) | ~v1_relat_1(C_211) | ~v1_funct_1(k2_funct_1('#skF_10')) | ~v1_relat_1(k2_funct_1('#skF_10')))), inference(resolution, [status(thm)], [c_1456, c_1877])).
% 7.24/2.48  tff(c_6504, plain, (![C_346]: (k1_funct_1(k5_relat_1(k2_funct_1('#skF_10'), C_346), '#skF_9')=k1_funct_1(C_346, '#skF_4'('#skF_10', k2_relat_1('#skF_10'), '#skF_9')) | ~v1_funct_1(C_346) | ~v1_relat_1(C_346))), inference(demodulation, [status(thm), theory('equality')], [c_857, c_1687, c_1800, c_1888])).
% 7.24/2.48  tff(c_848, plain, (k1_funct_1(k5_relat_1(k2_funct_1('#skF_10'), '#skF_10'), '#skF_9')!='#skF_9'), inference(splitRight, [status(thm)], [c_46])).
% 7.24/2.48  tff(c_6516, plain, (k1_funct_1('#skF_10', '#skF_4'('#skF_10', k2_relat_1('#skF_10'), '#skF_9'))!='#skF_9' | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_6504, c_848])).
% 7.24/2.48  tff(c_6523, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_1804, c_6516])).
% 7.24/2.48  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.24/2.48  
% 7.24/2.48  Inference rules
% 7.24/2.48  ----------------------
% 7.24/2.48  #Ref     : 0
% 7.24/2.48  #Sup     : 1352
% 7.24/2.48  #Fact    : 0
% 7.24/2.48  #Define  : 0
% 7.24/2.48  #Split   : 10
% 7.24/2.48  #Chain   : 0
% 7.24/2.48  #Close   : 0
% 7.24/2.48  
% 7.24/2.48  Ordering : KBO
% 7.24/2.48  
% 7.24/2.48  Simplification rules
% 7.24/2.48  ----------------------
% 7.24/2.48  #Subsume      : 133
% 7.24/2.48  #Demod        : 642
% 7.24/2.48  #Tautology    : 193
% 7.24/2.48  #SimpNegUnit  : 1
% 7.24/2.48  #BackRed      : 7
% 7.24/2.48  
% 7.24/2.48  #Partial instantiations: 0
% 7.24/2.48  #Strategies tried      : 1
% 7.24/2.48  
% 7.24/2.48  Timing (in seconds)
% 7.24/2.48  ----------------------
% 7.24/2.48  Preprocessing        : 0.32
% 7.24/2.48  Parsing              : 0.16
% 7.24/2.48  CNF conversion       : 0.03
% 7.24/2.48  Main loop            : 1.32
% 7.24/2.48  Inferencing          : 0.48
% 7.24/2.48  Reduction            : 0.37
% 7.24/2.48  Demodulation         : 0.26
% 7.24/2.48  BG Simplification    : 0.06
% 7.24/2.48  Subsumption          : 0.29
% 7.24/2.48  Abstraction          : 0.08
% 7.24/2.48  MUC search           : 0.00
% 7.24/2.48  Cooper               : 0.00
% 7.24/2.48  Total                : 1.68
% 7.24/2.48  Index Insertion      : 0.00
% 7.24/2.48  Index Deletion       : 0.00
% 7.24/2.48  Index Matching       : 0.00
% 7.24/2.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
