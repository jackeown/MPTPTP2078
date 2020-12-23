%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0619+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:35 EST 2020

% Result     : Theorem 4.08s
% Output     : CNFRefutation 4.08s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 579 expanded)
%              Number of leaves         :   21 ( 221 expanded)
%              Depth                    :   31
%              Number of atoms          :  189 (1802 expanded)
%              Number of equality atoms :   83 ( 768 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > v1_funct_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > #skF_6 > #skF_7 > #skF_3 > #skF_8 > #skF_2 > #skF_1 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_55,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ( k1_relat_1(B) = k1_tarski(A)
         => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_46,axiom,(
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

tff(c_34,plain,(
    k1_tarski('#skF_7') = k1_relat_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_4,plain,(
    ! [C_5] : r2_hidden(C_5,k1_tarski(C_5)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_43,plain,(
    r2_hidden('#skF_7',k1_relat_1('#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_4])).

tff(c_32,plain,(
    k1_tarski(k1_funct_1('#skF_8','#skF_7')) != k2_relat_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_38,plain,(
    v1_relat_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_36,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_621,plain,(
    ! [A_89,B_90] :
      ( k1_funct_1(A_89,'#skF_4'(A_89,B_90)) = '#skF_3'(A_89,B_90)
      | r2_hidden('#skF_5'(A_89,B_90),B_90)
      | k2_relat_1(A_89) = B_90
      | ~ v1_funct_1(A_89)
      | ~ v1_relat_1(A_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_2,plain,(
    ! [C_5,A_1] :
      ( C_5 = A_1
      | ~ r2_hidden(C_5,k1_tarski(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1428,plain,(
    ! [A_127,A_128] :
      ( '#skF_5'(A_127,k1_tarski(A_128)) = A_128
      | k1_funct_1(A_127,'#skF_4'(A_127,k1_tarski(A_128))) = '#skF_3'(A_127,k1_tarski(A_128))
      | k2_relat_1(A_127) = k1_tarski(A_128)
      | ~ v1_funct_1(A_127)
      | ~ v1_relat_1(A_127) ) ),
    inference(resolution,[status(thm)],[c_621,c_2])).

tff(c_358,plain,(
    ! [A_81,B_82] :
      ( r2_hidden('#skF_4'(A_81,B_82),k1_relat_1(A_81))
      | r2_hidden('#skF_5'(A_81,B_82),B_82)
      | k2_relat_1(A_81) = B_82
      | ~ v1_funct_1(A_81)
      | ~ v1_relat_1(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_14,plain,(
    ! [A_6,D_45] :
      ( r2_hidden(k1_funct_1(A_6,D_45),k2_relat_1(A_6))
      | ~ r2_hidden(D_45,k1_relat_1(A_6))
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_134,plain,(
    ! [A_63,C_64] :
      ( r2_hidden('#skF_6'(A_63,k2_relat_1(A_63),C_64),k1_relat_1(A_63))
      | ~ r2_hidden(C_64,k2_relat_1(A_63))
      | ~ v1_funct_1(A_63)
      | ~ v1_relat_1(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_47,plain,(
    ! [C_47,A_48] :
      ( C_47 = A_48
      | ~ r2_hidden(C_47,k1_tarski(A_48)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_50,plain,(
    ! [C_47] :
      ( C_47 = '#skF_7'
      | ~ r2_hidden(C_47,k1_relat_1('#skF_8')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_47])).

tff(c_138,plain,(
    ! [C_64] :
      ( '#skF_6'('#skF_8',k2_relat_1('#skF_8'),C_64) = '#skF_7'
      | ~ r2_hidden(C_64,k2_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_134,c_50])).

tff(c_142,plain,(
    ! [C_65] :
      ( '#skF_6'('#skF_8',k2_relat_1('#skF_8'),C_65) = '#skF_7'
      | ~ r2_hidden(C_65,k2_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_138])).

tff(c_146,plain,(
    ! [D_45] :
      ( '#skF_6'('#skF_8',k2_relat_1('#skF_8'),k1_funct_1('#skF_8',D_45)) = '#skF_7'
      | ~ r2_hidden(D_45,k1_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_14,c_142])).

tff(c_157,plain,(
    ! [D_45] :
      ( '#skF_6'('#skF_8',k2_relat_1('#skF_8'),k1_funct_1('#skF_8',D_45)) = '#skF_7'
      | ~ r2_hidden(D_45,k1_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_146])).

tff(c_175,plain,(
    ! [A_68,C_69] :
      ( k1_funct_1(A_68,'#skF_6'(A_68,k2_relat_1(A_68),C_69)) = C_69
      | ~ r2_hidden(C_69,k2_relat_1(A_68))
      | ~ v1_funct_1(A_68)
      | ~ v1_relat_1(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_191,plain,(
    ! [D_45] :
      ( k1_funct_1('#skF_8',D_45) = k1_funct_1('#skF_8','#skF_7')
      | ~ r2_hidden(k1_funct_1('#skF_8',D_45),k2_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8')
      | ~ r2_hidden(D_45,k1_relat_1('#skF_8')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_157,c_175])).

tff(c_207,plain,(
    ! [D_72] :
      ( k1_funct_1('#skF_8',D_72) = k1_funct_1('#skF_8','#skF_7')
      | ~ r2_hidden(k1_funct_1('#skF_8',D_72),k2_relat_1('#skF_8'))
      | ~ r2_hidden(D_72,k1_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_191])).

tff(c_215,plain,(
    ! [D_45] :
      ( k1_funct_1('#skF_8',D_45) = k1_funct_1('#skF_8','#skF_7')
      | ~ r2_hidden(D_45,k1_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_14,c_207])).

tff(c_220,plain,(
    ! [D_45] :
      ( k1_funct_1('#skF_8',D_45) = k1_funct_1('#skF_8','#skF_7')
      | ~ r2_hidden(D_45,k1_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_215])).

tff(c_362,plain,(
    ! [B_82] :
      ( k1_funct_1('#skF_8','#skF_4'('#skF_8',B_82)) = k1_funct_1('#skF_8','#skF_7')
      | r2_hidden('#skF_5'('#skF_8',B_82),B_82)
      | k2_relat_1('#skF_8') = B_82
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_358,c_220])).

tff(c_580,plain,(
    ! [B_88] :
      ( k1_funct_1('#skF_8','#skF_4'('#skF_8',B_88)) = k1_funct_1('#skF_8','#skF_7')
      | r2_hidden('#skF_5'('#skF_8',B_88),B_88)
      | k2_relat_1('#skF_8') = B_88 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_362])).

tff(c_617,plain,(
    ! [A_1] :
      ( '#skF_5'('#skF_8',k1_tarski(A_1)) = A_1
      | k1_funct_1('#skF_8','#skF_4'('#skF_8',k1_tarski(A_1))) = k1_funct_1('#skF_8','#skF_7')
      | k2_relat_1('#skF_8') = k1_tarski(A_1) ) ),
    inference(resolution,[status(thm)],[c_580,c_2])).

tff(c_1443,plain,(
    ! [A_128] :
      ( '#skF_5'('#skF_8',k1_tarski(A_128)) = A_128
      | '#skF_3'('#skF_8',k1_tarski(A_128)) = k1_funct_1('#skF_8','#skF_7')
      | k2_relat_1('#skF_8') = k1_tarski(A_128)
      | '#skF_5'('#skF_8',k1_tarski(A_128)) = A_128
      | k2_relat_1('#skF_8') = k1_tarski(A_128)
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1428,c_617])).

tff(c_1487,plain,(
    ! [A_130] :
      ( '#skF_3'('#skF_8',k1_tarski(A_130)) = k1_funct_1('#skF_8','#skF_7')
      | '#skF_5'('#skF_8',k1_tarski(A_130)) = A_130
      | k2_relat_1('#skF_8') = k1_tarski(A_130) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_1443])).

tff(c_26,plain,(
    ! [A_6,B_28] :
      ( ~ r2_hidden('#skF_3'(A_6,B_28),B_28)
      | r2_hidden('#skF_5'(A_6,B_28),B_28)
      | k2_relat_1(A_6) = B_28
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_1498,plain,(
    ! [A_130] :
      ( ~ r2_hidden(k1_funct_1('#skF_8','#skF_7'),k1_tarski(A_130))
      | r2_hidden('#skF_5'('#skF_8',k1_tarski(A_130)),k1_tarski(A_130))
      | k2_relat_1('#skF_8') = k1_tarski(A_130)
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8')
      | '#skF_5'('#skF_8',k1_tarski(A_130)) = A_130
      | k2_relat_1('#skF_8') = k1_tarski(A_130) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1487,c_26])).

tff(c_2160,plain,(
    ! [A_150] :
      ( ~ r2_hidden(k1_funct_1('#skF_8','#skF_7'),k1_tarski(A_150))
      | r2_hidden('#skF_5'('#skF_8',k1_tarski(A_150)),k1_tarski(A_150))
      | '#skF_5'('#skF_8',k1_tarski(A_150)) = A_150
      | k2_relat_1('#skF_8') = k1_tarski(A_150) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_1498])).

tff(c_2179,plain,(
    ! [A_151] :
      ( ~ r2_hidden(k1_funct_1('#skF_8','#skF_7'),k1_tarski(A_151))
      | '#skF_5'('#skF_8',k1_tarski(A_151)) = A_151
      | k2_relat_1('#skF_8') = k1_tarski(A_151) ) ),
    inference(resolution,[status(thm)],[c_2160,c_2])).

tff(c_2186,plain,
    ( '#skF_5'('#skF_8',k1_tarski(k1_funct_1('#skF_8','#skF_7'))) = k1_funct_1('#skF_8','#skF_7')
    | k1_tarski(k1_funct_1('#skF_8','#skF_7')) = k2_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_4,c_2179])).

tff(c_2191,plain,(
    '#skF_5'('#skF_8',k1_tarski(k1_funct_1('#skF_8','#skF_7'))) = k1_funct_1('#skF_8','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_2186])).

tff(c_24,plain,(
    ! [A_6,B_28,D_41] :
      ( r2_hidden('#skF_4'(A_6,B_28),k1_relat_1(A_6))
      | k1_funct_1(A_6,D_41) != '#skF_5'(A_6,B_28)
      | ~ r2_hidden(D_41,k1_relat_1(A_6))
      | k2_relat_1(A_6) = B_28
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_2213,plain,(
    ! [D_41] :
      ( r2_hidden('#skF_4'('#skF_8',k1_tarski(k1_funct_1('#skF_8','#skF_7'))),k1_relat_1('#skF_8'))
      | k1_funct_1('#skF_8',D_41) != k1_funct_1('#skF_8','#skF_7')
      | ~ r2_hidden(D_41,k1_relat_1('#skF_8'))
      | k1_tarski(k1_funct_1('#skF_8','#skF_7')) = k2_relat_1('#skF_8')
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2191,c_24])).

tff(c_2252,plain,(
    ! [D_41] :
      ( r2_hidden('#skF_4'('#skF_8',k1_tarski(k1_funct_1('#skF_8','#skF_7'))),k1_relat_1('#skF_8'))
      | k1_funct_1('#skF_8',D_41) != k1_funct_1('#skF_8','#skF_7')
      | ~ r2_hidden(D_41,k1_relat_1('#skF_8'))
      | k1_tarski(k1_funct_1('#skF_8','#skF_7')) = k2_relat_1('#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_2213])).

tff(c_2253,plain,(
    ! [D_41] :
      ( r2_hidden('#skF_4'('#skF_8',k1_tarski(k1_funct_1('#skF_8','#skF_7'))),k1_relat_1('#skF_8'))
      | k1_funct_1('#skF_8',D_41) != k1_funct_1('#skF_8','#skF_7')
      | ~ r2_hidden(D_41,k1_relat_1('#skF_8')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_2252])).

tff(c_2270,plain,(
    ! [D_152] :
      ( k1_funct_1('#skF_8',D_152) != k1_funct_1('#skF_8','#skF_7')
      | ~ r2_hidden(D_152,k1_relat_1('#skF_8')) ) ),
    inference(splitLeft,[status(thm)],[c_2253])).

tff(c_2406,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_43,c_2270])).

tff(c_2407,plain,(
    r2_hidden('#skF_4'('#skF_8',k1_tarski(k1_funct_1('#skF_8','#skF_7'))),k1_relat_1('#skF_8')) ),
    inference(splitRight,[status(thm)],[c_2253])).

tff(c_2427,plain,(
    '#skF_4'('#skF_8',k1_tarski(k1_funct_1('#skF_8','#skF_7'))) = '#skF_7' ),
    inference(resolution,[status(thm)],[c_2407,c_50])).

tff(c_22,plain,(
    ! [A_6,B_28,D_41] :
      ( k1_funct_1(A_6,'#skF_4'(A_6,B_28)) = '#skF_3'(A_6,B_28)
      | k1_funct_1(A_6,D_41) != '#skF_5'(A_6,B_28)
      | ~ r2_hidden(D_41,k1_relat_1(A_6))
      | k2_relat_1(A_6) = B_28
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_2208,plain,(
    ! [D_41] :
      ( k1_funct_1('#skF_8','#skF_4'('#skF_8',k1_tarski(k1_funct_1('#skF_8','#skF_7')))) = '#skF_3'('#skF_8',k1_tarski(k1_funct_1('#skF_8','#skF_7')))
      | k1_funct_1('#skF_8',D_41) != k1_funct_1('#skF_8','#skF_7')
      | ~ r2_hidden(D_41,k1_relat_1('#skF_8'))
      | k1_tarski(k1_funct_1('#skF_8','#skF_7')) = k2_relat_1('#skF_8')
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2191,c_22])).

tff(c_2247,plain,(
    ! [D_41] :
      ( k1_funct_1('#skF_8','#skF_4'('#skF_8',k1_tarski(k1_funct_1('#skF_8','#skF_7')))) = '#skF_3'('#skF_8',k1_tarski(k1_funct_1('#skF_8','#skF_7')))
      | k1_funct_1('#skF_8',D_41) != k1_funct_1('#skF_8','#skF_7')
      | ~ r2_hidden(D_41,k1_relat_1('#skF_8'))
      | k1_tarski(k1_funct_1('#skF_8','#skF_7')) = k2_relat_1('#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_2208])).

tff(c_2248,plain,(
    ! [D_41] :
      ( k1_funct_1('#skF_8','#skF_4'('#skF_8',k1_tarski(k1_funct_1('#skF_8','#skF_7')))) = '#skF_3'('#skF_8',k1_tarski(k1_funct_1('#skF_8','#skF_7')))
      | k1_funct_1('#skF_8',D_41) != k1_funct_1('#skF_8','#skF_7')
      | ~ r2_hidden(D_41,k1_relat_1('#skF_8')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_2247])).

tff(c_2542,plain,(
    ! [D_41] :
      ( '#skF_3'('#skF_8',k1_tarski(k1_funct_1('#skF_8','#skF_7'))) = k1_funct_1('#skF_8','#skF_7')
      | k1_funct_1('#skF_8',D_41) != k1_funct_1('#skF_8','#skF_7')
      | ~ r2_hidden(D_41,k1_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2427,c_2248])).

tff(c_2544,plain,(
    ! [D_158] :
      ( k1_funct_1('#skF_8',D_158) != k1_funct_1('#skF_8','#skF_7')
      | ~ r2_hidden(D_158,k1_relat_1('#skF_8')) ) ),
    inference(splitLeft,[status(thm)],[c_2542])).

tff(c_2680,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_43,c_2544])).

tff(c_2681,plain,(
    '#skF_3'('#skF_8',k1_tarski(k1_funct_1('#skF_8','#skF_7'))) = k1_funct_1('#skF_8','#skF_7') ),
    inference(splitRight,[status(thm)],[c_2542])).

tff(c_20,plain,(
    ! [A_6,B_28,D_41] :
      ( ~ r2_hidden('#skF_3'(A_6,B_28),B_28)
      | k1_funct_1(A_6,D_41) != '#skF_5'(A_6,B_28)
      | ~ r2_hidden(D_41,k1_relat_1(A_6))
      | k2_relat_1(A_6) = B_28
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_2695,plain,(
    ! [D_41] :
      ( ~ r2_hidden(k1_funct_1('#skF_8','#skF_7'),k1_tarski(k1_funct_1('#skF_8','#skF_7')))
      | k1_funct_1('#skF_8',D_41) != '#skF_5'('#skF_8',k1_tarski(k1_funct_1('#skF_8','#skF_7')))
      | ~ r2_hidden(D_41,k1_relat_1('#skF_8'))
      | k1_tarski(k1_funct_1('#skF_8','#skF_7')) = k2_relat_1('#skF_8')
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2681,c_20])).

tff(c_2712,plain,(
    ! [D_41] :
      ( k1_funct_1('#skF_8',D_41) != k1_funct_1('#skF_8','#skF_7')
      | ~ r2_hidden(D_41,k1_relat_1('#skF_8'))
      | k1_tarski(k1_funct_1('#skF_8','#skF_7')) = k2_relat_1('#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_2191,c_4,c_2695])).

tff(c_2721,plain,(
    ! [D_159] :
      ( k1_funct_1('#skF_8',D_159) != k1_funct_1('#skF_8','#skF_7')
      | ~ r2_hidden(D_159,k1_relat_1('#skF_8')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_2712])).

tff(c_2857,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_43,c_2721])).

%------------------------------------------------------------------------------
