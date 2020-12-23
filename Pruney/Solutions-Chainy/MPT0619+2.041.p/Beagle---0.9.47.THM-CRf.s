%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:57 EST 2020

% Result     : Theorem 3.87s
% Output     : CNFRefutation 3.87s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 581 expanded)
%              Number of leaves         :   23 ( 223 expanded)
%              Depth                    :   31
%              Number of atoms          :  189 (1802 expanded)
%              Number of equality atoms :   83 ( 768 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > v1_funct_1 > k1_enumset1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > #skF_6 > #skF_7 > #skF_3 > #skF_8 > #skF_2 > #skF_1 > #skF_5 > #skF_4

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

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff(f_60,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ( k1_relat_1(B) = k1_tarski(A)
         => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_51,axiom,(
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

tff(c_38,plain,(
    k1_tarski('#skF_7') = k1_relat_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_4,plain,(
    ! [C_5] : r2_hidden(C_5,k1_tarski(C_5)) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_47,plain,(
    r2_hidden('#skF_7',k1_relat_1('#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_4])).

tff(c_36,plain,(
    k1_tarski(k1_funct_1('#skF_8','#skF_7')) != k2_relat_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_42,plain,(
    v1_relat_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_40,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_514,plain,(
    ! [A_90,B_91] :
      ( k1_funct_1(A_90,'#skF_4'(A_90,B_91)) = '#skF_3'(A_90,B_91)
      | r2_hidden('#skF_5'(A_90,B_91),B_91)
      | k2_relat_1(A_90) = B_91
      | ~ v1_funct_1(A_90)
      | ~ v1_relat_1(A_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_2,plain,(
    ! [C_5,A_1] :
      ( C_5 = A_1
      | ~ r2_hidden(C_5,k1_tarski(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1498,plain,(
    ! [A_138,A_139] :
      ( '#skF_5'(A_138,k1_tarski(A_139)) = A_139
      | k1_funct_1(A_138,'#skF_4'(A_138,k1_tarski(A_139))) = '#skF_3'(A_138,k1_tarski(A_139))
      | k2_relat_1(A_138) = k1_tarski(A_139)
      | ~ v1_funct_1(A_138)
      | ~ v1_relat_1(A_138) ) ),
    inference(resolution,[status(thm)],[c_514,c_2])).

tff(c_362,plain,(
    ! [A_86,B_87] :
      ( r2_hidden('#skF_4'(A_86,B_87),k1_relat_1(A_86))
      | r2_hidden('#skF_5'(A_86,B_87),B_87)
      | k2_relat_1(A_86) = B_87
      | ~ v1_funct_1(A_86)
      | ~ v1_relat_1(A_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_18,plain,(
    ! [A_9,D_48] :
      ( r2_hidden(k1_funct_1(A_9,D_48),k2_relat_1(A_9))
      | ~ r2_hidden(D_48,k1_relat_1(A_9))
      | ~ v1_funct_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_109,plain,(
    ! [A_66,C_67] :
      ( r2_hidden('#skF_6'(A_66,k2_relat_1(A_66),C_67),k1_relat_1(A_66))
      | ~ r2_hidden(C_67,k2_relat_1(A_66))
      | ~ v1_funct_1(A_66)
      | ~ v1_relat_1(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_60,plain,(
    ! [C_51,A_52] :
      ( C_51 = A_52
      | ~ r2_hidden(C_51,k1_tarski(A_52)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_63,plain,(
    ! [C_51] :
      ( C_51 = '#skF_7'
      | ~ r2_hidden(C_51,k1_relat_1('#skF_8')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_60])).

tff(c_113,plain,(
    ! [C_67] :
      ( '#skF_6'('#skF_8',k2_relat_1('#skF_8'),C_67) = '#skF_7'
      | ~ r2_hidden(C_67,k2_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_109,c_63])).

tff(c_117,plain,(
    ! [C_68] :
      ( '#skF_6'('#skF_8',k2_relat_1('#skF_8'),C_68) = '#skF_7'
      | ~ r2_hidden(C_68,k2_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_113])).

tff(c_121,plain,(
    ! [D_48] :
      ( '#skF_6'('#skF_8',k2_relat_1('#skF_8'),k1_funct_1('#skF_8',D_48)) = '#skF_7'
      | ~ r2_hidden(D_48,k1_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_18,c_117])).

tff(c_132,plain,(
    ! [D_48] :
      ( '#skF_6'('#skF_8',k2_relat_1('#skF_8'),k1_funct_1('#skF_8',D_48)) = '#skF_7'
      | ~ r2_hidden(D_48,k1_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_121])).

tff(c_196,plain,(
    ! [A_73,C_74] :
      ( k1_funct_1(A_73,'#skF_6'(A_73,k2_relat_1(A_73),C_74)) = C_74
      | ~ r2_hidden(C_74,k2_relat_1(A_73))
      | ~ v1_funct_1(A_73)
      | ~ v1_relat_1(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_212,plain,(
    ! [D_48] :
      ( k1_funct_1('#skF_8',D_48) = k1_funct_1('#skF_8','#skF_7')
      | ~ r2_hidden(k1_funct_1('#skF_8',D_48),k2_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8')
      | ~ r2_hidden(D_48,k1_relat_1('#skF_8')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_132,c_196])).

tff(c_230,plain,(
    ! [D_80] :
      ( k1_funct_1('#skF_8',D_80) = k1_funct_1('#skF_8','#skF_7')
      | ~ r2_hidden(k1_funct_1('#skF_8',D_80),k2_relat_1('#skF_8'))
      | ~ r2_hidden(D_80,k1_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_212])).

tff(c_238,plain,(
    ! [D_48] :
      ( k1_funct_1('#skF_8',D_48) = k1_funct_1('#skF_8','#skF_7')
      | ~ r2_hidden(D_48,k1_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_18,c_230])).

tff(c_243,plain,(
    ! [D_48] :
      ( k1_funct_1('#skF_8',D_48) = k1_funct_1('#skF_8','#skF_7')
      | ~ r2_hidden(D_48,k1_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_238])).

tff(c_366,plain,(
    ! [B_87] :
      ( k1_funct_1('#skF_8','#skF_4'('#skF_8',B_87)) = k1_funct_1('#skF_8','#skF_7')
      | r2_hidden('#skF_5'('#skF_8',B_87),B_87)
      | k2_relat_1('#skF_8') = B_87
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_362,c_243])).

tff(c_589,plain,(
    ! [B_93] :
      ( k1_funct_1('#skF_8','#skF_4'('#skF_8',B_93)) = k1_funct_1('#skF_8','#skF_7')
      | r2_hidden('#skF_5'('#skF_8',B_93),B_93)
      | k2_relat_1('#skF_8') = B_93 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_366])).

tff(c_626,plain,(
    ! [A_1] :
      ( '#skF_5'('#skF_8',k1_tarski(A_1)) = A_1
      | k1_funct_1('#skF_8','#skF_4'('#skF_8',k1_tarski(A_1))) = k1_funct_1('#skF_8','#skF_7')
      | k2_relat_1('#skF_8') = k1_tarski(A_1) ) ),
    inference(resolution,[status(thm)],[c_589,c_2])).

tff(c_1513,plain,(
    ! [A_139] :
      ( '#skF_5'('#skF_8',k1_tarski(A_139)) = A_139
      | '#skF_3'('#skF_8',k1_tarski(A_139)) = k1_funct_1('#skF_8','#skF_7')
      | k2_relat_1('#skF_8') = k1_tarski(A_139)
      | '#skF_5'('#skF_8',k1_tarski(A_139)) = A_139
      | k2_relat_1('#skF_8') = k1_tarski(A_139)
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1498,c_626])).

tff(c_1557,plain,(
    ! [A_141] :
      ( '#skF_3'('#skF_8',k1_tarski(A_141)) = k1_funct_1('#skF_8','#skF_7')
      | '#skF_5'('#skF_8',k1_tarski(A_141)) = A_141
      | k2_relat_1('#skF_8') = k1_tarski(A_141) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_1513])).

tff(c_30,plain,(
    ! [A_9,B_31] :
      ( ~ r2_hidden('#skF_3'(A_9,B_31),B_31)
      | r2_hidden('#skF_5'(A_9,B_31),B_31)
      | k2_relat_1(A_9) = B_31
      | ~ v1_funct_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1568,plain,(
    ! [A_141] :
      ( ~ r2_hidden(k1_funct_1('#skF_8','#skF_7'),k1_tarski(A_141))
      | r2_hidden('#skF_5'('#skF_8',k1_tarski(A_141)),k1_tarski(A_141))
      | k2_relat_1('#skF_8') = k1_tarski(A_141)
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8')
      | '#skF_5'('#skF_8',k1_tarski(A_141)) = A_141
      | k2_relat_1('#skF_8') = k1_tarski(A_141) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1557,c_30])).

tff(c_1639,plain,(
    ! [A_145] :
      ( ~ r2_hidden(k1_funct_1('#skF_8','#skF_7'),k1_tarski(A_145))
      | r2_hidden('#skF_5'('#skF_8',k1_tarski(A_145)),k1_tarski(A_145))
      | '#skF_5'('#skF_8',k1_tarski(A_145)) = A_145
      | k2_relat_1('#skF_8') = k1_tarski(A_145) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_1568])).

tff(c_1658,plain,(
    ! [A_146] :
      ( ~ r2_hidden(k1_funct_1('#skF_8','#skF_7'),k1_tarski(A_146))
      | '#skF_5'('#skF_8',k1_tarski(A_146)) = A_146
      | k2_relat_1('#skF_8') = k1_tarski(A_146) ) ),
    inference(resolution,[status(thm)],[c_1639,c_2])).

tff(c_1665,plain,
    ( '#skF_5'('#skF_8',k1_tarski(k1_funct_1('#skF_8','#skF_7'))) = k1_funct_1('#skF_8','#skF_7')
    | k1_tarski(k1_funct_1('#skF_8','#skF_7')) = k2_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_4,c_1658])).

tff(c_1670,plain,(
    '#skF_5'('#skF_8',k1_tarski(k1_funct_1('#skF_8','#skF_7'))) = k1_funct_1('#skF_8','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_1665])).

tff(c_28,plain,(
    ! [A_9,B_31,D_44] :
      ( r2_hidden('#skF_4'(A_9,B_31),k1_relat_1(A_9))
      | k1_funct_1(A_9,D_44) != '#skF_5'(A_9,B_31)
      | ~ r2_hidden(D_44,k1_relat_1(A_9))
      | k2_relat_1(A_9) = B_31
      | ~ v1_funct_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1678,plain,(
    ! [D_44] :
      ( r2_hidden('#skF_4'('#skF_8',k1_tarski(k1_funct_1('#skF_8','#skF_7'))),k1_relat_1('#skF_8'))
      | k1_funct_1('#skF_8',D_44) != k1_funct_1('#skF_8','#skF_7')
      | ~ r2_hidden(D_44,k1_relat_1('#skF_8'))
      | k1_tarski(k1_funct_1('#skF_8','#skF_7')) = k2_relat_1('#skF_8')
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1670,c_28])).

tff(c_1705,plain,(
    ! [D_44] :
      ( r2_hidden('#skF_4'('#skF_8',k1_tarski(k1_funct_1('#skF_8','#skF_7'))),k1_relat_1('#skF_8'))
      | k1_funct_1('#skF_8',D_44) != k1_funct_1('#skF_8','#skF_7')
      | ~ r2_hidden(D_44,k1_relat_1('#skF_8'))
      | k1_tarski(k1_funct_1('#skF_8','#skF_7')) = k2_relat_1('#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_1678])).

tff(c_1706,plain,(
    ! [D_44] :
      ( r2_hidden('#skF_4'('#skF_8',k1_tarski(k1_funct_1('#skF_8','#skF_7'))),k1_relat_1('#skF_8'))
      | k1_funct_1('#skF_8',D_44) != k1_funct_1('#skF_8','#skF_7')
      | ~ r2_hidden(D_44,k1_relat_1('#skF_8')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_1705])).

tff(c_1794,plain,(
    ! [D_149] :
      ( k1_funct_1('#skF_8',D_149) != k1_funct_1('#skF_8','#skF_7')
      | ~ r2_hidden(D_149,k1_relat_1('#skF_8')) ) ),
    inference(splitLeft,[status(thm)],[c_1706])).

tff(c_1906,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_47,c_1794])).

tff(c_1907,plain,(
    r2_hidden('#skF_4'('#skF_8',k1_tarski(k1_funct_1('#skF_8','#skF_7'))),k1_relat_1('#skF_8')) ),
    inference(splitRight,[status(thm)],[c_1706])).

tff(c_1927,plain,(
    '#skF_4'('#skF_8',k1_tarski(k1_funct_1('#skF_8','#skF_7'))) = '#skF_7' ),
    inference(resolution,[status(thm)],[c_1907,c_63])).

tff(c_26,plain,(
    ! [A_9,B_31,D_44] :
      ( k1_funct_1(A_9,'#skF_4'(A_9,B_31)) = '#skF_3'(A_9,B_31)
      | k1_funct_1(A_9,D_44) != '#skF_5'(A_9,B_31)
      | ~ r2_hidden(D_44,k1_relat_1(A_9))
      | k2_relat_1(A_9) = B_31
      | ~ v1_funct_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1673,plain,(
    ! [D_44] :
      ( k1_funct_1('#skF_8','#skF_4'('#skF_8',k1_tarski(k1_funct_1('#skF_8','#skF_7')))) = '#skF_3'('#skF_8',k1_tarski(k1_funct_1('#skF_8','#skF_7')))
      | k1_funct_1('#skF_8',D_44) != k1_funct_1('#skF_8','#skF_7')
      | ~ r2_hidden(D_44,k1_relat_1('#skF_8'))
      | k1_tarski(k1_funct_1('#skF_8','#skF_7')) = k2_relat_1('#skF_8')
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1670,c_26])).

tff(c_1700,plain,(
    ! [D_44] :
      ( k1_funct_1('#skF_8','#skF_4'('#skF_8',k1_tarski(k1_funct_1('#skF_8','#skF_7')))) = '#skF_3'('#skF_8',k1_tarski(k1_funct_1('#skF_8','#skF_7')))
      | k1_funct_1('#skF_8',D_44) != k1_funct_1('#skF_8','#skF_7')
      | ~ r2_hidden(D_44,k1_relat_1('#skF_8'))
      | k1_tarski(k1_funct_1('#skF_8','#skF_7')) = k2_relat_1('#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_1673])).

tff(c_1701,plain,(
    ! [D_44] :
      ( k1_funct_1('#skF_8','#skF_4'('#skF_8',k1_tarski(k1_funct_1('#skF_8','#skF_7')))) = '#skF_3'('#skF_8',k1_tarski(k1_funct_1('#skF_8','#skF_7')))
      | k1_funct_1('#skF_8',D_44) != k1_funct_1('#skF_8','#skF_7')
      | ~ r2_hidden(D_44,k1_relat_1('#skF_8')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_1700])).

tff(c_1965,plain,(
    ! [D_44] :
      ( '#skF_3'('#skF_8',k1_tarski(k1_funct_1('#skF_8','#skF_7'))) = k1_funct_1('#skF_8','#skF_7')
      | k1_funct_1('#skF_8',D_44) != k1_funct_1('#skF_8','#skF_7')
      | ~ r2_hidden(D_44,k1_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1927,c_1701])).

tff(c_1968,plain,(
    ! [D_150] :
      ( k1_funct_1('#skF_8',D_150) != k1_funct_1('#skF_8','#skF_7')
      | ~ r2_hidden(D_150,k1_relat_1('#skF_8')) ) ),
    inference(splitLeft,[status(thm)],[c_1965])).

tff(c_2078,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_47,c_1968])).

tff(c_2079,plain,(
    '#skF_3'('#skF_8',k1_tarski(k1_funct_1('#skF_8','#skF_7'))) = k1_funct_1('#skF_8','#skF_7') ),
    inference(splitRight,[status(thm)],[c_1965])).

tff(c_24,plain,(
    ! [A_9,B_31,D_44] :
      ( ~ r2_hidden('#skF_3'(A_9,B_31),B_31)
      | k1_funct_1(A_9,D_44) != '#skF_5'(A_9,B_31)
      | ~ r2_hidden(D_44,k1_relat_1(A_9))
      | k2_relat_1(A_9) = B_31
      | ~ v1_funct_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_2088,plain,(
    ! [D_44] :
      ( ~ r2_hidden(k1_funct_1('#skF_8','#skF_7'),k1_tarski(k1_funct_1('#skF_8','#skF_7')))
      | k1_funct_1('#skF_8',D_44) != '#skF_5'('#skF_8',k1_tarski(k1_funct_1('#skF_8','#skF_7')))
      | ~ r2_hidden(D_44,k1_relat_1('#skF_8'))
      | k1_tarski(k1_funct_1('#skF_8','#skF_7')) = k2_relat_1('#skF_8')
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2079,c_24])).

tff(c_2103,plain,(
    ! [D_44] :
      ( k1_funct_1('#skF_8',D_44) != k1_funct_1('#skF_8','#skF_7')
      | ~ r2_hidden(D_44,k1_relat_1('#skF_8'))
      | k1_tarski(k1_funct_1('#skF_8','#skF_7')) = k2_relat_1('#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_1670,c_4,c_2088])).

tff(c_2113,plain,(
    ! [D_151] :
      ( k1_funct_1('#skF_8',D_151) != k1_funct_1('#skF_8','#skF_7')
      | ~ r2_hidden(D_151,k1_relat_1('#skF_8')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_2103])).

tff(c_2223,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_47,c_2113])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:59:08 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.87/1.74  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.87/1.75  
% 3.87/1.75  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.87/1.75  %$ r2_hidden > v1_relat_1 > v1_funct_1 > k1_enumset1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > #skF_6 > #skF_7 > #skF_3 > #skF_8 > #skF_2 > #skF_1 > #skF_5 > #skF_4
% 3.87/1.75  
% 3.87/1.75  %Foreground sorts:
% 3.87/1.75  
% 3.87/1.75  
% 3.87/1.75  %Background operators:
% 3.87/1.75  
% 3.87/1.75  
% 3.87/1.75  %Foreground operators:
% 3.87/1.75  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.87/1.75  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.87/1.75  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.87/1.75  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 3.87/1.75  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.87/1.75  tff('#skF_7', type, '#skF_7': $i).
% 3.87/1.75  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.87/1.75  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.87/1.75  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.87/1.75  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.87/1.75  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.87/1.75  tff('#skF_8', type, '#skF_8': $i).
% 3.87/1.75  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.87/1.75  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.87/1.75  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.87/1.75  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.87/1.75  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.87/1.75  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 3.87/1.75  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.87/1.75  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.87/1.75  
% 3.87/1.76  tff(f_60, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_funct_1)).
% 3.87/1.76  tff(f_32, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 3.87/1.76  tff(f_51, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_funct_1)).
% 3.87/1.76  tff(c_38, plain, (k1_tarski('#skF_7')=k1_relat_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.87/1.76  tff(c_4, plain, (![C_5]: (r2_hidden(C_5, k1_tarski(C_5)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.87/1.76  tff(c_47, plain, (r2_hidden('#skF_7', k1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_38, c_4])).
% 3.87/1.76  tff(c_36, plain, (k1_tarski(k1_funct_1('#skF_8', '#skF_7'))!=k2_relat_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.87/1.76  tff(c_42, plain, (v1_relat_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.87/1.76  tff(c_40, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.87/1.76  tff(c_514, plain, (![A_90, B_91]: (k1_funct_1(A_90, '#skF_4'(A_90, B_91))='#skF_3'(A_90, B_91) | r2_hidden('#skF_5'(A_90, B_91), B_91) | k2_relat_1(A_90)=B_91 | ~v1_funct_1(A_90) | ~v1_relat_1(A_90))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.87/1.76  tff(c_2, plain, (![C_5, A_1]: (C_5=A_1 | ~r2_hidden(C_5, k1_tarski(A_1)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.87/1.76  tff(c_1498, plain, (![A_138, A_139]: ('#skF_5'(A_138, k1_tarski(A_139))=A_139 | k1_funct_1(A_138, '#skF_4'(A_138, k1_tarski(A_139)))='#skF_3'(A_138, k1_tarski(A_139)) | k2_relat_1(A_138)=k1_tarski(A_139) | ~v1_funct_1(A_138) | ~v1_relat_1(A_138))), inference(resolution, [status(thm)], [c_514, c_2])).
% 3.87/1.76  tff(c_362, plain, (![A_86, B_87]: (r2_hidden('#skF_4'(A_86, B_87), k1_relat_1(A_86)) | r2_hidden('#skF_5'(A_86, B_87), B_87) | k2_relat_1(A_86)=B_87 | ~v1_funct_1(A_86) | ~v1_relat_1(A_86))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.87/1.76  tff(c_18, plain, (![A_9, D_48]: (r2_hidden(k1_funct_1(A_9, D_48), k2_relat_1(A_9)) | ~r2_hidden(D_48, k1_relat_1(A_9)) | ~v1_funct_1(A_9) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.87/1.76  tff(c_109, plain, (![A_66, C_67]: (r2_hidden('#skF_6'(A_66, k2_relat_1(A_66), C_67), k1_relat_1(A_66)) | ~r2_hidden(C_67, k2_relat_1(A_66)) | ~v1_funct_1(A_66) | ~v1_relat_1(A_66))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.87/1.76  tff(c_60, plain, (![C_51, A_52]: (C_51=A_52 | ~r2_hidden(C_51, k1_tarski(A_52)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.87/1.76  tff(c_63, plain, (![C_51]: (C_51='#skF_7' | ~r2_hidden(C_51, k1_relat_1('#skF_8')))), inference(superposition, [status(thm), theory('equality')], [c_38, c_60])).
% 3.87/1.76  tff(c_113, plain, (![C_67]: ('#skF_6'('#skF_8', k2_relat_1('#skF_8'), C_67)='#skF_7' | ~r2_hidden(C_67, k2_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_109, c_63])).
% 3.87/1.76  tff(c_117, plain, (![C_68]: ('#skF_6'('#skF_8', k2_relat_1('#skF_8'), C_68)='#skF_7' | ~r2_hidden(C_68, k2_relat_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_113])).
% 3.87/1.76  tff(c_121, plain, (![D_48]: ('#skF_6'('#skF_8', k2_relat_1('#skF_8'), k1_funct_1('#skF_8', D_48))='#skF_7' | ~r2_hidden(D_48, k1_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_18, c_117])).
% 3.87/1.76  tff(c_132, plain, (![D_48]: ('#skF_6'('#skF_8', k2_relat_1('#skF_8'), k1_funct_1('#skF_8', D_48))='#skF_7' | ~r2_hidden(D_48, k1_relat_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_121])).
% 3.87/1.76  tff(c_196, plain, (![A_73, C_74]: (k1_funct_1(A_73, '#skF_6'(A_73, k2_relat_1(A_73), C_74))=C_74 | ~r2_hidden(C_74, k2_relat_1(A_73)) | ~v1_funct_1(A_73) | ~v1_relat_1(A_73))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.87/1.76  tff(c_212, plain, (![D_48]: (k1_funct_1('#skF_8', D_48)=k1_funct_1('#skF_8', '#skF_7') | ~r2_hidden(k1_funct_1('#skF_8', D_48), k2_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~r2_hidden(D_48, k1_relat_1('#skF_8')))), inference(superposition, [status(thm), theory('equality')], [c_132, c_196])).
% 3.87/1.76  tff(c_230, plain, (![D_80]: (k1_funct_1('#skF_8', D_80)=k1_funct_1('#skF_8', '#skF_7') | ~r2_hidden(k1_funct_1('#skF_8', D_80), k2_relat_1('#skF_8')) | ~r2_hidden(D_80, k1_relat_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_212])).
% 3.87/1.76  tff(c_238, plain, (![D_48]: (k1_funct_1('#skF_8', D_48)=k1_funct_1('#skF_8', '#skF_7') | ~r2_hidden(D_48, k1_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_18, c_230])).
% 3.87/1.76  tff(c_243, plain, (![D_48]: (k1_funct_1('#skF_8', D_48)=k1_funct_1('#skF_8', '#skF_7') | ~r2_hidden(D_48, k1_relat_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_238])).
% 3.87/1.76  tff(c_366, plain, (![B_87]: (k1_funct_1('#skF_8', '#skF_4'('#skF_8', B_87))=k1_funct_1('#skF_8', '#skF_7') | r2_hidden('#skF_5'('#skF_8', B_87), B_87) | k2_relat_1('#skF_8')=B_87 | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_362, c_243])).
% 3.87/1.76  tff(c_589, plain, (![B_93]: (k1_funct_1('#skF_8', '#skF_4'('#skF_8', B_93))=k1_funct_1('#skF_8', '#skF_7') | r2_hidden('#skF_5'('#skF_8', B_93), B_93) | k2_relat_1('#skF_8')=B_93)), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_366])).
% 3.87/1.76  tff(c_626, plain, (![A_1]: ('#skF_5'('#skF_8', k1_tarski(A_1))=A_1 | k1_funct_1('#skF_8', '#skF_4'('#skF_8', k1_tarski(A_1)))=k1_funct_1('#skF_8', '#skF_7') | k2_relat_1('#skF_8')=k1_tarski(A_1))), inference(resolution, [status(thm)], [c_589, c_2])).
% 3.87/1.76  tff(c_1513, plain, (![A_139]: ('#skF_5'('#skF_8', k1_tarski(A_139))=A_139 | '#skF_3'('#skF_8', k1_tarski(A_139))=k1_funct_1('#skF_8', '#skF_7') | k2_relat_1('#skF_8')=k1_tarski(A_139) | '#skF_5'('#skF_8', k1_tarski(A_139))=A_139 | k2_relat_1('#skF_8')=k1_tarski(A_139) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_1498, c_626])).
% 3.87/1.76  tff(c_1557, plain, (![A_141]: ('#skF_3'('#skF_8', k1_tarski(A_141))=k1_funct_1('#skF_8', '#skF_7') | '#skF_5'('#skF_8', k1_tarski(A_141))=A_141 | k2_relat_1('#skF_8')=k1_tarski(A_141))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_1513])).
% 3.87/1.76  tff(c_30, plain, (![A_9, B_31]: (~r2_hidden('#skF_3'(A_9, B_31), B_31) | r2_hidden('#skF_5'(A_9, B_31), B_31) | k2_relat_1(A_9)=B_31 | ~v1_funct_1(A_9) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.87/1.76  tff(c_1568, plain, (![A_141]: (~r2_hidden(k1_funct_1('#skF_8', '#skF_7'), k1_tarski(A_141)) | r2_hidden('#skF_5'('#skF_8', k1_tarski(A_141)), k1_tarski(A_141)) | k2_relat_1('#skF_8')=k1_tarski(A_141) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | '#skF_5'('#skF_8', k1_tarski(A_141))=A_141 | k2_relat_1('#skF_8')=k1_tarski(A_141))), inference(superposition, [status(thm), theory('equality')], [c_1557, c_30])).
% 3.87/1.76  tff(c_1639, plain, (![A_145]: (~r2_hidden(k1_funct_1('#skF_8', '#skF_7'), k1_tarski(A_145)) | r2_hidden('#skF_5'('#skF_8', k1_tarski(A_145)), k1_tarski(A_145)) | '#skF_5'('#skF_8', k1_tarski(A_145))=A_145 | k2_relat_1('#skF_8')=k1_tarski(A_145))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_1568])).
% 3.87/1.76  tff(c_1658, plain, (![A_146]: (~r2_hidden(k1_funct_1('#skF_8', '#skF_7'), k1_tarski(A_146)) | '#skF_5'('#skF_8', k1_tarski(A_146))=A_146 | k2_relat_1('#skF_8')=k1_tarski(A_146))), inference(resolution, [status(thm)], [c_1639, c_2])).
% 3.87/1.76  tff(c_1665, plain, ('#skF_5'('#skF_8', k1_tarski(k1_funct_1('#skF_8', '#skF_7')))=k1_funct_1('#skF_8', '#skF_7') | k1_tarski(k1_funct_1('#skF_8', '#skF_7'))=k2_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_4, c_1658])).
% 3.87/1.76  tff(c_1670, plain, ('#skF_5'('#skF_8', k1_tarski(k1_funct_1('#skF_8', '#skF_7')))=k1_funct_1('#skF_8', '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_36, c_1665])).
% 3.87/1.76  tff(c_28, plain, (![A_9, B_31, D_44]: (r2_hidden('#skF_4'(A_9, B_31), k1_relat_1(A_9)) | k1_funct_1(A_9, D_44)!='#skF_5'(A_9, B_31) | ~r2_hidden(D_44, k1_relat_1(A_9)) | k2_relat_1(A_9)=B_31 | ~v1_funct_1(A_9) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.87/1.76  tff(c_1678, plain, (![D_44]: (r2_hidden('#skF_4'('#skF_8', k1_tarski(k1_funct_1('#skF_8', '#skF_7'))), k1_relat_1('#skF_8')) | k1_funct_1('#skF_8', D_44)!=k1_funct_1('#skF_8', '#skF_7') | ~r2_hidden(D_44, k1_relat_1('#skF_8')) | k1_tarski(k1_funct_1('#skF_8', '#skF_7'))=k2_relat_1('#skF_8') | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_1670, c_28])).
% 3.87/1.76  tff(c_1705, plain, (![D_44]: (r2_hidden('#skF_4'('#skF_8', k1_tarski(k1_funct_1('#skF_8', '#skF_7'))), k1_relat_1('#skF_8')) | k1_funct_1('#skF_8', D_44)!=k1_funct_1('#skF_8', '#skF_7') | ~r2_hidden(D_44, k1_relat_1('#skF_8')) | k1_tarski(k1_funct_1('#skF_8', '#skF_7'))=k2_relat_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_1678])).
% 3.87/1.76  tff(c_1706, plain, (![D_44]: (r2_hidden('#skF_4'('#skF_8', k1_tarski(k1_funct_1('#skF_8', '#skF_7'))), k1_relat_1('#skF_8')) | k1_funct_1('#skF_8', D_44)!=k1_funct_1('#skF_8', '#skF_7') | ~r2_hidden(D_44, k1_relat_1('#skF_8')))), inference(negUnitSimplification, [status(thm)], [c_36, c_1705])).
% 3.87/1.76  tff(c_1794, plain, (![D_149]: (k1_funct_1('#skF_8', D_149)!=k1_funct_1('#skF_8', '#skF_7') | ~r2_hidden(D_149, k1_relat_1('#skF_8')))), inference(splitLeft, [status(thm)], [c_1706])).
% 3.87/1.76  tff(c_1906, plain, $false, inference(resolution, [status(thm)], [c_47, c_1794])).
% 3.87/1.76  tff(c_1907, plain, (r2_hidden('#skF_4'('#skF_8', k1_tarski(k1_funct_1('#skF_8', '#skF_7'))), k1_relat_1('#skF_8'))), inference(splitRight, [status(thm)], [c_1706])).
% 3.87/1.76  tff(c_1927, plain, ('#skF_4'('#skF_8', k1_tarski(k1_funct_1('#skF_8', '#skF_7')))='#skF_7'), inference(resolution, [status(thm)], [c_1907, c_63])).
% 3.87/1.76  tff(c_26, plain, (![A_9, B_31, D_44]: (k1_funct_1(A_9, '#skF_4'(A_9, B_31))='#skF_3'(A_9, B_31) | k1_funct_1(A_9, D_44)!='#skF_5'(A_9, B_31) | ~r2_hidden(D_44, k1_relat_1(A_9)) | k2_relat_1(A_9)=B_31 | ~v1_funct_1(A_9) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.87/1.76  tff(c_1673, plain, (![D_44]: (k1_funct_1('#skF_8', '#skF_4'('#skF_8', k1_tarski(k1_funct_1('#skF_8', '#skF_7'))))='#skF_3'('#skF_8', k1_tarski(k1_funct_1('#skF_8', '#skF_7'))) | k1_funct_1('#skF_8', D_44)!=k1_funct_1('#skF_8', '#skF_7') | ~r2_hidden(D_44, k1_relat_1('#skF_8')) | k1_tarski(k1_funct_1('#skF_8', '#skF_7'))=k2_relat_1('#skF_8') | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_1670, c_26])).
% 3.87/1.76  tff(c_1700, plain, (![D_44]: (k1_funct_1('#skF_8', '#skF_4'('#skF_8', k1_tarski(k1_funct_1('#skF_8', '#skF_7'))))='#skF_3'('#skF_8', k1_tarski(k1_funct_1('#skF_8', '#skF_7'))) | k1_funct_1('#skF_8', D_44)!=k1_funct_1('#skF_8', '#skF_7') | ~r2_hidden(D_44, k1_relat_1('#skF_8')) | k1_tarski(k1_funct_1('#skF_8', '#skF_7'))=k2_relat_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_1673])).
% 3.87/1.76  tff(c_1701, plain, (![D_44]: (k1_funct_1('#skF_8', '#skF_4'('#skF_8', k1_tarski(k1_funct_1('#skF_8', '#skF_7'))))='#skF_3'('#skF_8', k1_tarski(k1_funct_1('#skF_8', '#skF_7'))) | k1_funct_1('#skF_8', D_44)!=k1_funct_1('#skF_8', '#skF_7') | ~r2_hidden(D_44, k1_relat_1('#skF_8')))), inference(negUnitSimplification, [status(thm)], [c_36, c_1700])).
% 3.87/1.76  tff(c_1965, plain, (![D_44]: ('#skF_3'('#skF_8', k1_tarski(k1_funct_1('#skF_8', '#skF_7')))=k1_funct_1('#skF_8', '#skF_7') | k1_funct_1('#skF_8', D_44)!=k1_funct_1('#skF_8', '#skF_7') | ~r2_hidden(D_44, k1_relat_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_1927, c_1701])).
% 3.87/1.76  tff(c_1968, plain, (![D_150]: (k1_funct_1('#skF_8', D_150)!=k1_funct_1('#skF_8', '#skF_7') | ~r2_hidden(D_150, k1_relat_1('#skF_8')))), inference(splitLeft, [status(thm)], [c_1965])).
% 3.87/1.76  tff(c_2078, plain, $false, inference(resolution, [status(thm)], [c_47, c_1968])).
% 3.87/1.76  tff(c_2079, plain, ('#skF_3'('#skF_8', k1_tarski(k1_funct_1('#skF_8', '#skF_7')))=k1_funct_1('#skF_8', '#skF_7')), inference(splitRight, [status(thm)], [c_1965])).
% 3.87/1.76  tff(c_24, plain, (![A_9, B_31, D_44]: (~r2_hidden('#skF_3'(A_9, B_31), B_31) | k1_funct_1(A_9, D_44)!='#skF_5'(A_9, B_31) | ~r2_hidden(D_44, k1_relat_1(A_9)) | k2_relat_1(A_9)=B_31 | ~v1_funct_1(A_9) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.87/1.76  tff(c_2088, plain, (![D_44]: (~r2_hidden(k1_funct_1('#skF_8', '#skF_7'), k1_tarski(k1_funct_1('#skF_8', '#skF_7'))) | k1_funct_1('#skF_8', D_44)!='#skF_5'('#skF_8', k1_tarski(k1_funct_1('#skF_8', '#skF_7'))) | ~r2_hidden(D_44, k1_relat_1('#skF_8')) | k1_tarski(k1_funct_1('#skF_8', '#skF_7'))=k2_relat_1('#skF_8') | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_2079, c_24])).
% 3.87/1.76  tff(c_2103, plain, (![D_44]: (k1_funct_1('#skF_8', D_44)!=k1_funct_1('#skF_8', '#skF_7') | ~r2_hidden(D_44, k1_relat_1('#skF_8')) | k1_tarski(k1_funct_1('#skF_8', '#skF_7'))=k2_relat_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_1670, c_4, c_2088])).
% 3.87/1.76  tff(c_2113, plain, (![D_151]: (k1_funct_1('#skF_8', D_151)!=k1_funct_1('#skF_8', '#skF_7') | ~r2_hidden(D_151, k1_relat_1('#skF_8')))), inference(negUnitSimplification, [status(thm)], [c_36, c_2103])).
% 3.87/1.76  tff(c_2223, plain, $false, inference(resolution, [status(thm)], [c_47, c_2113])).
% 3.87/1.76  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.87/1.76  
% 3.87/1.76  Inference rules
% 3.87/1.76  ----------------------
% 3.87/1.76  #Ref     : 0
% 3.87/1.76  #Sup     : 382
% 3.87/1.76  #Fact    : 2
% 3.87/1.76  #Define  : 0
% 3.87/1.76  #Split   : 6
% 3.87/1.76  #Chain   : 0
% 3.87/1.76  #Close   : 0
% 3.87/1.76  
% 3.87/1.76  Ordering : KBO
% 3.87/1.76  
% 3.87/1.76  Simplification rules
% 3.87/1.76  ----------------------
% 3.87/1.76  #Subsume      : 60
% 3.87/1.76  #Demod        : 456
% 3.87/1.76  #Tautology    : 172
% 3.87/1.76  #SimpNegUnit  : 88
% 3.87/1.76  #BackRed      : 11
% 3.87/1.76  
% 3.87/1.76  #Partial instantiations: 0
% 3.87/1.76  #Strategies tried      : 1
% 3.87/1.76  
% 3.87/1.77  Timing (in seconds)
% 3.87/1.77  ----------------------
% 3.87/1.77  Preprocessing        : 0.41
% 3.87/1.77  Parsing              : 0.21
% 3.87/1.77  CNF conversion       : 0.03
% 3.87/1.77  Main loop            : 0.58
% 3.87/1.77  Inferencing          : 0.20
% 3.87/1.77  Reduction            : 0.19
% 3.87/1.77  Demodulation         : 0.13
% 3.87/1.77  BG Simplification    : 0.03
% 3.87/1.77  Subsumption          : 0.12
% 3.87/1.77  Abstraction          : 0.04
% 3.87/1.77  MUC search           : 0.00
% 3.87/1.77  Cooper               : 0.00
% 3.87/1.77  Total                : 1.02
% 3.87/1.77  Index Insertion      : 0.00
% 3.87/1.77  Index Deletion       : 0.00
% 3.87/1.77  Index Matching       : 0.00
% 3.87/1.77  BG Taut test         : 0.00
%------------------------------------------------------------------------------
