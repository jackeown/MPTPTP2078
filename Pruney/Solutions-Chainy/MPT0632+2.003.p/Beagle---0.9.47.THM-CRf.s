%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:19 EST 2020

% Result     : Theorem 5.75s
% Output     : CNFRefutation 6.07s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 406 expanded)
%              Number of leaves         :   27 ( 147 expanded)
%              Depth                    :   18
%              Number of atoms          :  285 (1121 expanded)
%              Number of equality atoms :  100 ( 565 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > v1_funct_1 > k5_relat_1 > k1_funct_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > #skF_4 > #skF_7 > #skF_3 > #skF_6 > #skF_8 > #skF_2 > #skF_1 > #skF_5

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

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

tff(f_116,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ( B = k6_relat_1(A)
        <=> ( k1_relat_1(B) = A
            & ! [C] :
                ( r2_hidden(C,A)
               => k1_funct_1(B,C) = C ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_funct_1)).

tff(f_56,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_29,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_102,axiom,(
    ! [A] :
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_funct_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).

tff(f_33,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(k6_relat_1(k1_relat_1(A)),A) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_relat_1)).

tff(f_84,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ! [C] :
          ( ( v1_relat_1(C)
            & v1_funct_1(C) )
         => ( r2_hidden(A,k1_relat_1(B))
           => k1_funct_1(k5_relat_1(B,C),A) = k1_funct_1(C,k1_funct_1(B,A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_funct_1)).

tff(f_37,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(A,k6_relat_1(k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).

tff(c_60,plain,
    ( k6_relat_1('#skF_6') = '#skF_7'
    | k1_relat_1('#skF_7') = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_85,plain,(
    k1_relat_1('#skF_7') = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_52,plain,
    ( r2_hidden('#skF_8','#skF_6')
    | k1_relat_1('#skF_7') != '#skF_6'
    | k6_relat_1('#skF_6') != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_110,plain,
    ( r2_hidden('#skF_8','#skF_6')
    | k6_relat_1('#skF_6') != '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_52])).

tff(c_111,plain,(
    k6_relat_1('#skF_6') != '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_110])).

tff(c_28,plain,(
    ! [A_44] : v1_relat_1(k6_relat_1(A_44)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_30,plain,(
    ! [A_44] : v1_funct_1(k6_relat_1(A_44)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_2,plain,(
    ! [A_1] : k1_relat_1(k6_relat_1(A_1)) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_46,plain,(
    v1_relat_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_44,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_800,plain,(
    ! [A_111,B_112] :
      ( r2_hidden('#skF_5'(A_111,B_112),k1_relat_1(A_111))
      | B_112 = A_111
      | k1_relat_1(B_112) != k1_relat_1(A_111)
      | ~ v1_funct_1(B_112)
      | ~ v1_relat_1(B_112)
      | ~ v1_funct_1(A_111)
      | ~ v1_relat_1(A_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_807,plain,(
    ! [B_112] :
      ( r2_hidden('#skF_5'('#skF_7',B_112),'#skF_6')
      | B_112 = '#skF_7'
      | k1_relat_1(B_112) != k1_relat_1('#skF_7')
      | ~ v1_funct_1(B_112)
      | ~ v1_relat_1(B_112)
      | ~ v1_funct_1('#skF_7')
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_85,c_800])).

tff(c_813,plain,(
    ! [B_112] :
      ( r2_hidden('#skF_5'('#skF_7',B_112),'#skF_6')
      | B_112 = '#skF_7'
      | k1_relat_1(B_112) != '#skF_6'
      | ~ v1_funct_1(B_112)
      | ~ v1_relat_1(B_112) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_85,c_807])).

tff(c_4,plain,(
    ! [A_1] : k2_relat_1(k6_relat_1(A_1)) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_223,plain,(
    ! [A_79,C_80] :
      ( r2_hidden('#skF_4'(A_79,k2_relat_1(A_79),C_80),k1_relat_1(A_79))
      | ~ r2_hidden(C_80,k2_relat_1(A_79))
      | ~ v1_funct_1(A_79)
      | ~ v1_relat_1(A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_229,plain,(
    ! [A_1,C_80] :
      ( r2_hidden('#skF_4'(k6_relat_1(A_1),k2_relat_1(k6_relat_1(A_1)),C_80),A_1)
      | ~ r2_hidden(C_80,k2_relat_1(k6_relat_1(A_1)))
      | ~ v1_funct_1(k6_relat_1(A_1))
      | ~ v1_relat_1(k6_relat_1(A_1)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_223])).

tff(c_236,plain,(
    ! [A_1,C_80] :
      ( r2_hidden('#skF_4'(k6_relat_1(A_1),A_1,C_80),A_1)
      | ~ r2_hidden(C_80,A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_30,c_4,c_4,c_229])).

tff(c_12,plain,(
    ! [A_4,C_40] :
      ( k1_funct_1(A_4,'#skF_4'(A_4,k2_relat_1(A_4),C_40)) = C_40
      | ~ r2_hidden(C_40,k2_relat_1(A_4))
      | ~ v1_funct_1(A_4)
      | ~ v1_relat_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_90,plain,(
    ! [A_66] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(A_66)),A_66) = A_66
      | ~ v1_relat_1(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_99,plain,
    ( k5_relat_1(k6_relat_1('#skF_6'),'#skF_7') = '#skF_7'
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_85,c_90])).

tff(c_106,plain,(
    k5_relat_1(k6_relat_1('#skF_6'),'#skF_7') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_99])).

tff(c_1535,plain,(
    ! [B_140,C_141,A_142] :
      ( k1_funct_1(k5_relat_1(B_140,C_141),A_142) = k1_funct_1(C_141,k1_funct_1(B_140,A_142))
      | ~ r2_hidden(A_142,k1_relat_1(B_140))
      | ~ v1_funct_1(C_141)
      | ~ v1_relat_1(C_141)
      | ~ v1_funct_1(B_140)
      | ~ v1_relat_1(B_140) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_1577,plain,(
    ! [A_1,C_141,A_142] :
      ( k1_funct_1(k5_relat_1(k6_relat_1(A_1),C_141),A_142) = k1_funct_1(C_141,k1_funct_1(k6_relat_1(A_1),A_142))
      | ~ r2_hidden(A_142,A_1)
      | ~ v1_funct_1(C_141)
      | ~ v1_relat_1(C_141)
      | ~ v1_funct_1(k6_relat_1(A_1))
      | ~ v1_relat_1(k6_relat_1(A_1)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1535])).

tff(c_1699,plain,(
    ! [A_146,C_147,A_148] :
      ( k1_funct_1(k5_relat_1(k6_relat_1(A_146),C_147),A_148) = k1_funct_1(C_147,k1_funct_1(k6_relat_1(A_146),A_148))
      | ~ r2_hidden(A_148,A_146)
      | ~ v1_funct_1(C_147)
      | ~ v1_relat_1(C_147) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_30,c_1577])).

tff(c_1737,plain,(
    ! [A_148] :
      ( k1_funct_1('#skF_7',k1_funct_1(k6_relat_1('#skF_6'),A_148)) = k1_funct_1('#skF_7',A_148)
      | ~ r2_hidden(A_148,'#skF_6')
      | ~ v1_funct_1('#skF_7')
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_106,c_1699])).

tff(c_1749,plain,(
    ! [A_149] :
      ( k1_funct_1('#skF_7',k1_funct_1(k6_relat_1('#skF_6'),A_149)) = k1_funct_1('#skF_7',A_149)
      | ~ r2_hidden(A_149,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_1737])).

tff(c_147,plain,(
    ! [A_70,D_71] :
      ( r2_hidden(k1_funct_1(A_70,D_71),k2_relat_1(A_70))
      | ~ r2_hidden(D_71,k1_relat_1(A_70))
      | ~ v1_funct_1(A_70)
      | ~ v1_relat_1(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_150,plain,(
    ! [A_1,D_71] :
      ( r2_hidden(k1_funct_1(k6_relat_1(A_1),D_71),A_1)
      | ~ r2_hidden(D_71,k1_relat_1(k6_relat_1(A_1)))
      | ~ v1_funct_1(k6_relat_1(A_1))
      | ~ v1_relat_1(k6_relat_1(A_1)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_147])).

tff(c_170,plain,(
    ! [A_74,D_75] :
      ( r2_hidden(k1_funct_1(k6_relat_1(A_74),D_75),A_74)
      | ~ r2_hidden(D_75,A_74) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_30,c_2,c_150])).

tff(c_54,plain,(
    ! [C_61] :
      ( k6_relat_1('#skF_6') = '#skF_7'
      | k1_funct_1('#skF_7',C_61) = C_61
      | ~ r2_hidden(C_61,'#skF_6') ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_141,plain,(
    ! [C_61] :
      ( k1_funct_1('#skF_7',C_61) = C_61
      | ~ r2_hidden(C_61,'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_111,c_54])).

tff(c_179,plain,(
    ! [D_75] :
      ( k1_funct_1('#skF_7',k1_funct_1(k6_relat_1('#skF_6'),D_75)) = k1_funct_1(k6_relat_1('#skF_6'),D_75)
      | ~ r2_hidden(D_75,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_170,c_141])).

tff(c_1806,plain,(
    ! [A_150] :
      ( k1_funct_1(k6_relat_1('#skF_6'),A_150) = k1_funct_1('#skF_7',A_150)
      | ~ r2_hidden(A_150,'#skF_6')
      | ~ r2_hidden(A_150,'#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1749,c_179])).

tff(c_1860,plain,(
    ! [C_40] :
      ( k1_funct_1('#skF_7','#skF_4'(k6_relat_1('#skF_6'),k2_relat_1(k6_relat_1('#skF_6')),C_40)) = C_40
      | ~ r2_hidden('#skF_4'(k6_relat_1('#skF_6'),k2_relat_1(k6_relat_1('#skF_6')),C_40),'#skF_6')
      | ~ r2_hidden('#skF_4'(k6_relat_1('#skF_6'),k2_relat_1(k6_relat_1('#skF_6')),C_40),'#skF_6')
      | ~ r2_hidden(C_40,k2_relat_1(k6_relat_1('#skF_6')))
      | ~ v1_funct_1(k6_relat_1('#skF_6'))
      | ~ v1_relat_1(k6_relat_1('#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_1806])).

tff(c_1949,plain,(
    ! [C_156] :
      ( k1_funct_1('#skF_7','#skF_4'(k6_relat_1('#skF_6'),'#skF_6',C_156)) = C_156
      | ~ r2_hidden('#skF_4'(k6_relat_1('#skF_6'),'#skF_6',C_156),'#skF_6')
      | ~ r2_hidden(C_156,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_30,c_4,c_4,c_4,c_4,c_1860])).

tff(c_1955,plain,(
    ! [C_157] :
      ( k1_funct_1('#skF_7','#skF_4'(k6_relat_1('#skF_6'),'#skF_6',C_157)) = C_157
      | ~ r2_hidden(C_157,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_236,c_1949])).

tff(c_239,plain,(
    ! [A_81,C_82] :
      ( r2_hidden('#skF_4'(k6_relat_1(A_81),A_81,C_82),A_81)
      | ~ r2_hidden(C_82,A_81) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_30,c_4,c_4,c_229])).

tff(c_244,plain,(
    ! [C_82] :
      ( k1_funct_1('#skF_7','#skF_4'(k6_relat_1('#skF_6'),'#skF_6',C_82)) = '#skF_4'(k6_relat_1('#skF_6'),'#skF_6',C_82)
      | ~ r2_hidden(C_82,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_239,c_141])).

tff(c_2113,plain,(
    ! [C_159] :
      ( '#skF_4'(k6_relat_1('#skF_6'),'#skF_6',C_159) = C_159
      | ~ r2_hidden(C_159,'#skF_6')
      | ~ r2_hidden(C_159,'#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1955,c_244])).

tff(c_153,plain,(
    ! [A_72,C_73] :
      ( k1_funct_1(A_72,'#skF_4'(A_72,k2_relat_1(A_72),C_73)) = C_73
      | ~ r2_hidden(C_73,k2_relat_1(A_72))
      | ~ v1_funct_1(A_72)
      | ~ v1_relat_1(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_165,plain,(
    ! [A_1,C_73] :
      ( k1_funct_1(k6_relat_1(A_1),'#skF_4'(k6_relat_1(A_1),A_1,C_73)) = C_73
      | ~ r2_hidden(C_73,k2_relat_1(k6_relat_1(A_1)))
      | ~ v1_funct_1(k6_relat_1(A_1))
      | ~ v1_relat_1(k6_relat_1(A_1)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_153])).

tff(c_169,plain,(
    ! [A_1,C_73] :
      ( k1_funct_1(k6_relat_1(A_1),'#skF_4'(k6_relat_1(A_1),A_1,C_73)) = C_73
      | ~ r2_hidden(C_73,A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_30,c_4,c_165])).

tff(c_2131,plain,(
    ! [C_159] :
      ( k1_funct_1(k6_relat_1('#skF_6'),C_159) = C_159
      | ~ r2_hidden(C_159,'#skF_6')
      | ~ r2_hidden(C_159,'#skF_6')
      | ~ r2_hidden(C_159,'#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2113,c_169])).

tff(c_920,plain,(
    ! [B_117] :
      ( r2_hidden('#skF_5'('#skF_7',B_117),'#skF_6')
      | B_117 = '#skF_7'
      | k1_relat_1(B_117) != '#skF_6'
      | ~ v1_funct_1(B_117)
      | ~ v1_relat_1(B_117) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_85,c_807])).

tff(c_928,plain,(
    ! [B_117] :
      ( k1_funct_1('#skF_7','#skF_5'('#skF_7',B_117)) = '#skF_5'('#skF_7',B_117)
      | B_117 = '#skF_7'
      | k1_relat_1(B_117) != '#skF_6'
      | ~ v1_funct_1(B_117)
      | ~ v1_relat_1(B_117) ) ),
    inference(resolution,[status(thm)],[c_920,c_141])).

tff(c_2943,plain,(
    ! [B_175,A_176] :
      ( k1_funct_1(B_175,'#skF_5'(A_176,B_175)) != k1_funct_1(A_176,'#skF_5'(A_176,B_175))
      | B_175 = A_176
      | k1_relat_1(B_175) != k1_relat_1(A_176)
      | ~ v1_funct_1(B_175)
      | ~ v1_relat_1(B_175)
      | ~ v1_funct_1(A_176)
      | ~ v1_relat_1(A_176) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_2986,plain,(
    ! [B_117] :
      ( k1_funct_1(B_117,'#skF_5'('#skF_7',B_117)) != '#skF_5'('#skF_7',B_117)
      | B_117 = '#skF_7'
      | k1_relat_1(B_117) != k1_relat_1('#skF_7')
      | ~ v1_funct_1(B_117)
      | ~ v1_relat_1(B_117)
      | ~ v1_funct_1('#skF_7')
      | ~ v1_relat_1('#skF_7')
      | B_117 = '#skF_7'
      | k1_relat_1(B_117) != '#skF_6'
      | ~ v1_funct_1(B_117)
      | ~ v1_relat_1(B_117) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_928,c_2943])).

tff(c_3001,plain,(
    ! [B_177] :
      ( k1_funct_1(B_177,'#skF_5'('#skF_7',B_177)) != '#skF_5'('#skF_7',B_177)
      | B_177 = '#skF_7'
      | k1_relat_1(B_177) != '#skF_6'
      | ~ v1_funct_1(B_177)
      | ~ v1_relat_1(B_177) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_85,c_2986])).

tff(c_3009,plain,
    ( k6_relat_1('#skF_6') = '#skF_7'
    | k1_relat_1(k6_relat_1('#skF_6')) != '#skF_6'
    | ~ v1_funct_1(k6_relat_1('#skF_6'))
    | ~ v1_relat_1(k6_relat_1('#skF_6'))
    | ~ r2_hidden('#skF_5'('#skF_7',k6_relat_1('#skF_6')),'#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_2131,c_3001])).

tff(c_3031,plain,
    ( k6_relat_1('#skF_6') = '#skF_7'
    | ~ r2_hidden('#skF_5'('#skF_7',k6_relat_1('#skF_6')),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_30,c_2,c_3009])).

tff(c_3032,plain,(
    ~ r2_hidden('#skF_5'('#skF_7',k6_relat_1('#skF_6')),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_111,c_3031])).

tff(c_3042,plain,
    ( k6_relat_1('#skF_6') = '#skF_7'
    | k1_relat_1(k6_relat_1('#skF_6')) != '#skF_6'
    | ~ v1_funct_1(k6_relat_1('#skF_6'))
    | ~ v1_relat_1(k6_relat_1('#skF_6')) ),
    inference(resolution,[status(thm)],[c_813,c_3032])).

tff(c_3045,plain,(
    k6_relat_1('#skF_6') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_30,c_2,c_3042])).

tff(c_3047,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_111,c_3045])).

tff(c_3049,plain,(
    k6_relat_1('#skF_6') = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_110])).

tff(c_50,plain,
    ( k1_funct_1('#skF_7','#skF_8') != '#skF_8'
    | k1_relat_1('#skF_7') != '#skF_6'
    | k6_relat_1('#skF_6') != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_3051,plain,
    ( k1_funct_1('#skF_7','#skF_8') != '#skF_8'
    | k6_relat_1('#skF_6') != '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_50])).

tff(c_3052,plain,(
    k6_relat_1('#skF_6') != '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_3051])).

tff(c_3071,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3049,c_3052])).

tff(c_3072,plain,(
    k1_funct_1('#skF_7','#skF_8') != '#skF_8' ),
    inference(splitRight,[status(thm)],[c_3051])).

tff(c_3048,plain,(
    r2_hidden('#skF_8','#skF_6') ),
    inference(splitRight,[status(thm)],[c_110])).

tff(c_3080,plain,(
    k2_relat_1('#skF_7') = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_3049,c_4])).

tff(c_3234,plain,(
    ! [A_190,C_191] :
      ( r2_hidden('#skF_4'(A_190,k2_relat_1(A_190),C_191),k1_relat_1(A_190))
      | ~ r2_hidden(C_191,k2_relat_1(A_190))
      | ~ v1_funct_1(A_190)
      | ~ v1_relat_1(A_190) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_3240,plain,(
    ! [C_191] :
      ( r2_hidden('#skF_4'('#skF_7',k2_relat_1('#skF_7'),C_191),'#skF_6')
      | ~ r2_hidden(C_191,k2_relat_1('#skF_7'))
      | ~ v1_funct_1('#skF_7')
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_85,c_3234])).

tff(c_3250,plain,(
    ! [C_191] :
      ( r2_hidden('#skF_4'('#skF_7','#skF_6',C_191),'#skF_6')
      | ~ r2_hidden(C_191,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_3080,c_3080,c_3240])).

tff(c_8,plain,(
    ! [A_3] :
      ( k5_relat_1(A_3,k6_relat_1(k2_relat_1(A_3))) = A_3
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_3548,plain,(
    ! [B_219,C_220,A_221] :
      ( k1_funct_1(k5_relat_1(B_219,C_220),A_221) = k1_funct_1(C_220,k1_funct_1(B_219,A_221))
      | ~ r2_hidden(A_221,k1_relat_1(B_219))
      | ~ v1_funct_1(C_220)
      | ~ v1_relat_1(C_220)
      | ~ v1_funct_1(B_219)
      | ~ v1_relat_1(B_219) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_3587,plain,(
    ! [C_220,A_221] :
      ( k1_funct_1(k5_relat_1('#skF_7',C_220),A_221) = k1_funct_1(C_220,k1_funct_1('#skF_7',A_221))
      | ~ r2_hidden(A_221,'#skF_6')
      | ~ v1_funct_1(C_220)
      | ~ v1_relat_1(C_220)
      | ~ v1_funct_1('#skF_7')
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_85,c_3548])).

tff(c_3696,plain,(
    ! [C_225,A_226] :
      ( k1_funct_1(k5_relat_1('#skF_7',C_225),A_226) = k1_funct_1(C_225,k1_funct_1('#skF_7',A_226))
      | ~ r2_hidden(A_226,'#skF_6')
      | ~ v1_funct_1(C_225)
      | ~ v1_relat_1(C_225) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_3587])).

tff(c_3728,plain,(
    ! [A_226] :
      ( k1_funct_1(k6_relat_1(k2_relat_1('#skF_7')),k1_funct_1('#skF_7',A_226)) = k1_funct_1('#skF_7',A_226)
      | ~ r2_hidden(A_226,'#skF_6')
      | ~ v1_funct_1(k6_relat_1(k2_relat_1('#skF_7')))
      | ~ v1_relat_1(k6_relat_1(k2_relat_1('#skF_7')))
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_3696])).

tff(c_3738,plain,(
    ! [A_227] :
      ( k1_funct_1('#skF_7',k1_funct_1('#skF_7',A_227)) = k1_funct_1('#skF_7',A_227)
      | ~ r2_hidden(A_227,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_28,c_30,c_3049,c_3080,c_3728])).

tff(c_3768,plain,(
    ! [C_40] :
      ( k1_funct_1('#skF_7','#skF_4'('#skF_7',k2_relat_1('#skF_7'),C_40)) = k1_funct_1('#skF_7',C_40)
      | ~ r2_hidden('#skF_4'('#skF_7',k2_relat_1('#skF_7'),C_40),'#skF_6')
      | ~ r2_hidden(C_40,k2_relat_1('#skF_7'))
      | ~ v1_funct_1('#skF_7')
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_3738])).

tff(c_3791,plain,(
    ! [C_229] :
      ( k1_funct_1('#skF_7','#skF_4'('#skF_7','#skF_6',C_229)) = k1_funct_1('#skF_7',C_229)
      | ~ r2_hidden('#skF_4'('#skF_7','#skF_6',C_229),'#skF_6')
      | ~ r2_hidden(C_229,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_3080,c_3080,c_3080,c_3768])).

tff(c_3796,plain,(
    ! [C_230] :
      ( k1_funct_1('#skF_7','#skF_4'('#skF_7','#skF_6',C_230)) = k1_funct_1('#skF_7',C_230)
      | ~ r2_hidden(C_230,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_3250,c_3791])).

tff(c_3158,plain,(
    ! [A_185,C_186] :
      ( k1_funct_1(A_185,'#skF_4'(A_185,k2_relat_1(A_185),C_186)) = C_186
      | ~ r2_hidden(C_186,k2_relat_1(A_185))
      | ~ v1_funct_1(A_185)
      | ~ v1_relat_1(A_185) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_3178,plain,(
    ! [C_186] :
      ( k1_funct_1('#skF_7','#skF_4'('#skF_7','#skF_6',C_186)) = C_186
      | ~ r2_hidden(C_186,k2_relat_1('#skF_7'))
      | ~ v1_funct_1('#skF_7')
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3080,c_3158])).

tff(c_3189,plain,(
    ! [C_186] :
      ( k1_funct_1('#skF_7','#skF_4'('#skF_7','#skF_6',C_186)) = C_186
      | ~ r2_hidden(C_186,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_3080,c_3178])).

tff(c_3827,plain,(
    ! [C_231] :
      ( k1_funct_1('#skF_7',C_231) = C_231
      | ~ r2_hidden(C_231,'#skF_6')
      | ~ r2_hidden(C_231,'#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3796,c_3189])).

tff(c_3860,plain,
    ( k1_funct_1('#skF_7','#skF_8') = '#skF_8'
    | ~ r2_hidden('#skF_8','#skF_6') ),
    inference(resolution,[status(thm)],[c_3048,c_3827])).

tff(c_3878,plain,(
    k1_funct_1('#skF_7','#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3048,c_3860])).

tff(c_3880,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3072,c_3878])).

tff(c_3882,plain,(
    k1_relat_1('#skF_7') != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_3881,plain,(
    k6_relat_1('#skF_6') = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_3886,plain,(
    k1_relat_1('#skF_7') = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_3881,c_2])).

tff(c_3903,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3882,c_3886])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 18:59:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.75/2.18  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.75/2.20  
% 5.75/2.20  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.75/2.20  %$ r2_hidden > v1_relat_1 > v1_funct_1 > k5_relat_1 > k1_funct_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > #skF_4 > #skF_7 > #skF_3 > #skF_6 > #skF_8 > #skF_2 > #skF_1 > #skF_5
% 5.75/2.20  
% 5.75/2.20  %Foreground sorts:
% 5.75/2.20  
% 5.75/2.20  
% 5.75/2.20  %Background operators:
% 5.75/2.20  
% 5.75/2.20  
% 5.75/2.20  %Foreground operators:
% 5.75/2.20  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.75/2.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.75/2.20  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.75/2.20  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 5.75/2.20  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 5.75/2.20  tff('#skF_7', type, '#skF_7': $i).
% 5.75/2.20  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 5.75/2.20  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.75/2.20  tff('#skF_6', type, '#skF_6': $i).
% 5.75/2.20  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 5.75/2.20  tff('#skF_8', type, '#skF_8': $i).
% 5.75/2.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.75/2.20  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.75/2.20  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 5.75/2.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.75/2.20  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 5.75/2.20  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.75/2.20  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 5.75/2.20  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.75/2.20  
% 6.07/2.23  tff(f_116, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((B = k6_relat_1(A)) <=> ((k1_relat_1(B) = A) & (![C]: (r2_hidden(C, A) => (k1_funct_1(B, C) = C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_funct_1)).
% 6.07/2.23  tff(f_56, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 6.07/2.23  tff(f_29, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 6.07/2.23  tff(f_102, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((k1_relat_1(A) = k1_relat_1(B)) & (![C]: (r2_hidden(C, k1_relat_1(A)) => (k1_funct_1(A, C) = k1_funct_1(B, C))))) => (A = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_funct_1)).
% 6.07/2.23  tff(f_52, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_funct_1)).
% 6.07/2.23  tff(f_33, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(k6_relat_1(k1_relat_1(A)), A) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t78_relat_1)).
% 6.07/2.23  tff(f_84, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(B)) => (k1_funct_1(k5_relat_1(B, C), A) = k1_funct_1(C, k1_funct_1(B, A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_funct_1)).
% 6.07/2.23  tff(f_37, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(A, k6_relat_1(k2_relat_1(A))) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t80_relat_1)).
% 6.07/2.23  tff(c_60, plain, (k6_relat_1('#skF_6')='#skF_7' | k1_relat_1('#skF_7')='#skF_6'), inference(cnfTransformation, [status(thm)], [f_116])).
% 6.07/2.23  tff(c_85, plain, (k1_relat_1('#skF_7')='#skF_6'), inference(splitLeft, [status(thm)], [c_60])).
% 6.07/2.23  tff(c_52, plain, (r2_hidden('#skF_8', '#skF_6') | k1_relat_1('#skF_7')!='#skF_6' | k6_relat_1('#skF_6')!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_116])).
% 6.07/2.23  tff(c_110, plain, (r2_hidden('#skF_8', '#skF_6') | k6_relat_1('#skF_6')!='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_85, c_52])).
% 6.07/2.23  tff(c_111, plain, (k6_relat_1('#skF_6')!='#skF_7'), inference(splitLeft, [status(thm)], [c_110])).
% 6.07/2.23  tff(c_28, plain, (![A_44]: (v1_relat_1(k6_relat_1(A_44)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 6.07/2.23  tff(c_30, plain, (![A_44]: (v1_funct_1(k6_relat_1(A_44)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 6.07/2.23  tff(c_2, plain, (![A_1]: (k1_relat_1(k6_relat_1(A_1))=A_1)), inference(cnfTransformation, [status(thm)], [f_29])).
% 6.07/2.23  tff(c_46, plain, (v1_relat_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_116])).
% 6.07/2.23  tff(c_44, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_116])).
% 6.07/2.23  tff(c_800, plain, (![A_111, B_112]: (r2_hidden('#skF_5'(A_111, B_112), k1_relat_1(A_111)) | B_112=A_111 | k1_relat_1(B_112)!=k1_relat_1(A_111) | ~v1_funct_1(B_112) | ~v1_relat_1(B_112) | ~v1_funct_1(A_111) | ~v1_relat_1(A_111))), inference(cnfTransformation, [status(thm)], [f_102])).
% 6.07/2.23  tff(c_807, plain, (![B_112]: (r2_hidden('#skF_5'('#skF_7', B_112), '#skF_6') | B_112='#skF_7' | k1_relat_1(B_112)!=k1_relat_1('#skF_7') | ~v1_funct_1(B_112) | ~v1_relat_1(B_112) | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_85, c_800])).
% 6.07/2.23  tff(c_813, plain, (![B_112]: (r2_hidden('#skF_5'('#skF_7', B_112), '#skF_6') | B_112='#skF_7' | k1_relat_1(B_112)!='#skF_6' | ~v1_funct_1(B_112) | ~v1_relat_1(B_112))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_85, c_807])).
% 6.07/2.23  tff(c_4, plain, (![A_1]: (k2_relat_1(k6_relat_1(A_1))=A_1)), inference(cnfTransformation, [status(thm)], [f_29])).
% 6.07/2.23  tff(c_223, plain, (![A_79, C_80]: (r2_hidden('#skF_4'(A_79, k2_relat_1(A_79), C_80), k1_relat_1(A_79)) | ~r2_hidden(C_80, k2_relat_1(A_79)) | ~v1_funct_1(A_79) | ~v1_relat_1(A_79))), inference(cnfTransformation, [status(thm)], [f_52])).
% 6.07/2.23  tff(c_229, plain, (![A_1, C_80]: (r2_hidden('#skF_4'(k6_relat_1(A_1), k2_relat_1(k6_relat_1(A_1)), C_80), A_1) | ~r2_hidden(C_80, k2_relat_1(k6_relat_1(A_1))) | ~v1_funct_1(k6_relat_1(A_1)) | ~v1_relat_1(k6_relat_1(A_1)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_223])).
% 6.07/2.23  tff(c_236, plain, (![A_1, C_80]: (r2_hidden('#skF_4'(k6_relat_1(A_1), A_1, C_80), A_1) | ~r2_hidden(C_80, A_1))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_30, c_4, c_4, c_229])).
% 6.07/2.23  tff(c_12, plain, (![A_4, C_40]: (k1_funct_1(A_4, '#skF_4'(A_4, k2_relat_1(A_4), C_40))=C_40 | ~r2_hidden(C_40, k2_relat_1(A_4)) | ~v1_funct_1(A_4) | ~v1_relat_1(A_4))), inference(cnfTransformation, [status(thm)], [f_52])).
% 6.07/2.23  tff(c_90, plain, (![A_66]: (k5_relat_1(k6_relat_1(k1_relat_1(A_66)), A_66)=A_66 | ~v1_relat_1(A_66))), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.07/2.23  tff(c_99, plain, (k5_relat_1(k6_relat_1('#skF_6'), '#skF_7')='#skF_7' | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_85, c_90])).
% 6.07/2.23  tff(c_106, plain, (k5_relat_1(k6_relat_1('#skF_6'), '#skF_7')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_46, c_99])).
% 6.07/2.23  tff(c_1535, plain, (![B_140, C_141, A_142]: (k1_funct_1(k5_relat_1(B_140, C_141), A_142)=k1_funct_1(C_141, k1_funct_1(B_140, A_142)) | ~r2_hidden(A_142, k1_relat_1(B_140)) | ~v1_funct_1(C_141) | ~v1_relat_1(C_141) | ~v1_funct_1(B_140) | ~v1_relat_1(B_140))), inference(cnfTransformation, [status(thm)], [f_84])).
% 6.07/2.23  tff(c_1577, plain, (![A_1, C_141, A_142]: (k1_funct_1(k5_relat_1(k6_relat_1(A_1), C_141), A_142)=k1_funct_1(C_141, k1_funct_1(k6_relat_1(A_1), A_142)) | ~r2_hidden(A_142, A_1) | ~v1_funct_1(C_141) | ~v1_relat_1(C_141) | ~v1_funct_1(k6_relat_1(A_1)) | ~v1_relat_1(k6_relat_1(A_1)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1535])).
% 6.07/2.23  tff(c_1699, plain, (![A_146, C_147, A_148]: (k1_funct_1(k5_relat_1(k6_relat_1(A_146), C_147), A_148)=k1_funct_1(C_147, k1_funct_1(k6_relat_1(A_146), A_148)) | ~r2_hidden(A_148, A_146) | ~v1_funct_1(C_147) | ~v1_relat_1(C_147))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_30, c_1577])).
% 6.07/2.23  tff(c_1737, plain, (![A_148]: (k1_funct_1('#skF_7', k1_funct_1(k6_relat_1('#skF_6'), A_148))=k1_funct_1('#skF_7', A_148) | ~r2_hidden(A_148, '#skF_6') | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_106, c_1699])).
% 6.07/2.23  tff(c_1749, plain, (![A_149]: (k1_funct_1('#skF_7', k1_funct_1(k6_relat_1('#skF_6'), A_149))=k1_funct_1('#skF_7', A_149) | ~r2_hidden(A_149, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_1737])).
% 6.07/2.23  tff(c_147, plain, (![A_70, D_71]: (r2_hidden(k1_funct_1(A_70, D_71), k2_relat_1(A_70)) | ~r2_hidden(D_71, k1_relat_1(A_70)) | ~v1_funct_1(A_70) | ~v1_relat_1(A_70))), inference(cnfTransformation, [status(thm)], [f_52])).
% 6.07/2.23  tff(c_150, plain, (![A_1, D_71]: (r2_hidden(k1_funct_1(k6_relat_1(A_1), D_71), A_1) | ~r2_hidden(D_71, k1_relat_1(k6_relat_1(A_1))) | ~v1_funct_1(k6_relat_1(A_1)) | ~v1_relat_1(k6_relat_1(A_1)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_147])).
% 6.07/2.23  tff(c_170, plain, (![A_74, D_75]: (r2_hidden(k1_funct_1(k6_relat_1(A_74), D_75), A_74) | ~r2_hidden(D_75, A_74))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_30, c_2, c_150])).
% 6.07/2.23  tff(c_54, plain, (![C_61]: (k6_relat_1('#skF_6')='#skF_7' | k1_funct_1('#skF_7', C_61)=C_61 | ~r2_hidden(C_61, '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_116])).
% 6.07/2.23  tff(c_141, plain, (![C_61]: (k1_funct_1('#skF_7', C_61)=C_61 | ~r2_hidden(C_61, '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_111, c_54])).
% 6.07/2.23  tff(c_179, plain, (![D_75]: (k1_funct_1('#skF_7', k1_funct_1(k6_relat_1('#skF_6'), D_75))=k1_funct_1(k6_relat_1('#skF_6'), D_75) | ~r2_hidden(D_75, '#skF_6'))), inference(resolution, [status(thm)], [c_170, c_141])).
% 6.07/2.23  tff(c_1806, plain, (![A_150]: (k1_funct_1(k6_relat_1('#skF_6'), A_150)=k1_funct_1('#skF_7', A_150) | ~r2_hidden(A_150, '#skF_6') | ~r2_hidden(A_150, '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_1749, c_179])).
% 6.07/2.23  tff(c_1860, plain, (![C_40]: (k1_funct_1('#skF_7', '#skF_4'(k6_relat_1('#skF_6'), k2_relat_1(k6_relat_1('#skF_6')), C_40))=C_40 | ~r2_hidden('#skF_4'(k6_relat_1('#skF_6'), k2_relat_1(k6_relat_1('#skF_6')), C_40), '#skF_6') | ~r2_hidden('#skF_4'(k6_relat_1('#skF_6'), k2_relat_1(k6_relat_1('#skF_6')), C_40), '#skF_6') | ~r2_hidden(C_40, k2_relat_1(k6_relat_1('#skF_6'))) | ~v1_funct_1(k6_relat_1('#skF_6')) | ~v1_relat_1(k6_relat_1('#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_12, c_1806])).
% 6.07/2.23  tff(c_1949, plain, (![C_156]: (k1_funct_1('#skF_7', '#skF_4'(k6_relat_1('#skF_6'), '#skF_6', C_156))=C_156 | ~r2_hidden('#skF_4'(k6_relat_1('#skF_6'), '#skF_6', C_156), '#skF_6') | ~r2_hidden(C_156, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_30, c_4, c_4, c_4, c_4, c_1860])).
% 6.07/2.23  tff(c_1955, plain, (![C_157]: (k1_funct_1('#skF_7', '#skF_4'(k6_relat_1('#skF_6'), '#skF_6', C_157))=C_157 | ~r2_hidden(C_157, '#skF_6'))), inference(resolution, [status(thm)], [c_236, c_1949])).
% 6.07/2.23  tff(c_239, plain, (![A_81, C_82]: (r2_hidden('#skF_4'(k6_relat_1(A_81), A_81, C_82), A_81) | ~r2_hidden(C_82, A_81))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_30, c_4, c_4, c_229])).
% 6.07/2.23  tff(c_244, plain, (![C_82]: (k1_funct_1('#skF_7', '#skF_4'(k6_relat_1('#skF_6'), '#skF_6', C_82))='#skF_4'(k6_relat_1('#skF_6'), '#skF_6', C_82) | ~r2_hidden(C_82, '#skF_6'))), inference(resolution, [status(thm)], [c_239, c_141])).
% 6.07/2.23  tff(c_2113, plain, (![C_159]: ('#skF_4'(k6_relat_1('#skF_6'), '#skF_6', C_159)=C_159 | ~r2_hidden(C_159, '#skF_6') | ~r2_hidden(C_159, '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_1955, c_244])).
% 6.07/2.23  tff(c_153, plain, (![A_72, C_73]: (k1_funct_1(A_72, '#skF_4'(A_72, k2_relat_1(A_72), C_73))=C_73 | ~r2_hidden(C_73, k2_relat_1(A_72)) | ~v1_funct_1(A_72) | ~v1_relat_1(A_72))), inference(cnfTransformation, [status(thm)], [f_52])).
% 6.07/2.23  tff(c_165, plain, (![A_1, C_73]: (k1_funct_1(k6_relat_1(A_1), '#skF_4'(k6_relat_1(A_1), A_1, C_73))=C_73 | ~r2_hidden(C_73, k2_relat_1(k6_relat_1(A_1))) | ~v1_funct_1(k6_relat_1(A_1)) | ~v1_relat_1(k6_relat_1(A_1)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_153])).
% 6.07/2.23  tff(c_169, plain, (![A_1, C_73]: (k1_funct_1(k6_relat_1(A_1), '#skF_4'(k6_relat_1(A_1), A_1, C_73))=C_73 | ~r2_hidden(C_73, A_1))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_30, c_4, c_165])).
% 6.07/2.23  tff(c_2131, plain, (![C_159]: (k1_funct_1(k6_relat_1('#skF_6'), C_159)=C_159 | ~r2_hidden(C_159, '#skF_6') | ~r2_hidden(C_159, '#skF_6') | ~r2_hidden(C_159, '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_2113, c_169])).
% 6.07/2.23  tff(c_920, plain, (![B_117]: (r2_hidden('#skF_5'('#skF_7', B_117), '#skF_6') | B_117='#skF_7' | k1_relat_1(B_117)!='#skF_6' | ~v1_funct_1(B_117) | ~v1_relat_1(B_117))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_85, c_807])).
% 6.07/2.23  tff(c_928, plain, (![B_117]: (k1_funct_1('#skF_7', '#skF_5'('#skF_7', B_117))='#skF_5'('#skF_7', B_117) | B_117='#skF_7' | k1_relat_1(B_117)!='#skF_6' | ~v1_funct_1(B_117) | ~v1_relat_1(B_117))), inference(resolution, [status(thm)], [c_920, c_141])).
% 6.07/2.23  tff(c_2943, plain, (![B_175, A_176]: (k1_funct_1(B_175, '#skF_5'(A_176, B_175))!=k1_funct_1(A_176, '#skF_5'(A_176, B_175)) | B_175=A_176 | k1_relat_1(B_175)!=k1_relat_1(A_176) | ~v1_funct_1(B_175) | ~v1_relat_1(B_175) | ~v1_funct_1(A_176) | ~v1_relat_1(A_176))), inference(cnfTransformation, [status(thm)], [f_102])).
% 6.07/2.23  tff(c_2986, plain, (![B_117]: (k1_funct_1(B_117, '#skF_5'('#skF_7', B_117))!='#skF_5'('#skF_7', B_117) | B_117='#skF_7' | k1_relat_1(B_117)!=k1_relat_1('#skF_7') | ~v1_funct_1(B_117) | ~v1_relat_1(B_117) | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7') | B_117='#skF_7' | k1_relat_1(B_117)!='#skF_6' | ~v1_funct_1(B_117) | ~v1_relat_1(B_117))), inference(superposition, [status(thm), theory('equality')], [c_928, c_2943])).
% 6.07/2.23  tff(c_3001, plain, (![B_177]: (k1_funct_1(B_177, '#skF_5'('#skF_7', B_177))!='#skF_5'('#skF_7', B_177) | B_177='#skF_7' | k1_relat_1(B_177)!='#skF_6' | ~v1_funct_1(B_177) | ~v1_relat_1(B_177))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_85, c_2986])).
% 6.07/2.23  tff(c_3009, plain, (k6_relat_1('#skF_6')='#skF_7' | k1_relat_1(k6_relat_1('#skF_6'))!='#skF_6' | ~v1_funct_1(k6_relat_1('#skF_6')) | ~v1_relat_1(k6_relat_1('#skF_6')) | ~r2_hidden('#skF_5'('#skF_7', k6_relat_1('#skF_6')), '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_2131, c_3001])).
% 6.07/2.23  tff(c_3031, plain, (k6_relat_1('#skF_6')='#skF_7' | ~r2_hidden('#skF_5'('#skF_7', k6_relat_1('#skF_6')), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_30, c_2, c_3009])).
% 6.07/2.23  tff(c_3032, plain, (~r2_hidden('#skF_5'('#skF_7', k6_relat_1('#skF_6')), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_111, c_3031])).
% 6.07/2.23  tff(c_3042, plain, (k6_relat_1('#skF_6')='#skF_7' | k1_relat_1(k6_relat_1('#skF_6'))!='#skF_6' | ~v1_funct_1(k6_relat_1('#skF_6')) | ~v1_relat_1(k6_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_813, c_3032])).
% 6.07/2.23  tff(c_3045, plain, (k6_relat_1('#skF_6')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_28, c_30, c_2, c_3042])).
% 6.07/2.23  tff(c_3047, plain, $false, inference(negUnitSimplification, [status(thm)], [c_111, c_3045])).
% 6.07/2.23  tff(c_3049, plain, (k6_relat_1('#skF_6')='#skF_7'), inference(splitRight, [status(thm)], [c_110])).
% 6.07/2.23  tff(c_50, plain, (k1_funct_1('#skF_7', '#skF_8')!='#skF_8' | k1_relat_1('#skF_7')!='#skF_6' | k6_relat_1('#skF_6')!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_116])).
% 6.07/2.23  tff(c_3051, plain, (k1_funct_1('#skF_7', '#skF_8')!='#skF_8' | k6_relat_1('#skF_6')!='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_85, c_50])).
% 6.07/2.23  tff(c_3052, plain, (k6_relat_1('#skF_6')!='#skF_7'), inference(splitLeft, [status(thm)], [c_3051])).
% 6.07/2.23  tff(c_3071, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3049, c_3052])).
% 6.07/2.23  tff(c_3072, plain, (k1_funct_1('#skF_7', '#skF_8')!='#skF_8'), inference(splitRight, [status(thm)], [c_3051])).
% 6.07/2.23  tff(c_3048, plain, (r2_hidden('#skF_8', '#skF_6')), inference(splitRight, [status(thm)], [c_110])).
% 6.07/2.23  tff(c_3080, plain, (k2_relat_1('#skF_7')='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_3049, c_4])).
% 6.07/2.23  tff(c_3234, plain, (![A_190, C_191]: (r2_hidden('#skF_4'(A_190, k2_relat_1(A_190), C_191), k1_relat_1(A_190)) | ~r2_hidden(C_191, k2_relat_1(A_190)) | ~v1_funct_1(A_190) | ~v1_relat_1(A_190))), inference(cnfTransformation, [status(thm)], [f_52])).
% 6.07/2.23  tff(c_3240, plain, (![C_191]: (r2_hidden('#skF_4'('#skF_7', k2_relat_1('#skF_7'), C_191), '#skF_6') | ~r2_hidden(C_191, k2_relat_1('#skF_7')) | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_85, c_3234])).
% 6.07/2.23  tff(c_3250, plain, (![C_191]: (r2_hidden('#skF_4'('#skF_7', '#skF_6', C_191), '#skF_6') | ~r2_hidden(C_191, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_3080, c_3080, c_3240])).
% 6.07/2.23  tff(c_8, plain, (![A_3]: (k5_relat_1(A_3, k6_relat_1(k2_relat_1(A_3)))=A_3 | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_37])).
% 6.07/2.23  tff(c_3548, plain, (![B_219, C_220, A_221]: (k1_funct_1(k5_relat_1(B_219, C_220), A_221)=k1_funct_1(C_220, k1_funct_1(B_219, A_221)) | ~r2_hidden(A_221, k1_relat_1(B_219)) | ~v1_funct_1(C_220) | ~v1_relat_1(C_220) | ~v1_funct_1(B_219) | ~v1_relat_1(B_219))), inference(cnfTransformation, [status(thm)], [f_84])).
% 6.07/2.23  tff(c_3587, plain, (![C_220, A_221]: (k1_funct_1(k5_relat_1('#skF_7', C_220), A_221)=k1_funct_1(C_220, k1_funct_1('#skF_7', A_221)) | ~r2_hidden(A_221, '#skF_6') | ~v1_funct_1(C_220) | ~v1_relat_1(C_220) | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_85, c_3548])).
% 6.07/2.23  tff(c_3696, plain, (![C_225, A_226]: (k1_funct_1(k5_relat_1('#skF_7', C_225), A_226)=k1_funct_1(C_225, k1_funct_1('#skF_7', A_226)) | ~r2_hidden(A_226, '#skF_6') | ~v1_funct_1(C_225) | ~v1_relat_1(C_225))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_3587])).
% 6.07/2.23  tff(c_3728, plain, (![A_226]: (k1_funct_1(k6_relat_1(k2_relat_1('#skF_7')), k1_funct_1('#skF_7', A_226))=k1_funct_1('#skF_7', A_226) | ~r2_hidden(A_226, '#skF_6') | ~v1_funct_1(k6_relat_1(k2_relat_1('#skF_7'))) | ~v1_relat_1(k6_relat_1(k2_relat_1('#skF_7'))) | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_8, c_3696])).
% 6.07/2.23  tff(c_3738, plain, (![A_227]: (k1_funct_1('#skF_7', k1_funct_1('#skF_7', A_227))=k1_funct_1('#skF_7', A_227) | ~r2_hidden(A_227, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_28, c_30, c_3049, c_3080, c_3728])).
% 6.07/2.23  tff(c_3768, plain, (![C_40]: (k1_funct_1('#skF_7', '#skF_4'('#skF_7', k2_relat_1('#skF_7'), C_40))=k1_funct_1('#skF_7', C_40) | ~r2_hidden('#skF_4'('#skF_7', k2_relat_1('#skF_7'), C_40), '#skF_6') | ~r2_hidden(C_40, k2_relat_1('#skF_7')) | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_12, c_3738])).
% 6.07/2.23  tff(c_3791, plain, (![C_229]: (k1_funct_1('#skF_7', '#skF_4'('#skF_7', '#skF_6', C_229))=k1_funct_1('#skF_7', C_229) | ~r2_hidden('#skF_4'('#skF_7', '#skF_6', C_229), '#skF_6') | ~r2_hidden(C_229, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_3080, c_3080, c_3080, c_3768])).
% 6.07/2.23  tff(c_3796, plain, (![C_230]: (k1_funct_1('#skF_7', '#skF_4'('#skF_7', '#skF_6', C_230))=k1_funct_1('#skF_7', C_230) | ~r2_hidden(C_230, '#skF_6'))), inference(resolution, [status(thm)], [c_3250, c_3791])).
% 6.07/2.23  tff(c_3158, plain, (![A_185, C_186]: (k1_funct_1(A_185, '#skF_4'(A_185, k2_relat_1(A_185), C_186))=C_186 | ~r2_hidden(C_186, k2_relat_1(A_185)) | ~v1_funct_1(A_185) | ~v1_relat_1(A_185))), inference(cnfTransformation, [status(thm)], [f_52])).
% 6.07/2.23  tff(c_3178, plain, (![C_186]: (k1_funct_1('#skF_7', '#skF_4'('#skF_7', '#skF_6', C_186))=C_186 | ~r2_hidden(C_186, k2_relat_1('#skF_7')) | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_3080, c_3158])).
% 6.07/2.23  tff(c_3189, plain, (![C_186]: (k1_funct_1('#skF_7', '#skF_4'('#skF_7', '#skF_6', C_186))=C_186 | ~r2_hidden(C_186, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_3080, c_3178])).
% 6.07/2.23  tff(c_3827, plain, (![C_231]: (k1_funct_1('#skF_7', C_231)=C_231 | ~r2_hidden(C_231, '#skF_6') | ~r2_hidden(C_231, '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_3796, c_3189])).
% 6.07/2.23  tff(c_3860, plain, (k1_funct_1('#skF_7', '#skF_8')='#skF_8' | ~r2_hidden('#skF_8', '#skF_6')), inference(resolution, [status(thm)], [c_3048, c_3827])).
% 6.07/2.23  tff(c_3878, plain, (k1_funct_1('#skF_7', '#skF_8')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_3048, c_3860])).
% 6.07/2.23  tff(c_3880, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3072, c_3878])).
% 6.07/2.23  tff(c_3882, plain, (k1_relat_1('#skF_7')!='#skF_6'), inference(splitRight, [status(thm)], [c_60])).
% 6.07/2.23  tff(c_3881, plain, (k6_relat_1('#skF_6')='#skF_7'), inference(splitRight, [status(thm)], [c_60])).
% 6.07/2.23  tff(c_3886, plain, (k1_relat_1('#skF_7')='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_3881, c_2])).
% 6.07/2.23  tff(c_3903, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3882, c_3886])).
% 6.07/2.23  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.07/2.23  
% 6.07/2.23  Inference rules
% 6.07/2.23  ----------------------
% 6.07/2.23  #Ref     : 2
% 6.07/2.23  #Sup     : 877
% 6.07/2.23  #Fact    : 0
% 6.07/2.23  #Define  : 0
% 6.07/2.23  #Split   : 4
% 6.07/2.23  #Chain   : 0
% 6.07/2.23  #Close   : 0
% 6.07/2.23  
% 6.07/2.23  Ordering : KBO
% 6.07/2.23  
% 6.07/2.23  Simplification rules
% 6.07/2.23  ----------------------
% 6.07/2.23  #Subsume      : 174
% 6.07/2.23  #Demod        : 833
% 6.07/2.23  #Tautology    : 248
% 6.07/2.23  #SimpNegUnit  : 7
% 6.07/2.23  #BackRed      : 8
% 6.07/2.23  
% 6.07/2.23  #Partial instantiations: 0
% 6.07/2.23  #Strategies tried      : 1
% 6.07/2.23  
% 6.07/2.23  Timing (in seconds)
% 6.07/2.23  ----------------------
% 6.07/2.23  Preprocessing        : 0.34
% 6.07/2.23  Parsing              : 0.17
% 6.07/2.23  CNF conversion       : 0.03
% 6.07/2.23  Main loop            : 1.08
% 6.07/2.23  Inferencing          : 0.38
% 6.07/2.23  Reduction            : 0.36
% 6.07/2.23  Demodulation         : 0.25
% 6.07/2.23  BG Simplification    : 0.06
% 6.07/2.23  Subsumption          : 0.21
% 6.07/2.23  Abstraction          : 0.06
% 6.07/2.23  MUC search           : 0.00
% 6.07/2.23  Cooper               : 0.00
% 6.07/2.23  Total                : 1.47
% 6.07/2.23  Index Insertion      : 0.00
% 6.07/2.23  Index Deletion       : 0.00
% 6.07/2.23  Index Matching       : 0.00
% 6.07/2.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
