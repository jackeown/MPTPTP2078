%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:39 EST 2020

% Result     : Theorem 28.99s
% Output     : CNFRefutation 29.12s
% Verified   : 
% Statistics : Number of formulae       :  221 (7892 expanded)
%              Number of leaves         :   29 (2685 expanded)
%              Depth                    :   35
%              Number of atoms          :  646 (30337 expanded)
%              Number of equality atoms :  145 (6121 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_5 > #skF_4 > #skF_7 > #skF_3 > #skF_8 > #skF_2 > #skF_1 > #skF_6

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_5',type,(
    '#skF_5': $i > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_6',type,(
    '#skF_6': $i > $i )).

tff(f_134,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ! [B] :
            ( ( v1_relat_1(B)
              & v1_funct_1(B) )
           => ( ( v2_funct_1(k5_relat_1(B,A))
                & k2_relat_1(B) = k1_relat_1(A) )
             => ( v2_funct_1(B)
                & v2_funct_1(A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_funct_1)).

tff(f_61,axiom,(
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

tff(f_76,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
      <=> ! [B,C] :
            ( ( r2_hidden(B,k1_relat_1(A))
              & r2_hidden(C,k1_relat_1(A))
              & k1_funct_1(A,B) = k1_funct_1(A,C) )
           => B = C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_funct_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_116,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( ( v2_funct_1(k5_relat_1(B,A))
              & r1_tarski(k2_relat_1(B),k1_relat_1(A)) )
           => v2_funct_1(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_funct_1)).

tff(f_46,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k2_relat_1(A),k1_relat_1(B))
           => k1_relat_1(k5_relat_1(A,B)) = k1_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_relat_1)).

tff(f_101,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ! [C] :
          ( ( v1_relat_1(C)
            & v1_funct_1(C) )
         => ( r2_hidden(A,k1_relat_1(k5_relat_1(C,B)))
           => k1_funct_1(k5_relat_1(C,B),A) = k1_funct_1(B,k1_funct_1(C,A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_funct_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_88,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A)
        & v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v1_relat_1(k5_relat_1(A,B))
        & v1_funct_1(k5_relat_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_funct_1)).

tff(c_60,plain,(
    v1_relat_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_58,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_16,plain,(
    ! [A_8,C_44] :
      ( r2_hidden('#skF_4'(A_8,k2_relat_1(A_8),C_44),k1_relat_1(A_8))
      | ~ r2_hidden(C_44,k2_relat_1(A_8))
      | ~ v1_funct_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_14,plain,(
    ! [A_8,C_44] :
      ( k1_funct_1(A_8,'#skF_4'(A_8,k2_relat_1(A_8),C_44)) = C_44
      | ~ r2_hidden(C_44,k2_relat_1(A_8))
      | ~ v1_funct_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_263,plain,(
    ! [A_99] :
      ( '#skF_5'(A_99) != '#skF_6'(A_99)
      | v2_funct_1(A_99)
      | ~ v1_funct_1(A_99)
      | ~ v1_relat_1(A_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_52,plain,(
    v2_funct_1(k5_relat_1('#skF_8','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_48,plain,
    ( ~ v2_funct_1('#skF_7')
    | ~ v2_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_63,plain,(
    ~ v2_funct_1('#skF_8') ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_56,plain,(
    v1_relat_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_54,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_50,plain,(
    k2_relat_1('#skF_8') = k1_relat_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_223,plain,(
    ! [B_92,A_93] :
      ( v2_funct_1(B_92)
      | ~ r1_tarski(k2_relat_1(B_92),k1_relat_1(A_93))
      | ~ v2_funct_1(k5_relat_1(B_92,A_93))
      | ~ v1_funct_1(B_92)
      | ~ v1_relat_1(B_92)
      | ~ v1_funct_1(A_93)
      | ~ v1_relat_1(A_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_229,plain,(
    ! [A_93] :
      ( v2_funct_1('#skF_8')
      | ~ r1_tarski(k1_relat_1('#skF_7'),k1_relat_1(A_93))
      | ~ v2_funct_1(k5_relat_1('#skF_8',A_93))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8')
      | ~ v1_funct_1(A_93)
      | ~ v1_relat_1(A_93) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_223])).

tff(c_233,plain,(
    ! [A_93] :
      ( v2_funct_1('#skF_8')
      | ~ r1_tarski(k1_relat_1('#skF_7'),k1_relat_1(A_93))
      | ~ v2_funct_1(k5_relat_1('#skF_8',A_93))
      | ~ v1_funct_1(A_93)
      | ~ v1_relat_1(A_93) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_229])).

tff(c_235,plain,(
    ! [A_94] :
      ( ~ r1_tarski(k1_relat_1('#skF_7'),k1_relat_1(A_94))
      | ~ v2_funct_1(k5_relat_1('#skF_8',A_94))
      | ~ v1_funct_1(A_94)
      | ~ v1_relat_1(A_94) ) ),
    inference(negUnitSimplification,[status(thm)],[c_63,c_233])).

tff(c_242,plain,
    ( ~ v2_funct_1(k5_relat_1('#skF_8','#skF_7'))
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_6,c_235])).

tff(c_248,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_52,c_242])).

tff(c_249,plain,(
    ~ v2_funct_1('#skF_7') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_266,plain,
    ( '#skF_5'('#skF_7') != '#skF_6'('#skF_7')
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_263,c_249])).

tff(c_269,plain,(
    '#skF_5'('#skF_7') != '#skF_6'('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_266])).

tff(c_36,plain,(
    ! [A_48] :
      ( r2_hidden('#skF_6'(A_48),k1_relat_1(A_48))
      | v2_funct_1(A_48)
      | ~ v1_funct_1(A_48)
      | ~ v1_relat_1(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_330,plain,(
    ! [A_111,C_112] :
      ( k1_funct_1(A_111,'#skF_4'(A_111,k2_relat_1(A_111),C_112)) = C_112
      | ~ r2_hidden(C_112,k2_relat_1(A_111))
      | ~ v1_funct_1(A_111)
      | ~ v1_relat_1(A_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_346,plain,(
    ! [C_112] :
      ( k1_funct_1('#skF_8','#skF_4'('#skF_8',k1_relat_1('#skF_7'),C_112)) = C_112
      | ~ r2_hidden(C_112,k2_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_330])).

tff(c_352,plain,(
    ! [C_112] :
      ( k1_funct_1('#skF_8','#skF_4'('#skF_8',k1_relat_1('#skF_7'),C_112)) = C_112
      | ~ r2_hidden(C_112,k1_relat_1('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_50,c_346])).

tff(c_370,plain,(
    ! [A_114,C_115] :
      ( r2_hidden('#skF_4'(A_114,k2_relat_1(A_114),C_115),k1_relat_1(A_114))
      | ~ r2_hidden(C_115,k2_relat_1(A_114))
      | ~ v1_funct_1(A_114)
      | ~ v1_relat_1(A_114) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_376,plain,(
    ! [C_115] :
      ( r2_hidden('#skF_4'('#skF_8',k1_relat_1('#skF_7'),C_115),k1_relat_1('#skF_8'))
      | ~ r2_hidden(C_115,k2_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_370])).

tff(c_378,plain,(
    ! [C_115] :
      ( r2_hidden('#skF_4'('#skF_8',k1_relat_1('#skF_7'),C_115),k1_relat_1('#skF_8'))
      | ~ r2_hidden(C_115,k1_relat_1('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_50,c_376])).

tff(c_250,plain,(
    v2_funct_1('#skF_8') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_28,plain,(
    ! [A_8,B_30] :
      ( r2_hidden('#skF_2'(A_8,B_30),k1_relat_1(A_8))
      | r2_hidden('#skF_3'(A_8,B_30),B_30)
      | k2_relat_1(A_8) = B_30
      | ~ v1_funct_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_417,plain,(
    ! [A_124,B_125] :
      ( k1_funct_1(A_124,'#skF_2'(A_124,B_125)) = '#skF_1'(A_124,B_125)
      | r2_hidden('#skF_3'(A_124,B_125),B_125)
      | k2_relat_1(A_124) = B_125
      | ~ v1_funct_1(A_124)
      | ~ v1_relat_1(A_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_12,plain,(
    ! [A_8,D_47] :
      ( r2_hidden(k1_funct_1(A_8,D_47),k2_relat_1(A_8))
      | ~ r2_hidden(D_47,k1_relat_1(A_8))
      | ~ v1_funct_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_784,plain,(
    ! [A_157,B_158] :
      ( r2_hidden('#skF_1'(A_157,B_158),k2_relat_1(A_157))
      | ~ r2_hidden('#skF_2'(A_157,B_158),k1_relat_1(A_157))
      | ~ v1_funct_1(A_157)
      | ~ v1_relat_1(A_157)
      | r2_hidden('#skF_3'(A_157,B_158),B_158)
      | k2_relat_1(A_157) = B_158
      | ~ v1_funct_1(A_157)
      | ~ v1_relat_1(A_157) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_417,c_12])).

tff(c_792,plain,(
    ! [A_159,B_160] :
      ( r2_hidden('#skF_1'(A_159,B_160),k2_relat_1(A_159))
      | r2_hidden('#skF_3'(A_159,B_160),B_160)
      | k2_relat_1(A_159) = B_160
      | ~ v1_funct_1(A_159)
      | ~ v1_relat_1(A_159) ) ),
    inference(resolution,[status(thm)],[c_28,c_784])).

tff(c_808,plain,(
    ! [B_160] :
      ( r2_hidden('#skF_1'('#skF_8',B_160),k1_relat_1('#skF_7'))
      | r2_hidden('#skF_3'('#skF_8',B_160),B_160)
      | k2_relat_1('#skF_8') = B_160
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_792])).

tff(c_817,plain,(
    ! [B_161] :
      ( r2_hidden('#skF_1'('#skF_8',B_161),k1_relat_1('#skF_7'))
      | r2_hidden('#skF_3'('#skF_8',B_161),B_161)
      | k1_relat_1('#skF_7') = B_161 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_50,c_808])).

tff(c_298,plain,(
    ! [A_108,B_109] :
      ( k1_relat_1(k5_relat_1(A_108,B_109)) = k1_relat_1(A_108)
      | ~ r1_tarski(k2_relat_1(A_108),k1_relat_1(B_109))
      | ~ v1_relat_1(B_109)
      | ~ v1_relat_1(A_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_301,plain,(
    ! [B_109] :
      ( k1_relat_1(k5_relat_1('#skF_8',B_109)) = k1_relat_1('#skF_8')
      | ~ r1_tarski(k1_relat_1('#skF_7'),k1_relat_1(B_109))
      | ~ v1_relat_1(B_109)
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_298])).

tff(c_304,plain,(
    ! [B_110] :
      ( k1_relat_1(k5_relat_1('#skF_8',B_110)) = k1_relat_1('#skF_8')
      | ~ r1_tarski(k1_relat_1('#skF_7'),k1_relat_1(B_110))
      | ~ v1_relat_1(B_110) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_301])).

tff(c_308,plain,
    ( k1_relat_1(k5_relat_1('#skF_8','#skF_7')) = k1_relat_1('#skF_8')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_6,c_304])).

tff(c_311,plain,(
    k1_relat_1(k5_relat_1('#skF_8','#skF_7')) = k1_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_308])).

tff(c_495,plain,(
    ! [C_138,B_139,A_140] :
      ( k1_funct_1(k5_relat_1(C_138,B_139),A_140) = k1_funct_1(B_139,k1_funct_1(C_138,A_140))
      | ~ r2_hidden(A_140,k1_relat_1(k5_relat_1(C_138,B_139)))
      | ~ v1_funct_1(C_138)
      | ~ v1_relat_1(C_138)
      | ~ v1_funct_1(B_139)
      | ~ v1_relat_1(B_139) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_518,plain,(
    ! [A_140] :
      ( k1_funct_1(k5_relat_1('#skF_8','#skF_7'),A_140) = k1_funct_1('#skF_7',k1_funct_1('#skF_8',A_140))
      | ~ r2_hidden(A_140,k1_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8')
      | ~ v1_funct_1('#skF_7')
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_311,c_495])).

tff(c_533,plain,(
    ! [A_140] :
      ( k1_funct_1(k5_relat_1('#skF_8','#skF_7'),A_140) = k1_funct_1('#skF_7',k1_funct_1('#skF_8',A_140))
      | ~ r2_hidden(A_140,k1_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_56,c_54,c_518])).

tff(c_833,plain,
    ( k1_funct_1(k5_relat_1('#skF_8','#skF_7'),'#skF_3'('#skF_8',k1_relat_1('#skF_8'))) = k1_funct_1('#skF_7',k1_funct_1('#skF_8','#skF_3'('#skF_8',k1_relat_1('#skF_8'))))
    | r2_hidden('#skF_1'('#skF_8',k1_relat_1('#skF_8')),k1_relat_1('#skF_7'))
    | k1_relat_1('#skF_7') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_817,c_533])).

tff(c_950,plain,(
    k1_relat_1('#skF_7') = k1_relat_1('#skF_8') ),
    inference(splitLeft,[status(thm)],[c_833])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( v1_relat_1(k5_relat_1(A_3,B_4))
      | ~ v1_relat_1(B_4)
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_303,plain,(
    ! [B_109] :
      ( k1_relat_1(k5_relat_1('#skF_8',B_109)) = k1_relat_1('#skF_8')
      | ~ r1_tarski(k1_relat_1('#skF_7'),k1_relat_1(B_109))
      | ~ v1_relat_1(B_109) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_301])).

tff(c_315,plain,
    ( k1_relat_1(k5_relat_1('#skF_8',k5_relat_1('#skF_8','#skF_7'))) = k1_relat_1('#skF_8')
    | ~ r1_tarski(k1_relat_1('#skF_7'),k1_relat_1('#skF_8'))
    | ~ v1_relat_1(k5_relat_1('#skF_8','#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_311,c_303])).

tff(c_380,plain,(
    ~ v1_relat_1(k5_relat_1('#skF_8','#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_315])).

tff(c_383,plain,
    ( ~ v1_relat_1('#skF_7')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_8,c_380])).

tff(c_387,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_60,c_383])).

tff(c_388,plain,
    ( ~ r1_tarski(k1_relat_1('#skF_7'),k1_relat_1('#skF_8'))
    | k1_relat_1(k5_relat_1('#skF_8',k5_relat_1('#skF_8','#skF_7'))) = k1_relat_1('#skF_8') ),
    inference(splitRight,[status(thm)],[c_315])).

tff(c_390,plain,(
    ~ r1_tarski(k1_relat_1('#skF_7'),k1_relat_1('#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_388])).

tff(c_964,plain,(
    ~ r1_tarski(k1_relat_1('#skF_8'),k1_relat_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_950,c_390])).

tff(c_972,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_964])).

tff(c_974,plain,(
    k1_relat_1('#skF_7') != k1_relat_1('#skF_8') ),
    inference(splitRight,[status(thm)],[c_833])).

tff(c_389,plain,(
    v1_relat_1(k5_relat_1('#skF_8','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_315])).

tff(c_40,plain,(
    ! [A_55,B_56] :
      ( v1_funct_1(k5_relat_1(A_55,B_56))
      | ~ v1_funct_1(B_56)
      | ~ v1_relat_1(B_56)
      | ~ v1_funct_1(A_55)
      | ~ v1_relat_1(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_373,plain,(
    ! [C_115] :
      ( r2_hidden('#skF_4'(k5_relat_1('#skF_8','#skF_7'),k2_relat_1(k5_relat_1('#skF_8','#skF_7')),C_115),k1_relat_1('#skF_8'))
      | ~ r2_hidden(C_115,k2_relat_1(k5_relat_1('#skF_8','#skF_7')))
      | ~ v1_funct_1(k5_relat_1('#skF_8','#skF_7'))
      | ~ v1_relat_1(k5_relat_1('#skF_8','#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_311,c_370])).

tff(c_432,plain,(
    ! [C_115] :
      ( r2_hidden('#skF_4'(k5_relat_1('#skF_8','#skF_7'),k2_relat_1(k5_relat_1('#skF_8','#skF_7')),C_115),k1_relat_1('#skF_8'))
      | ~ r2_hidden(C_115,k2_relat_1(k5_relat_1('#skF_8','#skF_7')))
      | ~ v1_funct_1(k5_relat_1('#skF_8','#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_389,c_373])).

tff(c_433,plain,(
    ~ v1_funct_1(k5_relat_1('#skF_8','#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_432])).

tff(c_436,plain,
    ( ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7')
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_40,c_433])).

tff(c_440,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_60,c_58,c_436])).

tff(c_442,plain,(
    v1_funct_1(k5_relat_1('#skF_8','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_432])).

tff(c_973,plain,
    ( r2_hidden('#skF_1'('#skF_8',k1_relat_1('#skF_8')),k1_relat_1('#skF_7'))
    | k1_funct_1(k5_relat_1('#skF_8','#skF_7'),'#skF_3'('#skF_8',k1_relat_1('#skF_8'))) = k1_funct_1('#skF_7',k1_funct_1('#skF_8','#skF_3'('#skF_8',k1_relat_1('#skF_8')))) ),
    inference(splitRight,[status(thm)],[c_833])).

tff(c_975,plain,(
    k1_funct_1(k5_relat_1('#skF_8','#skF_7'),'#skF_3'('#skF_8',k1_relat_1('#skF_8'))) = k1_funct_1('#skF_7',k1_funct_1('#skF_8','#skF_3'('#skF_8',k1_relat_1('#skF_8')))) ),
    inference(splitLeft,[status(thm)],[c_973])).

tff(c_987,plain,
    ( r2_hidden(k1_funct_1('#skF_7',k1_funct_1('#skF_8','#skF_3'('#skF_8',k1_relat_1('#skF_8')))),k2_relat_1(k5_relat_1('#skF_8','#skF_7')))
    | ~ r2_hidden('#skF_3'('#skF_8',k1_relat_1('#skF_8')),k1_relat_1(k5_relat_1('#skF_8','#skF_7')))
    | ~ v1_funct_1(k5_relat_1('#skF_8','#skF_7'))
    | ~ v1_relat_1(k5_relat_1('#skF_8','#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_975,c_12])).

tff(c_999,plain,
    ( r2_hidden(k1_funct_1('#skF_7',k1_funct_1('#skF_8','#skF_3'('#skF_8',k1_relat_1('#skF_8')))),k2_relat_1(k5_relat_1('#skF_8','#skF_7')))
    | ~ r2_hidden('#skF_3'('#skF_8',k1_relat_1('#skF_8')),k1_relat_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_389,c_442,c_311,c_987])).

tff(c_1001,plain,(
    ~ r2_hidden('#skF_3'('#skF_8',k1_relat_1('#skF_8')),k1_relat_1('#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_999])).

tff(c_1031,plain,
    ( r2_hidden('#skF_2'('#skF_8',k1_relat_1('#skF_8')),k1_relat_1('#skF_8'))
    | k2_relat_1('#skF_8') = k1_relat_1('#skF_8')
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_28,c_1001])).

tff(c_1051,plain,
    ( r2_hidden('#skF_2'('#skF_8',k1_relat_1('#skF_8')),k1_relat_1('#skF_8'))
    | k1_relat_1('#skF_7') = k1_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_50,c_1031])).

tff(c_1052,plain,(
    r2_hidden('#skF_2'('#skF_8',k1_relat_1('#skF_8')),k1_relat_1('#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_974,c_1051])).

tff(c_26,plain,(
    ! [A_8,B_30] :
      ( k1_funct_1(A_8,'#skF_2'(A_8,B_30)) = '#skF_1'(A_8,B_30)
      | r2_hidden('#skF_3'(A_8,B_30),B_30)
      | k2_relat_1(A_8) = B_30
      | ~ v1_funct_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1028,plain,
    ( k1_funct_1('#skF_8','#skF_2'('#skF_8',k1_relat_1('#skF_8'))) = '#skF_1'('#skF_8',k1_relat_1('#skF_8'))
    | k2_relat_1('#skF_8') = k1_relat_1('#skF_8')
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_26,c_1001])).

tff(c_1047,plain,
    ( k1_funct_1('#skF_8','#skF_2'('#skF_8',k1_relat_1('#skF_8'))) = '#skF_1'('#skF_8',k1_relat_1('#skF_8'))
    | k1_relat_1('#skF_7') = k1_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_50,c_1028])).

tff(c_1048,plain,(
    k1_funct_1('#skF_8','#skF_2'('#skF_8',k1_relat_1('#skF_8'))) = '#skF_1'('#skF_8',k1_relat_1('#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_974,c_1047])).

tff(c_30,plain,(
    ! [C_54,B_53,A_48] :
      ( C_54 = B_53
      | k1_funct_1(A_48,C_54) != k1_funct_1(A_48,B_53)
      | ~ r2_hidden(C_54,k1_relat_1(A_48))
      | ~ r2_hidden(B_53,k1_relat_1(A_48))
      | ~ v2_funct_1(A_48)
      | ~ v1_funct_1(A_48)
      | ~ v1_relat_1(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_1111,plain,(
    ! [C_54] :
      ( C_54 = '#skF_2'('#skF_8',k1_relat_1('#skF_8'))
      | k1_funct_1('#skF_8',C_54) != '#skF_1'('#skF_8',k1_relat_1('#skF_8'))
      | ~ r2_hidden(C_54,k1_relat_1('#skF_8'))
      | ~ r2_hidden('#skF_2'('#skF_8',k1_relat_1('#skF_8')),k1_relat_1('#skF_8'))
      | ~ v2_funct_1('#skF_8')
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1048,c_30])).

tff(c_1174,plain,(
    ! [C_180] :
      ( C_180 = '#skF_2'('#skF_8',k1_relat_1('#skF_8'))
      | k1_funct_1('#skF_8',C_180) != '#skF_1'('#skF_8',k1_relat_1('#skF_8'))
      | ~ r2_hidden(C_180,k1_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_250,c_1052,c_1111])).

tff(c_1270,plain,(
    ! [C_181] :
      ( '#skF_4'('#skF_8',k1_relat_1('#skF_7'),C_181) = '#skF_2'('#skF_8',k1_relat_1('#skF_8'))
      | k1_funct_1('#skF_8','#skF_4'('#skF_8',k1_relat_1('#skF_7'),C_181)) != '#skF_1'('#skF_8',k1_relat_1('#skF_8'))
      | ~ r2_hidden(C_181,k1_relat_1('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_378,c_1174])).

tff(c_1401,plain,(
    ! [C_190] :
      ( '#skF_4'('#skF_8',k1_relat_1('#skF_7'),C_190) = '#skF_2'('#skF_8',k1_relat_1('#skF_8'))
      | C_190 != '#skF_1'('#skF_8',k1_relat_1('#skF_8'))
      | ~ r2_hidden(C_190,k1_relat_1('#skF_7'))
      | ~ r2_hidden(C_190,k1_relat_1('#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_352,c_1270])).

tff(c_1447,plain,
    ( '#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_6'('#skF_7')) = '#skF_2'('#skF_8',k1_relat_1('#skF_8'))
    | '#skF_1'('#skF_8',k1_relat_1('#skF_8')) != '#skF_6'('#skF_7')
    | ~ r2_hidden('#skF_6'('#skF_7'),k1_relat_1('#skF_7'))
    | v2_funct_1('#skF_7')
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_36,c_1401])).

tff(c_1481,plain,
    ( '#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_6'('#skF_7')) = '#skF_2'('#skF_8',k1_relat_1('#skF_8'))
    | '#skF_1'('#skF_8',k1_relat_1('#skF_8')) != '#skF_6'('#skF_7')
    | ~ r2_hidden('#skF_6'('#skF_7'),k1_relat_1('#skF_7'))
    | v2_funct_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_1447])).

tff(c_1482,plain,
    ( '#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_6'('#skF_7')) = '#skF_2'('#skF_8',k1_relat_1('#skF_8'))
    | '#skF_1'('#skF_8',k1_relat_1('#skF_8')) != '#skF_6'('#skF_7')
    | ~ r2_hidden('#skF_6'('#skF_7'),k1_relat_1('#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_249,c_1481])).

tff(c_1517,plain,(
    ~ r2_hidden('#skF_6'('#skF_7'),k1_relat_1('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_1482])).

tff(c_1520,plain,
    ( v2_funct_1('#skF_7')
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_36,c_1517])).

tff(c_1523,plain,(
    v2_funct_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_1520])).

tff(c_1525,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_249,c_1523])).

tff(c_1527,plain,(
    r2_hidden('#skF_6'('#skF_7'),k1_relat_1('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_1482])).

tff(c_38,plain,(
    ! [A_48] :
      ( r2_hidden('#skF_5'(A_48),k1_relat_1(A_48))
      | v2_funct_1(A_48)
      | ~ v1_funct_1(A_48)
      | ~ v1_relat_1(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_34,plain,(
    ! [A_48] :
      ( k1_funct_1(A_48,'#skF_5'(A_48)) = k1_funct_1(A_48,'#skF_6'(A_48))
      | v2_funct_1(A_48)
      | ~ v1_funct_1(A_48)
      | ~ v1_relat_1(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_541,plain,(
    ! [A_143] :
      ( k1_funct_1(k5_relat_1('#skF_8','#skF_7'),A_143) = k1_funct_1('#skF_7',k1_funct_1('#skF_8',A_143))
      | ~ r2_hidden(A_143,k1_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_56,c_54,c_518])).

tff(c_629,plain,(
    ! [C_145] :
      ( k1_funct_1(k5_relat_1('#skF_8','#skF_7'),'#skF_4'('#skF_8',k1_relat_1('#skF_7'),C_145)) = k1_funct_1('#skF_7',k1_funct_1('#skF_8','#skF_4'('#skF_8',k1_relat_1('#skF_7'),C_145)))
      | ~ r2_hidden(C_145,k1_relat_1('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_378,c_541])).

tff(c_641,plain,(
    ! [C_145] :
      ( r2_hidden(k1_funct_1('#skF_7',k1_funct_1('#skF_8','#skF_4'('#skF_8',k1_relat_1('#skF_7'),C_145))),k2_relat_1(k5_relat_1('#skF_8','#skF_7')))
      | ~ r2_hidden('#skF_4'('#skF_8',k1_relat_1('#skF_7'),C_145),k1_relat_1(k5_relat_1('#skF_8','#skF_7')))
      | ~ v1_funct_1(k5_relat_1('#skF_8','#skF_7'))
      | ~ v1_relat_1(k5_relat_1('#skF_8','#skF_7'))
      | ~ r2_hidden(C_145,k1_relat_1('#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_629,c_12])).

tff(c_748,plain,(
    ! [C_154] :
      ( r2_hidden(k1_funct_1('#skF_7',k1_funct_1('#skF_8','#skF_4'('#skF_8',k1_relat_1('#skF_7'),C_154))),k2_relat_1(k5_relat_1('#skF_8','#skF_7')))
      | ~ r2_hidden('#skF_4'('#skF_8',k1_relat_1('#skF_7'),C_154),k1_relat_1('#skF_8'))
      | ~ r2_hidden(C_154,k1_relat_1('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_389,c_442,c_311,c_641])).

tff(c_752,plain,(
    ! [C_155] :
      ( r2_hidden(k1_funct_1('#skF_7',C_155),k2_relat_1(k5_relat_1('#skF_8','#skF_7')))
      | ~ r2_hidden('#skF_4'('#skF_8',k1_relat_1('#skF_7'),C_155),k1_relat_1('#skF_8'))
      | ~ r2_hidden(C_155,k1_relat_1('#skF_7'))
      | ~ r2_hidden(C_155,k1_relat_1('#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_352,c_748])).

tff(c_757,plain,(
    ! [C_156] :
      ( r2_hidden(k1_funct_1('#skF_7',C_156),k2_relat_1(k5_relat_1('#skF_8','#skF_7')))
      | ~ r2_hidden(C_156,k1_relat_1('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_378,c_752])).

tff(c_767,plain,
    ( r2_hidden(k1_funct_1('#skF_7','#skF_6'('#skF_7')),k2_relat_1(k5_relat_1('#skF_8','#skF_7')))
    | ~ r2_hidden('#skF_5'('#skF_7'),k1_relat_1('#skF_7'))
    | v2_funct_1('#skF_7')
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_757])).

tff(c_771,plain,
    ( r2_hidden(k1_funct_1('#skF_7','#skF_6'('#skF_7')),k2_relat_1(k5_relat_1('#skF_8','#skF_7')))
    | ~ r2_hidden('#skF_5'('#skF_7'),k1_relat_1('#skF_7'))
    | v2_funct_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_767])).

tff(c_772,plain,
    ( r2_hidden(k1_funct_1('#skF_7','#skF_6'('#skF_7')),k2_relat_1(k5_relat_1('#skF_8','#skF_7')))
    | ~ r2_hidden('#skF_5'('#skF_7'),k1_relat_1('#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_249,c_771])).

tff(c_773,plain,(
    ~ r2_hidden('#skF_5'('#skF_7'),k1_relat_1('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_772])).

tff(c_776,plain,
    ( v2_funct_1('#skF_7')
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_38,c_773])).

tff(c_779,plain,(
    v2_funct_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_776])).

tff(c_781,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_249,c_779])).

tff(c_783,plain,(
    r2_hidden('#skF_5'('#skF_7'),k1_relat_1('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_772])).

tff(c_583,plain,(
    ! [C_115] :
      ( k1_funct_1(k5_relat_1('#skF_8','#skF_7'),'#skF_4'('#skF_8',k1_relat_1('#skF_7'),C_115)) = k1_funct_1('#skF_7',k1_funct_1('#skF_8','#skF_4'('#skF_8',k1_relat_1('#skF_7'),C_115)))
      | ~ r2_hidden(C_115,k1_relat_1('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_378,c_541])).

tff(c_441,plain,(
    ! [C_115] :
      ( r2_hidden('#skF_4'(k5_relat_1('#skF_8','#skF_7'),k2_relat_1(k5_relat_1('#skF_8','#skF_7')),C_115),k1_relat_1('#skF_8'))
      | ~ r2_hidden(C_115,k2_relat_1(k5_relat_1('#skF_8','#skF_7'))) ) ),
    inference(splitRight,[status(thm)],[c_432])).

tff(c_282,plain,(
    ! [A_105,D_106] :
      ( r2_hidden(k1_funct_1(A_105,D_106),k2_relat_1(A_105))
      | ~ r2_hidden(D_106,k1_relat_1(A_105))
      | ~ v1_funct_1(A_105)
      | ~ v1_relat_1(A_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_288,plain,(
    ! [D_106] :
      ( r2_hidden(k1_funct_1('#skF_8',D_106),k1_relat_1('#skF_7'))
      | ~ r2_hidden(D_106,k1_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_282])).

tff(c_290,plain,(
    ! [D_106] :
      ( r2_hidden(k1_funct_1('#skF_8',D_106),k1_relat_1('#skF_7'))
      | ~ r2_hidden(D_106,k1_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_288])).

tff(c_3211,plain,(
    ! [C_258] :
      ( k1_funct_1(k5_relat_1('#skF_8','#skF_7'),'#skF_4'(k5_relat_1('#skF_8','#skF_7'),k2_relat_1(k5_relat_1('#skF_8','#skF_7')),C_258)) = k1_funct_1('#skF_7',k1_funct_1('#skF_8','#skF_4'(k5_relat_1('#skF_8','#skF_7'),k2_relat_1(k5_relat_1('#skF_8','#skF_7')),C_258)))
      | ~ r2_hidden(C_258,k2_relat_1(k5_relat_1('#skF_8','#skF_7'))) ) ),
    inference(resolution,[status(thm)],[c_441,c_541])).

tff(c_3234,plain,(
    ! [C_258] :
      ( k1_funct_1('#skF_7',k1_funct_1('#skF_8','#skF_4'(k5_relat_1('#skF_8','#skF_7'),k2_relat_1(k5_relat_1('#skF_8','#skF_7')),C_258))) = C_258
      | ~ r2_hidden(C_258,k2_relat_1(k5_relat_1('#skF_8','#skF_7')))
      | ~ v1_funct_1(k5_relat_1('#skF_8','#skF_7'))
      | ~ v1_relat_1(k5_relat_1('#skF_8','#skF_7'))
      | ~ r2_hidden(C_258,k2_relat_1(k5_relat_1('#skF_8','#skF_7'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3211,c_14])).

tff(c_3265,plain,(
    ! [C_259] :
      ( k1_funct_1('#skF_7',k1_funct_1('#skF_8','#skF_4'(k5_relat_1('#skF_8','#skF_7'),k2_relat_1(k5_relat_1('#skF_8','#skF_7')),C_259))) = C_259
      | ~ r2_hidden(C_259,k2_relat_1(k5_relat_1('#skF_8','#skF_7'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_389,c_442,c_3234])).

tff(c_3286,plain,(
    ! [C_259] :
      ( r2_hidden(C_259,k2_relat_1('#skF_7'))
      | ~ r2_hidden(k1_funct_1('#skF_8','#skF_4'(k5_relat_1('#skF_8','#skF_7'),k2_relat_1(k5_relat_1('#skF_8','#skF_7')),C_259)),k1_relat_1('#skF_7'))
      | ~ v1_funct_1('#skF_7')
      | ~ v1_relat_1('#skF_7')
      | ~ r2_hidden(C_259,k2_relat_1(k5_relat_1('#skF_8','#skF_7'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3265,c_12])).

tff(c_3399,plain,(
    ! [C_263] :
      ( r2_hidden(C_263,k2_relat_1('#skF_7'))
      | ~ r2_hidden(k1_funct_1('#skF_8','#skF_4'(k5_relat_1('#skF_8','#skF_7'),k2_relat_1(k5_relat_1('#skF_8','#skF_7')),C_263)),k1_relat_1('#skF_7'))
      | ~ r2_hidden(C_263,k2_relat_1(k5_relat_1('#skF_8','#skF_7'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_3286])).

tff(c_3404,plain,(
    ! [C_264] :
      ( r2_hidden(C_264,k2_relat_1('#skF_7'))
      | ~ r2_hidden(C_264,k2_relat_1(k5_relat_1('#skF_8','#skF_7')))
      | ~ r2_hidden('#skF_4'(k5_relat_1('#skF_8','#skF_7'),k2_relat_1(k5_relat_1('#skF_8','#skF_7')),C_264),k1_relat_1('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_290,c_3399])).

tff(c_3437,plain,(
    ! [C_267] :
      ( r2_hidden(C_267,k2_relat_1('#skF_7'))
      | ~ r2_hidden(C_267,k2_relat_1(k5_relat_1('#skF_8','#skF_7'))) ) ),
    inference(resolution,[status(thm)],[c_441,c_3404])).

tff(c_3587,plain,(
    ! [A_8] :
      ( r2_hidden('#skF_3'(A_8,k2_relat_1(k5_relat_1('#skF_8','#skF_7'))),k2_relat_1('#skF_7'))
      | r2_hidden('#skF_2'(A_8,k2_relat_1(k5_relat_1('#skF_8','#skF_7'))),k1_relat_1(A_8))
      | k2_relat_1(k5_relat_1('#skF_8','#skF_7')) = k2_relat_1(A_8)
      | ~ v1_funct_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(resolution,[status(thm)],[c_28,c_3437])).

tff(c_484,plain,(
    ! [A_135,B_136,D_137] :
      ( r2_hidden('#skF_2'(A_135,B_136),k1_relat_1(A_135))
      | k1_funct_1(A_135,D_137) != '#skF_3'(A_135,B_136)
      | ~ r2_hidden(D_137,k1_relat_1(A_135))
      | k2_relat_1(A_135) = B_136
      | ~ v1_funct_1(A_135)
      | ~ v1_relat_1(A_135) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_490,plain,(
    ! [A_8,B_136,C_44] :
      ( r2_hidden('#skF_2'(A_8,B_136),k1_relat_1(A_8))
      | C_44 != '#skF_3'(A_8,B_136)
      | ~ r2_hidden('#skF_4'(A_8,k2_relat_1(A_8),C_44),k1_relat_1(A_8))
      | k2_relat_1(A_8) = B_136
      | ~ v1_funct_1(A_8)
      | ~ v1_relat_1(A_8)
      | ~ r2_hidden(C_44,k2_relat_1(A_8))
      | ~ v1_funct_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_484])).

tff(c_38294,plain,(
    ! [A_685,B_686] :
      ( r2_hidden('#skF_2'(A_685,B_686),k1_relat_1(A_685))
      | ~ r2_hidden('#skF_4'(A_685,k2_relat_1(A_685),'#skF_3'(A_685,B_686)),k1_relat_1(A_685))
      | k2_relat_1(A_685) = B_686
      | ~ v1_funct_1(A_685)
      | ~ v1_relat_1(A_685)
      | ~ r2_hidden('#skF_3'(A_685,B_686),k2_relat_1(A_685))
      | ~ v1_funct_1(A_685)
      | ~ v1_relat_1(A_685) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_490])).

tff(c_38310,plain,(
    ! [A_687,B_688] :
      ( r2_hidden('#skF_2'(A_687,B_688),k1_relat_1(A_687))
      | k2_relat_1(A_687) = B_688
      | ~ r2_hidden('#skF_3'(A_687,B_688),k2_relat_1(A_687))
      | ~ v1_funct_1(A_687)
      | ~ v1_relat_1(A_687) ) ),
    inference(resolution,[status(thm)],[c_16,c_38294])).

tff(c_38330,plain,
    ( r2_hidden('#skF_2'('#skF_7',k2_relat_1(k5_relat_1('#skF_8','#skF_7'))),k1_relat_1('#skF_7'))
    | k2_relat_1(k5_relat_1('#skF_8','#skF_7')) = k2_relat_1('#skF_7')
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_3587,c_38310])).

tff(c_38419,plain,
    ( r2_hidden('#skF_2'('#skF_7',k2_relat_1(k5_relat_1('#skF_8','#skF_7'))),k1_relat_1('#skF_7'))
    | k2_relat_1(k5_relat_1('#skF_8','#skF_7')) = k2_relat_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_38330])).

tff(c_38473,plain,(
    k2_relat_1(k5_relat_1('#skF_8','#skF_7')) = k2_relat_1('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_38419])).

tff(c_457,plain,(
    ! [C_131,B_132,A_133] :
      ( C_131 = B_132
      | k1_funct_1(A_133,C_131) != k1_funct_1(A_133,B_132)
      | ~ r2_hidden(C_131,k1_relat_1(A_133))
      | ~ r2_hidden(B_132,k1_relat_1(A_133))
      | ~ v2_funct_1(A_133)
      | ~ v1_funct_1(A_133)
      | ~ v1_relat_1(A_133) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_469,plain,(
    ! [C_131,A_8,C_44] :
      ( C_131 = '#skF_4'(A_8,k2_relat_1(A_8),C_44)
      | k1_funct_1(A_8,C_131) != C_44
      | ~ r2_hidden(C_131,k1_relat_1(A_8))
      | ~ r2_hidden('#skF_4'(A_8,k2_relat_1(A_8),C_44),k1_relat_1(A_8))
      | ~ v2_funct_1(A_8)
      | ~ v1_funct_1(A_8)
      | ~ v1_relat_1(A_8)
      | ~ r2_hidden(C_44,k2_relat_1(A_8))
      | ~ v1_funct_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_457])).

tff(c_38768,plain,(
    ! [A_697,C_698] :
      ( '#skF_4'(A_697,k2_relat_1(A_697),k1_funct_1(A_697,C_698)) = C_698
      | ~ r2_hidden(C_698,k1_relat_1(A_697))
      | ~ r2_hidden('#skF_4'(A_697,k2_relat_1(A_697),k1_funct_1(A_697,C_698)),k1_relat_1(A_697))
      | ~ v2_funct_1(A_697)
      | ~ v1_funct_1(A_697)
      | ~ v1_relat_1(A_697)
      | ~ r2_hidden(k1_funct_1(A_697,C_698),k2_relat_1(A_697))
      | ~ v1_funct_1(A_697)
      | ~ v1_relat_1(A_697) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_469])).

tff(c_39046,plain,(
    ! [A_704,C_705] :
      ( '#skF_4'(A_704,k2_relat_1(A_704),k1_funct_1(A_704,C_705)) = C_705
      | ~ r2_hidden(C_705,k1_relat_1(A_704))
      | ~ v2_funct_1(A_704)
      | ~ r2_hidden(k1_funct_1(A_704,C_705),k2_relat_1(A_704))
      | ~ v1_funct_1(A_704)
      | ~ v1_relat_1(A_704) ) ),
    inference(resolution,[status(thm)],[c_16,c_38768])).

tff(c_39220,plain,(
    ! [A_708,D_709] :
      ( '#skF_4'(A_708,k2_relat_1(A_708),k1_funct_1(A_708,D_709)) = D_709
      | ~ v2_funct_1(A_708)
      | ~ r2_hidden(D_709,k1_relat_1(A_708))
      | ~ v1_funct_1(A_708)
      | ~ v1_relat_1(A_708) ) ),
    inference(resolution,[status(thm)],[c_12,c_39046])).

tff(c_39245,plain,(
    ! [D_709] :
      ( '#skF_4'(k5_relat_1('#skF_8','#skF_7'),k2_relat_1('#skF_7'),k1_funct_1(k5_relat_1('#skF_8','#skF_7'),D_709)) = D_709
      | ~ v2_funct_1(k5_relat_1('#skF_8','#skF_7'))
      | ~ r2_hidden(D_709,k1_relat_1(k5_relat_1('#skF_8','#skF_7')))
      | ~ v1_funct_1(k5_relat_1('#skF_8','#skF_7'))
      | ~ v1_relat_1(k5_relat_1('#skF_8','#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38473,c_39220])).

tff(c_39347,plain,(
    ! [D_710] :
      ( '#skF_4'(k5_relat_1('#skF_8','#skF_7'),k2_relat_1('#skF_7'),k1_funct_1(k5_relat_1('#skF_8','#skF_7'),D_710)) = D_710
      | ~ r2_hidden(D_710,k1_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_389,c_442,c_311,c_52,c_39245])).

tff(c_39706,plain,(
    ! [C_716] :
      ( '#skF_4'(k5_relat_1('#skF_8','#skF_7'),k2_relat_1('#skF_7'),k1_funct_1('#skF_7',k1_funct_1('#skF_8','#skF_4'('#skF_8',k1_relat_1('#skF_7'),C_716)))) = '#skF_4'('#skF_8',k1_relat_1('#skF_7'),C_716)
      | ~ r2_hidden('#skF_4'('#skF_8',k1_relat_1('#skF_7'),C_716),k1_relat_1('#skF_8'))
      | ~ r2_hidden(C_716,k1_relat_1('#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_583,c_39347])).

tff(c_40037,plain,(
    ! [C_723] :
      ( '#skF_4'(k5_relat_1('#skF_8','#skF_7'),k2_relat_1('#skF_7'),k1_funct_1('#skF_7',C_723)) = '#skF_4'('#skF_8',k1_relat_1('#skF_7'),C_723)
      | ~ r2_hidden('#skF_4'('#skF_8',k1_relat_1('#skF_7'),C_723),k1_relat_1('#skF_8'))
      | ~ r2_hidden(C_723,k1_relat_1('#skF_7'))
      | ~ r2_hidden(C_723,k1_relat_1('#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_352,c_39706])).

tff(c_40073,plain,(
    ! [C_724] :
      ( '#skF_4'(k5_relat_1('#skF_8','#skF_7'),k2_relat_1('#skF_7'),k1_funct_1('#skF_7',C_724)) = '#skF_4'('#skF_8',k1_relat_1('#skF_7'),C_724)
      | ~ r2_hidden(C_724,k1_relat_1('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_378,c_40037])).

tff(c_40137,plain,
    ( '#skF_4'(k5_relat_1('#skF_8','#skF_7'),k2_relat_1('#skF_7'),k1_funct_1('#skF_7','#skF_6'('#skF_7'))) = '#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_5'('#skF_7'))
    | ~ r2_hidden('#skF_5'('#skF_7'),k1_relat_1('#skF_7'))
    | v2_funct_1('#skF_7')
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_40073])).

tff(c_40150,plain,
    ( '#skF_4'(k5_relat_1('#skF_8','#skF_7'),k2_relat_1('#skF_7'),k1_funct_1('#skF_7','#skF_6'('#skF_7'))) = '#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_5'('#skF_7'))
    | v2_funct_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_783,c_40137])).

tff(c_40151,plain,(
    '#skF_4'(k5_relat_1('#skF_8','#skF_7'),k2_relat_1('#skF_7'),k1_funct_1('#skF_7','#skF_6'('#skF_7'))) = '#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_5'('#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_249,c_40150])).

tff(c_40072,plain,(
    ! [C_115] :
      ( '#skF_4'(k5_relat_1('#skF_8','#skF_7'),k2_relat_1('#skF_7'),k1_funct_1('#skF_7',C_115)) = '#skF_4'('#skF_8',k1_relat_1('#skF_7'),C_115)
      | ~ r2_hidden(C_115,k1_relat_1('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_378,c_40037])).

tff(c_40155,plain,
    ( '#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_5'('#skF_7')) = '#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_6'('#skF_7'))
    | ~ r2_hidden('#skF_6'('#skF_7'),k1_relat_1('#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_40151,c_40072])).

tff(c_40180,plain,(
    '#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_5'('#skF_7')) = '#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_6'('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1527,c_40155])).

tff(c_40233,plain,
    ( k1_funct_1('#skF_8','#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_6'('#skF_7'))) = '#skF_5'('#skF_7')
    | ~ r2_hidden('#skF_5'('#skF_7'),k1_relat_1('#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_40180,c_352])).

tff(c_40249,plain,(
    k1_funct_1('#skF_8','#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_6'('#skF_7'))) = '#skF_5'('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_783,c_40233])).

tff(c_40312,plain,
    ( '#skF_5'('#skF_7') = '#skF_6'('#skF_7')
    | ~ r2_hidden('#skF_6'('#skF_7'),k1_relat_1('#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_40249,c_352])).

tff(c_40355,plain,(
    '#skF_5'('#skF_7') = '#skF_6'('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1527,c_40312])).

tff(c_40357,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_269,c_40355])).

tff(c_40359,plain,(
    k2_relat_1(k5_relat_1('#skF_8','#skF_7')) != k2_relat_1('#skF_7') ),
    inference(splitRight,[status(thm)],[c_38419])).

tff(c_40358,plain,(
    r2_hidden('#skF_2'('#skF_7',k2_relat_1(k5_relat_1('#skF_8','#skF_7'))),k1_relat_1('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_38419])).

tff(c_789,plain,(
    ! [A_8,B_30] :
      ( r2_hidden('#skF_1'(A_8,B_30),k2_relat_1(A_8))
      | r2_hidden('#skF_3'(A_8,B_30),B_30)
      | k2_relat_1(A_8) = B_30
      | ~ v1_funct_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(resolution,[status(thm)],[c_28,c_784])).

tff(c_3576,plain,(
    ! [A_8] :
      ( r2_hidden('#skF_3'(A_8,k2_relat_1(k5_relat_1('#skF_8','#skF_7'))),k2_relat_1('#skF_7'))
      | r2_hidden('#skF_1'(A_8,k2_relat_1(k5_relat_1('#skF_8','#skF_7'))),k2_relat_1(A_8))
      | k2_relat_1(k5_relat_1('#skF_8','#skF_7')) = k2_relat_1(A_8)
      | ~ v1_funct_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(resolution,[status(thm)],[c_789,c_3437])).

tff(c_672,plain,(
    ! [A_147,B_148,D_149] :
      ( k1_funct_1(A_147,'#skF_2'(A_147,B_148)) = '#skF_1'(A_147,B_148)
      | k1_funct_1(A_147,D_149) != '#skF_3'(A_147,B_148)
      | ~ r2_hidden(D_149,k1_relat_1(A_147))
      | k2_relat_1(A_147) = B_148
      | ~ v1_funct_1(A_147)
      | ~ v1_relat_1(A_147) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_682,plain,(
    ! [A_8,B_148,C_44] :
      ( k1_funct_1(A_8,'#skF_2'(A_8,B_148)) = '#skF_1'(A_8,B_148)
      | C_44 != '#skF_3'(A_8,B_148)
      | ~ r2_hidden('#skF_4'(A_8,k2_relat_1(A_8),C_44),k1_relat_1(A_8))
      | k2_relat_1(A_8) = B_148
      | ~ v1_funct_1(A_8)
      | ~ v1_relat_1(A_8)
      | ~ r2_hidden(C_44,k2_relat_1(A_8))
      | ~ v1_funct_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_672])).

tff(c_40455,plain,(
    ! [A_728,B_729] :
      ( k1_funct_1(A_728,'#skF_2'(A_728,B_729)) = '#skF_1'(A_728,B_729)
      | ~ r2_hidden('#skF_4'(A_728,k2_relat_1(A_728),'#skF_3'(A_728,B_729)),k1_relat_1(A_728))
      | k2_relat_1(A_728) = B_729
      | ~ v1_funct_1(A_728)
      | ~ v1_relat_1(A_728)
      | ~ r2_hidden('#skF_3'(A_728,B_729),k2_relat_1(A_728))
      | ~ v1_funct_1(A_728)
      | ~ v1_relat_1(A_728) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_682])).

tff(c_40556,plain,(
    ! [A_730,B_731] :
      ( k1_funct_1(A_730,'#skF_2'(A_730,B_731)) = '#skF_1'(A_730,B_731)
      | k2_relat_1(A_730) = B_731
      | ~ r2_hidden('#skF_3'(A_730,B_731),k2_relat_1(A_730))
      | ~ v1_funct_1(A_730)
      | ~ v1_relat_1(A_730) ) ),
    inference(resolution,[status(thm)],[c_16,c_40455])).

tff(c_40580,plain,
    ( k1_funct_1('#skF_7','#skF_2'('#skF_7',k2_relat_1(k5_relat_1('#skF_8','#skF_7')))) = '#skF_1'('#skF_7',k2_relat_1(k5_relat_1('#skF_8','#skF_7')))
    | r2_hidden('#skF_1'('#skF_7',k2_relat_1(k5_relat_1('#skF_8','#skF_7'))),k2_relat_1('#skF_7'))
    | k2_relat_1(k5_relat_1('#skF_8','#skF_7')) = k2_relat_1('#skF_7')
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_3576,c_40556])).

tff(c_40670,plain,
    ( k1_funct_1('#skF_7','#skF_2'('#skF_7',k2_relat_1(k5_relat_1('#skF_8','#skF_7')))) = '#skF_1'('#skF_7',k2_relat_1(k5_relat_1('#skF_8','#skF_7')))
    | r2_hidden('#skF_1'('#skF_7',k2_relat_1(k5_relat_1('#skF_8','#skF_7'))),k2_relat_1('#skF_7'))
    | k2_relat_1(k5_relat_1('#skF_8','#skF_7')) = k2_relat_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_40580])).

tff(c_40671,plain,
    ( k1_funct_1('#skF_7','#skF_2'('#skF_7',k2_relat_1(k5_relat_1('#skF_8','#skF_7')))) = '#skF_1'('#skF_7',k2_relat_1(k5_relat_1('#skF_8','#skF_7')))
    | r2_hidden('#skF_1'('#skF_7',k2_relat_1(k5_relat_1('#skF_8','#skF_7'))),k2_relat_1('#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_40359,c_40670])).

tff(c_40723,plain,(
    r2_hidden('#skF_1'('#skF_7',k2_relat_1(k5_relat_1('#skF_8','#skF_7'))),k2_relat_1('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_40671])).

tff(c_763,plain,(
    ! [C_44] :
      ( r2_hidden(C_44,k2_relat_1(k5_relat_1('#skF_8','#skF_7')))
      | ~ r2_hidden('#skF_4'('#skF_7',k2_relat_1('#skF_7'),C_44),k1_relat_1('#skF_7'))
      | ~ r2_hidden(C_44,k2_relat_1('#skF_7'))
      | ~ v1_funct_1('#skF_7')
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_757])).

tff(c_835,plain,(
    ! [C_162] :
      ( r2_hidden(C_162,k2_relat_1(k5_relat_1('#skF_8','#skF_7')))
      | ~ r2_hidden('#skF_4'('#skF_7',k2_relat_1('#skF_7'),C_162),k1_relat_1('#skF_7'))
      | ~ r2_hidden(C_162,k2_relat_1('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_763])).

tff(c_839,plain,(
    ! [C_44] :
      ( r2_hidden(C_44,k2_relat_1(k5_relat_1('#skF_8','#skF_7')))
      | ~ r2_hidden(C_44,k2_relat_1('#skF_7'))
      | ~ v1_funct_1('#skF_7')
      | ~ v1_relat_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_16,c_835])).

tff(c_842,plain,(
    ! [C_44] :
      ( r2_hidden(C_44,k2_relat_1(k5_relat_1('#skF_8','#skF_7')))
      | ~ r2_hidden(C_44,k2_relat_1('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_839])).

tff(c_24,plain,(
    ! [A_8,B_30] :
      ( ~ r2_hidden('#skF_1'(A_8,B_30),B_30)
      | r2_hidden('#skF_3'(A_8,B_30),B_30)
      | k2_relat_1(A_8) = B_30
      | ~ v1_funct_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_37398,plain,(
    ! [A_660] :
      ( r2_hidden('#skF_3'(A_660,k2_relat_1(k5_relat_1('#skF_8','#skF_7'))),k2_relat_1('#skF_7'))
      | ~ r2_hidden('#skF_1'(A_660,k2_relat_1(k5_relat_1('#skF_8','#skF_7'))),k2_relat_1(k5_relat_1('#skF_8','#skF_7')))
      | k2_relat_1(k5_relat_1('#skF_8','#skF_7')) = k2_relat_1(A_660)
      | ~ v1_funct_1(A_660)
      | ~ v1_relat_1(A_660) ) ),
    inference(resolution,[status(thm)],[c_24,c_3437])).

tff(c_37429,plain,(
    ! [A_660] :
      ( r2_hidden('#skF_3'(A_660,k2_relat_1(k5_relat_1('#skF_8','#skF_7'))),k2_relat_1('#skF_7'))
      | k2_relat_1(k5_relat_1('#skF_8','#skF_7')) = k2_relat_1(A_660)
      | ~ v1_funct_1(A_660)
      | ~ v1_relat_1(A_660)
      | ~ r2_hidden('#skF_1'(A_660,k2_relat_1(k5_relat_1('#skF_8','#skF_7'))),k2_relat_1('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_842,c_37398])).

tff(c_40572,plain,
    ( k1_funct_1('#skF_7','#skF_2'('#skF_7',k2_relat_1(k5_relat_1('#skF_8','#skF_7')))) = '#skF_1'('#skF_7',k2_relat_1(k5_relat_1('#skF_8','#skF_7')))
    | k2_relat_1(k5_relat_1('#skF_8','#skF_7')) = k2_relat_1('#skF_7')
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7')
    | ~ r2_hidden('#skF_1'('#skF_7',k2_relat_1(k5_relat_1('#skF_8','#skF_7'))),k2_relat_1('#skF_7')) ),
    inference(resolution,[status(thm)],[c_37429,c_40556])).

tff(c_40662,plain,
    ( k1_funct_1('#skF_7','#skF_2'('#skF_7',k2_relat_1(k5_relat_1('#skF_8','#skF_7')))) = '#skF_1'('#skF_7',k2_relat_1(k5_relat_1('#skF_8','#skF_7')))
    | k2_relat_1(k5_relat_1('#skF_8','#skF_7')) = k2_relat_1('#skF_7')
    | ~ r2_hidden('#skF_1'('#skF_7',k2_relat_1(k5_relat_1('#skF_8','#skF_7'))),k2_relat_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_40572])).

tff(c_40663,plain,
    ( k1_funct_1('#skF_7','#skF_2'('#skF_7',k2_relat_1(k5_relat_1('#skF_8','#skF_7')))) = '#skF_1'('#skF_7',k2_relat_1(k5_relat_1('#skF_8','#skF_7')))
    | ~ r2_hidden('#skF_1'('#skF_7',k2_relat_1(k5_relat_1('#skF_8','#skF_7'))),k2_relat_1('#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_40359,c_40662])).

tff(c_40857,plain,(
    k1_funct_1('#skF_7','#skF_2'('#skF_7',k2_relat_1(k5_relat_1('#skF_8','#skF_7')))) = '#skF_1'('#skF_7',k2_relat_1(k5_relat_1('#skF_8','#skF_7'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40723,c_40663])).

tff(c_756,plain,(
    ! [C_115] :
      ( r2_hidden(k1_funct_1('#skF_7',C_115),k2_relat_1(k5_relat_1('#skF_8','#skF_7')))
      | ~ r2_hidden(C_115,k1_relat_1('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_378,c_752])).

tff(c_40879,plain,
    ( r2_hidden('#skF_1'('#skF_7',k2_relat_1(k5_relat_1('#skF_8','#skF_7'))),k2_relat_1(k5_relat_1('#skF_8','#skF_7')))
    | ~ r2_hidden('#skF_2'('#skF_7',k2_relat_1(k5_relat_1('#skF_8','#skF_7'))),k1_relat_1('#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_40857,c_756])).

tff(c_40919,plain,(
    r2_hidden('#skF_1'('#skF_7',k2_relat_1(k5_relat_1('#skF_8','#skF_7'))),k2_relat_1(k5_relat_1('#skF_8','#skF_7'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40358,c_40879])).

tff(c_18,plain,(
    ! [A_8,B_30,D_43] :
      ( ~ r2_hidden('#skF_1'(A_8,B_30),B_30)
      | k1_funct_1(A_8,D_43) != '#skF_3'(A_8,B_30)
      | ~ r2_hidden(D_43,k1_relat_1(A_8))
      | k2_relat_1(A_8) = B_30
      | ~ v1_funct_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_40944,plain,(
    ! [D_43] :
      ( k1_funct_1('#skF_7',D_43) != '#skF_3'('#skF_7',k2_relat_1(k5_relat_1('#skF_8','#skF_7')))
      | ~ r2_hidden(D_43,k1_relat_1('#skF_7'))
      | k2_relat_1(k5_relat_1('#skF_8','#skF_7')) = k2_relat_1('#skF_7')
      | ~ v1_funct_1('#skF_7')
      | ~ v1_relat_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_40919,c_18])).

tff(c_40953,plain,(
    ! [D_43] :
      ( k1_funct_1('#skF_7',D_43) != '#skF_3'('#skF_7',k2_relat_1(k5_relat_1('#skF_8','#skF_7')))
      | ~ r2_hidden(D_43,k1_relat_1('#skF_7'))
      | k2_relat_1(k5_relat_1('#skF_8','#skF_7')) = k2_relat_1('#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_40944])).

tff(c_40969,plain,(
    ! [D_734] :
      ( k1_funct_1('#skF_7',D_734) != '#skF_3'('#skF_7',k2_relat_1(k5_relat_1('#skF_8','#skF_7')))
      | ~ r2_hidden(D_734,k1_relat_1('#skF_7')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40359,c_40953])).

tff(c_40987,plain,(
    ! [C_44] :
      ( C_44 != '#skF_3'('#skF_7',k2_relat_1(k5_relat_1('#skF_8','#skF_7')))
      | ~ r2_hidden('#skF_4'('#skF_7',k2_relat_1('#skF_7'),C_44),k1_relat_1('#skF_7'))
      | ~ r2_hidden(C_44,k2_relat_1('#skF_7'))
      | ~ v1_funct_1('#skF_7')
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_40969])).

tff(c_41000,plain,(
    ! [C_736] :
      ( C_736 != '#skF_3'('#skF_7',k2_relat_1(k5_relat_1('#skF_8','#skF_7')))
      | ~ r2_hidden('#skF_4'('#skF_7',k2_relat_1('#skF_7'),C_736),k1_relat_1('#skF_7'))
      | ~ r2_hidden(C_736,k2_relat_1('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_40987])).

tff(c_41004,plain,(
    ! [C_44] :
      ( C_44 != '#skF_3'('#skF_7',k2_relat_1(k5_relat_1('#skF_8','#skF_7')))
      | ~ r2_hidden(C_44,k2_relat_1('#skF_7'))
      | ~ v1_funct_1('#skF_7')
      | ~ v1_relat_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_16,c_41000])).

tff(c_41008,plain,(
    ~ r2_hidden('#skF_3'('#skF_7',k2_relat_1(k5_relat_1('#skF_8','#skF_7'))),k2_relat_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_41004])).

tff(c_3588,plain,(
    ! [A_8] :
      ( r2_hidden('#skF_3'(A_8,k2_relat_1(k5_relat_1('#skF_8','#skF_7'))),k2_relat_1('#skF_7'))
      | ~ r2_hidden('#skF_1'(A_8,k2_relat_1(k5_relat_1('#skF_8','#skF_7'))),k2_relat_1(k5_relat_1('#skF_8','#skF_7')))
      | k2_relat_1(k5_relat_1('#skF_8','#skF_7')) = k2_relat_1(A_8)
      | ~ v1_funct_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(resolution,[status(thm)],[c_24,c_3437])).

tff(c_40939,plain,
    ( r2_hidden('#skF_3'('#skF_7',k2_relat_1(k5_relat_1('#skF_8','#skF_7'))),k2_relat_1('#skF_7'))
    | k2_relat_1(k5_relat_1('#skF_8','#skF_7')) = k2_relat_1('#skF_7')
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_40919,c_3588])).

tff(c_40947,plain,
    ( r2_hidden('#skF_3'('#skF_7',k2_relat_1(k5_relat_1('#skF_8','#skF_7'))),k2_relat_1('#skF_7'))
    | k2_relat_1(k5_relat_1('#skF_8','#skF_7')) = k2_relat_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_40939])).

tff(c_40948,plain,(
    r2_hidden('#skF_3'('#skF_7',k2_relat_1(k5_relat_1('#skF_8','#skF_7'))),k2_relat_1('#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_40359,c_40947])).

tff(c_41010,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_41008,c_40948])).

tff(c_41012,plain,(
    ~ r2_hidden('#skF_1'('#skF_7',k2_relat_1(k5_relat_1('#skF_8','#skF_7'))),k2_relat_1('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_40671])).

tff(c_41011,plain,(
    k1_funct_1('#skF_7','#skF_2'('#skF_7',k2_relat_1(k5_relat_1('#skF_8','#skF_7')))) = '#skF_1'('#skF_7',k2_relat_1(k5_relat_1('#skF_8','#skF_7'))) ),
    inference(splitRight,[status(thm)],[c_40671])).

tff(c_3578,plain,(
    ! [C_115] :
      ( r2_hidden(k1_funct_1('#skF_7',C_115),k2_relat_1('#skF_7'))
      | ~ r2_hidden(C_115,k1_relat_1('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_756,c_3437])).

tff(c_41168,plain,
    ( r2_hidden('#skF_1'('#skF_7',k2_relat_1(k5_relat_1('#skF_8','#skF_7'))),k2_relat_1('#skF_7'))
    | ~ r2_hidden('#skF_2'('#skF_7',k2_relat_1(k5_relat_1('#skF_8','#skF_7'))),k1_relat_1('#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_41011,c_3578])).

tff(c_41209,plain,(
    r2_hidden('#skF_1'('#skF_7',k2_relat_1(k5_relat_1('#skF_8','#skF_7'))),k2_relat_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40358,c_41168])).

tff(c_41211,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_41012,c_41209])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:44:24 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 28.99/17.61  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 29.12/17.63  
% 29.12/17.63  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 29.12/17.63  %$ r2_hidden > r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_5 > #skF_4 > #skF_7 > #skF_3 > #skF_8 > #skF_2 > #skF_1 > #skF_6
% 29.12/17.63  
% 29.12/17.63  %Foreground sorts:
% 29.12/17.63  
% 29.12/17.63  
% 29.12/17.63  %Background operators:
% 29.12/17.63  
% 29.12/17.63  
% 29.12/17.63  %Foreground operators:
% 29.12/17.63  tff('#skF_5', type, '#skF_5': $i > $i).
% 29.12/17.63  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 29.12/17.63  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 29.12/17.63  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 29.12/17.63  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 29.12/17.63  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 29.12/17.63  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 29.12/17.63  tff('#skF_7', type, '#skF_7': $i).
% 29.12/17.63  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 29.12/17.63  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 29.12/17.63  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 29.12/17.63  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 29.12/17.63  tff('#skF_8', type, '#skF_8': $i).
% 29.12/17.63  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 29.12/17.63  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 29.12/17.63  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 29.12/17.63  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 29.12/17.63  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 29.12/17.63  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 29.12/17.63  tff('#skF_6', type, '#skF_6': $i > $i).
% 29.12/17.63  
% 29.12/17.66  tff(f_134, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v2_funct_1(k5_relat_1(B, A)) & (k2_relat_1(B) = k1_relat_1(A))) => (v2_funct_1(B) & v2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_funct_1)).
% 29.12/17.66  tff(f_61, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_funct_1)).
% 29.12/17.66  tff(f_76, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) <=> (![B, C]: (((r2_hidden(B, k1_relat_1(A)) & r2_hidden(C, k1_relat_1(A))) & (k1_funct_1(A, B) = k1_funct_1(A, C))) => (B = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_funct_1)).
% 29.12/17.66  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 29.12/17.66  tff(f_116, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v2_funct_1(k5_relat_1(B, A)) & r1_tarski(k2_relat_1(B), k1_relat_1(A))) => v2_funct_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_funct_1)).
% 29.12/17.67  tff(f_46, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(A), k1_relat_1(B)) => (k1_relat_1(k5_relat_1(A, B)) = k1_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_relat_1)).
% 29.12/17.67  tff(f_101, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(k5_relat_1(C, B))) => (k1_funct_1(k5_relat_1(C, B), A) = k1_funct_1(B, k1_funct_1(C, A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_funct_1)).
% 29.12/17.67  tff(f_37, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 29.12/17.67  tff(f_88, axiom, (![A, B]: ((((v1_relat_1(A) & v1_funct_1(A)) & v1_relat_1(B)) & v1_funct_1(B)) => (v1_relat_1(k5_relat_1(A, B)) & v1_funct_1(k5_relat_1(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_funct_1)).
% 29.12/17.67  tff(c_60, plain, (v1_relat_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_134])).
% 29.12/17.67  tff(c_58, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_134])).
% 29.12/17.67  tff(c_16, plain, (![A_8, C_44]: (r2_hidden('#skF_4'(A_8, k2_relat_1(A_8), C_44), k1_relat_1(A_8)) | ~r2_hidden(C_44, k2_relat_1(A_8)) | ~v1_funct_1(A_8) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_61])).
% 29.12/17.67  tff(c_14, plain, (![A_8, C_44]: (k1_funct_1(A_8, '#skF_4'(A_8, k2_relat_1(A_8), C_44))=C_44 | ~r2_hidden(C_44, k2_relat_1(A_8)) | ~v1_funct_1(A_8) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_61])).
% 29.12/17.67  tff(c_263, plain, (![A_99]: ('#skF_5'(A_99)!='#skF_6'(A_99) | v2_funct_1(A_99) | ~v1_funct_1(A_99) | ~v1_relat_1(A_99))), inference(cnfTransformation, [status(thm)], [f_76])).
% 29.12/17.67  tff(c_52, plain, (v2_funct_1(k5_relat_1('#skF_8', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_134])).
% 29.12/17.67  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 29.12/17.67  tff(c_48, plain, (~v2_funct_1('#skF_7') | ~v2_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_134])).
% 29.12/17.67  tff(c_63, plain, (~v2_funct_1('#skF_8')), inference(splitLeft, [status(thm)], [c_48])).
% 29.12/17.67  tff(c_56, plain, (v1_relat_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_134])).
% 29.12/17.67  tff(c_54, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_134])).
% 29.12/17.67  tff(c_50, plain, (k2_relat_1('#skF_8')=k1_relat_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_134])).
% 29.12/17.67  tff(c_223, plain, (![B_92, A_93]: (v2_funct_1(B_92) | ~r1_tarski(k2_relat_1(B_92), k1_relat_1(A_93)) | ~v2_funct_1(k5_relat_1(B_92, A_93)) | ~v1_funct_1(B_92) | ~v1_relat_1(B_92) | ~v1_funct_1(A_93) | ~v1_relat_1(A_93))), inference(cnfTransformation, [status(thm)], [f_116])).
% 29.12/17.67  tff(c_229, plain, (![A_93]: (v2_funct_1('#skF_8') | ~r1_tarski(k1_relat_1('#skF_7'), k1_relat_1(A_93)) | ~v2_funct_1(k5_relat_1('#skF_8', A_93)) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~v1_funct_1(A_93) | ~v1_relat_1(A_93))), inference(superposition, [status(thm), theory('equality')], [c_50, c_223])).
% 29.12/17.67  tff(c_233, plain, (![A_93]: (v2_funct_1('#skF_8') | ~r1_tarski(k1_relat_1('#skF_7'), k1_relat_1(A_93)) | ~v2_funct_1(k5_relat_1('#skF_8', A_93)) | ~v1_funct_1(A_93) | ~v1_relat_1(A_93))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_229])).
% 29.12/17.67  tff(c_235, plain, (![A_94]: (~r1_tarski(k1_relat_1('#skF_7'), k1_relat_1(A_94)) | ~v2_funct_1(k5_relat_1('#skF_8', A_94)) | ~v1_funct_1(A_94) | ~v1_relat_1(A_94))), inference(negUnitSimplification, [status(thm)], [c_63, c_233])).
% 29.12/17.67  tff(c_242, plain, (~v2_funct_1(k5_relat_1('#skF_8', '#skF_7')) | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_6, c_235])).
% 29.12/17.67  tff(c_248, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_52, c_242])).
% 29.12/17.67  tff(c_249, plain, (~v2_funct_1('#skF_7')), inference(splitRight, [status(thm)], [c_48])).
% 29.12/17.67  tff(c_266, plain, ('#skF_5'('#skF_7')!='#skF_6'('#skF_7') | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_263, c_249])).
% 29.12/17.67  tff(c_269, plain, ('#skF_5'('#skF_7')!='#skF_6'('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_266])).
% 29.12/17.67  tff(c_36, plain, (![A_48]: (r2_hidden('#skF_6'(A_48), k1_relat_1(A_48)) | v2_funct_1(A_48) | ~v1_funct_1(A_48) | ~v1_relat_1(A_48))), inference(cnfTransformation, [status(thm)], [f_76])).
% 29.12/17.67  tff(c_330, plain, (![A_111, C_112]: (k1_funct_1(A_111, '#skF_4'(A_111, k2_relat_1(A_111), C_112))=C_112 | ~r2_hidden(C_112, k2_relat_1(A_111)) | ~v1_funct_1(A_111) | ~v1_relat_1(A_111))), inference(cnfTransformation, [status(thm)], [f_61])).
% 29.12/17.67  tff(c_346, plain, (![C_112]: (k1_funct_1('#skF_8', '#skF_4'('#skF_8', k1_relat_1('#skF_7'), C_112))=C_112 | ~r2_hidden(C_112, k2_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_50, c_330])).
% 29.12/17.67  tff(c_352, plain, (![C_112]: (k1_funct_1('#skF_8', '#skF_4'('#skF_8', k1_relat_1('#skF_7'), C_112))=C_112 | ~r2_hidden(C_112, k1_relat_1('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_50, c_346])).
% 29.12/17.67  tff(c_370, plain, (![A_114, C_115]: (r2_hidden('#skF_4'(A_114, k2_relat_1(A_114), C_115), k1_relat_1(A_114)) | ~r2_hidden(C_115, k2_relat_1(A_114)) | ~v1_funct_1(A_114) | ~v1_relat_1(A_114))), inference(cnfTransformation, [status(thm)], [f_61])).
% 29.12/17.67  tff(c_376, plain, (![C_115]: (r2_hidden('#skF_4'('#skF_8', k1_relat_1('#skF_7'), C_115), k1_relat_1('#skF_8')) | ~r2_hidden(C_115, k2_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_50, c_370])).
% 29.12/17.67  tff(c_378, plain, (![C_115]: (r2_hidden('#skF_4'('#skF_8', k1_relat_1('#skF_7'), C_115), k1_relat_1('#skF_8')) | ~r2_hidden(C_115, k1_relat_1('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_50, c_376])).
% 29.12/17.67  tff(c_250, plain, (v2_funct_1('#skF_8')), inference(splitRight, [status(thm)], [c_48])).
% 29.12/17.67  tff(c_28, plain, (![A_8, B_30]: (r2_hidden('#skF_2'(A_8, B_30), k1_relat_1(A_8)) | r2_hidden('#skF_3'(A_8, B_30), B_30) | k2_relat_1(A_8)=B_30 | ~v1_funct_1(A_8) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_61])).
% 29.12/17.67  tff(c_417, plain, (![A_124, B_125]: (k1_funct_1(A_124, '#skF_2'(A_124, B_125))='#skF_1'(A_124, B_125) | r2_hidden('#skF_3'(A_124, B_125), B_125) | k2_relat_1(A_124)=B_125 | ~v1_funct_1(A_124) | ~v1_relat_1(A_124))), inference(cnfTransformation, [status(thm)], [f_61])).
% 29.12/17.67  tff(c_12, plain, (![A_8, D_47]: (r2_hidden(k1_funct_1(A_8, D_47), k2_relat_1(A_8)) | ~r2_hidden(D_47, k1_relat_1(A_8)) | ~v1_funct_1(A_8) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_61])).
% 29.12/17.67  tff(c_784, plain, (![A_157, B_158]: (r2_hidden('#skF_1'(A_157, B_158), k2_relat_1(A_157)) | ~r2_hidden('#skF_2'(A_157, B_158), k1_relat_1(A_157)) | ~v1_funct_1(A_157) | ~v1_relat_1(A_157) | r2_hidden('#skF_3'(A_157, B_158), B_158) | k2_relat_1(A_157)=B_158 | ~v1_funct_1(A_157) | ~v1_relat_1(A_157))), inference(superposition, [status(thm), theory('equality')], [c_417, c_12])).
% 29.12/17.67  tff(c_792, plain, (![A_159, B_160]: (r2_hidden('#skF_1'(A_159, B_160), k2_relat_1(A_159)) | r2_hidden('#skF_3'(A_159, B_160), B_160) | k2_relat_1(A_159)=B_160 | ~v1_funct_1(A_159) | ~v1_relat_1(A_159))), inference(resolution, [status(thm)], [c_28, c_784])).
% 29.12/17.67  tff(c_808, plain, (![B_160]: (r2_hidden('#skF_1'('#skF_8', B_160), k1_relat_1('#skF_7')) | r2_hidden('#skF_3'('#skF_8', B_160), B_160) | k2_relat_1('#skF_8')=B_160 | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_50, c_792])).
% 29.12/17.67  tff(c_817, plain, (![B_161]: (r2_hidden('#skF_1'('#skF_8', B_161), k1_relat_1('#skF_7')) | r2_hidden('#skF_3'('#skF_8', B_161), B_161) | k1_relat_1('#skF_7')=B_161)), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_50, c_808])).
% 29.12/17.67  tff(c_298, plain, (![A_108, B_109]: (k1_relat_1(k5_relat_1(A_108, B_109))=k1_relat_1(A_108) | ~r1_tarski(k2_relat_1(A_108), k1_relat_1(B_109)) | ~v1_relat_1(B_109) | ~v1_relat_1(A_108))), inference(cnfTransformation, [status(thm)], [f_46])).
% 29.12/17.67  tff(c_301, plain, (![B_109]: (k1_relat_1(k5_relat_1('#skF_8', B_109))=k1_relat_1('#skF_8') | ~r1_tarski(k1_relat_1('#skF_7'), k1_relat_1(B_109)) | ~v1_relat_1(B_109) | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_50, c_298])).
% 29.12/17.67  tff(c_304, plain, (![B_110]: (k1_relat_1(k5_relat_1('#skF_8', B_110))=k1_relat_1('#skF_8') | ~r1_tarski(k1_relat_1('#skF_7'), k1_relat_1(B_110)) | ~v1_relat_1(B_110))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_301])).
% 29.12/17.67  tff(c_308, plain, (k1_relat_1(k5_relat_1('#skF_8', '#skF_7'))=k1_relat_1('#skF_8') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_6, c_304])).
% 29.12/17.67  tff(c_311, plain, (k1_relat_1(k5_relat_1('#skF_8', '#skF_7'))=k1_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_308])).
% 29.12/17.67  tff(c_495, plain, (![C_138, B_139, A_140]: (k1_funct_1(k5_relat_1(C_138, B_139), A_140)=k1_funct_1(B_139, k1_funct_1(C_138, A_140)) | ~r2_hidden(A_140, k1_relat_1(k5_relat_1(C_138, B_139))) | ~v1_funct_1(C_138) | ~v1_relat_1(C_138) | ~v1_funct_1(B_139) | ~v1_relat_1(B_139))), inference(cnfTransformation, [status(thm)], [f_101])).
% 29.12/17.67  tff(c_518, plain, (![A_140]: (k1_funct_1(k5_relat_1('#skF_8', '#skF_7'), A_140)=k1_funct_1('#skF_7', k1_funct_1('#skF_8', A_140)) | ~r2_hidden(A_140, k1_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_311, c_495])).
% 29.12/17.67  tff(c_533, plain, (![A_140]: (k1_funct_1(k5_relat_1('#skF_8', '#skF_7'), A_140)=k1_funct_1('#skF_7', k1_funct_1('#skF_8', A_140)) | ~r2_hidden(A_140, k1_relat_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_56, c_54, c_518])).
% 29.12/17.67  tff(c_833, plain, (k1_funct_1(k5_relat_1('#skF_8', '#skF_7'), '#skF_3'('#skF_8', k1_relat_1('#skF_8')))=k1_funct_1('#skF_7', k1_funct_1('#skF_8', '#skF_3'('#skF_8', k1_relat_1('#skF_8')))) | r2_hidden('#skF_1'('#skF_8', k1_relat_1('#skF_8')), k1_relat_1('#skF_7')) | k1_relat_1('#skF_7')=k1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_817, c_533])).
% 29.12/17.67  tff(c_950, plain, (k1_relat_1('#skF_7')=k1_relat_1('#skF_8')), inference(splitLeft, [status(thm)], [c_833])).
% 29.12/17.67  tff(c_8, plain, (![A_3, B_4]: (v1_relat_1(k5_relat_1(A_3, B_4)) | ~v1_relat_1(B_4) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_37])).
% 29.12/17.67  tff(c_303, plain, (![B_109]: (k1_relat_1(k5_relat_1('#skF_8', B_109))=k1_relat_1('#skF_8') | ~r1_tarski(k1_relat_1('#skF_7'), k1_relat_1(B_109)) | ~v1_relat_1(B_109))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_301])).
% 29.12/17.67  tff(c_315, plain, (k1_relat_1(k5_relat_1('#skF_8', k5_relat_1('#skF_8', '#skF_7')))=k1_relat_1('#skF_8') | ~r1_tarski(k1_relat_1('#skF_7'), k1_relat_1('#skF_8')) | ~v1_relat_1(k5_relat_1('#skF_8', '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_311, c_303])).
% 29.12/17.67  tff(c_380, plain, (~v1_relat_1(k5_relat_1('#skF_8', '#skF_7'))), inference(splitLeft, [status(thm)], [c_315])).
% 29.12/17.67  tff(c_383, plain, (~v1_relat_1('#skF_7') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_8, c_380])).
% 29.12/17.67  tff(c_387, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_60, c_383])).
% 29.12/17.67  tff(c_388, plain, (~r1_tarski(k1_relat_1('#skF_7'), k1_relat_1('#skF_8')) | k1_relat_1(k5_relat_1('#skF_8', k5_relat_1('#skF_8', '#skF_7')))=k1_relat_1('#skF_8')), inference(splitRight, [status(thm)], [c_315])).
% 29.12/17.67  tff(c_390, plain, (~r1_tarski(k1_relat_1('#skF_7'), k1_relat_1('#skF_8'))), inference(splitLeft, [status(thm)], [c_388])).
% 29.12/17.67  tff(c_964, plain, (~r1_tarski(k1_relat_1('#skF_8'), k1_relat_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_950, c_390])).
% 29.12/17.67  tff(c_972, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_964])).
% 29.12/17.67  tff(c_974, plain, (k1_relat_1('#skF_7')!=k1_relat_1('#skF_8')), inference(splitRight, [status(thm)], [c_833])).
% 29.12/17.67  tff(c_389, plain, (v1_relat_1(k5_relat_1('#skF_8', '#skF_7'))), inference(splitRight, [status(thm)], [c_315])).
% 29.12/17.67  tff(c_40, plain, (![A_55, B_56]: (v1_funct_1(k5_relat_1(A_55, B_56)) | ~v1_funct_1(B_56) | ~v1_relat_1(B_56) | ~v1_funct_1(A_55) | ~v1_relat_1(A_55))), inference(cnfTransformation, [status(thm)], [f_88])).
% 29.12/17.67  tff(c_373, plain, (![C_115]: (r2_hidden('#skF_4'(k5_relat_1('#skF_8', '#skF_7'), k2_relat_1(k5_relat_1('#skF_8', '#skF_7')), C_115), k1_relat_1('#skF_8')) | ~r2_hidden(C_115, k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))) | ~v1_funct_1(k5_relat_1('#skF_8', '#skF_7')) | ~v1_relat_1(k5_relat_1('#skF_8', '#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_311, c_370])).
% 29.12/17.67  tff(c_432, plain, (![C_115]: (r2_hidden('#skF_4'(k5_relat_1('#skF_8', '#skF_7'), k2_relat_1(k5_relat_1('#skF_8', '#skF_7')), C_115), k1_relat_1('#skF_8')) | ~r2_hidden(C_115, k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))) | ~v1_funct_1(k5_relat_1('#skF_8', '#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_389, c_373])).
% 29.12/17.67  tff(c_433, plain, (~v1_funct_1(k5_relat_1('#skF_8', '#skF_7'))), inference(splitLeft, [status(thm)], [c_432])).
% 29.12/17.67  tff(c_436, plain, (~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7') | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_40, c_433])).
% 29.12/17.67  tff(c_440, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_60, c_58, c_436])).
% 29.12/17.67  tff(c_442, plain, (v1_funct_1(k5_relat_1('#skF_8', '#skF_7'))), inference(splitRight, [status(thm)], [c_432])).
% 29.12/17.67  tff(c_973, plain, (r2_hidden('#skF_1'('#skF_8', k1_relat_1('#skF_8')), k1_relat_1('#skF_7')) | k1_funct_1(k5_relat_1('#skF_8', '#skF_7'), '#skF_3'('#skF_8', k1_relat_1('#skF_8')))=k1_funct_1('#skF_7', k1_funct_1('#skF_8', '#skF_3'('#skF_8', k1_relat_1('#skF_8'))))), inference(splitRight, [status(thm)], [c_833])).
% 29.12/17.67  tff(c_975, plain, (k1_funct_1(k5_relat_1('#skF_8', '#skF_7'), '#skF_3'('#skF_8', k1_relat_1('#skF_8')))=k1_funct_1('#skF_7', k1_funct_1('#skF_8', '#skF_3'('#skF_8', k1_relat_1('#skF_8'))))), inference(splitLeft, [status(thm)], [c_973])).
% 29.12/17.67  tff(c_987, plain, (r2_hidden(k1_funct_1('#skF_7', k1_funct_1('#skF_8', '#skF_3'('#skF_8', k1_relat_1('#skF_8')))), k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))) | ~r2_hidden('#skF_3'('#skF_8', k1_relat_1('#skF_8')), k1_relat_1(k5_relat_1('#skF_8', '#skF_7'))) | ~v1_funct_1(k5_relat_1('#skF_8', '#skF_7')) | ~v1_relat_1(k5_relat_1('#skF_8', '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_975, c_12])).
% 29.12/17.67  tff(c_999, plain, (r2_hidden(k1_funct_1('#skF_7', k1_funct_1('#skF_8', '#skF_3'('#skF_8', k1_relat_1('#skF_8')))), k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))) | ~r2_hidden('#skF_3'('#skF_8', k1_relat_1('#skF_8')), k1_relat_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_389, c_442, c_311, c_987])).
% 29.12/17.67  tff(c_1001, plain, (~r2_hidden('#skF_3'('#skF_8', k1_relat_1('#skF_8')), k1_relat_1('#skF_8'))), inference(splitLeft, [status(thm)], [c_999])).
% 29.12/17.67  tff(c_1031, plain, (r2_hidden('#skF_2'('#skF_8', k1_relat_1('#skF_8')), k1_relat_1('#skF_8')) | k2_relat_1('#skF_8')=k1_relat_1('#skF_8') | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_28, c_1001])).
% 29.12/17.67  tff(c_1051, plain, (r2_hidden('#skF_2'('#skF_8', k1_relat_1('#skF_8')), k1_relat_1('#skF_8')) | k1_relat_1('#skF_7')=k1_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_50, c_1031])).
% 29.12/17.67  tff(c_1052, plain, (r2_hidden('#skF_2'('#skF_8', k1_relat_1('#skF_8')), k1_relat_1('#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_974, c_1051])).
% 29.12/17.67  tff(c_26, plain, (![A_8, B_30]: (k1_funct_1(A_8, '#skF_2'(A_8, B_30))='#skF_1'(A_8, B_30) | r2_hidden('#skF_3'(A_8, B_30), B_30) | k2_relat_1(A_8)=B_30 | ~v1_funct_1(A_8) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_61])).
% 29.12/17.67  tff(c_1028, plain, (k1_funct_1('#skF_8', '#skF_2'('#skF_8', k1_relat_1('#skF_8')))='#skF_1'('#skF_8', k1_relat_1('#skF_8')) | k2_relat_1('#skF_8')=k1_relat_1('#skF_8') | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_26, c_1001])).
% 29.12/17.67  tff(c_1047, plain, (k1_funct_1('#skF_8', '#skF_2'('#skF_8', k1_relat_1('#skF_8')))='#skF_1'('#skF_8', k1_relat_1('#skF_8')) | k1_relat_1('#skF_7')=k1_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_50, c_1028])).
% 29.12/17.67  tff(c_1048, plain, (k1_funct_1('#skF_8', '#skF_2'('#skF_8', k1_relat_1('#skF_8')))='#skF_1'('#skF_8', k1_relat_1('#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_974, c_1047])).
% 29.12/17.67  tff(c_30, plain, (![C_54, B_53, A_48]: (C_54=B_53 | k1_funct_1(A_48, C_54)!=k1_funct_1(A_48, B_53) | ~r2_hidden(C_54, k1_relat_1(A_48)) | ~r2_hidden(B_53, k1_relat_1(A_48)) | ~v2_funct_1(A_48) | ~v1_funct_1(A_48) | ~v1_relat_1(A_48))), inference(cnfTransformation, [status(thm)], [f_76])).
% 29.12/17.67  tff(c_1111, plain, (![C_54]: (C_54='#skF_2'('#skF_8', k1_relat_1('#skF_8')) | k1_funct_1('#skF_8', C_54)!='#skF_1'('#skF_8', k1_relat_1('#skF_8')) | ~r2_hidden(C_54, k1_relat_1('#skF_8')) | ~r2_hidden('#skF_2'('#skF_8', k1_relat_1('#skF_8')), k1_relat_1('#skF_8')) | ~v2_funct_1('#skF_8') | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_1048, c_30])).
% 29.12/17.67  tff(c_1174, plain, (![C_180]: (C_180='#skF_2'('#skF_8', k1_relat_1('#skF_8')) | k1_funct_1('#skF_8', C_180)!='#skF_1'('#skF_8', k1_relat_1('#skF_8')) | ~r2_hidden(C_180, k1_relat_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_250, c_1052, c_1111])).
% 29.12/17.67  tff(c_1270, plain, (![C_181]: ('#skF_4'('#skF_8', k1_relat_1('#skF_7'), C_181)='#skF_2'('#skF_8', k1_relat_1('#skF_8')) | k1_funct_1('#skF_8', '#skF_4'('#skF_8', k1_relat_1('#skF_7'), C_181))!='#skF_1'('#skF_8', k1_relat_1('#skF_8')) | ~r2_hidden(C_181, k1_relat_1('#skF_7')))), inference(resolution, [status(thm)], [c_378, c_1174])).
% 29.12/17.67  tff(c_1401, plain, (![C_190]: ('#skF_4'('#skF_8', k1_relat_1('#skF_7'), C_190)='#skF_2'('#skF_8', k1_relat_1('#skF_8')) | C_190!='#skF_1'('#skF_8', k1_relat_1('#skF_8')) | ~r2_hidden(C_190, k1_relat_1('#skF_7')) | ~r2_hidden(C_190, k1_relat_1('#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_352, c_1270])).
% 29.12/17.67  tff(c_1447, plain, ('#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_6'('#skF_7'))='#skF_2'('#skF_8', k1_relat_1('#skF_8')) | '#skF_1'('#skF_8', k1_relat_1('#skF_8'))!='#skF_6'('#skF_7') | ~r2_hidden('#skF_6'('#skF_7'), k1_relat_1('#skF_7')) | v2_funct_1('#skF_7') | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_36, c_1401])).
% 29.12/17.67  tff(c_1481, plain, ('#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_6'('#skF_7'))='#skF_2'('#skF_8', k1_relat_1('#skF_8')) | '#skF_1'('#skF_8', k1_relat_1('#skF_8'))!='#skF_6'('#skF_7') | ~r2_hidden('#skF_6'('#skF_7'), k1_relat_1('#skF_7')) | v2_funct_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_1447])).
% 29.12/17.67  tff(c_1482, plain, ('#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_6'('#skF_7'))='#skF_2'('#skF_8', k1_relat_1('#skF_8')) | '#skF_1'('#skF_8', k1_relat_1('#skF_8'))!='#skF_6'('#skF_7') | ~r2_hidden('#skF_6'('#skF_7'), k1_relat_1('#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_249, c_1481])).
% 29.12/17.67  tff(c_1517, plain, (~r2_hidden('#skF_6'('#skF_7'), k1_relat_1('#skF_7'))), inference(splitLeft, [status(thm)], [c_1482])).
% 29.12/17.67  tff(c_1520, plain, (v2_funct_1('#skF_7') | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_36, c_1517])).
% 29.12/17.67  tff(c_1523, plain, (v2_funct_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_1520])).
% 29.12/17.67  tff(c_1525, plain, $false, inference(negUnitSimplification, [status(thm)], [c_249, c_1523])).
% 29.12/17.67  tff(c_1527, plain, (r2_hidden('#skF_6'('#skF_7'), k1_relat_1('#skF_7'))), inference(splitRight, [status(thm)], [c_1482])).
% 29.12/17.67  tff(c_38, plain, (![A_48]: (r2_hidden('#skF_5'(A_48), k1_relat_1(A_48)) | v2_funct_1(A_48) | ~v1_funct_1(A_48) | ~v1_relat_1(A_48))), inference(cnfTransformation, [status(thm)], [f_76])).
% 29.12/17.67  tff(c_34, plain, (![A_48]: (k1_funct_1(A_48, '#skF_5'(A_48))=k1_funct_1(A_48, '#skF_6'(A_48)) | v2_funct_1(A_48) | ~v1_funct_1(A_48) | ~v1_relat_1(A_48))), inference(cnfTransformation, [status(thm)], [f_76])).
% 29.12/17.67  tff(c_541, plain, (![A_143]: (k1_funct_1(k5_relat_1('#skF_8', '#skF_7'), A_143)=k1_funct_1('#skF_7', k1_funct_1('#skF_8', A_143)) | ~r2_hidden(A_143, k1_relat_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_56, c_54, c_518])).
% 29.12/17.67  tff(c_629, plain, (![C_145]: (k1_funct_1(k5_relat_1('#skF_8', '#skF_7'), '#skF_4'('#skF_8', k1_relat_1('#skF_7'), C_145))=k1_funct_1('#skF_7', k1_funct_1('#skF_8', '#skF_4'('#skF_8', k1_relat_1('#skF_7'), C_145))) | ~r2_hidden(C_145, k1_relat_1('#skF_7')))), inference(resolution, [status(thm)], [c_378, c_541])).
% 29.12/17.67  tff(c_641, plain, (![C_145]: (r2_hidden(k1_funct_1('#skF_7', k1_funct_1('#skF_8', '#skF_4'('#skF_8', k1_relat_1('#skF_7'), C_145))), k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))) | ~r2_hidden('#skF_4'('#skF_8', k1_relat_1('#skF_7'), C_145), k1_relat_1(k5_relat_1('#skF_8', '#skF_7'))) | ~v1_funct_1(k5_relat_1('#skF_8', '#skF_7')) | ~v1_relat_1(k5_relat_1('#skF_8', '#skF_7')) | ~r2_hidden(C_145, k1_relat_1('#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_629, c_12])).
% 29.12/17.67  tff(c_748, plain, (![C_154]: (r2_hidden(k1_funct_1('#skF_7', k1_funct_1('#skF_8', '#skF_4'('#skF_8', k1_relat_1('#skF_7'), C_154))), k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))) | ~r2_hidden('#skF_4'('#skF_8', k1_relat_1('#skF_7'), C_154), k1_relat_1('#skF_8')) | ~r2_hidden(C_154, k1_relat_1('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_389, c_442, c_311, c_641])).
% 29.12/17.67  tff(c_752, plain, (![C_155]: (r2_hidden(k1_funct_1('#skF_7', C_155), k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))) | ~r2_hidden('#skF_4'('#skF_8', k1_relat_1('#skF_7'), C_155), k1_relat_1('#skF_8')) | ~r2_hidden(C_155, k1_relat_1('#skF_7')) | ~r2_hidden(C_155, k1_relat_1('#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_352, c_748])).
% 29.12/17.67  tff(c_757, plain, (![C_156]: (r2_hidden(k1_funct_1('#skF_7', C_156), k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))) | ~r2_hidden(C_156, k1_relat_1('#skF_7')))), inference(resolution, [status(thm)], [c_378, c_752])).
% 29.12/17.67  tff(c_767, plain, (r2_hidden(k1_funct_1('#skF_7', '#skF_6'('#skF_7')), k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))) | ~r2_hidden('#skF_5'('#skF_7'), k1_relat_1('#skF_7')) | v2_funct_1('#skF_7') | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_34, c_757])).
% 29.12/17.67  tff(c_771, plain, (r2_hidden(k1_funct_1('#skF_7', '#skF_6'('#skF_7')), k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))) | ~r2_hidden('#skF_5'('#skF_7'), k1_relat_1('#skF_7')) | v2_funct_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_767])).
% 29.12/17.67  tff(c_772, plain, (r2_hidden(k1_funct_1('#skF_7', '#skF_6'('#skF_7')), k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))) | ~r2_hidden('#skF_5'('#skF_7'), k1_relat_1('#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_249, c_771])).
% 29.12/17.67  tff(c_773, plain, (~r2_hidden('#skF_5'('#skF_7'), k1_relat_1('#skF_7'))), inference(splitLeft, [status(thm)], [c_772])).
% 29.12/17.67  tff(c_776, plain, (v2_funct_1('#skF_7') | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_38, c_773])).
% 29.12/17.67  tff(c_779, plain, (v2_funct_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_776])).
% 29.12/17.67  tff(c_781, plain, $false, inference(negUnitSimplification, [status(thm)], [c_249, c_779])).
% 29.12/17.67  tff(c_783, plain, (r2_hidden('#skF_5'('#skF_7'), k1_relat_1('#skF_7'))), inference(splitRight, [status(thm)], [c_772])).
% 29.12/17.67  tff(c_583, plain, (![C_115]: (k1_funct_1(k5_relat_1('#skF_8', '#skF_7'), '#skF_4'('#skF_8', k1_relat_1('#skF_7'), C_115))=k1_funct_1('#skF_7', k1_funct_1('#skF_8', '#skF_4'('#skF_8', k1_relat_1('#skF_7'), C_115))) | ~r2_hidden(C_115, k1_relat_1('#skF_7')))), inference(resolution, [status(thm)], [c_378, c_541])).
% 29.12/17.67  tff(c_441, plain, (![C_115]: (r2_hidden('#skF_4'(k5_relat_1('#skF_8', '#skF_7'), k2_relat_1(k5_relat_1('#skF_8', '#skF_7')), C_115), k1_relat_1('#skF_8')) | ~r2_hidden(C_115, k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))))), inference(splitRight, [status(thm)], [c_432])).
% 29.12/17.67  tff(c_282, plain, (![A_105, D_106]: (r2_hidden(k1_funct_1(A_105, D_106), k2_relat_1(A_105)) | ~r2_hidden(D_106, k1_relat_1(A_105)) | ~v1_funct_1(A_105) | ~v1_relat_1(A_105))), inference(cnfTransformation, [status(thm)], [f_61])).
% 29.12/17.67  tff(c_288, plain, (![D_106]: (r2_hidden(k1_funct_1('#skF_8', D_106), k1_relat_1('#skF_7')) | ~r2_hidden(D_106, k1_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_50, c_282])).
% 29.12/17.67  tff(c_290, plain, (![D_106]: (r2_hidden(k1_funct_1('#skF_8', D_106), k1_relat_1('#skF_7')) | ~r2_hidden(D_106, k1_relat_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_288])).
% 29.12/17.67  tff(c_3211, plain, (![C_258]: (k1_funct_1(k5_relat_1('#skF_8', '#skF_7'), '#skF_4'(k5_relat_1('#skF_8', '#skF_7'), k2_relat_1(k5_relat_1('#skF_8', '#skF_7')), C_258))=k1_funct_1('#skF_7', k1_funct_1('#skF_8', '#skF_4'(k5_relat_1('#skF_8', '#skF_7'), k2_relat_1(k5_relat_1('#skF_8', '#skF_7')), C_258))) | ~r2_hidden(C_258, k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))))), inference(resolution, [status(thm)], [c_441, c_541])).
% 29.12/17.67  tff(c_3234, plain, (![C_258]: (k1_funct_1('#skF_7', k1_funct_1('#skF_8', '#skF_4'(k5_relat_1('#skF_8', '#skF_7'), k2_relat_1(k5_relat_1('#skF_8', '#skF_7')), C_258)))=C_258 | ~r2_hidden(C_258, k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))) | ~v1_funct_1(k5_relat_1('#skF_8', '#skF_7')) | ~v1_relat_1(k5_relat_1('#skF_8', '#skF_7')) | ~r2_hidden(C_258, k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))))), inference(superposition, [status(thm), theory('equality')], [c_3211, c_14])).
% 29.12/17.67  tff(c_3265, plain, (![C_259]: (k1_funct_1('#skF_7', k1_funct_1('#skF_8', '#skF_4'(k5_relat_1('#skF_8', '#skF_7'), k2_relat_1(k5_relat_1('#skF_8', '#skF_7')), C_259)))=C_259 | ~r2_hidden(C_259, k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))))), inference(demodulation, [status(thm), theory('equality')], [c_389, c_442, c_3234])).
% 29.12/17.67  tff(c_3286, plain, (![C_259]: (r2_hidden(C_259, k2_relat_1('#skF_7')) | ~r2_hidden(k1_funct_1('#skF_8', '#skF_4'(k5_relat_1('#skF_8', '#skF_7'), k2_relat_1(k5_relat_1('#skF_8', '#skF_7')), C_259)), k1_relat_1('#skF_7')) | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7') | ~r2_hidden(C_259, k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))))), inference(superposition, [status(thm), theory('equality')], [c_3265, c_12])).
% 29.12/17.67  tff(c_3399, plain, (![C_263]: (r2_hidden(C_263, k2_relat_1('#skF_7')) | ~r2_hidden(k1_funct_1('#skF_8', '#skF_4'(k5_relat_1('#skF_8', '#skF_7'), k2_relat_1(k5_relat_1('#skF_8', '#skF_7')), C_263)), k1_relat_1('#skF_7')) | ~r2_hidden(C_263, k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_3286])).
% 29.12/17.67  tff(c_3404, plain, (![C_264]: (r2_hidden(C_264, k2_relat_1('#skF_7')) | ~r2_hidden(C_264, k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))) | ~r2_hidden('#skF_4'(k5_relat_1('#skF_8', '#skF_7'), k2_relat_1(k5_relat_1('#skF_8', '#skF_7')), C_264), k1_relat_1('#skF_8')))), inference(resolution, [status(thm)], [c_290, c_3399])).
% 29.12/17.67  tff(c_3437, plain, (![C_267]: (r2_hidden(C_267, k2_relat_1('#skF_7')) | ~r2_hidden(C_267, k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))))), inference(resolution, [status(thm)], [c_441, c_3404])).
% 29.12/17.67  tff(c_3587, plain, (![A_8]: (r2_hidden('#skF_3'(A_8, k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))), k2_relat_1('#skF_7')) | r2_hidden('#skF_2'(A_8, k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))), k1_relat_1(A_8)) | k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))=k2_relat_1(A_8) | ~v1_funct_1(A_8) | ~v1_relat_1(A_8))), inference(resolution, [status(thm)], [c_28, c_3437])).
% 29.12/17.67  tff(c_484, plain, (![A_135, B_136, D_137]: (r2_hidden('#skF_2'(A_135, B_136), k1_relat_1(A_135)) | k1_funct_1(A_135, D_137)!='#skF_3'(A_135, B_136) | ~r2_hidden(D_137, k1_relat_1(A_135)) | k2_relat_1(A_135)=B_136 | ~v1_funct_1(A_135) | ~v1_relat_1(A_135))), inference(cnfTransformation, [status(thm)], [f_61])).
% 29.12/17.67  tff(c_490, plain, (![A_8, B_136, C_44]: (r2_hidden('#skF_2'(A_8, B_136), k1_relat_1(A_8)) | C_44!='#skF_3'(A_8, B_136) | ~r2_hidden('#skF_4'(A_8, k2_relat_1(A_8), C_44), k1_relat_1(A_8)) | k2_relat_1(A_8)=B_136 | ~v1_funct_1(A_8) | ~v1_relat_1(A_8) | ~r2_hidden(C_44, k2_relat_1(A_8)) | ~v1_funct_1(A_8) | ~v1_relat_1(A_8))), inference(superposition, [status(thm), theory('equality')], [c_14, c_484])).
% 29.12/17.67  tff(c_38294, plain, (![A_685, B_686]: (r2_hidden('#skF_2'(A_685, B_686), k1_relat_1(A_685)) | ~r2_hidden('#skF_4'(A_685, k2_relat_1(A_685), '#skF_3'(A_685, B_686)), k1_relat_1(A_685)) | k2_relat_1(A_685)=B_686 | ~v1_funct_1(A_685) | ~v1_relat_1(A_685) | ~r2_hidden('#skF_3'(A_685, B_686), k2_relat_1(A_685)) | ~v1_funct_1(A_685) | ~v1_relat_1(A_685))), inference(reflexivity, [status(thm), theory('equality')], [c_490])).
% 29.12/17.67  tff(c_38310, plain, (![A_687, B_688]: (r2_hidden('#skF_2'(A_687, B_688), k1_relat_1(A_687)) | k2_relat_1(A_687)=B_688 | ~r2_hidden('#skF_3'(A_687, B_688), k2_relat_1(A_687)) | ~v1_funct_1(A_687) | ~v1_relat_1(A_687))), inference(resolution, [status(thm)], [c_16, c_38294])).
% 29.12/17.67  tff(c_38330, plain, (r2_hidden('#skF_2'('#skF_7', k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))), k1_relat_1('#skF_7')) | k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))=k2_relat_1('#skF_7') | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_3587, c_38310])).
% 29.12/17.67  tff(c_38419, plain, (r2_hidden('#skF_2'('#skF_7', k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))), k1_relat_1('#skF_7')) | k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))=k2_relat_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_38330])).
% 29.12/17.67  tff(c_38473, plain, (k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))=k2_relat_1('#skF_7')), inference(splitLeft, [status(thm)], [c_38419])).
% 29.12/17.67  tff(c_457, plain, (![C_131, B_132, A_133]: (C_131=B_132 | k1_funct_1(A_133, C_131)!=k1_funct_1(A_133, B_132) | ~r2_hidden(C_131, k1_relat_1(A_133)) | ~r2_hidden(B_132, k1_relat_1(A_133)) | ~v2_funct_1(A_133) | ~v1_funct_1(A_133) | ~v1_relat_1(A_133))), inference(cnfTransformation, [status(thm)], [f_76])).
% 29.12/17.67  tff(c_469, plain, (![C_131, A_8, C_44]: (C_131='#skF_4'(A_8, k2_relat_1(A_8), C_44) | k1_funct_1(A_8, C_131)!=C_44 | ~r2_hidden(C_131, k1_relat_1(A_8)) | ~r2_hidden('#skF_4'(A_8, k2_relat_1(A_8), C_44), k1_relat_1(A_8)) | ~v2_funct_1(A_8) | ~v1_funct_1(A_8) | ~v1_relat_1(A_8) | ~r2_hidden(C_44, k2_relat_1(A_8)) | ~v1_funct_1(A_8) | ~v1_relat_1(A_8))), inference(superposition, [status(thm), theory('equality')], [c_14, c_457])).
% 29.12/17.67  tff(c_38768, plain, (![A_697, C_698]: ('#skF_4'(A_697, k2_relat_1(A_697), k1_funct_1(A_697, C_698))=C_698 | ~r2_hidden(C_698, k1_relat_1(A_697)) | ~r2_hidden('#skF_4'(A_697, k2_relat_1(A_697), k1_funct_1(A_697, C_698)), k1_relat_1(A_697)) | ~v2_funct_1(A_697) | ~v1_funct_1(A_697) | ~v1_relat_1(A_697) | ~r2_hidden(k1_funct_1(A_697, C_698), k2_relat_1(A_697)) | ~v1_funct_1(A_697) | ~v1_relat_1(A_697))), inference(reflexivity, [status(thm), theory('equality')], [c_469])).
% 29.12/17.67  tff(c_39046, plain, (![A_704, C_705]: ('#skF_4'(A_704, k2_relat_1(A_704), k1_funct_1(A_704, C_705))=C_705 | ~r2_hidden(C_705, k1_relat_1(A_704)) | ~v2_funct_1(A_704) | ~r2_hidden(k1_funct_1(A_704, C_705), k2_relat_1(A_704)) | ~v1_funct_1(A_704) | ~v1_relat_1(A_704))), inference(resolution, [status(thm)], [c_16, c_38768])).
% 29.12/17.67  tff(c_39220, plain, (![A_708, D_709]: ('#skF_4'(A_708, k2_relat_1(A_708), k1_funct_1(A_708, D_709))=D_709 | ~v2_funct_1(A_708) | ~r2_hidden(D_709, k1_relat_1(A_708)) | ~v1_funct_1(A_708) | ~v1_relat_1(A_708))), inference(resolution, [status(thm)], [c_12, c_39046])).
% 29.12/17.67  tff(c_39245, plain, (![D_709]: ('#skF_4'(k5_relat_1('#skF_8', '#skF_7'), k2_relat_1('#skF_7'), k1_funct_1(k5_relat_1('#skF_8', '#skF_7'), D_709))=D_709 | ~v2_funct_1(k5_relat_1('#skF_8', '#skF_7')) | ~r2_hidden(D_709, k1_relat_1(k5_relat_1('#skF_8', '#skF_7'))) | ~v1_funct_1(k5_relat_1('#skF_8', '#skF_7')) | ~v1_relat_1(k5_relat_1('#skF_8', '#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_38473, c_39220])).
% 29.12/17.67  tff(c_39347, plain, (![D_710]: ('#skF_4'(k5_relat_1('#skF_8', '#skF_7'), k2_relat_1('#skF_7'), k1_funct_1(k5_relat_1('#skF_8', '#skF_7'), D_710))=D_710 | ~r2_hidden(D_710, k1_relat_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_389, c_442, c_311, c_52, c_39245])).
% 29.12/17.67  tff(c_39706, plain, (![C_716]: ('#skF_4'(k5_relat_1('#skF_8', '#skF_7'), k2_relat_1('#skF_7'), k1_funct_1('#skF_7', k1_funct_1('#skF_8', '#skF_4'('#skF_8', k1_relat_1('#skF_7'), C_716))))='#skF_4'('#skF_8', k1_relat_1('#skF_7'), C_716) | ~r2_hidden('#skF_4'('#skF_8', k1_relat_1('#skF_7'), C_716), k1_relat_1('#skF_8')) | ~r2_hidden(C_716, k1_relat_1('#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_583, c_39347])).
% 29.12/17.67  tff(c_40037, plain, (![C_723]: ('#skF_4'(k5_relat_1('#skF_8', '#skF_7'), k2_relat_1('#skF_7'), k1_funct_1('#skF_7', C_723))='#skF_4'('#skF_8', k1_relat_1('#skF_7'), C_723) | ~r2_hidden('#skF_4'('#skF_8', k1_relat_1('#skF_7'), C_723), k1_relat_1('#skF_8')) | ~r2_hidden(C_723, k1_relat_1('#skF_7')) | ~r2_hidden(C_723, k1_relat_1('#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_352, c_39706])).
% 29.12/17.67  tff(c_40073, plain, (![C_724]: ('#skF_4'(k5_relat_1('#skF_8', '#skF_7'), k2_relat_1('#skF_7'), k1_funct_1('#skF_7', C_724))='#skF_4'('#skF_8', k1_relat_1('#skF_7'), C_724) | ~r2_hidden(C_724, k1_relat_1('#skF_7')))), inference(resolution, [status(thm)], [c_378, c_40037])).
% 29.12/17.67  tff(c_40137, plain, ('#skF_4'(k5_relat_1('#skF_8', '#skF_7'), k2_relat_1('#skF_7'), k1_funct_1('#skF_7', '#skF_6'('#skF_7')))='#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_5'('#skF_7')) | ~r2_hidden('#skF_5'('#skF_7'), k1_relat_1('#skF_7')) | v2_funct_1('#skF_7') | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_34, c_40073])).
% 29.12/17.67  tff(c_40150, plain, ('#skF_4'(k5_relat_1('#skF_8', '#skF_7'), k2_relat_1('#skF_7'), k1_funct_1('#skF_7', '#skF_6'('#skF_7')))='#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_5'('#skF_7')) | v2_funct_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_783, c_40137])).
% 29.12/17.67  tff(c_40151, plain, ('#skF_4'(k5_relat_1('#skF_8', '#skF_7'), k2_relat_1('#skF_7'), k1_funct_1('#skF_7', '#skF_6'('#skF_7')))='#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_5'('#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_249, c_40150])).
% 29.12/17.67  tff(c_40072, plain, (![C_115]: ('#skF_4'(k5_relat_1('#skF_8', '#skF_7'), k2_relat_1('#skF_7'), k1_funct_1('#skF_7', C_115))='#skF_4'('#skF_8', k1_relat_1('#skF_7'), C_115) | ~r2_hidden(C_115, k1_relat_1('#skF_7')))), inference(resolution, [status(thm)], [c_378, c_40037])).
% 29.12/17.67  tff(c_40155, plain, ('#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_5'('#skF_7'))='#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_6'('#skF_7')) | ~r2_hidden('#skF_6'('#skF_7'), k1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_40151, c_40072])).
% 29.12/17.67  tff(c_40180, plain, ('#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_5'('#skF_7'))='#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_6'('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_1527, c_40155])).
% 29.12/17.67  tff(c_40233, plain, (k1_funct_1('#skF_8', '#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_6'('#skF_7')))='#skF_5'('#skF_7') | ~r2_hidden('#skF_5'('#skF_7'), k1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_40180, c_352])).
% 29.12/17.67  tff(c_40249, plain, (k1_funct_1('#skF_8', '#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_6'('#skF_7')))='#skF_5'('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_783, c_40233])).
% 29.12/17.67  tff(c_40312, plain, ('#skF_5'('#skF_7')='#skF_6'('#skF_7') | ~r2_hidden('#skF_6'('#skF_7'), k1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_40249, c_352])).
% 29.12/17.67  tff(c_40355, plain, ('#skF_5'('#skF_7')='#skF_6'('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_1527, c_40312])).
% 29.12/17.67  tff(c_40357, plain, $false, inference(negUnitSimplification, [status(thm)], [c_269, c_40355])).
% 29.12/17.67  tff(c_40359, plain, (k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))!=k2_relat_1('#skF_7')), inference(splitRight, [status(thm)], [c_38419])).
% 29.12/17.67  tff(c_40358, plain, (r2_hidden('#skF_2'('#skF_7', k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))), k1_relat_1('#skF_7'))), inference(splitRight, [status(thm)], [c_38419])).
% 29.12/17.67  tff(c_789, plain, (![A_8, B_30]: (r2_hidden('#skF_1'(A_8, B_30), k2_relat_1(A_8)) | r2_hidden('#skF_3'(A_8, B_30), B_30) | k2_relat_1(A_8)=B_30 | ~v1_funct_1(A_8) | ~v1_relat_1(A_8))), inference(resolution, [status(thm)], [c_28, c_784])).
% 29.12/17.67  tff(c_3576, plain, (![A_8]: (r2_hidden('#skF_3'(A_8, k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))), k2_relat_1('#skF_7')) | r2_hidden('#skF_1'(A_8, k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))), k2_relat_1(A_8)) | k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))=k2_relat_1(A_8) | ~v1_funct_1(A_8) | ~v1_relat_1(A_8))), inference(resolution, [status(thm)], [c_789, c_3437])).
% 29.12/17.67  tff(c_672, plain, (![A_147, B_148, D_149]: (k1_funct_1(A_147, '#skF_2'(A_147, B_148))='#skF_1'(A_147, B_148) | k1_funct_1(A_147, D_149)!='#skF_3'(A_147, B_148) | ~r2_hidden(D_149, k1_relat_1(A_147)) | k2_relat_1(A_147)=B_148 | ~v1_funct_1(A_147) | ~v1_relat_1(A_147))), inference(cnfTransformation, [status(thm)], [f_61])).
% 29.12/17.67  tff(c_682, plain, (![A_8, B_148, C_44]: (k1_funct_1(A_8, '#skF_2'(A_8, B_148))='#skF_1'(A_8, B_148) | C_44!='#skF_3'(A_8, B_148) | ~r2_hidden('#skF_4'(A_8, k2_relat_1(A_8), C_44), k1_relat_1(A_8)) | k2_relat_1(A_8)=B_148 | ~v1_funct_1(A_8) | ~v1_relat_1(A_8) | ~r2_hidden(C_44, k2_relat_1(A_8)) | ~v1_funct_1(A_8) | ~v1_relat_1(A_8))), inference(superposition, [status(thm), theory('equality')], [c_14, c_672])).
% 29.12/17.67  tff(c_40455, plain, (![A_728, B_729]: (k1_funct_1(A_728, '#skF_2'(A_728, B_729))='#skF_1'(A_728, B_729) | ~r2_hidden('#skF_4'(A_728, k2_relat_1(A_728), '#skF_3'(A_728, B_729)), k1_relat_1(A_728)) | k2_relat_1(A_728)=B_729 | ~v1_funct_1(A_728) | ~v1_relat_1(A_728) | ~r2_hidden('#skF_3'(A_728, B_729), k2_relat_1(A_728)) | ~v1_funct_1(A_728) | ~v1_relat_1(A_728))), inference(reflexivity, [status(thm), theory('equality')], [c_682])).
% 29.12/17.67  tff(c_40556, plain, (![A_730, B_731]: (k1_funct_1(A_730, '#skF_2'(A_730, B_731))='#skF_1'(A_730, B_731) | k2_relat_1(A_730)=B_731 | ~r2_hidden('#skF_3'(A_730, B_731), k2_relat_1(A_730)) | ~v1_funct_1(A_730) | ~v1_relat_1(A_730))), inference(resolution, [status(thm)], [c_16, c_40455])).
% 29.12/17.67  tff(c_40580, plain, (k1_funct_1('#skF_7', '#skF_2'('#skF_7', k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))))='#skF_1'('#skF_7', k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))) | r2_hidden('#skF_1'('#skF_7', k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))), k2_relat_1('#skF_7')) | k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))=k2_relat_1('#skF_7') | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_3576, c_40556])).
% 29.12/17.67  tff(c_40670, plain, (k1_funct_1('#skF_7', '#skF_2'('#skF_7', k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))))='#skF_1'('#skF_7', k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))) | r2_hidden('#skF_1'('#skF_7', k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))), k2_relat_1('#skF_7')) | k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))=k2_relat_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_40580])).
% 29.12/17.67  tff(c_40671, plain, (k1_funct_1('#skF_7', '#skF_2'('#skF_7', k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))))='#skF_1'('#skF_7', k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))) | r2_hidden('#skF_1'('#skF_7', k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))), k2_relat_1('#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_40359, c_40670])).
% 29.12/17.67  tff(c_40723, plain, (r2_hidden('#skF_1'('#skF_7', k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))), k2_relat_1('#skF_7'))), inference(splitLeft, [status(thm)], [c_40671])).
% 29.12/17.67  tff(c_763, plain, (![C_44]: (r2_hidden(C_44, k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))) | ~r2_hidden('#skF_4'('#skF_7', k2_relat_1('#skF_7'), C_44), k1_relat_1('#skF_7')) | ~r2_hidden(C_44, k2_relat_1('#skF_7')) | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_14, c_757])).
% 29.12/17.67  tff(c_835, plain, (![C_162]: (r2_hidden(C_162, k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))) | ~r2_hidden('#skF_4'('#skF_7', k2_relat_1('#skF_7'), C_162), k1_relat_1('#skF_7')) | ~r2_hidden(C_162, k2_relat_1('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_763])).
% 29.12/17.67  tff(c_839, plain, (![C_44]: (r2_hidden(C_44, k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))) | ~r2_hidden(C_44, k2_relat_1('#skF_7')) | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7'))), inference(resolution, [status(thm)], [c_16, c_835])).
% 29.12/17.67  tff(c_842, plain, (![C_44]: (r2_hidden(C_44, k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))) | ~r2_hidden(C_44, k2_relat_1('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_839])).
% 29.12/17.67  tff(c_24, plain, (![A_8, B_30]: (~r2_hidden('#skF_1'(A_8, B_30), B_30) | r2_hidden('#skF_3'(A_8, B_30), B_30) | k2_relat_1(A_8)=B_30 | ~v1_funct_1(A_8) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_61])).
% 29.12/17.67  tff(c_37398, plain, (![A_660]: (r2_hidden('#skF_3'(A_660, k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))), k2_relat_1('#skF_7')) | ~r2_hidden('#skF_1'(A_660, k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))), k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))) | k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))=k2_relat_1(A_660) | ~v1_funct_1(A_660) | ~v1_relat_1(A_660))), inference(resolution, [status(thm)], [c_24, c_3437])).
% 29.12/17.67  tff(c_37429, plain, (![A_660]: (r2_hidden('#skF_3'(A_660, k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))), k2_relat_1('#skF_7')) | k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))=k2_relat_1(A_660) | ~v1_funct_1(A_660) | ~v1_relat_1(A_660) | ~r2_hidden('#skF_1'(A_660, k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))), k2_relat_1('#skF_7')))), inference(resolution, [status(thm)], [c_842, c_37398])).
% 29.12/17.67  tff(c_40572, plain, (k1_funct_1('#skF_7', '#skF_2'('#skF_7', k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))))='#skF_1'('#skF_7', k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))) | k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))=k2_relat_1('#skF_7') | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7') | ~r2_hidden('#skF_1'('#skF_7', k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))), k2_relat_1('#skF_7'))), inference(resolution, [status(thm)], [c_37429, c_40556])).
% 29.12/17.67  tff(c_40662, plain, (k1_funct_1('#skF_7', '#skF_2'('#skF_7', k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))))='#skF_1'('#skF_7', k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))) | k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))=k2_relat_1('#skF_7') | ~r2_hidden('#skF_1'('#skF_7', k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))), k2_relat_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_40572])).
% 29.12/17.67  tff(c_40663, plain, (k1_funct_1('#skF_7', '#skF_2'('#skF_7', k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))))='#skF_1'('#skF_7', k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))) | ~r2_hidden('#skF_1'('#skF_7', k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))), k2_relat_1('#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_40359, c_40662])).
% 29.12/17.67  tff(c_40857, plain, (k1_funct_1('#skF_7', '#skF_2'('#skF_7', k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))))='#skF_1'('#skF_7', k2_relat_1(k5_relat_1('#skF_8', '#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_40723, c_40663])).
% 29.12/17.67  tff(c_756, plain, (![C_115]: (r2_hidden(k1_funct_1('#skF_7', C_115), k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))) | ~r2_hidden(C_115, k1_relat_1('#skF_7')))), inference(resolution, [status(thm)], [c_378, c_752])).
% 29.12/17.67  tff(c_40879, plain, (r2_hidden('#skF_1'('#skF_7', k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))), k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))) | ~r2_hidden('#skF_2'('#skF_7', k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))), k1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_40857, c_756])).
% 29.12/17.67  tff(c_40919, plain, (r2_hidden('#skF_1'('#skF_7', k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))), k2_relat_1(k5_relat_1('#skF_8', '#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_40358, c_40879])).
% 29.12/17.67  tff(c_18, plain, (![A_8, B_30, D_43]: (~r2_hidden('#skF_1'(A_8, B_30), B_30) | k1_funct_1(A_8, D_43)!='#skF_3'(A_8, B_30) | ~r2_hidden(D_43, k1_relat_1(A_8)) | k2_relat_1(A_8)=B_30 | ~v1_funct_1(A_8) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_61])).
% 29.12/17.67  tff(c_40944, plain, (![D_43]: (k1_funct_1('#skF_7', D_43)!='#skF_3'('#skF_7', k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))) | ~r2_hidden(D_43, k1_relat_1('#skF_7')) | k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))=k2_relat_1('#skF_7') | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7'))), inference(resolution, [status(thm)], [c_40919, c_18])).
% 29.12/17.67  tff(c_40953, plain, (![D_43]: (k1_funct_1('#skF_7', D_43)!='#skF_3'('#skF_7', k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))) | ~r2_hidden(D_43, k1_relat_1('#skF_7')) | k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))=k2_relat_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_40944])).
% 29.12/17.67  tff(c_40969, plain, (![D_734]: (k1_funct_1('#skF_7', D_734)!='#skF_3'('#skF_7', k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))) | ~r2_hidden(D_734, k1_relat_1('#skF_7')))), inference(negUnitSimplification, [status(thm)], [c_40359, c_40953])).
% 29.12/17.67  tff(c_40987, plain, (![C_44]: (C_44!='#skF_3'('#skF_7', k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))) | ~r2_hidden('#skF_4'('#skF_7', k2_relat_1('#skF_7'), C_44), k1_relat_1('#skF_7')) | ~r2_hidden(C_44, k2_relat_1('#skF_7')) | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_14, c_40969])).
% 29.12/17.67  tff(c_41000, plain, (![C_736]: (C_736!='#skF_3'('#skF_7', k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))) | ~r2_hidden('#skF_4'('#skF_7', k2_relat_1('#skF_7'), C_736), k1_relat_1('#skF_7')) | ~r2_hidden(C_736, k2_relat_1('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_40987])).
% 29.12/17.67  tff(c_41004, plain, (![C_44]: (C_44!='#skF_3'('#skF_7', k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))) | ~r2_hidden(C_44, k2_relat_1('#skF_7')) | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7'))), inference(resolution, [status(thm)], [c_16, c_41000])).
% 29.12/17.67  tff(c_41008, plain, (~r2_hidden('#skF_3'('#skF_7', k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))), k2_relat_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_41004])).
% 29.12/17.67  tff(c_3588, plain, (![A_8]: (r2_hidden('#skF_3'(A_8, k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))), k2_relat_1('#skF_7')) | ~r2_hidden('#skF_1'(A_8, k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))), k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))) | k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))=k2_relat_1(A_8) | ~v1_funct_1(A_8) | ~v1_relat_1(A_8))), inference(resolution, [status(thm)], [c_24, c_3437])).
% 29.12/17.67  tff(c_40939, plain, (r2_hidden('#skF_3'('#skF_7', k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))), k2_relat_1('#skF_7')) | k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))=k2_relat_1('#skF_7') | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_40919, c_3588])).
% 29.12/17.67  tff(c_40947, plain, (r2_hidden('#skF_3'('#skF_7', k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))), k2_relat_1('#skF_7')) | k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))=k2_relat_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_40939])).
% 29.12/17.67  tff(c_40948, plain, (r2_hidden('#skF_3'('#skF_7', k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))), k2_relat_1('#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_40359, c_40947])).
% 29.12/17.67  tff(c_41010, plain, $false, inference(negUnitSimplification, [status(thm)], [c_41008, c_40948])).
% 29.12/17.67  tff(c_41012, plain, (~r2_hidden('#skF_1'('#skF_7', k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))), k2_relat_1('#skF_7'))), inference(splitRight, [status(thm)], [c_40671])).
% 29.12/17.67  tff(c_41011, plain, (k1_funct_1('#skF_7', '#skF_2'('#skF_7', k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))))='#skF_1'('#skF_7', k2_relat_1(k5_relat_1('#skF_8', '#skF_7')))), inference(splitRight, [status(thm)], [c_40671])).
% 29.12/17.67  tff(c_3578, plain, (![C_115]: (r2_hidden(k1_funct_1('#skF_7', C_115), k2_relat_1('#skF_7')) | ~r2_hidden(C_115, k1_relat_1('#skF_7')))), inference(resolution, [status(thm)], [c_756, c_3437])).
% 29.12/17.67  tff(c_41168, plain, (r2_hidden('#skF_1'('#skF_7', k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))), k2_relat_1('#skF_7')) | ~r2_hidden('#skF_2'('#skF_7', k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))), k1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_41011, c_3578])).
% 29.12/17.67  tff(c_41209, plain, (r2_hidden('#skF_1'('#skF_7', k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))), k2_relat_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_40358, c_41168])).
% 29.12/17.67  tff(c_41211, plain, $false, inference(negUnitSimplification, [status(thm)], [c_41012, c_41209])).
% 29.12/17.67  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 29.12/17.67  
% 29.12/17.67  Inference rules
% 29.12/17.67  ----------------------
% 29.12/17.67  #Ref     : 14
% 29.12/17.67  #Sup     : 9077
% 29.12/17.67  #Fact    : 2
% 29.12/17.67  #Define  : 0
% 29.12/17.67  #Split   : 78
% 29.12/17.67  #Chain   : 0
% 29.12/17.67  #Close   : 0
% 29.12/17.67  
% 29.12/17.67  Ordering : KBO
% 29.12/17.67  
% 29.12/17.67  Simplification rules
% 29.12/17.67  ----------------------
% 29.12/17.67  #Subsume      : 1527
% 29.12/17.67  #Demod        : 29556
% 29.12/17.67  #Tautology    : 1737
% 29.12/17.67  #SimpNegUnit  : 408
% 29.12/17.67  #BackRed      : 155
% 29.12/17.67  
% 29.12/17.67  #Partial instantiations: 0
% 29.12/17.67  #Strategies tried      : 1
% 29.12/17.67  
% 29.12/17.67  Timing (in seconds)
% 29.12/17.67  ----------------------
% 29.12/17.67  Preprocessing        : 0.34
% 29.12/17.67  Parsing              : 0.17
% 29.12/17.67  CNF conversion       : 0.03
% 29.12/17.67  Main loop            : 16.54
% 29.12/17.67  Inferencing          : 2.85
% 29.12/17.67  Reduction            : 7.60
% 29.12/17.67  Demodulation         : 6.45
% 29.12/17.67  BG Simplification    : 0.38
% 29.12/17.67  Subsumption          : 5.12
% 29.12/17.67  Abstraction          : 0.85
% 29.12/17.67  MUC search           : 0.00
% 29.12/17.67  Cooper               : 0.00
% 29.12/17.67  Total                : 16.95
% 29.12/17.67  Index Insertion      : 0.00
% 29.12/17.67  Index Deletion       : 0.00
% 29.12/17.67  Index Matching       : 0.00
% 29.12/17.67  BG Taut test         : 0.00
%------------------------------------------------------------------------------
