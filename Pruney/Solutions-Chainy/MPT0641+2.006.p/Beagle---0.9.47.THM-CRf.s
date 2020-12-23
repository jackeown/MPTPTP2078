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
% DateTime   : Thu Dec  3 10:03:39 EST 2020

% Result     : Theorem 13.80s
% Output     : CNFRefutation 14.04s
% Verified   : 
% Statistics : Number of formulae       :  171 (4062 expanded)
%              Number of leaves         :   29 (1415 expanded)
%              Depth                    :   36
%              Number of atoms          :  513 (16171 expanded)
%              Number of equality atoms :  111 (3322 expanded)
%              Maximal formula depth    :   15 (   5 average)
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

tff(f_101,axiom,(
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
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_46,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k2_relat_1(A),k1_relat_1(B))
           => k1_relat_1(k5_relat_1(A,B)) = k1_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_relat_1)).

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

tff(c_36,plain,(
    ! [A_48] :
      ( r2_hidden('#skF_6'(A_48),k1_relat_1(A_48))
      | v2_funct_1(A_48)
      | ~ v1_funct_1(A_48)
      | ~ v1_relat_1(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

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

tff(c_452,plain,(
    ! [B_128,C_129,A_130] :
      ( k1_funct_1(k5_relat_1(B_128,C_129),A_130) = k1_funct_1(C_129,k1_funct_1(B_128,A_130))
      | ~ r2_hidden(A_130,k1_relat_1(B_128))
      | ~ v1_funct_1(C_129)
      | ~ v1_relat_1(C_129)
      | ~ v1_funct_1(B_128)
      | ~ v1_relat_1(B_128) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_467,plain,(
    ! [C_129,C_115] :
      ( k1_funct_1(k5_relat_1('#skF_8',C_129),'#skF_4'('#skF_8',k1_relat_1('#skF_7'),C_115)) = k1_funct_1(C_129,k1_funct_1('#skF_8','#skF_4'('#skF_8',k1_relat_1('#skF_7'),C_115)))
      | ~ v1_funct_1(C_129)
      | ~ v1_relat_1(C_129)
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8')
      | ~ r2_hidden(C_115,k1_relat_1('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_378,c_452])).

tff(c_487,plain,(
    ! [C_129,C_115] :
      ( k1_funct_1(k5_relat_1('#skF_8',C_129),'#skF_4'('#skF_8',k1_relat_1('#skF_7'),C_115)) = k1_funct_1(C_129,k1_funct_1('#skF_8','#skF_4'('#skF_8',k1_relat_1('#skF_7'),C_115)))
      | ~ v1_funct_1(C_129)
      | ~ v1_relat_1(C_129)
      | ~ r2_hidden(C_115,k1_relat_1('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_467])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( v1_relat_1(k5_relat_1(A_3,B_4))
      | ~ v1_relat_1(B_4)
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

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

tff(c_12,plain,(
    ! [A_8,D_47] :
      ( r2_hidden(k1_funct_1(A_8,D_47),k2_relat_1(A_8))
      | ~ r2_hidden(D_47,k1_relat_1(A_8))
      | ~ v1_funct_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

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

tff(c_454,plain,(
    ! [C_129,C_115] :
      ( k1_funct_1(k5_relat_1('#skF_8',C_129),'#skF_4'(k5_relat_1('#skF_8','#skF_7'),k2_relat_1(k5_relat_1('#skF_8','#skF_7')),C_115)) = k1_funct_1(C_129,k1_funct_1('#skF_8','#skF_4'(k5_relat_1('#skF_8','#skF_7'),k2_relat_1(k5_relat_1('#skF_8','#skF_7')),C_115)))
      | ~ v1_funct_1(C_129)
      | ~ v1_relat_1(C_129)
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8')
      | ~ r2_hidden(C_115,k2_relat_1(k5_relat_1('#skF_8','#skF_7'))) ) ),
    inference(resolution,[status(thm)],[c_441,c_452])).

tff(c_3175,plain,(
    ! [C_279,C_280] :
      ( k1_funct_1(k5_relat_1('#skF_8',C_279),'#skF_4'(k5_relat_1('#skF_8','#skF_7'),k2_relat_1(k5_relat_1('#skF_8','#skF_7')),C_280)) = k1_funct_1(C_279,k1_funct_1('#skF_8','#skF_4'(k5_relat_1('#skF_8','#skF_7'),k2_relat_1(k5_relat_1('#skF_8','#skF_7')),C_280)))
      | ~ v1_funct_1(C_279)
      | ~ v1_relat_1(C_279)
      | ~ r2_hidden(C_280,k2_relat_1(k5_relat_1('#skF_8','#skF_7'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_454])).

tff(c_14,plain,(
    ! [A_8,C_44] :
      ( k1_funct_1(A_8,'#skF_4'(A_8,k2_relat_1(A_8),C_44)) = C_44
      | ~ r2_hidden(C_44,k2_relat_1(A_8))
      | ~ v1_funct_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_3200,plain,(
    ! [C_280] :
      ( k1_funct_1('#skF_7',k1_funct_1('#skF_8','#skF_4'(k5_relat_1('#skF_8','#skF_7'),k2_relat_1(k5_relat_1('#skF_8','#skF_7')),C_280))) = C_280
      | ~ r2_hidden(C_280,k2_relat_1(k5_relat_1('#skF_8','#skF_7')))
      | ~ v1_funct_1(k5_relat_1('#skF_8','#skF_7'))
      | ~ v1_relat_1(k5_relat_1('#skF_8','#skF_7'))
      | ~ v1_funct_1('#skF_7')
      | ~ v1_relat_1('#skF_7')
      | ~ r2_hidden(C_280,k2_relat_1(k5_relat_1('#skF_8','#skF_7'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3175,c_14])).

tff(c_3221,plain,(
    ! [C_281] :
      ( k1_funct_1('#skF_7',k1_funct_1('#skF_8','#skF_4'(k5_relat_1('#skF_8','#skF_7'),k2_relat_1(k5_relat_1('#skF_8','#skF_7')),C_281))) = C_281
      | ~ r2_hidden(C_281,k2_relat_1(k5_relat_1('#skF_8','#skF_7'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_389,c_442,c_3200])).

tff(c_3240,plain,(
    ! [C_281] :
      ( r2_hidden(C_281,k2_relat_1('#skF_7'))
      | ~ r2_hidden(k1_funct_1('#skF_8','#skF_4'(k5_relat_1('#skF_8','#skF_7'),k2_relat_1(k5_relat_1('#skF_8','#skF_7')),C_281)),k1_relat_1('#skF_7'))
      | ~ v1_funct_1('#skF_7')
      | ~ v1_relat_1('#skF_7')
      | ~ r2_hidden(C_281,k2_relat_1(k5_relat_1('#skF_8','#skF_7'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3221,c_12])).

tff(c_3259,plain,(
    ! [C_282] :
      ( r2_hidden(C_282,k2_relat_1('#skF_7'))
      | ~ r2_hidden(k1_funct_1('#skF_8','#skF_4'(k5_relat_1('#skF_8','#skF_7'),k2_relat_1(k5_relat_1('#skF_8','#skF_7')),C_282)),k1_relat_1('#skF_7'))
      | ~ r2_hidden(C_282,k2_relat_1(k5_relat_1('#skF_8','#skF_7'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_3240])).

tff(c_3335,plain,(
    ! [C_286] :
      ( r2_hidden(C_286,k2_relat_1('#skF_7'))
      | ~ r2_hidden(C_286,k2_relat_1(k5_relat_1('#skF_8','#skF_7')))
      | ~ r2_hidden('#skF_4'(k5_relat_1('#skF_8','#skF_7'),k2_relat_1(k5_relat_1('#skF_8','#skF_7')),C_286),k1_relat_1('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_290,c_3259])).

tff(c_3340,plain,(
    ! [C_287] :
      ( r2_hidden(C_287,k2_relat_1('#skF_7'))
      | ~ r2_hidden(C_287,k2_relat_1(k5_relat_1('#skF_8','#skF_7'))) ) ),
    inference(resolution,[status(thm)],[c_441,c_3335])).

tff(c_3431,plain,(
    ! [D_47] :
      ( r2_hidden(k1_funct_1(k5_relat_1('#skF_8','#skF_7'),D_47),k2_relat_1('#skF_7'))
      | ~ r2_hidden(D_47,k1_relat_1(k5_relat_1('#skF_8','#skF_7')))
      | ~ v1_funct_1(k5_relat_1('#skF_8','#skF_7'))
      | ~ v1_relat_1(k5_relat_1('#skF_8','#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_12,c_3340])).

tff(c_3476,plain,(
    ! [D_288] :
      ( r2_hidden(k1_funct_1(k5_relat_1('#skF_8','#skF_7'),D_288),k2_relat_1('#skF_7'))
      | ~ r2_hidden(D_288,k1_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_389,c_442,c_311,c_3431])).

tff(c_3518,plain,(
    ! [C_115] :
      ( r2_hidden(k1_funct_1('#skF_7',k1_funct_1('#skF_8','#skF_4'('#skF_8',k1_relat_1('#skF_7'),C_115))),k2_relat_1('#skF_7'))
      | ~ r2_hidden('#skF_4'('#skF_8',k1_relat_1('#skF_7'),C_115),k1_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_7')
      | ~ v1_relat_1('#skF_7')
      | ~ r2_hidden(C_115,k1_relat_1('#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_487,c_3476])).

tff(c_11087,plain,(
    ! [C_407] :
      ( r2_hidden(k1_funct_1('#skF_7',k1_funct_1('#skF_8','#skF_4'('#skF_8',k1_relat_1('#skF_7'),C_407))),k2_relat_1('#skF_7'))
      | ~ r2_hidden('#skF_4'('#skF_8',k1_relat_1('#skF_7'),C_407),k1_relat_1('#skF_8'))
      | ~ r2_hidden(C_407,k1_relat_1('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_3518])).

tff(c_11100,plain,(
    ! [C_408] :
      ( r2_hidden(k1_funct_1('#skF_7',C_408),k2_relat_1('#skF_7'))
      | ~ r2_hidden('#skF_4'('#skF_8',k1_relat_1('#skF_7'),C_408),k1_relat_1('#skF_8'))
      | ~ r2_hidden(C_408,k1_relat_1('#skF_7'))
      | ~ r2_hidden(C_408,k1_relat_1('#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_352,c_11087])).

tff(c_11108,plain,(
    ! [C_409] :
      ( r2_hidden(k1_funct_1('#skF_7',C_409),k2_relat_1('#skF_7'))
      | ~ r2_hidden(C_409,k1_relat_1('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_378,c_11100])).

tff(c_11136,plain,
    ( r2_hidden(k1_funct_1('#skF_7','#skF_6'('#skF_7')),k2_relat_1('#skF_7'))
    | ~ r2_hidden('#skF_5'('#skF_7'),k1_relat_1('#skF_7'))
    | v2_funct_1('#skF_7')
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_11108])).

tff(c_11147,plain,
    ( r2_hidden(k1_funct_1('#skF_7','#skF_6'('#skF_7')),k2_relat_1('#skF_7'))
    | ~ r2_hidden('#skF_5'('#skF_7'),k1_relat_1('#skF_7'))
    | v2_funct_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_11136])).

tff(c_11148,plain,
    ( r2_hidden(k1_funct_1('#skF_7','#skF_6'('#skF_7')),k2_relat_1('#skF_7'))
    | ~ r2_hidden('#skF_5'('#skF_7'),k1_relat_1('#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_249,c_11147])).

tff(c_11149,plain,(
    ~ r2_hidden('#skF_5'('#skF_7'),k1_relat_1('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_11148])).

tff(c_11152,plain,
    ( v2_funct_1('#skF_7')
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_38,c_11149])).

tff(c_11155,plain,(
    v2_funct_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_11152])).

tff(c_11157,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_249,c_11155])).

tff(c_11159,plain,(
    r2_hidden('#skF_5'('#skF_7'),k1_relat_1('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_11148])).

tff(c_263,plain,(
    ! [A_99] :
      ( '#skF_5'(A_99) != '#skF_6'(A_99)
      | v2_funct_1(A_99)
      | ~ v1_funct_1(A_99)
      | ~ v1_relat_1(A_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_266,plain,
    ( '#skF_5'('#skF_7') != '#skF_6'('#skF_7')
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_263,c_249])).

tff(c_269,plain,(
    '#skF_5'('#skF_7') != '#skF_6'('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_266])).

tff(c_28,plain,(
    ! [A_8,B_30] :
      ( r2_hidden('#skF_2'(A_8,B_30),k1_relat_1(A_8))
      | r2_hidden('#skF_3'(A_8,B_30),B_30)
      | k2_relat_1(A_8) = B_30
      | ~ v1_funct_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_250,plain,(
    v2_funct_1('#skF_8') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_26,plain,(
    ! [A_8,B_30] :
      ( k1_funct_1(A_8,'#skF_2'(A_8,B_30)) = '#skF_1'(A_8,B_30)
      | r2_hidden('#skF_3'(A_8,B_30),B_30)
      | k2_relat_1(A_8) = B_30
      | ~ v1_funct_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_500,plain,(
    ! [C_131,B_132,A_133] :
      ( C_131 = B_132
      | k1_funct_1(A_133,C_131) != k1_funct_1(A_133,B_132)
      | ~ r2_hidden(C_131,k1_relat_1(A_133))
      | ~ r2_hidden(B_132,k1_relat_1(A_133))
      | ~ v2_funct_1(A_133)
      | ~ v1_funct_1(A_133)
      | ~ v1_relat_1(A_133) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_3264,plain,(
    ! [C_283,A_284,B_285] :
      ( C_283 = '#skF_2'(A_284,B_285)
      | k1_funct_1(A_284,C_283) != '#skF_1'(A_284,B_285)
      | ~ r2_hidden(C_283,k1_relat_1(A_284))
      | ~ r2_hidden('#skF_2'(A_284,B_285),k1_relat_1(A_284))
      | ~ v2_funct_1(A_284)
      | ~ v1_funct_1(A_284)
      | ~ v1_relat_1(A_284)
      | r2_hidden('#skF_3'(A_284,B_285),B_285)
      | k2_relat_1(A_284) = B_285
      | ~ v1_funct_1(A_284)
      | ~ v1_relat_1(A_284) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_500])).

tff(c_3324,plain,(
    ! [C_112,B_285] :
      ( '#skF_4'('#skF_8',k1_relat_1('#skF_7'),C_112) = '#skF_2'('#skF_8',B_285)
      | C_112 != '#skF_1'('#skF_8',B_285)
      | ~ r2_hidden('#skF_4'('#skF_8',k1_relat_1('#skF_7'),C_112),k1_relat_1('#skF_8'))
      | ~ r2_hidden('#skF_2'('#skF_8',B_285),k1_relat_1('#skF_8'))
      | ~ v2_funct_1('#skF_8')
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8')
      | r2_hidden('#skF_3'('#skF_8',B_285),B_285)
      | k2_relat_1('#skF_8') = B_285
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8')
      | ~ r2_hidden(C_112,k1_relat_1('#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_352,c_3264])).

tff(c_16301,plain,(
    ! [C_508,B_509] :
      ( '#skF_4'('#skF_8',k1_relat_1('#skF_7'),C_508) = '#skF_2'('#skF_8',B_509)
      | C_508 != '#skF_1'('#skF_8',B_509)
      | ~ r2_hidden('#skF_4'('#skF_8',k1_relat_1('#skF_7'),C_508),k1_relat_1('#skF_8'))
      | ~ r2_hidden('#skF_2'('#skF_8',B_509),k1_relat_1('#skF_8'))
      | r2_hidden('#skF_3'('#skF_8',B_509),B_509)
      | k1_relat_1('#skF_7') = B_509
      | ~ r2_hidden(C_508,k1_relat_1('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_50,c_56,c_54,c_250,c_3324])).

tff(c_16392,plain,(
    ! [C_511,B_512] :
      ( '#skF_4'('#skF_8',k1_relat_1('#skF_7'),C_511) = '#skF_2'('#skF_8',B_512)
      | C_511 != '#skF_1'('#skF_8',B_512)
      | ~ r2_hidden('#skF_2'('#skF_8',B_512),k1_relat_1('#skF_8'))
      | r2_hidden('#skF_3'('#skF_8',B_512),B_512)
      | k1_relat_1('#skF_7') = B_512
      | ~ r2_hidden(C_511,k1_relat_1('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_378,c_16301])).

tff(c_16408,plain,(
    ! [C_511,B_30] :
      ( '#skF_4'('#skF_8',k1_relat_1('#skF_7'),C_511) = '#skF_2'('#skF_8',B_30)
      | C_511 != '#skF_1'('#skF_8',B_30)
      | k1_relat_1('#skF_7') = B_30
      | ~ r2_hidden(C_511,k1_relat_1('#skF_7'))
      | r2_hidden('#skF_3'('#skF_8',B_30),B_30)
      | k2_relat_1('#skF_8') = B_30
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_28,c_16392])).

tff(c_16427,plain,(
    ! [C_513,B_514] :
      ( '#skF_4'('#skF_8',k1_relat_1('#skF_7'),C_513) = '#skF_2'('#skF_8',B_514)
      | C_513 != '#skF_1'('#skF_8',B_514)
      | ~ r2_hidden(C_513,k1_relat_1('#skF_7'))
      | r2_hidden('#skF_3'('#skF_8',B_514),B_514)
      | k1_relat_1('#skF_7') = B_514 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_50,c_16408])).

tff(c_16511,plain,(
    ! [B_514] :
      ( '#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_6'('#skF_7')) = '#skF_2'('#skF_8',B_514)
      | '#skF_1'('#skF_8',B_514) != '#skF_6'('#skF_7')
      | r2_hidden('#skF_3'('#skF_8',B_514),B_514)
      | k1_relat_1('#skF_7') = B_514
      | v2_funct_1('#skF_7')
      | ~ v1_funct_1('#skF_7')
      | ~ v1_relat_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_36,c_16427])).

tff(c_16570,plain,(
    ! [B_514] :
      ( '#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_6'('#skF_7')) = '#skF_2'('#skF_8',B_514)
      | '#skF_1'('#skF_8',B_514) != '#skF_6'('#skF_7')
      | r2_hidden('#skF_3'('#skF_8',B_514),B_514)
      | k1_relat_1('#skF_7') = B_514
      | v2_funct_1('#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_16511])).

tff(c_16577,plain,(
    ! [B_515] :
      ( '#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_6'('#skF_7')) = '#skF_2'('#skF_8',B_515)
      | '#skF_1'('#skF_8',B_515) != '#skF_6'('#skF_7')
      | r2_hidden('#skF_3'('#skF_8',B_515),B_515)
      | k1_relat_1('#skF_7') = B_515 ) ),
    inference(negUnitSimplification,[status(thm)],[c_249,c_16570])).

tff(c_16621,plain,(
    ! [B_515] :
      ( r2_hidden('#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_6'('#skF_7')),k1_relat_1('#skF_8'))
      | r2_hidden('#skF_3'('#skF_8',B_515),B_515)
      | k2_relat_1('#skF_8') = B_515
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8')
      | '#skF_1'('#skF_8',B_515) != '#skF_6'('#skF_7')
      | r2_hidden('#skF_3'('#skF_8',B_515),B_515)
      | k1_relat_1('#skF_7') = B_515 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16577,c_28])).

tff(c_16677,plain,(
    ! [B_515] :
      ( r2_hidden('#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_6'('#skF_7')),k1_relat_1('#skF_8'))
      | '#skF_1'('#skF_8',B_515) != '#skF_6'('#skF_7')
      | r2_hidden('#skF_3'('#skF_8',B_515),B_515)
      | k1_relat_1('#skF_7') = B_515 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_50,c_16621])).

tff(c_16976,plain,(
    r2_hidden('#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_6'('#skF_7')),k1_relat_1('#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_16677])).

tff(c_16,plain,(
    ! [A_8,C_44] :
      ( r2_hidden('#skF_4'(A_8,k2_relat_1(A_8),C_44),k1_relat_1(A_8))
      | ~ r2_hidden(C_44,k2_relat_1(A_8))
      | ~ v1_funct_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_510,plain,(
    ! [B_132,A_8,C_44] :
      ( B_132 = '#skF_4'(A_8,k2_relat_1(A_8),C_44)
      | k1_funct_1(A_8,B_132) != C_44
      | ~ r2_hidden('#skF_4'(A_8,k2_relat_1(A_8),C_44),k1_relat_1(A_8))
      | ~ r2_hidden(B_132,k1_relat_1(A_8))
      | ~ v2_funct_1(A_8)
      | ~ v1_funct_1(A_8)
      | ~ v1_relat_1(A_8)
      | ~ r2_hidden(C_44,k2_relat_1(A_8))
      | ~ v1_funct_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_500])).

tff(c_16986,plain,(
    ! [A_519,B_520] :
      ( '#skF_4'(A_519,k2_relat_1(A_519),k1_funct_1(A_519,B_520)) = B_520
      | ~ r2_hidden('#skF_4'(A_519,k2_relat_1(A_519),k1_funct_1(A_519,B_520)),k1_relat_1(A_519))
      | ~ r2_hidden(B_520,k1_relat_1(A_519))
      | ~ v2_funct_1(A_519)
      | ~ v1_funct_1(A_519)
      | ~ v1_relat_1(A_519)
      | ~ r2_hidden(k1_funct_1(A_519,B_520),k2_relat_1(A_519))
      | ~ v1_funct_1(A_519)
      | ~ v1_relat_1(A_519) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_510])).

tff(c_17357,plain,(
    ! [A_524,B_525] :
      ( '#skF_4'(A_524,k2_relat_1(A_524),k1_funct_1(A_524,B_525)) = B_525
      | ~ r2_hidden(B_525,k1_relat_1(A_524))
      | ~ v2_funct_1(A_524)
      | ~ r2_hidden(k1_funct_1(A_524,B_525),k2_relat_1(A_524))
      | ~ v1_funct_1(A_524)
      | ~ v1_relat_1(A_524) ) ),
    inference(resolution,[status(thm)],[c_16,c_16986])).

tff(c_17477,plain,(
    ! [A_526,D_527] :
      ( '#skF_4'(A_526,k2_relat_1(A_526),k1_funct_1(A_526,D_527)) = D_527
      | ~ v2_funct_1(A_526)
      | ~ r2_hidden(D_527,k1_relat_1(A_526))
      | ~ v1_funct_1(A_526)
      | ~ v1_relat_1(A_526) ) ),
    inference(resolution,[status(thm)],[c_12,c_17357])).

tff(c_3217,plain,(
    ! [C_280] :
      ( k1_funct_1('#skF_7',k1_funct_1('#skF_8','#skF_4'(k5_relat_1('#skF_8','#skF_7'),k2_relat_1(k5_relat_1('#skF_8','#skF_7')),C_280))) = C_280
      | ~ r2_hidden(C_280,k2_relat_1(k5_relat_1('#skF_8','#skF_7'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_389,c_442,c_3200])).

tff(c_17484,plain,(
    ! [D_527] :
      ( k1_funct_1(k5_relat_1('#skF_8','#skF_7'),D_527) = k1_funct_1('#skF_7',k1_funct_1('#skF_8',D_527))
      | ~ r2_hidden(k1_funct_1(k5_relat_1('#skF_8','#skF_7'),D_527),k2_relat_1(k5_relat_1('#skF_8','#skF_7')))
      | ~ v2_funct_1(k5_relat_1('#skF_8','#skF_7'))
      | ~ r2_hidden(D_527,k1_relat_1(k5_relat_1('#skF_8','#skF_7')))
      | ~ v1_funct_1(k5_relat_1('#skF_8','#skF_7'))
      | ~ v1_relat_1(k5_relat_1('#skF_8','#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_17477,c_3217])).

tff(c_17648,plain,(
    ! [D_528] :
      ( k1_funct_1(k5_relat_1('#skF_8','#skF_7'),D_528) = k1_funct_1('#skF_7',k1_funct_1('#skF_8',D_528))
      | ~ r2_hidden(k1_funct_1(k5_relat_1('#skF_8','#skF_7'),D_528),k2_relat_1(k5_relat_1('#skF_8','#skF_7')))
      | ~ r2_hidden(D_528,k1_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_389,c_442,c_311,c_52,c_17484])).

tff(c_17730,plain,(
    ! [D_47] :
      ( k1_funct_1(k5_relat_1('#skF_8','#skF_7'),D_47) = k1_funct_1('#skF_7',k1_funct_1('#skF_8',D_47))
      | ~ r2_hidden(D_47,k1_relat_1('#skF_8'))
      | ~ r2_hidden(D_47,k1_relat_1(k5_relat_1('#skF_8','#skF_7')))
      | ~ v1_funct_1(k5_relat_1('#skF_8','#skF_7'))
      | ~ v1_relat_1(k5_relat_1('#skF_8','#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_12,c_17648])).

tff(c_17859,plain,(
    ! [D_532] :
      ( k1_funct_1(k5_relat_1('#skF_8','#skF_7'),D_532) = k1_funct_1('#skF_7',k1_funct_1('#skF_8',D_532))
      | ~ r2_hidden(D_532,k1_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_389,c_442,c_311,c_17730])).

tff(c_18007,plain,(
    k1_funct_1(k5_relat_1('#skF_8','#skF_7'),'#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_6'('#skF_7'))) = k1_funct_1('#skF_7',k1_funct_1('#skF_8','#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_6'('#skF_7')))) ),
    inference(resolution,[status(thm)],[c_16976,c_17859])).

tff(c_17474,plain,(
    ! [A_8,D_47] :
      ( '#skF_4'(A_8,k2_relat_1(A_8),k1_funct_1(A_8,D_47)) = D_47
      | ~ v2_funct_1(A_8)
      | ~ r2_hidden(D_47,k1_relat_1(A_8))
      | ~ v1_funct_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(resolution,[status(thm)],[c_12,c_17357])).

tff(c_18253,plain,
    ( '#skF_4'(k5_relat_1('#skF_8','#skF_7'),k2_relat_1(k5_relat_1('#skF_8','#skF_7')),k1_funct_1('#skF_7',k1_funct_1('#skF_8','#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_6'('#skF_7'))))) = '#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_6'('#skF_7'))
    | ~ v2_funct_1(k5_relat_1('#skF_8','#skF_7'))
    | ~ r2_hidden('#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_6'('#skF_7')),k1_relat_1(k5_relat_1('#skF_8','#skF_7')))
    | ~ v1_funct_1(k5_relat_1('#skF_8','#skF_7'))
    | ~ v1_relat_1(k5_relat_1('#skF_8','#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_18007,c_17474])).

tff(c_18286,plain,(
    '#skF_4'(k5_relat_1('#skF_8','#skF_7'),k2_relat_1(k5_relat_1('#skF_8','#skF_7')),k1_funct_1('#skF_7',k1_funct_1('#skF_8','#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_6'('#skF_7'))))) = '#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_6'('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_389,c_442,c_16976,c_311,c_52,c_18253])).

tff(c_19036,plain,
    ( '#skF_4'(k5_relat_1('#skF_8','#skF_7'),k2_relat_1(k5_relat_1('#skF_8','#skF_7')),k1_funct_1('#skF_7','#skF_6'('#skF_7'))) = '#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_6'('#skF_7'))
    | ~ r2_hidden('#skF_6'('#skF_7'),k1_relat_1('#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_352,c_18286])).

tff(c_19055,plain,(
    ~ r2_hidden('#skF_6'('#skF_7'),k1_relat_1('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_19036])).

tff(c_19058,plain,
    ( v2_funct_1('#skF_7')
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_36,c_19055])).

tff(c_19061,plain,(
    v2_funct_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_19058])).

tff(c_19063,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_249,c_19061])).

tff(c_19065,plain,(
    r2_hidden('#skF_6'('#skF_7'),k1_relat_1('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_19036])).

tff(c_19064,plain,(
    '#skF_4'(k5_relat_1('#skF_8','#skF_7'),k2_relat_1(k5_relat_1('#skF_8','#skF_7')),k1_funct_1('#skF_7','#skF_6'('#skF_7'))) = '#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_6'('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_19036])).

tff(c_16514,plain,(
    ! [B_514] :
      ( '#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_5'('#skF_7')) = '#skF_2'('#skF_8',B_514)
      | '#skF_5'('#skF_7') != '#skF_1'('#skF_8',B_514)
      | r2_hidden('#skF_3'('#skF_8',B_514),B_514)
      | k1_relat_1('#skF_7') = B_514
      | v2_funct_1('#skF_7')
      | ~ v1_funct_1('#skF_7')
      | ~ v1_relat_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_38,c_16427])).

tff(c_16574,plain,(
    ! [B_514] :
      ( '#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_5'('#skF_7')) = '#skF_2'('#skF_8',B_514)
      | '#skF_5'('#skF_7') != '#skF_1'('#skF_8',B_514)
      | r2_hidden('#skF_3'('#skF_8',B_514),B_514)
      | k1_relat_1('#skF_7') = B_514
      | v2_funct_1('#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_16514])).

tff(c_16702,plain,(
    ! [B_516] :
      ( '#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_5'('#skF_7')) = '#skF_2'('#skF_8',B_516)
      | '#skF_5'('#skF_7') != '#skF_1'('#skF_8',B_516)
      | r2_hidden('#skF_3'('#skF_8',B_516),B_516)
      | k1_relat_1('#skF_7') = B_516 ) ),
    inference(negUnitSimplification,[status(thm)],[c_249,c_16574])).

tff(c_16749,plain,(
    ! [B_516] :
      ( r2_hidden('#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_5'('#skF_7')),k1_relat_1('#skF_8'))
      | r2_hidden('#skF_3'('#skF_8',B_516),B_516)
      | k2_relat_1('#skF_8') = B_516
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8')
      | '#skF_5'('#skF_7') != '#skF_1'('#skF_8',B_516)
      | r2_hidden('#skF_3'('#skF_8',B_516),B_516)
      | k1_relat_1('#skF_7') = B_516 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16702,c_28])).

tff(c_16818,plain,(
    ! [B_516] :
      ( r2_hidden('#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_5'('#skF_7')),k1_relat_1('#skF_8'))
      | '#skF_5'('#skF_7') != '#skF_1'('#skF_8',B_516)
      | r2_hidden('#skF_3'('#skF_8',B_516),B_516)
      | k1_relat_1('#skF_7') = B_516 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_50,c_16749])).

tff(c_17197,plain,(
    r2_hidden('#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_5'('#skF_7')),k1_relat_1('#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_16818])).

tff(c_18002,plain,(
    k1_funct_1(k5_relat_1('#skF_8','#skF_7'),'#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_5'('#skF_7'))) = k1_funct_1('#skF_7',k1_funct_1('#skF_8','#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_5'('#skF_7')))) ),
    inference(resolution,[status(thm)],[c_17197,c_17859])).

tff(c_18070,plain,
    ( '#skF_4'(k5_relat_1('#skF_8','#skF_7'),k2_relat_1(k5_relat_1('#skF_8','#skF_7')),k1_funct_1('#skF_7',k1_funct_1('#skF_8','#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_5'('#skF_7'))))) = '#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_5'('#skF_7'))
    | ~ v2_funct_1(k5_relat_1('#skF_8','#skF_7'))
    | ~ r2_hidden('#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_5'('#skF_7')),k1_relat_1(k5_relat_1('#skF_8','#skF_7')))
    | ~ v1_funct_1(k5_relat_1('#skF_8','#skF_7'))
    | ~ v1_relat_1(k5_relat_1('#skF_8','#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_18002,c_17474])).

tff(c_18099,plain,(
    '#skF_4'(k5_relat_1('#skF_8','#skF_7'),k2_relat_1(k5_relat_1('#skF_8','#skF_7')),k1_funct_1('#skF_7',k1_funct_1('#skF_8','#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_5'('#skF_7'))))) = '#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_5'('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_389,c_442,c_17197,c_311,c_52,c_18070])).

tff(c_19670,plain,
    ( '#skF_4'(k5_relat_1('#skF_8','#skF_7'),k2_relat_1(k5_relat_1('#skF_8','#skF_7')),k1_funct_1('#skF_7','#skF_5'('#skF_7'))) = '#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_5'('#skF_7'))
    | ~ r2_hidden('#skF_5'('#skF_7'),k1_relat_1('#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_352,c_18099])).

tff(c_19689,plain,(
    '#skF_4'(k5_relat_1('#skF_8','#skF_7'),k2_relat_1(k5_relat_1('#skF_8','#skF_7')),k1_funct_1('#skF_7','#skF_5'('#skF_7'))) = '#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_5'('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11159,c_19670])).

tff(c_19715,plain,
    ( '#skF_4'(k5_relat_1('#skF_8','#skF_7'),k2_relat_1(k5_relat_1('#skF_8','#skF_7')),k1_funct_1('#skF_7','#skF_6'('#skF_7'))) = '#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_5'('#skF_7'))
    | v2_funct_1('#skF_7')
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_19689])).

tff(c_19733,plain,
    ( '#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_5'('#skF_7')) = '#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_6'('#skF_7'))
    | v2_funct_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_19064,c_19715])).

tff(c_19734,plain,(
    '#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_5'('#skF_7')) = '#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_6'('#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_249,c_19733])).

tff(c_19775,plain,
    ( k1_funct_1('#skF_8','#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_6'('#skF_7'))) = '#skF_5'('#skF_7')
    | ~ r2_hidden('#skF_5'('#skF_7'),k1_relat_1('#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_19734,c_352])).

tff(c_19795,plain,(
    k1_funct_1('#skF_8','#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_6'('#skF_7'))) = '#skF_5'('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11159,c_19775])).

tff(c_19852,plain,
    ( '#skF_5'('#skF_7') = '#skF_6'('#skF_7')
    | ~ r2_hidden('#skF_6'('#skF_7'),k1_relat_1('#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_19795,c_352])).

tff(c_19904,plain,(
    '#skF_5'('#skF_7') = '#skF_6'('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_19065,c_19852])).

tff(c_19906,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_269,c_19904])).

tff(c_19908,plain,(
    ~ r2_hidden('#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_5'('#skF_7')),k1_relat_1('#skF_8')) ),
    inference(splitRight,[status(thm)],[c_16818])).

tff(c_19912,plain,(
    ~ r2_hidden('#skF_5'('#skF_7'),k1_relat_1('#skF_7')) ),
    inference(resolution,[status(thm)],[c_378,c_19908])).

tff(c_19916,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_11159,c_19912])).

tff(c_19918,plain,(
    ~ r2_hidden('#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_6'('#skF_7')),k1_relat_1('#skF_8')) ),
    inference(splitRight,[status(thm)],[c_16677])).

tff(c_19923,plain,(
    ~ r2_hidden('#skF_6'('#skF_7'),k1_relat_1('#skF_7')) ),
    inference(resolution,[status(thm)],[c_378,c_19918])).

tff(c_19926,plain,
    ( v2_funct_1('#skF_7')
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_36,c_19923])).

tff(c_19929,plain,(
    v2_funct_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_19926])).

tff(c_19931,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_249,c_19929])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 09:51:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 13.80/5.51  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.88/5.52  
% 13.88/5.52  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.88/5.52  %$ r2_hidden > r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_5 > #skF_4 > #skF_7 > #skF_3 > #skF_8 > #skF_2 > #skF_1 > #skF_6
% 13.88/5.52  
% 13.88/5.52  %Foreground sorts:
% 13.88/5.52  
% 13.88/5.52  
% 13.88/5.52  %Background operators:
% 13.88/5.52  
% 13.88/5.52  
% 13.88/5.52  %Foreground operators:
% 13.88/5.52  tff('#skF_5', type, '#skF_5': $i > $i).
% 13.88/5.52  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 13.88/5.52  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 13.88/5.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 13.88/5.52  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 13.88/5.52  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 13.88/5.52  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 13.88/5.52  tff('#skF_7', type, '#skF_7': $i).
% 13.88/5.52  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 13.88/5.52  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 13.88/5.52  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 13.88/5.52  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 13.88/5.52  tff('#skF_8', type, '#skF_8': $i).
% 13.88/5.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 13.88/5.52  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 13.88/5.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 13.88/5.52  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 13.88/5.52  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 13.88/5.52  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 13.88/5.52  tff('#skF_6', type, '#skF_6': $i > $i).
% 13.88/5.52  
% 14.04/5.55  tff(f_134, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v2_funct_1(k5_relat_1(B, A)) & (k2_relat_1(B) = k1_relat_1(A))) => (v2_funct_1(B) & v2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_funct_1)).
% 14.04/5.55  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 14.04/5.55  tff(f_116, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v2_funct_1(k5_relat_1(B, A)) & r1_tarski(k2_relat_1(B), k1_relat_1(A))) => v2_funct_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_funct_1)).
% 14.04/5.55  tff(f_76, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) <=> (![B, C]: (((r2_hidden(B, k1_relat_1(A)) & r2_hidden(C, k1_relat_1(A))) & (k1_funct_1(A, B) = k1_funct_1(A, C))) => (B = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_funct_1)).
% 14.04/5.55  tff(f_61, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_funct_1)).
% 14.04/5.55  tff(f_101, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(B)) => (k1_funct_1(k5_relat_1(B, C), A) = k1_funct_1(C, k1_funct_1(B, A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_funct_1)).
% 14.04/5.55  tff(f_37, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 14.04/5.55  tff(f_46, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(A), k1_relat_1(B)) => (k1_relat_1(k5_relat_1(A, B)) = k1_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_relat_1)).
% 14.04/5.55  tff(f_88, axiom, (![A, B]: ((((v1_relat_1(A) & v1_funct_1(A)) & v1_relat_1(B)) & v1_funct_1(B)) => (v1_relat_1(k5_relat_1(A, B)) & v1_funct_1(k5_relat_1(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_funct_1)).
% 14.04/5.55  tff(c_60, plain, (v1_relat_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_134])).
% 14.04/5.55  tff(c_58, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_134])).
% 14.04/5.55  tff(c_52, plain, (v2_funct_1(k5_relat_1('#skF_8', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_134])).
% 14.04/5.55  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 14.04/5.55  tff(c_48, plain, (~v2_funct_1('#skF_7') | ~v2_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_134])).
% 14.04/5.55  tff(c_63, plain, (~v2_funct_1('#skF_8')), inference(splitLeft, [status(thm)], [c_48])).
% 14.04/5.55  tff(c_56, plain, (v1_relat_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_134])).
% 14.04/5.55  tff(c_54, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_134])).
% 14.04/5.55  tff(c_50, plain, (k2_relat_1('#skF_8')=k1_relat_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_134])).
% 14.04/5.55  tff(c_223, plain, (![B_92, A_93]: (v2_funct_1(B_92) | ~r1_tarski(k2_relat_1(B_92), k1_relat_1(A_93)) | ~v2_funct_1(k5_relat_1(B_92, A_93)) | ~v1_funct_1(B_92) | ~v1_relat_1(B_92) | ~v1_funct_1(A_93) | ~v1_relat_1(A_93))), inference(cnfTransformation, [status(thm)], [f_116])).
% 14.04/5.55  tff(c_229, plain, (![A_93]: (v2_funct_1('#skF_8') | ~r1_tarski(k1_relat_1('#skF_7'), k1_relat_1(A_93)) | ~v2_funct_1(k5_relat_1('#skF_8', A_93)) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~v1_funct_1(A_93) | ~v1_relat_1(A_93))), inference(superposition, [status(thm), theory('equality')], [c_50, c_223])).
% 14.04/5.55  tff(c_233, plain, (![A_93]: (v2_funct_1('#skF_8') | ~r1_tarski(k1_relat_1('#skF_7'), k1_relat_1(A_93)) | ~v2_funct_1(k5_relat_1('#skF_8', A_93)) | ~v1_funct_1(A_93) | ~v1_relat_1(A_93))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_229])).
% 14.04/5.55  tff(c_235, plain, (![A_94]: (~r1_tarski(k1_relat_1('#skF_7'), k1_relat_1(A_94)) | ~v2_funct_1(k5_relat_1('#skF_8', A_94)) | ~v1_funct_1(A_94) | ~v1_relat_1(A_94))), inference(negUnitSimplification, [status(thm)], [c_63, c_233])).
% 14.04/5.55  tff(c_242, plain, (~v2_funct_1(k5_relat_1('#skF_8', '#skF_7')) | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_6, c_235])).
% 14.04/5.55  tff(c_248, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_52, c_242])).
% 14.04/5.55  tff(c_249, plain, (~v2_funct_1('#skF_7')), inference(splitRight, [status(thm)], [c_48])).
% 14.04/5.55  tff(c_36, plain, (![A_48]: (r2_hidden('#skF_6'(A_48), k1_relat_1(A_48)) | v2_funct_1(A_48) | ~v1_funct_1(A_48) | ~v1_relat_1(A_48))), inference(cnfTransformation, [status(thm)], [f_76])).
% 14.04/5.55  tff(c_370, plain, (![A_114, C_115]: (r2_hidden('#skF_4'(A_114, k2_relat_1(A_114), C_115), k1_relat_1(A_114)) | ~r2_hidden(C_115, k2_relat_1(A_114)) | ~v1_funct_1(A_114) | ~v1_relat_1(A_114))), inference(cnfTransformation, [status(thm)], [f_61])).
% 14.04/5.55  tff(c_376, plain, (![C_115]: (r2_hidden('#skF_4'('#skF_8', k1_relat_1('#skF_7'), C_115), k1_relat_1('#skF_8')) | ~r2_hidden(C_115, k2_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_50, c_370])).
% 14.04/5.55  tff(c_378, plain, (![C_115]: (r2_hidden('#skF_4'('#skF_8', k1_relat_1('#skF_7'), C_115), k1_relat_1('#skF_8')) | ~r2_hidden(C_115, k1_relat_1('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_50, c_376])).
% 14.04/5.55  tff(c_38, plain, (![A_48]: (r2_hidden('#skF_5'(A_48), k1_relat_1(A_48)) | v2_funct_1(A_48) | ~v1_funct_1(A_48) | ~v1_relat_1(A_48))), inference(cnfTransformation, [status(thm)], [f_76])).
% 14.04/5.55  tff(c_34, plain, (![A_48]: (k1_funct_1(A_48, '#skF_5'(A_48))=k1_funct_1(A_48, '#skF_6'(A_48)) | v2_funct_1(A_48) | ~v1_funct_1(A_48) | ~v1_relat_1(A_48))), inference(cnfTransformation, [status(thm)], [f_76])).
% 14.04/5.55  tff(c_330, plain, (![A_111, C_112]: (k1_funct_1(A_111, '#skF_4'(A_111, k2_relat_1(A_111), C_112))=C_112 | ~r2_hidden(C_112, k2_relat_1(A_111)) | ~v1_funct_1(A_111) | ~v1_relat_1(A_111))), inference(cnfTransformation, [status(thm)], [f_61])).
% 14.04/5.55  tff(c_346, plain, (![C_112]: (k1_funct_1('#skF_8', '#skF_4'('#skF_8', k1_relat_1('#skF_7'), C_112))=C_112 | ~r2_hidden(C_112, k2_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_50, c_330])).
% 14.04/5.55  tff(c_352, plain, (![C_112]: (k1_funct_1('#skF_8', '#skF_4'('#skF_8', k1_relat_1('#skF_7'), C_112))=C_112 | ~r2_hidden(C_112, k1_relat_1('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_50, c_346])).
% 14.04/5.55  tff(c_452, plain, (![B_128, C_129, A_130]: (k1_funct_1(k5_relat_1(B_128, C_129), A_130)=k1_funct_1(C_129, k1_funct_1(B_128, A_130)) | ~r2_hidden(A_130, k1_relat_1(B_128)) | ~v1_funct_1(C_129) | ~v1_relat_1(C_129) | ~v1_funct_1(B_128) | ~v1_relat_1(B_128))), inference(cnfTransformation, [status(thm)], [f_101])).
% 14.04/5.55  tff(c_467, plain, (![C_129, C_115]: (k1_funct_1(k5_relat_1('#skF_8', C_129), '#skF_4'('#skF_8', k1_relat_1('#skF_7'), C_115))=k1_funct_1(C_129, k1_funct_1('#skF_8', '#skF_4'('#skF_8', k1_relat_1('#skF_7'), C_115))) | ~v1_funct_1(C_129) | ~v1_relat_1(C_129) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~r2_hidden(C_115, k1_relat_1('#skF_7')))), inference(resolution, [status(thm)], [c_378, c_452])).
% 14.04/5.55  tff(c_487, plain, (![C_129, C_115]: (k1_funct_1(k5_relat_1('#skF_8', C_129), '#skF_4'('#skF_8', k1_relat_1('#skF_7'), C_115))=k1_funct_1(C_129, k1_funct_1('#skF_8', '#skF_4'('#skF_8', k1_relat_1('#skF_7'), C_115))) | ~v1_funct_1(C_129) | ~v1_relat_1(C_129) | ~r2_hidden(C_115, k1_relat_1('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_467])).
% 14.04/5.55  tff(c_8, plain, (![A_3, B_4]: (v1_relat_1(k5_relat_1(A_3, B_4)) | ~v1_relat_1(B_4) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_37])).
% 14.04/5.55  tff(c_298, plain, (![A_108, B_109]: (k1_relat_1(k5_relat_1(A_108, B_109))=k1_relat_1(A_108) | ~r1_tarski(k2_relat_1(A_108), k1_relat_1(B_109)) | ~v1_relat_1(B_109) | ~v1_relat_1(A_108))), inference(cnfTransformation, [status(thm)], [f_46])).
% 14.04/5.55  tff(c_301, plain, (![B_109]: (k1_relat_1(k5_relat_1('#skF_8', B_109))=k1_relat_1('#skF_8') | ~r1_tarski(k1_relat_1('#skF_7'), k1_relat_1(B_109)) | ~v1_relat_1(B_109) | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_50, c_298])).
% 14.04/5.55  tff(c_304, plain, (![B_110]: (k1_relat_1(k5_relat_1('#skF_8', B_110))=k1_relat_1('#skF_8') | ~r1_tarski(k1_relat_1('#skF_7'), k1_relat_1(B_110)) | ~v1_relat_1(B_110))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_301])).
% 14.04/5.55  tff(c_308, plain, (k1_relat_1(k5_relat_1('#skF_8', '#skF_7'))=k1_relat_1('#skF_8') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_6, c_304])).
% 14.04/5.55  tff(c_311, plain, (k1_relat_1(k5_relat_1('#skF_8', '#skF_7'))=k1_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_308])).
% 14.04/5.55  tff(c_303, plain, (![B_109]: (k1_relat_1(k5_relat_1('#skF_8', B_109))=k1_relat_1('#skF_8') | ~r1_tarski(k1_relat_1('#skF_7'), k1_relat_1(B_109)) | ~v1_relat_1(B_109))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_301])).
% 14.04/5.55  tff(c_315, plain, (k1_relat_1(k5_relat_1('#skF_8', k5_relat_1('#skF_8', '#skF_7')))=k1_relat_1('#skF_8') | ~r1_tarski(k1_relat_1('#skF_7'), k1_relat_1('#skF_8')) | ~v1_relat_1(k5_relat_1('#skF_8', '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_311, c_303])).
% 14.04/5.55  tff(c_380, plain, (~v1_relat_1(k5_relat_1('#skF_8', '#skF_7'))), inference(splitLeft, [status(thm)], [c_315])).
% 14.04/5.55  tff(c_383, plain, (~v1_relat_1('#skF_7') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_8, c_380])).
% 14.04/5.55  tff(c_387, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_60, c_383])).
% 14.04/5.55  tff(c_389, plain, (v1_relat_1(k5_relat_1('#skF_8', '#skF_7'))), inference(splitRight, [status(thm)], [c_315])).
% 14.04/5.55  tff(c_40, plain, (![A_55, B_56]: (v1_funct_1(k5_relat_1(A_55, B_56)) | ~v1_funct_1(B_56) | ~v1_relat_1(B_56) | ~v1_funct_1(A_55) | ~v1_relat_1(A_55))), inference(cnfTransformation, [status(thm)], [f_88])).
% 14.04/5.55  tff(c_373, plain, (![C_115]: (r2_hidden('#skF_4'(k5_relat_1('#skF_8', '#skF_7'), k2_relat_1(k5_relat_1('#skF_8', '#skF_7')), C_115), k1_relat_1('#skF_8')) | ~r2_hidden(C_115, k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))) | ~v1_funct_1(k5_relat_1('#skF_8', '#skF_7')) | ~v1_relat_1(k5_relat_1('#skF_8', '#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_311, c_370])).
% 14.04/5.55  tff(c_432, plain, (![C_115]: (r2_hidden('#skF_4'(k5_relat_1('#skF_8', '#skF_7'), k2_relat_1(k5_relat_1('#skF_8', '#skF_7')), C_115), k1_relat_1('#skF_8')) | ~r2_hidden(C_115, k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))) | ~v1_funct_1(k5_relat_1('#skF_8', '#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_389, c_373])).
% 14.04/5.55  tff(c_433, plain, (~v1_funct_1(k5_relat_1('#skF_8', '#skF_7'))), inference(splitLeft, [status(thm)], [c_432])).
% 14.04/5.55  tff(c_436, plain, (~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7') | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_40, c_433])).
% 14.04/5.55  tff(c_440, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_60, c_58, c_436])).
% 14.04/5.55  tff(c_442, plain, (v1_funct_1(k5_relat_1('#skF_8', '#skF_7'))), inference(splitRight, [status(thm)], [c_432])).
% 14.04/5.55  tff(c_12, plain, (![A_8, D_47]: (r2_hidden(k1_funct_1(A_8, D_47), k2_relat_1(A_8)) | ~r2_hidden(D_47, k1_relat_1(A_8)) | ~v1_funct_1(A_8) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_61])).
% 14.04/5.55  tff(c_441, plain, (![C_115]: (r2_hidden('#skF_4'(k5_relat_1('#skF_8', '#skF_7'), k2_relat_1(k5_relat_1('#skF_8', '#skF_7')), C_115), k1_relat_1('#skF_8')) | ~r2_hidden(C_115, k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))))), inference(splitRight, [status(thm)], [c_432])).
% 14.04/5.55  tff(c_282, plain, (![A_105, D_106]: (r2_hidden(k1_funct_1(A_105, D_106), k2_relat_1(A_105)) | ~r2_hidden(D_106, k1_relat_1(A_105)) | ~v1_funct_1(A_105) | ~v1_relat_1(A_105))), inference(cnfTransformation, [status(thm)], [f_61])).
% 14.04/5.55  tff(c_288, plain, (![D_106]: (r2_hidden(k1_funct_1('#skF_8', D_106), k1_relat_1('#skF_7')) | ~r2_hidden(D_106, k1_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_50, c_282])).
% 14.04/5.55  tff(c_290, plain, (![D_106]: (r2_hidden(k1_funct_1('#skF_8', D_106), k1_relat_1('#skF_7')) | ~r2_hidden(D_106, k1_relat_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_288])).
% 14.04/5.55  tff(c_454, plain, (![C_129, C_115]: (k1_funct_1(k5_relat_1('#skF_8', C_129), '#skF_4'(k5_relat_1('#skF_8', '#skF_7'), k2_relat_1(k5_relat_1('#skF_8', '#skF_7')), C_115))=k1_funct_1(C_129, k1_funct_1('#skF_8', '#skF_4'(k5_relat_1('#skF_8', '#skF_7'), k2_relat_1(k5_relat_1('#skF_8', '#skF_7')), C_115))) | ~v1_funct_1(C_129) | ~v1_relat_1(C_129) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~r2_hidden(C_115, k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))))), inference(resolution, [status(thm)], [c_441, c_452])).
% 14.04/5.55  tff(c_3175, plain, (![C_279, C_280]: (k1_funct_1(k5_relat_1('#skF_8', C_279), '#skF_4'(k5_relat_1('#skF_8', '#skF_7'), k2_relat_1(k5_relat_1('#skF_8', '#skF_7')), C_280))=k1_funct_1(C_279, k1_funct_1('#skF_8', '#skF_4'(k5_relat_1('#skF_8', '#skF_7'), k2_relat_1(k5_relat_1('#skF_8', '#skF_7')), C_280))) | ~v1_funct_1(C_279) | ~v1_relat_1(C_279) | ~r2_hidden(C_280, k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_454])).
% 14.04/5.55  tff(c_14, plain, (![A_8, C_44]: (k1_funct_1(A_8, '#skF_4'(A_8, k2_relat_1(A_8), C_44))=C_44 | ~r2_hidden(C_44, k2_relat_1(A_8)) | ~v1_funct_1(A_8) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_61])).
% 14.04/5.55  tff(c_3200, plain, (![C_280]: (k1_funct_1('#skF_7', k1_funct_1('#skF_8', '#skF_4'(k5_relat_1('#skF_8', '#skF_7'), k2_relat_1(k5_relat_1('#skF_8', '#skF_7')), C_280)))=C_280 | ~r2_hidden(C_280, k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))) | ~v1_funct_1(k5_relat_1('#skF_8', '#skF_7')) | ~v1_relat_1(k5_relat_1('#skF_8', '#skF_7')) | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7') | ~r2_hidden(C_280, k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))))), inference(superposition, [status(thm), theory('equality')], [c_3175, c_14])).
% 14.04/5.55  tff(c_3221, plain, (![C_281]: (k1_funct_1('#skF_7', k1_funct_1('#skF_8', '#skF_4'(k5_relat_1('#skF_8', '#skF_7'), k2_relat_1(k5_relat_1('#skF_8', '#skF_7')), C_281)))=C_281 | ~r2_hidden(C_281, k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_389, c_442, c_3200])).
% 14.04/5.55  tff(c_3240, plain, (![C_281]: (r2_hidden(C_281, k2_relat_1('#skF_7')) | ~r2_hidden(k1_funct_1('#skF_8', '#skF_4'(k5_relat_1('#skF_8', '#skF_7'), k2_relat_1(k5_relat_1('#skF_8', '#skF_7')), C_281)), k1_relat_1('#skF_7')) | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7') | ~r2_hidden(C_281, k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))))), inference(superposition, [status(thm), theory('equality')], [c_3221, c_12])).
% 14.04/5.55  tff(c_3259, plain, (![C_282]: (r2_hidden(C_282, k2_relat_1('#skF_7')) | ~r2_hidden(k1_funct_1('#skF_8', '#skF_4'(k5_relat_1('#skF_8', '#skF_7'), k2_relat_1(k5_relat_1('#skF_8', '#skF_7')), C_282)), k1_relat_1('#skF_7')) | ~r2_hidden(C_282, k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_3240])).
% 14.04/5.55  tff(c_3335, plain, (![C_286]: (r2_hidden(C_286, k2_relat_1('#skF_7')) | ~r2_hidden(C_286, k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))) | ~r2_hidden('#skF_4'(k5_relat_1('#skF_8', '#skF_7'), k2_relat_1(k5_relat_1('#skF_8', '#skF_7')), C_286), k1_relat_1('#skF_8')))), inference(resolution, [status(thm)], [c_290, c_3259])).
% 14.04/5.55  tff(c_3340, plain, (![C_287]: (r2_hidden(C_287, k2_relat_1('#skF_7')) | ~r2_hidden(C_287, k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))))), inference(resolution, [status(thm)], [c_441, c_3335])).
% 14.04/5.55  tff(c_3431, plain, (![D_47]: (r2_hidden(k1_funct_1(k5_relat_1('#skF_8', '#skF_7'), D_47), k2_relat_1('#skF_7')) | ~r2_hidden(D_47, k1_relat_1(k5_relat_1('#skF_8', '#skF_7'))) | ~v1_funct_1(k5_relat_1('#skF_8', '#skF_7')) | ~v1_relat_1(k5_relat_1('#skF_8', '#skF_7')))), inference(resolution, [status(thm)], [c_12, c_3340])).
% 14.04/5.55  tff(c_3476, plain, (![D_288]: (r2_hidden(k1_funct_1(k5_relat_1('#skF_8', '#skF_7'), D_288), k2_relat_1('#skF_7')) | ~r2_hidden(D_288, k1_relat_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_389, c_442, c_311, c_3431])).
% 14.04/5.55  tff(c_3518, plain, (![C_115]: (r2_hidden(k1_funct_1('#skF_7', k1_funct_1('#skF_8', '#skF_4'('#skF_8', k1_relat_1('#skF_7'), C_115))), k2_relat_1('#skF_7')) | ~r2_hidden('#skF_4'('#skF_8', k1_relat_1('#skF_7'), C_115), k1_relat_1('#skF_8')) | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7') | ~r2_hidden(C_115, k1_relat_1('#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_487, c_3476])).
% 14.04/5.55  tff(c_11087, plain, (![C_407]: (r2_hidden(k1_funct_1('#skF_7', k1_funct_1('#skF_8', '#skF_4'('#skF_8', k1_relat_1('#skF_7'), C_407))), k2_relat_1('#skF_7')) | ~r2_hidden('#skF_4'('#skF_8', k1_relat_1('#skF_7'), C_407), k1_relat_1('#skF_8')) | ~r2_hidden(C_407, k1_relat_1('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_3518])).
% 14.04/5.55  tff(c_11100, plain, (![C_408]: (r2_hidden(k1_funct_1('#skF_7', C_408), k2_relat_1('#skF_7')) | ~r2_hidden('#skF_4'('#skF_8', k1_relat_1('#skF_7'), C_408), k1_relat_1('#skF_8')) | ~r2_hidden(C_408, k1_relat_1('#skF_7')) | ~r2_hidden(C_408, k1_relat_1('#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_352, c_11087])).
% 14.04/5.55  tff(c_11108, plain, (![C_409]: (r2_hidden(k1_funct_1('#skF_7', C_409), k2_relat_1('#skF_7')) | ~r2_hidden(C_409, k1_relat_1('#skF_7')))), inference(resolution, [status(thm)], [c_378, c_11100])).
% 14.04/5.55  tff(c_11136, plain, (r2_hidden(k1_funct_1('#skF_7', '#skF_6'('#skF_7')), k2_relat_1('#skF_7')) | ~r2_hidden('#skF_5'('#skF_7'), k1_relat_1('#skF_7')) | v2_funct_1('#skF_7') | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_34, c_11108])).
% 14.04/5.55  tff(c_11147, plain, (r2_hidden(k1_funct_1('#skF_7', '#skF_6'('#skF_7')), k2_relat_1('#skF_7')) | ~r2_hidden('#skF_5'('#skF_7'), k1_relat_1('#skF_7')) | v2_funct_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_11136])).
% 14.04/5.55  tff(c_11148, plain, (r2_hidden(k1_funct_1('#skF_7', '#skF_6'('#skF_7')), k2_relat_1('#skF_7')) | ~r2_hidden('#skF_5'('#skF_7'), k1_relat_1('#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_249, c_11147])).
% 14.04/5.55  tff(c_11149, plain, (~r2_hidden('#skF_5'('#skF_7'), k1_relat_1('#skF_7'))), inference(splitLeft, [status(thm)], [c_11148])).
% 14.04/5.55  tff(c_11152, plain, (v2_funct_1('#skF_7') | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_38, c_11149])).
% 14.04/5.55  tff(c_11155, plain, (v2_funct_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_11152])).
% 14.04/5.55  tff(c_11157, plain, $false, inference(negUnitSimplification, [status(thm)], [c_249, c_11155])).
% 14.04/5.55  tff(c_11159, plain, (r2_hidden('#skF_5'('#skF_7'), k1_relat_1('#skF_7'))), inference(splitRight, [status(thm)], [c_11148])).
% 14.04/5.55  tff(c_263, plain, (![A_99]: ('#skF_5'(A_99)!='#skF_6'(A_99) | v2_funct_1(A_99) | ~v1_funct_1(A_99) | ~v1_relat_1(A_99))), inference(cnfTransformation, [status(thm)], [f_76])).
% 14.04/5.55  tff(c_266, plain, ('#skF_5'('#skF_7')!='#skF_6'('#skF_7') | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_263, c_249])).
% 14.04/5.55  tff(c_269, plain, ('#skF_5'('#skF_7')!='#skF_6'('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_266])).
% 14.04/5.55  tff(c_28, plain, (![A_8, B_30]: (r2_hidden('#skF_2'(A_8, B_30), k1_relat_1(A_8)) | r2_hidden('#skF_3'(A_8, B_30), B_30) | k2_relat_1(A_8)=B_30 | ~v1_funct_1(A_8) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_61])).
% 14.04/5.55  tff(c_250, plain, (v2_funct_1('#skF_8')), inference(splitRight, [status(thm)], [c_48])).
% 14.04/5.55  tff(c_26, plain, (![A_8, B_30]: (k1_funct_1(A_8, '#skF_2'(A_8, B_30))='#skF_1'(A_8, B_30) | r2_hidden('#skF_3'(A_8, B_30), B_30) | k2_relat_1(A_8)=B_30 | ~v1_funct_1(A_8) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_61])).
% 14.04/5.55  tff(c_500, plain, (![C_131, B_132, A_133]: (C_131=B_132 | k1_funct_1(A_133, C_131)!=k1_funct_1(A_133, B_132) | ~r2_hidden(C_131, k1_relat_1(A_133)) | ~r2_hidden(B_132, k1_relat_1(A_133)) | ~v2_funct_1(A_133) | ~v1_funct_1(A_133) | ~v1_relat_1(A_133))), inference(cnfTransformation, [status(thm)], [f_76])).
% 14.04/5.55  tff(c_3264, plain, (![C_283, A_284, B_285]: (C_283='#skF_2'(A_284, B_285) | k1_funct_1(A_284, C_283)!='#skF_1'(A_284, B_285) | ~r2_hidden(C_283, k1_relat_1(A_284)) | ~r2_hidden('#skF_2'(A_284, B_285), k1_relat_1(A_284)) | ~v2_funct_1(A_284) | ~v1_funct_1(A_284) | ~v1_relat_1(A_284) | r2_hidden('#skF_3'(A_284, B_285), B_285) | k2_relat_1(A_284)=B_285 | ~v1_funct_1(A_284) | ~v1_relat_1(A_284))), inference(superposition, [status(thm), theory('equality')], [c_26, c_500])).
% 14.04/5.55  tff(c_3324, plain, (![C_112, B_285]: ('#skF_4'('#skF_8', k1_relat_1('#skF_7'), C_112)='#skF_2'('#skF_8', B_285) | C_112!='#skF_1'('#skF_8', B_285) | ~r2_hidden('#skF_4'('#skF_8', k1_relat_1('#skF_7'), C_112), k1_relat_1('#skF_8')) | ~r2_hidden('#skF_2'('#skF_8', B_285), k1_relat_1('#skF_8')) | ~v2_funct_1('#skF_8') | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | r2_hidden('#skF_3'('#skF_8', B_285), B_285) | k2_relat_1('#skF_8')=B_285 | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~r2_hidden(C_112, k1_relat_1('#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_352, c_3264])).
% 14.04/5.55  tff(c_16301, plain, (![C_508, B_509]: ('#skF_4'('#skF_8', k1_relat_1('#skF_7'), C_508)='#skF_2'('#skF_8', B_509) | C_508!='#skF_1'('#skF_8', B_509) | ~r2_hidden('#skF_4'('#skF_8', k1_relat_1('#skF_7'), C_508), k1_relat_1('#skF_8')) | ~r2_hidden('#skF_2'('#skF_8', B_509), k1_relat_1('#skF_8')) | r2_hidden('#skF_3'('#skF_8', B_509), B_509) | k1_relat_1('#skF_7')=B_509 | ~r2_hidden(C_508, k1_relat_1('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_50, c_56, c_54, c_250, c_3324])).
% 14.04/5.55  tff(c_16392, plain, (![C_511, B_512]: ('#skF_4'('#skF_8', k1_relat_1('#skF_7'), C_511)='#skF_2'('#skF_8', B_512) | C_511!='#skF_1'('#skF_8', B_512) | ~r2_hidden('#skF_2'('#skF_8', B_512), k1_relat_1('#skF_8')) | r2_hidden('#skF_3'('#skF_8', B_512), B_512) | k1_relat_1('#skF_7')=B_512 | ~r2_hidden(C_511, k1_relat_1('#skF_7')))), inference(resolution, [status(thm)], [c_378, c_16301])).
% 14.04/5.55  tff(c_16408, plain, (![C_511, B_30]: ('#skF_4'('#skF_8', k1_relat_1('#skF_7'), C_511)='#skF_2'('#skF_8', B_30) | C_511!='#skF_1'('#skF_8', B_30) | k1_relat_1('#skF_7')=B_30 | ~r2_hidden(C_511, k1_relat_1('#skF_7')) | r2_hidden('#skF_3'('#skF_8', B_30), B_30) | k2_relat_1('#skF_8')=B_30 | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_28, c_16392])).
% 14.04/5.55  tff(c_16427, plain, (![C_513, B_514]: ('#skF_4'('#skF_8', k1_relat_1('#skF_7'), C_513)='#skF_2'('#skF_8', B_514) | C_513!='#skF_1'('#skF_8', B_514) | ~r2_hidden(C_513, k1_relat_1('#skF_7')) | r2_hidden('#skF_3'('#skF_8', B_514), B_514) | k1_relat_1('#skF_7')=B_514)), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_50, c_16408])).
% 14.04/5.55  tff(c_16511, plain, (![B_514]: ('#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_6'('#skF_7'))='#skF_2'('#skF_8', B_514) | '#skF_1'('#skF_8', B_514)!='#skF_6'('#skF_7') | r2_hidden('#skF_3'('#skF_8', B_514), B_514) | k1_relat_1('#skF_7')=B_514 | v2_funct_1('#skF_7') | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7'))), inference(resolution, [status(thm)], [c_36, c_16427])).
% 14.04/5.55  tff(c_16570, plain, (![B_514]: ('#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_6'('#skF_7'))='#skF_2'('#skF_8', B_514) | '#skF_1'('#skF_8', B_514)!='#skF_6'('#skF_7') | r2_hidden('#skF_3'('#skF_8', B_514), B_514) | k1_relat_1('#skF_7')=B_514 | v2_funct_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_16511])).
% 14.04/5.55  tff(c_16577, plain, (![B_515]: ('#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_6'('#skF_7'))='#skF_2'('#skF_8', B_515) | '#skF_1'('#skF_8', B_515)!='#skF_6'('#skF_7') | r2_hidden('#skF_3'('#skF_8', B_515), B_515) | k1_relat_1('#skF_7')=B_515)), inference(negUnitSimplification, [status(thm)], [c_249, c_16570])).
% 14.04/5.55  tff(c_16621, plain, (![B_515]: (r2_hidden('#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_6'('#skF_7')), k1_relat_1('#skF_8')) | r2_hidden('#skF_3'('#skF_8', B_515), B_515) | k2_relat_1('#skF_8')=B_515 | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | '#skF_1'('#skF_8', B_515)!='#skF_6'('#skF_7') | r2_hidden('#skF_3'('#skF_8', B_515), B_515) | k1_relat_1('#skF_7')=B_515)), inference(superposition, [status(thm), theory('equality')], [c_16577, c_28])).
% 14.04/5.55  tff(c_16677, plain, (![B_515]: (r2_hidden('#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_6'('#skF_7')), k1_relat_1('#skF_8')) | '#skF_1'('#skF_8', B_515)!='#skF_6'('#skF_7') | r2_hidden('#skF_3'('#skF_8', B_515), B_515) | k1_relat_1('#skF_7')=B_515)), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_50, c_16621])).
% 14.04/5.55  tff(c_16976, plain, (r2_hidden('#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_6'('#skF_7')), k1_relat_1('#skF_8'))), inference(splitLeft, [status(thm)], [c_16677])).
% 14.04/5.55  tff(c_16, plain, (![A_8, C_44]: (r2_hidden('#skF_4'(A_8, k2_relat_1(A_8), C_44), k1_relat_1(A_8)) | ~r2_hidden(C_44, k2_relat_1(A_8)) | ~v1_funct_1(A_8) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_61])).
% 14.04/5.55  tff(c_510, plain, (![B_132, A_8, C_44]: (B_132='#skF_4'(A_8, k2_relat_1(A_8), C_44) | k1_funct_1(A_8, B_132)!=C_44 | ~r2_hidden('#skF_4'(A_8, k2_relat_1(A_8), C_44), k1_relat_1(A_8)) | ~r2_hidden(B_132, k1_relat_1(A_8)) | ~v2_funct_1(A_8) | ~v1_funct_1(A_8) | ~v1_relat_1(A_8) | ~r2_hidden(C_44, k2_relat_1(A_8)) | ~v1_funct_1(A_8) | ~v1_relat_1(A_8))), inference(superposition, [status(thm), theory('equality')], [c_14, c_500])).
% 14.04/5.55  tff(c_16986, plain, (![A_519, B_520]: ('#skF_4'(A_519, k2_relat_1(A_519), k1_funct_1(A_519, B_520))=B_520 | ~r2_hidden('#skF_4'(A_519, k2_relat_1(A_519), k1_funct_1(A_519, B_520)), k1_relat_1(A_519)) | ~r2_hidden(B_520, k1_relat_1(A_519)) | ~v2_funct_1(A_519) | ~v1_funct_1(A_519) | ~v1_relat_1(A_519) | ~r2_hidden(k1_funct_1(A_519, B_520), k2_relat_1(A_519)) | ~v1_funct_1(A_519) | ~v1_relat_1(A_519))), inference(reflexivity, [status(thm), theory('equality')], [c_510])).
% 14.04/5.55  tff(c_17357, plain, (![A_524, B_525]: ('#skF_4'(A_524, k2_relat_1(A_524), k1_funct_1(A_524, B_525))=B_525 | ~r2_hidden(B_525, k1_relat_1(A_524)) | ~v2_funct_1(A_524) | ~r2_hidden(k1_funct_1(A_524, B_525), k2_relat_1(A_524)) | ~v1_funct_1(A_524) | ~v1_relat_1(A_524))), inference(resolution, [status(thm)], [c_16, c_16986])).
% 14.04/5.55  tff(c_17477, plain, (![A_526, D_527]: ('#skF_4'(A_526, k2_relat_1(A_526), k1_funct_1(A_526, D_527))=D_527 | ~v2_funct_1(A_526) | ~r2_hidden(D_527, k1_relat_1(A_526)) | ~v1_funct_1(A_526) | ~v1_relat_1(A_526))), inference(resolution, [status(thm)], [c_12, c_17357])).
% 14.04/5.55  tff(c_3217, plain, (![C_280]: (k1_funct_1('#skF_7', k1_funct_1('#skF_8', '#skF_4'(k5_relat_1('#skF_8', '#skF_7'), k2_relat_1(k5_relat_1('#skF_8', '#skF_7')), C_280)))=C_280 | ~r2_hidden(C_280, k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_389, c_442, c_3200])).
% 14.04/5.55  tff(c_17484, plain, (![D_527]: (k1_funct_1(k5_relat_1('#skF_8', '#skF_7'), D_527)=k1_funct_1('#skF_7', k1_funct_1('#skF_8', D_527)) | ~r2_hidden(k1_funct_1(k5_relat_1('#skF_8', '#skF_7'), D_527), k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))) | ~v2_funct_1(k5_relat_1('#skF_8', '#skF_7')) | ~r2_hidden(D_527, k1_relat_1(k5_relat_1('#skF_8', '#skF_7'))) | ~v1_funct_1(k5_relat_1('#skF_8', '#skF_7')) | ~v1_relat_1(k5_relat_1('#skF_8', '#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_17477, c_3217])).
% 14.04/5.55  tff(c_17648, plain, (![D_528]: (k1_funct_1(k5_relat_1('#skF_8', '#skF_7'), D_528)=k1_funct_1('#skF_7', k1_funct_1('#skF_8', D_528)) | ~r2_hidden(k1_funct_1(k5_relat_1('#skF_8', '#skF_7'), D_528), k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))) | ~r2_hidden(D_528, k1_relat_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_389, c_442, c_311, c_52, c_17484])).
% 14.04/5.55  tff(c_17730, plain, (![D_47]: (k1_funct_1(k5_relat_1('#skF_8', '#skF_7'), D_47)=k1_funct_1('#skF_7', k1_funct_1('#skF_8', D_47)) | ~r2_hidden(D_47, k1_relat_1('#skF_8')) | ~r2_hidden(D_47, k1_relat_1(k5_relat_1('#skF_8', '#skF_7'))) | ~v1_funct_1(k5_relat_1('#skF_8', '#skF_7')) | ~v1_relat_1(k5_relat_1('#skF_8', '#skF_7')))), inference(resolution, [status(thm)], [c_12, c_17648])).
% 14.04/5.55  tff(c_17859, plain, (![D_532]: (k1_funct_1(k5_relat_1('#skF_8', '#skF_7'), D_532)=k1_funct_1('#skF_7', k1_funct_1('#skF_8', D_532)) | ~r2_hidden(D_532, k1_relat_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_389, c_442, c_311, c_17730])).
% 14.04/5.55  tff(c_18007, plain, (k1_funct_1(k5_relat_1('#skF_8', '#skF_7'), '#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_6'('#skF_7')))=k1_funct_1('#skF_7', k1_funct_1('#skF_8', '#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_6'('#skF_7'))))), inference(resolution, [status(thm)], [c_16976, c_17859])).
% 14.04/5.55  tff(c_17474, plain, (![A_8, D_47]: ('#skF_4'(A_8, k2_relat_1(A_8), k1_funct_1(A_8, D_47))=D_47 | ~v2_funct_1(A_8) | ~r2_hidden(D_47, k1_relat_1(A_8)) | ~v1_funct_1(A_8) | ~v1_relat_1(A_8))), inference(resolution, [status(thm)], [c_12, c_17357])).
% 14.04/5.55  tff(c_18253, plain, ('#skF_4'(k5_relat_1('#skF_8', '#skF_7'), k2_relat_1(k5_relat_1('#skF_8', '#skF_7')), k1_funct_1('#skF_7', k1_funct_1('#skF_8', '#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_6'('#skF_7')))))='#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_6'('#skF_7')) | ~v2_funct_1(k5_relat_1('#skF_8', '#skF_7')) | ~r2_hidden('#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_6'('#skF_7')), k1_relat_1(k5_relat_1('#skF_8', '#skF_7'))) | ~v1_funct_1(k5_relat_1('#skF_8', '#skF_7')) | ~v1_relat_1(k5_relat_1('#skF_8', '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_18007, c_17474])).
% 14.04/5.55  tff(c_18286, plain, ('#skF_4'(k5_relat_1('#skF_8', '#skF_7'), k2_relat_1(k5_relat_1('#skF_8', '#skF_7')), k1_funct_1('#skF_7', k1_funct_1('#skF_8', '#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_6'('#skF_7')))))='#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_6'('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_389, c_442, c_16976, c_311, c_52, c_18253])).
% 14.04/5.55  tff(c_19036, plain, ('#skF_4'(k5_relat_1('#skF_8', '#skF_7'), k2_relat_1(k5_relat_1('#skF_8', '#skF_7')), k1_funct_1('#skF_7', '#skF_6'('#skF_7')))='#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_6'('#skF_7')) | ~r2_hidden('#skF_6'('#skF_7'), k1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_352, c_18286])).
% 14.04/5.55  tff(c_19055, plain, (~r2_hidden('#skF_6'('#skF_7'), k1_relat_1('#skF_7'))), inference(splitLeft, [status(thm)], [c_19036])).
% 14.04/5.55  tff(c_19058, plain, (v2_funct_1('#skF_7') | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_36, c_19055])).
% 14.04/5.55  tff(c_19061, plain, (v2_funct_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_19058])).
% 14.04/5.55  tff(c_19063, plain, $false, inference(negUnitSimplification, [status(thm)], [c_249, c_19061])).
% 14.04/5.55  tff(c_19065, plain, (r2_hidden('#skF_6'('#skF_7'), k1_relat_1('#skF_7'))), inference(splitRight, [status(thm)], [c_19036])).
% 14.04/5.55  tff(c_19064, plain, ('#skF_4'(k5_relat_1('#skF_8', '#skF_7'), k2_relat_1(k5_relat_1('#skF_8', '#skF_7')), k1_funct_1('#skF_7', '#skF_6'('#skF_7')))='#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_6'('#skF_7'))), inference(splitRight, [status(thm)], [c_19036])).
% 14.04/5.55  tff(c_16514, plain, (![B_514]: ('#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_5'('#skF_7'))='#skF_2'('#skF_8', B_514) | '#skF_5'('#skF_7')!='#skF_1'('#skF_8', B_514) | r2_hidden('#skF_3'('#skF_8', B_514), B_514) | k1_relat_1('#skF_7')=B_514 | v2_funct_1('#skF_7') | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7'))), inference(resolution, [status(thm)], [c_38, c_16427])).
% 14.04/5.55  tff(c_16574, plain, (![B_514]: ('#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_5'('#skF_7'))='#skF_2'('#skF_8', B_514) | '#skF_5'('#skF_7')!='#skF_1'('#skF_8', B_514) | r2_hidden('#skF_3'('#skF_8', B_514), B_514) | k1_relat_1('#skF_7')=B_514 | v2_funct_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_16514])).
% 14.04/5.55  tff(c_16702, plain, (![B_516]: ('#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_5'('#skF_7'))='#skF_2'('#skF_8', B_516) | '#skF_5'('#skF_7')!='#skF_1'('#skF_8', B_516) | r2_hidden('#skF_3'('#skF_8', B_516), B_516) | k1_relat_1('#skF_7')=B_516)), inference(negUnitSimplification, [status(thm)], [c_249, c_16574])).
% 14.04/5.55  tff(c_16749, plain, (![B_516]: (r2_hidden('#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_5'('#skF_7')), k1_relat_1('#skF_8')) | r2_hidden('#skF_3'('#skF_8', B_516), B_516) | k2_relat_1('#skF_8')=B_516 | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | '#skF_5'('#skF_7')!='#skF_1'('#skF_8', B_516) | r2_hidden('#skF_3'('#skF_8', B_516), B_516) | k1_relat_1('#skF_7')=B_516)), inference(superposition, [status(thm), theory('equality')], [c_16702, c_28])).
% 14.04/5.55  tff(c_16818, plain, (![B_516]: (r2_hidden('#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_5'('#skF_7')), k1_relat_1('#skF_8')) | '#skF_5'('#skF_7')!='#skF_1'('#skF_8', B_516) | r2_hidden('#skF_3'('#skF_8', B_516), B_516) | k1_relat_1('#skF_7')=B_516)), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_50, c_16749])).
% 14.04/5.55  tff(c_17197, plain, (r2_hidden('#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_5'('#skF_7')), k1_relat_1('#skF_8'))), inference(splitLeft, [status(thm)], [c_16818])).
% 14.04/5.55  tff(c_18002, plain, (k1_funct_1(k5_relat_1('#skF_8', '#skF_7'), '#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_5'('#skF_7')))=k1_funct_1('#skF_7', k1_funct_1('#skF_8', '#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_5'('#skF_7'))))), inference(resolution, [status(thm)], [c_17197, c_17859])).
% 14.04/5.55  tff(c_18070, plain, ('#skF_4'(k5_relat_1('#skF_8', '#skF_7'), k2_relat_1(k5_relat_1('#skF_8', '#skF_7')), k1_funct_1('#skF_7', k1_funct_1('#skF_8', '#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_5'('#skF_7')))))='#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_5'('#skF_7')) | ~v2_funct_1(k5_relat_1('#skF_8', '#skF_7')) | ~r2_hidden('#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_5'('#skF_7')), k1_relat_1(k5_relat_1('#skF_8', '#skF_7'))) | ~v1_funct_1(k5_relat_1('#skF_8', '#skF_7')) | ~v1_relat_1(k5_relat_1('#skF_8', '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_18002, c_17474])).
% 14.04/5.55  tff(c_18099, plain, ('#skF_4'(k5_relat_1('#skF_8', '#skF_7'), k2_relat_1(k5_relat_1('#skF_8', '#skF_7')), k1_funct_1('#skF_7', k1_funct_1('#skF_8', '#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_5'('#skF_7')))))='#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_5'('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_389, c_442, c_17197, c_311, c_52, c_18070])).
% 14.04/5.55  tff(c_19670, plain, ('#skF_4'(k5_relat_1('#skF_8', '#skF_7'), k2_relat_1(k5_relat_1('#skF_8', '#skF_7')), k1_funct_1('#skF_7', '#skF_5'('#skF_7')))='#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_5'('#skF_7')) | ~r2_hidden('#skF_5'('#skF_7'), k1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_352, c_18099])).
% 14.04/5.55  tff(c_19689, plain, ('#skF_4'(k5_relat_1('#skF_8', '#skF_7'), k2_relat_1(k5_relat_1('#skF_8', '#skF_7')), k1_funct_1('#skF_7', '#skF_5'('#skF_7')))='#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_5'('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_11159, c_19670])).
% 14.04/5.55  tff(c_19715, plain, ('#skF_4'(k5_relat_1('#skF_8', '#skF_7'), k2_relat_1(k5_relat_1('#skF_8', '#skF_7')), k1_funct_1('#skF_7', '#skF_6'('#skF_7')))='#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_5'('#skF_7')) | v2_funct_1('#skF_7') | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_34, c_19689])).
% 14.04/5.55  tff(c_19733, plain, ('#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_5'('#skF_7'))='#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_6'('#skF_7')) | v2_funct_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_19064, c_19715])).
% 14.04/5.55  tff(c_19734, plain, ('#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_5'('#skF_7'))='#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_6'('#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_249, c_19733])).
% 14.04/5.55  tff(c_19775, plain, (k1_funct_1('#skF_8', '#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_6'('#skF_7')))='#skF_5'('#skF_7') | ~r2_hidden('#skF_5'('#skF_7'), k1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_19734, c_352])).
% 14.04/5.55  tff(c_19795, plain, (k1_funct_1('#skF_8', '#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_6'('#skF_7')))='#skF_5'('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_11159, c_19775])).
% 14.04/5.55  tff(c_19852, plain, ('#skF_5'('#skF_7')='#skF_6'('#skF_7') | ~r2_hidden('#skF_6'('#skF_7'), k1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_19795, c_352])).
% 14.04/5.55  tff(c_19904, plain, ('#skF_5'('#skF_7')='#skF_6'('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_19065, c_19852])).
% 14.04/5.55  tff(c_19906, plain, $false, inference(negUnitSimplification, [status(thm)], [c_269, c_19904])).
% 14.04/5.55  tff(c_19908, plain, (~r2_hidden('#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_5'('#skF_7')), k1_relat_1('#skF_8'))), inference(splitRight, [status(thm)], [c_16818])).
% 14.04/5.55  tff(c_19912, plain, (~r2_hidden('#skF_5'('#skF_7'), k1_relat_1('#skF_7'))), inference(resolution, [status(thm)], [c_378, c_19908])).
% 14.04/5.55  tff(c_19916, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_11159, c_19912])).
% 14.04/5.55  tff(c_19918, plain, (~r2_hidden('#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_6'('#skF_7')), k1_relat_1('#skF_8'))), inference(splitRight, [status(thm)], [c_16677])).
% 14.04/5.55  tff(c_19923, plain, (~r2_hidden('#skF_6'('#skF_7'), k1_relat_1('#skF_7'))), inference(resolution, [status(thm)], [c_378, c_19918])).
% 14.04/5.55  tff(c_19926, plain, (v2_funct_1('#skF_7') | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_36, c_19923])).
% 14.04/5.55  tff(c_19929, plain, (v2_funct_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_19926])).
% 14.04/5.55  tff(c_19931, plain, $false, inference(negUnitSimplification, [status(thm)], [c_249, c_19929])).
% 14.04/5.55  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.04/5.55  
% 14.04/5.55  Inference rules
% 14.04/5.55  ----------------------
% 14.04/5.55  #Ref     : 9
% 14.04/5.55  #Sup     : 4421
% 14.04/5.55  #Fact    : 0
% 14.04/5.55  #Define  : 0
% 14.04/5.55  #Split   : 41
% 14.04/5.55  #Chain   : 0
% 14.04/5.55  #Close   : 0
% 14.04/5.55  
% 14.04/5.55  Ordering : KBO
% 14.04/5.55  
% 14.04/5.55  Simplification rules
% 14.04/5.55  ----------------------
% 14.04/5.55  #Subsume      : 481
% 14.04/5.55  #Demod        : 7372
% 14.04/5.55  #Tautology    : 1305
% 14.04/5.55  #SimpNegUnit  : 358
% 14.04/5.55  #BackRed      : 86
% 14.04/5.55  
% 14.04/5.55  #Partial instantiations: 0
% 14.04/5.55  #Strategies tried      : 1
% 14.04/5.55  
% 14.04/5.55  Timing (in seconds)
% 14.04/5.55  ----------------------
% 14.04/5.55  Preprocessing        : 0.35
% 14.04/5.55  Parsing              : 0.18
% 14.04/5.55  CNF conversion       : 0.03
% 14.04/5.55  Main loop            : 4.33
% 14.04/5.55  Inferencing          : 1.18
% 14.04/5.55  Reduction            : 1.43
% 14.04/5.55  Demodulation         : 1.04
% 14.04/5.55  BG Simplification    : 0.19
% 14.04/5.55  Subsumption          : 1.29
% 14.04/5.55  Abstraction          : 0.28
% 14.04/5.55  MUC search           : 0.00
% 14.04/5.55  Cooper               : 0.00
% 14.04/5.56  Total                : 4.73
% 14.04/5.56  Index Insertion      : 0.00
% 14.04/5.56  Index Deletion       : 0.00
% 14.04/5.56  Index Matching       : 0.00
% 14.04/5.56  BG Taut test         : 0.00
%------------------------------------------------------------------------------
