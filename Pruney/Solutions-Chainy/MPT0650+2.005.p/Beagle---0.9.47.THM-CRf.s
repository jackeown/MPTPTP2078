%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:45 EST 2020

% Result     : Theorem 10.95s
% Output     : CNFRefutation 10.95s
% Verified   : 
% Statistics : Number of formulae       :  136 (1266 expanded)
%              Number of leaves         :   37 ( 474 expanded)
%              Depth                    :   19
%              Number of atoms          :  255 (3856 expanded)
%              Number of equality atoms :   43 ( 989 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > k4_tarski > k1_funct_1 > #nlpp > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_11 > #skF_6 > #skF_4 > #skF_3 > #skF_12 > #skF_14 > #skF_13 > #skF_10 > #skF_2 > #skF_8 > #skF_7 > #skF_1 > #skF_9 > #skF_5

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_11',type,(
    '#skF_11': ( $i * $i ) > $i )).

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

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_12',type,(
    '#skF_12': ( $i * $i ) > $i )).

tff('#skF_14',type,(
    '#skF_14': $i )).

tff('#skF_13',type,(
    '#skF_13': $i )).

tff('#skF_10',type,(
    '#skF_10': ( $i * $i ) > $i )).

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

tff('#skF_9',type,(
    '#skF_9': ( $i * $i ) > $i )).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_funct_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

tff(f_73,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_65,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(A) = k4_relat_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).

tff(f_57,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => v1_relat_1(k4_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).

tff(f_53,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( B = k4_relat_1(A)
          <=> ! [C,D] :
                ( r2_hidden(k4_tarski(C,D),B)
              <=> r2_hidden(k4_tarski(D,C),A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_relat_1)).

tff(f_96,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_86,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ! [C] :
          ( ( v1_relat_1(C)
            & v1_funct_1(C) )
         => ( r2_hidden(A,k1_relat_1(B))
           => k1_funct_1(k5_relat_1(B,C),A) = k1_funct_1(C,k1_funct_1(B,A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_funct_1)).

tff(c_62,plain,(
    v1_relat_1('#skF_14') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_60,plain,(
    v1_funct_1('#skF_14') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_56,plain,(
    r2_hidden('#skF_13',k2_relat_1('#skF_14')) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_14,plain,(
    ! [A_20,C_35] :
      ( r2_hidden(k4_tarski('#skF_8'(A_20,k2_relat_1(A_20),C_35),C_35),A_20)
      | ~ r2_hidden(C_35,k2_relat_1(A_20)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_42,plain,(
    ! [A_58] :
      ( v1_funct_1(k2_funct_1(A_58))
      | ~ v1_funct_1(A_58)
      | ~ v1_relat_1(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_58,plain,(
    v2_funct_1('#skF_14') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_997,plain,(
    ! [A_159] :
      ( k4_relat_1(A_159) = k2_funct_1(A_159)
      | ~ v2_funct_1(A_159)
      | ~ v1_funct_1(A_159)
      | ~ v1_relat_1(A_159) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1000,plain,
    ( k4_relat_1('#skF_14') = k2_funct_1('#skF_14')
    | ~ v1_funct_1('#skF_14')
    | ~ v1_relat_1('#skF_14') ),
    inference(resolution,[status(thm)],[c_58,c_997])).

tff(c_1003,plain,(
    k4_relat_1('#skF_14') = k2_funct_1('#skF_14') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_1000])).

tff(c_38,plain,(
    ! [A_56] :
      ( v1_relat_1(k4_relat_1(A_56))
      | ~ v1_relat_1(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1016,plain,
    ( v1_relat_1(k2_funct_1('#skF_14'))
    | ~ v1_relat_1('#skF_14') ),
    inference(superposition,[status(thm),theory(equality)],[c_1003,c_38])).

tff(c_1020,plain,(
    v1_relat_1(k2_funct_1('#skF_14')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_1016])).

tff(c_1964,plain,(
    ! [C_238,D_239,A_240] :
      ( r2_hidden(k4_tarski(C_238,D_239),k4_relat_1(A_240))
      | ~ r2_hidden(k4_tarski(D_239,C_238),A_240)
      | ~ v1_relat_1(k4_relat_1(A_240))
      | ~ v1_relat_1(A_240) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1979,plain,(
    ! [C_238,D_239] :
      ( r2_hidden(k4_tarski(C_238,D_239),k2_funct_1('#skF_14'))
      | ~ r2_hidden(k4_tarski(D_239,C_238),'#skF_14')
      | ~ v1_relat_1(k4_relat_1('#skF_14'))
      | ~ v1_relat_1('#skF_14') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1003,c_1964])).

tff(c_1986,plain,(
    ! [C_241,D_242] :
      ( r2_hidden(k4_tarski(C_241,D_242),k2_funct_1('#skF_14'))
      | ~ r2_hidden(k4_tarski(D_242,C_241),'#skF_14') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_1020,c_1003,c_1979])).

tff(c_50,plain,(
    ! [C_65,A_63,B_64] :
      ( k1_funct_1(C_65,A_63) = B_64
      | ~ r2_hidden(k4_tarski(A_63,B_64),C_65)
      | ~ v1_funct_1(C_65)
      | ~ v1_relat_1(C_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_1992,plain,(
    ! [C_241,D_242] :
      ( k1_funct_1(k2_funct_1('#skF_14'),C_241) = D_242
      | ~ v1_funct_1(k2_funct_1('#skF_14'))
      | ~ v1_relat_1(k2_funct_1('#skF_14'))
      | ~ r2_hidden(k4_tarski(D_242,C_241),'#skF_14') ) ),
    inference(resolution,[status(thm)],[c_1986,c_50])).

tff(c_2002,plain,(
    ! [C_241,D_242] :
      ( k1_funct_1(k2_funct_1('#skF_14'),C_241) = D_242
      | ~ v1_funct_1(k2_funct_1('#skF_14'))
      | ~ r2_hidden(k4_tarski(D_242,C_241),'#skF_14') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1020,c_1992])).

tff(c_2452,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_14')) ),
    inference(splitLeft,[status(thm)],[c_2002])).

tff(c_2455,plain,
    ( ~ v1_funct_1('#skF_14')
    | ~ v1_relat_1('#skF_14') ),
    inference(resolution,[status(thm)],[c_42,c_2452])).

tff(c_2459,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_2455])).

tff(c_2541,plain,(
    ! [C_273,D_274] :
      ( k1_funct_1(k2_funct_1('#skF_14'),C_273) = D_274
      | ~ r2_hidden(k4_tarski(D_274,C_273),'#skF_14') ) ),
    inference(splitRight,[status(thm)],[c_2002])).

tff(c_2687,plain,(
    ! [C_283] :
      ( k1_funct_1(k2_funct_1('#skF_14'),C_283) = '#skF_8'('#skF_14',k2_relat_1('#skF_14'),C_283)
      | ~ r2_hidden(C_283,k2_relat_1('#skF_14')) ) ),
    inference(resolution,[status(thm)],[c_14,c_2541])).

tff(c_2742,plain,(
    k1_funct_1(k2_funct_1('#skF_14'),'#skF_13') = '#skF_8'('#skF_14',k2_relat_1('#skF_14'),'#skF_13') ),
    inference(resolution,[status(thm)],[c_56,c_2687])).

tff(c_69,plain,(
    ! [A_75] :
      ( k4_relat_1(A_75) = k2_funct_1(A_75)
      | ~ v2_funct_1(A_75)
      | ~ v1_funct_1(A_75)
      | ~ v1_relat_1(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_72,plain,
    ( k4_relat_1('#skF_14') = k2_funct_1('#skF_14')
    | ~ v1_funct_1('#skF_14')
    | ~ v1_relat_1('#skF_14') ),
    inference(resolution,[status(thm)],[c_58,c_69])).

tff(c_75,plain,(
    k4_relat_1('#skF_14') = k2_funct_1('#skF_14') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_72])).

tff(c_79,plain,
    ( v1_relat_1(k2_funct_1('#skF_14'))
    | ~ v1_relat_1('#skF_14') ),
    inference(superposition,[status(thm),theory(equality)],[c_75,c_38])).

tff(c_83,plain,(
    v1_relat_1(k2_funct_1('#skF_14')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_79])).

tff(c_172,plain,(
    ! [C_106,D_107,A_108] :
      ( r2_hidden(k4_tarski(C_106,D_107),k4_relat_1(A_108))
      | ~ r2_hidden(k4_tarski(D_107,C_106),A_108)
      | ~ v1_relat_1(k4_relat_1(A_108))
      | ~ v1_relat_1(A_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_187,plain,(
    ! [C_106,D_107] :
      ( r2_hidden(k4_tarski(C_106,D_107),k2_funct_1('#skF_14'))
      | ~ r2_hidden(k4_tarski(D_107,C_106),'#skF_14')
      | ~ v1_relat_1(k4_relat_1('#skF_14'))
      | ~ v1_relat_1('#skF_14') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_75,c_172])).

tff(c_194,plain,(
    ! [C_109,D_110] :
      ( r2_hidden(k4_tarski(C_109,D_110),k2_funct_1('#skF_14'))
      | ~ r2_hidden(k4_tarski(D_110,C_109),'#skF_14') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_83,c_75,c_187])).

tff(c_200,plain,(
    ! [C_109,D_110] :
      ( k1_funct_1(k2_funct_1('#skF_14'),C_109) = D_110
      | ~ v1_funct_1(k2_funct_1('#skF_14'))
      | ~ v1_relat_1(k2_funct_1('#skF_14'))
      | ~ r2_hidden(k4_tarski(D_110,C_109),'#skF_14') ) ),
    inference(resolution,[status(thm)],[c_194,c_50])).

tff(c_210,plain,(
    ! [C_109,D_110] :
      ( k1_funct_1(k2_funct_1('#skF_14'),C_109) = D_110
      | ~ v1_funct_1(k2_funct_1('#skF_14'))
      | ~ r2_hidden(k4_tarski(D_110,C_109),'#skF_14') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_200])).

tff(c_605,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_14')) ),
    inference(splitLeft,[status(thm)],[c_210])).

tff(c_629,plain,
    ( ~ v1_funct_1('#skF_14')
    | ~ v1_relat_1('#skF_14') ),
    inference(resolution,[status(thm)],[c_42,c_605])).

tff(c_633,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_629])).

tff(c_636,plain,(
    ! [C_138,D_139] :
      ( k1_funct_1(k2_funct_1('#skF_14'),C_138) = D_139
      | ~ r2_hidden(k4_tarski(D_139,C_138),'#skF_14') ) ),
    inference(splitRight,[status(thm)],[c_210])).

tff(c_753,plain,(
    ! [C_147] :
      ( k1_funct_1(k2_funct_1('#skF_14'),C_147) = '#skF_8'('#skF_14',k2_relat_1('#skF_14'),C_147)
      | ~ r2_hidden(C_147,k2_relat_1('#skF_14')) ) ),
    inference(resolution,[status(thm)],[c_14,c_636])).

tff(c_808,plain,(
    k1_funct_1(k2_funct_1('#skF_14'),'#skF_13') = '#skF_8'('#skF_14',k2_relat_1('#skF_14'),'#skF_13') ),
    inference(resolution,[status(thm)],[c_56,c_753])).

tff(c_54,plain,
    ( k1_funct_1(k5_relat_1(k2_funct_1('#skF_14'),'#skF_14'),'#skF_13') != '#skF_13'
    | k1_funct_1('#skF_14',k1_funct_1(k2_funct_1('#skF_14'),'#skF_13')) != '#skF_13' ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_68,plain,(
    k1_funct_1('#skF_14',k1_funct_1(k2_funct_1('#skF_14'),'#skF_13')) != '#skF_13' ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_809,plain,(
    k1_funct_1('#skF_14','#skF_8'('#skF_14',k2_relat_1('#skF_14'),'#skF_13')) != '#skF_13' ),
    inference(demodulation,[status(thm),theory(equality)],[c_808,c_68])).

tff(c_4,plain,(
    ! [C_16,A_1,D_19] :
      ( r2_hidden(C_16,k1_relat_1(A_1))
      | ~ r2_hidden(k4_tarski(C_16,D_19),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_213,plain,(
    ! [C_111,D_112] :
      ( r2_hidden(C_111,k1_relat_1(k2_funct_1('#skF_14')))
      | ~ r2_hidden(k4_tarski(D_112,C_111),'#skF_14') ) ),
    inference(resolution,[status(thm)],[c_194,c_4])).

tff(c_226,plain,(
    ! [C_35] :
      ( r2_hidden(C_35,k1_relat_1(k2_funct_1('#skF_14')))
      | ~ r2_hidden(C_35,k2_relat_1('#skF_14')) ) ),
    inference(resolution,[status(thm)],[c_14,c_213])).

tff(c_635,plain,(
    v1_funct_1(k2_funct_1('#skF_14')) ),
    inference(splitRight,[status(thm)],[c_210])).

tff(c_116,plain,(
    ! [A_91,C_92] :
      ( r2_hidden(k4_tarski(A_91,k1_funct_1(C_92,A_91)),C_92)
      | ~ r2_hidden(A_91,k1_relat_1(C_92))
      | ~ v1_funct_1(C_92)
      | ~ v1_relat_1(C_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_16,plain,(
    ! [C_35,A_20,D_38] :
      ( r2_hidden(C_35,k2_relat_1(A_20))
      | ~ r2_hidden(k4_tarski(D_38,C_35),A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_129,plain,(
    ! [C_92,A_91] :
      ( r2_hidden(k1_funct_1(C_92,A_91),k2_relat_1(C_92))
      | ~ r2_hidden(A_91,k1_relat_1(C_92))
      | ~ v1_funct_1(C_92)
      | ~ v1_relat_1(C_92) ) ),
    inference(resolution,[status(thm)],[c_116,c_16])).

tff(c_813,plain,
    ( r2_hidden('#skF_8'('#skF_14',k2_relat_1('#skF_14'),'#skF_13'),k2_relat_1(k2_funct_1('#skF_14')))
    | ~ r2_hidden('#skF_13',k1_relat_1(k2_funct_1('#skF_14')))
    | ~ v1_funct_1(k2_funct_1('#skF_14'))
    | ~ v1_relat_1(k2_funct_1('#skF_14')) ),
    inference(superposition,[status(thm),theory(equality)],[c_808,c_129])).

tff(c_820,plain,
    ( r2_hidden('#skF_8'('#skF_14',k2_relat_1('#skF_14'),'#skF_13'),k2_relat_1(k2_funct_1('#skF_14')))
    | ~ r2_hidden('#skF_13',k1_relat_1(k2_funct_1('#skF_14'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_635,c_813])).

tff(c_928,plain,(
    ~ r2_hidden('#skF_13',k1_relat_1(k2_funct_1('#skF_14'))) ),
    inference(splitLeft,[status(thm)],[c_820])).

tff(c_931,plain,(
    ~ r2_hidden('#skF_13',k2_relat_1('#skF_14')) ),
    inference(resolution,[status(thm)],[c_226,c_928])).

tff(c_935,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_931])).

tff(c_937,plain,(
    r2_hidden('#skF_13',k1_relat_1(k2_funct_1('#skF_14'))) ),
    inference(splitRight,[status(thm)],[c_820])).

tff(c_48,plain,(
    ! [A_63,C_65] :
      ( r2_hidden(k4_tarski(A_63,k1_funct_1(C_65,A_63)),C_65)
      | ~ r2_hidden(A_63,k1_relat_1(C_65))
      | ~ v1_funct_1(C_65)
      | ~ v1_relat_1(C_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_816,plain,
    ( r2_hidden(k4_tarski('#skF_13','#skF_8'('#skF_14',k2_relat_1('#skF_14'),'#skF_13')),k2_funct_1('#skF_14'))
    | ~ r2_hidden('#skF_13',k1_relat_1(k2_funct_1('#skF_14')))
    | ~ v1_funct_1(k2_funct_1('#skF_14'))
    | ~ v1_relat_1(k2_funct_1('#skF_14')) ),
    inference(superposition,[status(thm),theory(equality)],[c_808,c_48])).

tff(c_822,plain,
    ( r2_hidden(k4_tarski('#skF_13','#skF_8'('#skF_14',k2_relat_1('#skF_14'),'#skF_13')),k2_funct_1('#skF_14'))
    | ~ r2_hidden('#skF_13',k1_relat_1(k2_funct_1('#skF_14'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_635,c_816])).

tff(c_944,plain,(
    r2_hidden(k4_tarski('#skF_13','#skF_8'('#skF_14',k2_relat_1('#skF_14'),'#skF_13')),k2_funct_1('#skF_14')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_937,c_822])).

tff(c_133,plain,(
    ! [D_101,C_102,A_103] :
      ( r2_hidden(k4_tarski(D_101,C_102),A_103)
      | ~ r2_hidden(k4_tarski(C_102,D_101),k4_relat_1(A_103))
      | ~ v1_relat_1(k4_relat_1(A_103))
      | ~ v1_relat_1(A_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_148,plain,(
    ! [D_101,C_102] :
      ( r2_hidden(k4_tarski(D_101,C_102),'#skF_14')
      | ~ r2_hidden(k4_tarski(C_102,D_101),k2_funct_1('#skF_14'))
      | ~ v1_relat_1(k4_relat_1('#skF_14'))
      | ~ v1_relat_1('#skF_14') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_75,c_133])).

tff(c_153,plain,(
    ! [D_101,C_102] :
      ( r2_hidden(k4_tarski(D_101,C_102),'#skF_14')
      | ~ r2_hidden(k4_tarski(C_102,D_101),k2_funct_1('#skF_14')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_83,c_75,c_148])).

tff(c_957,plain,(
    r2_hidden(k4_tarski('#skF_8'('#skF_14',k2_relat_1('#skF_14'),'#skF_13'),'#skF_13'),'#skF_14') ),
    inference(resolution,[status(thm)],[c_944,c_153])).

tff(c_973,plain,
    ( k1_funct_1('#skF_14','#skF_8'('#skF_14',k2_relat_1('#skF_14'),'#skF_13')) = '#skF_13'
    | ~ v1_funct_1('#skF_14')
    | ~ v1_relat_1('#skF_14') ),
    inference(resolution,[status(thm)],[c_957,c_50])).

tff(c_988,plain,(
    k1_funct_1('#skF_14','#skF_8'('#skF_14',k2_relat_1('#skF_14'),'#skF_13')) = '#skF_13' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_973])).

tff(c_990,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_809,c_988])).

tff(c_992,plain,(
    k1_funct_1('#skF_14',k1_funct_1(k2_funct_1('#skF_14'),'#skF_13')) = '#skF_13' ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_2746,plain,(
    k1_funct_1('#skF_14','#skF_8'('#skF_14',k2_relat_1('#skF_14'),'#skF_13')) = '#skF_13' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2742,c_992])).

tff(c_2461,plain,(
    v1_funct_1(k2_funct_1('#skF_14')) ),
    inference(splitRight,[status(thm)],[c_2002])).

tff(c_1030,plain,(
    ! [A_171,C_172] :
      ( r2_hidden(k4_tarski('#skF_8'(A_171,k2_relat_1(A_171),C_172),C_172),A_171)
      | ~ r2_hidden(C_172,k2_relat_1(A_171)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1041,plain,(
    ! [A_171,C_172] :
      ( r2_hidden('#skF_8'(A_171,k2_relat_1(A_171),C_172),k1_relat_1(A_171))
      | ~ r2_hidden(C_172,k2_relat_1(A_171)) ) ),
    inference(resolution,[status(thm)],[c_1030,c_4])).

tff(c_1072,plain,(
    ! [C_185,D_186,A_187] :
      ( r2_hidden(k4_tarski(C_185,D_186),k4_relat_1(A_187))
      | ~ r2_hidden(k4_tarski(D_186,C_185),A_187)
      | ~ v1_relat_1(k4_relat_1(A_187))
      | ~ v1_relat_1(A_187) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1084,plain,(
    ! [C_185,D_186] :
      ( r2_hidden(k4_tarski(C_185,D_186),k2_funct_1('#skF_14'))
      | ~ r2_hidden(k4_tarski(D_186,C_185),'#skF_14')
      | ~ v1_relat_1(k4_relat_1('#skF_14'))
      | ~ v1_relat_1('#skF_14') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1003,c_1072])).

tff(c_1090,plain,(
    ! [C_188,D_189] :
      ( r2_hidden(k4_tarski(C_188,D_189),k2_funct_1('#skF_14'))
      | ~ r2_hidden(k4_tarski(D_189,C_188),'#skF_14') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_1020,c_1003,c_1084])).

tff(c_1093,plain,(
    ! [C_188,D_189] :
      ( k1_funct_1(k2_funct_1('#skF_14'),C_188) = D_189
      | ~ v1_funct_1(k2_funct_1('#skF_14'))
      | ~ v1_relat_1(k2_funct_1('#skF_14'))
      | ~ r2_hidden(k4_tarski(D_189,C_188),'#skF_14') ) ),
    inference(resolution,[status(thm)],[c_1090,c_50])).

tff(c_1102,plain,(
    ! [C_188,D_189] :
      ( k1_funct_1(k2_funct_1('#skF_14'),C_188) = D_189
      | ~ v1_funct_1(k2_funct_1('#skF_14'))
      | ~ r2_hidden(k4_tarski(D_189,C_188),'#skF_14') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1020,c_1093])).

tff(c_1567,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_14')) ),
    inference(splitLeft,[status(thm)],[c_1102])).

tff(c_1627,plain,
    ( ~ v1_funct_1('#skF_14')
    | ~ v1_relat_1('#skF_14') ),
    inference(resolution,[status(thm)],[c_42,c_1567])).

tff(c_1631,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_1627])).

tff(c_1634,plain,(
    ! [C_223,D_224] :
      ( k1_funct_1(k2_funct_1('#skF_14'),C_223) = D_224
      | ~ r2_hidden(k4_tarski(D_224,C_223),'#skF_14') ) ),
    inference(splitRight,[status(thm)],[c_1102])).

tff(c_1741,plain,(
    ! [C_230] :
      ( k1_funct_1(k2_funct_1('#skF_14'),C_230) = '#skF_8'('#skF_14',k2_relat_1('#skF_14'),C_230)
      | ~ r2_hidden(C_230,k2_relat_1('#skF_14')) ) ),
    inference(resolution,[status(thm)],[c_14,c_1634])).

tff(c_1791,plain,(
    k1_funct_1(k2_funct_1('#skF_14'),'#skF_13') = '#skF_8'('#skF_14',k2_relat_1('#skF_14'),'#skF_13') ),
    inference(resolution,[status(thm)],[c_56,c_1741])).

tff(c_1046,plain,(
    ! [A_181,C_182] :
      ( r2_hidden(k4_tarski(A_181,k1_funct_1(C_182,A_181)),C_182)
      | ~ r2_hidden(A_181,k1_relat_1(C_182))
      | ~ v1_funct_1(C_182)
      | ~ v1_relat_1(C_182) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_1058,plain,
    ( r2_hidden(k4_tarski(k1_funct_1(k2_funct_1('#skF_14'),'#skF_13'),'#skF_13'),'#skF_14')
    | ~ r2_hidden(k1_funct_1(k2_funct_1('#skF_14'),'#skF_13'),k1_relat_1('#skF_14'))
    | ~ v1_funct_1('#skF_14')
    | ~ v1_relat_1('#skF_14') ),
    inference(superposition,[status(thm),theory(equality)],[c_992,c_1046])).

tff(c_1064,plain,
    ( r2_hidden(k4_tarski(k1_funct_1(k2_funct_1('#skF_14'),'#skF_13'),'#skF_13'),'#skF_14')
    | ~ r2_hidden(k1_funct_1(k2_funct_1('#skF_14'),'#skF_13'),k1_relat_1('#skF_14')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_1058])).

tff(c_1071,plain,(
    ~ r2_hidden(k1_funct_1(k2_funct_1('#skF_14'),'#skF_13'),k1_relat_1('#skF_14')) ),
    inference(splitLeft,[status(thm)],[c_1064])).

tff(c_1859,plain,(
    ~ r2_hidden('#skF_8'('#skF_14',k2_relat_1('#skF_14'),'#skF_13'),k1_relat_1('#skF_14')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1791,c_1071])).

tff(c_1902,plain,(
    ~ r2_hidden('#skF_13',k2_relat_1('#skF_14')) ),
    inference(resolution,[status(thm)],[c_1041,c_1859])).

tff(c_1906,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_1902])).

tff(c_1907,plain,(
    r2_hidden(k4_tarski(k1_funct_1(k2_funct_1('#skF_14'),'#skF_13'),'#skF_13'),'#skF_14') ),
    inference(splitRight,[status(thm)],[c_1064])).

tff(c_2028,plain,(
    ! [C_245,D_246] :
      ( r2_hidden(C_245,k1_relat_1(k2_funct_1('#skF_14')))
      | ~ r2_hidden(k4_tarski(D_246,C_245),'#skF_14') ) ),
    inference(resolution,[status(thm)],[c_1986,c_4])).

tff(c_2044,plain,(
    r2_hidden('#skF_13',k1_relat_1(k2_funct_1('#skF_14'))) ),
    inference(resolution,[status(thm)],[c_1907,c_2028])).

tff(c_2825,plain,(
    ! [B_284,C_285,A_286] :
      ( k1_funct_1(k5_relat_1(B_284,C_285),A_286) = k1_funct_1(C_285,k1_funct_1(B_284,A_286))
      | ~ r2_hidden(A_286,k1_relat_1(B_284))
      | ~ v1_funct_1(C_285)
      | ~ v1_relat_1(C_285)
      | ~ v1_funct_1(B_284)
      | ~ v1_relat_1(B_284) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_2842,plain,(
    ! [C_285] :
      ( k1_funct_1(k5_relat_1(k2_funct_1('#skF_14'),C_285),'#skF_13') = k1_funct_1(C_285,k1_funct_1(k2_funct_1('#skF_14'),'#skF_13'))
      | ~ v1_funct_1(C_285)
      | ~ v1_relat_1(C_285)
      | ~ v1_funct_1(k2_funct_1('#skF_14'))
      | ~ v1_relat_1(k2_funct_1('#skF_14')) ) ),
    inference(resolution,[status(thm)],[c_2044,c_2825])).

tff(c_16584,plain,(
    ! [C_586] :
      ( k1_funct_1(k5_relat_1(k2_funct_1('#skF_14'),C_586),'#skF_13') = k1_funct_1(C_586,'#skF_8'('#skF_14',k2_relat_1('#skF_14'),'#skF_13'))
      | ~ v1_funct_1(C_586)
      | ~ v1_relat_1(C_586) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1020,c_2461,c_2742,c_2842])).

tff(c_991,plain,(
    k1_funct_1(k5_relat_1(k2_funct_1('#skF_14'),'#skF_14'),'#skF_13') != '#skF_13' ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_16596,plain,
    ( k1_funct_1('#skF_14','#skF_8'('#skF_14',k2_relat_1('#skF_14'),'#skF_13')) != '#skF_13'
    | ~ v1_funct_1('#skF_14')
    | ~ v1_relat_1('#skF_14') ),
    inference(superposition,[status(thm),theory(equality)],[c_16584,c_991])).

tff(c_16603,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_2746,c_16596])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:38:27 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.95/4.15  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.95/4.16  
% 10.95/4.16  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.95/4.16  %$ r2_hidden > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > k4_tarski > k1_funct_1 > #nlpp > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_11 > #skF_6 > #skF_4 > #skF_3 > #skF_12 > #skF_14 > #skF_13 > #skF_10 > #skF_2 > #skF_8 > #skF_7 > #skF_1 > #skF_9 > #skF_5
% 10.95/4.16  
% 10.95/4.16  %Foreground sorts:
% 10.95/4.16  
% 10.95/4.16  
% 10.95/4.16  %Background operators:
% 10.95/4.16  
% 10.95/4.16  
% 10.95/4.16  %Foreground operators:
% 10.95/4.16  tff('#skF_11', type, '#skF_11': ($i * $i) > $i).
% 10.95/4.16  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 10.95/4.16  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 10.95/4.16  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 10.95/4.16  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 10.95/4.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.95/4.16  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 10.95/4.16  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 10.95/4.16  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 10.95/4.16  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 10.95/4.16  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 10.95/4.16  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 10.95/4.16  tff('#skF_12', type, '#skF_12': ($i * $i) > $i).
% 10.95/4.16  tff('#skF_14', type, '#skF_14': $i).
% 10.95/4.16  tff('#skF_13', type, '#skF_13': $i).
% 10.95/4.16  tff('#skF_10', type, '#skF_10': ($i * $i) > $i).
% 10.95/4.16  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 10.95/4.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.95/4.16  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 10.95/4.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.95/4.16  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 10.95/4.16  tff('#skF_8', type, '#skF_8': ($i * $i * $i) > $i).
% 10.95/4.16  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 10.95/4.16  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 10.95/4.16  tff('#skF_9', type, '#skF_9': ($i * $i) > $i).
% 10.95/4.16  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 10.95/4.16  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 10.95/4.16  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 10.95/4.16  
% 10.95/4.18  tff(f_109, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v2_funct_1(B) & r2_hidden(A, k2_relat_1(B))) => ((A = k1_funct_1(B, k1_funct_1(k2_funct_1(B), A))) & (A = k1_funct_1(k5_relat_1(k2_funct_1(B), B), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t57_funct_1)).
% 10.95/4.18  tff(f_41, axiom, (![A, B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(D, C), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_relat_1)).
% 10.95/4.18  tff(f_73, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 10.95/4.18  tff(f_65, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(A) = k4_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_funct_1)).
% 10.95/4.18  tff(f_57, axiom, (![A]: (v1_relat_1(A) => v1_relat_1(k4_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_relat_1)).
% 10.95/4.18  tff(f_53, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => ((B = k4_relat_1(A)) <=> (![C, D]: (r2_hidden(k4_tarski(C, D), B) <=> r2_hidden(k4_tarski(D, C), A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_relat_1)).
% 10.95/4.18  tff(f_96, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_funct_1)).
% 10.95/4.18  tff(f_33, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_relat_1)).
% 10.95/4.18  tff(f_86, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(B)) => (k1_funct_1(k5_relat_1(B, C), A) = k1_funct_1(C, k1_funct_1(B, A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_funct_1)).
% 10.95/4.18  tff(c_62, plain, (v1_relat_1('#skF_14')), inference(cnfTransformation, [status(thm)], [f_109])).
% 10.95/4.18  tff(c_60, plain, (v1_funct_1('#skF_14')), inference(cnfTransformation, [status(thm)], [f_109])).
% 10.95/4.18  tff(c_56, plain, (r2_hidden('#skF_13', k2_relat_1('#skF_14'))), inference(cnfTransformation, [status(thm)], [f_109])).
% 10.95/4.18  tff(c_14, plain, (![A_20, C_35]: (r2_hidden(k4_tarski('#skF_8'(A_20, k2_relat_1(A_20), C_35), C_35), A_20) | ~r2_hidden(C_35, k2_relat_1(A_20)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 10.95/4.18  tff(c_42, plain, (![A_58]: (v1_funct_1(k2_funct_1(A_58)) | ~v1_funct_1(A_58) | ~v1_relat_1(A_58))), inference(cnfTransformation, [status(thm)], [f_73])).
% 10.95/4.18  tff(c_58, plain, (v2_funct_1('#skF_14')), inference(cnfTransformation, [status(thm)], [f_109])).
% 10.95/4.18  tff(c_997, plain, (![A_159]: (k4_relat_1(A_159)=k2_funct_1(A_159) | ~v2_funct_1(A_159) | ~v1_funct_1(A_159) | ~v1_relat_1(A_159))), inference(cnfTransformation, [status(thm)], [f_65])).
% 10.95/4.18  tff(c_1000, plain, (k4_relat_1('#skF_14')=k2_funct_1('#skF_14') | ~v1_funct_1('#skF_14') | ~v1_relat_1('#skF_14')), inference(resolution, [status(thm)], [c_58, c_997])).
% 10.95/4.18  tff(c_1003, plain, (k4_relat_1('#skF_14')=k2_funct_1('#skF_14')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_1000])).
% 10.95/4.18  tff(c_38, plain, (![A_56]: (v1_relat_1(k4_relat_1(A_56)) | ~v1_relat_1(A_56))), inference(cnfTransformation, [status(thm)], [f_57])).
% 10.95/4.18  tff(c_1016, plain, (v1_relat_1(k2_funct_1('#skF_14')) | ~v1_relat_1('#skF_14')), inference(superposition, [status(thm), theory('equality')], [c_1003, c_38])).
% 10.95/4.18  tff(c_1020, plain, (v1_relat_1(k2_funct_1('#skF_14'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_1016])).
% 10.95/4.18  tff(c_1964, plain, (![C_238, D_239, A_240]: (r2_hidden(k4_tarski(C_238, D_239), k4_relat_1(A_240)) | ~r2_hidden(k4_tarski(D_239, C_238), A_240) | ~v1_relat_1(k4_relat_1(A_240)) | ~v1_relat_1(A_240))), inference(cnfTransformation, [status(thm)], [f_53])).
% 10.95/4.18  tff(c_1979, plain, (![C_238, D_239]: (r2_hidden(k4_tarski(C_238, D_239), k2_funct_1('#skF_14')) | ~r2_hidden(k4_tarski(D_239, C_238), '#skF_14') | ~v1_relat_1(k4_relat_1('#skF_14')) | ~v1_relat_1('#skF_14'))), inference(superposition, [status(thm), theory('equality')], [c_1003, c_1964])).
% 10.95/4.18  tff(c_1986, plain, (![C_241, D_242]: (r2_hidden(k4_tarski(C_241, D_242), k2_funct_1('#skF_14')) | ~r2_hidden(k4_tarski(D_242, C_241), '#skF_14'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_1020, c_1003, c_1979])).
% 10.95/4.18  tff(c_50, plain, (![C_65, A_63, B_64]: (k1_funct_1(C_65, A_63)=B_64 | ~r2_hidden(k4_tarski(A_63, B_64), C_65) | ~v1_funct_1(C_65) | ~v1_relat_1(C_65))), inference(cnfTransformation, [status(thm)], [f_96])).
% 10.95/4.18  tff(c_1992, plain, (![C_241, D_242]: (k1_funct_1(k2_funct_1('#skF_14'), C_241)=D_242 | ~v1_funct_1(k2_funct_1('#skF_14')) | ~v1_relat_1(k2_funct_1('#skF_14')) | ~r2_hidden(k4_tarski(D_242, C_241), '#skF_14'))), inference(resolution, [status(thm)], [c_1986, c_50])).
% 10.95/4.18  tff(c_2002, plain, (![C_241, D_242]: (k1_funct_1(k2_funct_1('#skF_14'), C_241)=D_242 | ~v1_funct_1(k2_funct_1('#skF_14')) | ~r2_hidden(k4_tarski(D_242, C_241), '#skF_14'))), inference(demodulation, [status(thm), theory('equality')], [c_1020, c_1992])).
% 10.95/4.18  tff(c_2452, plain, (~v1_funct_1(k2_funct_1('#skF_14'))), inference(splitLeft, [status(thm)], [c_2002])).
% 10.95/4.18  tff(c_2455, plain, (~v1_funct_1('#skF_14') | ~v1_relat_1('#skF_14')), inference(resolution, [status(thm)], [c_42, c_2452])).
% 10.95/4.18  tff(c_2459, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_2455])).
% 10.95/4.18  tff(c_2541, plain, (![C_273, D_274]: (k1_funct_1(k2_funct_1('#skF_14'), C_273)=D_274 | ~r2_hidden(k4_tarski(D_274, C_273), '#skF_14'))), inference(splitRight, [status(thm)], [c_2002])).
% 10.95/4.18  tff(c_2687, plain, (![C_283]: (k1_funct_1(k2_funct_1('#skF_14'), C_283)='#skF_8'('#skF_14', k2_relat_1('#skF_14'), C_283) | ~r2_hidden(C_283, k2_relat_1('#skF_14')))), inference(resolution, [status(thm)], [c_14, c_2541])).
% 10.95/4.18  tff(c_2742, plain, (k1_funct_1(k2_funct_1('#skF_14'), '#skF_13')='#skF_8'('#skF_14', k2_relat_1('#skF_14'), '#skF_13')), inference(resolution, [status(thm)], [c_56, c_2687])).
% 10.95/4.18  tff(c_69, plain, (![A_75]: (k4_relat_1(A_75)=k2_funct_1(A_75) | ~v2_funct_1(A_75) | ~v1_funct_1(A_75) | ~v1_relat_1(A_75))), inference(cnfTransformation, [status(thm)], [f_65])).
% 10.95/4.18  tff(c_72, plain, (k4_relat_1('#skF_14')=k2_funct_1('#skF_14') | ~v1_funct_1('#skF_14') | ~v1_relat_1('#skF_14')), inference(resolution, [status(thm)], [c_58, c_69])).
% 10.95/4.18  tff(c_75, plain, (k4_relat_1('#skF_14')=k2_funct_1('#skF_14')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_72])).
% 10.95/4.18  tff(c_79, plain, (v1_relat_1(k2_funct_1('#skF_14')) | ~v1_relat_1('#skF_14')), inference(superposition, [status(thm), theory('equality')], [c_75, c_38])).
% 10.95/4.18  tff(c_83, plain, (v1_relat_1(k2_funct_1('#skF_14'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_79])).
% 10.95/4.18  tff(c_172, plain, (![C_106, D_107, A_108]: (r2_hidden(k4_tarski(C_106, D_107), k4_relat_1(A_108)) | ~r2_hidden(k4_tarski(D_107, C_106), A_108) | ~v1_relat_1(k4_relat_1(A_108)) | ~v1_relat_1(A_108))), inference(cnfTransformation, [status(thm)], [f_53])).
% 10.95/4.18  tff(c_187, plain, (![C_106, D_107]: (r2_hidden(k4_tarski(C_106, D_107), k2_funct_1('#skF_14')) | ~r2_hidden(k4_tarski(D_107, C_106), '#skF_14') | ~v1_relat_1(k4_relat_1('#skF_14')) | ~v1_relat_1('#skF_14'))), inference(superposition, [status(thm), theory('equality')], [c_75, c_172])).
% 10.95/4.18  tff(c_194, plain, (![C_109, D_110]: (r2_hidden(k4_tarski(C_109, D_110), k2_funct_1('#skF_14')) | ~r2_hidden(k4_tarski(D_110, C_109), '#skF_14'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_83, c_75, c_187])).
% 10.95/4.18  tff(c_200, plain, (![C_109, D_110]: (k1_funct_1(k2_funct_1('#skF_14'), C_109)=D_110 | ~v1_funct_1(k2_funct_1('#skF_14')) | ~v1_relat_1(k2_funct_1('#skF_14')) | ~r2_hidden(k4_tarski(D_110, C_109), '#skF_14'))), inference(resolution, [status(thm)], [c_194, c_50])).
% 10.95/4.18  tff(c_210, plain, (![C_109, D_110]: (k1_funct_1(k2_funct_1('#skF_14'), C_109)=D_110 | ~v1_funct_1(k2_funct_1('#skF_14')) | ~r2_hidden(k4_tarski(D_110, C_109), '#skF_14'))), inference(demodulation, [status(thm), theory('equality')], [c_83, c_200])).
% 10.95/4.18  tff(c_605, plain, (~v1_funct_1(k2_funct_1('#skF_14'))), inference(splitLeft, [status(thm)], [c_210])).
% 10.95/4.18  tff(c_629, plain, (~v1_funct_1('#skF_14') | ~v1_relat_1('#skF_14')), inference(resolution, [status(thm)], [c_42, c_605])).
% 10.95/4.18  tff(c_633, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_629])).
% 10.95/4.18  tff(c_636, plain, (![C_138, D_139]: (k1_funct_1(k2_funct_1('#skF_14'), C_138)=D_139 | ~r2_hidden(k4_tarski(D_139, C_138), '#skF_14'))), inference(splitRight, [status(thm)], [c_210])).
% 10.95/4.18  tff(c_753, plain, (![C_147]: (k1_funct_1(k2_funct_1('#skF_14'), C_147)='#skF_8'('#skF_14', k2_relat_1('#skF_14'), C_147) | ~r2_hidden(C_147, k2_relat_1('#skF_14')))), inference(resolution, [status(thm)], [c_14, c_636])).
% 10.95/4.18  tff(c_808, plain, (k1_funct_1(k2_funct_1('#skF_14'), '#skF_13')='#skF_8'('#skF_14', k2_relat_1('#skF_14'), '#skF_13')), inference(resolution, [status(thm)], [c_56, c_753])).
% 10.95/4.18  tff(c_54, plain, (k1_funct_1(k5_relat_1(k2_funct_1('#skF_14'), '#skF_14'), '#skF_13')!='#skF_13' | k1_funct_1('#skF_14', k1_funct_1(k2_funct_1('#skF_14'), '#skF_13'))!='#skF_13'), inference(cnfTransformation, [status(thm)], [f_109])).
% 10.95/4.18  tff(c_68, plain, (k1_funct_1('#skF_14', k1_funct_1(k2_funct_1('#skF_14'), '#skF_13'))!='#skF_13'), inference(splitLeft, [status(thm)], [c_54])).
% 10.95/4.18  tff(c_809, plain, (k1_funct_1('#skF_14', '#skF_8'('#skF_14', k2_relat_1('#skF_14'), '#skF_13'))!='#skF_13'), inference(demodulation, [status(thm), theory('equality')], [c_808, c_68])).
% 10.95/4.18  tff(c_4, plain, (![C_16, A_1, D_19]: (r2_hidden(C_16, k1_relat_1(A_1)) | ~r2_hidden(k4_tarski(C_16, D_19), A_1))), inference(cnfTransformation, [status(thm)], [f_33])).
% 10.95/4.18  tff(c_213, plain, (![C_111, D_112]: (r2_hidden(C_111, k1_relat_1(k2_funct_1('#skF_14'))) | ~r2_hidden(k4_tarski(D_112, C_111), '#skF_14'))), inference(resolution, [status(thm)], [c_194, c_4])).
% 10.95/4.18  tff(c_226, plain, (![C_35]: (r2_hidden(C_35, k1_relat_1(k2_funct_1('#skF_14'))) | ~r2_hidden(C_35, k2_relat_1('#skF_14')))), inference(resolution, [status(thm)], [c_14, c_213])).
% 10.95/4.18  tff(c_635, plain, (v1_funct_1(k2_funct_1('#skF_14'))), inference(splitRight, [status(thm)], [c_210])).
% 10.95/4.18  tff(c_116, plain, (![A_91, C_92]: (r2_hidden(k4_tarski(A_91, k1_funct_1(C_92, A_91)), C_92) | ~r2_hidden(A_91, k1_relat_1(C_92)) | ~v1_funct_1(C_92) | ~v1_relat_1(C_92))), inference(cnfTransformation, [status(thm)], [f_96])).
% 10.95/4.18  tff(c_16, plain, (![C_35, A_20, D_38]: (r2_hidden(C_35, k2_relat_1(A_20)) | ~r2_hidden(k4_tarski(D_38, C_35), A_20))), inference(cnfTransformation, [status(thm)], [f_41])).
% 10.95/4.18  tff(c_129, plain, (![C_92, A_91]: (r2_hidden(k1_funct_1(C_92, A_91), k2_relat_1(C_92)) | ~r2_hidden(A_91, k1_relat_1(C_92)) | ~v1_funct_1(C_92) | ~v1_relat_1(C_92))), inference(resolution, [status(thm)], [c_116, c_16])).
% 10.95/4.18  tff(c_813, plain, (r2_hidden('#skF_8'('#skF_14', k2_relat_1('#skF_14'), '#skF_13'), k2_relat_1(k2_funct_1('#skF_14'))) | ~r2_hidden('#skF_13', k1_relat_1(k2_funct_1('#skF_14'))) | ~v1_funct_1(k2_funct_1('#skF_14')) | ~v1_relat_1(k2_funct_1('#skF_14'))), inference(superposition, [status(thm), theory('equality')], [c_808, c_129])).
% 10.95/4.18  tff(c_820, plain, (r2_hidden('#skF_8'('#skF_14', k2_relat_1('#skF_14'), '#skF_13'), k2_relat_1(k2_funct_1('#skF_14'))) | ~r2_hidden('#skF_13', k1_relat_1(k2_funct_1('#skF_14')))), inference(demodulation, [status(thm), theory('equality')], [c_83, c_635, c_813])).
% 10.95/4.18  tff(c_928, plain, (~r2_hidden('#skF_13', k1_relat_1(k2_funct_1('#skF_14')))), inference(splitLeft, [status(thm)], [c_820])).
% 10.95/4.18  tff(c_931, plain, (~r2_hidden('#skF_13', k2_relat_1('#skF_14'))), inference(resolution, [status(thm)], [c_226, c_928])).
% 10.95/4.18  tff(c_935, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_931])).
% 10.95/4.18  tff(c_937, plain, (r2_hidden('#skF_13', k1_relat_1(k2_funct_1('#skF_14')))), inference(splitRight, [status(thm)], [c_820])).
% 10.95/4.18  tff(c_48, plain, (![A_63, C_65]: (r2_hidden(k4_tarski(A_63, k1_funct_1(C_65, A_63)), C_65) | ~r2_hidden(A_63, k1_relat_1(C_65)) | ~v1_funct_1(C_65) | ~v1_relat_1(C_65))), inference(cnfTransformation, [status(thm)], [f_96])).
% 10.95/4.18  tff(c_816, plain, (r2_hidden(k4_tarski('#skF_13', '#skF_8'('#skF_14', k2_relat_1('#skF_14'), '#skF_13')), k2_funct_1('#skF_14')) | ~r2_hidden('#skF_13', k1_relat_1(k2_funct_1('#skF_14'))) | ~v1_funct_1(k2_funct_1('#skF_14')) | ~v1_relat_1(k2_funct_1('#skF_14'))), inference(superposition, [status(thm), theory('equality')], [c_808, c_48])).
% 10.95/4.18  tff(c_822, plain, (r2_hidden(k4_tarski('#skF_13', '#skF_8'('#skF_14', k2_relat_1('#skF_14'), '#skF_13')), k2_funct_1('#skF_14')) | ~r2_hidden('#skF_13', k1_relat_1(k2_funct_1('#skF_14')))), inference(demodulation, [status(thm), theory('equality')], [c_83, c_635, c_816])).
% 10.95/4.18  tff(c_944, plain, (r2_hidden(k4_tarski('#skF_13', '#skF_8'('#skF_14', k2_relat_1('#skF_14'), '#skF_13')), k2_funct_1('#skF_14'))), inference(demodulation, [status(thm), theory('equality')], [c_937, c_822])).
% 10.95/4.18  tff(c_133, plain, (![D_101, C_102, A_103]: (r2_hidden(k4_tarski(D_101, C_102), A_103) | ~r2_hidden(k4_tarski(C_102, D_101), k4_relat_1(A_103)) | ~v1_relat_1(k4_relat_1(A_103)) | ~v1_relat_1(A_103))), inference(cnfTransformation, [status(thm)], [f_53])).
% 10.95/4.18  tff(c_148, plain, (![D_101, C_102]: (r2_hidden(k4_tarski(D_101, C_102), '#skF_14') | ~r2_hidden(k4_tarski(C_102, D_101), k2_funct_1('#skF_14')) | ~v1_relat_1(k4_relat_1('#skF_14')) | ~v1_relat_1('#skF_14'))), inference(superposition, [status(thm), theory('equality')], [c_75, c_133])).
% 10.95/4.18  tff(c_153, plain, (![D_101, C_102]: (r2_hidden(k4_tarski(D_101, C_102), '#skF_14') | ~r2_hidden(k4_tarski(C_102, D_101), k2_funct_1('#skF_14')))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_83, c_75, c_148])).
% 10.95/4.18  tff(c_957, plain, (r2_hidden(k4_tarski('#skF_8'('#skF_14', k2_relat_1('#skF_14'), '#skF_13'), '#skF_13'), '#skF_14')), inference(resolution, [status(thm)], [c_944, c_153])).
% 10.95/4.18  tff(c_973, plain, (k1_funct_1('#skF_14', '#skF_8'('#skF_14', k2_relat_1('#skF_14'), '#skF_13'))='#skF_13' | ~v1_funct_1('#skF_14') | ~v1_relat_1('#skF_14')), inference(resolution, [status(thm)], [c_957, c_50])).
% 10.95/4.18  tff(c_988, plain, (k1_funct_1('#skF_14', '#skF_8'('#skF_14', k2_relat_1('#skF_14'), '#skF_13'))='#skF_13'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_973])).
% 10.95/4.18  tff(c_990, plain, $false, inference(negUnitSimplification, [status(thm)], [c_809, c_988])).
% 10.95/4.18  tff(c_992, plain, (k1_funct_1('#skF_14', k1_funct_1(k2_funct_1('#skF_14'), '#skF_13'))='#skF_13'), inference(splitRight, [status(thm)], [c_54])).
% 10.95/4.18  tff(c_2746, plain, (k1_funct_1('#skF_14', '#skF_8'('#skF_14', k2_relat_1('#skF_14'), '#skF_13'))='#skF_13'), inference(demodulation, [status(thm), theory('equality')], [c_2742, c_992])).
% 10.95/4.18  tff(c_2461, plain, (v1_funct_1(k2_funct_1('#skF_14'))), inference(splitRight, [status(thm)], [c_2002])).
% 10.95/4.18  tff(c_1030, plain, (![A_171, C_172]: (r2_hidden(k4_tarski('#skF_8'(A_171, k2_relat_1(A_171), C_172), C_172), A_171) | ~r2_hidden(C_172, k2_relat_1(A_171)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 10.95/4.18  tff(c_1041, plain, (![A_171, C_172]: (r2_hidden('#skF_8'(A_171, k2_relat_1(A_171), C_172), k1_relat_1(A_171)) | ~r2_hidden(C_172, k2_relat_1(A_171)))), inference(resolution, [status(thm)], [c_1030, c_4])).
% 10.95/4.18  tff(c_1072, plain, (![C_185, D_186, A_187]: (r2_hidden(k4_tarski(C_185, D_186), k4_relat_1(A_187)) | ~r2_hidden(k4_tarski(D_186, C_185), A_187) | ~v1_relat_1(k4_relat_1(A_187)) | ~v1_relat_1(A_187))), inference(cnfTransformation, [status(thm)], [f_53])).
% 10.95/4.18  tff(c_1084, plain, (![C_185, D_186]: (r2_hidden(k4_tarski(C_185, D_186), k2_funct_1('#skF_14')) | ~r2_hidden(k4_tarski(D_186, C_185), '#skF_14') | ~v1_relat_1(k4_relat_1('#skF_14')) | ~v1_relat_1('#skF_14'))), inference(superposition, [status(thm), theory('equality')], [c_1003, c_1072])).
% 10.95/4.18  tff(c_1090, plain, (![C_188, D_189]: (r2_hidden(k4_tarski(C_188, D_189), k2_funct_1('#skF_14')) | ~r2_hidden(k4_tarski(D_189, C_188), '#skF_14'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_1020, c_1003, c_1084])).
% 10.95/4.18  tff(c_1093, plain, (![C_188, D_189]: (k1_funct_1(k2_funct_1('#skF_14'), C_188)=D_189 | ~v1_funct_1(k2_funct_1('#skF_14')) | ~v1_relat_1(k2_funct_1('#skF_14')) | ~r2_hidden(k4_tarski(D_189, C_188), '#skF_14'))), inference(resolution, [status(thm)], [c_1090, c_50])).
% 10.95/4.18  tff(c_1102, plain, (![C_188, D_189]: (k1_funct_1(k2_funct_1('#skF_14'), C_188)=D_189 | ~v1_funct_1(k2_funct_1('#skF_14')) | ~r2_hidden(k4_tarski(D_189, C_188), '#skF_14'))), inference(demodulation, [status(thm), theory('equality')], [c_1020, c_1093])).
% 10.95/4.18  tff(c_1567, plain, (~v1_funct_1(k2_funct_1('#skF_14'))), inference(splitLeft, [status(thm)], [c_1102])).
% 10.95/4.18  tff(c_1627, plain, (~v1_funct_1('#skF_14') | ~v1_relat_1('#skF_14')), inference(resolution, [status(thm)], [c_42, c_1567])).
% 10.95/4.18  tff(c_1631, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_1627])).
% 10.95/4.18  tff(c_1634, plain, (![C_223, D_224]: (k1_funct_1(k2_funct_1('#skF_14'), C_223)=D_224 | ~r2_hidden(k4_tarski(D_224, C_223), '#skF_14'))), inference(splitRight, [status(thm)], [c_1102])).
% 10.95/4.18  tff(c_1741, plain, (![C_230]: (k1_funct_1(k2_funct_1('#skF_14'), C_230)='#skF_8'('#skF_14', k2_relat_1('#skF_14'), C_230) | ~r2_hidden(C_230, k2_relat_1('#skF_14')))), inference(resolution, [status(thm)], [c_14, c_1634])).
% 10.95/4.18  tff(c_1791, plain, (k1_funct_1(k2_funct_1('#skF_14'), '#skF_13')='#skF_8'('#skF_14', k2_relat_1('#skF_14'), '#skF_13')), inference(resolution, [status(thm)], [c_56, c_1741])).
% 10.95/4.18  tff(c_1046, plain, (![A_181, C_182]: (r2_hidden(k4_tarski(A_181, k1_funct_1(C_182, A_181)), C_182) | ~r2_hidden(A_181, k1_relat_1(C_182)) | ~v1_funct_1(C_182) | ~v1_relat_1(C_182))), inference(cnfTransformation, [status(thm)], [f_96])).
% 10.95/4.18  tff(c_1058, plain, (r2_hidden(k4_tarski(k1_funct_1(k2_funct_1('#skF_14'), '#skF_13'), '#skF_13'), '#skF_14') | ~r2_hidden(k1_funct_1(k2_funct_1('#skF_14'), '#skF_13'), k1_relat_1('#skF_14')) | ~v1_funct_1('#skF_14') | ~v1_relat_1('#skF_14')), inference(superposition, [status(thm), theory('equality')], [c_992, c_1046])).
% 10.95/4.18  tff(c_1064, plain, (r2_hidden(k4_tarski(k1_funct_1(k2_funct_1('#skF_14'), '#skF_13'), '#skF_13'), '#skF_14') | ~r2_hidden(k1_funct_1(k2_funct_1('#skF_14'), '#skF_13'), k1_relat_1('#skF_14'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_1058])).
% 10.95/4.18  tff(c_1071, plain, (~r2_hidden(k1_funct_1(k2_funct_1('#skF_14'), '#skF_13'), k1_relat_1('#skF_14'))), inference(splitLeft, [status(thm)], [c_1064])).
% 10.95/4.18  tff(c_1859, plain, (~r2_hidden('#skF_8'('#skF_14', k2_relat_1('#skF_14'), '#skF_13'), k1_relat_1('#skF_14'))), inference(demodulation, [status(thm), theory('equality')], [c_1791, c_1071])).
% 10.95/4.18  tff(c_1902, plain, (~r2_hidden('#skF_13', k2_relat_1('#skF_14'))), inference(resolution, [status(thm)], [c_1041, c_1859])).
% 10.95/4.18  tff(c_1906, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_1902])).
% 10.95/4.18  tff(c_1907, plain, (r2_hidden(k4_tarski(k1_funct_1(k2_funct_1('#skF_14'), '#skF_13'), '#skF_13'), '#skF_14')), inference(splitRight, [status(thm)], [c_1064])).
% 10.95/4.18  tff(c_2028, plain, (![C_245, D_246]: (r2_hidden(C_245, k1_relat_1(k2_funct_1('#skF_14'))) | ~r2_hidden(k4_tarski(D_246, C_245), '#skF_14'))), inference(resolution, [status(thm)], [c_1986, c_4])).
% 10.95/4.18  tff(c_2044, plain, (r2_hidden('#skF_13', k1_relat_1(k2_funct_1('#skF_14')))), inference(resolution, [status(thm)], [c_1907, c_2028])).
% 10.95/4.18  tff(c_2825, plain, (![B_284, C_285, A_286]: (k1_funct_1(k5_relat_1(B_284, C_285), A_286)=k1_funct_1(C_285, k1_funct_1(B_284, A_286)) | ~r2_hidden(A_286, k1_relat_1(B_284)) | ~v1_funct_1(C_285) | ~v1_relat_1(C_285) | ~v1_funct_1(B_284) | ~v1_relat_1(B_284))), inference(cnfTransformation, [status(thm)], [f_86])).
% 10.95/4.18  tff(c_2842, plain, (![C_285]: (k1_funct_1(k5_relat_1(k2_funct_1('#skF_14'), C_285), '#skF_13')=k1_funct_1(C_285, k1_funct_1(k2_funct_1('#skF_14'), '#skF_13')) | ~v1_funct_1(C_285) | ~v1_relat_1(C_285) | ~v1_funct_1(k2_funct_1('#skF_14')) | ~v1_relat_1(k2_funct_1('#skF_14')))), inference(resolution, [status(thm)], [c_2044, c_2825])).
% 10.95/4.18  tff(c_16584, plain, (![C_586]: (k1_funct_1(k5_relat_1(k2_funct_1('#skF_14'), C_586), '#skF_13')=k1_funct_1(C_586, '#skF_8'('#skF_14', k2_relat_1('#skF_14'), '#skF_13')) | ~v1_funct_1(C_586) | ~v1_relat_1(C_586))), inference(demodulation, [status(thm), theory('equality')], [c_1020, c_2461, c_2742, c_2842])).
% 10.95/4.18  tff(c_991, plain, (k1_funct_1(k5_relat_1(k2_funct_1('#skF_14'), '#skF_14'), '#skF_13')!='#skF_13'), inference(splitRight, [status(thm)], [c_54])).
% 10.95/4.18  tff(c_16596, plain, (k1_funct_1('#skF_14', '#skF_8'('#skF_14', k2_relat_1('#skF_14'), '#skF_13'))!='#skF_13' | ~v1_funct_1('#skF_14') | ~v1_relat_1('#skF_14')), inference(superposition, [status(thm), theory('equality')], [c_16584, c_991])).
% 10.95/4.18  tff(c_16603, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_2746, c_16596])).
% 10.95/4.18  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.95/4.18  
% 10.95/4.18  Inference rules
% 10.95/4.18  ----------------------
% 10.95/4.18  #Ref     : 0
% 10.95/4.18  #Sup     : 3669
% 10.95/4.18  #Fact    : 0
% 10.95/4.18  #Define  : 0
% 10.95/4.18  #Split   : 8
% 10.95/4.18  #Chain   : 0
% 10.95/4.18  #Close   : 0
% 10.95/4.18  
% 10.95/4.18  Ordering : KBO
% 10.95/4.18  
% 10.95/4.18  Simplification rules
% 10.95/4.18  ----------------------
% 10.95/4.18  #Subsume      : 223
% 10.95/4.18  #Demod        : 855
% 10.95/4.18  #Tautology    : 255
% 10.95/4.18  #SimpNegUnit  : 1
% 10.95/4.18  #BackRed      : 7
% 10.95/4.18  
% 10.95/4.18  #Partial instantiations: 0
% 10.95/4.18  #Strategies tried      : 1
% 10.95/4.18  
% 10.95/4.18  Timing (in seconds)
% 10.95/4.18  ----------------------
% 10.95/4.18  Preprocessing        : 0.42
% 10.95/4.18  Parsing              : 0.23
% 10.95/4.18  CNF conversion       : 0.03
% 10.95/4.18  Main loop            : 2.97
% 10.95/4.18  Inferencing          : 0.79
% 10.95/4.18  Reduction            : 0.72
% 10.95/4.18  Demodulation         : 0.49
% 10.95/4.18  BG Simplification    : 0.12
% 10.95/4.18  Subsumption          : 1.10
% 10.95/4.18  Abstraction          : 0.16
% 10.95/4.18  MUC search           : 0.00
% 10.95/4.18  Cooper               : 0.00
% 10.95/4.18  Total                : 3.44
% 10.95/4.18  Index Insertion      : 0.00
% 10.95/4.18  Index Deletion       : 0.00
% 10.95/4.18  Index Matching       : 0.00
% 10.95/4.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
