%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:45 EST 2020

% Result     : Theorem 4.19s
% Output     : CNFRefutation 4.45s
% Verified   : 
% Statistics : Number of formulae       :  133 ( 934 expanded)
%              Number of leaves         :   33 ( 354 expanded)
%              Depth                    :   17
%              Number of atoms          :  296 (2890 expanded)
%              Number of equality atoms :   31 ( 710 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > k4_tarski > k1_funct_1 > #nlpp > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_6 > #skF_3 > #skF_10 > #skF_9 > #skF_2 > #skF_8 > #skF_7 > #skF_1 > #skF_5 > #skF_4

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

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_116,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ( ( v2_funct_1(B)
            & r2_hidden(A,k2_relat_1(B)) )
         => ( A = k1_funct_1(B,k1_funct_1(k2_funct_1(B),A))
            & A = k1_funct_1(k5_relat_1(k2_funct_1(B),B),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_funct_1)).

tff(f_64,axiom,(
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

tff(f_103,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

tff(f_72,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(A) = k4_relat_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).

tff(f_41,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => v1_relat_1(k4_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).

tff(f_37,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( B = k4_relat_1(A)
          <=> ! [C,D] :
                ( r2_hidden(k4_tarski(C,D),B)
              <=> r2_hidden(k4_tarski(D,C),A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_relat_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
       => ( r2_hidden(A,k1_relat_1(C))
          & r2_hidden(B,k2_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_relat_1)).

tff(f_80,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_93,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ! [C] :
          ( ( v1_relat_1(C)
            & v1_funct_1(C) )
         => ( r2_hidden(A,k1_relat_1(B))
           => k1_funct_1(k5_relat_1(B,C),A) = k1_funct_1(C,k1_funct_1(B,A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_funct_1)).

tff(c_60,plain,(
    v1_relat_1('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_58,plain,(
    v1_funct_1('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_54,plain,(
    r2_hidden('#skF_9',k2_relat_1('#skF_10')) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_24,plain,(
    ! [A_22,C_58] :
      ( r2_hidden('#skF_8'(A_22,k2_relat_1(A_22),C_58),k1_relat_1(A_22))
      | ~ r2_hidden(C_58,k2_relat_1(A_22))
      | ~ v1_funct_1(A_22)
      | ~ v1_relat_1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_22,plain,(
    ! [A_22,C_58] :
      ( k1_funct_1(A_22,'#skF_8'(A_22,k2_relat_1(A_22),C_58)) = C_58
      | ~ r2_hidden(C_58,k2_relat_1(A_22))
      | ~ v1_funct_1(A_22)
      | ~ v1_relat_1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_46,plain,(
    ! [A_68,C_70] :
      ( r2_hidden(k4_tarski(A_68,k1_funct_1(C_70,A_68)),C_70)
      | ~ r2_hidden(A_68,k1_relat_1(C_70))
      | ~ v1_funct_1(C_70)
      | ~ v1_relat_1(C_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_56,plain,(
    v2_funct_1('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_64,plain,(
    ! [A_74] :
      ( k4_relat_1(A_74) = k2_funct_1(A_74)
      | ~ v2_funct_1(A_74)
      | ~ v1_funct_1(A_74)
      | ~ v1_relat_1(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_67,plain,
    ( k4_relat_1('#skF_10') = k2_funct_1('#skF_10')
    | ~ v1_funct_1('#skF_10')
    | ~ v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_56,c_64])).

tff(c_70,plain,(
    k4_relat_1('#skF_10') = k2_funct_1('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_67])).

tff(c_14,plain,(
    ! [A_18] :
      ( v1_relat_1(k4_relat_1(A_18))
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_74,plain,
    ( v1_relat_1(k2_funct_1('#skF_10'))
    | ~ v1_relat_1('#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_14])).

tff(c_78,plain,(
    v1_relat_1(k2_funct_1('#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_74])).

tff(c_115,plain,(
    ! [C_92,D_93,A_94] :
      ( r2_hidden(k4_tarski(C_92,D_93),k4_relat_1(A_94))
      | ~ r2_hidden(k4_tarski(D_93,C_92),A_94)
      | ~ v1_relat_1(k4_relat_1(A_94))
      | ~ v1_relat_1(A_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_127,plain,(
    ! [C_92,D_93] :
      ( r2_hidden(k4_tarski(C_92,D_93),k2_funct_1('#skF_10'))
      | ~ r2_hidden(k4_tarski(D_93,C_92),'#skF_10')
      | ~ v1_relat_1(k4_relat_1('#skF_10'))
      | ~ v1_relat_1('#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_115])).

tff(c_133,plain,(
    ! [C_95,D_96] :
      ( r2_hidden(k4_tarski(C_95,D_96),k2_funct_1('#skF_10'))
      | ~ r2_hidden(k4_tarski(D_96,C_95),'#skF_10') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_78,c_70,c_127])).

tff(c_18,plain,(
    ! [A_19,C_21,B_20] :
      ( r2_hidden(A_19,k1_relat_1(C_21))
      | ~ r2_hidden(k4_tarski(A_19,B_20),C_21)
      | ~ v1_relat_1(C_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_142,plain,(
    ! [C_95,D_96] :
      ( r2_hidden(C_95,k1_relat_1(k2_funct_1('#skF_10')))
      | ~ v1_relat_1(k2_funct_1('#skF_10'))
      | ~ r2_hidden(k4_tarski(D_96,C_95),'#skF_10') ) ),
    inference(resolution,[status(thm)],[c_133,c_18])).

tff(c_175,plain,(
    ! [C_100,D_101] :
      ( r2_hidden(C_100,k1_relat_1(k2_funct_1('#skF_10')))
      | ~ r2_hidden(k4_tarski(D_101,C_100),'#skF_10') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_142])).

tff(c_178,plain,(
    ! [A_68] :
      ( r2_hidden(k1_funct_1('#skF_10',A_68),k1_relat_1(k2_funct_1('#skF_10')))
      | ~ r2_hidden(A_68,k1_relat_1('#skF_10'))
      | ~ v1_funct_1('#skF_10')
      | ~ v1_relat_1('#skF_10') ) ),
    inference(resolution,[status(thm)],[c_46,c_175])).

tff(c_182,plain,(
    ! [A_102] :
      ( r2_hidden(k1_funct_1('#skF_10',A_102),k1_relat_1(k2_funct_1('#skF_10')))
      | ~ r2_hidden(A_102,k1_relat_1('#skF_10')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_178])).

tff(c_186,plain,(
    ! [C_58] :
      ( r2_hidden(C_58,k1_relat_1(k2_funct_1('#skF_10')))
      | ~ r2_hidden('#skF_8'('#skF_10',k2_relat_1('#skF_10'),C_58),k1_relat_1('#skF_10'))
      | ~ r2_hidden(C_58,k2_relat_1('#skF_10'))
      | ~ v1_funct_1('#skF_10')
      | ~ v1_relat_1('#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_182])).

tff(c_777,plain,(
    ! [C_147] :
      ( r2_hidden(C_147,k1_relat_1(k2_funct_1('#skF_10')))
      | ~ r2_hidden('#skF_8'('#skF_10',k2_relat_1('#skF_10'),C_147),k1_relat_1('#skF_10'))
      | ~ r2_hidden(C_147,k2_relat_1('#skF_10')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_186])).

tff(c_781,plain,(
    ! [C_58] :
      ( r2_hidden(C_58,k1_relat_1(k2_funct_1('#skF_10')))
      | ~ r2_hidden(C_58,k2_relat_1('#skF_10'))
      | ~ v1_funct_1('#skF_10')
      | ~ v1_relat_1('#skF_10') ) ),
    inference(resolution,[status(thm)],[c_24,c_777])).

tff(c_785,plain,(
    ! [C_148] :
      ( r2_hidden(C_148,k1_relat_1(k2_funct_1('#skF_10')))
      | ~ r2_hidden(C_148,k2_relat_1('#skF_10')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_781])).

tff(c_40,plain,(
    ! [A_63] :
      ( v1_funct_1(k2_funct_1(A_63))
      | ~ v1_funct_1(A_63)
      | ~ v1_relat_1(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_48,plain,(
    ! [C_70,A_68,B_69] :
      ( k1_funct_1(C_70,A_68) = B_69
      | ~ r2_hidden(k4_tarski(A_68,B_69),C_70)
      | ~ v1_funct_1(C_70)
      | ~ v1_relat_1(C_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_136,plain,(
    ! [C_95,D_96] :
      ( k1_funct_1(k2_funct_1('#skF_10'),C_95) = D_96
      | ~ v1_funct_1(k2_funct_1('#skF_10'))
      | ~ v1_relat_1(k2_funct_1('#skF_10'))
      | ~ r2_hidden(k4_tarski(D_96,C_95),'#skF_10') ) ),
    inference(resolution,[status(thm)],[c_133,c_48])).

tff(c_145,plain,(
    ! [C_95,D_96] :
      ( k1_funct_1(k2_funct_1('#skF_10'),C_95) = D_96
      | ~ v1_funct_1(k2_funct_1('#skF_10'))
      | ~ r2_hidden(k4_tarski(D_96,C_95),'#skF_10') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_136])).

tff(c_216,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_10')) ),
    inference(splitLeft,[status(thm)],[c_145])).

tff(c_219,plain,
    ( ~ v1_funct_1('#skF_10')
    | ~ v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_40,c_216])).

tff(c_223,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_219])).

tff(c_225,plain,(
    v1_funct_1(k2_funct_1('#skF_10')) ),
    inference(splitRight,[status(thm)],[c_145])).

tff(c_189,plain,(
    ! [D_103,C_104,A_105] :
      ( r2_hidden(k4_tarski(D_103,C_104),A_105)
      | ~ r2_hidden(k4_tarski(C_104,D_103),k4_relat_1(A_105))
      | ~ v1_relat_1(k4_relat_1(A_105))
      | ~ v1_relat_1(A_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_199,plain,(
    ! [D_103,C_104] :
      ( r2_hidden(k4_tarski(D_103,C_104),'#skF_10')
      | ~ r2_hidden(k4_tarski(C_104,D_103),k2_funct_1('#skF_10'))
      | ~ v1_relat_1(k4_relat_1('#skF_10'))
      | ~ v1_relat_1('#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_189])).

tff(c_204,plain,(
    ! [D_106,C_107] :
      ( r2_hidden(k4_tarski(D_106,C_107),'#skF_10')
      | ~ r2_hidden(k4_tarski(C_107,D_106),k2_funct_1('#skF_10')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_78,c_70,c_199])).

tff(c_211,plain,(
    ! [A_68] :
      ( r2_hidden(k4_tarski(k1_funct_1(k2_funct_1('#skF_10'),A_68),A_68),'#skF_10')
      | ~ r2_hidden(A_68,k1_relat_1(k2_funct_1('#skF_10')))
      | ~ v1_funct_1(k2_funct_1('#skF_10'))
      | ~ v1_relat_1(k2_funct_1('#skF_10')) ) ),
    inference(resolution,[status(thm)],[c_46,c_204])).

tff(c_215,plain,(
    ! [A_68] :
      ( r2_hidden(k4_tarski(k1_funct_1(k2_funct_1('#skF_10'),A_68),A_68),'#skF_10')
      | ~ r2_hidden(A_68,k1_relat_1(k2_funct_1('#skF_10')))
      | ~ v1_funct_1(k2_funct_1('#skF_10')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_211])).

tff(c_226,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_10')) ),
    inference(splitLeft,[status(thm)],[c_215])).

tff(c_228,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_225,c_226])).

tff(c_266,plain,(
    ! [A_113] :
      ( r2_hidden(k4_tarski(k1_funct_1(k2_funct_1('#skF_10'),A_113),A_113),'#skF_10')
      | ~ r2_hidden(A_113,k1_relat_1(k2_funct_1('#skF_10'))) ) ),
    inference(splitRight,[status(thm)],[c_215])).

tff(c_276,plain,(
    ! [A_113] :
      ( k1_funct_1('#skF_10',k1_funct_1(k2_funct_1('#skF_10'),A_113)) = A_113
      | ~ v1_funct_1('#skF_10')
      | ~ v1_relat_1('#skF_10')
      | ~ r2_hidden(A_113,k1_relat_1(k2_funct_1('#skF_10'))) ) ),
    inference(resolution,[status(thm)],[c_266,c_48])).

tff(c_296,plain,(
    ! [A_113] :
      ( k1_funct_1('#skF_10',k1_funct_1(k2_funct_1('#skF_10'),A_113)) = A_113
      | ~ r2_hidden(A_113,k1_relat_1(k2_funct_1('#skF_10'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_276])).

tff(c_821,plain,(
    ! [C_149] :
      ( k1_funct_1('#skF_10',k1_funct_1(k2_funct_1('#skF_10'),C_149)) = C_149
      | ~ r2_hidden(C_149,k2_relat_1('#skF_10')) ) ),
    inference(resolution,[status(thm)],[c_785,c_296])).

tff(c_52,plain,
    ( k1_funct_1(k5_relat_1(k2_funct_1('#skF_10'),'#skF_10'),'#skF_9') != '#skF_9'
    | k1_funct_1('#skF_10',k1_funct_1(k2_funct_1('#skF_10'),'#skF_9')) != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_80,plain,(
    k1_funct_1('#skF_10',k1_funct_1(k2_funct_1('#skF_10'),'#skF_9')) != '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_854,plain,(
    ~ r2_hidden('#skF_9',k2_relat_1('#skF_10')) ),
    inference(superposition,[status(thm),theory(equality)],[c_821,c_80])).

tff(c_883,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_854])).

tff(c_885,plain,(
    k1_funct_1('#skF_10',k1_funct_1(k2_funct_1('#skF_10'),'#skF_9')) = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_1699,plain,(
    ! [C_232,D_233,A_234] :
      ( r2_hidden(k4_tarski(C_232,D_233),k4_relat_1(A_234))
      | ~ r2_hidden(k4_tarski(D_233,C_232),A_234)
      | ~ v1_relat_1(k4_relat_1(A_234))
      | ~ v1_relat_1(A_234) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1714,plain,(
    ! [C_232,D_233] :
      ( r2_hidden(k4_tarski(C_232,D_233),k2_funct_1('#skF_10'))
      | ~ r2_hidden(k4_tarski(D_233,C_232),'#skF_10')
      | ~ v1_relat_1(k4_relat_1('#skF_10'))
      | ~ v1_relat_1('#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_1699])).

tff(c_1721,plain,(
    ! [C_235,D_236] :
      ( r2_hidden(k4_tarski(C_235,D_236),k2_funct_1('#skF_10'))
      | ~ r2_hidden(k4_tarski(D_236,C_235),'#skF_10') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_78,c_70,c_1714])).

tff(c_1727,plain,(
    ! [C_235,D_236] :
      ( k1_funct_1(k2_funct_1('#skF_10'),C_235) = D_236
      | ~ v1_funct_1(k2_funct_1('#skF_10'))
      | ~ v1_relat_1(k2_funct_1('#skF_10'))
      | ~ r2_hidden(k4_tarski(D_236,C_235),'#skF_10') ) ),
    inference(resolution,[status(thm)],[c_1721,c_48])).

tff(c_1737,plain,(
    ! [C_235,D_236] :
      ( k1_funct_1(k2_funct_1('#skF_10'),C_235) = D_236
      | ~ v1_funct_1(k2_funct_1('#skF_10'))
      | ~ r2_hidden(k4_tarski(D_236,C_235),'#skF_10') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_1727])).

tff(c_1793,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_10')) ),
    inference(splitLeft,[status(thm)],[c_1737])).

tff(c_1796,plain,
    ( ~ v1_funct_1('#skF_10')
    | ~ v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_40,c_1793])).

tff(c_1800,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_1796])).

tff(c_1802,plain,(
    v1_funct_1(k2_funct_1('#skF_10')) ),
    inference(splitRight,[status(thm)],[c_1737])).

tff(c_953,plain,(
    ! [C_170,D_171,A_172] :
      ( r2_hidden(k4_tarski(C_170,D_171),k4_relat_1(A_172))
      | ~ r2_hidden(k4_tarski(D_171,C_170),A_172)
      | ~ v1_relat_1(k4_relat_1(A_172))
      | ~ v1_relat_1(A_172) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_968,plain,(
    ! [C_170,D_171] :
      ( r2_hidden(k4_tarski(C_170,D_171),k2_funct_1('#skF_10'))
      | ~ r2_hidden(k4_tarski(D_171,C_170),'#skF_10')
      | ~ v1_relat_1(k4_relat_1('#skF_10'))
      | ~ v1_relat_1('#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_953])).

tff(c_975,plain,(
    ! [C_173,D_174] :
      ( r2_hidden(k4_tarski(C_173,D_174),k2_funct_1('#skF_10'))
      | ~ r2_hidden(k4_tarski(D_174,C_173),'#skF_10') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_78,c_70,c_968])).

tff(c_987,plain,(
    ! [C_173,D_174] :
      ( r2_hidden(C_173,k1_relat_1(k2_funct_1('#skF_10')))
      | ~ v1_relat_1(k2_funct_1('#skF_10'))
      | ~ r2_hidden(k4_tarski(D_174,C_173),'#skF_10') ) ),
    inference(resolution,[status(thm)],[c_975,c_18])).

tff(c_1022,plain,(
    ! [C_180,D_181] :
      ( r2_hidden(C_180,k1_relat_1(k2_funct_1('#skF_10')))
      | ~ r2_hidden(k4_tarski(D_181,C_180),'#skF_10') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_987])).

tff(c_1025,plain,(
    ! [A_68] :
      ( r2_hidden(k1_funct_1('#skF_10',A_68),k1_relat_1(k2_funct_1('#skF_10')))
      | ~ r2_hidden(A_68,k1_relat_1('#skF_10'))
      | ~ v1_funct_1('#skF_10')
      | ~ v1_relat_1('#skF_10') ) ),
    inference(resolution,[status(thm)],[c_46,c_1022])).

tff(c_1029,plain,(
    ! [A_182] :
      ( r2_hidden(k1_funct_1('#skF_10',A_182),k1_relat_1(k2_funct_1('#skF_10')))
      | ~ r2_hidden(A_182,k1_relat_1('#skF_10')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_1025])).

tff(c_1033,plain,(
    ! [C_58] :
      ( r2_hidden(C_58,k1_relat_1(k2_funct_1('#skF_10')))
      | ~ r2_hidden('#skF_8'('#skF_10',k2_relat_1('#skF_10'),C_58),k1_relat_1('#skF_10'))
      | ~ r2_hidden(C_58,k2_relat_1('#skF_10'))
      | ~ v1_funct_1('#skF_10')
      | ~ v1_relat_1('#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_1029])).

tff(c_1579,plain,(
    ! [C_220] :
      ( r2_hidden(C_220,k1_relat_1(k2_funct_1('#skF_10')))
      | ~ r2_hidden('#skF_8'('#skF_10',k2_relat_1('#skF_10'),C_220),k1_relat_1('#skF_10'))
      | ~ r2_hidden(C_220,k2_relat_1('#skF_10')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_1033])).

tff(c_1583,plain,(
    ! [C_58] :
      ( r2_hidden(C_58,k1_relat_1(k2_funct_1('#skF_10')))
      | ~ r2_hidden(C_58,k2_relat_1('#skF_10'))
      | ~ v1_funct_1('#skF_10')
      | ~ v1_relat_1('#skF_10') ) ),
    inference(resolution,[status(thm)],[c_24,c_1579])).

tff(c_1602,plain,(
    ! [C_222] :
      ( r2_hidden(C_222,k1_relat_1(k2_funct_1('#skF_10')))
      | ~ r2_hidden(C_222,k2_relat_1('#skF_10')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_1583])).

tff(c_981,plain,(
    ! [C_173,D_174] :
      ( k1_funct_1(k2_funct_1('#skF_10'),C_173) = D_174
      | ~ v1_funct_1(k2_funct_1('#skF_10'))
      | ~ v1_relat_1(k2_funct_1('#skF_10'))
      | ~ r2_hidden(k4_tarski(D_174,C_173),'#skF_10') ) ),
    inference(resolution,[status(thm)],[c_975,c_48])).

tff(c_991,plain,(
    ! [C_173,D_174] :
      ( k1_funct_1(k2_funct_1('#skF_10'),C_173) = D_174
      | ~ v1_funct_1(k2_funct_1('#skF_10'))
      | ~ r2_hidden(k4_tarski(D_174,C_173),'#skF_10') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_981])).

tff(c_1039,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_10')) ),
    inference(splitLeft,[status(thm)],[c_991])).

tff(c_1042,plain,
    ( ~ v1_funct_1('#skF_10')
    | ~ v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_40,c_1039])).

tff(c_1046,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_1042])).

tff(c_1048,plain,(
    v1_funct_1(k2_funct_1('#skF_10')) ),
    inference(splitRight,[status(thm)],[c_991])).

tff(c_919,plain,(
    ! [D_163,C_164,A_165] :
      ( r2_hidden(k4_tarski(D_163,C_164),A_165)
      | ~ r2_hidden(k4_tarski(C_164,D_163),k4_relat_1(A_165))
      | ~ v1_relat_1(k4_relat_1(A_165))
      | ~ v1_relat_1(A_165) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_926,plain,(
    ! [D_163,C_164] :
      ( r2_hidden(k4_tarski(D_163,C_164),'#skF_10')
      | ~ r2_hidden(k4_tarski(C_164,D_163),k2_funct_1('#skF_10'))
      | ~ v1_relat_1(k4_relat_1('#skF_10'))
      | ~ v1_relat_1('#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_919])).

tff(c_930,plain,(
    ! [D_166,C_167] :
      ( r2_hidden(k4_tarski(D_166,C_167),'#skF_10')
      | ~ r2_hidden(k4_tarski(C_167,D_166),k2_funct_1('#skF_10')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_78,c_70,c_926])).

tff(c_934,plain,(
    ! [A_68] :
      ( r2_hidden(k4_tarski(k1_funct_1(k2_funct_1('#skF_10'),A_68),A_68),'#skF_10')
      | ~ r2_hidden(A_68,k1_relat_1(k2_funct_1('#skF_10')))
      | ~ v1_funct_1(k2_funct_1('#skF_10'))
      | ~ v1_relat_1(k2_funct_1('#skF_10')) ) ),
    inference(resolution,[status(thm)],[c_46,c_930])).

tff(c_937,plain,(
    ! [A_68] :
      ( r2_hidden(k4_tarski(k1_funct_1(k2_funct_1('#skF_10'),A_68),A_68),'#skF_10')
      | ~ r2_hidden(A_68,k1_relat_1(k2_funct_1('#skF_10')))
      | ~ v1_funct_1(k2_funct_1('#skF_10')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_934])).

tff(c_1185,plain,(
    ! [A_202] :
      ( r2_hidden(k4_tarski(k1_funct_1(k2_funct_1('#skF_10'),A_202),A_202),'#skF_10')
      | ~ r2_hidden(A_202,k1_relat_1(k2_funct_1('#skF_10'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1048,c_937])).

tff(c_1209,plain,(
    ! [A_202] :
      ( r2_hidden(k1_funct_1(k2_funct_1('#skF_10'),A_202),k1_relat_1('#skF_10'))
      | ~ v1_relat_1('#skF_10')
      | ~ r2_hidden(A_202,k1_relat_1(k2_funct_1('#skF_10'))) ) ),
    inference(resolution,[status(thm)],[c_1185,c_18])).

tff(c_1309,plain,(
    ! [A_206] :
      ( r2_hidden(k1_funct_1(k2_funct_1('#skF_10'),A_206),k1_relat_1('#skF_10'))
      | ~ r2_hidden(A_206,k1_relat_1(k2_funct_1('#skF_10'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_1209])).

tff(c_899,plain,(
    ! [A_161,C_162] :
      ( r2_hidden(k4_tarski(A_161,k1_funct_1(C_162,A_161)),C_162)
      | ~ r2_hidden(A_161,k1_relat_1(C_162))
      | ~ v1_funct_1(C_162)
      | ~ v1_relat_1(C_162) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_911,plain,
    ( r2_hidden(k4_tarski(k1_funct_1(k2_funct_1('#skF_10'),'#skF_9'),'#skF_9'),'#skF_10')
    | ~ r2_hidden(k1_funct_1(k2_funct_1('#skF_10'),'#skF_9'),k1_relat_1('#skF_10'))
    | ~ v1_funct_1('#skF_10')
    | ~ v1_relat_1('#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_885,c_899])).

tff(c_917,plain,
    ( r2_hidden(k4_tarski(k1_funct_1(k2_funct_1('#skF_10'),'#skF_9'),'#skF_9'),'#skF_10')
    | ~ r2_hidden(k1_funct_1(k2_funct_1('#skF_10'),'#skF_9'),k1_relat_1('#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_911])).

tff(c_918,plain,(
    ~ r2_hidden(k1_funct_1(k2_funct_1('#skF_10'),'#skF_9'),k1_relat_1('#skF_10')) ),
    inference(splitLeft,[status(thm)],[c_917])).

tff(c_1320,plain,(
    ~ r2_hidden('#skF_9',k1_relat_1(k2_funct_1('#skF_10'))) ),
    inference(resolution,[status(thm)],[c_1309,c_918])).

tff(c_1613,plain,(
    ~ r2_hidden('#skF_9',k2_relat_1('#skF_10')) ),
    inference(resolution,[status(thm)],[c_1602,c_1320])).

tff(c_1643,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_1613])).

tff(c_1644,plain,(
    r2_hidden(k4_tarski(k1_funct_1(k2_funct_1('#skF_10'),'#skF_9'),'#skF_9'),'#skF_10') ),
    inference(splitRight,[status(thm)],[c_917])).

tff(c_1733,plain,(
    ! [C_235,D_236] :
      ( r2_hidden(C_235,k1_relat_1(k2_funct_1('#skF_10')))
      | ~ v1_relat_1(k2_funct_1('#skF_10'))
      | ~ r2_hidden(k4_tarski(D_236,C_235),'#skF_10') ) ),
    inference(resolution,[status(thm)],[c_1721,c_18])).

tff(c_1770,plain,(
    ! [C_240,D_241] :
      ( r2_hidden(C_240,k1_relat_1(k2_funct_1('#skF_10')))
      | ~ r2_hidden(k4_tarski(D_241,C_240),'#skF_10') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_1733])).

tff(c_1776,plain,(
    r2_hidden('#skF_9',k1_relat_1(k2_funct_1('#skF_10'))) ),
    inference(resolution,[status(thm)],[c_1644,c_1770])).

tff(c_2301,plain,(
    ! [B_276,C_277,A_278] :
      ( k1_funct_1(k5_relat_1(B_276,C_277),A_278) = k1_funct_1(C_277,k1_funct_1(B_276,A_278))
      | ~ r2_hidden(A_278,k1_relat_1(B_276))
      | ~ v1_funct_1(C_277)
      | ~ v1_relat_1(C_277)
      | ~ v1_funct_1(B_276)
      | ~ v1_relat_1(B_276) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_2324,plain,(
    ! [C_277] :
      ( k1_funct_1(k5_relat_1(k2_funct_1('#skF_10'),C_277),'#skF_9') = k1_funct_1(C_277,k1_funct_1(k2_funct_1('#skF_10'),'#skF_9'))
      | ~ v1_funct_1(C_277)
      | ~ v1_relat_1(C_277)
      | ~ v1_funct_1(k2_funct_1('#skF_10'))
      | ~ v1_relat_1(k2_funct_1('#skF_10')) ) ),
    inference(resolution,[status(thm)],[c_1776,c_2301])).

tff(c_2375,plain,(
    ! [C_280] :
      ( k1_funct_1(k5_relat_1(k2_funct_1('#skF_10'),C_280),'#skF_9') = k1_funct_1(C_280,k1_funct_1(k2_funct_1('#skF_10'),'#skF_9'))
      | ~ v1_funct_1(C_280)
      | ~ v1_relat_1(C_280) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_1802,c_2324])).

tff(c_884,plain,(
    k1_funct_1(k5_relat_1(k2_funct_1('#skF_10'),'#skF_10'),'#skF_9') != '#skF_9' ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_2387,plain,
    ( k1_funct_1('#skF_10',k1_funct_1(k2_funct_1('#skF_10'),'#skF_9')) != '#skF_9'
    | ~ v1_funct_1('#skF_10')
    | ~ v1_relat_1('#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_2375,c_884])).

tff(c_2394,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_885,c_2387])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:51:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.19/1.78  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.19/1.79  
% 4.19/1.79  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.19/1.79  %$ r2_hidden > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > k4_tarski > k1_funct_1 > #nlpp > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_6 > #skF_3 > #skF_10 > #skF_9 > #skF_2 > #skF_8 > #skF_7 > #skF_1 > #skF_5 > #skF_4
% 4.19/1.79  
% 4.19/1.79  %Foreground sorts:
% 4.19/1.79  
% 4.19/1.79  
% 4.19/1.79  %Background operators:
% 4.19/1.79  
% 4.19/1.79  
% 4.19/1.79  %Foreground operators:
% 4.19/1.79  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 4.19/1.79  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.19/1.79  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 4.19/1.79  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 4.19/1.79  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.19/1.79  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.19/1.79  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 4.19/1.79  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 4.19/1.79  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.19/1.79  tff('#skF_10', type, '#skF_10': $i).
% 4.19/1.79  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.19/1.79  tff('#skF_9', type, '#skF_9': $i).
% 4.19/1.79  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.19/1.79  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.19/1.79  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.19/1.79  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.19/1.79  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.19/1.79  tff('#skF_8', type, '#skF_8': ($i * $i * $i) > $i).
% 4.19/1.79  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 4.19/1.79  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.19/1.79  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 4.19/1.79  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.19/1.79  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 4.19/1.79  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 4.19/1.79  
% 4.45/1.81  tff(f_116, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v2_funct_1(B) & r2_hidden(A, k2_relat_1(B))) => ((A = k1_funct_1(B, k1_funct_1(k2_funct_1(B), A))) & (A = k1_funct_1(k5_relat_1(k2_funct_1(B), B), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t57_funct_1)).
% 4.45/1.81  tff(f_64, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_funct_1)).
% 4.45/1.81  tff(f_103, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_funct_1)).
% 4.45/1.81  tff(f_72, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(A) = k4_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_funct_1)).
% 4.45/1.81  tff(f_41, axiom, (![A]: (v1_relat_1(A) => v1_relat_1(k4_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_relat_1)).
% 4.45/1.81  tff(f_37, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => ((B = k4_relat_1(A)) <=> (![C, D]: (r2_hidden(k4_tarski(C, D), B) <=> r2_hidden(k4_tarski(D, C), A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_relat_1)).
% 4.45/1.81  tff(f_49, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) => (r2_hidden(A, k1_relat_1(C)) & r2_hidden(B, k2_relat_1(C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_relat_1)).
% 4.45/1.81  tff(f_80, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 4.45/1.81  tff(f_93, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(B)) => (k1_funct_1(k5_relat_1(B, C), A) = k1_funct_1(C, k1_funct_1(B, A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_funct_1)).
% 4.45/1.81  tff(c_60, plain, (v1_relat_1('#skF_10')), inference(cnfTransformation, [status(thm)], [f_116])).
% 4.45/1.81  tff(c_58, plain, (v1_funct_1('#skF_10')), inference(cnfTransformation, [status(thm)], [f_116])).
% 4.45/1.81  tff(c_54, plain, (r2_hidden('#skF_9', k2_relat_1('#skF_10'))), inference(cnfTransformation, [status(thm)], [f_116])).
% 4.45/1.81  tff(c_24, plain, (![A_22, C_58]: (r2_hidden('#skF_8'(A_22, k2_relat_1(A_22), C_58), k1_relat_1(A_22)) | ~r2_hidden(C_58, k2_relat_1(A_22)) | ~v1_funct_1(A_22) | ~v1_relat_1(A_22))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.45/1.81  tff(c_22, plain, (![A_22, C_58]: (k1_funct_1(A_22, '#skF_8'(A_22, k2_relat_1(A_22), C_58))=C_58 | ~r2_hidden(C_58, k2_relat_1(A_22)) | ~v1_funct_1(A_22) | ~v1_relat_1(A_22))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.45/1.81  tff(c_46, plain, (![A_68, C_70]: (r2_hidden(k4_tarski(A_68, k1_funct_1(C_70, A_68)), C_70) | ~r2_hidden(A_68, k1_relat_1(C_70)) | ~v1_funct_1(C_70) | ~v1_relat_1(C_70))), inference(cnfTransformation, [status(thm)], [f_103])).
% 4.45/1.81  tff(c_56, plain, (v2_funct_1('#skF_10')), inference(cnfTransformation, [status(thm)], [f_116])).
% 4.45/1.81  tff(c_64, plain, (![A_74]: (k4_relat_1(A_74)=k2_funct_1(A_74) | ~v2_funct_1(A_74) | ~v1_funct_1(A_74) | ~v1_relat_1(A_74))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.45/1.81  tff(c_67, plain, (k4_relat_1('#skF_10')=k2_funct_1('#skF_10') | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_56, c_64])).
% 4.45/1.81  tff(c_70, plain, (k4_relat_1('#skF_10')=k2_funct_1('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_67])).
% 4.45/1.81  tff(c_14, plain, (![A_18]: (v1_relat_1(k4_relat_1(A_18)) | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.45/1.81  tff(c_74, plain, (v1_relat_1(k2_funct_1('#skF_10')) | ~v1_relat_1('#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_70, c_14])).
% 4.45/1.81  tff(c_78, plain, (v1_relat_1(k2_funct_1('#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_74])).
% 4.45/1.81  tff(c_115, plain, (![C_92, D_93, A_94]: (r2_hidden(k4_tarski(C_92, D_93), k4_relat_1(A_94)) | ~r2_hidden(k4_tarski(D_93, C_92), A_94) | ~v1_relat_1(k4_relat_1(A_94)) | ~v1_relat_1(A_94))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.45/1.81  tff(c_127, plain, (![C_92, D_93]: (r2_hidden(k4_tarski(C_92, D_93), k2_funct_1('#skF_10')) | ~r2_hidden(k4_tarski(D_93, C_92), '#skF_10') | ~v1_relat_1(k4_relat_1('#skF_10')) | ~v1_relat_1('#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_70, c_115])).
% 4.45/1.81  tff(c_133, plain, (![C_95, D_96]: (r2_hidden(k4_tarski(C_95, D_96), k2_funct_1('#skF_10')) | ~r2_hidden(k4_tarski(D_96, C_95), '#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_78, c_70, c_127])).
% 4.45/1.81  tff(c_18, plain, (![A_19, C_21, B_20]: (r2_hidden(A_19, k1_relat_1(C_21)) | ~r2_hidden(k4_tarski(A_19, B_20), C_21) | ~v1_relat_1(C_21))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.45/1.81  tff(c_142, plain, (![C_95, D_96]: (r2_hidden(C_95, k1_relat_1(k2_funct_1('#skF_10'))) | ~v1_relat_1(k2_funct_1('#skF_10')) | ~r2_hidden(k4_tarski(D_96, C_95), '#skF_10'))), inference(resolution, [status(thm)], [c_133, c_18])).
% 4.45/1.81  tff(c_175, plain, (![C_100, D_101]: (r2_hidden(C_100, k1_relat_1(k2_funct_1('#skF_10'))) | ~r2_hidden(k4_tarski(D_101, C_100), '#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_142])).
% 4.45/1.81  tff(c_178, plain, (![A_68]: (r2_hidden(k1_funct_1('#skF_10', A_68), k1_relat_1(k2_funct_1('#skF_10'))) | ~r2_hidden(A_68, k1_relat_1('#skF_10')) | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10'))), inference(resolution, [status(thm)], [c_46, c_175])).
% 4.45/1.81  tff(c_182, plain, (![A_102]: (r2_hidden(k1_funct_1('#skF_10', A_102), k1_relat_1(k2_funct_1('#skF_10'))) | ~r2_hidden(A_102, k1_relat_1('#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_178])).
% 4.45/1.81  tff(c_186, plain, (![C_58]: (r2_hidden(C_58, k1_relat_1(k2_funct_1('#skF_10'))) | ~r2_hidden('#skF_8'('#skF_10', k2_relat_1('#skF_10'), C_58), k1_relat_1('#skF_10')) | ~r2_hidden(C_58, k2_relat_1('#skF_10')) | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_22, c_182])).
% 4.45/1.81  tff(c_777, plain, (![C_147]: (r2_hidden(C_147, k1_relat_1(k2_funct_1('#skF_10'))) | ~r2_hidden('#skF_8'('#skF_10', k2_relat_1('#skF_10'), C_147), k1_relat_1('#skF_10')) | ~r2_hidden(C_147, k2_relat_1('#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_186])).
% 4.45/1.81  tff(c_781, plain, (![C_58]: (r2_hidden(C_58, k1_relat_1(k2_funct_1('#skF_10'))) | ~r2_hidden(C_58, k2_relat_1('#skF_10')) | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10'))), inference(resolution, [status(thm)], [c_24, c_777])).
% 4.45/1.81  tff(c_785, plain, (![C_148]: (r2_hidden(C_148, k1_relat_1(k2_funct_1('#skF_10'))) | ~r2_hidden(C_148, k2_relat_1('#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_781])).
% 4.45/1.81  tff(c_40, plain, (![A_63]: (v1_funct_1(k2_funct_1(A_63)) | ~v1_funct_1(A_63) | ~v1_relat_1(A_63))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.45/1.81  tff(c_48, plain, (![C_70, A_68, B_69]: (k1_funct_1(C_70, A_68)=B_69 | ~r2_hidden(k4_tarski(A_68, B_69), C_70) | ~v1_funct_1(C_70) | ~v1_relat_1(C_70))), inference(cnfTransformation, [status(thm)], [f_103])).
% 4.45/1.81  tff(c_136, plain, (![C_95, D_96]: (k1_funct_1(k2_funct_1('#skF_10'), C_95)=D_96 | ~v1_funct_1(k2_funct_1('#skF_10')) | ~v1_relat_1(k2_funct_1('#skF_10')) | ~r2_hidden(k4_tarski(D_96, C_95), '#skF_10'))), inference(resolution, [status(thm)], [c_133, c_48])).
% 4.45/1.81  tff(c_145, plain, (![C_95, D_96]: (k1_funct_1(k2_funct_1('#skF_10'), C_95)=D_96 | ~v1_funct_1(k2_funct_1('#skF_10')) | ~r2_hidden(k4_tarski(D_96, C_95), '#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_136])).
% 4.45/1.81  tff(c_216, plain, (~v1_funct_1(k2_funct_1('#skF_10'))), inference(splitLeft, [status(thm)], [c_145])).
% 4.45/1.81  tff(c_219, plain, (~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_40, c_216])).
% 4.45/1.81  tff(c_223, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_219])).
% 4.45/1.81  tff(c_225, plain, (v1_funct_1(k2_funct_1('#skF_10'))), inference(splitRight, [status(thm)], [c_145])).
% 4.45/1.81  tff(c_189, plain, (![D_103, C_104, A_105]: (r2_hidden(k4_tarski(D_103, C_104), A_105) | ~r2_hidden(k4_tarski(C_104, D_103), k4_relat_1(A_105)) | ~v1_relat_1(k4_relat_1(A_105)) | ~v1_relat_1(A_105))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.45/1.81  tff(c_199, plain, (![D_103, C_104]: (r2_hidden(k4_tarski(D_103, C_104), '#skF_10') | ~r2_hidden(k4_tarski(C_104, D_103), k2_funct_1('#skF_10')) | ~v1_relat_1(k4_relat_1('#skF_10')) | ~v1_relat_1('#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_70, c_189])).
% 4.45/1.81  tff(c_204, plain, (![D_106, C_107]: (r2_hidden(k4_tarski(D_106, C_107), '#skF_10') | ~r2_hidden(k4_tarski(C_107, D_106), k2_funct_1('#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_78, c_70, c_199])).
% 4.45/1.81  tff(c_211, plain, (![A_68]: (r2_hidden(k4_tarski(k1_funct_1(k2_funct_1('#skF_10'), A_68), A_68), '#skF_10') | ~r2_hidden(A_68, k1_relat_1(k2_funct_1('#skF_10'))) | ~v1_funct_1(k2_funct_1('#skF_10')) | ~v1_relat_1(k2_funct_1('#skF_10')))), inference(resolution, [status(thm)], [c_46, c_204])).
% 4.45/1.81  tff(c_215, plain, (![A_68]: (r2_hidden(k4_tarski(k1_funct_1(k2_funct_1('#skF_10'), A_68), A_68), '#skF_10') | ~r2_hidden(A_68, k1_relat_1(k2_funct_1('#skF_10'))) | ~v1_funct_1(k2_funct_1('#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_211])).
% 4.45/1.81  tff(c_226, plain, (~v1_funct_1(k2_funct_1('#skF_10'))), inference(splitLeft, [status(thm)], [c_215])).
% 4.45/1.81  tff(c_228, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_225, c_226])).
% 4.45/1.81  tff(c_266, plain, (![A_113]: (r2_hidden(k4_tarski(k1_funct_1(k2_funct_1('#skF_10'), A_113), A_113), '#skF_10') | ~r2_hidden(A_113, k1_relat_1(k2_funct_1('#skF_10'))))), inference(splitRight, [status(thm)], [c_215])).
% 4.45/1.81  tff(c_276, plain, (![A_113]: (k1_funct_1('#skF_10', k1_funct_1(k2_funct_1('#skF_10'), A_113))=A_113 | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10') | ~r2_hidden(A_113, k1_relat_1(k2_funct_1('#skF_10'))))), inference(resolution, [status(thm)], [c_266, c_48])).
% 4.45/1.81  tff(c_296, plain, (![A_113]: (k1_funct_1('#skF_10', k1_funct_1(k2_funct_1('#skF_10'), A_113))=A_113 | ~r2_hidden(A_113, k1_relat_1(k2_funct_1('#skF_10'))))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_276])).
% 4.45/1.81  tff(c_821, plain, (![C_149]: (k1_funct_1('#skF_10', k1_funct_1(k2_funct_1('#skF_10'), C_149))=C_149 | ~r2_hidden(C_149, k2_relat_1('#skF_10')))), inference(resolution, [status(thm)], [c_785, c_296])).
% 4.45/1.81  tff(c_52, plain, (k1_funct_1(k5_relat_1(k2_funct_1('#skF_10'), '#skF_10'), '#skF_9')!='#skF_9' | k1_funct_1('#skF_10', k1_funct_1(k2_funct_1('#skF_10'), '#skF_9'))!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_116])).
% 4.45/1.81  tff(c_80, plain, (k1_funct_1('#skF_10', k1_funct_1(k2_funct_1('#skF_10'), '#skF_9'))!='#skF_9'), inference(splitLeft, [status(thm)], [c_52])).
% 4.45/1.81  tff(c_854, plain, (~r2_hidden('#skF_9', k2_relat_1('#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_821, c_80])).
% 4.45/1.81  tff(c_883, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_854])).
% 4.45/1.81  tff(c_885, plain, (k1_funct_1('#skF_10', k1_funct_1(k2_funct_1('#skF_10'), '#skF_9'))='#skF_9'), inference(splitRight, [status(thm)], [c_52])).
% 4.45/1.81  tff(c_1699, plain, (![C_232, D_233, A_234]: (r2_hidden(k4_tarski(C_232, D_233), k4_relat_1(A_234)) | ~r2_hidden(k4_tarski(D_233, C_232), A_234) | ~v1_relat_1(k4_relat_1(A_234)) | ~v1_relat_1(A_234))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.45/1.81  tff(c_1714, plain, (![C_232, D_233]: (r2_hidden(k4_tarski(C_232, D_233), k2_funct_1('#skF_10')) | ~r2_hidden(k4_tarski(D_233, C_232), '#skF_10') | ~v1_relat_1(k4_relat_1('#skF_10')) | ~v1_relat_1('#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_70, c_1699])).
% 4.45/1.81  tff(c_1721, plain, (![C_235, D_236]: (r2_hidden(k4_tarski(C_235, D_236), k2_funct_1('#skF_10')) | ~r2_hidden(k4_tarski(D_236, C_235), '#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_78, c_70, c_1714])).
% 4.45/1.81  tff(c_1727, plain, (![C_235, D_236]: (k1_funct_1(k2_funct_1('#skF_10'), C_235)=D_236 | ~v1_funct_1(k2_funct_1('#skF_10')) | ~v1_relat_1(k2_funct_1('#skF_10')) | ~r2_hidden(k4_tarski(D_236, C_235), '#skF_10'))), inference(resolution, [status(thm)], [c_1721, c_48])).
% 4.45/1.81  tff(c_1737, plain, (![C_235, D_236]: (k1_funct_1(k2_funct_1('#skF_10'), C_235)=D_236 | ~v1_funct_1(k2_funct_1('#skF_10')) | ~r2_hidden(k4_tarski(D_236, C_235), '#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_1727])).
% 4.45/1.81  tff(c_1793, plain, (~v1_funct_1(k2_funct_1('#skF_10'))), inference(splitLeft, [status(thm)], [c_1737])).
% 4.45/1.81  tff(c_1796, plain, (~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_40, c_1793])).
% 4.45/1.81  tff(c_1800, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_1796])).
% 4.45/1.81  tff(c_1802, plain, (v1_funct_1(k2_funct_1('#skF_10'))), inference(splitRight, [status(thm)], [c_1737])).
% 4.45/1.81  tff(c_953, plain, (![C_170, D_171, A_172]: (r2_hidden(k4_tarski(C_170, D_171), k4_relat_1(A_172)) | ~r2_hidden(k4_tarski(D_171, C_170), A_172) | ~v1_relat_1(k4_relat_1(A_172)) | ~v1_relat_1(A_172))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.45/1.81  tff(c_968, plain, (![C_170, D_171]: (r2_hidden(k4_tarski(C_170, D_171), k2_funct_1('#skF_10')) | ~r2_hidden(k4_tarski(D_171, C_170), '#skF_10') | ~v1_relat_1(k4_relat_1('#skF_10')) | ~v1_relat_1('#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_70, c_953])).
% 4.45/1.81  tff(c_975, plain, (![C_173, D_174]: (r2_hidden(k4_tarski(C_173, D_174), k2_funct_1('#skF_10')) | ~r2_hidden(k4_tarski(D_174, C_173), '#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_78, c_70, c_968])).
% 4.45/1.81  tff(c_987, plain, (![C_173, D_174]: (r2_hidden(C_173, k1_relat_1(k2_funct_1('#skF_10'))) | ~v1_relat_1(k2_funct_1('#skF_10')) | ~r2_hidden(k4_tarski(D_174, C_173), '#skF_10'))), inference(resolution, [status(thm)], [c_975, c_18])).
% 4.45/1.81  tff(c_1022, plain, (![C_180, D_181]: (r2_hidden(C_180, k1_relat_1(k2_funct_1('#skF_10'))) | ~r2_hidden(k4_tarski(D_181, C_180), '#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_987])).
% 4.45/1.81  tff(c_1025, plain, (![A_68]: (r2_hidden(k1_funct_1('#skF_10', A_68), k1_relat_1(k2_funct_1('#skF_10'))) | ~r2_hidden(A_68, k1_relat_1('#skF_10')) | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10'))), inference(resolution, [status(thm)], [c_46, c_1022])).
% 4.45/1.81  tff(c_1029, plain, (![A_182]: (r2_hidden(k1_funct_1('#skF_10', A_182), k1_relat_1(k2_funct_1('#skF_10'))) | ~r2_hidden(A_182, k1_relat_1('#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_1025])).
% 4.45/1.81  tff(c_1033, plain, (![C_58]: (r2_hidden(C_58, k1_relat_1(k2_funct_1('#skF_10'))) | ~r2_hidden('#skF_8'('#skF_10', k2_relat_1('#skF_10'), C_58), k1_relat_1('#skF_10')) | ~r2_hidden(C_58, k2_relat_1('#skF_10')) | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_22, c_1029])).
% 4.45/1.81  tff(c_1579, plain, (![C_220]: (r2_hidden(C_220, k1_relat_1(k2_funct_1('#skF_10'))) | ~r2_hidden('#skF_8'('#skF_10', k2_relat_1('#skF_10'), C_220), k1_relat_1('#skF_10')) | ~r2_hidden(C_220, k2_relat_1('#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_1033])).
% 4.45/1.81  tff(c_1583, plain, (![C_58]: (r2_hidden(C_58, k1_relat_1(k2_funct_1('#skF_10'))) | ~r2_hidden(C_58, k2_relat_1('#skF_10')) | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10'))), inference(resolution, [status(thm)], [c_24, c_1579])).
% 4.45/1.81  tff(c_1602, plain, (![C_222]: (r2_hidden(C_222, k1_relat_1(k2_funct_1('#skF_10'))) | ~r2_hidden(C_222, k2_relat_1('#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_1583])).
% 4.45/1.81  tff(c_981, plain, (![C_173, D_174]: (k1_funct_1(k2_funct_1('#skF_10'), C_173)=D_174 | ~v1_funct_1(k2_funct_1('#skF_10')) | ~v1_relat_1(k2_funct_1('#skF_10')) | ~r2_hidden(k4_tarski(D_174, C_173), '#skF_10'))), inference(resolution, [status(thm)], [c_975, c_48])).
% 4.45/1.81  tff(c_991, plain, (![C_173, D_174]: (k1_funct_1(k2_funct_1('#skF_10'), C_173)=D_174 | ~v1_funct_1(k2_funct_1('#skF_10')) | ~r2_hidden(k4_tarski(D_174, C_173), '#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_981])).
% 4.45/1.81  tff(c_1039, plain, (~v1_funct_1(k2_funct_1('#skF_10'))), inference(splitLeft, [status(thm)], [c_991])).
% 4.45/1.81  tff(c_1042, plain, (~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_40, c_1039])).
% 4.45/1.81  tff(c_1046, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_1042])).
% 4.45/1.81  tff(c_1048, plain, (v1_funct_1(k2_funct_1('#skF_10'))), inference(splitRight, [status(thm)], [c_991])).
% 4.45/1.81  tff(c_919, plain, (![D_163, C_164, A_165]: (r2_hidden(k4_tarski(D_163, C_164), A_165) | ~r2_hidden(k4_tarski(C_164, D_163), k4_relat_1(A_165)) | ~v1_relat_1(k4_relat_1(A_165)) | ~v1_relat_1(A_165))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.45/1.81  tff(c_926, plain, (![D_163, C_164]: (r2_hidden(k4_tarski(D_163, C_164), '#skF_10') | ~r2_hidden(k4_tarski(C_164, D_163), k2_funct_1('#skF_10')) | ~v1_relat_1(k4_relat_1('#skF_10')) | ~v1_relat_1('#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_70, c_919])).
% 4.45/1.81  tff(c_930, plain, (![D_166, C_167]: (r2_hidden(k4_tarski(D_166, C_167), '#skF_10') | ~r2_hidden(k4_tarski(C_167, D_166), k2_funct_1('#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_78, c_70, c_926])).
% 4.45/1.81  tff(c_934, plain, (![A_68]: (r2_hidden(k4_tarski(k1_funct_1(k2_funct_1('#skF_10'), A_68), A_68), '#skF_10') | ~r2_hidden(A_68, k1_relat_1(k2_funct_1('#skF_10'))) | ~v1_funct_1(k2_funct_1('#skF_10')) | ~v1_relat_1(k2_funct_1('#skF_10')))), inference(resolution, [status(thm)], [c_46, c_930])).
% 4.45/1.81  tff(c_937, plain, (![A_68]: (r2_hidden(k4_tarski(k1_funct_1(k2_funct_1('#skF_10'), A_68), A_68), '#skF_10') | ~r2_hidden(A_68, k1_relat_1(k2_funct_1('#skF_10'))) | ~v1_funct_1(k2_funct_1('#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_934])).
% 4.45/1.81  tff(c_1185, plain, (![A_202]: (r2_hidden(k4_tarski(k1_funct_1(k2_funct_1('#skF_10'), A_202), A_202), '#skF_10') | ~r2_hidden(A_202, k1_relat_1(k2_funct_1('#skF_10'))))), inference(demodulation, [status(thm), theory('equality')], [c_1048, c_937])).
% 4.45/1.81  tff(c_1209, plain, (![A_202]: (r2_hidden(k1_funct_1(k2_funct_1('#skF_10'), A_202), k1_relat_1('#skF_10')) | ~v1_relat_1('#skF_10') | ~r2_hidden(A_202, k1_relat_1(k2_funct_1('#skF_10'))))), inference(resolution, [status(thm)], [c_1185, c_18])).
% 4.45/1.81  tff(c_1309, plain, (![A_206]: (r2_hidden(k1_funct_1(k2_funct_1('#skF_10'), A_206), k1_relat_1('#skF_10')) | ~r2_hidden(A_206, k1_relat_1(k2_funct_1('#skF_10'))))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_1209])).
% 4.45/1.81  tff(c_899, plain, (![A_161, C_162]: (r2_hidden(k4_tarski(A_161, k1_funct_1(C_162, A_161)), C_162) | ~r2_hidden(A_161, k1_relat_1(C_162)) | ~v1_funct_1(C_162) | ~v1_relat_1(C_162))), inference(cnfTransformation, [status(thm)], [f_103])).
% 4.45/1.81  tff(c_911, plain, (r2_hidden(k4_tarski(k1_funct_1(k2_funct_1('#skF_10'), '#skF_9'), '#skF_9'), '#skF_10') | ~r2_hidden(k1_funct_1(k2_funct_1('#skF_10'), '#skF_9'), k1_relat_1('#skF_10')) | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_885, c_899])).
% 4.45/1.81  tff(c_917, plain, (r2_hidden(k4_tarski(k1_funct_1(k2_funct_1('#skF_10'), '#skF_9'), '#skF_9'), '#skF_10') | ~r2_hidden(k1_funct_1(k2_funct_1('#skF_10'), '#skF_9'), k1_relat_1('#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_911])).
% 4.45/1.81  tff(c_918, plain, (~r2_hidden(k1_funct_1(k2_funct_1('#skF_10'), '#skF_9'), k1_relat_1('#skF_10'))), inference(splitLeft, [status(thm)], [c_917])).
% 4.45/1.81  tff(c_1320, plain, (~r2_hidden('#skF_9', k1_relat_1(k2_funct_1('#skF_10')))), inference(resolution, [status(thm)], [c_1309, c_918])).
% 4.45/1.81  tff(c_1613, plain, (~r2_hidden('#skF_9', k2_relat_1('#skF_10'))), inference(resolution, [status(thm)], [c_1602, c_1320])).
% 4.45/1.81  tff(c_1643, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_1613])).
% 4.45/1.81  tff(c_1644, plain, (r2_hidden(k4_tarski(k1_funct_1(k2_funct_1('#skF_10'), '#skF_9'), '#skF_9'), '#skF_10')), inference(splitRight, [status(thm)], [c_917])).
% 4.45/1.81  tff(c_1733, plain, (![C_235, D_236]: (r2_hidden(C_235, k1_relat_1(k2_funct_1('#skF_10'))) | ~v1_relat_1(k2_funct_1('#skF_10')) | ~r2_hidden(k4_tarski(D_236, C_235), '#skF_10'))), inference(resolution, [status(thm)], [c_1721, c_18])).
% 4.45/1.81  tff(c_1770, plain, (![C_240, D_241]: (r2_hidden(C_240, k1_relat_1(k2_funct_1('#skF_10'))) | ~r2_hidden(k4_tarski(D_241, C_240), '#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_1733])).
% 4.45/1.81  tff(c_1776, plain, (r2_hidden('#skF_9', k1_relat_1(k2_funct_1('#skF_10')))), inference(resolution, [status(thm)], [c_1644, c_1770])).
% 4.45/1.81  tff(c_2301, plain, (![B_276, C_277, A_278]: (k1_funct_1(k5_relat_1(B_276, C_277), A_278)=k1_funct_1(C_277, k1_funct_1(B_276, A_278)) | ~r2_hidden(A_278, k1_relat_1(B_276)) | ~v1_funct_1(C_277) | ~v1_relat_1(C_277) | ~v1_funct_1(B_276) | ~v1_relat_1(B_276))), inference(cnfTransformation, [status(thm)], [f_93])).
% 4.45/1.81  tff(c_2324, plain, (![C_277]: (k1_funct_1(k5_relat_1(k2_funct_1('#skF_10'), C_277), '#skF_9')=k1_funct_1(C_277, k1_funct_1(k2_funct_1('#skF_10'), '#skF_9')) | ~v1_funct_1(C_277) | ~v1_relat_1(C_277) | ~v1_funct_1(k2_funct_1('#skF_10')) | ~v1_relat_1(k2_funct_1('#skF_10')))), inference(resolution, [status(thm)], [c_1776, c_2301])).
% 4.45/1.81  tff(c_2375, plain, (![C_280]: (k1_funct_1(k5_relat_1(k2_funct_1('#skF_10'), C_280), '#skF_9')=k1_funct_1(C_280, k1_funct_1(k2_funct_1('#skF_10'), '#skF_9')) | ~v1_funct_1(C_280) | ~v1_relat_1(C_280))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_1802, c_2324])).
% 4.45/1.81  tff(c_884, plain, (k1_funct_1(k5_relat_1(k2_funct_1('#skF_10'), '#skF_10'), '#skF_9')!='#skF_9'), inference(splitRight, [status(thm)], [c_52])).
% 4.45/1.81  tff(c_2387, plain, (k1_funct_1('#skF_10', k1_funct_1(k2_funct_1('#skF_10'), '#skF_9'))!='#skF_9' | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_2375, c_884])).
% 4.45/1.81  tff(c_2394, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_885, c_2387])).
% 4.45/1.81  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.45/1.81  
% 4.45/1.81  Inference rules
% 4.45/1.81  ----------------------
% 4.45/1.81  #Ref     : 0
% 4.45/1.81  #Sup     : 463
% 4.45/1.81  #Fact    : 0
% 4.45/1.81  #Define  : 0
% 4.45/1.81  #Split   : 13
% 4.45/1.81  #Chain   : 0
% 4.45/1.81  #Close   : 0
% 4.45/1.81  
% 4.45/1.81  Ordering : KBO
% 4.45/1.81  
% 4.45/1.81  Simplification rules
% 4.45/1.81  ----------------------
% 4.45/1.81  #Subsume      : 50
% 4.45/1.81  #Demod        : 349
% 4.45/1.81  #Tautology    : 99
% 4.45/1.81  #SimpNegUnit  : 0
% 4.45/1.81  #BackRed      : 0
% 4.45/1.81  
% 4.45/1.81  #Partial instantiations: 0
% 4.45/1.81  #Strategies tried      : 1
% 4.45/1.81  
% 4.45/1.81  Timing (in seconds)
% 4.45/1.81  ----------------------
% 4.45/1.82  Preprocessing        : 0.35
% 4.45/1.82  Parsing              : 0.18
% 4.45/1.82  CNF conversion       : 0.03
% 4.45/1.82  Main loop            : 0.64
% 4.45/1.82  Inferencing          : 0.25
% 4.45/1.82  Reduction            : 0.18
% 4.45/1.82  Demodulation         : 0.13
% 4.45/1.82  BG Simplification    : 0.04
% 4.45/1.82  Subsumption          : 0.12
% 4.45/1.82  Abstraction          : 0.04
% 4.45/1.82  MUC search           : 0.00
% 4.45/1.82  Cooper               : 0.00
% 4.45/1.82  Total                : 1.04
% 4.45/1.82  Index Insertion      : 0.00
% 4.45/1.82  Index Deletion       : 0.00
% 4.45/1.82  Index Matching       : 0.00
% 4.45/1.82  BG Taut test         : 0.00
%------------------------------------------------------------------------------
