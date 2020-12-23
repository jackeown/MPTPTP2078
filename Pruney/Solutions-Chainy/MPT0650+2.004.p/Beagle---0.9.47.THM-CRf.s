%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:45 EST 2020

% Result     : Theorem 5.10s
% Output     : CNFRefutation 5.45s
% Verified   : 
% Statistics : Number of formulae       :  132 ( 815 expanded)
%              Number of leaves         :   34 ( 311 expanded)
%              Depth                    :   17
%              Number of atoms          :  301 (2552 expanded)
%              Number of equality atoms :   28 ( 623 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > k4_tarski > k1_funct_1 > #nlpp > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_3 > #skF_10 > #skF_9 > #skF_2 > #skF_8 > #skF_7 > #skF_1 > #skF_5 > #skF_4

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff(f_124,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ( ( v2_funct_1(B)
            & r2_hidden(A,k2_relat_1(B)) )
         => ( A = k1_funct_1(B,k1_funct_1(k2_funct_1(B),A))
            & A = k1_funct_1(k5_relat_1(k2_funct_1(B),B),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_funct_1)).

tff(f_82,axiom,(
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

tff(f_67,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B,C] :
          ( ( r2_hidden(B,k1_relat_1(A))
           => ( C = k1_funct_1(A,B)
            <=> r2_hidden(k4_tarski(B,C),A) ) )
          & ( ~ r2_hidden(B,k1_relat_1(A))
           => ( C = k1_funct_1(A,B)
            <=> C = k1_xboole_0 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_funct_1)).

tff(f_90,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(A) = k4_relat_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).

tff(f_41,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => v1_relat_1(k4_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_relat_1)).

tff(f_37,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( B = k4_relat_1(A)
          <=> ! [C,D] :
                ( r2_hidden(k4_tarski(C,D),B)
              <=> r2_hidden(k4_tarski(D,C),A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_relat_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
       => ( r2_hidden(A,k1_relat_1(C))
          & r2_hidden(B,k2_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_relat_1)).

tff(f_98,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_111,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ! [C] :
          ( ( v1_relat_1(C)
            & v1_funct_1(C) )
         => ( r2_hidden(A,k1_relat_1(B))
           => k1_funct_1(k5_relat_1(B,C),A) = k1_funct_1(C,k1_funct_1(B,A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_funct_1)).

tff(c_62,plain,(
    v1_relat_1('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_60,plain,(
    v1_funct_1('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_56,plain,(
    r2_hidden('#skF_9',k2_relat_1('#skF_10')) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_32,plain,(
    ! [A_27,C_63] :
      ( r2_hidden('#skF_8'(A_27,k2_relat_1(A_27),C_63),k1_relat_1(A_27))
      | ~ r2_hidden(C_63,k2_relat_1(A_27))
      | ~ v1_funct_1(A_27)
      | ~ v1_relat_1(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_30,plain,(
    ! [A_27,C_63] :
      ( k1_funct_1(A_27,'#skF_8'(A_27,k2_relat_1(A_27),C_63)) = C_63
      | ~ r2_hidden(C_63,k2_relat_1(A_27))
      | ~ v1_funct_1(A_27)
      | ~ v1_relat_1(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_22,plain,(
    ! [B_25,A_22] :
      ( r2_hidden(k4_tarski(B_25,k1_funct_1(A_22,B_25)),A_22)
      | ~ r2_hidden(B_25,k1_relat_1(A_22))
      | ~ v1_funct_1(A_22)
      | ~ v1_relat_1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_58,plain,(
    v2_funct_1('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_66,plain,(
    ! [A_76] :
      ( k4_relat_1(A_76) = k2_funct_1(A_76)
      | ~ v2_funct_1(A_76)
      | ~ v1_funct_1(A_76)
      | ~ v1_relat_1(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_69,plain,
    ( k4_relat_1('#skF_10') = k2_funct_1('#skF_10')
    | ~ v1_funct_1('#skF_10')
    | ~ v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_58,c_66])).

tff(c_72,plain,(
    k4_relat_1('#skF_10') = k2_funct_1('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_69])).

tff(c_14,plain,(
    ! [A_18] :
      ( v1_relat_1(k4_relat_1(A_18))
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_76,plain,
    ( v1_relat_1(k2_funct_1('#skF_10'))
    | ~ v1_relat_1('#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_14])).

tff(c_80,plain,(
    v1_relat_1(k2_funct_1('#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_76])).

tff(c_141,plain,(
    ! [C_98,D_99,A_100] :
      ( r2_hidden(k4_tarski(C_98,D_99),k4_relat_1(A_100))
      | ~ r2_hidden(k4_tarski(D_99,C_98),A_100)
      | ~ v1_relat_1(k4_relat_1(A_100))
      | ~ v1_relat_1(A_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_153,plain,(
    ! [C_98,D_99] :
      ( r2_hidden(k4_tarski(C_98,D_99),k2_funct_1('#skF_10'))
      | ~ r2_hidden(k4_tarski(D_99,C_98),'#skF_10')
      | ~ v1_relat_1(k4_relat_1('#skF_10'))
      | ~ v1_relat_1('#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_141])).

tff(c_159,plain,(
    ! [C_101,D_102] :
      ( r2_hidden(k4_tarski(C_101,D_102),k2_funct_1('#skF_10'))
      | ~ r2_hidden(k4_tarski(D_102,C_101),'#skF_10') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_80,c_72,c_153])).

tff(c_18,plain,(
    ! [A_19,C_21,B_20] :
      ( r2_hidden(A_19,k1_relat_1(C_21))
      | ~ r2_hidden(k4_tarski(A_19,B_20),C_21)
      | ~ v1_relat_1(C_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_168,plain,(
    ! [C_101,D_102] :
      ( r2_hidden(C_101,k1_relat_1(k2_funct_1('#skF_10')))
      | ~ v1_relat_1(k2_funct_1('#skF_10'))
      | ~ r2_hidden(k4_tarski(D_102,C_101),'#skF_10') ) ),
    inference(resolution,[status(thm)],[c_159,c_18])).

tff(c_220,plain,(
    ! [C_109,D_110] :
      ( r2_hidden(C_109,k1_relat_1(k2_funct_1('#skF_10')))
      | ~ r2_hidden(k4_tarski(D_110,C_109),'#skF_10') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_168])).

tff(c_223,plain,(
    ! [B_25] :
      ( r2_hidden(k1_funct_1('#skF_10',B_25),k1_relat_1(k2_funct_1('#skF_10')))
      | ~ r2_hidden(B_25,k1_relat_1('#skF_10'))
      | ~ v1_funct_1('#skF_10')
      | ~ v1_relat_1('#skF_10') ) ),
    inference(resolution,[status(thm)],[c_22,c_220])).

tff(c_227,plain,(
    ! [B_111] :
      ( r2_hidden(k1_funct_1('#skF_10',B_111),k1_relat_1(k2_funct_1('#skF_10')))
      | ~ r2_hidden(B_111,k1_relat_1('#skF_10')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_223])).

tff(c_231,plain,(
    ! [C_63] :
      ( r2_hidden(C_63,k1_relat_1(k2_funct_1('#skF_10')))
      | ~ r2_hidden('#skF_8'('#skF_10',k2_relat_1('#skF_10'),C_63),k1_relat_1('#skF_10'))
      | ~ r2_hidden(C_63,k2_relat_1('#skF_10'))
      | ~ v1_funct_1('#skF_10')
      | ~ v1_relat_1('#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_227])).

tff(c_736,plain,(
    ! [C_152] :
      ( r2_hidden(C_152,k1_relat_1(k2_funct_1('#skF_10')))
      | ~ r2_hidden('#skF_8'('#skF_10',k2_relat_1('#skF_10'),C_152),k1_relat_1('#skF_10'))
      | ~ r2_hidden(C_152,k2_relat_1('#skF_10')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_231])).

tff(c_740,plain,(
    ! [C_63] :
      ( r2_hidden(C_63,k1_relat_1(k2_funct_1('#skF_10')))
      | ~ r2_hidden(C_63,k2_relat_1('#skF_10'))
      | ~ v1_funct_1('#skF_10')
      | ~ v1_relat_1('#skF_10') ) ),
    inference(resolution,[status(thm)],[c_32,c_736])).

tff(c_746,plain,(
    ! [C_63] :
      ( r2_hidden(C_63,k1_relat_1(k2_funct_1('#skF_10')))
      | ~ r2_hidden(C_63,k2_relat_1('#skF_10')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_740])).

tff(c_48,plain,(
    ! [A_68] :
      ( v1_funct_1(k2_funct_1(A_68))
      | ~ v1_funct_1(A_68)
      | ~ v1_relat_1(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_107,plain,(
    ! [D_91,C_92,A_93] :
      ( r2_hidden(k4_tarski(D_91,C_92),A_93)
      | ~ r2_hidden(k4_tarski(C_92,D_91),k4_relat_1(A_93))
      | ~ v1_relat_1(k4_relat_1(A_93))
      | ~ v1_relat_1(A_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_114,plain,(
    ! [D_91,C_92] :
      ( r2_hidden(k4_tarski(D_91,C_92),'#skF_10')
      | ~ r2_hidden(k4_tarski(C_92,D_91),k2_funct_1('#skF_10'))
      | ~ v1_relat_1(k4_relat_1('#skF_10'))
      | ~ v1_relat_1('#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_107])).

tff(c_118,plain,(
    ! [D_94,C_95] :
      ( r2_hidden(k4_tarski(D_94,C_95),'#skF_10')
      | ~ r2_hidden(k4_tarski(C_95,D_94),k2_funct_1('#skF_10')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_80,c_72,c_114])).

tff(c_122,plain,(
    ! [B_25] :
      ( r2_hidden(k4_tarski(k1_funct_1(k2_funct_1('#skF_10'),B_25),B_25),'#skF_10')
      | ~ r2_hidden(B_25,k1_relat_1(k2_funct_1('#skF_10')))
      | ~ v1_funct_1(k2_funct_1('#skF_10'))
      | ~ v1_relat_1(k2_funct_1('#skF_10')) ) ),
    inference(resolution,[status(thm)],[c_22,c_118])).

tff(c_125,plain,(
    ! [B_25] :
      ( r2_hidden(k4_tarski(k1_funct_1(k2_funct_1('#skF_10'),B_25),B_25),'#skF_10')
      | ~ r2_hidden(B_25,k1_relat_1(k2_funct_1('#skF_10')))
      | ~ v1_funct_1(k2_funct_1('#skF_10')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_122])).

tff(c_359,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_10')) ),
    inference(splitLeft,[status(thm)],[c_125])).

tff(c_362,plain,
    ( ~ v1_funct_1('#skF_10')
    | ~ v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_48,c_359])).

tff(c_366,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_362])).

tff(c_369,plain,(
    ! [B_128] :
      ( r2_hidden(k4_tarski(k1_funct_1(k2_funct_1('#skF_10'),B_128),B_128),'#skF_10')
      | ~ r2_hidden(B_128,k1_relat_1(k2_funct_1('#skF_10'))) ) ),
    inference(splitRight,[status(thm)],[c_125])).

tff(c_390,plain,(
    ! [B_128] :
      ( r2_hidden(k1_funct_1(k2_funct_1('#skF_10'),B_128),k1_relat_1('#skF_10'))
      | ~ v1_relat_1('#skF_10')
      | ~ r2_hidden(B_128,k1_relat_1(k2_funct_1('#skF_10'))) ) ),
    inference(resolution,[status(thm)],[c_369,c_18])).

tff(c_413,plain,(
    ! [B_128] :
      ( r2_hidden(k1_funct_1(k2_funct_1('#skF_10'),B_128),k1_relat_1('#skF_10'))
      | ~ r2_hidden(B_128,k1_relat_1(k2_funct_1('#skF_10'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_390])).

tff(c_20,plain,(
    ! [A_22,B_25,C_26] :
      ( k1_funct_1(A_22,B_25) = C_26
      | ~ r2_hidden(k4_tarski(B_25,C_26),A_22)
      | ~ r2_hidden(B_25,k1_relat_1(A_22))
      | ~ v1_funct_1(A_22)
      | ~ v1_relat_1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_382,plain,(
    ! [B_128] :
      ( k1_funct_1('#skF_10',k1_funct_1(k2_funct_1('#skF_10'),B_128)) = B_128
      | ~ r2_hidden(k1_funct_1(k2_funct_1('#skF_10'),B_128),k1_relat_1('#skF_10'))
      | ~ v1_funct_1('#skF_10')
      | ~ v1_relat_1('#skF_10')
      | ~ r2_hidden(B_128,k1_relat_1(k2_funct_1('#skF_10'))) ) ),
    inference(resolution,[status(thm)],[c_369,c_20])).

tff(c_1234,plain,(
    ! [B_174] :
      ( k1_funct_1('#skF_10',k1_funct_1(k2_funct_1('#skF_10'),B_174)) = B_174
      | ~ r2_hidden(k1_funct_1(k2_funct_1('#skF_10'),B_174),k1_relat_1('#skF_10'))
      | ~ r2_hidden(B_174,k1_relat_1(k2_funct_1('#skF_10'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_382])).

tff(c_1272,plain,(
    ! [B_175] :
      ( k1_funct_1('#skF_10',k1_funct_1(k2_funct_1('#skF_10'),B_175)) = B_175
      | ~ r2_hidden(B_175,k1_relat_1(k2_funct_1('#skF_10'))) ) ),
    inference(resolution,[status(thm)],[c_413,c_1234])).

tff(c_1327,plain,(
    ! [C_176] :
      ( k1_funct_1('#skF_10',k1_funct_1(k2_funct_1('#skF_10'),C_176)) = C_176
      | ~ r2_hidden(C_176,k2_relat_1('#skF_10')) ) ),
    inference(resolution,[status(thm)],[c_746,c_1272])).

tff(c_54,plain,
    ( k1_funct_1(k5_relat_1(k2_funct_1('#skF_10'),'#skF_10'),'#skF_9') != '#skF_9'
    | k1_funct_1('#skF_10',k1_funct_1(k2_funct_1('#skF_10'),'#skF_9')) != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_82,plain,(
    k1_funct_1('#skF_10',k1_funct_1(k2_funct_1('#skF_10'),'#skF_9')) != '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_1362,plain,(
    ~ r2_hidden('#skF_9',k2_relat_1('#skF_10')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1327,c_82])).

tff(c_1398,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_1362])).

tff(c_1400,plain,(
    k1_funct_1('#skF_10',k1_funct_1(k2_funct_1('#skF_10'),'#skF_9')) = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_2332,plain,(
    ! [D_275,C_276,A_277] :
      ( r2_hidden(k4_tarski(D_275,C_276),A_277)
      | ~ r2_hidden(k4_tarski(C_276,D_275),k4_relat_1(A_277))
      | ~ v1_relat_1(k4_relat_1(A_277))
      | ~ v1_relat_1(A_277) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2342,plain,(
    ! [D_275,C_276] :
      ( r2_hidden(k4_tarski(D_275,C_276),'#skF_10')
      | ~ r2_hidden(k4_tarski(C_276,D_275),k2_funct_1('#skF_10'))
      | ~ v1_relat_1(k4_relat_1('#skF_10'))
      | ~ v1_relat_1('#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_2332])).

tff(c_2347,plain,(
    ! [D_278,C_279] :
      ( r2_hidden(k4_tarski(D_278,C_279),'#skF_10')
      | ~ r2_hidden(k4_tarski(C_279,D_278),k2_funct_1('#skF_10')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_80,c_72,c_2342])).

tff(c_2354,plain,(
    ! [B_25] :
      ( r2_hidden(k4_tarski(k1_funct_1(k2_funct_1('#skF_10'),B_25),B_25),'#skF_10')
      | ~ r2_hidden(B_25,k1_relat_1(k2_funct_1('#skF_10')))
      | ~ v1_funct_1(k2_funct_1('#skF_10'))
      | ~ v1_relat_1(k2_funct_1('#skF_10')) ) ),
    inference(resolution,[status(thm)],[c_22,c_2347])).

tff(c_2358,plain,(
    ! [B_25] :
      ( r2_hidden(k4_tarski(k1_funct_1(k2_funct_1('#skF_10'),B_25),B_25),'#skF_10')
      | ~ r2_hidden(B_25,k1_relat_1(k2_funct_1('#skF_10')))
      | ~ v1_funct_1(k2_funct_1('#skF_10')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_2354])).

tff(c_2451,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_10')) ),
    inference(splitLeft,[status(thm)],[c_2358])).

tff(c_2454,plain,
    ( ~ v1_funct_1('#skF_10')
    | ~ v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_48,c_2451])).

tff(c_2458,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_2454])).

tff(c_2460,plain,(
    v1_funct_1(k2_funct_1('#skF_10')) ),
    inference(splitRight,[status(thm)],[c_2358])).

tff(c_1502,plain,(
    ! [C_200,D_201,A_202] :
      ( r2_hidden(k4_tarski(C_200,D_201),k4_relat_1(A_202))
      | ~ r2_hidden(k4_tarski(D_201,C_200),A_202)
      | ~ v1_relat_1(k4_relat_1(A_202))
      | ~ v1_relat_1(A_202) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1514,plain,(
    ! [C_200,D_201] :
      ( r2_hidden(k4_tarski(C_200,D_201),k2_funct_1('#skF_10'))
      | ~ r2_hidden(k4_tarski(D_201,C_200),'#skF_10')
      | ~ v1_relat_1(k4_relat_1('#skF_10'))
      | ~ v1_relat_1('#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_1502])).

tff(c_1520,plain,(
    ! [C_203,D_204] :
      ( r2_hidden(k4_tarski(C_203,D_204),k2_funct_1('#skF_10'))
      | ~ r2_hidden(k4_tarski(D_204,C_203),'#skF_10') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_80,c_72,c_1514])).

tff(c_1526,plain,(
    ! [C_203,D_204] :
      ( r2_hidden(C_203,k1_relat_1(k2_funct_1('#skF_10')))
      | ~ v1_relat_1(k2_funct_1('#skF_10'))
      | ~ r2_hidden(k4_tarski(D_204,C_203),'#skF_10') ) ),
    inference(resolution,[status(thm)],[c_1520,c_18])).

tff(c_1537,plain,(
    ! [C_205,D_206] :
      ( r2_hidden(C_205,k1_relat_1(k2_funct_1('#skF_10')))
      | ~ r2_hidden(k4_tarski(D_206,C_205),'#skF_10') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_1526])).

tff(c_1540,plain,(
    ! [B_25] :
      ( r2_hidden(k1_funct_1('#skF_10',B_25),k1_relat_1(k2_funct_1('#skF_10')))
      | ~ r2_hidden(B_25,k1_relat_1('#skF_10'))
      | ~ v1_funct_1('#skF_10')
      | ~ v1_relat_1('#skF_10') ) ),
    inference(resolution,[status(thm)],[c_22,c_1537])).

tff(c_1563,plain,(
    ! [B_212] :
      ( r2_hidden(k1_funct_1('#skF_10',B_212),k1_relat_1(k2_funct_1('#skF_10')))
      | ~ r2_hidden(B_212,k1_relat_1('#skF_10')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_1540])).

tff(c_1567,plain,(
    ! [C_63] :
      ( r2_hidden(C_63,k1_relat_1(k2_funct_1('#skF_10')))
      | ~ r2_hidden('#skF_8'('#skF_10',k2_relat_1('#skF_10'),C_63),k1_relat_1('#skF_10'))
      | ~ r2_hidden(C_63,k2_relat_1('#skF_10'))
      | ~ v1_funct_1('#skF_10')
      | ~ v1_relat_1('#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_1563])).

tff(c_2106,plain,(
    ! [C_250] :
      ( r2_hidden(C_250,k1_relat_1(k2_funct_1('#skF_10')))
      | ~ r2_hidden('#skF_8'('#skF_10',k2_relat_1('#skF_10'),C_250),k1_relat_1('#skF_10'))
      | ~ r2_hidden(C_250,k2_relat_1('#skF_10')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_1567])).

tff(c_2113,plain,(
    ! [C_63] :
      ( r2_hidden(C_63,k1_relat_1(k2_funct_1('#skF_10')))
      | ~ r2_hidden(C_63,k2_relat_1('#skF_10'))
      | ~ v1_funct_1('#skF_10')
      | ~ v1_relat_1('#skF_10') ) ),
    inference(resolution,[status(thm)],[c_32,c_2106])).

tff(c_2146,plain,(
    ! [C_253] :
      ( r2_hidden(C_253,k1_relat_1(k2_funct_1('#skF_10')))
      | ~ r2_hidden(C_253,k2_relat_1('#skF_10')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_2113])).

tff(c_1468,plain,(
    ! [D_193,C_194,A_195] :
      ( r2_hidden(k4_tarski(D_193,C_194),A_195)
      | ~ r2_hidden(k4_tarski(C_194,D_193),k4_relat_1(A_195))
      | ~ v1_relat_1(k4_relat_1(A_195))
      | ~ v1_relat_1(A_195) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1475,plain,(
    ! [D_193,C_194] :
      ( r2_hidden(k4_tarski(D_193,C_194),'#skF_10')
      | ~ r2_hidden(k4_tarski(C_194,D_193),k2_funct_1('#skF_10'))
      | ~ v1_relat_1(k4_relat_1('#skF_10'))
      | ~ v1_relat_1('#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_1468])).

tff(c_1479,plain,(
    ! [D_196,C_197] :
      ( r2_hidden(k4_tarski(D_196,C_197),'#skF_10')
      | ~ r2_hidden(k4_tarski(C_197,D_196),k2_funct_1('#skF_10')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_80,c_72,c_1475])).

tff(c_1483,plain,(
    ! [B_25] :
      ( r2_hidden(k4_tarski(k1_funct_1(k2_funct_1('#skF_10'),B_25),B_25),'#skF_10')
      | ~ r2_hidden(B_25,k1_relat_1(k2_funct_1('#skF_10')))
      | ~ v1_funct_1(k2_funct_1('#skF_10'))
      | ~ v1_relat_1(k2_funct_1('#skF_10')) ) ),
    inference(resolution,[status(thm)],[c_22,c_1479])).

tff(c_1486,plain,(
    ! [B_25] :
      ( r2_hidden(k4_tarski(k1_funct_1(k2_funct_1('#skF_10'),B_25),B_25),'#skF_10')
      | ~ r2_hidden(B_25,k1_relat_1(k2_funct_1('#skF_10')))
      | ~ v1_funct_1(k2_funct_1('#skF_10')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_1483])).

tff(c_1726,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_10')) ),
    inference(splitLeft,[status(thm)],[c_1486])).

tff(c_1729,plain,
    ( ~ v1_funct_1('#skF_10')
    | ~ v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_48,c_1726])).

tff(c_1733,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_1729])).

tff(c_1736,plain,(
    ! [B_230] :
      ( r2_hidden(k4_tarski(k1_funct_1(k2_funct_1('#skF_10'),B_230),B_230),'#skF_10')
      | ~ r2_hidden(B_230,k1_relat_1(k2_funct_1('#skF_10'))) ) ),
    inference(splitRight,[status(thm)],[c_1486])).

tff(c_1754,plain,(
    ! [B_230] :
      ( r2_hidden(k1_funct_1(k2_funct_1('#skF_10'),B_230),k1_relat_1('#skF_10'))
      | ~ v1_relat_1('#skF_10')
      | ~ r2_hidden(B_230,k1_relat_1(k2_funct_1('#skF_10'))) ) ),
    inference(resolution,[status(thm)],[c_1736,c_18])).

tff(c_1884,plain,(
    ! [B_237] :
      ( r2_hidden(k1_funct_1(k2_funct_1('#skF_10'),B_237),k1_relat_1('#skF_10'))
      | ~ r2_hidden(B_237,k1_relat_1(k2_funct_1('#skF_10'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_1754])).

tff(c_1424,plain,(
    ! [B_187,A_188] :
      ( r2_hidden(k4_tarski(B_187,k1_funct_1(A_188,B_187)),A_188)
      | ~ r2_hidden(B_187,k1_relat_1(A_188))
      | ~ v1_funct_1(A_188)
      | ~ v1_relat_1(A_188) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_1433,plain,
    ( r2_hidden(k4_tarski(k1_funct_1(k2_funct_1('#skF_10'),'#skF_9'),'#skF_9'),'#skF_10')
    | ~ r2_hidden(k1_funct_1(k2_funct_1('#skF_10'),'#skF_9'),k1_relat_1('#skF_10'))
    | ~ v1_funct_1('#skF_10')
    | ~ v1_relat_1('#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_1400,c_1424])).

tff(c_1437,plain,
    ( r2_hidden(k4_tarski(k1_funct_1(k2_funct_1('#skF_10'),'#skF_9'),'#skF_9'),'#skF_10')
    | ~ r2_hidden(k1_funct_1(k2_funct_1('#skF_10'),'#skF_9'),k1_relat_1('#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_1433])).

tff(c_1438,plain,(
    ~ r2_hidden(k1_funct_1(k2_funct_1('#skF_10'),'#skF_9'),k1_relat_1('#skF_10')) ),
    inference(splitLeft,[status(thm)],[c_1437])).

tff(c_1892,plain,(
    ~ r2_hidden('#skF_9',k1_relat_1(k2_funct_1('#skF_10'))) ),
    inference(resolution,[status(thm)],[c_1884,c_1438])).

tff(c_2154,plain,(
    ~ r2_hidden('#skF_9',k2_relat_1('#skF_10')) ),
    inference(resolution,[status(thm)],[c_2146,c_1892])).

tff(c_2181,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_2154])).

tff(c_2182,plain,(
    r2_hidden(k4_tarski(k1_funct_1(k2_funct_1('#skF_10'),'#skF_9'),'#skF_9'),'#skF_10') ),
    inference(splitRight,[status(thm)],[c_1437])).

tff(c_2212,plain,(
    ! [C_258,D_259,A_260] :
      ( r2_hidden(k4_tarski(C_258,D_259),k4_relat_1(A_260))
      | ~ r2_hidden(k4_tarski(D_259,C_258),A_260)
      | ~ v1_relat_1(k4_relat_1(A_260))
      | ~ v1_relat_1(A_260) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2221,plain,(
    ! [C_258,D_259] :
      ( r2_hidden(k4_tarski(C_258,D_259),k2_funct_1('#skF_10'))
      | ~ r2_hidden(k4_tarski(D_259,C_258),'#skF_10')
      | ~ v1_relat_1(k4_relat_1('#skF_10'))
      | ~ v1_relat_1('#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_2212])).

tff(c_2226,plain,(
    ! [C_261,D_262] :
      ( r2_hidden(k4_tarski(C_261,D_262),k2_funct_1('#skF_10'))
      | ~ r2_hidden(k4_tarski(D_262,C_261),'#skF_10') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_80,c_72,c_2221])).

tff(c_2229,plain,(
    ! [C_261,D_262] :
      ( r2_hidden(C_261,k1_relat_1(k2_funct_1('#skF_10')))
      | ~ v1_relat_1(k2_funct_1('#skF_10'))
      | ~ r2_hidden(k4_tarski(D_262,C_261),'#skF_10') ) ),
    inference(resolution,[status(thm)],[c_2226,c_18])).

tff(c_2239,plain,(
    ! [C_263,D_264] :
      ( r2_hidden(C_263,k1_relat_1(k2_funct_1('#skF_10')))
      | ~ r2_hidden(k4_tarski(D_264,C_263),'#skF_10') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_2229])).

tff(c_2245,plain,(
    r2_hidden('#skF_9',k1_relat_1(k2_funct_1('#skF_10'))) ),
    inference(resolution,[status(thm)],[c_2182,c_2239])).

tff(c_3084,plain,(
    ! [B_326,C_327,A_328] :
      ( k1_funct_1(k5_relat_1(B_326,C_327),A_328) = k1_funct_1(C_327,k1_funct_1(B_326,A_328))
      | ~ r2_hidden(A_328,k1_relat_1(B_326))
      | ~ v1_funct_1(C_327)
      | ~ v1_relat_1(C_327)
      | ~ v1_funct_1(B_326)
      | ~ v1_relat_1(B_326) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_3113,plain,(
    ! [C_327] :
      ( k1_funct_1(k5_relat_1(k2_funct_1('#skF_10'),C_327),'#skF_9') = k1_funct_1(C_327,k1_funct_1(k2_funct_1('#skF_10'),'#skF_9'))
      | ~ v1_funct_1(C_327)
      | ~ v1_relat_1(C_327)
      | ~ v1_funct_1(k2_funct_1('#skF_10'))
      | ~ v1_relat_1(k2_funct_1('#skF_10')) ) ),
    inference(resolution,[status(thm)],[c_2245,c_3084])).

tff(c_3252,plain,(
    ! [C_337] :
      ( k1_funct_1(k5_relat_1(k2_funct_1('#skF_10'),C_337),'#skF_9') = k1_funct_1(C_337,k1_funct_1(k2_funct_1('#skF_10'),'#skF_9'))
      | ~ v1_funct_1(C_337)
      | ~ v1_relat_1(C_337) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_2460,c_3113])).

tff(c_1399,plain,(
    k1_funct_1(k5_relat_1(k2_funct_1('#skF_10'),'#skF_10'),'#skF_9') != '#skF_9' ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_3264,plain,
    ( k1_funct_1('#skF_10',k1_funct_1(k2_funct_1('#skF_10'),'#skF_9')) != '#skF_9'
    | ~ v1_funct_1('#skF_10')
    | ~ v1_relat_1('#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_3252,c_1399])).

tff(c_3271,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_1400,c_3264])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n010.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 14:17:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.10/2.03  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.10/2.04  
% 5.10/2.04  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.45/2.04  %$ r2_hidden > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > k4_tarski > k1_funct_1 > #nlpp > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_3 > #skF_10 > #skF_9 > #skF_2 > #skF_8 > #skF_7 > #skF_1 > #skF_5 > #skF_4
% 5.45/2.04  
% 5.45/2.04  %Foreground sorts:
% 5.45/2.04  
% 5.45/2.04  
% 5.45/2.04  %Background operators:
% 5.45/2.04  
% 5.45/2.04  
% 5.45/2.04  %Foreground operators:
% 5.45/2.04  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 5.45/2.04  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.45/2.04  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 5.45/2.04  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 5.45/2.04  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.45/2.04  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.45/2.04  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 5.45/2.04  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.45/2.04  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 5.45/2.04  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 5.45/2.04  tff('#skF_10', type, '#skF_10': $i).
% 5.45/2.04  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.45/2.04  tff('#skF_9', type, '#skF_9': $i).
% 5.45/2.04  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 5.45/2.04  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.45/2.04  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.45/2.04  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.45/2.04  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 5.45/2.04  tff('#skF_8', type, '#skF_8': ($i * $i * $i) > $i).
% 5.45/2.04  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 5.45/2.04  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.45/2.04  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 5.45/2.04  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.45/2.04  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 5.45/2.04  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 5.45/2.04  
% 5.45/2.07  tff(f_124, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v2_funct_1(B) & r2_hidden(A, k2_relat_1(B))) => ((A = k1_funct_1(B, k1_funct_1(k2_funct_1(B), A))) & (A = k1_funct_1(k5_relat_1(k2_funct_1(B), B), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t57_funct_1)).
% 5.45/2.07  tff(f_82, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_funct_1)).
% 5.45/2.07  tff(f_67, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: ((r2_hidden(B, k1_relat_1(A)) => ((C = k1_funct_1(A, B)) <=> r2_hidden(k4_tarski(B, C), A))) & (~r2_hidden(B, k1_relat_1(A)) => ((C = k1_funct_1(A, B)) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_funct_1)).
% 5.45/2.07  tff(f_90, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(A) = k4_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_funct_1)).
% 5.45/2.07  tff(f_41, axiom, (![A]: (v1_relat_1(A) => v1_relat_1(k4_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_relat_1)).
% 5.45/2.07  tff(f_37, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => ((B = k4_relat_1(A)) <=> (![C, D]: (r2_hidden(k4_tarski(C, D), B) <=> r2_hidden(k4_tarski(D, C), A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_relat_1)).
% 5.45/2.07  tff(f_49, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) => (r2_hidden(A, k1_relat_1(C)) & r2_hidden(B, k2_relat_1(C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_relat_1)).
% 5.45/2.07  tff(f_98, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 5.45/2.07  tff(f_111, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(B)) => (k1_funct_1(k5_relat_1(B, C), A) = k1_funct_1(C, k1_funct_1(B, A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_funct_1)).
% 5.45/2.07  tff(c_62, plain, (v1_relat_1('#skF_10')), inference(cnfTransformation, [status(thm)], [f_124])).
% 5.45/2.07  tff(c_60, plain, (v1_funct_1('#skF_10')), inference(cnfTransformation, [status(thm)], [f_124])).
% 5.45/2.07  tff(c_56, plain, (r2_hidden('#skF_9', k2_relat_1('#skF_10'))), inference(cnfTransformation, [status(thm)], [f_124])).
% 5.45/2.07  tff(c_32, plain, (![A_27, C_63]: (r2_hidden('#skF_8'(A_27, k2_relat_1(A_27), C_63), k1_relat_1(A_27)) | ~r2_hidden(C_63, k2_relat_1(A_27)) | ~v1_funct_1(A_27) | ~v1_relat_1(A_27))), inference(cnfTransformation, [status(thm)], [f_82])).
% 5.45/2.07  tff(c_30, plain, (![A_27, C_63]: (k1_funct_1(A_27, '#skF_8'(A_27, k2_relat_1(A_27), C_63))=C_63 | ~r2_hidden(C_63, k2_relat_1(A_27)) | ~v1_funct_1(A_27) | ~v1_relat_1(A_27))), inference(cnfTransformation, [status(thm)], [f_82])).
% 5.45/2.07  tff(c_22, plain, (![B_25, A_22]: (r2_hidden(k4_tarski(B_25, k1_funct_1(A_22, B_25)), A_22) | ~r2_hidden(B_25, k1_relat_1(A_22)) | ~v1_funct_1(A_22) | ~v1_relat_1(A_22))), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.45/2.07  tff(c_58, plain, (v2_funct_1('#skF_10')), inference(cnfTransformation, [status(thm)], [f_124])).
% 5.45/2.07  tff(c_66, plain, (![A_76]: (k4_relat_1(A_76)=k2_funct_1(A_76) | ~v2_funct_1(A_76) | ~v1_funct_1(A_76) | ~v1_relat_1(A_76))), inference(cnfTransformation, [status(thm)], [f_90])).
% 5.45/2.07  tff(c_69, plain, (k4_relat_1('#skF_10')=k2_funct_1('#skF_10') | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_58, c_66])).
% 5.45/2.07  tff(c_72, plain, (k4_relat_1('#skF_10')=k2_funct_1('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_69])).
% 5.45/2.07  tff(c_14, plain, (![A_18]: (v1_relat_1(k4_relat_1(A_18)) | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.45/2.07  tff(c_76, plain, (v1_relat_1(k2_funct_1('#skF_10')) | ~v1_relat_1('#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_72, c_14])).
% 5.45/2.07  tff(c_80, plain, (v1_relat_1(k2_funct_1('#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_76])).
% 5.45/2.07  tff(c_141, plain, (![C_98, D_99, A_100]: (r2_hidden(k4_tarski(C_98, D_99), k4_relat_1(A_100)) | ~r2_hidden(k4_tarski(D_99, C_98), A_100) | ~v1_relat_1(k4_relat_1(A_100)) | ~v1_relat_1(A_100))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.45/2.07  tff(c_153, plain, (![C_98, D_99]: (r2_hidden(k4_tarski(C_98, D_99), k2_funct_1('#skF_10')) | ~r2_hidden(k4_tarski(D_99, C_98), '#skF_10') | ~v1_relat_1(k4_relat_1('#skF_10')) | ~v1_relat_1('#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_72, c_141])).
% 5.45/2.07  tff(c_159, plain, (![C_101, D_102]: (r2_hidden(k4_tarski(C_101, D_102), k2_funct_1('#skF_10')) | ~r2_hidden(k4_tarski(D_102, C_101), '#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_80, c_72, c_153])).
% 5.45/2.07  tff(c_18, plain, (![A_19, C_21, B_20]: (r2_hidden(A_19, k1_relat_1(C_21)) | ~r2_hidden(k4_tarski(A_19, B_20), C_21) | ~v1_relat_1(C_21))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.45/2.07  tff(c_168, plain, (![C_101, D_102]: (r2_hidden(C_101, k1_relat_1(k2_funct_1('#skF_10'))) | ~v1_relat_1(k2_funct_1('#skF_10')) | ~r2_hidden(k4_tarski(D_102, C_101), '#skF_10'))), inference(resolution, [status(thm)], [c_159, c_18])).
% 5.45/2.07  tff(c_220, plain, (![C_109, D_110]: (r2_hidden(C_109, k1_relat_1(k2_funct_1('#skF_10'))) | ~r2_hidden(k4_tarski(D_110, C_109), '#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_168])).
% 5.45/2.07  tff(c_223, plain, (![B_25]: (r2_hidden(k1_funct_1('#skF_10', B_25), k1_relat_1(k2_funct_1('#skF_10'))) | ~r2_hidden(B_25, k1_relat_1('#skF_10')) | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10'))), inference(resolution, [status(thm)], [c_22, c_220])).
% 5.45/2.07  tff(c_227, plain, (![B_111]: (r2_hidden(k1_funct_1('#skF_10', B_111), k1_relat_1(k2_funct_1('#skF_10'))) | ~r2_hidden(B_111, k1_relat_1('#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_223])).
% 5.45/2.07  tff(c_231, plain, (![C_63]: (r2_hidden(C_63, k1_relat_1(k2_funct_1('#skF_10'))) | ~r2_hidden('#skF_8'('#skF_10', k2_relat_1('#skF_10'), C_63), k1_relat_1('#skF_10')) | ~r2_hidden(C_63, k2_relat_1('#skF_10')) | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_30, c_227])).
% 5.45/2.07  tff(c_736, plain, (![C_152]: (r2_hidden(C_152, k1_relat_1(k2_funct_1('#skF_10'))) | ~r2_hidden('#skF_8'('#skF_10', k2_relat_1('#skF_10'), C_152), k1_relat_1('#skF_10')) | ~r2_hidden(C_152, k2_relat_1('#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_231])).
% 5.45/2.07  tff(c_740, plain, (![C_63]: (r2_hidden(C_63, k1_relat_1(k2_funct_1('#skF_10'))) | ~r2_hidden(C_63, k2_relat_1('#skF_10')) | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10'))), inference(resolution, [status(thm)], [c_32, c_736])).
% 5.45/2.07  tff(c_746, plain, (![C_63]: (r2_hidden(C_63, k1_relat_1(k2_funct_1('#skF_10'))) | ~r2_hidden(C_63, k2_relat_1('#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_740])).
% 5.45/2.07  tff(c_48, plain, (![A_68]: (v1_funct_1(k2_funct_1(A_68)) | ~v1_funct_1(A_68) | ~v1_relat_1(A_68))), inference(cnfTransformation, [status(thm)], [f_98])).
% 5.45/2.07  tff(c_107, plain, (![D_91, C_92, A_93]: (r2_hidden(k4_tarski(D_91, C_92), A_93) | ~r2_hidden(k4_tarski(C_92, D_91), k4_relat_1(A_93)) | ~v1_relat_1(k4_relat_1(A_93)) | ~v1_relat_1(A_93))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.45/2.07  tff(c_114, plain, (![D_91, C_92]: (r2_hidden(k4_tarski(D_91, C_92), '#skF_10') | ~r2_hidden(k4_tarski(C_92, D_91), k2_funct_1('#skF_10')) | ~v1_relat_1(k4_relat_1('#skF_10')) | ~v1_relat_1('#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_72, c_107])).
% 5.45/2.07  tff(c_118, plain, (![D_94, C_95]: (r2_hidden(k4_tarski(D_94, C_95), '#skF_10') | ~r2_hidden(k4_tarski(C_95, D_94), k2_funct_1('#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_80, c_72, c_114])).
% 5.45/2.07  tff(c_122, plain, (![B_25]: (r2_hidden(k4_tarski(k1_funct_1(k2_funct_1('#skF_10'), B_25), B_25), '#skF_10') | ~r2_hidden(B_25, k1_relat_1(k2_funct_1('#skF_10'))) | ~v1_funct_1(k2_funct_1('#skF_10')) | ~v1_relat_1(k2_funct_1('#skF_10')))), inference(resolution, [status(thm)], [c_22, c_118])).
% 5.45/2.07  tff(c_125, plain, (![B_25]: (r2_hidden(k4_tarski(k1_funct_1(k2_funct_1('#skF_10'), B_25), B_25), '#skF_10') | ~r2_hidden(B_25, k1_relat_1(k2_funct_1('#skF_10'))) | ~v1_funct_1(k2_funct_1('#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_122])).
% 5.45/2.07  tff(c_359, plain, (~v1_funct_1(k2_funct_1('#skF_10'))), inference(splitLeft, [status(thm)], [c_125])).
% 5.45/2.07  tff(c_362, plain, (~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_48, c_359])).
% 5.45/2.07  tff(c_366, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_362])).
% 5.45/2.07  tff(c_369, plain, (![B_128]: (r2_hidden(k4_tarski(k1_funct_1(k2_funct_1('#skF_10'), B_128), B_128), '#skF_10') | ~r2_hidden(B_128, k1_relat_1(k2_funct_1('#skF_10'))))), inference(splitRight, [status(thm)], [c_125])).
% 5.45/2.07  tff(c_390, plain, (![B_128]: (r2_hidden(k1_funct_1(k2_funct_1('#skF_10'), B_128), k1_relat_1('#skF_10')) | ~v1_relat_1('#skF_10') | ~r2_hidden(B_128, k1_relat_1(k2_funct_1('#skF_10'))))), inference(resolution, [status(thm)], [c_369, c_18])).
% 5.45/2.07  tff(c_413, plain, (![B_128]: (r2_hidden(k1_funct_1(k2_funct_1('#skF_10'), B_128), k1_relat_1('#skF_10')) | ~r2_hidden(B_128, k1_relat_1(k2_funct_1('#skF_10'))))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_390])).
% 5.45/2.07  tff(c_20, plain, (![A_22, B_25, C_26]: (k1_funct_1(A_22, B_25)=C_26 | ~r2_hidden(k4_tarski(B_25, C_26), A_22) | ~r2_hidden(B_25, k1_relat_1(A_22)) | ~v1_funct_1(A_22) | ~v1_relat_1(A_22))), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.45/2.07  tff(c_382, plain, (![B_128]: (k1_funct_1('#skF_10', k1_funct_1(k2_funct_1('#skF_10'), B_128))=B_128 | ~r2_hidden(k1_funct_1(k2_funct_1('#skF_10'), B_128), k1_relat_1('#skF_10')) | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10') | ~r2_hidden(B_128, k1_relat_1(k2_funct_1('#skF_10'))))), inference(resolution, [status(thm)], [c_369, c_20])).
% 5.45/2.07  tff(c_1234, plain, (![B_174]: (k1_funct_1('#skF_10', k1_funct_1(k2_funct_1('#skF_10'), B_174))=B_174 | ~r2_hidden(k1_funct_1(k2_funct_1('#skF_10'), B_174), k1_relat_1('#skF_10')) | ~r2_hidden(B_174, k1_relat_1(k2_funct_1('#skF_10'))))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_382])).
% 5.45/2.07  tff(c_1272, plain, (![B_175]: (k1_funct_1('#skF_10', k1_funct_1(k2_funct_1('#skF_10'), B_175))=B_175 | ~r2_hidden(B_175, k1_relat_1(k2_funct_1('#skF_10'))))), inference(resolution, [status(thm)], [c_413, c_1234])).
% 5.45/2.07  tff(c_1327, plain, (![C_176]: (k1_funct_1('#skF_10', k1_funct_1(k2_funct_1('#skF_10'), C_176))=C_176 | ~r2_hidden(C_176, k2_relat_1('#skF_10')))), inference(resolution, [status(thm)], [c_746, c_1272])).
% 5.45/2.07  tff(c_54, plain, (k1_funct_1(k5_relat_1(k2_funct_1('#skF_10'), '#skF_10'), '#skF_9')!='#skF_9' | k1_funct_1('#skF_10', k1_funct_1(k2_funct_1('#skF_10'), '#skF_9'))!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_124])).
% 5.45/2.07  tff(c_82, plain, (k1_funct_1('#skF_10', k1_funct_1(k2_funct_1('#skF_10'), '#skF_9'))!='#skF_9'), inference(splitLeft, [status(thm)], [c_54])).
% 5.45/2.07  tff(c_1362, plain, (~r2_hidden('#skF_9', k2_relat_1('#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_1327, c_82])).
% 5.45/2.07  tff(c_1398, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_1362])).
% 5.45/2.07  tff(c_1400, plain, (k1_funct_1('#skF_10', k1_funct_1(k2_funct_1('#skF_10'), '#skF_9'))='#skF_9'), inference(splitRight, [status(thm)], [c_54])).
% 5.45/2.07  tff(c_2332, plain, (![D_275, C_276, A_277]: (r2_hidden(k4_tarski(D_275, C_276), A_277) | ~r2_hidden(k4_tarski(C_276, D_275), k4_relat_1(A_277)) | ~v1_relat_1(k4_relat_1(A_277)) | ~v1_relat_1(A_277))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.45/2.07  tff(c_2342, plain, (![D_275, C_276]: (r2_hidden(k4_tarski(D_275, C_276), '#skF_10') | ~r2_hidden(k4_tarski(C_276, D_275), k2_funct_1('#skF_10')) | ~v1_relat_1(k4_relat_1('#skF_10')) | ~v1_relat_1('#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_72, c_2332])).
% 5.45/2.07  tff(c_2347, plain, (![D_278, C_279]: (r2_hidden(k4_tarski(D_278, C_279), '#skF_10') | ~r2_hidden(k4_tarski(C_279, D_278), k2_funct_1('#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_80, c_72, c_2342])).
% 5.45/2.07  tff(c_2354, plain, (![B_25]: (r2_hidden(k4_tarski(k1_funct_1(k2_funct_1('#skF_10'), B_25), B_25), '#skF_10') | ~r2_hidden(B_25, k1_relat_1(k2_funct_1('#skF_10'))) | ~v1_funct_1(k2_funct_1('#skF_10')) | ~v1_relat_1(k2_funct_1('#skF_10')))), inference(resolution, [status(thm)], [c_22, c_2347])).
% 5.45/2.07  tff(c_2358, plain, (![B_25]: (r2_hidden(k4_tarski(k1_funct_1(k2_funct_1('#skF_10'), B_25), B_25), '#skF_10') | ~r2_hidden(B_25, k1_relat_1(k2_funct_1('#skF_10'))) | ~v1_funct_1(k2_funct_1('#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_2354])).
% 5.45/2.07  tff(c_2451, plain, (~v1_funct_1(k2_funct_1('#skF_10'))), inference(splitLeft, [status(thm)], [c_2358])).
% 5.45/2.07  tff(c_2454, plain, (~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_48, c_2451])).
% 5.45/2.07  tff(c_2458, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_2454])).
% 5.45/2.07  tff(c_2460, plain, (v1_funct_1(k2_funct_1('#skF_10'))), inference(splitRight, [status(thm)], [c_2358])).
% 5.45/2.07  tff(c_1502, plain, (![C_200, D_201, A_202]: (r2_hidden(k4_tarski(C_200, D_201), k4_relat_1(A_202)) | ~r2_hidden(k4_tarski(D_201, C_200), A_202) | ~v1_relat_1(k4_relat_1(A_202)) | ~v1_relat_1(A_202))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.45/2.07  tff(c_1514, plain, (![C_200, D_201]: (r2_hidden(k4_tarski(C_200, D_201), k2_funct_1('#skF_10')) | ~r2_hidden(k4_tarski(D_201, C_200), '#skF_10') | ~v1_relat_1(k4_relat_1('#skF_10')) | ~v1_relat_1('#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_72, c_1502])).
% 5.45/2.07  tff(c_1520, plain, (![C_203, D_204]: (r2_hidden(k4_tarski(C_203, D_204), k2_funct_1('#skF_10')) | ~r2_hidden(k4_tarski(D_204, C_203), '#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_80, c_72, c_1514])).
% 5.45/2.07  tff(c_1526, plain, (![C_203, D_204]: (r2_hidden(C_203, k1_relat_1(k2_funct_1('#skF_10'))) | ~v1_relat_1(k2_funct_1('#skF_10')) | ~r2_hidden(k4_tarski(D_204, C_203), '#skF_10'))), inference(resolution, [status(thm)], [c_1520, c_18])).
% 5.45/2.07  tff(c_1537, plain, (![C_205, D_206]: (r2_hidden(C_205, k1_relat_1(k2_funct_1('#skF_10'))) | ~r2_hidden(k4_tarski(D_206, C_205), '#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_1526])).
% 5.45/2.07  tff(c_1540, plain, (![B_25]: (r2_hidden(k1_funct_1('#skF_10', B_25), k1_relat_1(k2_funct_1('#skF_10'))) | ~r2_hidden(B_25, k1_relat_1('#skF_10')) | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10'))), inference(resolution, [status(thm)], [c_22, c_1537])).
% 5.45/2.07  tff(c_1563, plain, (![B_212]: (r2_hidden(k1_funct_1('#skF_10', B_212), k1_relat_1(k2_funct_1('#skF_10'))) | ~r2_hidden(B_212, k1_relat_1('#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_1540])).
% 5.45/2.07  tff(c_1567, plain, (![C_63]: (r2_hidden(C_63, k1_relat_1(k2_funct_1('#skF_10'))) | ~r2_hidden('#skF_8'('#skF_10', k2_relat_1('#skF_10'), C_63), k1_relat_1('#skF_10')) | ~r2_hidden(C_63, k2_relat_1('#skF_10')) | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_30, c_1563])).
% 5.45/2.07  tff(c_2106, plain, (![C_250]: (r2_hidden(C_250, k1_relat_1(k2_funct_1('#skF_10'))) | ~r2_hidden('#skF_8'('#skF_10', k2_relat_1('#skF_10'), C_250), k1_relat_1('#skF_10')) | ~r2_hidden(C_250, k2_relat_1('#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_1567])).
% 5.45/2.07  tff(c_2113, plain, (![C_63]: (r2_hidden(C_63, k1_relat_1(k2_funct_1('#skF_10'))) | ~r2_hidden(C_63, k2_relat_1('#skF_10')) | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10'))), inference(resolution, [status(thm)], [c_32, c_2106])).
% 5.45/2.07  tff(c_2146, plain, (![C_253]: (r2_hidden(C_253, k1_relat_1(k2_funct_1('#skF_10'))) | ~r2_hidden(C_253, k2_relat_1('#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_2113])).
% 5.45/2.07  tff(c_1468, plain, (![D_193, C_194, A_195]: (r2_hidden(k4_tarski(D_193, C_194), A_195) | ~r2_hidden(k4_tarski(C_194, D_193), k4_relat_1(A_195)) | ~v1_relat_1(k4_relat_1(A_195)) | ~v1_relat_1(A_195))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.45/2.07  tff(c_1475, plain, (![D_193, C_194]: (r2_hidden(k4_tarski(D_193, C_194), '#skF_10') | ~r2_hidden(k4_tarski(C_194, D_193), k2_funct_1('#skF_10')) | ~v1_relat_1(k4_relat_1('#skF_10')) | ~v1_relat_1('#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_72, c_1468])).
% 5.45/2.07  tff(c_1479, plain, (![D_196, C_197]: (r2_hidden(k4_tarski(D_196, C_197), '#skF_10') | ~r2_hidden(k4_tarski(C_197, D_196), k2_funct_1('#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_80, c_72, c_1475])).
% 5.45/2.07  tff(c_1483, plain, (![B_25]: (r2_hidden(k4_tarski(k1_funct_1(k2_funct_1('#skF_10'), B_25), B_25), '#skF_10') | ~r2_hidden(B_25, k1_relat_1(k2_funct_1('#skF_10'))) | ~v1_funct_1(k2_funct_1('#skF_10')) | ~v1_relat_1(k2_funct_1('#skF_10')))), inference(resolution, [status(thm)], [c_22, c_1479])).
% 5.45/2.07  tff(c_1486, plain, (![B_25]: (r2_hidden(k4_tarski(k1_funct_1(k2_funct_1('#skF_10'), B_25), B_25), '#skF_10') | ~r2_hidden(B_25, k1_relat_1(k2_funct_1('#skF_10'))) | ~v1_funct_1(k2_funct_1('#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_1483])).
% 5.45/2.07  tff(c_1726, plain, (~v1_funct_1(k2_funct_1('#skF_10'))), inference(splitLeft, [status(thm)], [c_1486])).
% 5.45/2.07  tff(c_1729, plain, (~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_48, c_1726])).
% 5.45/2.07  tff(c_1733, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_1729])).
% 5.45/2.07  tff(c_1736, plain, (![B_230]: (r2_hidden(k4_tarski(k1_funct_1(k2_funct_1('#skF_10'), B_230), B_230), '#skF_10') | ~r2_hidden(B_230, k1_relat_1(k2_funct_1('#skF_10'))))), inference(splitRight, [status(thm)], [c_1486])).
% 5.45/2.07  tff(c_1754, plain, (![B_230]: (r2_hidden(k1_funct_1(k2_funct_1('#skF_10'), B_230), k1_relat_1('#skF_10')) | ~v1_relat_1('#skF_10') | ~r2_hidden(B_230, k1_relat_1(k2_funct_1('#skF_10'))))), inference(resolution, [status(thm)], [c_1736, c_18])).
% 5.45/2.07  tff(c_1884, plain, (![B_237]: (r2_hidden(k1_funct_1(k2_funct_1('#skF_10'), B_237), k1_relat_1('#skF_10')) | ~r2_hidden(B_237, k1_relat_1(k2_funct_1('#skF_10'))))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_1754])).
% 5.45/2.07  tff(c_1424, plain, (![B_187, A_188]: (r2_hidden(k4_tarski(B_187, k1_funct_1(A_188, B_187)), A_188) | ~r2_hidden(B_187, k1_relat_1(A_188)) | ~v1_funct_1(A_188) | ~v1_relat_1(A_188))), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.45/2.07  tff(c_1433, plain, (r2_hidden(k4_tarski(k1_funct_1(k2_funct_1('#skF_10'), '#skF_9'), '#skF_9'), '#skF_10') | ~r2_hidden(k1_funct_1(k2_funct_1('#skF_10'), '#skF_9'), k1_relat_1('#skF_10')) | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_1400, c_1424])).
% 5.45/2.07  tff(c_1437, plain, (r2_hidden(k4_tarski(k1_funct_1(k2_funct_1('#skF_10'), '#skF_9'), '#skF_9'), '#skF_10') | ~r2_hidden(k1_funct_1(k2_funct_1('#skF_10'), '#skF_9'), k1_relat_1('#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_1433])).
% 5.45/2.07  tff(c_1438, plain, (~r2_hidden(k1_funct_1(k2_funct_1('#skF_10'), '#skF_9'), k1_relat_1('#skF_10'))), inference(splitLeft, [status(thm)], [c_1437])).
% 5.45/2.07  tff(c_1892, plain, (~r2_hidden('#skF_9', k1_relat_1(k2_funct_1('#skF_10')))), inference(resolution, [status(thm)], [c_1884, c_1438])).
% 5.45/2.07  tff(c_2154, plain, (~r2_hidden('#skF_9', k2_relat_1('#skF_10'))), inference(resolution, [status(thm)], [c_2146, c_1892])).
% 5.45/2.07  tff(c_2181, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_2154])).
% 5.45/2.07  tff(c_2182, plain, (r2_hidden(k4_tarski(k1_funct_1(k2_funct_1('#skF_10'), '#skF_9'), '#skF_9'), '#skF_10')), inference(splitRight, [status(thm)], [c_1437])).
% 5.45/2.07  tff(c_2212, plain, (![C_258, D_259, A_260]: (r2_hidden(k4_tarski(C_258, D_259), k4_relat_1(A_260)) | ~r2_hidden(k4_tarski(D_259, C_258), A_260) | ~v1_relat_1(k4_relat_1(A_260)) | ~v1_relat_1(A_260))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.45/2.07  tff(c_2221, plain, (![C_258, D_259]: (r2_hidden(k4_tarski(C_258, D_259), k2_funct_1('#skF_10')) | ~r2_hidden(k4_tarski(D_259, C_258), '#skF_10') | ~v1_relat_1(k4_relat_1('#skF_10')) | ~v1_relat_1('#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_72, c_2212])).
% 5.45/2.07  tff(c_2226, plain, (![C_261, D_262]: (r2_hidden(k4_tarski(C_261, D_262), k2_funct_1('#skF_10')) | ~r2_hidden(k4_tarski(D_262, C_261), '#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_80, c_72, c_2221])).
% 5.45/2.07  tff(c_2229, plain, (![C_261, D_262]: (r2_hidden(C_261, k1_relat_1(k2_funct_1('#skF_10'))) | ~v1_relat_1(k2_funct_1('#skF_10')) | ~r2_hidden(k4_tarski(D_262, C_261), '#skF_10'))), inference(resolution, [status(thm)], [c_2226, c_18])).
% 5.45/2.07  tff(c_2239, plain, (![C_263, D_264]: (r2_hidden(C_263, k1_relat_1(k2_funct_1('#skF_10'))) | ~r2_hidden(k4_tarski(D_264, C_263), '#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_2229])).
% 5.45/2.07  tff(c_2245, plain, (r2_hidden('#skF_9', k1_relat_1(k2_funct_1('#skF_10')))), inference(resolution, [status(thm)], [c_2182, c_2239])).
% 5.45/2.07  tff(c_3084, plain, (![B_326, C_327, A_328]: (k1_funct_1(k5_relat_1(B_326, C_327), A_328)=k1_funct_1(C_327, k1_funct_1(B_326, A_328)) | ~r2_hidden(A_328, k1_relat_1(B_326)) | ~v1_funct_1(C_327) | ~v1_relat_1(C_327) | ~v1_funct_1(B_326) | ~v1_relat_1(B_326))), inference(cnfTransformation, [status(thm)], [f_111])).
% 5.45/2.07  tff(c_3113, plain, (![C_327]: (k1_funct_1(k5_relat_1(k2_funct_1('#skF_10'), C_327), '#skF_9')=k1_funct_1(C_327, k1_funct_1(k2_funct_1('#skF_10'), '#skF_9')) | ~v1_funct_1(C_327) | ~v1_relat_1(C_327) | ~v1_funct_1(k2_funct_1('#skF_10')) | ~v1_relat_1(k2_funct_1('#skF_10')))), inference(resolution, [status(thm)], [c_2245, c_3084])).
% 5.45/2.07  tff(c_3252, plain, (![C_337]: (k1_funct_1(k5_relat_1(k2_funct_1('#skF_10'), C_337), '#skF_9')=k1_funct_1(C_337, k1_funct_1(k2_funct_1('#skF_10'), '#skF_9')) | ~v1_funct_1(C_337) | ~v1_relat_1(C_337))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_2460, c_3113])).
% 5.45/2.07  tff(c_1399, plain, (k1_funct_1(k5_relat_1(k2_funct_1('#skF_10'), '#skF_10'), '#skF_9')!='#skF_9'), inference(splitRight, [status(thm)], [c_54])).
% 5.45/2.07  tff(c_3264, plain, (k1_funct_1('#skF_10', k1_funct_1(k2_funct_1('#skF_10'), '#skF_9'))!='#skF_9' | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_3252, c_1399])).
% 5.45/2.07  tff(c_3271, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_1400, c_3264])).
% 5.45/2.07  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.45/2.07  
% 5.45/2.07  Inference rules
% 5.45/2.07  ----------------------
% 5.45/2.07  #Ref     : 0
% 5.45/2.07  #Sup     : 639
% 5.45/2.07  #Fact    : 0
% 5.45/2.07  #Define  : 0
% 5.45/2.07  #Split   : 20
% 5.45/2.07  #Chain   : 0
% 5.45/2.07  #Close   : 0
% 5.45/2.07  
% 5.45/2.07  Ordering : KBO
% 5.45/2.07  
% 5.45/2.07  Simplification rules
% 5.45/2.07  ----------------------
% 5.45/2.07  #Subsume      : 124
% 5.45/2.07  #Demod        : 503
% 5.45/2.07  #Tautology    : 104
% 5.45/2.07  #SimpNegUnit  : 1
% 5.45/2.07  #BackRed      : 10
% 5.45/2.07  
% 5.45/2.07  #Partial instantiations: 0
% 5.45/2.07  #Strategies tried      : 1
% 5.45/2.07  
% 5.45/2.07  Timing (in seconds)
% 5.45/2.07  ----------------------
% 5.45/2.07  Preprocessing        : 0.37
% 5.45/2.07  Parsing              : 0.18
% 5.45/2.07  CNF conversion       : 0.03
% 5.45/2.07  Main loop            : 0.87
% 5.45/2.07  Inferencing          : 0.33
% 5.45/2.07  Reduction            : 0.27
% 5.45/2.07  Demodulation         : 0.18
% 5.45/2.07  BG Simplification    : 0.04
% 5.45/2.07  Subsumption          : 0.17
% 5.45/2.07  Abstraction          : 0.05
% 5.45/2.07  MUC search           : 0.00
% 5.45/2.07  Cooper               : 0.00
% 5.45/2.07  Total                : 1.29
% 5.45/2.07  Index Insertion      : 0.00
% 5.45/2.07  Index Deletion       : 0.00
% 5.45/2.07  Index Matching       : 0.00
% 5.45/2.07  BG Taut test         : 0.00
%------------------------------------------------------------------------------
