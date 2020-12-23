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
% DateTime   : Thu Dec  3 10:17:07 EST 2020

% Result     : Theorem 9.02s
% Output     : CNFRefutation 9.02s
% Verified   : 
% Statistics : Number of formulae       :  192 (42924 expanded)
%              Number of leaves         :   31 (14801 expanded)
%              Depth                    :   29
%              Number of atoms          :  508 (153080 expanded)
%              Number of equality atoms :   89 (31202 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v1_partfun1 > r2_hidden > r1_partfun1 > m1_subset_1 > v1_funct_1 > k5_partfun1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_4 > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_8 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(k5_partfun1,type,(
    k5_partfun1: ( $i * $i * $i ) > $i )).

tff(r1_partfun1,type,(
    r1_partfun1: ( $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_35,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_132,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,A,k1_tarski(B))
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
           => k5_partfun1(A,k1_tarski(B),C) = k1_tarski(D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t164_funct_2)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [D] :
          ( D = k5_partfun1(A,B,C)
        <=> ! [E] :
              ( r2_hidden(E,D)
            <=> ? [F] :
                  ( v1_funct_1(F)
                  & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(A,B)))
                  & F = E
                  & v1_partfun1(F,A)
                  & r1_partfun1(C,F) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_partfun1)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ( B = k1_xboole_0
            & A != k1_xboole_0 )
          | v1_partfun1(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t132_funct_2)).

tff(f_118,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( v1_partfun1(C,A)
      <=> k5_partfun1(A,B,C) = k1_tarski(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t174_partfun1)).

tff(f_93,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
     => ! [D] :
          ( ( v1_funct_1(D)
            & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
         => r1_partfun1(C,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_partfun1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( A != k1_xboole_0
     => ( k2_zfmisc_1(k1_tarski(B),A) != k1_xboole_0
        & k2_zfmisc_1(A,k1_tarski(B)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t130_zfmisc_1)).

tff(c_8,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_70,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_66,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_5',k1_tarski('#skF_6')))) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_64,plain,(
    k5_partfun1('#skF_5',k1_tarski('#skF_6'),'#skF_7') != k1_tarski('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_74,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_72,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5',k1_tarski('#skF_6')))) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_1965,plain,(
    ! [A_233,B_234,C_235,D_236] :
      ( '#skF_2'(A_233,B_234,C_235,D_236) = '#skF_1'(A_233,B_234,C_235,D_236)
      | r2_hidden('#skF_3'(A_233,B_234,C_235,D_236),D_236)
      | k5_partfun1(A_233,B_234,C_235) = D_236
      | ~ m1_subset_1(C_235,k1_zfmisc_1(k2_zfmisc_1(A_233,B_234)))
      | ~ v1_funct_1(C_235) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1975,plain,(
    ! [D_236] :
      ( '#skF_2'('#skF_5',k1_tarski('#skF_6'),'#skF_7',D_236) = '#skF_1'('#skF_5',k1_tarski('#skF_6'),'#skF_7',D_236)
      | r2_hidden('#skF_3'('#skF_5',k1_tarski('#skF_6'),'#skF_7',D_236),D_236)
      | k5_partfun1('#skF_5',k1_tarski('#skF_6'),'#skF_7') = D_236
      | ~ v1_funct_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_72,c_1965])).

tff(c_2113,plain,(
    ! [D_243] :
      ( '#skF_2'('#skF_5',k1_tarski('#skF_6'),'#skF_7',D_243) = '#skF_1'('#skF_5',k1_tarski('#skF_6'),'#skF_7',D_243)
      | r2_hidden('#skF_3'('#skF_5',k1_tarski('#skF_6'),'#skF_7',D_243),D_243)
      | k5_partfun1('#skF_5',k1_tarski('#skF_6'),'#skF_7') = D_243 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_1975])).

tff(c_332,plain,(
    ! [A_136,B_137,C_138,D_139] :
      ( v1_funct_1('#skF_2'(A_136,B_137,C_138,D_139))
      | r2_hidden('#skF_3'(A_136,B_137,C_138,D_139),D_139)
      | k5_partfun1(A_136,B_137,C_138) = D_139
      | ~ m1_subset_1(C_138,k1_zfmisc_1(k2_zfmisc_1(A_136,B_137)))
      | ~ v1_funct_1(C_138) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_334,plain,(
    ! [D_139] :
      ( v1_funct_1('#skF_2'('#skF_5',k1_tarski('#skF_6'),'#skF_7',D_139))
      | r2_hidden('#skF_3'('#skF_5',k1_tarski('#skF_6'),'#skF_7',D_139),D_139)
      | k5_partfun1('#skF_5',k1_tarski('#skF_6'),'#skF_7') = D_139
      | ~ v1_funct_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_72,c_332])).

tff(c_402,plain,(
    ! [D_146] :
      ( v1_funct_1('#skF_2'('#skF_5',k1_tarski('#skF_6'),'#skF_7',D_146))
      | r2_hidden('#skF_3'('#skF_5',k1_tarski('#skF_6'),'#skF_7',D_146),D_146)
      | k5_partfun1('#skF_5',k1_tarski('#skF_6'),'#skF_7') = D_146 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_334])).

tff(c_68,plain,(
    v1_funct_2('#skF_8','#skF_5',k1_tarski('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_142,plain,(
    ! [B_80,C_81,A_82] :
      ( k1_xboole_0 = B_80
      | v1_partfun1(C_81,A_82)
      | ~ v1_funct_2(C_81,A_82,B_80)
      | ~ m1_subset_1(C_81,k1_zfmisc_1(k2_zfmisc_1(A_82,B_80)))
      | ~ v1_funct_1(C_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_148,plain,
    ( k1_tarski('#skF_6') = k1_xboole_0
    | v1_partfun1('#skF_8','#skF_5')
    | ~ v1_funct_2('#skF_8','#skF_5',k1_tarski('#skF_6'))
    | ~ v1_funct_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_66,c_142])).

tff(c_160,plain,
    ( k1_tarski('#skF_6') = k1_xboole_0
    | v1_partfun1('#skF_8','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_148])).

tff(c_181,plain,(
    v1_partfun1('#skF_8','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_160])).

tff(c_162,plain,(
    ! [A_83,B_84,C_85] :
      ( k5_partfun1(A_83,B_84,C_85) = k1_tarski(C_85)
      | ~ v1_partfun1(C_85,A_83)
      | ~ m1_subset_1(C_85,k1_zfmisc_1(k2_zfmisc_1(A_83,B_84)))
      | ~ v1_funct_1(C_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_168,plain,
    ( k5_partfun1('#skF_5',k1_tarski('#skF_6'),'#skF_8') = k1_tarski('#skF_8')
    | ~ v1_partfun1('#skF_8','#skF_5')
    | ~ v1_funct_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_66,c_162])).

tff(c_180,plain,
    ( k5_partfun1('#skF_5',k1_tarski('#skF_6'),'#skF_8') = k1_tarski('#skF_8')
    | ~ v1_partfun1('#skF_8','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_168])).

tff(c_184,plain,(
    k5_partfun1('#skF_5',k1_tarski('#skF_6'),'#skF_8') = k1_tarski('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_181,c_180])).

tff(c_260,plain,(
    ! [E_99,A_100,B_101,C_102] :
      ( '#skF_4'(E_99,k5_partfun1(A_100,B_101,C_102),A_100,B_101,C_102) = E_99
      | ~ r2_hidden(E_99,k5_partfun1(A_100,B_101,C_102))
      | ~ m1_subset_1(C_102,k1_zfmisc_1(k2_zfmisc_1(A_100,B_101)))
      | ~ v1_funct_1(C_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_262,plain,(
    ! [E_99] :
      ( '#skF_4'(E_99,k5_partfun1('#skF_5',k1_tarski('#skF_6'),'#skF_8'),'#skF_5',k1_tarski('#skF_6'),'#skF_8') = E_99
      | ~ r2_hidden(E_99,k1_tarski('#skF_8'))
      | ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_5',k1_tarski('#skF_6'))))
      | ~ v1_funct_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_184,c_260])).

tff(c_264,plain,(
    ! [E_99] :
      ( '#skF_4'(E_99,k1_tarski('#skF_8'),'#skF_5',k1_tarski('#skF_6'),'#skF_8') = E_99
      | ~ r2_hidden(E_99,k1_tarski('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_66,c_184,c_262])).

tff(c_275,plain,(
    ! [E_106,A_107,B_108,C_109] :
      ( v1_funct_1('#skF_4'(E_106,k5_partfun1(A_107,B_108,C_109),A_107,B_108,C_109))
      | ~ r2_hidden(E_106,k5_partfun1(A_107,B_108,C_109))
      | ~ m1_subset_1(C_109,k1_zfmisc_1(k2_zfmisc_1(A_107,B_108)))
      | ~ v1_funct_1(C_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_279,plain,(
    ! [E_106] :
      ( v1_funct_1('#skF_4'(E_106,k5_partfun1('#skF_5',k1_tarski('#skF_6'),'#skF_8'),'#skF_5',k1_tarski('#skF_6'),'#skF_8'))
      | ~ r2_hidden(E_106,k5_partfun1('#skF_5',k1_tarski('#skF_6'),'#skF_8'))
      | ~ v1_funct_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_66,c_275])).

tff(c_290,plain,(
    ! [E_110] :
      ( v1_funct_1('#skF_4'(E_110,k1_tarski('#skF_8'),'#skF_5',k1_tarski('#skF_6'),'#skF_8'))
      | ~ r2_hidden(E_110,k1_tarski('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_184,c_184,c_279])).

tff(c_293,plain,(
    ! [E_99] :
      ( v1_funct_1(E_99)
      | ~ r2_hidden(E_99,k1_tarski('#skF_8'))
      | ~ r2_hidden(E_99,k1_tarski('#skF_8')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_264,c_290])).

tff(c_411,plain,
    ( v1_funct_1('#skF_3'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')))
    | ~ r2_hidden('#skF_3'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')),k1_tarski('#skF_8'))
    | v1_funct_1('#skF_2'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')))
    | k5_partfun1('#skF_5',k1_tarski('#skF_6'),'#skF_7') = k1_tarski('#skF_8') ),
    inference(resolution,[status(thm)],[c_402,c_293])).

tff(c_423,plain,
    ( v1_funct_1('#skF_3'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')))
    | ~ r2_hidden('#skF_3'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')),k1_tarski('#skF_8'))
    | v1_funct_1('#skF_2'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8'))) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_411])).

tff(c_425,plain,(
    ~ r2_hidden('#skF_3'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')),k1_tarski('#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_423])).

tff(c_2139,plain,
    ( '#skF_2'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')) = '#skF_1'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8'))
    | k5_partfun1('#skF_5',k1_tarski('#skF_6'),'#skF_7') = k1_tarski('#skF_8') ),
    inference(resolution,[status(thm)],[c_2113,c_425])).

tff(c_2172,plain,(
    '#skF_2'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')) = '#skF_1'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_2139])).

tff(c_343,plain,(
    ! [D_139] :
      ( v1_funct_1('#skF_2'('#skF_5',k1_tarski('#skF_6'),'#skF_7',D_139))
      | r2_hidden('#skF_3'('#skF_5',k1_tarski('#skF_6'),'#skF_7',D_139),D_139)
      | k5_partfun1('#skF_5',k1_tarski('#skF_6'),'#skF_7') = D_139 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_334])).

tff(c_428,plain,
    ( v1_funct_1('#skF_2'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')))
    | k5_partfun1('#skF_5',k1_tarski('#skF_6'),'#skF_7') = k1_tarski('#skF_8') ),
    inference(resolution,[status(thm)],[c_343,c_425])).

tff(c_431,plain,(
    v1_funct_1('#skF_2'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8'))) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_428])).

tff(c_2183,plain,(
    v1_funct_1('#skF_1'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2172,c_431])).

tff(c_48,plain,(
    ! [A_8,B_9,C_10,D_32] :
      ( m1_subset_1('#skF_2'(A_8,B_9,C_10,D_32),k1_zfmisc_1(k2_zfmisc_1(A_8,B_9)))
      | r2_hidden('#skF_3'(A_8,B_9,C_10,D_32),D_32)
      | k5_partfun1(A_8,B_9,C_10) = D_32
      | ~ m1_subset_1(C_10,k1_zfmisc_1(k2_zfmisc_1(A_8,B_9)))
      | ~ v1_funct_1(C_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_2187,plain,
    ( m1_subset_1('#skF_1'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')),k1_zfmisc_1(k2_zfmisc_1('#skF_5',k1_tarski('#skF_6'))))
    | r2_hidden('#skF_3'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')),k1_tarski('#skF_8'))
    | k5_partfun1('#skF_5',k1_tarski('#skF_6'),'#skF_7') = k1_tarski('#skF_8')
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5',k1_tarski('#skF_6'))))
    | ~ v1_funct_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_2172,c_48])).

tff(c_2192,plain,
    ( m1_subset_1('#skF_1'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')),k1_zfmisc_1(k2_zfmisc_1('#skF_5',k1_tarski('#skF_6'))))
    | r2_hidden('#skF_3'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')),k1_tarski('#skF_8'))
    | k5_partfun1('#skF_5',k1_tarski('#skF_6'),'#skF_7') = k1_tarski('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_2187])).

tff(c_2193,plain,(
    m1_subset_1('#skF_1'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')),k1_zfmisc_1(k2_zfmisc_1('#skF_5',k1_tarski('#skF_6')))) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_425,c_2192])).

tff(c_56,plain,(
    ! [C_55,D_57,A_53,B_54] :
      ( r1_partfun1(C_55,D_57)
      | ~ m1_subset_1(D_57,k1_zfmisc_1(k2_zfmisc_1(A_53,k1_tarski(B_54))))
      | ~ v1_funct_1(D_57)
      | ~ m1_subset_1(C_55,k1_zfmisc_1(k2_zfmisc_1(A_53,k1_tarski(B_54))))
      | ~ v1_funct_1(C_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_2232,plain,(
    ! [C_55] :
      ( r1_partfun1(C_55,'#skF_1'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')))
      | ~ v1_funct_1('#skF_1'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')))
      | ~ m1_subset_1(C_55,k1_zfmisc_1(k2_zfmisc_1('#skF_5',k1_tarski('#skF_6'))))
      | ~ v1_funct_1(C_55) ) ),
    inference(resolution,[status(thm)],[c_2193,c_56])).

tff(c_2277,plain,(
    ! [C_55] :
      ( r1_partfun1(C_55,'#skF_1'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')))
      | ~ m1_subset_1(C_55,k1_zfmisc_1(k2_zfmisc_1('#skF_5',k1_tarski('#skF_6'))))
      | ~ v1_funct_1(C_55) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2183,c_2232])).

tff(c_475,plain,(
    ! [A_151,B_152,C_153,D_154] :
      ( ~ r2_hidden('#skF_1'(A_151,B_152,C_153,D_154),D_154)
      | r2_hidden('#skF_3'(A_151,B_152,C_153,D_154),D_154)
      | k5_partfun1(A_151,B_152,C_153) = D_154
      | ~ m1_subset_1(C_153,k1_zfmisc_1(k2_zfmisc_1(A_151,B_152)))
      | ~ v1_funct_1(C_153) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_477,plain,(
    ! [D_154] :
      ( ~ r2_hidden('#skF_1'('#skF_5',k1_tarski('#skF_6'),'#skF_7',D_154),D_154)
      | r2_hidden('#skF_3'('#skF_5',k1_tarski('#skF_6'),'#skF_7',D_154),D_154)
      | k5_partfun1('#skF_5',k1_tarski('#skF_6'),'#skF_7') = D_154
      | ~ v1_funct_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_72,c_475])).

tff(c_510,plain,(
    ! [D_156] :
      ( ~ r2_hidden('#skF_1'('#skF_5',k1_tarski('#skF_6'),'#skF_7',D_156),D_156)
      | r2_hidden('#skF_3'('#skF_5',k1_tarski('#skF_6'),'#skF_7',D_156),D_156)
      | k5_partfun1('#skF_5',k1_tarski('#skF_6'),'#skF_7') = D_156 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_477])).

tff(c_513,plain,
    ( ~ r2_hidden('#skF_1'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')),k1_tarski('#skF_8'))
    | k5_partfun1('#skF_5',k1_tarski('#skF_6'),'#skF_7') = k1_tarski('#skF_8') ),
    inference(resolution,[status(thm)],[c_510,c_425])).

tff(c_528,plain,(
    ~ r2_hidden('#skF_1'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')),k1_tarski('#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_513])).

tff(c_681,plain,(
    ! [A_178,B_179,C_180,D_181] :
      ( v1_partfun1('#skF_2'(A_178,B_179,C_180,D_181),A_178)
      | r2_hidden('#skF_3'(A_178,B_179,C_180,D_181),D_181)
      | k5_partfun1(A_178,B_179,C_180) = D_181
      | ~ m1_subset_1(C_180,k1_zfmisc_1(k2_zfmisc_1(A_178,B_179)))
      | ~ v1_funct_1(C_180) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_683,plain,(
    ! [D_181] :
      ( v1_partfun1('#skF_2'('#skF_5',k1_tarski('#skF_6'),'#skF_7',D_181),'#skF_5')
      | r2_hidden('#skF_3'('#skF_5',k1_tarski('#skF_6'),'#skF_7',D_181),D_181)
      | k5_partfun1('#skF_5',k1_tarski('#skF_6'),'#skF_7') = D_181
      | ~ v1_funct_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_72,c_681])).

tff(c_719,plain,(
    ! [D_183] :
      ( v1_partfun1('#skF_2'('#skF_5',k1_tarski('#skF_6'),'#skF_7',D_183),'#skF_5')
      | r2_hidden('#skF_3'('#skF_5',k1_tarski('#skF_6'),'#skF_7',D_183),D_183)
      | k5_partfun1('#skF_5',k1_tarski('#skF_6'),'#skF_7') = D_183 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_683])).

tff(c_724,plain,
    ( v1_partfun1('#skF_2'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')),'#skF_5')
    | k5_partfun1('#skF_5',k1_tarski('#skF_6'),'#skF_7') = k1_tarski('#skF_8') ),
    inference(resolution,[status(thm)],[c_719,c_425])).

tff(c_740,plain,(
    v1_partfun1('#skF_2'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_724])).

tff(c_2181,plain,(
    v1_partfun1('#skF_1'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2172,c_740])).

tff(c_16,plain,(
    ! [F_49,A_8,B_9,C_10] :
      ( r2_hidden(F_49,k5_partfun1(A_8,B_9,C_10))
      | ~ r1_partfun1(C_10,F_49)
      | ~ v1_partfun1(F_49,A_8)
      | ~ m1_subset_1(F_49,k1_zfmisc_1(k2_zfmisc_1(A_8,B_9)))
      | ~ v1_funct_1(F_49)
      | ~ m1_subset_1(C_10,k1_zfmisc_1(k2_zfmisc_1(A_8,B_9)))
      | ~ v1_funct_1(C_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_2212,plain,(
    ! [C_10] :
      ( r2_hidden('#skF_1'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')),k5_partfun1('#skF_5',k1_tarski('#skF_6'),C_10))
      | ~ r1_partfun1(C_10,'#skF_1'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')))
      | ~ v1_partfun1('#skF_1'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')),'#skF_5')
      | ~ v1_funct_1('#skF_1'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')))
      | ~ m1_subset_1(C_10,k1_zfmisc_1(k2_zfmisc_1('#skF_5',k1_tarski('#skF_6'))))
      | ~ v1_funct_1(C_10) ) ),
    inference(resolution,[status(thm)],[c_2193,c_16])).

tff(c_3347,plain,(
    ! [C_333] :
      ( r2_hidden('#skF_1'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')),k5_partfun1('#skF_5',k1_tarski('#skF_6'),C_333))
      | ~ r1_partfun1(C_333,'#skF_1'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')))
      | ~ m1_subset_1(C_333,k1_zfmisc_1(k2_zfmisc_1('#skF_5',k1_tarski('#skF_6'))))
      | ~ v1_funct_1(C_333) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2183,c_2181,c_2212])).

tff(c_3355,plain,
    ( r2_hidden('#skF_1'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')),k1_tarski('#skF_8'))
    | ~ r1_partfun1('#skF_8','#skF_1'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')))
    | ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_5',k1_tarski('#skF_6'))))
    | ~ v1_funct_1('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_184,c_3347])).

tff(c_3360,plain,
    ( r2_hidden('#skF_1'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')),k1_tarski('#skF_8'))
    | ~ r1_partfun1('#skF_8','#skF_1'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_66,c_3355])).

tff(c_3361,plain,(
    ~ r1_partfun1('#skF_8','#skF_1'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8'))) ),
    inference(negUnitSimplification,[status(thm)],[c_528,c_3360])).

tff(c_3364,plain,
    ( ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_5',k1_tarski('#skF_6'))))
    | ~ v1_funct_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_2277,c_3361])).

tff(c_3368,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_66,c_3364])).

tff(c_3370,plain,(
    r2_hidden('#skF_3'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')),k1_tarski('#skF_8')) ),
    inference(splitRight,[status(thm)],[c_423])).

tff(c_3710,plain,(
    ! [E_371,A_372,B_373,C_374] :
      ( m1_subset_1('#skF_4'(E_371,k5_partfun1(A_372,B_373,C_374),A_372,B_373,C_374),k1_zfmisc_1(k2_zfmisc_1(A_372,B_373)))
      | ~ r2_hidden(E_371,k5_partfun1(A_372,B_373,C_374))
      | ~ m1_subset_1(C_374,k1_zfmisc_1(k2_zfmisc_1(A_372,B_373)))
      | ~ v1_funct_1(C_374) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_3743,plain,(
    ! [E_371] :
      ( m1_subset_1('#skF_4'(E_371,k1_tarski('#skF_8'),'#skF_5',k1_tarski('#skF_6'),'#skF_8'),k1_zfmisc_1(k2_zfmisc_1('#skF_5',k1_tarski('#skF_6'))))
      | ~ r2_hidden(E_371,k5_partfun1('#skF_5',k1_tarski('#skF_6'),'#skF_8'))
      | ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_5',k1_tarski('#skF_6'))))
      | ~ v1_funct_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_184,c_3710])).

tff(c_3765,plain,(
    ! [E_375] :
      ( m1_subset_1('#skF_4'(E_375,k1_tarski('#skF_8'),'#skF_5',k1_tarski('#skF_6'),'#skF_8'),k1_zfmisc_1(k2_zfmisc_1('#skF_5',k1_tarski('#skF_6'))))
      | ~ r2_hidden(E_375,k1_tarski('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_66,c_184,c_3743])).

tff(c_3795,plain,(
    ! [E_99] :
      ( m1_subset_1(E_99,k1_zfmisc_1(k2_zfmisc_1('#skF_5',k1_tarski('#skF_6'))))
      | ~ r2_hidden(E_99,k1_tarski('#skF_8'))
      | ~ r2_hidden(E_99,k1_tarski('#skF_8')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_264,c_3765])).

tff(c_3376,plain,
    ( v1_funct_1('#skF_3'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')))
    | ~ r2_hidden('#skF_3'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')),k1_tarski('#skF_8')) ),
    inference(resolution,[status(thm)],[c_3370,c_293])).

tff(c_3385,plain,(
    v1_funct_1('#skF_3'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3370,c_3376])).

tff(c_298,plain,(
    ! [E_117,A_118,B_119,C_120] :
      ( v1_partfun1('#skF_4'(E_117,k5_partfun1(A_118,B_119,C_120),A_118,B_119,C_120),A_118)
      | ~ r2_hidden(E_117,k5_partfun1(A_118,B_119,C_120))
      | ~ m1_subset_1(C_120,k1_zfmisc_1(k2_zfmisc_1(A_118,B_119)))
      | ~ v1_funct_1(C_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_303,plain,(
    ! [E_117] :
      ( v1_partfun1('#skF_4'(E_117,k1_tarski('#skF_8'),'#skF_5',k1_tarski('#skF_6'),'#skF_8'),'#skF_5')
      | ~ r2_hidden(E_117,k5_partfun1('#skF_5',k1_tarski('#skF_6'),'#skF_8'))
      | ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_5',k1_tarski('#skF_6'))))
      | ~ v1_funct_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_184,c_298])).

tff(c_307,plain,(
    ! [E_121] :
      ( v1_partfun1('#skF_4'(E_121,k1_tarski('#skF_8'),'#skF_5',k1_tarski('#skF_6'),'#skF_8'),'#skF_5')
      | ~ r2_hidden(E_121,k1_tarski('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_66,c_184,c_303])).

tff(c_312,plain,(
    ! [E_99] :
      ( v1_partfun1(E_99,'#skF_5')
      | ~ r2_hidden(E_99,k1_tarski('#skF_8'))
      | ~ r2_hidden(E_99,k1_tarski('#skF_8')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_264,c_307])).

tff(c_3374,plain,
    ( v1_partfun1('#skF_3'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')),'#skF_5')
    | ~ r2_hidden('#skF_3'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')),k1_tarski('#skF_8')) ),
    inference(resolution,[status(thm)],[c_3370,c_312])).

tff(c_3382,plain,(
    v1_partfun1('#skF_3'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3370,c_3374])).

tff(c_3807,plain,(
    ! [E_376] :
      ( m1_subset_1(E_376,k1_zfmisc_1(k2_zfmisc_1('#skF_5',k1_tarski('#skF_6'))))
      | ~ r2_hidden(E_376,k1_tarski('#skF_8'))
      | ~ r2_hidden(E_376,k1_tarski('#skF_8')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_264,c_3765])).

tff(c_4169,plain,(
    ! [C_384,E_385] :
      ( r1_partfun1(C_384,E_385)
      | ~ v1_funct_1(E_385)
      | ~ m1_subset_1(C_384,k1_zfmisc_1(k2_zfmisc_1('#skF_5',k1_tarski('#skF_6'))))
      | ~ v1_funct_1(C_384)
      | ~ r2_hidden(E_385,k1_tarski('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_3807,c_56])).

tff(c_4178,plain,(
    ! [E_385] :
      ( r1_partfun1('#skF_7',E_385)
      | ~ v1_funct_1(E_385)
      | ~ v1_funct_1('#skF_7')
      | ~ r2_hidden(E_385,k1_tarski('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_72,c_4169])).

tff(c_4190,plain,(
    ! [E_386] :
      ( r1_partfun1('#skF_7',E_386)
      | ~ v1_funct_1(E_386)
      | ~ r2_hidden(E_386,k1_tarski('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_4178])).

tff(c_4237,plain,
    ( r1_partfun1('#skF_7','#skF_3'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')))
    | ~ v1_funct_1('#skF_3'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8'))) ),
    inference(resolution,[status(thm)],[c_3370,c_4190])).

tff(c_4274,plain,(
    r1_partfun1('#skF_7','#skF_3'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3385,c_4237])).

tff(c_5415,plain,(
    ! [A_447,B_448,C_449,D_450] :
      ( v1_partfun1('#skF_2'(A_447,B_448,C_449,D_450),A_447)
      | ~ r1_partfun1(C_449,'#skF_3'(A_447,B_448,C_449,D_450))
      | ~ v1_partfun1('#skF_3'(A_447,B_448,C_449,D_450),A_447)
      | ~ m1_subset_1('#skF_3'(A_447,B_448,C_449,D_450),k1_zfmisc_1(k2_zfmisc_1(A_447,B_448)))
      | ~ v1_funct_1('#skF_3'(A_447,B_448,C_449,D_450))
      | k5_partfun1(A_447,B_448,C_449) = D_450
      | ~ m1_subset_1(C_449,k1_zfmisc_1(k2_zfmisc_1(A_447,B_448)))
      | ~ v1_funct_1(C_449) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_5420,plain,
    ( v1_partfun1('#skF_2'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')),'#skF_5')
    | ~ v1_partfun1('#skF_3'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')),'#skF_5')
    | ~ m1_subset_1('#skF_3'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')),k1_zfmisc_1(k2_zfmisc_1('#skF_5',k1_tarski('#skF_6'))))
    | ~ v1_funct_1('#skF_3'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')))
    | k5_partfun1('#skF_5',k1_tarski('#skF_6'),'#skF_7') = k1_tarski('#skF_8')
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5',k1_tarski('#skF_6'))))
    | ~ v1_funct_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_4274,c_5415])).

tff(c_5427,plain,
    ( v1_partfun1('#skF_2'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')),'#skF_5')
    | ~ m1_subset_1('#skF_3'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')),k1_zfmisc_1(k2_zfmisc_1('#skF_5',k1_tarski('#skF_6'))))
    | k5_partfun1('#skF_5',k1_tarski('#skF_6'),'#skF_7') = k1_tarski('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_3385,c_3382,c_5420])).

tff(c_5428,plain,
    ( v1_partfun1('#skF_2'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')),'#skF_5')
    | ~ m1_subset_1('#skF_3'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')),k1_zfmisc_1(k2_zfmisc_1('#skF_5',k1_tarski('#skF_6')))) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_5427])).

tff(c_5429,plain,(
    ~ m1_subset_1('#skF_3'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')),k1_zfmisc_1(k2_zfmisc_1('#skF_5',k1_tarski('#skF_6')))) ),
    inference(splitLeft,[status(thm)],[c_5428])).

tff(c_5432,plain,(
    ~ r2_hidden('#skF_3'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')),k1_tarski('#skF_8')) ),
    inference(resolution,[status(thm)],[c_3795,c_5429])).

tff(c_5436,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3370,c_5432])).

tff(c_5438,plain,(
    m1_subset_1('#skF_3'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')),k1_zfmisc_1(k2_zfmisc_1('#skF_5',k1_tarski('#skF_6')))) ),
    inference(splitRight,[status(thm)],[c_5428])).

tff(c_7337,plain,(
    ! [A_556,B_557,C_558,D_559] :
      ( '#skF_2'(A_556,B_557,C_558,D_559) = '#skF_1'(A_556,B_557,C_558,D_559)
      | ~ r1_partfun1(C_558,'#skF_3'(A_556,B_557,C_558,D_559))
      | ~ v1_partfun1('#skF_3'(A_556,B_557,C_558,D_559),A_556)
      | ~ m1_subset_1('#skF_3'(A_556,B_557,C_558,D_559),k1_zfmisc_1(k2_zfmisc_1(A_556,B_557)))
      | ~ v1_funct_1('#skF_3'(A_556,B_557,C_558,D_559))
      | k5_partfun1(A_556,B_557,C_558) = D_559
      | ~ m1_subset_1(C_558,k1_zfmisc_1(k2_zfmisc_1(A_556,B_557)))
      | ~ v1_funct_1(C_558) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_7351,plain,
    ( '#skF_2'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')) = '#skF_1'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8'))
    | ~ v1_partfun1('#skF_3'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')),'#skF_5')
    | ~ m1_subset_1('#skF_3'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')),k1_zfmisc_1(k2_zfmisc_1('#skF_5',k1_tarski('#skF_6'))))
    | ~ v1_funct_1('#skF_3'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')))
    | k5_partfun1('#skF_5',k1_tarski('#skF_6'),'#skF_7') = k1_tarski('#skF_8')
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5',k1_tarski('#skF_6'))))
    | ~ v1_funct_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_4274,c_7337])).

tff(c_7368,plain,
    ( '#skF_2'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')) = '#skF_1'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8'))
    | k5_partfun1('#skF_5',k1_tarski('#skF_6'),'#skF_7') = k1_tarski('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_3385,c_5438,c_3382,c_7351])).

tff(c_7369,plain,(
    '#skF_2'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')) = '#skF_1'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_7368])).

tff(c_5993,plain,(
    ! [A_481,B_482,C_483,D_484] :
      ( '#skF_2'(A_481,B_482,C_483,D_484) = '#skF_1'(A_481,B_482,C_483,D_484)
      | ~ r1_partfun1(C_483,'#skF_3'(A_481,B_482,C_483,D_484))
      | ~ v1_partfun1('#skF_3'(A_481,B_482,C_483,D_484),A_481)
      | ~ m1_subset_1('#skF_3'(A_481,B_482,C_483,D_484),k1_zfmisc_1(k2_zfmisc_1(A_481,B_482)))
      | ~ v1_funct_1('#skF_3'(A_481,B_482,C_483,D_484))
      | k5_partfun1(A_481,B_482,C_483) = D_484
      | ~ m1_subset_1(C_483,k1_zfmisc_1(k2_zfmisc_1(A_481,B_482)))
      | ~ v1_funct_1(C_483) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_6007,plain,
    ( '#skF_2'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')) = '#skF_1'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8'))
    | ~ v1_partfun1('#skF_3'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')),'#skF_5')
    | ~ m1_subset_1('#skF_3'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')),k1_zfmisc_1(k2_zfmisc_1('#skF_5',k1_tarski('#skF_6'))))
    | ~ v1_funct_1('#skF_3'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')))
    | k5_partfun1('#skF_5',k1_tarski('#skF_6'),'#skF_7') = k1_tarski('#skF_8')
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5',k1_tarski('#skF_6'))))
    | ~ v1_funct_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_4274,c_5993])).

tff(c_6024,plain,
    ( '#skF_2'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')) = '#skF_1'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8'))
    | k5_partfun1('#skF_5',k1_tarski('#skF_6'),'#skF_7') = k1_tarski('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_3385,c_5438,c_3382,c_6007])).

tff(c_6025,plain,(
    '#skF_2'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')) = '#skF_1'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_6024])).

tff(c_219,plain,(
    ! [C_93,D_94,A_95,B_96] :
      ( r1_partfun1(C_93,D_94)
      | ~ m1_subset_1(D_94,k1_zfmisc_1(k2_zfmisc_1(A_95,k1_tarski(B_96))))
      | ~ v1_funct_1(D_94)
      | ~ m1_subset_1(C_93,k1_zfmisc_1(k2_zfmisc_1(A_95,k1_tarski(B_96))))
      | ~ v1_funct_1(C_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_223,plain,(
    ! [C_93] :
      ( r1_partfun1(C_93,'#skF_8')
      | ~ v1_funct_1('#skF_8')
      | ~ m1_subset_1(C_93,k1_zfmisc_1(k2_zfmisc_1('#skF_5',k1_tarski('#skF_6'))))
      | ~ v1_funct_1(C_93) ) ),
    inference(resolution,[status(thm)],[c_66,c_219])).

tff(c_232,plain,(
    ! [C_93] :
      ( r1_partfun1(C_93,'#skF_8')
      | ~ m1_subset_1(C_93,k1_zfmisc_1(k2_zfmisc_1('#skF_5',k1_tarski('#skF_6'))))
      | ~ v1_funct_1(C_93) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_223])).

tff(c_3853,plain,(
    ! [E_377] :
      ( r1_partfun1(E_377,'#skF_8')
      | ~ v1_funct_1(E_377)
      | ~ r2_hidden(E_377,k1_tarski('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_3807,c_232])).

tff(c_3904,plain,
    ( r1_partfun1('#skF_3'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')),'#skF_8')
    | ~ v1_funct_1('#skF_3'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')))
    | v1_funct_1('#skF_2'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')))
    | k5_partfun1('#skF_5',k1_tarski('#skF_6'),'#skF_7') = k1_tarski('#skF_8') ),
    inference(resolution,[status(thm)],[c_343,c_3853])).

tff(c_3940,plain,
    ( r1_partfun1('#skF_3'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')),'#skF_8')
    | v1_funct_1('#skF_2'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')))
    | k5_partfun1('#skF_5',k1_tarski('#skF_6'),'#skF_7') = k1_tarski('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3385,c_3904])).

tff(c_3941,plain,
    ( r1_partfun1('#skF_3'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')),'#skF_8')
    | v1_funct_1('#skF_2'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8'))) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_3940])).

tff(c_3946,plain,(
    v1_funct_1('#skF_2'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8'))) ),
    inference(splitLeft,[status(thm)],[c_3941])).

tff(c_6035,plain,(
    v1_funct_1('#skF_1'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6025,c_3946])).

tff(c_5799,plain,(
    ! [A_475,B_476,C_477,D_478] :
      ( m1_subset_1('#skF_2'(A_475,B_476,C_477,D_478),k1_zfmisc_1(k2_zfmisc_1(A_475,B_476)))
      | ~ r1_partfun1(C_477,'#skF_3'(A_475,B_476,C_477,D_478))
      | ~ v1_partfun1('#skF_3'(A_475,B_476,C_477,D_478),A_475)
      | ~ m1_subset_1('#skF_3'(A_475,B_476,C_477,D_478),k1_zfmisc_1(k2_zfmisc_1(A_475,B_476)))
      | ~ v1_funct_1('#skF_3'(A_475,B_476,C_477,D_478))
      | k5_partfun1(A_475,B_476,C_477) = D_478
      | ~ m1_subset_1(C_477,k1_zfmisc_1(k2_zfmisc_1(A_475,B_476)))
      | ~ v1_funct_1(C_477) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_5810,plain,
    ( m1_subset_1('#skF_2'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')),k1_zfmisc_1(k2_zfmisc_1('#skF_5',k1_tarski('#skF_6'))))
    | ~ v1_partfun1('#skF_3'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')),'#skF_5')
    | ~ m1_subset_1('#skF_3'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')),k1_zfmisc_1(k2_zfmisc_1('#skF_5',k1_tarski('#skF_6'))))
    | ~ v1_funct_1('#skF_3'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')))
    | k5_partfun1('#skF_5',k1_tarski('#skF_6'),'#skF_7') = k1_tarski('#skF_8')
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5',k1_tarski('#skF_6'))))
    | ~ v1_funct_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_4274,c_5799])).

tff(c_5824,plain,
    ( m1_subset_1('#skF_2'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')),k1_zfmisc_1(k2_zfmisc_1('#skF_5',k1_tarski('#skF_6'))))
    | k5_partfun1('#skF_5',k1_tarski('#skF_6'),'#skF_7') = k1_tarski('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_3385,c_5438,c_3382,c_5810])).

tff(c_5825,plain,(
    m1_subset_1('#skF_2'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')),k1_zfmisc_1(k2_zfmisc_1('#skF_5',k1_tarski('#skF_6')))) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_5824])).

tff(c_6032,plain,(
    m1_subset_1('#skF_1'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')),k1_zfmisc_1(k2_zfmisc_1('#skF_5',k1_tarski('#skF_6')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6025,c_5825])).

tff(c_6097,plain,(
    ! [C_55] :
      ( r1_partfun1(C_55,'#skF_1'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')))
      | ~ v1_funct_1('#skF_1'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')))
      | ~ m1_subset_1(C_55,k1_zfmisc_1(k2_zfmisc_1('#skF_5',k1_tarski('#skF_6'))))
      | ~ v1_funct_1(C_55) ) ),
    inference(resolution,[status(thm)],[c_6032,c_56])).

tff(c_6145,plain,(
    ! [C_55] :
      ( r1_partfun1(C_55,'#skF_1'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')))
      | ~ m1_subset_1(C_55,k1_zfmisc_1(k2_zfmisc_1('#skF_5',k1_tarski('#skF_6'))))
      | ~ v1_funct_1(C_55) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6035,c_6097])).

tff(c_5849,plain,
    ( r1_partfun1('#skF_2'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')),'#skF_8')
    | ~ v1_funct_1('#skF_2'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8'))) ),
    inference(resolution,[status(thm)],[c_5825,c_232])).

tff(c_5896,plain,(
    r1_partfun1('#skF_2'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3946,c_5849])).

tff(c_5437,plain,(
    v1_partfun1('#skF_2'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_5428])).

tff(c_62,plain,(
    ! [A_63,B_64,C_65] :
      ( k5_partfun1(A_63,B_64,C_65) = k1_tarski(C_65)
      | ~ v1_partfun1(C_65,A_63)
      | ~ m1_subset_1(C_65,k1_zfmisc_1(k2_zfmisc_1(A_63,B_64)))
      | ~ v1_funct_1(C_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_5860,plain,
    ( k5_partfun1('#skF_5',k1_tarski('#skF_6'),'#skF_2'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8'))) = k1_tarski('#skF_2'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')))
    | ~ v1_partfun1('#skF_2'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')),'#skF_5')
    | ~ v1_funct_1('#skF_2'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8'))) ),
    inference(resolution,[status(thm)],[c_5825,c_62])).

tff(c_5908,plain,(
    k5_partfun1('#skF_5',k1_tarski('#skF_6'),'#skF_2'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8'))) = k1_tarski('#skF_2'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3946,c_5437,c_5860])).

tff(c_4143,plain,(
    ! [F_380,A_381,B_382,C_383] :
      ( r2_hidden(F_380,k5_partfun1(A_381,B_382,C_383))
      | ~ r1_partfun1(C_383,F_380)
      | ~ v1_partfun1(F_380,A_381)
      | ~ m1_subset_1(F_380,k1_zfmisc_1(k2_zfmisc_1(A_381,B_382)))
      | ~ v1_funct_1(F_380)
      | ~ m1_subset_1(C_383,k1_zfmisc_1(k2_zfmisc_1(A_381,B_382)))
      | ~ v1_funct_1(C_383) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_4153,plain,(
    ! [C_383] :
      ( r2_hidden('#skF_8',k5_partfun1('#skF_5',k1_tarski('#skF_6'),C_383))
      | ~ r1_partfun1(C_383,'#skF_8')
      | ~ v1_partfun1('#skF_8','#skF_5')
      | ~ v1_funct_1('#skF_8')
      | ~ m1_subset_1(C_383,k1_zfmisc_1(k2_zfmisc_1('#skF_5',k1_tarski('#skF_6'))))
      | ~ v1_funct_1(C_383) ) ),
    inference(resolution,[status(thm)],[c_66,c_4143])).

tff(c_4496,plain,(
    ! [C_395] :
      ( r2_hidden('#skF_8',k5_partfun1('#skF_5',k1_tarski('#skF_6'),C_395))
      | ~ r1_partfun1(C_395,'#skF_8')
      | ~ m1_subset_1(C_395,k1_zfmisc_1(k2_zfmisc_1('#skF_5',k1_tarski('#skF_6'))))
      | ~ v1_funct_1(C_395) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_181,c_4153])).

tff(c_4513,plain,(
    ! [E_99] :
      ( r2_hidden('#skF_8',k5_partfun1('#skF_5',k1_tarski('#skF_6'),E_99))
      | ~ r1_partfun1(E_99,'#skF_8')
      | ~ v1_funct_1(E_99)
      | ~ r2_hidden(E_99,k1_tarski('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_3795,c_4496])).

tff(c_5963,plain,
    ( r2_hidden('#skF_8',k1_tarski('#skF_2'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8'))))
    | ~ r1_partfun1('#skF_2'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')),'#skF_8')
    | ~ v1_funct_1('#skF_2'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')))
    | ~ r2_hidden('#skF_2'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')),k1_tarski('#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_5908,c_4513])).

tff(c_5982,plain,
    ( r2_hidden('#skF_8',k1_tarski('#skF_2'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8'))))
    | ~ r2_hidden('#skF_2'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')),k1_tarski('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3946,c_5896,c_5963])).

tff(c_5992,plain,(
    ~ r2_hidden('#skF_2'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')),k1_tarski('#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_5982])).

tff(c_6026,plain,(
    ~ r2_hidden('#skF_1'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')),k1_tarski('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6025,c_5992])).

tff(c_5836,plain,(
    ! [C_10] :
      ( r2_hidden('#skF_2'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')),k5_partfun1('#skF_5',k1_tarski('#skF_6'),C_10))
      | ~ r1_partfun1(C_10,'#skF_2'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')))
      | ~ v1_partfun1('#skF_2'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')),'#skF_5')
      | ~ v1_funct_1('#skF_2'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')))
      | ~ m1_subset_1(C_10,k1_zfmisc_1(k2_zfmisc_1('#skF_5',k1_tarski('#skF_6'))))
      | ~ v1_funct_1(C_10) ) ),
    inference(resolution,[status(thm)],[c_5825,c_16])).

tff(c_5878,plain,(
    ! [C_10] :
      ( r2_hidden('#skF_2'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')),k5_partfun1('#skF_5',k1_tarski('#skF_6'),C_10))
      | ~ r1_partfun1(C_10,'#skF_2'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')))
      | ~ m1_subset_1(C_10,k1_zfmisc_1(k2_zfmisc_1('#skF_5',k1_tarski('#skF_6'))))
      | ~ v1_funct_1(C_10) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3946,c_5437,c_5836])).

tff(c_7254,plain,(
    ! [C_555] :
      ( r2_hidden('#skF_1'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')),k5_partfun1('#skF_5',k1_tarski('#skF_6'),C_555))
      | ~ r1_partfun1(C_555,'#skF_1'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')))
      | ~ m1_subset_1(C_555,k1_zfmisc_1(k2_zfmisc_1('#skF_5',k1_tarski('#skF_6'))))
      | ~ v1_funct_1(C_555) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6025,c_6025,c_5878])).

tff(c_7265,plain,
    ( r2_hidden('#skF_1'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')),k1_tarski('#skF_8'))
    | ~ r1_partfun1('#skF_8','#skF_1'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')))
    | ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_5',k1_tarski('#skF_6'))))
    | ~ v1_funct_1('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_184,c_7254])).

tff(c_7272,plain,
    ( r2_hidden('#skF_1'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')),k1_tarski('#skF_8'))
    | ~ r1_partfun1('#skF_8','#skF_1'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_66,c_7265])).

tff(c_7273,plain,(
    ~ r1_partfun1('#skF_8','#skF_1'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8'))) ),
    inference(negUnitSimplification,[status(thm)],[c_6026,c_7272])).

tff(c_7276,plain,
    ( ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_5',k1_tarski('#skF_6'))))
    | ~ v1_funct_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_6145,c_7273])).

tff(c_7280,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_66,c_7276])).

tff(c_7282,plain,(
    r2_hidden('#skF_2'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')),k1_tarski('#skF_8')) ),
    inference(splitRight,[status(thm)],[c_5982])).

tff(c_7371,plain,(
    r2_hidden('#skF_1'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')),k1_tarski('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7369,c_7282])).

tff(c_28,plain,(
    ! [A_8,B_9,C_10,D_32] :
      ( ~ r2_hidden('#skF_1'(A_8,B_9,C_10,D_32),D_32)
      | ~ r1_partfun1(C_10,'#skF_3'(A_8,B_9,C_10,D_32))
      | ~ v1_partfun1('#skF_3'(A_8,B_9,C_10,D_32),A_8)
      | ~ m1_subset_1('#skF_3'(A_8,B_9,C_10,D_32),k1_zfmisc_1(k2_zfmisc_1(A_8,B_9)))
      | ~ v1_funct_1('#skF_3'(A_8,B_9,C_10,D_32))
      | k5_partfun1(A_8,B_9,C_10) = D_32
      | ~ m1_subset_1(C_10,k1_zfmisc_1(k2_zfmisc_1(A_8,B_9)))
      | ~ v1_funct_1(C_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_7421,plain,
    ( ~ r1_partfun1('#skF_7','#skF_3'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')))
    | ~ v1_partfun1('#skF_3'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')),'#skF_5')
    | ~ m1_subset_1('#skF_3'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')),k1_zfmisc_1(k2_zfmisc_1('#skF_5',k1_tarski('#skF_6'))))
    | ~ v1_funct_1('#skF_3'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')))
    | k5_partfun1('#skF_5',k1_tarski('#skF_6'),'#skF_7') = k1_tarski('#skF_8')
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5',k1_tarski('#skF_6'))))
    | ~ v1_funct_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_7371,c_28])).

tff(c_7447,plain,(
    k5_partfun1('#skF_5',k1_tarski('#skF_6'),'#skF_7') = k1_tarski('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_3385,c_5438,c_3382,c_4274,c_7421])).

tff(c_7449,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_7447])).

tff(c_7451,plain,(
    ~ v1_funct_1('#skF_2'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8'))) ),
    inference(splitRight,[status(thm)],[c_3941])).

tff(c_7650,plain,(
    ! [C_565,E_566] :
      ( r1_partfun1(C_565,E_566)
      | ~ v1_funct_1(E_566)
      | ~ m1_subset_1(C_565,k1_zfmisc_1(k2_zfmisc_1('#skF_5',k1_tarski('#skF_6'))))
      | ~ v1_funct_1(C_565)
      | ~ r2_hidden(E_566,k1_tarski('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_3807,c_56])).

tff(c_7659,plain,(
    ! [E_566] :
      ( r1_partfun1('#skF_7',E_566)
      | ~ v1_funct_1(E_566)
      | ~ v1_funct_1('#skF_7')
      | ~ r2_hidden(E_566,k1_tarski('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_72,c_7650])).

tff(c_7697,plain,(
    ! [E_571] :
      ( r1_partfun1('#skF_7',E_571)
      | ~ v1_funct_1(E_571)
      | ~ r2_hidden(E_571,k1_tarski('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_7659])).

tff(c_7744,plain,
    ( r1_partfun1('#skF_7','#skF_3'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')))
    | ~ v1_funct_1('#skF_3'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8'))) ),
    inference(resolution,[status(thm)],[c_3370,c_7697])).

tff(c_7781,plain,(
    r1_partfun1('#skF_7','#skF_3'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3385,c_7744])).

tff(c_8304,plain,(
    ! [A_589,B_590,C_591,D_592] :
      ( v1_funct_1('#skF_2'(A_589,B_590,C_591,D_592))
      | ~ r1_partfun1(C_591,'#skF_3'(A_589,B_590,C_591,D_592))
      | ~ v1_partfun1('#skF_3'(A_589,B_590,C_591,D_592),A_589)
      | ~ m1_subset_1('#skF_3'(A_589,B_590,C_591,D_592),k1_zfmisc_1(k2_zfmisc_1(A_589,B_590)))
      | ~ v1_funct_1('#skF_3'(A_589,B_590,C_591,D_592))
      | k5_partfun1(A_589,B_590,C_591) = D_592
      | ~ m1_subset_1(C_591,k1_zfmisc_1(k2_zfmisc_1(A_589,B_590)))
      | ~ v1_funct_1(C_591) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_8309,plain,
    ( v1_funct_1('#skF_2'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')))
    | ~ v1_partfun1('#skF_3'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')),'#skF_5')
    | ~ m1_subset_1('#skF_3'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')),k1_zfmisc_1(k2_zfmisc_1('#skF_5',k1_tarski('#skF_6'))))
    | ~ v1_funct_1('#skF_3'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')))
    | k5_partfun1('#skF_5',k1_tarski('#skF_6'),'#skF_7') = k1_tarski('#skF_8')
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5',k1_tarski('#skF_6'))))
    | ~ v1_funct_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_7781,c_8304])).

tff(c_8316,plain,
    ( v1_funct_1('#skF_2'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')))
    | ~ m1_subset_1('#skF_3'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')),k1_zfmisc_1(k2_zfmisc_1('#skF_5',k1_tarski('#skF_6'))))
    | k5_partfun1('#skF_5',k1_tarski('#skF_6'),'#skF_7') = k1_tarski('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_3385,c_3382,c_8309])).

tff(c_8317,plain,(
    ~ m1_subset_1('#skF_3'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')),k1_zfmisc_1(k2_zfmisc_1('#skF_5',k1_tarski('#skF_6')))) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_7451,c_8316])).

tff(c_8421,plain,(
    ~ r2_hidden('#skF_3'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')),k1_tarski('#skF_8')) ),
    inference(resolution,[status(thm)],[c_3795,c_8317])).

tff(c_8425,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3370,c_8421])).

tff(c_8426,plain,(
    k1_tarski('#skF_6') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_160])).

tff(c_12,plain,(
    ! [A_6,B_7] :
      ( k2_zfmisc_1(A_6,k1_tarski(B_7)) != k1_xboole_0
      | k1_xboole_0 = A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_8436,plain,(
    ! [A_6] :
      ( k2_zfmisc_1(A_6,k1_xboole_0) != k1_xboole_0
      | k1_xboole_0 = A_6 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8426,c_12])).

tff(c_8442,plain,(
    ! [A_6] : k1_xboole_0 = A_6 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_8436])).

tff(c_8430,plain,(
    k5_partfun1('#skF_5',k1_xboole_0,'#skF_7') != k1_tarski('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8426,c_64])).

tff(c_8760,plain,(
    k1_tarski('#skF_8') != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_8442,c_8430])).

tff(c_8774,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_8442,c_8760])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 13:00:19 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.02/3.13  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.02/3.16  
% 9.02/3.16  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.02/3.16  %$ v1_funct_2 > v1_partfun1 > r2_hidden > r1_partfun1 > m1_subset_1 > v1_funct_1 > k5_partfun1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_4 > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_8 > #skF_3 > #skF_1
% 9.02/3.16  
% 9.02/3.16  %Foreground sorts:
% 9.02/3.16  
% 9.02/3.16  
% 9.02/3.16  %Background operators:
% 9.02/3.16  
% 9.02/3.16  
% 9.02/3.16  %Foreground operators:
% 9.02/3.16  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 9.02/3.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.02/3.16  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.02/3.16  tff(k1_tarski, type, k1_tarski: $i > $i).
% 9.02/3.16  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.02/3.16  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i * $i) > $i).
% 9.02/3.16  tff('#skF_7', type, '#skF_7': $i).
% 9.02/3.16  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 9.02/3.16  tff('#skF_5', type, '#skF_5': $i).
% 9.02/3.16  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 9.02/3.16  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 9.02/3.16  tff('#skF_6', type, '#skF_6': $i).
% 9.02/3.16  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 9.02/3.16  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 9.02/3.16  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.02/3.16  tff('#skF_8', type, '#skF_8': $i).
% 9.02/3.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.02/3.16  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 9.02/3.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.02/3.16  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 9.02/3.16  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 9.02/3.16  tff(k5_partfun1, type, k5_partfun1: ($i * $i * $i) > $i).
% 9.02/3.16  tff(r1_partfun1, type, r1_partfun1: ($i * $i) > $o).
% 9.02/3.16  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.02/3.16  
% 9.02/3.19  tff(f_35, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 9.02/3.19  tff(f_132, negated_conjecture, ~(![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (k5_partfun1(A, k1_tarski(B), C) = k1_tarski(D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t164_funct_2)).
% 9.02/3.19  tff(f_65, axiom, (![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: ((D = k5_partfun1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> (?[F]: ((((v1_funct_1(F) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & (F = E)) & v1_partfun1(F, A)) & r1_partfun1(C, F))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_partfun1)).
% 9.02/3.19  tff(f_82, axiom, (![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | v1_partfun1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t132_funct_2)).
% 9.02/3.19  tff(f_118, axiom, (![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (v1_partfun1(C, A) <=> (k5_partfun1(A, B, C) = k1_tarski(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t174_partfun1)).
% 9.02/3.19  tff(f_93, axiom, (![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (![D]: ((v1_funct_1(D) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => r1_partfun1(C, D))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_partfun1)).
% 9.02/3.19  tff(f_44, axiom, (![A, B]: (~(A = k1_xboole_0) => (~(k2_zfmisc_1(k1_tarski(B), A) = k1_xboole_0) & ~(k2_zfmisc_1(A, k1_tarski(B)) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t130_zfmisc_1)).
% 9.02/3.19  tff(c_8, plain, (![A_4]: (k2_zfmisc_1(A_4, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 9.02/3.19  tff(c_70, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_132])).
% 9.02/3.19  tff(c_66, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_5', k1_tarski('#skF_6'))))), inference(cnfTransformation, [status(thm)], [f_132])).
% 9.02/3.19  tff(c_64, plain, (k5_partfun1('#skF_5', k1_tarski('#skF_6'), '#skF_7')!=k1_tarski('#skF_8')), inference(cnfTransformation, [status(thm)], [f_132])).
% 9.02/3.19  tff(c_74, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_132])).
% 9.02/3.19  tff(c_72, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', k1_tarski('#skF_6'))))), inference(cnfTransformation, [status(thm)], [f_132])).
% 9.02/3.19  tff(c_1965, plain, (![A_233, B_234, C_235, D_236]: ('#skF_2'(A_233, B_234, C_235, D_236)='#skF_1'(A_233, B_234, C_235, D_236) | r2_hidden('#skF_3'(A_233, B_234, C_235, D_236), D_236) | k5_partfun1(A_233, B_234, C_235)=D_236 | ~m1_subset_1(C_235, k1_zfmisc_1(k2_zfmisc_1(A_233, B_234))) | ~v1_funct_1(C_235))), inference(cnfTransformation, [status(thm)], [f_65])).
% 9.02/3.19  tff(c_1975, plain, (![D_236]: ('#skF_2'('#skF_5', k1_tarski('#skF_6'), '#skF_7', D_236)='#skF_1'('#skF_5', k1_tarski('#skF_6'), '#skF_7', D_236) | r2_hidden('#skF_3'('#skF_5', k1_tarski('#skF_6'), '#skF_7', D_236), D_236) | k5_partfun1('#skF_5', k1_tarski('#skF_6'), '#skF_7')=D_236 | ~v1_funct_1('#skF_7'))), inference(resolution, [status(thm)], [c_72, c_1965])).
% 9.02/3.19  tff(c_2113, plain, (![D_243]: ('#skF_2'('#skF_5', k1_tarski('#skF_6'), '#skF_7', D_243)='#skF_1'('#skF_5', k1_tarski('#skF_6'), '#skF_7', D_243) | r2_hidden('#skF_3'('#skF_5', k1_tarski('#skF_6'), '#skF_7', D_243), D_243) | k5_partfun1('#skF_5', k1_tarski('#skF_6'), '#skF_7')=D_243)), inference(demodulation, [status(thm), theory('equality')], [c_74, c_1975])).
% 9.02/3.19  tff(c_332, plain, (![A_136, B_137, C_138, D_139]: (v1_funct_1('#skF_2'(A_136, B_137, C_138, D_139)) | r2_hidden('#skF_3'(A_136, B_137, C_138, D_139), D_139) | k5_partfun1(A_136, B_137, C_138)=D_139 | ~m1_subset_1(C_138, k1_zfmisc_1(k2_zfmisc_1(A_136, B_137))) | ~v1_funct_1(C_138))), inference(cnfTransformation, [status(thm)], [f_65])).
% 9.02/3.19  tff(c_334, plain, (![D_139]: (v1_funct_1('#skF_2'('#skF_5', k1_tarski('#skF_6'), '#skF_7', D_139)) | r2_hidden('#skF_3'('#skF_5', k1_tarski('#skF_6'), '#skF_7', D_139), D_139) | k5_partfun1('#skF_5', k1_tarski('#skF_6'), '#skF_7')=D_139 | ~v1_funct_1('#skF_7'))), inference(resolution, [status(thm)], [c_72, c_332])).
% 9.02/3.19  tff(c_402, plain, (![D_146]: (v1_funct_1('#skF_2'('#skF_5', k1_tarski('#skF_6'), '#skF_7', D_146)) | r2_hidden('#skF_3'('#skF_5', k1_tarski('#skF_6'), '#skF_7', D_146), D_146) | k5_partfun1('#skF_5', k1_tarski('#skF_6'), '#skF_7')=D_146)), inference(demodulation, [status(thm), theory('equality')], [c_74, c_334])).
% 9.02/3.19  tff(c_68, plain, (v1_funct_2('#skF_8', '#skF_5', k1_tarski('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_132])).
% 9.02/3.19  tff(c_142, plain, (![B_80, C_81, A_82]: (k1_xboole_0=B_80 | v1_partfun1(C_81, A_82) | ~v1_funct_2(C_81, A_82, B_80) | ~m1_subset_1(C_81, k1_zfmisc_1(k2_zfmisc_1(A_82, B_80))) | ~v1_funct_1(C_81))), inference(cnfTransformation, [status(thm)], [f_82])).
% 9.02/3.19  tff(c_148, plain, (k1_tarski('#skF_6')=k1_xboole_0 | v1_partfun1('#skF_8', '#skF_5') | ~v1_funct_2('#skF_8', '#skF_5', k1_tarski('#skF_6')) | ~v1_funct_1('#skF_8')), inference(resolution, [status(thm)], [c_66, c_142])).
% 9.02/3.19  tff(c_160, plain, (k1_tarski('#skF_6')=k1_xboole_0 | v1_partfun1('#skF_8', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_148])).
% 9.02/3.19  tff(c_181, plain, (v1_partfun1('#skF_8', '#skF_5')), inference(splitLeft, [status(thm)], [c_160])).
% 9.02/3.19  tff(c_162, plain, (![A_83, B_84, C_85]: (k5_partfun1(A_83, B_84, C_85)=k1_tarski(C_85) | ~v1_partfun1(C_85, A_83) | ~m1_subset_1(C_85, k1_zfmisc_1(k2_zfmisc_1(A_83, B_84))) | ~v1_funct_1(C_85))), inference(cnfTransformation, [status(thm)], [f_118])).
% 9.02/3.19  tff(c_168, plain, (k5_partfun1('#skF_5', k1_tarski('#skF_6'), '#skF_8')=k1_tarski('#skF_8') | ~v1_partfun1('#skF_8', '#skF_5') | ~v1_funct_1('#skF_8')), inference(resolution, [status(thm)], [c_66, c_162])).
% 9.02/3.19  tff(c_180, plain, (k5_partfun1('#skF_5', k1_tarski('#skF_6'), '#skF_8')=k1_tarski('#skF_8') | ~v1_partfun1('#skF_8', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_168])).
% 9.02/3.19  tff(c_184, plain, (k5_partfun1('#skF_5', k1_tarski('#skF_6'), '#skF_8')=k1_tarski('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_181, c_180])).
% 9.02/3.19  tff(c_260, plain, (![E_99, A_100, B_101, C_102]: ('#skF_4'(E_99, k5_partfun1(A_100, B_101, C_102), A_100, B_101, C_102)=E_99 | ~r2_hidden(E_99, k5_partfun1(A_100, B_101, C_102)) | ~m1_subset_1(C_102, k1_zfmisc_1(k2_zfmisc_1(A_100, B_101))) | ~v1_funct_1(C_102))), inference(cnfTransformation, [status(thm)], [f_65])).
% 9.02/3.19  tff(c_262, plain, (![E_99]: ('#skF_4'(E_99, k5_partfun1('#skF_5', k1_tarski('#skF_6'), '#skF_8'), '#skF_5', k1_tarski('#skF_6'), '#skF_8')=E_99 | ~r2_hidden(E_99, k1_tarski('#skF_8')) | ~m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_5', k1_tarski('#skF_6')))) | ~v1_funct_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_184, c_260])).
% 9.02/3.19  tff(c_264, plain, (![E_99]: ('#skF_4'(E_99, k1_tarski('#skF_8'), '#skF_5', k1_tarski('#skF_6'), '#skF_8')=E_99 | ~r2_hidden(E_99, k1_tarski('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_66, c_184, c_262])).
% 9.02/3.19  tff(c_275, plain, (![E_106, A_107, B_108, C_109]: (v1_funct_1('#skF_4'(E_106, k5_partfun1(A_107, B_108, C_109), A_107, B_108, C_109)) | ~r2_hidden(E_106, k5_partfun1(A_107, B_108, C_109)) | ~m1_subset_1(C_109, k1_zfmisc_1(k2_zfmisc_1(A_107, B_108))) | ~v1_funct_1(C_109))), inference(cnfTransformation, [status(thm)], [f_65])).
% 9.02/3.19  tff(c_279, plain, (![E_106]: (v1_funct_1('#skF_4'(E_106, k5_partfun1('#skF_5', k1_tarski('#skF_6'), '#skF_8'), '#skF_5', k1_tarski('#skF_6'), '#skF_8')) | ~r2_hidden(E_106, k5_partfun1('#skF_5', k1_tarski('#skF_6'), '#skF_8')) | ~v1_funct_1('#skF_8'))), inference(resolution, [status(thm)], [c_66, c_275])).
% 9.02/3.19  tff(c_290, plain, (![E_110]: (v1_funct_1('#skF_4'(E_110, k1_tarski('#skF_8'), '#skF_5', k1_tarski('#skF_6'), '#skF_8')) | ~r2_hidden(E_110, k1_tarski('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_184, c_184, c_279])).
% 9.02/3.19  tff(c_293, plain, (![E_99]: (v1_funct_1(E_99) | ~r2_hidden(E_99, k1_tarski('#skF_8')) | ~r2_hidden(E_99, k1_tarski('#skF_8')))), inference(superposition, [status(thm), theory('equality')], [c_264, c_290])).
% 9.02/3.19  tff(c_411, plain, (v1_funct_1('#skF_3'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8'))) | ~r2_hidden('#skF_3'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')), k1_tarski('#skF_8')) | v1_funct_1('#skF_2'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8'))) | k5_partfun1('#skF_5', k1_tarski('#skF_6'), '#skF_7')=k1_tarski('#skF_8')), inference(resolution, [status(thm)], [c_402, c_293])).
% 9.02/3.19  tff(c_423, plain, (v1_funct_1('#skF_3'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8'))) | ~r2_hidden('#skF_3'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')), k1_tarski('#skF_8')) | v1_funct_1('#skF_2'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')))), inference(negUnitSimplification, [status(thm)], [c_64, c_411])).
% 9.02/3.19  tff(c_425, plain, (~r2_hidden('#skF_3'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')), k1_tarski('#skF_8'))), inference(splitLeft, [status(thm)], [c_423])).
% 9.02/3.19  tff(c_2139, plain, ('#skF_2'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8'))='#skF_1'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')) | k5_partfun1('#skF_5', k1_tarski('#skF_6'), '#skF_7')=k1_tarski('#skF_8')), inference(resolution, [status(thm)], [c_2113, c_425])).
% 9.02/3.19  tff(c_2172, plain, ('#skF_2'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8'))='#skF_1'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_64, c_2139])).
% 9.02/3.19  tff(c_343, plain, (![D_139]: (v1_funct_1('#skF_2'('#skF_5', k1_tarski('#skF_6'), '#skF_7', D_139)) | r2_hidden('#skF_3'('#skF_5', k1_tarski('#skF_6'), '#skF_7', D_139), D_139) | k5_partfun1('#skF_5', k1_tarski('#skF_6'), '#skF_7')=D_139)), inference(demodulation, [status(thm), theory('equality')], [c_74, c_334])).
% 9.02/3.19  tff(c_428, plain, (v1_funct_1('#skF_2'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8'))) | k5_partfun1('#skF_5', k1_tarski('#skF_6'), '#skF_7')=k1_tarski('#skF_8')), inference(resolution, [status(thm)], [c_343, c_425])).
% 9.02/3.19  tff(c_431, plain, (v1_funct_1('#skF_2'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')))), inference(negUnitSimplification, [status(thm)], [c_64, c_428])).
% 9.02/3.19  tff(c_2183, plain, (v1_funct_1('#skF_1'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_2172, c_431])).
% 9.02/3.19  tff(c_48, plain, (![A_8, B_9, C_10, D_32]: (m1_subset_1('#skF_2'(A_8, B_9, C_10, D_32), k1_zfmisc_1(k2_zfmisc_1(A_8, B_9))) | r2_hidden('#skF_3'(A_8, B_9, C_10, D_32), D_32) | k5_partfun1(A_8, B_9, C_10)=D_32 | ~m1_subset_1(C_10, k1_zfmisc_1(k2_zfmisc_1(A_8, B_9))) | ~v1_funct_1(C_10))), inference(cnfTransformation, [status(thm)], [f_65])).
% 9.02/3.19  tff(c_2187, plain, (m1_subset_1('#skF_1'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')), k1_zfmisc_1(k2_zfmisc_1('#skF_5', k1_tarski('#skF_6')))) | r2_hidden('#skF_3'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')), k1_tarski('#skF_8')) | k5_partfun1('#skF_5', k1_tarski('#skF_6'), '#skF_7')=k1_tarski('#skF_8') | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', k1_tarski('#skF_6')))) | ~v1_funct_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_2172, c_48])).
% 9.02/3.19  tff(c_2192, plain, (m1_subset_1('#skF_1'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')), k1_zfmisc_1(k2_zfmisc_1('#skF_5', k1_tarski('#skF_6')))) | r2_hidden('#skF_3'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')), k1_tarski('#skF_8')) | k5_partfun1('#skF_5', k1_tarski('#skF_6'), '#skF_7')=k1_tarski('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_2187])).
% 9.02/3.19  tff(c_2193, plain, (m1_subset_1('#skF_1'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')), k1_zfmisc_1(k2_zfmisc_1('#skF_5', k1_tarski('#skF_6'))))), inference(negUnitSimplification, [status(thm)], [c_64, c_425, c_2192])).
% 9.02/3.19  tff(c_56, plain, (![C_55, D_57, A_53, B_54]: (r1_partfun1(C_55, D_57) | ~m1_subset_1(D_57, k1_zfmisc_1(k2_zfmisc_1(A_53, k1_tarski(B_54)))) | ~v1_funct_1(D_57) | ~m1_subset_1(C_55, k1_zfmisc_1(k2_zfmisc_1(A_53, k1_tarski(B_54)))) | ~v1_funct_1(C_55))), inference(cnfTransformation, [status(thm)], [f_93])).
% 9.02/3.19  tff(c_2232, plain, (![C_55]: (r1_partfun1(C_55, '#skF_1'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8'))) | ~v1_funct_1('#skF_1'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8'))) | ~m1_subset_1(C_55, k1_zfmisc_1(k2_zfmisc_1('#skF_5', k1_tarski('#skF_6')))) | ~v1_funct_1(C_55))), inference(resolution, [status(thm)], [c_2193, c_56])).
% 9.02/3.19  tff(c_2277, plain, (![C_55]: (r1_partfun1(C_55, '#skF_1'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8'))) | ~m1_subset_1(C_55, k1_zfmisc_1(k2_zfmisc_1('#skF_5', k1_tarski('#skF_6')))) | ~v1_funct_1(C_55))), inference(demodulation, [status(thm), theory('equality')], [c_2183, c_2232])).
% 9.02/3.19  tff(c_475, plain, (![A_151, B_152, C_153, D_154]: (~r2_hidden('#skF_1'(A_151, B_152, C_153, D_154), D_154) | r2_hidden('#skF_3'(A_151, B_152, C_153, D_154), D_154) | k5_partfun1(A_151, B_152, C_153)=D_154 | ~m1_subset_1(C_153, k1_zfmisc_1(k2_zfmisc_1(A_151, B_152))) | ~v1_funct_1(C_153))), inference(cnfTransformation, [status(thm)], [f_65])).
% 9.02/3.19  tff(c_477, plain, (![D_154]: (~r2_hidden('#skF_1'('#skF_5', k1_tarski('#skF_6'), '#skF_7', D_154), D_154) | r2_hidden('#skF_3'('#skF_5', k1_tarski('#skF_6'), '#skF_7', D_154), D_154) | k5_partfun1('#skF_5', k1_tarski('#skF_6'), '#skF_7')=D_154 | ~v1_funct_1('#skF_7'))), inference(resolution, [status(thm)], [c_72, c_475])).
% 9.02/3.19  tff(c_510, plain, (![D_156]: (~r2_hidden('#skF_1'('#skF_5', k1_tarski('#skF_6'), '#skF_7', D_156), D_156) | r2_hidden('#skF_3'('#skF_5', k1_tarski('#skF_6'), '#skF_7', D_156), D_156) | k5_partfun1('#skF_5', k1_tarski('#skF_6'), '#skF_7')=D_156)), inference(demodulation, [status(thm), theory('equality')], [c_74, c_477])).
% 9.02/3.19  tff(c_513, plain, (~r2_hidden('#skF_1'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')), k1_tarski('#skF_8')) | k5_partfun1('#skF_5', k1_tarski('#skF_6'), '#skF_7')=k1_tarski('#skF_8')), inference(resolution, [status(thm)], [c_510, c_425])).
% 9.02/3.19  tff(c_528, plain, (~r2_hidden('#skF_1'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')), k1_tarski('#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_64, c_513])).
% 9.02/3.19  tff(c_681, plain, (![A_178, B_179, C_180, D_181]: (v1_partfun1('#skF_2'(A_178, B_179, C_180, D_181), A_178) | r2_hidden('#skF_3'(A_178, B_179, C_180, D_181), D_181) | k5_partfun1(A_178, B_179, C_180)=D_181 | ~m1_subset_1(C_180, k1_zfmisc_1(k2_zfmisc_1(A_178, B_179))) | ~v1_funct_1(C_180))), inference(cnfTransformation, [status(thm)], [f_65])).
% 9.02/3.19  tff(c_683, plain, (![D_181]: (v1_partfun1('#skF_2'('#skF_5', k1_tarski('#skF_6'), '#skF_7', D_181), '#skF_5') | r2_hidden('#skF_3'('#skF_5', k1_tarski('#skF_6'), '#skF_7', D_181), D_181) | k5_partfun1('#skF_5', k1_tarski('#skF_6'), '#skF_7')=D_181 | ~v1_funct_1('#skF_7'))), inference(resolution, [status(thm)], [c_72, c_681])).
% 9.02/3.19  tff(c_719, plain, (![D_183]: (v1_partfun1('#skF_2'('#skF_5', k1_tarski('#skF_6'), '#skF_7', D_183), '#skF_5') | r2_hidden('#skF_3'('#skF_5', k1_tarski('#skF_6'), '#skF_7', D_183), D_183) | k5_partfun1('#skF_5', k1_tarski('#skF_6'), '#skF_7')=D_183)), inference(demodulation, [status(thm), theory('equality')], [c_74, c_683])).
% 9.02/3.19  tff(c_724, plain, (v1_partfun1('#skF_2'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')), '#skF_5') | k5_partfun1('#skF_5', k1_tarski('#skF_6'), '#skF_7')=k1_tarski('#skF_8')), inference(resolution, [status(thm)], [c_719, c_425])).
% 9.02/3.19  tff(c_740, plain, (v1_partfun1('#skF_2'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_64, c_724])).
% 9.02/3.19  tff(c_2181, plain, (v1_partfun1('#skF_1'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_2172, c_740])).
% 9.02/3.19  tff(c_16, plain, (![F_49, A_8, B_9, C_10]: (r2_hidden(F_49, k5_partfun1(A_8, B_9, C_10)) | ~r1_partfun1(C_10, F_49) | ~v1_partfun1(F_49, A_8) | ~m1_subset_1(F_49, k1_zfmisc_1(k2_zfmisc_1(A_8, B_9))) | ~v1_funct_1(F_49) | ~m1_subset_1(C_10, k1_zfmisc_1(k2_zfmisc_1(A_8, B_9))) | ~v1_funct_1(C_10))), inference(cnfTransformation, [status(thm)], [f_65])).
% 9.02/3.19  tff(c_2212, plain, (![C_10]: (r2_hidden('#skF_1'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')), k5_partfun1('#skF_5', k1_tarski('#skF_6'), C_10)) | ~r1_partfun1(C_10, '#skF_1'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8'))) | ~v1_partfun1('#skF_1'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')), '#skF_5') | ~v1_funct_1('#skF_1'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8'))) | ~m1_subset_1(C_10, k1_zfmisc_1(k2_zfmisc_1('#skF_5', k1_tarski('#skF_6')))) | ~v1_funct_1(C_10))), inference(resolution, [status(thm)], [c_2193, c_16])).
% 9.02/3.19  tff(c_3347, plain, (![C_333]: (r2_hidden('#skF_1'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')), k5_partfun1('#skF_5', k1_tarski('#skF_6'), C_333)) | ~r1_partfun1(C_333, '#skF_1'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8'))) | ~m1_subset_1(C_333, k1_zfmisc_1(k2_zfmisc_1('#skF_5', k1_tarski('#skF_6')))) | ~v1_funct_1(C_333))), inference(demodulation, [status(thm), theory('equality')], [c_2183, c_2181, c_2212])).
% 9.02/3.19  tff(c_3355, plain, (r2_hidden('#skF_1'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')), k1_tarski('#skF_8')) | ~r1_partfun1('#skF_8', '#skF_1'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8'))) | ~m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_5', k1_tarski('#skF_6')))) | ~v1_funct_1('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_184, c_3347])).
% 9.02/3.19  tff(c_3360, plain, (r2_hidden('#skF_1'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')), k1_tarski('#skF_8')) | ~r1_partfun1('#skF_8', '#skF_1'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_66, c_3355])).
% 9.02/3.19  tff(c_3361, plain, (~r1_partfun1('#skF_8', '#skF_1'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')))), inference(negUnitSimplification, [status(thm)], [c_528, c_3360])).
% 9.02/3.19  tff(c_3364, plain, (~m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_5', k1_tarski('#skF_6')))) | ~v1_funct_1('#skF_8')), inference(resolution, [status(thm)], [c_2277, c_3361])).
% 9.02/3.19  tff(c_3368, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_66, c_3364])).
% 9.02/3.19  tff(c_3370, plain, (r2_hidden('#skF_3'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')), k1_tarski('#skF_8'))), inference(splitRight, [status(thm)], [c_423])).
% 9.02/3.19  tff(c_3710, plain, (![E_371, A_372, B_373, C_374]: (m1_subset_1('#skF_4'(E_371, k5_partfun1(A_372, B_373, C_374), A_372, B_373, C_374), k1_zfmisc_1(k2_zfmisc_1(A_372, B_373))) | ~r2_hidden(E_371, k5_partfun1(A_372, B_373, C_374)) | ~m1_subset_1(C_374, k1_zfmisc_1(k2_zfmisc_1(A_372, B_373))) | ~v1_funct_1(C_374))), inference(cnfTransformation, [status(thm)], [f_65])).
% 9.02/3.19  tff(c_3743, plain, (![E_371]: (m1_subset_1('#skF_4'(E_371, k1_tarski('#skF_8'), '#skF_5', k1_tarski('#skF_6'), '#skF_8'), k1_zfmisc_1(k2_zfmisc_1('#skF_5', k1_tarski('#skF_6')))) | ~r2_hidden(E_371, k5_partfun1('#skF_5', k1_tarski('#skF_6'), '#skF_8')) | ~m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_5', k1_tarski('#skF_6')))) | ~v1_funct_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_184, c_3710])).
% 9.02/3.19  tff(c_3765, plain, (![E_375]: (m1_subset_1('#skF_4'(E_375, k1_tarski('#skF_8'), '#skF_5', k1_tarski('#skF_6'), '#skF_8'), k1_zfmisc_1(k2_zfmisc_1('#skF_5', k1_tarski('#skF_6')))) | ~r2_hidden(E_375, k1_tarski('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_66, c_184, c_3743])).
% 9.02/3.19  tff(c_3795, plain, (![E_99]: (m1_subset_1(E_99, k1_zfmisc_1(k2_zfmisc_1('#skF_5', k1_tarski('#skF_6')))) | ~r2_hidden(E_99, k1_tarski('#skF_8')) | ~r2_hidden(E_99, k1_tarski('#skF_8')))), inference(superposition, [status(thm), theory('equality')], [c_264, c_3765])).
% 9.02/3.19  tff(c_3376, plain, (v1_funct_1('#skF_3'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8'))) | ~r2_hidden('#skF_3'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')), k1_tarski('#skF_8'))), inference(resolution, [status(thm)], [c_3370, c_293])).
% 9.02/3.19  tff(c_3385, plain, (v1_funct_1('#skF_3'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_3370, c_3376])).
% 9.02/3.19  tff(c_298, plain, (![E_117, A_118, B_119, C_120]: (v1_partfun1('#skF_4'(E_117, k5_partfun1(A_118, B_119, C_120), A_118, B_119, C_120), A_118) | ~r2_hidden(E_117, k5_partfun1(A_118, B_119, C_120)) | ~m1_subset_1(C_120, k1_zfmisc_1(k2_zfmisc_1(A_118, B_119))) | ~v1_funct_1(C_120))), inference(cnfTransformation, [status(thm)], [f_65])).
% 9.02/3.19  tff(c_303, plain, (![E_117]: (v1_partfun1('#skF_4'(E_117, k1_tarski('#skF_8'), '#skF_5', k1_tarski('#skF_6'), '#skF_8'), '#skF_5') | ~r2_hidden(E_117, k5_partfun1('#skF_5', k1_tarski('#skF_6'), '#skF_8')) | ~m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_5', k1_tarski('#skF_6')))) | ~v1_funct_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_184, c_298])).
% 9.02/3.19  tff(c_307, plain, (![E_121]: (v1_partfun1('#skF_4'(E_121, k1_tarski('#skF_8'), '#skF_5', k1_tarski('#skF_6'), '#skF_8'), '#skF_5') | ~r2_hidden(E_121, k1_tarski('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_66, c_184, c_303])).
% 9.02/3.19  tff(c_312, plain, (![E_99]: (v1_partfun1(E_99, '#skF_5') | ~r2_hidden(E_99, k1_tarski('#skF_8')) | ~r2_hidden(E_99, k1_tarski('#skF_8')))), inference(superposition, [status(thm), theory('equality')], [c_264, c_307])).
% 9.02/3.19  tff(c_3374, plain, (v1_partfun1('#skF_3'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')), '#skF_5') | ~r2_hidden('#skF_3'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')), k1_tarski('#skF_8'))), inference(resolution, [status(thm)], [c_3370, c_312])).
% 9.02/3.19  tff(c_3382, plain, (v1_partfun1('#skF_3'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_3370, c_3374])).
% 9.02/3.19  tff(c_3807, plain, (![E_376]: (m1_subset_1(E_376, k1_zfmisc_1(k2_zfmisc_1('#skF_5', k1_tarski('#skF_6')))) | ~r2_hidden(E_376, k1_tarski('#skF_8')) | ~r2_hidden(E_376, k1_tarski('#skF_8')))), inference(superposition, [status(thm), theory('equality')], [c_264, c_3765])).
% 9.02/3.19  tff(c_4169, plain, (![C_384, E_385]: (r1_partfun1(C_384, E_385) | ~v1_funct_1(E_385) | ~m1_subset_1(C_384, k1_zfmisc_1(k2_zfmisc_1('#skF_5', k1_tarski('#skF_6')))) | ~v1_funct_1(C_384) | ~r2_hidden(E_385, k1_tarski('#skF_8')))), inference(resolution, [status(thm)], [c_3807, c_56])).
% 9.02/3.19  tff(c_4178, plain, (![E_385]: (r1_partfun1('#skF_7', E_385) | ~v1_funct_1(E_385) | ~v1_funct_1('#skF_7') | ~r2_hidden(E_385, k1_tarski('#skF_8')))), inference(resolution, [status(thm)], [c_72, c_4169])).
% 9.02/3.19  tff(c_4190, plain, (![E_386]: (r1_partfun1('#skF_7', E_386) | ~v1_funct_1(E_386) | ~r2_hidden(E_386, k1_tarski('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_4178])).
% 9.02/3.19  tff(c_4237, plain, (r1_partfun1('#skF_7', '#skF_3'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8'))) | ~v1_funct_1('#skF_3'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')))), inference(resolution, [status(thm)], [c_3370, c_4190])).
% 9.02/3.19  tff(c_4274, plain, (r1_partfun1('#skF_7', '#skF_3'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_3385, c_4237])).
% 9.02/3.19  tff(c_5415, plain, (![A_447, B_448, C_449, D_450]: (v1_partfun1('#skF_2'(A_447, B_448, C_449, D_450), A_447) | ~r1_partfun1(C_449, '#skF_3'(A_447, B_448, C_449, D_450)) | ~v1_partfun1('#skF_3'(A_447, B_448, C_449, D_450), A_447) | ~m1_subset_1('#skF_3'(A_447, B_448, C_449, D_450), k1_zfmisc_1(k2_zfmisc_1(A_447, B_448))) | ~v1_funct_1('#skF_3'(A_447, B_448, C_449, D_450)) | k5_partfun1(A_447, B_448, C_449)=D_450 | ~m1_subset_1(C_449, k1_zfmisc_1(k2_zfmisc_1(A_447, B_448))) | ~v1_funct_1(C_449))), inference(cnfTransformation, [status(thm)], [f_65])).
% 9.02/3.19  tff(c_5420, plain, (v1_partfun1('#skF_2'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')), '#skF_5') | ~v1_partfun1('#skF_3'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')), '#skF_5') | ~m1_subset_1('#skF_3'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')), k1_zfmisc_1(k2_zfmisc_1('#skF_5', k1_tarski('#skF_6')))) | ~v1_funct_1('#skF_3'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8'))) | k5_partfun1('#skF_5', k1_tarski('#skF_6'), '#skF_7')=k1_tarski('#skF_8') | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', k1_tarski('#skF_6')))) | ~v1_funct_1('#skF_7')), inference(resolution, [status(thm)], [c_4274, c_5415])).
% 9.02/3.19  tff(c_5427, plain, (v1_partfun1('#skF_2'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')), '#skF_5') | ~m1_subset_1('#skF_3'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')), k1_zfmisc_1(k2_zfmisc_1('#skF_5', k1_tarski('#skF_6')))) | k5_partfun1('#skF_5', k1_tarski('#skF_6'), '#skF_7')=k1_tarski('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_3385, c_3382, c_5420])).
% 9.02/3.19  tff(c_5428, plain, (v1_partfun1('#skF_2'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')), '#skF_5') | ~m1_subset_1('#skF_3'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')), k1_zfmisc_1(k2_zfmisc_1('#skF_5', k1_tarski('#skF_6'))))), inference(negUnitSimplification, [status(thm)], [c_64, c_5427])).
% 9.02/3.19  tff(c_5429, plain, (~m1_subset_1('#skF_3'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')), k1_zfmisc_1(k2_zfmisc_1('#skF_5', k1_tarski('#skF_6'))))), inference(splitLeft, [status(thm)], [c_5428])).
% 9.02/3.19  tff(c_5432, plain, (~r2_hidden('#skF_3'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')), k1_tarski('#skF_8'))), inference(resolution, [status(thm)], [c_3795, c_5429])).
% 9.02/3.19  tff(c_5436, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3370, c_5432])).
% 9.02/3.19  tff(c_5438, plain, (m1_subset_1('#skF_3'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')), k1_zfmisc_1(k2_zfmisc_1('#skF_5', k1_tarski('#skF_6'))))), inference(splitRight, [status(thm)], [c_5428])).
% 9.02/3.19  tff(c_7337, plain, (![A_556, B_557, C_558, D_559]: ('#skF_2'(A_556, B_557, C_558, D_559)='#skF_1'(A_556, B_557, C_558, D_559) | ~r1_partfun1(C_558, '#skF_3'(A_556, B_557, C_558, D_559)) | ~v1_partfun1('#skF_3'(A_556, B_557, C_558, D_559), A_556) | ~m1_subset_1('#skF_3'(A_556, B_557, C_558, D_559), k1_zfmisc_1(k2_zfmisc_1(A_556, B_557))) | ~v1_funct_1('#skF_3'(A_556, B_557, C_558, D_559)) | k5_partfun1(A_556, B_557, C_558)=D_559 | ~m1_subset_1(C_558, k1_zfmisc_1(k2_zfmisc_1(A_556, B_557))) | ~v1_funct_1(C_558))), inference(cnfTransformation, [status(thm)], [f_65])).
% 9.02/3.19  tff(c_7351, plain, ('#skF_2'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8'))='#skF_1'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')) | ~v1_partfun1('#skF_3'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')), '#skF_5') | ~m1_subset_1('#skF_3'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')), k1_zfmisc_1(k2_zfmisc_1('#skF_5', k1_tarski('#skF_6')))) | ~v1_funct_1('#skF_3'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8'))) | k5_partfun1('#skF_5', k1_tarski('#skF_6'), '#skF_7')=k1_tarski('#skF_8') | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', k1_tarski('#skF_6')))) | ~v1_funct_1('#skF_7')), inference(resolution, [status(thm)], [c_4274, c_7337])).
% 9.02/3.19  tff(c_7368, plain, ('#skF_2'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8'))='#skF_1'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')) | k5_partfun1('#skF_5', k1_tarski('#skF_6'), '#skF_7')=k1_tarski('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_3385, c_5438, c_3382, c_7351])).
% 9.02/3.19  tff(c_7369, plain, ('#skF_2'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8'))='#skF_1'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_64, c_7368])).
% 9.02/3.19  tff(c_5993, plain, (![A_481, B_482, C_483, D_484]: ('#skF_2'(A_481, B_482, C_483, D_484)='#skF_1'(A_481, B_482, C_483, D_484) | ~r1_partfun1(C_483, '#skF_3'(A_481, B_482, C_483, D_484)) | ~v1_partfun1('#skF_3'(A_481, B_482, C_483, D_484), A_481) | ~m1_subset_1('#skF_3'(A_481, B_482, C_483, D_484), k1_zfmisc_1(k2_zfmisc_1(A_481, B_482))) | ~v1_funct_1('#skF_3'(A_481, B_482, C_483, D_484)) | k5_partfun1(A_481, B_482, C_483)=D_484 | ~m1_subset_1(C_483, k1_zfmisc_1(k2_zfmisc_1(A_481, B_482))) | ~v1_funct_1(C_483))), inference(cnfTransformation, [status(thm)], [f_65])).
% 9.02/3.19  tff(c_6007, plain, ('#skF_2'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8'))='#skF_1'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')) | ~v1_partfun1('#skF_3'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')), '#skF_5') | ~m1_subset_1('#skF_3'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')), k1_zfmisc_1(k2_zfmisc_1('#skF_5', k1_tarski('#skF_6')))) | ~v1_funct_1('#skF_3'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8'))) | k5_partfun1('#skF_5', k1_tarski('#skF_6'), '#skF_7')=k1_tarski('#skF_8') | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', k1_tarski('#skF_6')))) | ~v1_funct_1('#skF_7')), inference(resolution, [status(thm)], [c_4274, c_5993])).
% 9.02/3.19  tff(c_6024, plain, ('#skF_2'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8'))='#skF_1'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')) | k5_partfun1('#skF_5', k1_tarski('#skF_6'), '#skF_7')=k1_tarski('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_3385, c_5438, c_3382, c_6007])).
% 9.02/3.19  tff(c_6025, plain, ('#skF_2'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8'))='#skF_1'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_64, c_6024])).
% 9.02/3.19  tff(c_219, plain, (![C_93, D_94, A_95, B_96]: (r1_partfun1(C_93, D_94) | ~m1_subset_1(D_94, k1_zfmisc_1(k2_zfmisc_1(A_95, k1_tarski(B_96)))) | ~v1_funct_1(D_94) | ~m1_subset_1(C_93, k1_zfmisc_1(k2_zfmisc_1(A_95, k1_tarski(B_96)))) | ~v1_funct_1(C_93))), inference(cnfTransformation, [status(thm)], [f_93])).
% 9.02/3.19  tff(c_223, plain, (![C_93]: (r1_partfun1(C_93, '#skF_8') | ~v1_funct_1('#skF_8') | ~m1_subset_1(C_93, k1_zfmisc_1(k2_zfmisc_1('#skF_5', k1_tarski('#skF_6')))) | ~v1_funct_1(C_93))), inference(resolution, [status(thm)], [c_66, c_219])).
% 9.02/3.19  tff(c_232, plain, (![C_93]: (r1_partfun1(C_93, '#skF_8') | ~m1_subset_1(C_93, k1_zfmisc_1(k2_zfmisc_1('#skF_5', k1_tarski('#skF_6')))) | ~v1_funct_1(C_93))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_223])).
% 9.02/3.19  tff(c_3853, plain, (![E_377]: (r1_partfun1(E_377, '#skF_8') | ~v1_funct_1(E_377) | ~r2_hidden(E_377, k1_tarski('#skF_8')))), inference(resolution, [status(thm)], [c_3807, c_232])).
% 9.02/3.19  tff(c_3904, plain, (r1_partfun1('#skF_3'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')), '#skF_8') | ~v1_funct_1('#skF_3'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8'))) | v1_funct_1('#skF_2'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8'))) | k5_partfun1('#skF_5', k1_tarski('#skF_6'), '#skF_7')=k1_tarski('#skF_8')), inference(resolution, [status(thm)], [c_343, c_3853])).
% 9.02/3.19  tff(c_3940, plain, (r1_partfun1('#skF_3'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')), '#skF_8') | v1_funct_1('#skF_2'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8'))) | k5_partfun1('#skF_5', k1_tarski('#skF_6'), '#skF_7')=k1_tarski('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_3385, c_3904])).
% 9.02/3.19  tff(c_3941, plain, (r1_partfun1('#skF_3'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')), '#skF_8') | v1_funct_1('#skF_2'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')))), inference(negUnitSimplification, [status(thm)], [c_64, c_3940])).
% 9.02/3.19  tff(c_3946, plain, (v1_funct_1('#skF_2'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')))), inference(splitLeft, [status(thm)], [c_3941])).
% 9.02/3.19  tff(c_6035, plain, (v1_funct_1('#skF_1'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_6025, c_3946])).
% 9.02/3.19  tff(c_5799, plain, (![A_475, B_476, C_477, D_478]: (m1_subset_1('#skF_2'(A_475, B_476, C_477, D_478), k1_zfmisc_1(k2_zfmisc_1(A_475, B_476))) | ~r1_partfun1(C_477, '#skF_3'(A_475, B_476, C_477, D_478)) | ~v1_partfun1('#skF_3'(A_475, B_476, C_477, D_478), A_475) | ~m1_subset_1('#skF_3'(A_475, B_476, C_477, D_478), k1_zfmisc_1(k2_zfmisc_1(A_475, B_476))) | ~v1_funct_1('#skF_3'(A_475, B_476, C_477, D_478)) | k5_partfun1(A_475, B_476, C_477)=D_478 | ~m1_subset_1(C_477, k1_zfmisc_1(k2_zfmisc_1(A_475, B_476))) | ~v1_funct_1(C_477))), inference(cnfTransformation, [status(thm)], [f_65])).
% 9.02/3.19  tff(c_5810, plain, (m1_subset_1('#skF_2'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')), k1_zfmisc_1(k2_zfmisc_1('#skF_5', k1_tarski('#skF_6')))) | ~v1_partfun1('#skF_3'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')), '#skF_5') | ~m1_subset_1('#skF_3'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')), k1_zfmisc_1(k2_zfmisc_1('#skF_5', k1_tarski('#skF_6')))) | ~v1_funct_1('#skF_3'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8'))) | k5_partfun1('#skF_5', k1_tarski('#skF_6'), '#skF_7')=k1_tarski('#skF_8') | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', k1_tarski('#skF_6')))) | ~v1_funct_1('#skF_7')), inference(resolution, [status(thm)], [c_4274, c_5799])).
% 9.02/3.19  tff(c_5824, plain, (m1_subset_1('#skF_2'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')), k1_zfmisc_1(k2_zfmisc_1('#skF_5', k1_tarski('#skF_6')))) | k5_partfun1('#skF_5', k1_tarski('#skF_6'), '#skF_7')=k1_tarski('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_3385, c_5438, c_3382, c_5810])).
% 9.02/3.19  tff(c_5825, plain, (m1_subset_1('#skF_2'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')), k1_zfmisc_1(k2_zfmisc_1('#skF_5', k1_tarski('#skF_6'))))), inference(negUnitSimplification, [status(thm)], [c_64, c_5824])).
% 9.02/3.19  tff(c_6032, plain, (m1_subset_1('#skF_1'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')), k1_zfmisc_1(k2_zfmisc_1('#skF_5', k1_tarski('#skF_6'))))), inference(demodulation, [status(thm), theory('equality')], [c_6025, c_5825])).
% 9.02/3.19  tff(c_6097, plain, (![C_55]: (r1_partfun1(C_55, '#skF_1'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8'))) | ~v1_funct_1('#skF_1'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8'))) | ~m1_subset_1(C_55, k1_zfmisc_1(k2_zfmisc_1('#skF_5', k1_tarski('#skF_6')))) | ~v1_funct_1(C_55))), inference(resolution, [status(thm)], [c_6032, c_56])).
% 9.02/3.19  tff(c_6145, plain, (![C_55]: (r1_partfun1(C_55, '#skF_1'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8'))) | ~m1_subset_1(C_55, k1_zfmisc_1(k2_zfmisc_1('#skF_5', k1_tarski('#skF_6')))) | ~v1_funct_1(C_55))), inference(demodulation, [status(thm), theory('equality')], [c_6035, c_6097])).
% 9.02/3.19  tff(c_5849, plain, (r1_partfun1('#skF_2'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')), '#skF_8') | ~v1_funct_1('#skF_2'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')))), inference(resolution, [status(thm)], [c_5825, c_232])).
% 9.02/3.19  tff(c_5896, plain, (r1_partfun1('#skF_2'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_3946, c_5849])).
% 9.02/3.19  tff(c_5437, plain, (v1_partfun1('#skF_2'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')), '#skF_5')), inference(splitRight, [status(thm)], [c_5428])).
% 9.02/3.19  tff(c_62, plain, (![A_63, B_64, C_65]: (k5_partfun1(A_63, B_64, C_65)=k1_tarski(C_65) | ~v1_partfun1(C_65, A_63) | ~m1_subset_1(C_65, k1_zfmisc_1(k2_zfmisc_1(A_63, B_64))) | ~v1_funct_1(C_65))), inference(cnfTransformation, [status(thm)], [f_118])).
% 9.02/3.19  tff(c_5860, plain, (k5_partfun1('#skF_5', k1_tarski('#skF_6'), '#skF_2'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')))=k1_tarski('#skF_2'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8'))) | ~v1_partfun1('#skF_2'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')), '#skF_5') | ~v1_funct_1('#skF_2'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')))), inference(resolution, [status(thm)], [c_5825, c_62])).
% 9.02/3.19  tff(c_5908, plain, (k5_partfun1('#skF_5', k1_tarski('#skF_6'), '#skF_2'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')))=k1_tarski('#skF_2'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_3946, c_5437, c_5860])).
% 9.02/3.19  tff(c_4143, plain, (![F_380, A_381, B_382, C_383]: (r2_hidden(F_380, k5_partfun1(A_381, B_382, C_383)) | ~r1_partfun1(C_383, F_380) | ~v1_partfun1(F_380, A_381) | ~m1_subset_1(F_380, k1_zfmisc_1(k2_zfmisc_1(A_381, B_382))) | ~v1_funct_1(F_380) | ~m1_subset_1(C_383, k1_zfmisc_1(k2_zfmisc_1(A_381, B_382))) | ~v1_funct_1(C_383))), inference(cnfTransformation, [status(thm)], [f_65])).
% 9.02/3.19  tff(c_4153, plain, (![C_383]: (r2_hidden('#skF_8', k5_partfun1('#skF_5', k1_tarski('#skF_6'), C_383)) | ~r1_partfun1(C_383, '#skF_8') | ~v1_partfun1('#skF_8', '#skF_5') | ~v1_funct_1('#skF_8') | ~m1_subset_1(C_383, k1_zfmisc_1(k2_zfmisc_1('#skF_5', k1_tarski('#skF_6')))) | ~v1_funct_1(C_383))), inference(resolution, [status(thm)], [c_66, c_4143])).
% 9.02/3.19  tff(c_4496, plain, (![C_395]: (r2_hidden('#skF_8', k5_partfun1('#skF_5', k1_tarski('#skF_6'), C_395)) | ~r1_partfun1(C_395, '#skF_8') | ~m1_subset_1(C_395, k1_zfmisc_1(k2_zfmisc_1('#skF_5', k1_tarski('#skF_6')))) | ~v1_funct_1(C_395))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_181, c_4153])).
% 9.02/3.19  tff(c_4513, plain, (![E_99]: (r2_hidden('#skF_8', k5_partfun1('#skF_5', k1_tarski('#skF_6'), E_99)) | ~r1_partfun1(E_99, '#skF_8') | ~v1_funct_1(E_99) | ~r2_hidden(E_99, k1_tarski('#skF_8')))), inference(resolution, [status(thm)], [c_3795, c_4496])).
% 9.02/3.19  tff(c_5963, plain, (r2_hidden('#skF_8', k1_tarski('#skF_2'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')))) | ~r1_partfun1('#skF_2'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')), '#skF_8') | ~v1_funct_1('#skF_2'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8'))) | ~r2_hidden('#skF_2'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')), k1_tarski('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_5908, c_4513])).
% 9.02/3.19  tff(c_5982, plain, (r2_hidden('#skF_8', k1_tarski('#skF_2'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')))) | ~r2_hidden('#skF_2'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')), k1_tarski('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_3946, c_5896, c_5963])).
% 9.02/3.19  tff(c_5992, plain, (~r2_hidden('#skF_2'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')), k1_tarski('#skF_8'))), inference(splitLeft, [status(thm)], [c_5982])).
% 9.02/3.19  tff(c_6026, plain, (~r2_hidden('#skF_1'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')), k1_tarski('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_6025, c_5992])).
% 9.02/3.19  tff(c_5836, plain, (![C_10]: (r2_hidden('#skF_2'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')), k5_partfun1('#skF_5', k1_tarski('#skF_6'), C_10)) | ~r1_partfun1(C_10, '#skF_2'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8'))) | ~v1_partfun1('#skF_2'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')), '#skF_5') | ~v1_funct_1('#skF_2'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8'))) | ~m1_subset_1(C_10, k1_zfmisc_1(k2_zfmisc_1('#skF_5', k1_tarski('#skF_6')))) | ~v1_funct_1(C_10))), inference(resolution, [status(thm)], [c_5825, c_16])).
% 9.02/3.19  tff(c_5878, plain, (![C_10]: (r2_hidden('#skF_2'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')), k5_partfun1('#skF_5', k1_tarski('#skF_6'), C_10)) | ~r1_partfun1(C_10, '#skF_2'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8'))) | ~m1_subset_1(C_10, k1_zfmisc_1(k2_zfmisc_1('#skF_5', k1_tarski('#skF_6')))) | ~v1_funct_1(C_10))), inference(demodulation, [status(thm), theory('equality')], [c_3946, c_5437, c_5836])).
% 9.02/3.19  tff(c_7254, plain, (![C_555]: (r2_hidden('#skF_1'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')), k5_partfun1('#skF_5', k1_tarski('#skF_6'), C_555)) | ~r1_partfun1(C_555, '#skF_1'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8'))) | ~m1_subset_1(C_555, k1_zfmisc_1(k2_zfmisc_1('#skF_5', k1_tarski('#skF_6')))) | ~v1_funct_1(C_555))), inference(demodulation, [status(thm), theory('equality')], [c_6025, c_6025, c_5878])).
% 9.02/3.19  tff(c_7265, plain, (r2_hidden('#skF_1'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')), k1_tarski('#skF_8')) | ~r1_partfun1('#skF_8', '#skF_1'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8'))) | ~m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_5', k1_tarski('#skF_6')))) | ~v1_funct_1('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_184, c_7254])).
% 9.02/3.19  tff(c_7272, plain, (r2_hidden('#skF_1'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')), k1_tarski('#skF_8')) | ~r1_partfun1('#skF_8', '#skF_1'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_66, c_7265])).
% 9.02/3.19  tff(c_7273, plain, (~r1_partfun1('#skF_8', '#skF_1'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')))), inference(negUnitSimplification, [status(thm)], [c_6026, c_7272])).
% 9.02/3.19  tff(c_7276, plain, (~m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_5', k1_tarski('#skF_6')))) | ~v1_funct_1('#skF_8')), inference(resolution, [status(thm)], [c_6145, c_7273])).
% 9.02/3.19  tff(c_7280, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_66, c_7276])).
% 9.02/3.19  tff(c_7282, plain, (r2_hidden('#skF_2'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')), k1_tarski('#skF_8'))), inference(splitRight, [status(thm)], [c_5982])).
% 9.02/3.19  tff(c_7371, plain, (r2_hidden('#skF_1'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')), k1_tarski('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_7369, c_7282])).
% 9.02/3.19  tff(c_28, plain, (![A_8, B_9, C_10, D_32]: (~r2_hidden('#skF_1'(A_8, B_9, C_10, D_32), D_32) | ~r1_partfun1(C_10, '#skF_3'(A_8, B_9, C_10, D_32)) | ~v1_partfun1('#skF_3'(A_8, B_9, C_10, D_32), A_8) | ~m1_subset_1('#skF_3'(A_8, B_9, C_10, D_32), k1_zfmisc_1(k2_zfmisc_1(A_8, B_9))) | ~v1_funct_1('#skF_3'(A_8, B_9, C_10, D_32)) | k5_partfun1(A_8, B_9, C_10)=D_32 | ~m1_subset_1(C_10, k1_zfmisc_1(k2_zfmisc_1(A_8, B_9))) | ~v1_funct_1(C_10))), inference(cnfTransformation, [status(thm)], [f_65])).
% 9.02/3.19  tff(c_7421, plain, (~r1_partfun1('#skF_7', '#skF_3'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8'))) | ~v1_partfun1('#skF_3'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')), '#skF_5') | ~m1_subset_1('#skF_3'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')), k1_zfmisc_1(k2_zfmisc_1('#skF_5', k1_tarski('#skF_6')))) | ~v1_funct_1('#skF_3'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8'))) | k5_partfun1('#skF_5', k1_tarski('#skF_6'), '#skF_7')=k1_tarski('#skF_8') | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', k1_tarski('#skF_6')))) | ~v1_funct_1('#skF_7')), inference(resolution, [status(thm)], [c_7371, c_28])).
% 9.02/3.19  tff(c_7447, plain, (k5_partfun1('#skF_5', k1_tarski('#skF_6'), '#skF_7')=k1_tarski('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_3385, c_5438, c_3382, c_4274, c_7421])).
% 9.02/3.19  tff(c_7449, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_7447])).
% 9.02/3.19  tff(c_7451, plain, (~v1_funct_1('#skF_2'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')))), inference(splitRight, [status(thm)], [c_3941])).
% 9.02/3.19  tff(c_7650, plain, (![C_565, E_566]: (r1_partfun1(C_565, E_566) | ~v1_funct_1(E_566) | ~m1_subset_1(C_565, k1_zfmisc_1(k2_zfmisc_1('#skF_5', k1_tarski('#skF_6')))) | ~v1_funct_1(C_565) | ~r2_hidden(E_566, k1_tarski('#skF_8')))), inference(resolution, [status(thm)], [c_3807, c_56])).
% 9.02/3.19  tff(c_7659, plain, (![E_566]: (r1_partfun1('#skF_7', E_566) | ~v1_funct_1(E_566) | ~v1_funct_1('#skF_7') | ~r2_hidden(E_566, k1_tarski('#skF_8')))), inference(resolution, [status(thm)], [c_72, c_7650])).
% 9.02/3.19  tff(c_7697, plain, (![E_571]: (r1_partfun1('#skF_7', E_571) | ~v1_funct_1(E_571) | ~r2_hidden(E_571, k1_tarski('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_7659])).
% 9.02/3.19  tff(c_7744, plain, (r1_partfun1('#skF_7', '#skF_3'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8'))) | ~v1_funct_1('#skF_3'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')))), inference(resolution, [status(thm)], [c_3370, c_7697])).
% 9.02/3.19  tff(c_7781, plain, (r1_partfun1('#skF_7', '#skF_3'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_3385, c_7744])).
% 9.02/3.19  tff(c_8304, plain, (![A_589, B_590, C_591, D_592]: (v1_funct_1('#skF_2'(A_589, B_590, C_591, D_592)) | ~r1_partfun1(C_591, '#skF_3'(A_589, B_590, C_591, D_592)) | ~v1_partfun1('#skF_3'(A_589, B_590, C_591, D_592), A_589) | ~m1_subset_1('#skF_3'(A_589, B_590, C_591, D_592), k1_zfmisc_1(k2_zfmisc_1(A_589, B_590))) | ~v1_funct_1('#skF_3'(A_589, B_590, C_591, D_592)) | k5_partfun1(A_589, B_590, C_591)=D_592 | ~m1_subset_1(C_591, k1_zfmisc_1(k2_zfmisc_1(A_589, B_590))) | ~v1_funct_1(C_591))), inference(cnfTransformation, [status(thm)], [f_65])).
% 9.02/3.19  tff(c_8309, plain, (v1_funct_1('#skF_2'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8'))) | ~v1_partfun1('#skF_3'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')), '#skF_5') | ~m1_subset_1('#skF_3'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')), k1_zfmisc_1(k2_zfmisc_1('#skF_5', k1_tarski('#skF_6')))) | ~v1_funct_1('#skF_3'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8'))) | k5_partfun1('#skF_5', k1_tarski('#skF_6'), '#skF_7')=k1_tarski('#skF_8') | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', k1_tarski('#skF_6')))) | ~v1_funct_1('#skF_7')), inference(resolution, [status(thm)], [c_7781, c_8304])).
% 9.02/3.19  tff(c_8316, plain, (v1_funct_1('#skF_2'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8'))) | ~m1_subset_1('#skF_3'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')), k1_zfmisc_1(k2_zfmisc_1('#skF_5', k1_tarski('#skF_6')))) | k5_partfun1('#skF_5', k1_tarski('#skF_6'), '#skF_7')=k1_tarski('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_3385, c_3382, c_8309])).
% 9.02/3.19  tff(c_8317, plain, (~m1_subset_1('#skF_3'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')), k1_zfmisc_1(k2_zfmisc_1('#skF_5', k1_tarski('#skF_6'))))), inference(negUnitSimplification, [status(thm)], [c_64, c_7451, c_8316])).
% 9.02/3.19  tff(c_8421, plain, (~r2_hidden('#skF_3'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')), k1_tarski('#skF_8'))), inference(resolution, [status(thm)], [c_3795, c_8317])).
% 9.02/3.19  tff(c_8425, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3370, c_8421])).
% 9.02/3.19  tff(c_8426, plain, (k1_tarski('#skF_6')=k1_xboole_0), inference(splitRight, [status(thm)], [c_160])).
% 9.02/3.19  tff(c_12, plain, (![A_6, B_7]: (k2_zfmisc_1(A_6, k1_tarski(B_7))!=k1_xboole_0 | k1_xboole_0=A_6)), inference(cnfTransformation, [status(thm)], [f_44])).
% 9.02/3.19  tff(c_8436, plain, (![A_6]: (k2_zfmisc_1(A_6, k1_xboole_0)!=k1_xboole_0 | k1_xboole_0=A_6)), inference(superposition, [status(thm), theory('equality')], [c_8426, c_12])).
% 9.02/3.19  tff(c_8442, plain, (![A_6]: (k1_xboole_0=A_6)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_8436])).
% 9.02/3.19  tff(c_8430, plain, (k5_partfun1('#skF_5', k1_xboole_0, '#skF_7')!=k1_tarski('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_8426, c_64])).
% 9.02/3.19  tff(c_8760, plain, (k1_tarski('#skF_8')!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_8442, c_8430])).
% 9.02/3.19  tff(c_8774, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_8442, c_8760])).
% 9.02/3.19  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.02/3.19  
% 9.02/3.19  Inference rules
% 9.02/3.19  ----------------------
% 9.02/3.19  #Ref     : 0
% 9.02/3.19  #Sup     : 1825
% 9.02/3.19  #Fact    : 0
% 9.02/3.19  #Define  : 0
% 9.02/3.19  #Split   : 13
% 9.02/3.19  #Chain   : 0
% 9.02/3.19  #Close   : 0
% 9.02/3.19  
% 9.02/3.19  Ordering : KBO
% 9.02/3.19  
% 9.02/3.19  Simplification rules
% 9.02/3.19  ----------------------
% 9.02/3.19  #Subsume      : 195
% 9.02/3.19  #Demod        : 1333
% 9.02/3.19  #Tautology    : 496
% 9.02/3.19  #SimpNegUnit  : 189
% 9.02/3.19  #BackRed      : 31
% 9.02/3.19  
% 9.02/3.19  #Partial instantiations: 230
% 9.02/3.19  #Strategies tried      : 1
% 9.02/3.19  
% 9.02/3.19  Timing (in seconds)
% 9.02/3.19  ----------------------
% 9.49/3.20  Preprocessing        : 0.36
% 9.49/3.20  Parsing              : 0.17
% 9.49/3.20  CNF conversion       : 0.03
% 9.49/3.20  Main loop            : 2.03
% 9.49/3.20  Inferencing          : 0.69
% 9.49/3.20  Reduction            : 0.69
% 9.49/3.20  Demodulation         : 0.50
% 9.49/3.20  BG Simplification    : 0.08
% 9.49/3.20  Subsumption          : 0.41
% 9.49/3.20  Abstraction          : 0.12
% 9.49/3.20  MUC search           : 0.00
% 9.50/3.20  Cooper               : 0.00
% 9.50/3.20  Total                : 2.45
% 9.50/3.20  Index Insertion      : 0.00
% 9.50/3.20  Index Deletion       : 0.00
% 9.50/3.20  Index Matching       : 0.00
% 9.50/3.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
