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

% Result     : Theorem 14.88s
% Output     : CNFRefutation 15.38s
% Verified   : 
% Statistics : Number of formulae       :  247 (40474 expanded)
%              Number of leaves         :   34 (13999 expanded)
%              Depth                    :   38
%              Number of atoms          :  715 (167140 expanded)
%              Number of equality atoms :  206 (30411 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v1_partfun1 > r2_hidden > r1_partfun1 > m1_subset_1 > v1_funct_1 > k5_partfun1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_6 > #skF_7 > #skF_10 > #skF_9 > #skF_4 > #skF_8 > #skF_5 > #skF_2 > #skF_3 > #skF_1

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

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i * $i ) > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(k5_partfun1,type,(
    k5_partfun1: ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(r1_partfun1,type,(
    r1_partfun1: ( $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_42,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_131,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,A,k1_tarski(B))
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
           => k5_partfun1(A,k1_tarski(B),C) = k1_tarski(D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t164_funct_2)).

tff(f_100,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
     => ! [D] :
          ( ( v1_funct_1(D)
            & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
         => r1_partfun1(C,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_partfun1)).

tff(f_89,axiom,(
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

tff(f_72,axiom,(
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

tff(f_32,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_117,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [D] :
          ( ( v1_funct_1(D)
            & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
         => ( ( v1_partfun1(C,A)
              & v1_partfun1(D,A)
              & r1_partfun1(C,D) )
           => C = D ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_partfun1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( A != k1_xboole_0
     => ( k2_zfmisc_1(k1_tarski(B),A) != k1_xboole_0
        & k2_zfmisc_1(A,k1_tarski(B)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t130_zfmisc_1)).

tff(c_20,plain,(
    ! [A_9] : k2_zfmisc_1(A_9,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_78,plain,(
    v1_funct_1('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_74,plain,(
    m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8')))) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_72,plain,(
    k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') != k1_tarski('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_82,plain,(
    v1_funct_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_80,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8')))) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_193,plain,(
    ! [C_96,D_97,A_98,B_99] :
      ( r1_partfun1(C_96,D_97)
      | ~ m1_subset_1(D_97,k1_zfmisc_1(k2_zfmisc_1(A_98,k1_tarski(B_99))))
      | ~ v1_funct_1(D_97)
      | ~ m1_subset_1(C_96,k1_zfmisc_1(k2_zfmisc_1(A_98,k1_tarski(B_99))))
      | ~ v1_funct_1(C_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_195,plain,(
    ! [C_96] :
      ( r1_partfun1(C_96,'#skF_10')
      | ~ v1_funct_1('#skF_10')
      | ~ m1_subset_1(C_96,k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
      | ~ v1_funct_1(C_96) ) ),
    inference(resolution,[status(thm)],[c_74,c_193])).

tff(c_208,plain,(
    ! [C_100] :
      ( r1_partfun1(C_100,'#skF_10')
      | ~ m1_subset_1(C_100,k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
      | ~ v1_funct_1(C_100) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_195])).

tff(c_214,plain,
    ( r1_partfun1('#skF_9','#skF_10')
    | ~ v1_funct_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_80,c_208])).

tff(c_220,plain,(
    r1_partfun1('#skF_9','#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_214])).

tff(c_76,plain,(
    v1_funct_2('#skF_10','#skF_7',k1_tarski('#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_170,plain,(
    ! [B_91,C_92,A_93] :
      ( k1_xboole_0 = B_91
      | v1_partfun1(C_92,A_93)
      | ~ v1_funct_2(C_92,A_93,B_91)
      | ~ m1_subset_1(C_92,k1_zfmisc_1(k2_zfmisc_1(A_93,B_91)))
      | ~ v1_funct_1(C_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_173,plain,
    ( k1_tarski('#skF_8') = k1_xboole_0
    | v1_partfun1('#skF_10','#skF_7')
    | ~ v1_funct_2('#skF_10','#skF_7',k1_tarski('#skF_8'))
    | ~ v1_funct_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_74,c_170])).

tff(c_185,plain,
    ( k1_tarski('#skF_8') = k1_xboole_0
    | v1_partfun1('#skF_10','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_173])).

tff(c_190,plain,(
    v1_partfun1('#skF_10','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_185])).

tff(c_699,plain,(
    ! [F_227,A_228,B_229,C_230] :
      ( r2_hidden(F_227,k5_partfun1(A_228,B_229,C_230))
      | ~ r1_partfun1(C_230,F_227)
      | ~ v1_partfun1(F_227,A_228)
      | ~ m1_subset_1(F_227,k1_zfmisc_1(k2_zfmisc_1(A_228,B_229)))
      | ~ v1_funct_1(F_227)
      | ~ m1_subset_1(C_230,k1_zfmisc_1(k2_zfmisc_1(A_228,B_229)))
      | ~ v1_funct_1(C_230) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_703,plain,(
    ! [C_230] :
      ( r2_hidden('#skF_10',k5_partfun1('#skF_7',k1_tarski('#skF_8'),C_230))
      | ~ r1_partfun1(C_230,'#skF_10')
      | ~ v1_partfun1('#skF_10','#skF_7')
      | ~ v1_funct_1('#skF_10')
      | ~ m1_subset_1(C_230,k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
      | ~ v1_funct_1(C_230) ) ),
    inference(resolution,[status(thm)],[c_74,c_699])).

tff(c_719,plain,(
    ! [C_231] :
      ( r2_hidden('#skF_10',k5_partfun1('#skF_7',k1_tarski('#skF_8'),C_231))
      | ~ r1_partfun1(C_231,'#skF_10')
      | ~ m1_subset_1(C_231,k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
      | ~ v1_funct_1(C_231) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_190,c_703])).

tff(c_729,plain,
    ( r2_hidden('#skF_10',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9'))
    | ~ r1_partfun1('#skF_9','#skF_10')
    | ~ v1_funct_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_80,c_719])).

tff(c_736,plain,(
    r2_hidden('#skF_10',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_220,c_729])).

tff(c_12,plain,(
    ! [A_1,B_2] :
      ( '#skF_1'(A_1,B_2) = A_1
      | r2_hidden('#skF_2'(A_1,B_2),B_2)
      | k1_tarski(A_1) = B_2 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_289,plain,(
    ! [A_132,B_133,C_134,D_135] :
      ( v1_funct_1('#skF_4'(A_132,B_133,C_134,D_135))
      | r2_hidden('#skF_5'(A_132,B_133,C_134,D_135),D_135)
      | k5_partfun1(A_132,B_133,C_134) = D_135
      | ~ m1_subset_1(C_134,k1_zfmisc_1(k2_zfmisc_1(A_132,B_133)))
      | ~ v1_funct_1(C_134) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_293,plain,(
    ! [D_135] :
      ( v1_funct_1('#skF_4'('#skF_7',k1_tarski('#skF_8'),'#skF_9',D_135))
      | r2_hidden('#skF_5'('#skF_7',k1_tarski('#skF_8'),'#skF_9',D_135),D_135)
      | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') = D_135
      | ~ v1_funct_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_80,c_289])).

tff(c_303,plain,(
    ! [D_135] :
      ( v1_funct_1('#skF_4'('#skF_7',k1_tarski('#skF_8'),'#skF_9',D_135))
      | r2_hidden('#skF_5'('#skF_7',k1_tarski('#skF_8'),'#skF_9',D_135),D_135)
      | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') = D_135 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_293])).

tff(c_329,plain,(
    ! [D_141] :
      ( v1_funct_1('#skF_4'('#skF_7',k1_tarski('#skF_8'),'#skF_9',D_141))
      | r2_hidden('#skF_5'('#skF_7',k1_tarski('#skF_8'),'#skF_9',D_141),D_141)
      | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') = D_141 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_293])).

tff(c_34,plain,(
    ! [E_51,B_14,A_13,C_15] :
      ( '#skF_6'(E_51,B_14,k5_partfun1(A_13,B_14,C_15),A_13,C_15) = E_51
      | ~ r2_hidden(E_51,k5_partfun1(A_13,B_14,C_15))
      | ~ m1_subset_1(C_15,k1_zfmisc_1(k2_zfmisc_1(A_13,B_14)))
      | ~ v1_funct_1(C_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_2113,plain,(
    ! [A_456,B_457,C_458] :
      ( '#skF_6'('#skF_5'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1(A_456,B_457,C_458)),B_457,k5_partfun1(A_456,B_457,C_458),A_456,C_458) = '#skF_5'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1(A_456,B_457,C_458))
      | ~ m1_subset_1(C_458,k1_zfmisc_1(k2_zfmisc_1(A_456,B_457)))
      | ~ v1_funct_1(C_458)
      | v1_funct_1('#skF_4'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1(A_456,B_457,C_458)))
      | k5_partfun1(A_456,B_457,C_458) = k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_329,c_34])).

tff(c_268,plain,(
    ! [E_112,B_113,A_114,C_115] :
      ( v1_funct_1('#skF_6'(E_112,B_113,k5_partfun1(A_114,B_113,C_115),A_114,C_115))
      | ~ r2_hidden(E_112,k5_partfun1(A_114,B_113,C_115))
      | ~ m1_subset_1(C_115,k1_zfmisc_1(k2_zfmisc_1(A_114,B_113)))
      | ~ v1_funct_1(C_115) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_270,plain,(
    ! [E_112] :
      ( v1_funct_1('#skF_6'(E_112,k1_tarski('#skF_8'),k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10'),'#skF_7','#skF_10'))
      | ~ r2_hidden(E_112,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10'))
      | ~ v1_funct_1('#skF_10') ) ),
    inference(resolution,[status(thm)],[c_74,c_268])).

tff(c_279,plain,(
    ! [E_112] :
      ( v1_funct_1('#skF_6'(E_112,k1_tarski('#skF_8'),k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10'),'#skF_7','#skF_10'))
      | ~ r2_hidden(E_112,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_270])).

tff(c_2169,plain,
    ( v1_funct_1('#skF_5'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')))
    | ~ r2_hidden('#skF_5'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')),k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10'))
    | ~ m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
    | ~ v1_funct_1('#skF_10')
    | v1_funct_1('#skF_4'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')))
    | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10') = k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_2113,c_279])).

tff(c_2184,plain,
    ( v1_funct_1('#skF_5'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')))
    | ~ r2_hidden('#skF_5'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')),k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10'))
    | v1_funct_1('#skF_4'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')))
    | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10') = k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_74,c_2169])).

tff(c_2355,plain,(
    ~ r2_hidden('#skF_5'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')),k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')) ),
    inference(splitLeft,[status(thm)],[c_2184])).

tff(c_2394,plain,
    ( v1_funct_1('#skF_4'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')))
    | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10') = k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') ),
    inference(resolution,[status(thm)],[c_303,c_2355])).

tff(c_2395,plain,(
    k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10') = k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') ),
    inference(splitLeft,[status(thm)],[c_2394])).

tff(c_2430,plain,(
    ! [E_112] :
      ( v1_funct_1('#skF_6'(E_112,k1_tarski('#skF_8'),k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9'),'#skF_7','#skF_10'))
      | ~ r2_hidden(E_112,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2395,c_2395,c_279])).

tff(c_32,plain,(
    ! [E_51,B_14,A_13,C_15] :
      ( v1_partfun1('#skF_6'(E_51,B_14,k5_partfun1(A_13,B_14,C_15),A_13,C_15),A_13)
      | ~ r2_hidden(E_51,k5_partfun1(A_13,B_14,C_15))
      | ~ m1_subset_1(C_15,k1_zfmisc_1(k2_zfmisc_1(A_13,B_14)))
      | ~ v1_funct_1(C_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_36,plain,(
    ! [E_51,B_14,A_13,C_15] :
      ( m1_subset_1('#skF_6'(E_51,B_14,k5_partfun1(A_13,B_14,C_15),A_13,C_15),k1_zfmisc_1(k2_zfmisc_1(A_13,B_14)))
      | ~ r2_hidden(E_51,k5_partfun1(A_13,B_14,C_15))
      | ~ m1_subset_1(C_15,k1_zfmisc_1(k2_zfmisc_1(A_13,B_14)))
      | ~ v1_funct_1(C_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_30,plain,(
    ! [C_15,E_51,B_14,A_13] :
      ( r1_partfun1(C_15,'#skF_6'(E_51,B_14,k5_partfun1(A_13,B_14,C_15),A_13,C_15))
      | ~ r2_hidden(E_51,k5_partfun1(A_13,B_14,C_15))
      | ~ m1_subset_1(C_15,k1_zfmisc_1(k2_zfmisc_1(A_13,B_14)))
      | ~ v1_funct_1(C_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_460,plain,(
    ! [D_174,C_175,A_176,B_177] :
      ( D_174 = C_175
      | ~ r1_partfun1(C_175,D_174)
      | ~ v1_partfun1(D_174,A_176)
      | ~ v1_partfun1(C_175,A_176)
      | ~ m1_subset_1(D_174,k1_zfmisc_1(k2_zfmisc_1(A_176,B_177)))
      | ~ v1_funct_1(D_174)
      | ~ m1_subset_1(C_175,k1_zfmisc_1(k2_zfmisc_1(A_176,B_177)))
      | ~ v1_funct_1(C_175) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_6979,plain,(
    ! [B_628,A_629,E_627,A_631,B_630,C_632] :
      ( '#skF_6'(E_627,B_628,k5_partfun1(A_631,B_628,C_632),A_631,C_632) = C_632
      | ~ v1_partfun1('#skF_6'(E_627,B_628,k5_partfun1(A_631,B_628,C_632),A_631,C_632),A_629)
      | ~ v1_partfun1(C_632,A_629)
      | ~ m1_subset_1('#skF_6'(E_627,B_628,k5_partfun1(A_631,B_628,C_632),A_631,C_632),k1_zfmisc_1(k2_zfmisc_1(A_629,B_630)))
      | ~ v1_funct_1('#skF_6'(E_627,B_628,k5_partfun1(A_631,B_628,C_632),A_631,C_632))
      | ~ m1_subset_1(C_632,k1_zfmisc_1(k2_zfmisc_1(A_629,B_630)))
      | ~ r2_hidden(E_627,k5_partfun1(A_631,B_628,C_632))
      | ~ m1_subset_1(C_632,k1_zfmisc_1(k2_zfmisc_1(A_631,B_628)))
      | ~ v1_funct_1(C_632) ) ),
    inference(resolution,[status(thm)],[c_30,c_460])).

tff(c_8697,plain,(
    ! [E_697,B_698,A_699,C_700] :
      ( '#skF_6'(E_697,B_698,k5_partfun1(A_699,B_698,C_700),A_699,C_700) = C_700
      | ~ v1_partfun1('#skF_6'(E_697,B_698,k5_partfun1(A_699,B_698,C_700),A_699,C_700),A_699)
      | ~ v1_partfun1(C_700,A_699)
      | ~ v1_funct_1('#skF_6'(E_697,B_698,k5_partfun1(A_699,B_698,C_700),A_699,C_700))
      | ~ r2_hidden(E_697,k5_partfun1(A_699,B_698,C_700))
      | ~ m1_subset_1(C_700,k1_zfmisc_1(k2_zfmisc_1(A_699,B_698)))
      | ~ v1_funct_1(C_700) ) ),
    inference(resolution,[status(thm)],[c_36,c_6979])).

tff(c_9131,plain,(
    ! [E_721,B_722,A_723,C_724] :
      ( '#skF_6'(E_721,B_722,k5_partfun1(A_723,B_722,C_724),A_723,C_724) = C_724
      | ~ v1_partfun1(C_724,A_723)
      | ~ v1_funct_1('#skF_6'(E_721,B_722,k5_partfun1(A_723,B_722,C_724),A_723,C_724))
      | ~ r2_hidden(E_721,k5_partfun1(A_723,B_722,C_724))
      | ~ m1_subset_1(C_724,k1_zfmisc_1(k2_zfmisc_1(A_723,B_722)))
      | ~ v1_funct_1(C_724) ) ),
    inference(resolution,[status(thm)],[c_32,c_8697])).

tff(c_9139,plain,(
    ! [E_721] :
      ( '#skF_6'(E_721,k1_tarski('#skF_8'),k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10'),'#skF_7','#skF_10') = '#skF_10'
      | ~ v1_partfun1('#skF_10','#skF_7')
      | ~ v1_funct_1('#skF_6'(E_721,k1_tarski('#skF_8'),k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9'),'#skF_7','#skF_10'))
      | ~ r2_hidden(E_721,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10'))
      | ~ m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
      | ~ v1_funct_1('#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2395,c_9131])).

tff(c_9780,plain,(
    ! [E_741] :
      ( '#skF_6'(E_741,k1_tarski('#skF_8'),k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9'),'#skF_7','#skF_10') = '#skF_10'
      | ~ v1_funct_1('#skF_6'(E_741,k1_tarski('#skF_8'),k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9'),'#skF_7','#skF_10'))
      | ~ r2_hidden(E_741,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_74,c_2395,c_190,c_2395,c_9139])).

tff(c_9797,plain,(
    ! [E_745] :
      ( '#skF_6'(E_745,k1_tarski('#skF_8'),k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9'),'#skF_7','#skF_10') = '#skF_10'
      | ~ r2_hidden(E_745,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_2430,c_9780])).

tff(c_258,plain,(
    ! [E_106,B_107,A_108,C_109] :
      ( '#skF_6'(E_106,B_107,k5_partfun1(A_108,B_107,C_109),A_108,C_109) = E_106
      | ~ r2_hidden(E_106,k5_partfun1(A_108,B_107,C_109))
      | ~ m1_subset_1(C_109,k1_zfmisc_1(k2_zfmisc_1(A_108,B_107)))
      | ~ v1_funct_1(C_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_266,plain,(
    ! [A_1,A_108,B_107,C_109] :
      ( '#skF_6'('#skF_2'(A_1,k5_partfun1(A_108,B_107,C_109)),B_107,k5_partfun1(A_108,B_107,C_109),A_108,C_109) = '#skF_2'(A_1,k5_partfun1(A_108,B_107,C_109))
      | ~ m1_subset_1(C_109,k1_zfmisc_1(k2_zfmisc_1(A_108,B_107)))
      | ~ v1_funct_1(C_109)
      | '#skF_1'(A_1,k5_partfun1(A_108,B_107,C_109)) = A_1
      | k5_partfun1(A_108,B_107,C_109) = k1_tarski(A_1) ) ),
    inference(resolution,[status(thm)],[c_12,c_258])).

tff(c_2457,plain,(
    ! [A_1] :
      ( '#skF_6'('#skF_2'(A_1,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')),k1_tarski('#skF_8'),k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9'),'#skF_7','#skF_10') = '#skF_2'(A_1,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10'))
      | ~ m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
      | ~ v1_funct_1('#skF_10')
      | '#skF_1'(A_1,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')) = A_1
      | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10') = k1_tarski(A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2395,c_266])).

tff(c_2494,plain,(
    ! [A_1] :
      ( '#skF_6'('#skF_2'(A_1,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')),k1_tarski('#skF_8'),k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9'),'#skF_7','#skF_10') = '#skF_2'(A_1,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9'))
      | '#skF_1'(A_1,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')) = A_1
      | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') = k1_tarski(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2395,c_2395,c_78,c_74,c_2395,c_2395,c_2457])).

tff(c_10129,plain,(
    ! [A_749] :
      ( '#skF_2'(A_749,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')) = '#skF_10'
      | '#skF_1'(A_749,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')) = A_749
      | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') = k1_tarski(A_749)
      | ~ r2_hidden('#skF_2'(A_749,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')),k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9797,c_2494])).

tff(c_10141,plain,(
    ! [A_750] :
      ( '#skF_2'(A_750,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')) = '#skF_10'
      | '#skF_1'(A_750,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')) = A_750
      | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') = k1_tarski(A_750) ) ),
    inference(resolution,[status(thm)],[c_12,c_10129])).

tff(c_8,plain,(
    ! [A_1,B_2] :
      ( '#skF_1'(A_1,B_2) = A_1
      | '#skF_2'(A_1,B_2) != A_1
      | k1_tarski(A_1) = B_2 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_10185,plain,(
    ! [A_750] :
      ( '#skF_1'(A_750,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')) = A_750
      | A_750 != '#skF_10'
      | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') = k1_tarski(A_750)
      | '#skF_1'(A_750,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')) = A_750
      | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') = k1_tarski(A_750) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10141,c_8])).

tff(c_10242,plain,(
    ! [A_752] :
      ( A_752 != '#skF_10'
      | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') = k1_tarski(A_752)
      | '#skF_1'(A_752,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')) = A_752 ) ),
    inference(factorization,[status(thm),theory(equality)],[c_10185])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | '#skF_2'(A_1,B_2) != A_1
      | k1_tarski(A_1) = B_2 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_10272,plain,(
    ! [A_756] :
      ( ~ r2_hidden(A_756,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9'))
      | '#skF_2'(A_756,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')) != A_756
      | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') = k1_tarski(A_756)
      | A_756 != '#skF_10'
      | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') = k1_tarski(A_756) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10242,c_6])).

tff(c_10459,plain,
    ( '#skF_2'('#skF_10',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')) != '#skF_10'
    | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') = k1_tarski('#skF_10') ),
    inference(resolution,[status(thm)],[c_736,c_10272])).

tff(c_10580,plain,(
    '#skF_2'('#skF_10',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')) != '#skF_10' ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_72,c_10459])).

tff(c_10139,plain,(
    ! [A_1] :
      ( '#skF_2'(A_1,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')) = '#skF_10'
      | '#skF_1'(A_1,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')) = A_1
      | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') = k1_tarski(A_1) ) ),
    inference(resolution,[status(thm)],[c_12,c_10129])).

tff(c_10601,plain,
    ( '#skF_1'('#skF_10',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')) = '#skF_10'
    | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') = k1_tarski('#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_10139,c_10580])).

tff(c_10604,plain,(
    '#skF_1'('#skF_10',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')) = '#skF_10' ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_10601])).

tff(c_10,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r2_hidden('#skF_2'(A_1,B_2),B_2)
      | k1_tarski(A_1) = B_2 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_265,plain,(
    ! [A_1,A_108,B_107,C_109] :
      ( '#skF_6'('#skF_2'(A_1,k5_partfun1(A_108,B_107,C_109)),B_107,k5_partfun1(A_108,B_107,C_109),A_108,C_109) = '#skF_2'(A_1,k5_partfun1(A_108,B_107,C_109))
      | ~ m1_subset_1(C_109,k1_zfmisc_1(k2_zfmisc_1(A_108,B_107)))
      | ~ v1_funct_1(C_109)
      | ~ r2_hidden('#skF_1'(A_1,k5_partfun1(A_108,B_107,C_109)),k5_partfun1(A_108,B_107,C_109))
      | k5_partfun1(A_108,B_107,C_109) = k1_tarski(A_1) ) ),
    inference(resolution,[status(thm)],[c_10,c_258])).

tff(c_10622,plain,
    ( '#skF_6'('#skF_2'('#skF_10',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')),k1_tarski('#skF_8'),k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9'),'#skF_7','#skF_9') = '#skF_2'('#skF_10',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9'))
    | ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
    | ~ v1_funct_1('#skF_9')
    | ~ r2_hidden('#skF_10',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9'))
    | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') = k1_tarski('#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_10604,c_265])).

tff(c_10648,plain,
    ( '#skF_6'('#skF_2'('#skF_10',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')),k1_tarski('#skF_8'),k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9'),'#skF_7','#skF_9') = '#skF_2'('#skF_10',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9'))
    | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') = k1_tarski('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_736,c_82,c_80,c_10622])).

tff(c_10649,plain,(
    '#skF_6'('#skF_2'('#skF_10',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')),k1_tarski('#skF_8'),k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9'),'#skF_7','#skF_9') = '#skF_2'('#skF_10',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_10648])).

tff(c_272,plain,(
    ! [E_112] :
      ( v1_funct_1('#skF_6'(E_112,k1_tarski('#skF_8'),k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9'),'#skF_7','#skF_9'))
      | ~ r2_hidden(E_112,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9'))
      | ~ v1_funct_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_80,c_268])).

tff(c_282,plain,(
    ! [E_112] :
      ( v1_funct_1('#skF_6'(E_112,k1_tarski('#skF_8'),k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9'),'#skF_7','#skF_9'))
      | ~ r2_hidden(E_112,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_272])).

tff(c_10765,plain,
    ( v1_funct_1('#skF_2'('#skF_10',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')))
    | ~ r2_hidden('#skF_2'('#skF_10',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')),k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')) ),
    inference(superposition,[status(thm),theory(equality)],[c_10649,c_282])).

tff(c_10856,plain,(
    ~ r2_hidden('#skF_2'('#skF_10',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')),k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')) ),
    inference(splitLeft,[status(thm)],[c_10765])).

tff(c_10862,plain,
    ( ~ r2_hidden('#skF_1'('#skF_10',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')),k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9'))
    | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') = k1_tarski('#skF_10') ),
    inference(resolution,[status(thm)],[c_10,c_10856])).

tff(c_10871,plain,(
    k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') = k1_tarski('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_736,c_10604,c_10862])).

tff(c_10873,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_10871])).

tff(c_10875,plain,(
    r2_hidden('#skF_2'('#skF_10',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')),k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')) ),
    inference(splitRight,[status(thm)],[c_10765])).

tff(c_2474,plain,(
    ! [E_51] :
      ( '#skF_6'(E_51,k1_tarski('#skF_8'),k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10'),'#skF_7','#skF_10') = E_51
      | ~ r2_hidden(E_51,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9'))
      | ~ m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
      | ~ v1_funct_1('#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2395,c_34])).

tff(c_2506,plain,(
    ! [E_51] :
      ( '#skF_6'(E_51,k1_tarski('#skF_8'),k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9'),'#skF_7','#skF_10') = E_51
      | ~ r2_hidden(E_51,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_74,c_2395,c_2474])).

tff(c_9824,plain,(
    ! [E_745] :
      ( E_745 = '#skF_10'
      | ~ r2_hidden(E_745,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9'))
      | ~ r2_hidden(E_745,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9797,c_2506])).

tff(c_10910,plain,
    ( '#skF_2'('#skF_10',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')) = '#skF_10'
    | ~ r2_hidden('#skF_2'('#skF_10',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')),k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')) ),
    inference(resolution,[status(thm)],[c_10875,c_9824])).

tff(c_10947,plain,(
    '#skF_2'('#skF_10',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')) = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10875,c_10910])).

tff(c_10949,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10580,c_10947])).

tff(c_10951,plain,(
    k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10') != k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') ),
    inference(splitRight,[status(thm)],[c_2394])).

tff(c_747,plain,(
    ! [A_232,B_233,C_234,D_235] :
      ( '#skF_4'(A_232,B_233,C_234,D_235) = '#skF_3'(A_232,B_233,C_234,D_235)
      | r2_hidden('#skF_5'(A_232,B_233,C_234,D_235),D_235)
      | k5_partfun1(A_232,B_233,C_234) = D_235
      | ~ m1_subset_1(C_234,k1_zfmisc_1(k2_zfmisc_1(A_232,B_233)))
      | ~ v1_funct_1(C_234) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_753,plain,(
    ! [D_235] :
      ( '#skF_4'('#skF_7',k1_tarski('#skF_8'),'#skF_9',D_235) = '#skF_3'('#skF_7',k1_tarski('#skF_8'),'#skF_9',D_235)
      | r2_hidden('#skF_5'('#skF_7',k1_tarski('#skF_8'),'#skF_9',D_235),D_235)
      | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') = D_235
      | ~ v1_funct_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_80,c_747])).

tff(c_764,plain,(
    ! [D_235] :
      ( '#skF_4'('#skF_7',k1_tarski('#skF_8'),'#skF_9',D_235) = '#skF_3'('#skF_7',k1_tarski('#skF_8'),'#skF_9',D_235)
      | r2_hidden('#skF_5'('#skF_7',k1_tarski('#skF_8'),'#skF_9',D_235),D_235)
      | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') = D_235 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_753])).

tff(c_2390,plain,
    ( '#skF_4'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')) = '#skF_3'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10'))
    | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10') = k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') ),
    inference(resolution,[status(thm)],[c_764,c_2355])).

tff(c_10990,plain,(
    '#skF_4'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')) = '#skF_3'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')) ),
    inference(negUnitSimplification,[status(thm)],[c_10951,c_2390])).

tff(c_10950,plain,(
    v1_funct_1('#skF_4'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10'))) ),
    inference(splitRight,[status(thm)],[c_2394])).

tff(c_10993,plain,(
    v1_funct_1('#skF_3'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10990,c_10950])).

tff(c_884,plain,(
    ! [A_253,B_254,C_255,D_256] :
      ( m1_subset_1('#skF_4'(A_253,B_254,C_255,D_256),k1_zfmisc_1(k2_zfmisc_1(A_253,B_254)))
      | r2_hidden('#skF_5'(A_253,B_254,C_255,D_256),D_256)
      | k5_partfun1(A_253,B_254,C_255) = D_256
      | ~ m1_subset_1(C_255,k1_zfmisc_1(k2_zfmisc_1(A_253,B_254)))
      | ~ v1_funct_1(C_255) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_68,plain,(
    ! [C_60,D_62,A_58,B_59] :
      ( r1_partfun1(C_60,D_62)
      | ~ m1_subset_1(D_62,k1_zfmisc_1(k2_zfmisc_1(A_58,k1_tarski(B_59))))
      | ~ v1_funct_1(D_62)
      | ~ m1_subset_1(C_60,k1_zfmisc_1(k2_zfmisc_1(A_58,k1_tarski(B_59))))
      | ~ v1_funct_1(C_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_1934,plain,(
    ! [C_431,A_433,D_432,C_434,B_430] :
      ( r1_partfun1(C_434,'#skF_4'(A_433,k1_tarski(B_430),C_431,D_432))
      | ~ v1_funct_1('#skF_4'(A_433,k1_tarski(B_430),C_431,D_432))
      | ~ m1_subset_1(C_434,k1_zfmisc_1(k2_zfmisc_1(A_433,k1_tarski(B_430))))
      | ~ v1_funct_1(C_434)
      | r2_hidden('#skF_5'(A_433,k1_tarski(B_430),C_431,D_432),D_432)
      | k5_partfun1(A_433,k1_tarski(B_430),C_431) = D_432
      | ~ m1_subset_1(C_431,k1_zfmisc_1(k2_zfmisc_1(A_433,k1_tarski(B_430))))
      | ~ v1_funct_1(C_431) ) ),
    inference(resolution,[status(thm)],[c_884,c_68])).

tff(c_1949,plain,(
    ! [C_431,D_432] :
      ( r1_partfun1('#skF_10','#skF_4'('#skF_7',k1_tarski('#skF_8'),C_431,D_432))
      | ~ v1_funct_1('#skF_4'('#skF_7',k1_tarski('#skF_8'),C_431,D_432))
      | ~ v1_funct_1('#skF_10')
      | r2_hidden('#skF_5'('#skF_7',k1_tarski('#skF_8'),C_431,D_432),D_432)
      | k5_partfun1('#skF_7',k1_tarski('#skF_8'),C_431) = D_432
      | ~ m1_subset_1(C_431,k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
      | ~ v1_funct_1(C_431) ) ),
    inference(resolution,[status(thm)],[c_74,c_1934])).

tff(c_1967,plain,(
    ! [C_435,D_436] :
      ( r1_partfun1('#skF_10','#skF_4'('#skF_7',k1_tarski('#skF_8'),C_435,D_436))
      | ~ v1_funct_1('#skF_4'('#skF_7',k1_tarski('#skF_8'),C_435,D_436))
      | r2_hidden('#skF_5'('#skF_7',k1_tarski('#skF_8'),C_435,D_436),D_436)
      | k5_partfun1('#skF_7',k1_tarski('#skF_8'),C_435) = D_436
      | ~ m1_subset_1(C_435,k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
      | ~ v1_funct_1(C_435) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_1949])).

tff(c_1984,plain,(
    ! [D_436] :
      ( r1_partfun1('#skF_10','#skF_4'('#skF_7',k1_tarski('#skF_8'),'#skF_9',D_436))
      | ~ v1_funct_1('#skF_4'('#skF_7',k1_tarski('#skF_8'),'#skF_9',D_436))
      | r2_hidden('#skF_5'('#skF_7',k1_tarski('#skF_8'),'#skF_9',D_436),D_436)
      | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') = D_436
      | ~ v1_funct_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_80,c_1967])).

tff(c_1995,plain,(
    ! [D_436] :
      ( r1_partfun1('#skF_10','#skF_4'('#skF_7',k1_tarski('#skF_8'),'#skF_9',D_436))
      | ~ v1_funct_1('#skF_4'('#skF_7',k1_tarski('#skF_8'),'#skF_9',D_436))
      | r2_hidden('#skF_5'('#skF_7',k1_tarski('#skF_8'),'#skF_9',D_436),D_436)
      | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') = D_436 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_1984])).

tff(c_2384,plain,
    ( r1_partfun1('#skF_10','#skF_4'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')))
    | ~ v1_funct_1('#skF_4'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')))
    | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10') = k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') ),
    inference(resolution,[status(thm)],[c_1995,c_2355])).

tff(c_11025,plain,
    ( r1_partfun1('#skF_10','#skF_3'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')))
    | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10') = k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10993,c_10990,c_10990,c_2384])).

tff(c_11026,plain,(
    r1_partfun1('#skF_10','#skF_3'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10'))) ),
    inference(negUnitSimplification,[status(thm)],[c_10951,c_11025])).

tff(c_558,plain,(
    ! [A_186,B_187,C_188,D_189] :
      ( v1_partfun1('#skF_4'(A_186,B_187,C_188,D_189),A_186)
      | r2_hidden('#skF_5'(A_186,B_187,C_188,D_189),D_189)
      | k5_partfun1(A_186,B_187,C_188) = D_189
      | ~ m1_subset_1(C_188,k1_zfmisc_1(k2_zfmisc_1(A_186,B_187)))
      | ~ v1_funct_1(C_188) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_562,plain,(
    ! [D_189] :
      ( v1_partfun1('#skF_4'('#skF_7',k1_tarski('#skF_8'),'#skF_9',D_189),'#skF_7')
      | r2_hidden('#skF_5'('#skF_7',k1_tarski('#skF_8'),'#skF_9',D_189),D_189)
      | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') = D_189
      | ~ v1_funct_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_80,c_558])).

tff(c_572,plain,(
    ! [D_189] :
      ( v1_partfun1('#skF_4'('#skF_7',k1_tarski('#skF_8'),'#skF_9',D_189),'#skF_7')
      | r2_hidden('#skF_5'('#skF_7',k1_tarski('#skF_8'),'#skF_9',D_189),D_189)
      | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') = D_189 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_562])).

tff(c_2391,plain,
    ( v1_partfun1('#skF_4'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')),'#skF_7')
    | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10') = k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') ),
    inference(resolution,[status(thm)],[c_572,c_2355])).

tff(c_10952,plain,(
    v1_partfun1('#skF_4'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_10951,c_2391])).

tff(c_10992,plain,(
    v1_partfun1('#skF_3'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10990,c_10952])).

tff(c_60,plain,(
    ! [A_13,B_14,C_15,D_37] :
      ( m1_subset_1('#skF_4'(A_13,B_14,C_15,D_37),k1_zfmisc_1(k2_zfmisc_1(A_13,B_14)))
      | r2_hidden('#skF_5'(A_13,B_14,C_15,D_37),D_37)
      | k5_partfun1(A_13,B_14,C_15) = D_37
      | ~ m1_subset_1(C_15,k1_zfmisc_1(k2_zfmisc_1(A_13,B_14)))
      | ~ v1_funct_1(C_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_11007,plain,
    ( m1_subset_1('#skF_3'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')),k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
    | r2_hidden('#skF_5'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')),k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10'))
    | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10') = k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')
    | ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
    | ~ v1_funct_1('#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_10990,c_60])).

tff(c_11021,plain,
    ( m1_subset_1('#skF_3'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')),k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
    | r2_hidden('#skF_5'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')),k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10'))
    | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10') = k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_11007])).

tff(c_11022,plain,(
    m1_subset_1('#skF_3'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')),k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8')))) ),
    inference(negUnitSimplification,[status(thm)],[c_10951,c_2355,c_11021])).

tff(c_28,plain,(
    ! [F_54,A_13,B_14,C_15] :
      ( r2_hidden(F_54,k5_partfun1(A_13,B_14,C_15))
      | ~ r1_partfun1(C_15,F_54)
      | ~ v1_partfun1(F_54,A_13)
      | ~ m1_subset_1(F_54,k1_zfmisc_1(k2_zfmisc_1(A_13,B_14)))
      | ~ v1_funct_1(F_54)
      | ~ m1_subset_1(C_15,k1_zfmisc_1(k2_zfmisc_1(A_13,B_14)))
      | ~ v1_funct_1(C_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_11053,plain,(
    ! [C_15] :
      ( r2_hidden('#skF_3'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')),k5_partfun1('#skF_7',k1_tarski('#skF_8'),C_15))
      | ~ r1_partfun1(C_15,'#skF_3'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')))
      | ~ v1_partfun1('#skF_3'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')),'#skF_7')
      | ~ v1_funct_1('#skF_3'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')))
      | ~ m1_subset_1(C_15,k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
      | ~ v1_funct_1(C_15) ) ),
    inference(resolution,[status(thm)],[c_11022,c_28])).

tff(c_11242,plain,(
    ! [C_774] :
      ( r2_hidden('#skF_3'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')),k5_partfun1('#skF_7',k1_tarski('#skF_8'),C_774))
      | ~ r1_partfun1(C_774,'#skF_3'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')))
      | ~ m1_subset_1(C_774,k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
      | ~ v1_funct_1(C_774) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10993,c_10992,c_11053])).

tff(c_382,plain,(
    ! [A_153,B_154,C_155,D_156] :
      ( ~ r2_hidden('#skF_3'(A_153,B_154,C_155,D_156),D_156)
      | r2_hidden('#skF_5'(A_153,B_154,C_155,D_156),D_156)
      | k5_partfun1(A_153,B_154,C_155) = D_156
      | ~ m1_subset_1(C_155,k1_zfmisc_1(k2_zfmisc_1(A_153,B_154)))
      | ~ v1_funct_1(C_155) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_386,plain,(
    ! [D_156] :
      ( ~ r2_hidden('#skF_3'('#skF_7',k1_tarski('#skF_8'),'#skF_9',D_156),D_156)
      | r2_hidden('#skF_5'('#skF_7',k1_tarski('#skF_8'),'#skF_9',D_156),D_156)
      | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') = D_156
      | ~ v1_funct_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_80,c_382])).

tff(c_396,plain,(
    ! [D_156] :
      ( ~ r2_hidden('#skF_3'('#skF_7',k1_tarski('#skF_8'),'#skF_9',D_156),D_156)
      | r2_hidden('#skF_5'('#skF_7',k1_tarski('#skF_8'),'#skF_9',D_156),D_156)
      | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') = D_156 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_386])).

tff(c_2392,plain,
    ( ~ r2_hidden('#skF_3'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')),k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10'))
    | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10') = k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') ),
    inference(resolution,[status(thm)],[c_396,c_2355])).

tff(c_10989,plain,(
    ~ r2_hidden('#skF_3'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')),k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')) ),
    inference(negUnitSimplification,[status(thm)],[c_10951,c_2392])).

tff(c_11245,plain,
    ( ~ r1_partfun1('#skF_10','#skF_3'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')))
    | ~ m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
    | ~ v1_funct_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_11242,c_10989])).

tff(c_11254,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_74,c_11026,c_11245])).

tff(c_11256,plain,(
    r2_hidden('#skF_5'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')),k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')) ),
    inference(splitRight,[status(thm)],[c_2184])).

tff(c_11258,plain,
    ( '#skF_6'('#skF_5'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')),k1_tarski('#skF_8'),k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10'),'#skF_7','#skF_10') = '#skF_5'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10'))
    | ~ m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
    | ~ v1_funct_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_11256,c_34])).

tff(c_11261,plain,(
    '#skF_6'('#skF_5'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')),k1_tarski('#skF_8'),k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10'),'#skF_7','#skF_10') = '#skF_5'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_74,c_11258])).

tff(c_11286,plain,
    ( v1_funct_1('#skF_5'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')))
    | ~ r2_hidden('#skF_5'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')),k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')) ),
    inference(superposition,[status(thm),theory(equality)],[c_11261,c_279])).

tff(c_11308,plain,(
    v1_funct_1('#skF_5'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11256,c_11286])).

tff(c_11277,plain,
    ( m1_subset_1('#skF_5'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')),k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
    | ~ r2_hidden('#skF_5'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')),k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10'))
    | ~ m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
    | ~ v1_funct_1('#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_11261,c_36])).

tff(c_11302,plain,(
    m1_subset_1('#skF_5'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')),k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_74,c_11256,c_11277])).

tff(c_11280,plain,
    ( v1_partfun1('#skF_5'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')),'#skF_7')
    | ~ r2_hidden('#skF_5'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')),k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10'))
    | ~ m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
    | ~ v1_funct_1('#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_11261,c_32])).

tff(c_11304,plain,(
    v1_partfun1('#skF_5'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_74,c_11256,c_11280])).

tff(c_11383,plain,(
    ! [C_60] :
      ( r1_partfun1(C_60,'#skF_5'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')))
      | ~ v1_funct_1('#skF_5'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')))
      | ~ m1_subset_1(C_60,k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
      | ~ v1_funct_1(C_60) ) ),
    inference(resolution,[status(thm)],[c_11302,c_68])).

tff(c_11545,plain,(
    ! [C_783] :
      ( r1_partfun1(C_783,'#skF_5'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')))
      | ~ m1_subset_1(C_783,k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
      | ~ v1_funct_1(C_783) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11308,c_11383])).

tff(c_50,plain,(
    ! [A_13,B_14,C_15,D_37] :
      ( v1_funct_1('#skF_4'(A_13,B_14,C_15,D_37))
      | ~ r1_partfun1(C_15,'#skF_5'(A_13,B_14,C_15,D_37))
      | ~ v1_partfun1('#skF_5'(A_13,B_14,C_15,D_37),A_13)
      | ~ m1_subset_1('#skF_5'(A_13,B_14,C_15,D_37),k1_zfmisc_1(k2_zfmisc_1(A_13,B_14)))
      | ~ v1_funct_1('#skF_5'(A_13,B_14,C_15,D_37))
      | k5_partfun1(A_13,B_14,C_15) = D_37
      | ~ m1_subset_1(C_15,k1_zfmisc_1(k2_zfmisc_1(A_13,B_14)))
      | ~ v1_funct_1(C_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_11557,plain,
    ( v1_funct_1('#skF_4'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')))
    | ~ v1_partfun1('#skF_5'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')),'#skF_7')
    | ~ m1_subset_1('#skF_5'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')),k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
    | ~ v1_funct_1('#skF_5'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')))
    | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10') = k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')
    | ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
    | ~ v1_funct_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_11545,c_50])).

tff(c_11571,plain,
    ( v1_funct_1('#skF_4'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')))
    | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10') = k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_11308,c_11302,c_11304,c_11557])).

tff(c_11575,plain,(
    k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10') = k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') ),
    inference(splitLeft,[status(thm)],[c_11571])).

tff(c_11619,plain,(
    ! [E_112] :
      ( v1_funct_1('#skF_6'(E_112,k1_tarski('#skF_8'),k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9'),'#skF_7','#skF_10'))
      | ~ r2_hidden(E_112,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11575,c_11575,c_279])).

tff(c_16799,plain,(
    ! [C_915,A_914,B_913,B_911,E_910,A_912] :
      ( '#skF_6'(E_910,B_911,k5_partfun1(A_914,B_911,C_915),A_914,C_915) = C_915
      | ~ v1_partfun1('#skF_6'(E_910,B_911,k5_partfun1(A_914,B_911,C_915),A_914,C_915),A_912)
      | ~ v1_partfun1(C_915,A_912)
      | ~ m1_subset_1('#skF_6'(E_910,B_911,k5_partfun1(A_914,B_911,C_915),A_914,C_915),k1_zfmisc_1(k2_zfmisc_1(A_912,B_913)))
      | ~ v1_funct_1('#skF_6'(E_910,B_911,k5_partfun1(A_914,B_911,C_915),A_914,C_915))
      | ~ m1_subset_1(C_915,k1_zfmisc_1(k2_zfmisc_1(A_912,B_913)))
      | ~ r2_hidden(E_910,k5_partfun1(A_914,B_911,C_915))
      | ~ m1_subset_1(C_915,k1_zfmisc_1(k2_zfmisc_1(A_914,B_911)))
      | ~ v1_funct_1(C_915) ) ),
    inference(resolution,[status(thm)],[c_30,c_460])).

tff(c_17289,plain,(
    ! [E_955,B_956,A_957,C_958] :
      ( '#skF_6'(E_955,B_956,k5_partfun1(A_957,B_956,C_958),A_957,C_958) = C_958
      | ~ v1_partfun1('#skF_6'(E_955,B_956,k5_partfun1(A_957,B_956,C_958),A_957,C_958),A_957)
      | ~ v1_partfun1(C_958,A_957)
      | ~ v1_funct_1('#skF_6'(E_955,B_956,k5_partfun1(A_957,B_956,C_958),A_957,C_958))
      | ~ r2_hidden(E_955,k5_partfun1(A_957,B_956,C_958))
      | ~ m1_subset_1(C_958,k1_zfmisc_1(k2_zfmisc_1(A_957,B_956)))
      | ~ v1_funct_1(C_958) ) ),
    inference(resolution,[status(thm)],[c_36,c_16799])).

tff(c_17464,plain,(
    ! [E_959,B_960,A_961,C_962] :
      ( '#skF_6'(E_959,B_960,k5_partfun1(A_961,B_960,C_962),A_961,C_962) = C_962
      | ~ v1_partfun1(C_962,A_961)
      | ~ v1_funct_1('#skF_6'(E_959,B_960,k5_partfun1(A_961,B_960,C_962),A_961,C_962))
      | ~ r2_hidden(E_959,k5_partfun1(A_961,B_960,C_962))
      | ~ m1_subset_1(C_962,k1_zfmisc_1(k2_zfmisc_1(A_961,B_960)))
      | ~ v1_funct_1(C_962) ) ),
    inference(resolution,[status(thm)],[c_32,c_17289])).

tff(c_17472,plain,(
    ! [E_959] :
      ( '#skF_6'(E_959,k1_tarski('#skF_8'),k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10'),'#skF_7','#skF_10') = '#skF_10'
      | ~ v1_partfun1('#skF_10','#skF_7')
      | ~ v1_funct_1('#skF_6'(E_959,k1_tarski('#skF_8'),k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9'),'#skF_7','#skF_10'))
      | ~ r2_hidden(E_959,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10'))
      | ~ m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
      | ~ v1_funct_1('#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11575,c_17464])).

tff(c_18100,plain,(
    ! [E_982] :
      ( '#skF_6'(E_982,k1_tarski('#skF_8'),k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9'),'#skF_7','#skF_10') = '#skF_10'
      | ~ v1_funct_1('#skF_6'(E_982,k1_tarski('#skF_8'),k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9'),'#skF_7','#skF_10'))
      | ~ r2_hidden(E_982,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_74,c_11575,c_190,c_11575,c_17472])).

tff(c_18113,plain,(
    ! [E_983] :
      ( '#skF_6'(E_983,k1_tarski('#skF_8'),k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9'),'#skF_7','#skF_10') = '#skF_10'
      | ~ r2_hidden(E_983,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_11619,c_18100])).

tff(c_11663,plain,(
    ! [E_51] :
      ( '#skF_6'(E_51,k1_tarski('#skF_8'),k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10'),'#skF_7','#skF_10') = E_51
      | ~ r2_hidden(E_51,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9'))
      | ~ m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
      | ~ v1_funct_1('#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11575,c_34])).

tff(c_11695,plain,(
    ! [E_51] :
      ( '#skF_6'(E_51,k1_tarski('#skF_8'),k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9'),'#skF_7','#skF_10') = E_51
      | ~ r2_hidden(E_51,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_74,c_11575,c_11663])).

tff(c_18164,plain,(
    ! [E_984] :
      ( E_984 = '#skF_10'
      | ~ r2_hidden(E_984,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9'))
      | ~ r2_hidden(E_984,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18113,c_11695])).

tff(c_18506,plain,(
    ! [A_987] :
      ( '#skF_2'(A_987,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')) = '#skF_10'
      | ~ r2_hidden('#skF_2'(A_987,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')),k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9'))
      | '#skF_1'(A_987,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')) = A_987
      | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') = k1_tarski(A_987) ) ),
    inference(resolution,[status(thm)],[c_12,c_18164])).

tff(c_18518,plain,(
    ! [A_988] :
      ( '#skF_2'(A_988,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')) = '#skF_10'
      | '#skF_1'(A_988,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')) = A_988
      | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') = k1_tarski(A_988) ) ),
    inference(resolution,[status(thm)],[c_12,c_18506])).

tff(c_18556,plain,(
    ! [A_988] :
      ( '#skF_1'(A_988,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')) = A_988
      | A_988 != '#skF_10'
      | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') = k1_tarski(A_988)
      | '#skF_1'(A_988,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')) = A_988
      | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') = k1_tarski(A_988) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18518,c_8])).

tff(c_18613,plain,(
    ! [A_993] :
      ( A_993 != '#skF_10'
      | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') = k1_tarski(A_993)
      | '#skF_1'(A_993,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')) = A_993 ) ),
    inference(factorization,[status(thm),theory(equality)],[c_18556])).

tff(c_18642,plain,(
    ! [A_994] :
      ( ~ r2_hidden(A_994,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9'))
      | '#skF_2'(A_994,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')) != A_994
      | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') = k1_tarski(A_994)
      | A_994 != '#skF_10'
      | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') = k1_tarski(A_994) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18613,c_6])).

tff(c_18821,plain,
    ( '#skF_2'('#skF_10',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')) != '#skF_10'
    | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') = k1_tarski('#skF_10') ),
    inference(resolution,[status(thm)],[c_736,c_18642])).

tff(c_18952,plain,(
    '#skF_2'('#skF_10',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')) != '#skF_10' ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_72,c_18821])).

tff(c_18516,plain,(
    ! [A_1] :
      ( '#skF_2'(A_1,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')) = '#skF_10'
      | '#skF_1'(A_1,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')) = A_1
      | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') = k1_tarski(A_1) ) ),
    inference(resolution,[status(thm)],[c_12,c_18506])).

tff(c_18985,plain,
    ( '#skF_1'('#skF_10',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')) = '#skF_10'
    | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') = k1_tarski('#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_18516,c_18952])).

tff(c_18988,plain,(
    '#skF_1'('#skF_10',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')) = '#skF_10' ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_18985])).

tff(c_19006,plain,
    ( '#skF_6'('#skF_2'('#skF_10',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')),k1_tarski('#skF_8'),k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9'),'#skF_7','#skF_9') = '#skF_2'('#skF_10',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9'))
    | ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
    | ~ v1_funct_1('#skF_9')
    | ~ r2_hidden('#skF_10',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9'))
    | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') = k1_tarski('#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_18988,c_265])).

tff(c_19032,plain,
    ( '#skF_6'('#skF_2'('#skF_10',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')),k1_tarski('#skF_8'),k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9'),'#skF_7','#skF_9') = '#skF_2'('#skF_10',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9'))
    | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') = k1_tarski('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_736,c_82,c_80,c_19006])).

tff(c_19033,plain,(
    '#skF_6'('#skF_2'('#skF_10',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')),k1_tarski('#skF_8'),k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9'),'#skF_7','#skF_9') = '#skF_2'('#skF_10',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_19032])).

tff(c_19356,plain,
    ( v1_partfun1('#skF_2'('#skF_10',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')),'#skF_7')
    | ~ r2_hidden('#skF_2'('#skF_10',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')),k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9'))
    | ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
    | ~ v1_funct_1('#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_19033,c_32])).

tff(c_19412,plain,
    ( v1_partfun1('#skF_2'('#skF_10',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')),'#skF_7')
    | ~ r2_hidden('#skF_2'('#skF_10',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')),k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_19356])).

tff(c_19423,plain,(
    ~ r2_hidden('#skF_2'('#skF_10',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')),k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')) ),
    inference(splitLeft,[status(thm)],[c_19412])).

tff(c_19450,plain,
    ( ~ r2_hidden('#skF_1'('#skF_10',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')),k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9'))
    | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') = k1_tarski('#skF_10') ),
    inference(resolution,[status(thm)],[c_10,c_19423])).

tff(c_19459,plain,(
    k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') = k1_tarski('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_736,c_18988,c_19450])).

tff(c_19461,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_19459])).

tff(c_19463,plain,(
    r2_hidden('#skF_2'('#skF_10',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')),k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')) ),
    inference(splitRight,[status(thm)],[c_19412])).

tff(c_18134,plain,(
    ! [E_983] :
      ( E_983 = '#skF_10'
      | ~ r2_hidden(E_983,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9'))
      | ~ r2_hidden(E_983,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18113,c_11695])).

tff(c_19475,plain,
    ( '#skF_2'('#skF_10',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')) = '#skF_10'
    | ~ r2_hidden('#skF_2'('#skF_10',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')),k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')) ),
    inference(resolution,[status(thm)],[c_19463,c_18134])).

tff(c_19512,plain,(
    '#skF_2'('#skF_10',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')) = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_19463,c_19475])).

tff(c_19514,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18952,c_19512])).

tff(c_19516,plain,(
    k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10') != k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') ),
    inference(splitRight,[status(thm)],[c_11571])).

tff(c_46,plain,(
    ! [A_13,B_14,C_15,D_37] :
      ( '#skF_4'(A_13,B_14,C_15,D_37) = '#skF_3'(A_13,B_14,C_15,D_37)
      | ~ r1_partfun1(C_15,'#skF_5'(A_13,B_14,C_15,D_37))
      | ~ v1_partfun1('#skF_5'(A_13,B_14,C_15,D_37),A_13)
      | ~ m1_subset_1('#skF_5'(A_13,B_14,C_15,D_37),k1_zfmisc_1(k2_zfmisc_1(A_13,B_14)))
      | ~ v1_funct_1('#skF_5'(A_13,B_14,C_15,D_37))
      | k5_partfun1(A_13,B_14,C_15) = D_37
      | ~ m1_subset_1(C_15,k1_zfmisc_1(k2_zfmisc_1(A_13,B_14)))
      | ~ v1_funct_1(C_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_11551,plain,
    ( '#skF_4'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')) = '#skF_3'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10'))
    | ~ v1_partfun1('#skF_5'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')),'#skF_7')
    | ~ m1_subset_1('#skF_5'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')),k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
    | ~ v1_funct_1('#skF_5'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')))
    | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10') = k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')
    | ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
    | ~ v1_funct_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_11545,c_46])).

tff(c_11565,plain,
    ( '#skF_4'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')) = '#skF_3'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10'))
    | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10') = k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_11308,c_11302,c_11304,c_11551])).

tff(c_19811,plain,(
    '#skF_4'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')) = '#skF_3'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')) ),
    inference(negUnitSimplification,[status(thm)],[c_19516,c_11565])).

tff(c_19515,plain,(
    v1_funct_1('#skF_4'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10'))) ),
    inference(splitRight,[status(thm)],[c_11571])).

tff(c_19818,plain,(
    v1_funct_1('#skF_3'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_19811,c_19515])).

tff(c_48,plain,(
    ! [A_13,B_14,C_15,D_37] :
      ( m1_subset_1('#skF_4'(A_13,B_14,C_15,D_37),k1_zfmisc_1(k2_zfmisc_1(A_13,B_14)))
      | ~ r1_partfun1(C_15,'#skF_5'(A_13,B_14,C_15,D_37))
      | ~ v1_partfun1('#skF_5'(A_13,B_14,C_15,D_37),A_13)
      | ~ m1_subset_1('#skF_5'(A_13,B_14,C_15,D_37),k1_zfmisc_1(k2_zfmisc_1(A_13,B_14)))
      | ~ v1_funct_1('#skF_5'(A_13,B_14,C_15,D_37))
      | k5_partfun1(A_13,B_14,C_15) = D_37
      | ~ m1_subset_1(C_15,k1_zfmisc_1(k2_zfmisc_1(A_13,B_14)))
      | ~ v1_funct_1(C_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_11548,plain,
    ( m1_subset_1('#skF_4'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')),k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
    | ~ v1_partfun1('#skF_5'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')),'#skF_7')
    | ~ m1_subset_1('#skF_5'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')),k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
    | ~ v1_funct_1('#skF_5'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')))
    | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10') = k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')
    | ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
    | ~ v1_funct_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_11545,c_48])).

tff(c_11562,plain,
    ( m1_subset_1('#skF_4'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')),k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
    | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10') = k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_11308,c_11302,c_11304,c_11548])).

tff(c_19651,plain,(
    m1_subset_1('#skF_4'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')),k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8')))) ),
    inference(negUnitSimplification,[status(thm)],[c_19516,c_11562])).

tff(c_19816,plain,(
    m1_subset_1('#skF_3'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')),k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_19811,c_19651])).

tff(c_20019,plain,(
    ! [C_60] :
      ( r1_partfun1(C_60,'#skF_3'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')))
      | ~ v1_funct_1('#skF_3'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')))
      | ~ m1_subset_1(C_60,k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
      | ~ v1_funct_1(C_60) ) ),
    inference(resolution,[status(thm)],[c_19816,c_68])).

tff(c_20070,plain,(
    ! [C_60] :
      ( r1_partfun1(C_60,'#skF_3'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')))
      | ~ m1_subset_1(C_60,k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
      | ~ v1_funct_1(C_60) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_19818,c_20019])).

tff(c_11437,plain,(
    ! [C_60] :
      ( r1_partfun1(C_60,'#skF_5'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')))
      | ~ m1_subset_1(C_60,k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
      | ~ v1_funct_1(C_60) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11308,c_11383])).

tff(c_42,plain,(
    ! [C_15,A_13,B_14,D_37] :
      ( r1_partfun1(C_15,'#skF_4'(A_13,B_14,C_15,D_37))
      | ~ r1_partfun1(C_15,'#skF_5'(A_13,B_14,C_15,D_37))
      | ~ v1_partfun1('#skF_5'(A_13,B_14,C_15,D_37),A_13)
      | ~ m1_subset_1('#skF_5'(A_13,B_14,C_15,D_37),k1_zfmisc_1(k2_zfmisc_1(A_13,B_14)))
      | ~ v1_funct_1('#skF_5'(A_13,B_14,C_15,D_37))
      | k5_partfun1(A_13,B_14,C_15) = D_37
      | ~ m1_subset_1(C_15,k1_zfmisc_1(k2_zfmisc_1(A_13,B_14)))
      | ~ v1_funct_1(C_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_11358,plain,
    ( r1_partfun1('#skF_9','#skF_4'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')))
    | ~ r1_partfun1('#skF_9','#skF_5'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')))
    | ~ v1_partfun1('#skF_5'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')),'#skF_7')
    | ~ v1_funct_1('#skF_5'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')))
    | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10') = k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')
    | ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
    | ~ v1_funct_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_11302,c_42])).

tff(c_11404,plain,
    ( r1_partfun1('#skF_9','#skF_4'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')))
    | ~ r1_partfun1('#skF_9','#skF_5'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')))
    | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10') = k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_11308,c_11304,c_11358])).

tff(c_20265,plain,
    ( r1_partfun1('#skF_9','#skF_3'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')))
    | ~ r1_partfun1('#skF_9','#skF_5'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')))
    | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10') = k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_19811,c_11404])).

tff(c_20266,plain,
    ( r1_partfun1('#skF_9','#skF_3'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')))
    | ~ r1_partfun1('#skF_9','#skF_5'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10'))) ),
    inference(negUnitSimplification,[status(thm)],[c_19516,c_20265])).

tff(c_20267,plain,(
    ~ r1_partfun1('#skF_9','#skF_5'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10'))) ),
    inference(splitLeft,[status(thm)],[c_20266])).

tff(c_20270,plain,
    ( ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
    | ~ v1_funct_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_11437,c_20267])).

tff(c_20274,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_20270])).

tff(c_20276,plain,(
    r1_partfun1('#skF_9','#skF_5'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10'))) ),
    inference(splitRight,[status(thm)],[c_20266])).

tff(c_44,plain,(
    ! [A_13,B_14,C_15,D_37] :
      ( v1_partfun1('#skF_4'(A_13,B_14,C_15,D_37),A_13)
      | ~ r1_partfun1(C_15,'#skF_5'(A_13,B_14,C_15,D_37))
      | ~ v1_partfun1('#skF_5'(A_13,B_14,C_15,D_37),A_13)
      | ~ m1_subset_1('#skF_5'(A_13,B_14,C_15,D_37),k1_zfmisc_1(k2_zfmisc_1(A_13,B_14)))
      | ~ v1_funct_1('#skF_5'(A_13,B_14,C_15,D_37))
      | k5_partfun1(A_13,B_14,C_15) = D_37
      | ~ m1_subset_1(C_15,k1_zfmisc_1(k2_zfmisc_1(A_13,B_14)))
      | ~ v1_funct_1(C_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_11554,plain,
    ( v1_partfun1('#skF_4'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')),'#skF_7')
    | ~ v1_partfun1('#skF_5'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')),'#skF_7')
    | ~ m1_subset_1('#skF_5'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')),k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
    | ~ v1_funct_1('#skF_5'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')))
    | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10') = k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')
    | ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
    | ~ v1_funct_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_11545,c_44])).

tff(c_11568,plain,
    ( v1_partfun1('#skF_4'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')),'#skF_7')
    | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10') = k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_11308,c_11302,c_11304,c_11554])).

tff(c_19546,plain,(
    v1_partfun1('#skF_4'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_19516,c_11568])).

tff(c_19668,plain,(
    ! [C_15] :
      ( r2_hidden('#skF_4'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')),k5_partfun1('#skF_7',k1_tarski('#skF_8'),C_15))
      | ~ r1_partfun1(C_15,'#skF_4'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')))
      | ~ v1_partfun1('#skF_4'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')),'#skF_7')
      | ~ v1_funct_1('#skF_4'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')))
      | ~ m1_subset_1(C_15,k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
      | ~ v1_funct_1(C_15) ) ),
    inference(resolution,[status(thm)],[c_19651,c_28])).

tff(c_19713,plain,(
    ! [C_15] :
      ( r2_hidden('#skF_4'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')),k5_partfun1('#skF_7',k1_tarski('#skF_8'),C_15))
      | ~ r1_partfun1(C_15,'#skF_4'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')))
      | ~ m1_subset_1(C_15,k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
      | ~ v1_funct_1(C_15) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_19515,c_19546,c_19668])).

tff(c_20327,plain,(
    ! [C_1038] :
      ( r2_hidden('#skF_3'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')),k5_partfun1('#skF_7',k1_tarski('#skF_8'),C_1038))
      | ~ r1_partfun1(C_1038,'#skF_3'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')))
      | ~ m1_subset_1(C_1038,k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
      | ~ v1_funct_1(C_1038) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_19811,c_19811,c_19713])).

tff(c_40,plain,(
    ! [A_13,B_14,C_15,D_37] :
      ( ~ r2_hidden('#skF_3'(A_13,B_14,C_15,D_37),D_37)
      | ~ r1_partfun1(C_15,'#skF_5'(A_13,B_14,C_15,D_37))
      | ~ v1_partfun1('#skF_5'(A_13,B_14,C_15,D_37),A_13)
      | ~ m1_subset_1('#skF_5'(A_13,B_14,C_15,D_37),k1_zfmisc_1(k2_zfmisc_1(A_13,B_14)))
      | ~ v1_funct_1('#skF_5'(A_13,B_14,C_15,D_37))
      | k5_partfun1(A_13,B_14,C_15) = D_37
      | ~ m1_subset_1(C_15,k1_zfmisc_1(k2_zfmisc_1(A_13,B_14)))
      | ~ v1_funct_1(C_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_20333,plain,
    ( ~ r1_partfun1('#skF_9','#skF_5'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')))
    | ~ v1_partfun1('#skF_5'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')),'#skF_7')
    | ~ m1_subset_1('#skF_5'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')),k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
    | ~ v1_funct_1('#skF_5'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')))
    | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10') = k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')
    | ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
    | ~ v1_funct_1('#skF_9')
    | ~ r1_partfun1('#skF_10','#skF_3'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')))
    | ~ m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
    | ~ v1_funct_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_20327,c_40])).

tff(c_20342,plain,
    ( k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10') = k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')
    | ~ r1_partfun1('#skF_10','#skF_3'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_74,c_82,c_80,c_11308,c_11302,c_11304,c_20276,c_20333])).

tff(c_20343,plain,(
    ~ r1_partfun1('#skF_10','#skF_3'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10'))) ),
    inference(negUnitSimplification,[status(thm)],[c_19516,c_20342])).

tff(c_20347,plain,
    ( ~ m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
    | ~ v1_funct_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_20070,c_20343])).

tff(c_20351,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_74,c_20347])).

tff(c_20352,plain,(
    k1_tarski('#skF_8') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_185])).

tff(c_24,plain,(
    ! [A_11,B_12] :
      ( k2_zfmisc_1(A_11,k1_tarski(B_12)) != k1_xboole_0
      | k1_xboole_0 = A_11 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_20362,plain,(
    ! [A_11] :
      ( k2_zfmisc_1(A_11,k1_xboole_0) != k1_xboole_0
      | k1_xboole_0 = A_11 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20352,c_24])).

tff(c_20374,plain,(
    ! [A_11] : k1_xboole_0 = A_11 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_20362])).

tff(c_20354,plain,(
    k5_partfun1('#skF_7',k1_xboole_0,'#skF_9') != k1_tarski('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20352,c_72])).

tff(c_20711,plain,(
    k1_tarski('#skF_10') != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_20374,c_20354])).

tff(c_20831,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_20374,c_20711])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n016.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:53:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 14.88/6.24  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 14.88/6.27  
% 14.88/6.27  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 14.88/6.27  %$ v1_funct_2 > v1_partfun1 > r2_hidden > r1_partfun1 > m1_subset_1 > v1_funct_1 > k5_partfun1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_6 > #skF_7 > #skF_10 > #skF_9 > #skF_4 > #skF_8 > #skF_5 > #skF_2 > #skF_3 > #skF_1
% 14.88/6.27  
% 14.88/6.27  %Foreground sorts:
% 14.88/6.27  
% 14.88/6.27  
% 14.88/6.27  %Background operators:
% 14.88/6.27  
% 14.88/6.27  
% 14.88/6.27  %Foreground operators:
% 14.88/6.27  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 14.88/6.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 14.88/6.27  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 14.88/6.27  tff(k1_tarski, type, k1_tarski: $i > $i).
% 14.88/6.27  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 14.88/6.27  tff('#skF_6', type, '#skF_6': ($i * $i * $i * $i * $i) > $i).
% 14.88/6.27  tff('#skF_7', type, '#skF_7': $i).
% 14.88/6.27  tff('#skF_10', type, '#skF_10': $i).
% 14.88/6.27  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 14.88/6.27  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 14.88/6.27  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 14.88/6.27  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 14.88/6.27  tff('#skF_9', type, '#skF_9': $i).
% 14.88/6.27  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 14.88/6.27  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 14.88/6.27  tff('#skF_8', type, '#skF_8': $i).
% 14.88/6.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 14.88/6.27  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i) > $i).
% 14.88/6.27  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 14.88/6.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 14.88/6.27  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 14.88/6.27  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 14.88/6.27  tff(k5_partfun1, type, k5_partfun1: ($i * $i * $i) > $i).
% 14.88/6.27  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 14.88/6.27  tff(r1_partfun1, type, r1_partfun1: ($i * $i) > $o).
% 14.88/6.27  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 14.88/6.27  
% 15.38/6.31  tff(f_42, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 15.38/6.31  tff(f_131, negated_conjecture, ~(![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (k5_partfun1(A, k1_tarski(B), C) = k1_tarski(D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t164_funct_2)).
% 15.38/6.31  tff(f_100, axiom, (![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (![D]: ((v1_funct_1(D) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => r1_partfun1(C, D))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_partfun1)).
% 15.38/6.31  tff(f_89, axiom, (![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | v1_partfun1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t132_funct_2)).
% 15.38/6.31  tff(f_72, axiom, (![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: ((D = k5_partfun1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> (?[F]: ((((v1_funct_1(F) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & (F = E)) & v1_partfun1(F, A)) & r1_partfun1(C, F))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_partfun1)).
% 15.38/6.31  tff(f_32, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 15.38/6.31  tff(f_117, axiom, (![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: ((v1_funct_1(D) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((v1_partfun1(C, A) & v1_partfun1(D, A)) & r1_partfun1(C, D)) => (C = D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_partfun1)).
% 15.38/6.31  tff(f_51, axiom, (![A, B]: (~(A = k1_xboole_0) => (~(k2_zfmisc_1(k1_tarski(B), A) = k1_xboole_0) & ~(k2_zfmisc_1(A, k1_tarski(B)) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t130_zfmisc_1)).
% 15.38/6.31  tff(c_20, plain, (![A_9]: (k2_zfmisc_1(A_9, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_42])).
% 15.38/6.31  tff(c_78, plain, (v1_funct_1('#skF_10')), inference(cnfTransformation, [status(thm)], [f_131])).
% 15.38/6.31  tff(c_74, plain, (m1_subset_1('#skF_10', k1_zfmisc_1(k2_zfmisc_1('#skF_7', k1_tarski('#skF_8'))))), inference(cnfTransformation, [status(thm)], [f_131])).
% 15.38/6.31  tff(c_72, plain, (k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_9')!=k1_tarski('#skF_10')), inference(cnfTransformation, [status(thm)], [f_131])).
% 15.38/6.31  tff(c_82, plain, (v1_funct_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_131])).
% 15.38/6.31  tff(c_80, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_7', k1_tarski('#skF_8'))))), inference(cnfTransformation, [status(thm)], [f_131])).
% 15.38/6.31  tff(c_193, plain, (![C_96, D_97, A_98, B_99]: (r1_partfun1(C_96, D_97) | ~m1_subset_1(D_97, k1_zfmisc_1(k2_zfmisc_1(A_98, k1_tarski(B_99)))) | ~v1_funct_1(D_97) | ~m1_subset_1(C_96, k1_zfmisc_1(k2_zfmisc_1(A_98, k1_tarski(B_99)))) | ~v1_funct_1(C_96))), inference(cnfTransformation, [status(thm)], [f_100])).
% 15.38/6.31  tff(c_195, plain, (![C_96]: (r1_partfun1(C_96, '#skF_10') | ~v1_funct_1('#skF_10') | ~m1_subset_1(C_96, k1_zfmisc_1(k2_zfmisc_1('#skF_7', k1_tarski('#skF_8')))) | ~v1_funct_1(C_96))), inference(resolution, [status(thm)], [c_74, c_193])).
% 15.38/6.31  tff(c_208, plain, (![C_100]: (r1_partfun1(C_100, '#skF_10') | ~m1_subset_1(C_100, k1_zfmisc_1(k2_zfmisc_1('#skF_7', k1_tarski('#skF_8')))) | ~v1_funct_1(C_100))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_195])).
% 15.38/6.31  tff(c_214, plain, (r1_partfun1('#skF_9', '#skF_10') | ~v1_funct_1('#skF_9')), inference(resolution, [status(thm)], [c_80, c_208])).
% 15.38/6.31  tff(c_220, plain, (r1_partfun1('#skF_9', '#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_214])).
% 15.38/6.31  tff(c_76, plain, (v1_funct_2('#skF_10', '#skF_7', k1_tarski('#skF_8'))), inference(cnfTransformation, [status(thm)], [f_131])).
% 15.38/6.31  tff(c_170, plain, (![B_91, C_92, A_93]: (k1_xboole_0=B_91 | v1_partfun1(C_92, A_93) | ~v1_funct_2(C_92, A_93, B_91) | ~m1_subset_1(C_92, k1_zfmisc_1(k2_zfmisc_1(A_93, B_91))) | ~v1_funct_1(C_92))), inference(cnfTransformation, [status(thm)], [f_89])).
% 15.38/6.31  tff(c_173, plain, (k1_tarski('#skF_8')=k1_xboole_0 | v1_partfun1('#skF_10', '#skF_7') | ~v1_funct_2('#skF_10', '#skF_7', k1_tarski('#skF_8')) | ~v1_funct_1('#skF_10')), inference(resolution, [status(thm)], [c_74, c_170])).
% 15.38/6.31  tff(c_185, plain, (k1_tarski('#skF_8')=k1_xboole_0 | v1_partfun1('#skF_10', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_173])).
% 15.38/6.31  tff(c_190, plain, (v1_partfun1('#skF_10', '#skF_7')), inference(splitLeft, [status(thm)], [c_185])).
% 15.38/6.31  tff(c_699, plain, (![F_227, A_228, B_229, C_230]: (r2_hidden(F_227, k5_partfun1(A_228, B_229, C_230)) | ~r1_partfun1(C_230, F_227) | ~v1_partfun1(F_227, A_228) | ~m1_subset_1(F_227, k1_zfmisc_1(k2_zfmisc_1(A_228, B_229))) | ~v1_funct_1(F_227) | ~m1_subset_1(C_230, k1_zfmisc_1(k2_zfmisc_1(A_228, B_229))) | ~v1_funct_1(C_230))), inference(cnfTransformation, [status(thm)], [f_72])).
% 15.38/6.31  tff(c_703, plain, (![C_230]: (r2_hidden('#skF_10', k5_partfun1('#skF_7', k1_tarski('#skF_8'), C_230)) | ~r1_partfun1(C_230, '#skF_10') | ~v1_partfun1('#skF_10', '#skF_7') | ~v1_funct_1('#skF_10') | ~m1_subset_1(C_230, k1_zfmisc_1(k2_zfmisc_1('#skF_7', k1_tarski('#skF_8')))) | ~v1_funct_1(C_230))), inference(resolution, [status(thm)], [c_74, c_699])).
% 15.38/6.31  tff(c_719, plain, (![C_231]: (r2_hidden('#skF_10', k5_partfun1('#skF_7', k1_tarski('#skF_8'), C_231)) | ~r1_partfun1(C_231, '#skF_10') | ~m1_subset_1(C_231, k1_zfmisc_1(k2_zfmisc_1('#skF_7', k1_tarski('#skF_8')))) | ~v1_funct_1(C_231))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_190, c_703])).
% 15.38/6.31  tff(c_729, plain, (r2_hidden('#skF_10', k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_9')) | ~r1_partfun1('#skF_9', '#skF_10') | ~v1_funct_1('#skF_9')), inference(resolution, [status(thm)], [c_80, c_719])).
% 15.38/6.31  tff(c_736, plain, (r2_hidden('#skF_10', k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_220, c_729])).
% 15.38/6.31  tff(c_12, plain, (![A_1, B_2]: ('#skF_1'(A_1, B_2)=A_1 | r2_hidden('#skF_2'(A_1, B_2), B_2) | k1_tarski(A_1)=B_2)), inference(cnfTransformation, [status(thm)], [f_32])).
% 15.38/6.31  tff(c_289, plain, (![A_132, B_133, C_134, D_135]: (v1_funct_1('#skF_4'(A_132, B_133, C_134, D_135)) | r2_hidden('#skF_5'(A_132, B_133, C_134, D_135), D_135) | k5_partfun1(A_132, B_133, C_134)=D_135 | ~m1_subset_1(C_134, k1_zfmisc_1(k2_zfmisc_1(A_132, B_133))) | ~v1_funct_1(C_134))), inference(cnfTransformation, [status(thm)], [f_72])).
% 15.38/6.31  tff(c_293, plain, (![D_135]: (v1_funct_1('#skF_4'('#skF_7', k1_tarski('#skF_8'), '#skF_9', D_135)) | r2_hidden('#skF_5'('#skF_7', k1_tarski('#skF_8'), '#skF_9', D_135), D_135) | k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_9')=D_135 | ~v1_funct_1('#skF_9'))), inference(resolution, [status(thm)], [c_80, c_289])).
% 15.38/6.31  tff(c_303, plain, (![D_135]: (v1_funct_1('#skF_4'('#skF_7', k1_tarski('#skF_8'), '#skF_9', D_135)) | r2_hidden('#skF_5'('#skF_7', k1_tarski('#skF_8'), '#skF_9', D_135), D_135) | k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_9')=D_135)), inference(demodulation, [status(thm), theory('equality')], [c_82, c_293])).
% 15.38/6.31  tff(c_329, plain, (![D_141]: (v1_funct_1('#skF_4'('#skF_7', k1_tarski('#skF_8'), '#skF_9', D_141)) | r2_hidden('#skF_5'('#skF_7', k1_tarski('#skF_8'), '#skF_9', D_141), D_141) | k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_9')=D_141)), inference(demodulation, [status(thm), theory('equality')], [c_82, c_293])).
% 15.38/6.31  tff(c_34, plain, (![E_51, B_14, A_13, C_15]: ('#skF_6'(E_51, B_14, k5_partfun1(A_13, B_14, C_15), A_13, C_15)=E_51 | ~r2_hidden(E_51, k5_partfun1(A_13, B_14, C_15)) | ~m1_subset_1(C_15, k1_zfmisc_1(k2_zfmisc_1(A_13, B_14))) | ~v1_funct_1(C_15))), inference(cnfTransformation, [status(thm)], [f_72])).
% 15.38/6.31  tff(c_2113, plain, (![A_456, B_457, C_458]: ('#skF_6'('#skF_5'('#skF_7', k1_tarski('#skF_8'), '#skF_9', k5_partfun1(A_456, B_457, C_458)), B_457, k5_partfun1(A_456, B_457, C_458), A_456, C_458)='#skF_5'('#skF_7', k1_tarski('#skF_8'), '#skF_9', k5_partfun1(A_456, B_457, C_458)) | ~m1_subset_1(C_458, k1_zfmisc_1(k2_zfmisc_1(A_456, B_457))) | ~v1_funct_1(C_458) | v1_funct_1('#skF_4'('#skF_7', k1_tarski('#skF_8'), '#skF_9', k5_partfun1(A_456, B_457, C_458))) | k5_partfun1(A_456, B_457, C_458)=k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_9'))), inference(resolution, [status(thm)], [c_329, c_34])).
% 15.38/6.31  tff(c_268, plain, (![E_112, B_113, A_114, C_115]: (v1_funct_1('#skF_6'(E_112, B_113, k5_partfun1(A_114, B_113, C_115), A_114, C_115)) | ~r2_hidden(E_112, k5_partfun1(A_114, B_113, C_115)) | ~m1_subset_1(C_115, k1_zfmisc_1(k2_zfmisc_1(A_114, B_113))) | ~v1_funct_1(C_115))), inference(cnfTransformation, [status(thm)], [f_72])).
% 15.38/6.31  tff(c_270, plain, (![E_112]: (v1_funct_1('#skF_6'(E_112, k1_tarski('#skF_8'), k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_10'), '#skF_7', '#skF_10')) | ~r2_hidden(E_112, k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_10')) | ~v1_funct_1('#skF_10'))), inference(resolution, [status(thm)], [c_74, c_268])).
% 15.38/6.31  tff(c_279, plain, (![E_112]: (v1_funct_1('#skF_6'(E_112, k1_tarski('#skF_8'), k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_10'), '#skF_7', '#skF_10')) | ~r2_hidden(E_112, k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_270])).
% 15.38/6.31  tff(c_2169, plain, (v1_funct_1('#skF_5'('#skF_7', k1_tarski('#skF_8'), '#skF_9', k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_10'))) | ~r2_hidden('#skF_5'('#skF_7', k1_tarski('#skF_8'), '#skF_9', k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_10')), k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_10')) | ~m1_subset_1('#skF_10', k1_zfmisc_1(k2_zfmisc_1('#skF_7', k1_tarski('#skF_8')))) | ~v1_funct_1('#skF_10') | v1_funct_1('#skF_4'('#skF_7', k1_tarski('#skF_8'), '#skF_9', k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_10'))) | k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_10')=k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_2113, c_279])).
% 15.38/6.31  tff(c_2184, plain, (v1_funct_1('#skF_5'('#skF_7', k1_tarski('#skF_8'), '#skF_9', k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_10'))) | ~r2_hidden('#skF_5'('#skF_7', k1_tarski('#skF_8'), '#skF_9', k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_10')), k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_10')) | v1_funct_1('#skF_4'('#skF_7', k1_tarski('#skF_8'), '#skF_9', k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_10'))) | k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_10')=k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_74, c_2169])).
% 15.38/6.31  tff(c_2355, plain, (~r2_hidden('#skF_5'('#skF_7', k1_tarski('#skF_8'), '#skF_9', k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_10')), k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_10'))), inference(splitLeft, [status(thm)], [c_2184])).
% 15.38/6.31  tff(c_2394, plain, (v1_funct_1('#skF_4'('#skF_7', k1_tarski('#skF_8'), '#skF_9', k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_10'))) | k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_10')=k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_9')), inference(resolution, [status(thm)], [c_303, c_2355])).
% 15.38/6.31  tff(c_2395, plain, (k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_10')=k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_9')), inference(splitLeft, [status(thm)], [c_2394])).
% 15.38/6.31  tff(c_2430, plain, (![E_112]: (v1_funct_1('#skF_6'(E_112, k1_tarski('#skF_8'), k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_9'), '#skF_7', '#skF_10')) | ~r2_hidden(E_112, k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_2395, c_2395, c_279])).
% 15.38/6.31  tff(c_32, plain, (![E_51, B_14, A_13, C_15]: (v1_partfun1('#skF_6'(E_51, B_14, k5_partfun1(A_13, B_14, C_15), A_13, C_15), A_13) | ~r2_hidden(E_51, k5_partfun1(A_13, B_14, C_15)) | ~m1_subset_1(C_15, k1_zfmisc_1(k2_zfmisc_1(A_13, B_14))) | ~v1_funct_1(C_15))), inference(cnfTransformation, [status(thm)], [f_72])).
% 15.38/6.31  tff(c_36, plain, (![E_51, B_14, A_13, C_15]: (m1_subset_1('#skF_6'(E_51, B_14, k5_partfun1(A_13, B_14, C_15), A_13, C_15), k1_zfmisc_1(k2_zfmisc_1(A_13, B_14))) | ~r2_hidden(E_51, k5_partfun1(A_13, B_14, C_15)) | ~m1_subset_1(C_15, k1_zfmisc_1(k2_zfmisc_1(A_13, B_14))) | ~v1_funct_1(C_15))), inference(cnfTransformation, [status(thm)], [f_72])).
% 15.38/6.31  tff(c_30, plain, (![C_15, E_51, B_14, A_13]: (r1_partfun1(C_15, '#skF_6'(E_51, B_14, k5_partfun1(A_13, B_14, C_15), A_13, C_15)) | ~r2_hidden(E_51, k5_partfun1(A_13, B_14, C_15)) | ~m1_subset_1(C_15, k1_zfmisc_1(k2_zfmisc_1(A_13, B_14))) | ~v1_funct_1(C_15))), inference(cnfTransformation, [status(thm)], [f_72])).
% 15.38/6.31  tff(c_460, plain, (![D_174, C_175, A_176, B_177]: (D_174=C_175 | ~r1_partfun1(C_175, D_174) | ~v1_partfun1(D_174, A_176) | ~v1_partfun1(C_175, A_176) | ~m1_subset_1(D_174, k1_zfmisc_1(k2_zfmisc_1(A_176, B_177))) | ~v1_funct_1(D_174) | ~m1_subset_1(C_175, k1_zfmisc_1(k2_zfmisc_1(A_176, B_177))) | ~v1_funct_1(C_175))), inference(cnfTransformation, [status(thm)], [f_117])).
% 15.38/6.31  tff(c_6979, plain, (![B_628, A_629, E_627, A_631, B_630, C_632]: ('#skF_6'(E_627, B_628, k5_partfun1(A_631, B_628, C_632), A_631, C_632)=C_632 | ~v1_partfun1('#skF_6'(E_627, B_628, k5_partfun1(A_631, B_628, C_632), A_631, C_632), A_629) | ~v1_partfun1(C_632, A_629) | ~m1_subset_1('#skF_6'(E_627, B_628, k5_partfun1(A_631, B_628, C_632), A_631, C_632), k1_zfmisc_1(k2_zfmisc_1(A_629, B_630))) | ~v1_funct_1('#skF_6'(E_627, B_628, k5_partfun1(A_631, B_628, C_632), A_631, C_632)) | ~m1_subset_1(C_632, k1_zfmisc_1(k2_zfmisc_1(A_629, B_630))) | ~r2_hidden(E_627, k5_partfun1(A_631, B_628, C_632)) | ~m1_subset_1(C_632, k1_zfmisc_1(k2_zfmisc_1(A_631, B_628))) | ~v1_funct_1(C_632))), inference(resolution, [status(thm)], [c_30, c_460])).
% 15.38/6.31  tff(c_8697, plain, (![E_697, B_698, A_699, C_700]: ('#skF_6'(E_697, B_698, k5_partfun1(A_699, B_698, C_700), A_699, C_700)=C_700 | ~v1_partfun1('#skF_6'(E_697, B_698, k5_partfun1(A_699, B_698, C_700), A_699, C_700), A_699) | ~v1_partfun1(C_700, A_699) | ~v1_funct_1('#skF_6'(E_697, B_698, k5_partfun1(A_699, B_698, C_700), A_699, C_700)) | ~r2_hidden(E_697, k5_partfun1(A_699, B_698, C_700)) | ~m1_subset_1(C_700, k1_zfmisc_1(k2_zfmisc_1(A_699, B_698))) | ~v1_funct_1(C_700))), inference(resolution, [status(thm)], [c_36, c_6979])).
% 15.38/6.31  tff(c_9131, plain, (![E_721, B_722, A_723, C_724]: ('#skF_6'(E_721, B_722, k5_partfun1(A_723, B_722, C_724), A_723, C_724)=C_724 | ~v1_partfun1(C_724, A_723) | ~v1_funct_1('#skF_6'(E_721, B_722, k5_partfun1(A_723, B_722, C_724), A_723, C_724)) | ~r2_hidden(E_721, k5_partfun1(A_723, B_722, C_724)) | ~m1_subset_1(C_724, k1_zfmisc_1(k2_zfmisc_1(A_723, B_722))) | ~v1_funct_1(C_724))), inference(resolution, [status(thm)], [c_32, c_8697])).
% 15.38/6.31  tff(c_9139, plain, (![E_721]: ('#skF_6'(E_721, k1_tarski('#skF_8'), k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_10'), '#skF_7', '#skF_10')='#skF_10' | ~v1_partfun1('#skF_10', '#skF_7') | ~v1_funct_1('#skF_6'(E_721, k1_tarski('#skF_8'), k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_9'), '#skF_7', '#skF_10')) | ~r2_hidden(E_721, k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_10')) | ~m1_subset_1('#skF_10', k1_zfmisc_1(k2_zfmisc_1('#skF_7', k1_tarski('#skF_8')))) | ~v1_funct_1('#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_2395, c_9131])).
% 15.38/6.31  tff(c_9780, plain, (![E_741]: ('#skF_6'(E_741, k1_tarski('#skF_8'), k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_9'), '#skF_7', '#skF_10')='#skF_10' | ~v1_funct_1('#skF_6'(E_741, k1_tarski('#skF_8'), k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_9'), '#skF_7', '#skF_10')) | ~r2_hidden(E_741, k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_74, c_2395, c_190, c_2395, c_9139])).
% 15.38/6.31  tff(c_9797, plain, (![E_745]: ('#skF_6'(E_745, k1_tarski('#skF_8'), k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_9'), '#skF_7', '#skF_10')='#skF_10' | ~r2_hidden(E_745, k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_9')))), inference(resolution, [status(thm)], [c_2430, c_9780])).
% 15.38/6.31  tff(c_258, plain, (![E_106, B_107, A_108, C_109]: ('#skF_6'(E_106, B_107, k5_partfun1(A_108, B_107, C_109), A_108, C_109)=E_106 | ~r2_hidden(E_106, k5_partfun1(A_108, B_107, C_109)) | ~m1_subset_1(C_109, k1_zfmisc_1(k2_zfmisc_1(A_108, B_107))) | ~v1_funct_1(C_109))), inference(cnfTransformation, [status(thm)], [f_72])).
% 15.38/6.31  tff(c_266, plain, (![A_1, A_108, B_107, C_109]: ('#skF_6'('#skF_2'(A_1, k5_partfun1(A_108, B_107, C_109)), B_107, k5_partfun1(A_108, B_107, C_109), A_108, C_109)='#skF_2'(A_1, k5_partfun1(A_108, B_107, C_109)) | ~m1_subset_1(C_109, k1_zfmisc_1(k2_zfmisc_1(A_108, B_107))) | ~v1_funct_1(C_109) | '#skF_1'(A_1, k5_partfun1(A_108, B_107, C_109))=A_1 | k5_partfun1(A_108, B_107, C_109)=k1_tarski(A_1))), inference(resolution, [status(thm)], [c_12, c_258])).
% 15.38/6.31  tff(c_2457, plain, (![A_1]: ('#skF_6'('#skF_2'(A_1, k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_10')), k1_tarski('#skF_8'), k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_9'), '#skF_7', '#skF_10')='#skF_2'(A_1, k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_10')) | ~m1_subset_1('#skF_10', k1_zfmisc_1(k2_zfmisc_1('#skF_7', k1_tarski('#skF_8')))) | ~v1_funct_1('#skF_10') | '#skF_1'(A_1, k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_10'))=A_1 | k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_10')=k1_tarski(A_1))), inference(superposition, [status(thm), theory('equality')], [c_2395, c_266])).
% 15.38/6.31  tff(c_2494, plain, (![A_1]: ('#skF_6'('#skF_2'(A_1, k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_9')), k1_tarski('#skF_8'), k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_9'), '#skF_7', '#skF_10')='#skF_2'(A_1, k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_9')) | '#skF_1'(A_1, k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_9'))=A_1 | k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_9')=k1_tarski(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_2395, c_2395, c_78, c_74, c_2395, c_2395, c_2457])).
% 15.38/6.31  tff(c_10129, plain, (![A_749]: ('#skF_2'(A_749, k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_9'))='#skF_10' | '#skF_1'(A_749, k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_9'))=A_749 | k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_9')=k1_tarski(A_749) | ~r2_hidden('#skF_2'(A_749, k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_9')), k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_9')))), inference(superposition, [status(thm), theory('equality')], [c_9797, c_2494])).
% 15.38/6.31  tff(c_10141, plain, (![A_750]: ('#skF_2'(A_750, k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_9'))='#skF_10' | '#skF_1'(A_750, k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_9'))=A_750 | k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_9')=k1_tarski(A_750))), inference(resolution, [status(thm)], [c_12, c_10129])).
% 15.38/6.31  tff(c_8, plain, (![A_1, B_2]: ('#skF_1'(A_1, B_2)=A_1 | '#skF_2'(A_1, B_2)!=A_1 | k1_tarski(A_1)=B_2)), inference(cnfTransformation, [status(thm)], [f_32])).
% 15.38/6.31  tff(c_10185, plain, (![A_750]: ('#skF_1'(A_750, k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_9'))=A_750 | A_750!='#skF_10' | k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_9')=k1_tarski(A_750) | '#skF_1'(A_750, k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_9'))=A_750 | k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_9')=k1_tarski(A_750))), inference(superposition, [status(thm), theory('equality')], [c_10141, c_8])).
% 15.38/6.31  tff(c_10242, plain, (![A_752]: (A_752!='#skF_10' | k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_9')=k1_tarski(A_752) | '#skF_1'(A_752, k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_9'))=A_752)), inference(factorization, [status(thm), theory('equality')], [c_10185])).
% 15.38/6.31  tff(c_6, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | '#skF_2'(A_1, B_2)!=A_1 | k1_tarski(A_1)=B_2)), inference(cnfTransformation, [status(thm)], [f_32])).
% 15.38/6.31  tff(c_10272, plain, (![A_756]: (~r2_hidden(A_756, k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_9')) | '#skF_2'(A_756, k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_9'))!=A_756 | k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_9')=k1_tarski(A_756) | A_756!='#skF_10' | k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_9')=k1_tarski(A_756))), inference(superposition, [status(thm), theory('equality')], [c_10242, c_6])).
% 15.38/6.31  tff(c_10459, plain, ('#skF_2'('#skF_10', k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_9'))!='#skF_10' | k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_9')=k1_tarski('#skF_10')), inference(resolution, [status(thm)], [c_736, c_10272])).
% 15.38/6.31  tff(c_10580, plain, ('#skF_2'('#skF_10', k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_9'))!='#skF_10'), inference(negUnitSimplification, [status(thm)], [c_72, c_72, c_10459])).
% 15.38/6.31  tff(c_10139, plain, (![A_1]: ('#skF_2'(A_1, k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_9'))='#skF_10' | '#skF_1'(A_1, k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_9'))=A_1 | k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_9')=k1_tarski(A_1))), inference(resolution, [status(thm)], [c_12, c_10129])).
% 15.38/6.31  tff(c_10601, plain, ('#skF_1'('#skF_10', k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_9'))='#skF_10' | k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_9')=k1_tarski('#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_10139, c_10580])).
% 15.38/6.31  tff(c_10604, plain, ('#skF_1'('#skF_10', k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_9'))='#skF_10'), inference(negUnitSimplification, [status(thm)], [c_72, c_10601])).
% 15.38/6.31  tff(c_10, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r2_hidden('#skF_2'(A_1, B_2), B_2) | k1_tarski(A_1)=B_2)), inference(cnfTransformation, [status(thm)], [f_32])).
% 15.38/6.31  tff(c_265, plain, (![A_1, A_108, B_107, C_109]: ('#skF_6'('#skF_2'(A_1, k5_partfun1(A_108, B_107, C_109)), B_107, k5_partfun1(A_108, B_107, C_109), A_108, C_109)='#skF_2'(A_1, k5_partfun1(A_108, B_107, C_109)) | ~m1_subset_1(C_109, k1_zfmisc_1(k2_zfmisc_1(A_108, B_107))) | ~v1_funct_1(C_109) | ~r2_hidden('#skF_1'(A_1, k5_partfun1(A_108, B_107, C_109)), k5_partfun1(A_108, B_107, C_109)) | k5_partfun1(A_108, B_107, C_109)=k1_tarski(A_1))), inference(resolution, [status(thm)], [c_10, c_258])).
% 15.38/6.31  tff(c_10622, plain, ('#skF_6'('#skF_2'('#skF_10', k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_9')), k1_tarski('#skF_8'), k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_9'), '#skF_7', '#skF_9')='#skF_2'('#skF_10', k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_9')) | ~m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_7', k1_tarski('#skF_8')))) | ~v1_funct_1('#skF_9') | ~r2_hidden('#skF_10', k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_9')) | k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_9')=k1_tarski('#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_10604, c_265])).
% 15.38/6.31  tff(c_10648, plain, ('#skF_6'('#skF_2'('#skF_10', k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_9')), k1_tarski('#skF_8'), k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_9'), '#skF_7', '#skF_9')='#skF_2'('#skF_10', k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_9')) | k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_9')=k1_tarski('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_736, c_82, c_80, c_10622])).
% 15.38/6.31  tff(c_10649, plain, ('#skF_6'('#skF_2'('#skF_10', k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_9')), k1_tarski('#skF_8'), k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_9'), '#skF_7', '#skF_9')='#skF_2'('#skF_10', k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_9'))), inference(negUnitSimplification, [status(thm)], [c_72, c_10648])).
% 15.38/6.31  tff(c_272, plain, (![E_112]: (v1_funct_1('#skF_6'(E_112, k1_tarski('#skF_8'), k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_9'), '#skF_7', '#skF_9')) | ~r2_hidden(E_112, k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_9')) | ~v1_funct_1('#skF_9'))), inference(resolution, [status(thm)], [c_80, c_268])).
% 15.38/6.31  tff(c_282, plain, (![E_112]: (v1_funct_1('#skF_6'(E_112, k1_tarski('#skF_8'), k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_9'), '#skF_7', '#skF_9')) | ~r2_hidden(E_112, k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_272])).
% 15.38/6.31  tff(c_10765, plain, (v1_funct_1('#skF_2'('#skF_10', k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_9'))) | ~r2_hidden('#skF_2'('#skF_10', k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_9')), k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_10649, c_282])).
% 15.38/6.31  tff(c_10856, plain, (~r2_hidden('#skF_2'('#skF_10', k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_9')), k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_9'))), inference(splitLeft, [status(thm)], [c_10765])).
% 15.38/6.31  tff(c_10862, plain, (~r2_hidden('#skF_1'('#skF_10', k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_9')), k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_9')) | k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_9')=k1_tarski('#skF_10')), inference(resolution, [status(thm)], [c_10, c_10856])).
% 15.38/6.31  tff(c_10871, plain, (k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_9')=k1_tarski('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_736, c_10604, c_10862])).
% 15.38/6.31  tff(c_10873, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_10871])).
% 15.38/6.31  tff(c_10875, plain, (r2_hidden('#skF_2'('#skF_10', k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_9')), k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_9'))), inference(splitRight, [status(thm)], [c_10765])).
% 15.38/6.31  tff(c_2474, plain, (![E_51]: ('#skF_6'(E_51, k1_tarski('#skF_8'), k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_10'), '#skF_7', '#skF_10')=E_51 | ~r2_hidden(E_51, k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_9')) | ~m1_subset_1('#skF_10', k1_zfmisc_1(k2_zfmisc_1('#skF_7', k1_tarski('#skF_8')))) | ~v1_funct_1('#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_2395, c_34])).
% 15.38/6.31  tff(c_2506, plain, (![E_51]: ('#skF_6'(E_51, k1_tarski('#skF_8'), k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_9'), '#skF_7', '#skF_10')=E_51 | ~r2_hidden(E_51, k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_74, c_2395, c_2474])).
% 15.38/6.31  tff(c_9824, plain, (![E_745]: (E_745='#skF_10' | ~r2_hidden(E_745, k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_9')) | ~r2_hidden(E_745, k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_9')))), inference(superposition, [status(thm), theory('equality')], [c_9797, c_2506])).
% 15.38/6.31  tff(c_10910, plain, ('#skF_2'('#skF_10', k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_9'))='#skF_10' | ~r2_hidden('#skF_2'('#skF_10', k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_9')), k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_9'))), inference(resolution, [status(thm)], [c_10875, c_9824])).
% 15.38/6.31  tff(c_10947, plain, ('#skF_2'('#skF_10', k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_9'))='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_10875, c_10910])).
% 15.38/6.31  tff(c_10949, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10580, c_10947])).
% 15.38/6.31  tff(c_10951, plain, (k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_10')!=k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_9')), inference(splitRight, [status(thm)], [c_2394])).
% 15.38/6.31  tff(c_747, plain, (![A_232, B_233, C_234, D_235]: ('#skF_4'(A_232, B_233, C_234, D_235)='#skF_3'(A_232, B_233, C_234, D_235) | r2_hidden('#skF_5'(A_232, B_233, C_234, D_235), D_235) | k5_partfun1(A_232, B_233, C_234)=D_235 | ~m1_subset_1(C_234, k1_zfmisc_1(k2_zfmisc_1(A_232, B_233))) | ~v1_funct_1(C_234))), inference(cnfTransformation, [status(thm)], [f_72])).
% 15.38/6.31  tff(c_753, plain, (![D_235]: ('#skF_4'('#skF_7', k1_tarski('#skF_8'), '#skF_9', D_235)='#skF_3'('#skF_7', k1_tarski('#skF_8'), '#skF_9', D_235) | r2_hidden('#skF_5'('#skF_7', k1_tarski('#skF_8'), '#skF_9', D_235), D_235) | k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_9')=D_235 | ~v1_funct_1('#skF_9'))), inference(resolution, [status(thm)], [c_80, c_747])).
% 15.38/6.31  tff(c_764, plain, (![D_235]: ('#skF_4'('#skF_7', k1_tarski('#skF_8'), '#skF_9', D_235)='#skF_3'('#skF_7', k1_tarski('#skF_8'), '#skF_9', D_235) | r2_hidden('#skF_5'('#skF_7', k1_tarski('#skF_8'), '#skF_9', D_235), D_235) | k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_9')=D_235)), inference(demodulation, [status(thm), theory('equality')], [c_82, c_753])).
% 15.38/6.31  tff(c_2390, plain, ('#skF_4'('#skF_7', k1_tarski('#skF_8'), '#skF_9', k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_10'))='#skF_3'('#skF_7', k1_tarski('#skF_8'), '#skF_9', k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_10')) | k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_10')=k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_9')), inference(resolution, [status(thm)], [c_764, c_2355])).
% 15.38/6.31  tff(c_10990, plain, ('#skF_4'('#skF_7', k1_tarski('#skF_8'), '#skF_9', k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_10'))='#skF_3'('#skF_7', k1_tarski('#skF_8'), '#skF_9', k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_10'))), inference(negUnitSimplification, [status(thm)], [c_10951, c_2390])).
% 15.38/6.31  tff(c_10950, plain, (v1_funct_1('#skF_4'('#skF_7', k1_tarski('#skF_8'), '#skF_9', k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_10')))), inference(splitRight, [status(thm)], [c_2394])).
% 15.38/6.31  tff(c_10993, plain, (v1_funct_1('#skF_3'('#skF_7', k1_tarski('#skF_8'), '#skF_9', k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_10990, c_10950])).
% 15.38/6.31  tff(c_884, plain, (![A_253, B_254, C_255, D_256]: (m1_subset_1('#skF_4'(A_253, B_254, C_255, D_256), k1_zfmisc_1(k2_zfmisc_1(A_253, B_254))) | r2_hidden('#skF_5'(A_253, B_254, C_255, D_256), D_256) | k5_partfun1(A_253, B_254, C_255)=D_256 | ~m1_subset_1(C_255, k1_zfmisc_1(k2_zfmisc_1(A_253, B_254))) | ~v1_funct_1(C_255))), inference(cnfTransformation, [status(thm)], [f_72])).
% 15.38/6.31  tff(c_68, plain, (![C_60, D_62, A_58, B_59]: (r1_partfun1(C_60, D_62) | ~m1_subset_1(D_62, k1_zfmisc_1(k2_zfmisc_1(A_58, k1_tarski(B_59)))) | ~v1_funct_1(D_62) | ~m1_subset_1(C_60, k1_zfmisc_1(k2_zfmisc_1(A_58, k1_tarski(B_59)))) | ~v1_funct_1(C_60))), inference(cnfTransformation, [status(thm)], [f_100])).
% 15.38/6.31  tff(c_1934, plain, (![C_431, A_433, D_432, C_434, B_430]: (r1_partfun1(C_434, '#skF_4'(A_433, k1_tarski(B_430), C_431, D_432)) | ~v1_funct_1('#skF_4'(A_433, k1_tarski(B_430), C_431, D_432)) | ~m1_subset_1(C_434, k1_zfmisc_1(k2_zfmisc_1(A_433, k1_tarski(B_430)))) | ~v1_funct_1(C_434) | r2_hidden('#skF_5'(A_433, k1_tarski(B_430), C_431, D_432), D_432) | k5_partfun1(A_433, k1_tarski(B_430), C_431)=D_432 | ~m1_subset_1(C_431, k1_zfmisc_1(k2_zfmisc_1(A_433, k1_tarski(B_430)))) | ~v1_funct_1(C_431))), inference(resolution, [status(thm)], [c_884, c_68])).
% 15.38/6.31  tff(c_1949, plain, (![C_431, D_432]: (r1_partfun1('#skF_10', '#skF_4'('#skF_7', k1_tarski('#skF_8'), C_431, D_432)) | ~v1_funct_1('#skF_4'('#skF_7', k1_tarski('#skF_8'), C_431, D_432)) | ~v1_funct_1('#skF_10') | r2_hidden('#skF_5'('#skF_7', k1_tarski('#skF_8'), C_431, D_432), D_432) | k5_partfun1('#skF_7', k1_tarski('#skF_8'), C_431)=D_432 | ~m1_subset_1(C_431, k1_zfmisc_1(k2_zfmisc_1('#skF_7', k1_tarski('#skF_8')))) | ~v1_funct_1(C_431))), inference(resolution, [status(thm)], [c_74, c_1934])).
% 15.38/6.31  tff(c_1967, plain, (![C_435, D_436]: (r1_partfun1('#skF_10', '#skF_4'('#skF_7', k1_tarski('#skF_8'), C_435, D_436)) | ~v1_funct_1('#skF_4'('#skF_7', k1_tarski('#skF_8'), C_435, D_436)) | r2_hidden('#skF_5'('#skF_7', k1_tarski('#skF_8'), C_435, D_436), D_436) | k5_partfun1('#skF_7', k1_tarski('#skF_8'), C_435)=D_436 | ~m1_subset_1(C_435, k1_zfmisc_1(k2_zfmisc_1('#skF_7', k1_tarski('#skF_8')))) | ~v1_funct_1(C_435))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_1949])).
% 15.38/6.31  tff(c_1984, plain, (![D_436]: (r1_partfun1('#skF_10', '#skF_4'('#skF_7', k1_tarski('#skF_8'), '#skF_9', D_436)) | ~v1_funct_1('#skF_4'('#skF_7', k1_tarski('#skF_8'), '#skF_9', D_436)) | r2_hidden('#skF_5'('#skF_7', k1_tarski('#skF_8'), '#skF_9', D_436), D_436) | k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_9')=D_436 | ~v1_funct_1('#skF_9'))), inference(resolution, [status(thm)], [c_80, c_1967])).
% 15.38/6.31  tff(c_1995, plain, (![D_436]: (r1_partfun1('#skF_10', '#skF_4'('#skF_7', k1_tarski('#skF_8'), '#skF_9', D_436)) | ~v1_funct_1('#skF_4'('#skF_7', k1_tarski('#skF_8'), '#skF_9', D_436)) | r2_hidden('#skF_5'('#skF_7', k1_tarski('#skF_8'), '#skF_9', D_436), D_436) | k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_9')=D_436)), inference(demodulation, [status(thm), theory('equality')], [c_82, c_1984])).
% 15.38/6.31  tff(c_2384, plain, (r1_partfun1('#skF_10', '#skF_4'('#skF_7', k1_tarski('#skF_8'), '#skF_9', k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_10'))) | ~v1_funct_1('#skF_4'('#skF_7', k1_tarski('#skF_8'), '#skF_9', k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_10'))) | k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_10')=k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_9')), inference(resolution, [status(thm)], [c_1995, c_2355])).
% 15.38/6.31  tff(c_11025, plain, (r1_partfun1('#skF_10', '#skF_3'('#skF_7', k1_tarski('#skF_8'), '#skF_9', k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_10'))) | k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_10')=k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_10993, c_10990, c_10990, c_2384])).
% 15.38/6.31  tff(c_11026, plain, (r1_partfun1('#skF_10', '#skF_3'('#skF_7', k1_tarski('#skF_8'), '#skF_9', k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_10')))), inference(negUnitSimplification, [status(thm)], [c_10951, c_11025])).
% 15.38/6.31  tff(c_558, plain, (![A_186, B_187, C_188, D_189]: (v1_partfun1('#skF_4'(A_186, B_187, C_188, D_189), A_186) | r2_hidden('#skF_5'(A_186, B_187, C_188, D_189), D_189) | k5_partfun1(A_186, B_187, C_188)=D_189 | ~m1_subset_1(C_188, k1_zfmisc_1(k2_zfmisc_1(A_186, B_187))) | ~v1_funct_1(C_188))), inference(cnfTransformation, [status(thm)], [f_72])).
% 15.38/6.31  tff(c_562, plain, (![D_189]: (v1_partfun1('#skF_4'('#skF_7', k1_tarski('#skF_8'), '#skF_9', D_189), '#skF_7') | r2_hidden('#skF_5'('#skF_7', k1_tarski('#skF_8'), '#skF_9', D_189), D_189) | k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_9')=D_189 | ~v1_funct_1('#skF_9'))), inference(resolution, [status(thm)], [c_80, c_558])).
% 15.38/6.31  tff(c_572, plain, (![D_189]: (v1_partfun1('#skF_4'('#skF_7', k1_tarski('#skF_8'), '#skF_9', D_189), '#skF_7') | r2_hidden('#skF_5'('#skF_7', k1_tarski('#skF_8'), '#skF_9', D_189), D_189) | k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_9')=D_189)), inference(demodulation, [status(thm), theory('equality')], [c_82, c_562])).
% 15.38/6.31  tff(c_2391, plain, (v1_partfun1('#skF_4'('#skF_7', k1_tarski('#skF_8'), '#skF_9', k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_10')), '#skF_7') | k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_10')=k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_9')), inference(resolution, [status(thm)], [c_572, c_2355])).
% 15.38/6.31  tff(c_10952, plain, (v1_partfun1('#skF_4'('#skF_7', k1_tarski('#skF_8'), '#skF_9', k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_10')), '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_10951, c_2391])).
% 15.38/6.31  tff(c_10992, plain, (v1_partfun1('#skF_3'('#skF_7', k1_tarski('#skF_8'), '#skF_9', k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_10')), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_10990, c_10952])).
% 15.38/6.31  tff(c_60, plain, (![A_13, B_14, C_15, D_37]: (m1_subset_1('#skF_4'(A_13, B_14, C_15, D_37), k1_zfmisc_1(k2_zfmisc_1(A_13, B_14))) | r2_hidden('#skF_5'(A_13, B_14, C_15, D_37), D_37) | k5_partfun1(A_13, B_14, C_15)=D_37 | ~m1_subset_1(C_15, k1_zfmisc_1(k2_zfmisc_1(A_13, B_14))) | ~v1_funct_1(C_15))), inference(cnfTransformation, [status(thm)], [f_72])).
% 15.38/6.31  tff(c_11007, plain, (m1_subset_1('#skF_3'('#skF_7', k1_tarski('#skF_8'), '#skF_9', k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_10')), k1_zfmisc_1(k2_zfmisc_1('#skF_7', k1_tarski('#skF_8')))) | r2_hidden('#skF_5'('#skF_7', k1_tarski('#skF_8'), '#skF_9', k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_10')), k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_10')) | k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_10')=k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_9') | ~m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_7', k1_tarski('#skF_8')))) | ~v1_funct_1('#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_10990, c_60])).
% 15.38/6.31  tff(c_11021, plain, (m1_subset_1('#skF_3'('#skF_7', k1_tarski('#skF_8'), '#skF_9', k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_10')), k1_zfmisc_1(k2_zfmisc_1('#skF_7', k1_tarski('#skF_8')))) | r2_hidden('#skF_5'('#skF_7', k1_tarski('#skF_8'), '#skF_9', k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_10')), k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_10')) | k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_10')=k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_11007])).
% 15.38/6.31  tff(c_11022, plain, (m1_subset_1('#skF_3'('#skF_7', k1_tarski('#skF_8'), '#skF_9', k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_10')), k1_zfmisc_1(k2_zfmisc_1('#skF_7', k1_tarski('#skF_8'))))), inference(negUnitSimplification, [status(thm)], [c_10951, c_2355, c_11021])).
% 15.38/6.31  tff(c_28, plain, (![F_54, A_13, B_14, C_15]: (r2_hidden(F_54, k5_partfun1(A_13, B_14, C_15)) | ~r1_partfun1(C_15, F_54) | ~v1_partfun1(F_54, A_13) | ~m1_subset_1(F_54, k1_zfmisc_1(k2_zfmisc_1(A_13, B_14))) | ~v1_funct_1(F_54) | ~m1_subset_1(C_15, k1_zfmisc_1(k2_zfmisc_1(A_13, B_14))) | ~v1_funct_1(C_15))), inference(cnfTransformation, [status(thm)], [f_72])).
% 15.38/6.31  tff(c_11053, plain, (![C_15]: (r2_hidden('#skF_3'('#skF_7', k1_tarski('#skF_8'), '#skF_9', k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_10')), k5_partfun1('#skF_7', k1_tarski('#skF_8'), C_15)) | ~r1_partfun1(C_15, '#skF_3'('#skF_7', k1_tarski('#skF_8'), '#skF_9', k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_10'))) | ~v1_partfun1('#skF_3'('#skF_7', k1_tarski('#skF_8'), '#skF_9', k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_10')), '#skF_7') | ~v1_funct_1('#skF_3'('#skF_7', k1_tarski('#skF_8'), '#skF_9', k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_10'))) | ~m1_subset_1(C_15, k1_zfmisc_1(k2_zfmisc_1('#skF_7', k1_tarski('#skF_8')))) | ~v1_funct_1(C_15))), inference(resolution, [status(thm)], [c_11022, c_28])).
% 15.38/6.31  tff(c_11242, plain, (![C_774]: (r2_hidden('#skF_3'('#skF_7', k1_tarski('#skF_8'), '#skF_9', k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_10')), k5_partfun1('#skF_7', k1_tarski('#skF_8'), C_774)) | ~r1_partfun1(C_774, '#skF_3'('#skF_7', k1_tarski('#skF_8'), '#skF_9', k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_10'))) | ~m1_subset_1(C_774, k1_zfmisc_1(k2_zfmisc_1('#skF_7', k1_tarski('#skF_8')))) | ~v1_funct_1(C_774))), inference(demodulation, [status(thm), theory('equality')], [c_10993, c_10992, c_11053])).
% 15.38/6.31  tff(c_382, plain, (![A_153, B_154, C_155, D_156]: (~r2_hidden('#skF_3'(A_153, B_154, C_155, D_156), D_156) | r2_hidden('#skF_5'(A_153, B_154, C_155, D_156), D_156) | k5_partfun1(A_153, B_154, C_155)=D_156 | ~m1_subset_1(C_155, k1_zfmisc_1(k2_zfmisc_1(A_153, B_154))) | ~v1_funct_1(C_155))), inference(cnfTransformation, [status(thm)], [f_72])).
% 15.38/6.31  tff(c_386, plain, (![D_156]: (~r2_hidden('#skF_3'('#skF_7', k1_tarski('#skF_8'), '#skF_9', D_156), D_156) | r2_hidden('#skF_5'('#skF_7', k1_tarski('#skF_8'), '#skF_9', D_156), D_156) | k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_9')=D_156 | ~v1_funct_1('#skF_9'))), inference(resolution, [status(thm)], [c_80, c_382])).
% 15.38/6.31  tff(c_396, plain, (![D_156]: (~r2_hidden('#skF_3'('#skF_7', k1_tarski('#skF_8'), '#skF_9', D_156), D_156) | r2_hidden('#skF_5'('#skF_7', k1_tarski('#skF_8'), '#skF_9', D_156), D_156) | k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_9')=D_156)), inference(demodulation, [status(thm), theory('equality')], [c_82, c_386])).
% 15.38/6.31  tff(c_2392, plain, (~r2_hidden('#skF_3'('#skF_7', k1_tarski('#skF_8'), '#skF_9', k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_10')), k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_10')) | k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_10')=k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_9')), inference(resolution, [status(thm)], [c_396, c_2355])).
% 15.38/6.31  tff(c_10989, plain, (~r2_hidden('#skF_3'('#skF_7', k1_tarski('#skF_8'), '#skF_9', k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_10')), k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_10'))), inference(negUnitSimplification, [status(thm)], [c_10951, c_2392])).
% 15.38/6.31  tff(c_11245, plain, (~r1_partfun1('#skF_10', '#skF_3'('#skF_7', k1_tarski('#skF_8'), '#skF_9', k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_10'))) | ~m1_subset_1('#skF_10', k1_zfmisc_1(k2_zfmisc_1('#skF_7', k1_tarski('#skF_8')))) | ~v1_funct_1('#skF_10')), inference(resolution, [status(thm)], [c_11242, c_10989])).
% 15.38/6.31  tff(c_11254, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_78, c_74, c_11026, c_11245])).
% 15.38/6.31  tff(c_11256, plain, (r2_hidden('#skF_5'('#skF_7', k1_tarski('#skF_8'), '#skF_9', k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_10')), k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_10'))), inference(splitRight, [status(thm)], [c_2184])).
% 15.38/6.31  tff(c_11258, plain, ('#skF_6'('#skF_5'('#skF_7', k1_tarski('#skF_8'), '#skF_9', k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_10')), k1_tarski('#skF_8'), k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_10'), '#skF_7', '#skF_10')='#skF_5'('#skF_7', k1_tarski('#skF_8'), '#skF_9', k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_10')) | ~m1_subset_1('#skF_10', k1_zfmisc_1(k2_zfmisc_1('#skF_7', k1_tarski('#skF_8')))) | ~v1_funct_1('#skF_10')), inference(resolution, [status(thm)], [c_11256, c_34])).
% 15.38/6.31  tff(c_11261, plain, ('#skF_6'('#skF_5'('#skF_7', k1_tarski('#skF_8'), '#skF_9', k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_10')), k1_tarski('#skF_8'), k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_10'), '#skF_7', '#skF_10')='#skF_5'('#skF_7', k1_tarski('#skF_8'), '#skF_9', k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_74, c_11258])).
% 15.38/6.31  tff(c_11286, plain, (v1_funct_1('#skF_5'('#skF_7', k1_tarski('#skF_8'), '#skF_9', k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_10'))) | ~r2_hidden('#skF_5'('#skF_7', k1_tarski('#skF_8'), '#skF_9', k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_10')), k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_11261, c_279])).
% 15.38/6.31  tff(c_11308, plain, (v1_funct_1('#skF_5'('#skF_7', k1_tarski('#skF_8'), '#skF_9', k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_11256, c_11286])).
% 15.38/6.31  tff(c_11277, plain, (m1_subset_1('#skF_5'('#skF_7', k1_tarski('#skF_8'), '#skF_9', k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_10')), k1_zfmisc_1(k2_zfmisc_1('#skF_7', k1_tarski('#skF_8')))) | ~r2_hidden('#skF_5'('#skF_7', k1_tarski('#skF_8'), '#skF_9', k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_10')), k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_10')) | ~m1_subset_1('#skF_10', k1_zfmisc_1(k2_zfmisc_1('#skF_7', k1_tarski('#skF_8')))) | ~v1_funct_1('#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_11261, c_36])).
% 15.38/6.31  tff(c_11302, plain, (m1_subset_1('#skF_5'('#skF_7', k1_tarski('#skF_8'), '#skF_9', k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_10')), k1_zfmisc_1(k2_zfmisc_1('#skF_7', k1_tarski('#skF_8'))))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_74, c_11256, c_11277])).
% 15.38/6.31  tff(c_11280, plain, (v1_partfun1('#skF_5'('#skF_7', k1_tarski('#skF_8'), '#skF_9', k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_10')), '#skF_7') | ~r2_hidden('#skF_5'('#skF_7', k1_tarski('#skF_8'), '#skF_9', k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_10')), k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_10')) | ~m1_subset_1('#skF_10', k1_zfmisc_1(k2_zfmisc_1('#skF_7', k1_tarski('#skF_8')))) | ~v1_funct_1('#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_11261, c_32])).
% 15.38/6.31  tff(c_11304, plain, (v1_partfun1('#skF_5'('#skF_7', k1_tarski('#skF_8'), '#skF_9', k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_10')), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_74, c_11256, c_11280])).
% 15.38/6.31  tff(c_11383, plain, (![C_60]: (r1_partfun1(C_60, '#skF_5'('#skF_7', k1_tarski('#skF_8'), '#skF_9', k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_10'))) | ~v1_funct_1('#skF_5'('#skF_7', k1_tarski('#skF_8'), '#skF_9', k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_10'))) | ~m1_subset_1(C_60, k1_zfmisc_1(k2_zfmisc_1('#skF_7', k1_tarski('#skF_8')))) | ~v1_funct_1(C_60))), inference(resolution, [status(thm)], [c_11302, c_68])).
% 15.38/6.31  tff(c_11545, plain, (![C_783]: (r1_partfun1(C_783, '#skF_5'('#skF_7', k1_tarski('#skF_8'), '#skF_9', k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_10'))) | ~m1_subset_1(C_783, k1_zfmisc_1(k2_zfmisc_1('#skF_7', k1_tarski('#skF_8')))) | ~v1_funct_1(C_783))), inference(demodulation, [status(thm), theory('equality')], [c_11308, c_11383])).
% 15.38/6.31  tff(c_50, plain, (![A_13, B_14, C_15, D_37]: (v1_funct_1('#skF_4'(A_13, B_14, C_15, D_37)) | ~r1_partfun1(C_15, '#skF_5'(A_13, B_14, C_15, D_37)) | ~v1_partfun1('#skF_5'(A_13, B_14, C_15, D_37), A_13) | ~m1_subset_1('#skF_5'(A_13, B_14, C_15, D_37), k1_zfmisc_1(k2_zfmisc_1(A_13, B_14))) | ~v1_funct_1('#skF_5'(A_13, B_14, C_15, D_37)) | k5_partfun1(A_13, B_14, C_15)=D_37 | ~m1_subset_1(C_15, k1_zfmisc_1(k2_zfmisc_1(A_13, B_14))) | ~v1_funct_1(C_15))), inference(cnfTransformation, [status(thm)], [f_72])).
% 15.38/6.31  tff(c_11557, plain, (v1_funct_1('#skF_4'('#skF_7', k1_tarski('#skF_8'), '#skF_9', k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_10'))) | ~v1_partfun1('#skF_5'('#skF_7', k1_tarski('#skF_8'), '#skF_9', k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_10')), '#skF_7') | ~m1_subset_1('#skF_5'('#skF_7', k1_tarski('#skF_8'), '#skF_9', k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_10')), k1_zfmisc_1(k2_zfmisc_1('#skF_7', k1_tarski('#skF_8')))) | ~v1_funct_1('#skF_5'('#skF_7', k1_tarski('#skF_8'), '#skF_9', k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_10'))) | k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_10')=k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_9') | ~m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_7', k1_tarski('#skF_8')))) | ~v1_funct_1('#skF_9')), inference(resolution, [status(thm)], [c_11545, c_50])).
% 15.38/6.31  tff(c_11571, plain, (v1_funct_1('#skF_4'('#skF_7', k1_tarski('#skF_8'), '#skF_9', k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_10'))) | k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_10')=k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_11308, c_11302, c_11304, c_11557])).
% 15.38/6.31  tff(c_11575, plain, (k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_10')=k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_9')), inference(splitLeft, [status(thm)], [c_11571])).
% 15.38/6.31  tff(c_11619, plain, (![E_112]: (v1_funct_1('#skF_6'(E_112, k1_tarski('#skF_8'), k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_9'), '#skF_7', '#skF_10')) | ~r2_hidden(E_112, k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_11575, c_11575, c_279])).
% 15.38/6.31  tff(c_16799, plain, (![C_915, A_914, B_913, B_911, E_910, A_912]: ('#skF_6'(E_910, B_911, k5_partfun1(A_914, B_911, C_915), A_914, C_915)=C_915 | ~v1_partfun1('#skF_6'(E_910, B_911, k5_partfun1(A_914, B_911, C_915), A_914, C_915), A_912) | ~v1_partfun1(C_915, A_912) | ~m1_subset_1('#skF_6'(E_910, B_911, k5_partfun1(A_914, B_911, C_915), A_914, C_915), k1_zfmisc_1(k2_zfmisc_1(A_912, B_913))) | ~v1_funct_1('#skF_6'(E_910, B_911, k5_partfun1(A_914, B_911, C_915), A_914, C_915)) | ~m1_subset_1(C_915, k1_zfmisc_1(k2_zfmisc_1(A_912, B_913))) | ~r2_hidden(E_910, k5_partfun1(A_914, B_911, C_915)) | ~m1_subset_1(C_915, k1_zfmisc_1(k2_zfmisc_1(A_914, B_911))) | ~v1_funct_1(C_915))), inference(resolution, [status(thm)], [c_30, c_460])).
% 15.38/6.31  tff(c_17289, plain, (![E_955, B_956, A_957, C_958]: ('#skF_6'(E_955, B_956, k5_partfun1(A_957, B_956, C_958), A_957, C_958)=C_958 | ~v1_partfun1('#skF_6'(E_955, B_956, k5_partfun1(A_957, B_956, C_958), A_957, C_958), A_957) | ~v1_partfun1(C_958, A_957) | ~v1_funct_1('#skF_6'(E_955, B_956, k5_partfun1(A_957, B_956, C_958), A_957, C_958)) | ~r2_hidden(E_955, k5_partfun1(A_957, B_956, C_958)) | ~m1_subset_1(C_958, k1_zfmisc_1(k2_zfmisc_1(A_957, B_956))) | ~v1_funct_1(C_958))), inference(resolution, [status(thm)], [c_36, c_16799])).
% 15.38/6.31  tff(c_17464, plain, (![E_959, B_960, A_961, C_962]: ('#skF_6'(E_959, B_960, k5_partfun1(A_961, B_960, C_962), A_961, C_962)=C_962 | ~v1_partfun1(C_962, A_961) | ~v1_funct_1('#skF_6'(E_959, B_960, k5_partfun1(A_961, B_960, C_962), A_961, C_962)) | ~r2_hidden(E_959, k5_partfun1(A_961, B_960, C_962)) | ~m1_subset_1(C_962, k1_zfmisc_1(k2_zfmisc_1(A_961, B_960))) | ~v1_funct_1(C_962))), inference(resolution, [status(thm)], [c_32, c_17289])).
% 15.38/6.31  tff(c_17472, plain, (![E_959]: ('#skF_6'(E_959, k1_tarski('#skF_8'), k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_10'), '#skF_7', '#skF_10')='#skF_10' | ~v1_partfun1('#skF_10', '#skF_7') | ~v1_funct_1('#skF_6'(E_959, k1_tarski('#skF_8'), k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_9'), '#skF_7', '#skF_10')) | ~r2_hidden(E_959, k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_10')) | ~m1_subset_1('#skF_10', k1_zfmisc_1(k2_zfmisc_1('#skF_7', k1_tarski('#skF_8')))) | ~v1_funct_1('#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_11575, c_17464])).
% 15.38/6.31  tff(c_18100, plain, (![E_982]: ('#skF_6'(E_982, k1_tarski('#skF_8'), k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_9'), '#skF_7', '#skF_10')='#skF_10' | ~v1_funct_1('#skF_6'(E_982, k1_tarski('#skF_8'), k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_9'), '#skF_7', '#skF_10')) | ~r2_hidden(E_982, k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_74, c_11575, c_190, c_11575, c_17472])).
% 15.38/6.31  tff(c_18113, plain, (![E_983]: ('#skF_6'(E_983, k1_tarski('#skF_8'), k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_9'), '#skF_7', '#skF_10')='#skF_10' | ~r2_hidden(E_983, k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_9')))), inference(resolution, [status(thm)], [c_11619, c_18100])).
% 15.38/6.31  tff(c_11663, plain, (![E_51]: ('#skF_6'(E_51, k1_tarski('#skF_8'), k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_10'), '#skF_7', '#skF_10')=E_51 | ~r2_hidden(E_51, k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_9')) | ~m1_subset_1('#skF_10', k1_zfmisc_1(k2_zfmisc_1('#skF_7', k1_tarski('#skF_8')))) | ~v1_funct_1('#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_11575, c_34])).
% 15.38/6.31  tff(c_11695, plain, (![E_51]: ('#skF_6'(E_51, k1_tarski('#skF_8'), k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_9'), '#skF_7', '#skF_10')=E_51 | ~r2_hidden(E_51, k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_74, c_11575, c_11663])).
% 15.38/6.31  tff(c_18164, plain, (![E_984]: (E_984='#skF_10' | ~r2_hidden(E_984, k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_9')) | ~r2_hidden(E_984, k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_9')))), inference(superposition, [status(thm), theory('equality')], [c_18113, c_11695])).
% 15.38/6.31  tff(c_18506, plain, (![A_987]: ('#skF_2'(A_987, k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_9'))='#skF_10' | ~r2_hidden('#skF_2'(A_987, k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_9')), k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_9')) | '#skF_1'(A_987, k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_9'))=A_987 | k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_9')=k1_tarski(A_987))), inference(resolution, [status(thm)], [c_12, c_18164])).
% 15.38/6.31  tff(c_18518, plain, (![A_988]: ('#skF_2'(A_988, k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_9'))='#skF_10' | '#skF_1'(A_988, k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_9'))=A_988 | k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_9')=k1_tarski(A_988))), inference(resolution, [status(thm)], [c_12, c_18506])).
% 15.38/6.31  tff(c_18556, plain, (![A_988]: ('#skF_1'(A_988, k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_9'))=A_988 | A_988!='#skF_10' | k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_9')=k1_tarski(A_988) | '#skF_1'(A_988, k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_9'))=A_988 | k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_9')=k1_tarski(A_988))), inference(superposition, [status(thm), theory('equality')], [c_18518, c_8])).
% 15.38/6.31  tff(c_18613, plain, (![A_993]: (A_993!='#skF_10' | k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_9')=k1_tarski(A_993) | '#skF_1'(A_993, k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_9'))=A_993)), inference(factorization, [status(thm), theory('equality')], [c_18556])).
% 15.38/6.31  tff(c_18642, plain, (![A_994]: (~r2_hidden(A_994, k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_9')) | '#skF_2'(A_994, k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_9'))!=A_994 | k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_9')=k1_tarski(A_994) | A_994!='#skF_10' | k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_9')=k1_tarski(A_994))), inference(superposition, [status(thm), theory('equality')], [c_18613, c_6])).
% 15.38/6.31  tff(c_18821, plain, ('#skF_2'('#skF_10', k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_9'))!='#skF_10' | k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_9')=k1_tarski('#skF_10')), inference(resolution, [status(thm)], [c_736, c_18642])).
% 15.38/6.31  tff(c_18952, plain, ('#skF_2'('#skF_10', k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_9'))!='#skF_10'), inference(negUnitSimplification, [status(thm)], [c_72, c_72, c_18821])).
% 15.38/6.31  tff(c_18516, plain, (![A_1]: ('#skF_2'(A_1, k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_9'))='#skF_10' | '#skF_1'(A_1, k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_9'))=A_1 | k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_9')=k1_tarski(A_1))), inference(resolution, [status(thm)], [c_12, c_18506])).
% 15.38/6.31  tff(c_18985, plain, ('#skF_1'('#skF_10', k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_9'))='#skF_10' | k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_9')=k1_tarski('#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_18516, c_18952])).
% 15.38/6.31  tff(c_18988, plain, ('#skF_1'('#skF_10', k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_9'))='#skF_10'), inference(negUnitSimplification, [status(thm)], [c_72, c_18985])).
% 15.38/6.31  tff(c_19006, plain, ('#skF_6'('#skF_2'('#skF_10', k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_9')), k1_tarski('#skF_8'), k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_9'), '#skF_7', '#skF_9')='#skF_2'('#skF_10', k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_9')) | ~m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_7', k1_tarski('#skF_8')))) | ~v1_funct_1('#skF_9') | ~r2_hidden('#skF_10', k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_9')) | k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_9')=k1_tarski('#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_18988, c_265])).
% 15.38/6.31  tff(c_19032, plain, ('#skF_6'('#skF_2'('#skF_10', k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_9')), k1_tarski('#skF_8'), k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_9'), '#skF_7', '#skF_9')='#skF_2'('#skF_10', k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_9')) | k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_9')=k1_tarski('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_736, c_82, c_80, c_19006])).
% 15.38/6.31  tff(c_19033, plain, ('#skF_6'('#skF_2'('#skF_10', k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_9')), k1_tarski('#skF_8'), k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_9'), '#skF_7', '#skF_9')='#skF_2'('#skF_10', k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_9'))), inference(negUnitSimplification, [status(thm)], [c_72, c_19032])).
% 15.38/6.31  tff(c_19356, plain, (v1_partfun1('#skF_2'('#skF_10', k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_9')), '#skF_7') | ~r2_hidden('#skF_2'('#skF_10', k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_9')), k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_9')) | ~m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_7', k1_tarski('#skF_8')))) | ~v1_funct_1('#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_19033, c_32])).
% 15.38/6.31  tff(c_19412, plain, (v1_partfun1('#skF_2'('#skF_10', k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_9')), '#skF_7') | ~r2_hidden('#skF_2'('#skF_10', k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_9')), k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_19356])).
% 15.38/6.31  tff(c_19423, plain, (~r2_hidden('#skF_2'('#skF_10', k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_9')), k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_9'))), inference(splitLeft, [status(thm)], [c_19412])).
% 15.38/6.31  tff(c_19450, plain, (~r2_hidden('#skF_1'('#skF_10', k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_9')), k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_9')) | k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_9')=k1_tarski('#skF_10')), inference(resolution, [status(thm)], [c_10, c_19423])).
% 15.38/6.31  tff(c_19459, plain, (k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_9')=k1_tarski('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_736, c_18988, c_19450])).
% 15.38/6.31  tff(c_19461, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_19459])).
% 15.38/6.31  tff(c_19463, plain, (r2_hidden('#skF_2'('#skF_10', k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_9')), k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_9'))), inference(splitRight, [status(thm)], [c_19412])).
% 15.38/6.31  tff(c_18134, plain, (![E_983]: (E_983='#skF_10' | ~r2_hidden(E_983, k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_9')) | ~r2_hidden(E_983, k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_9')))), inference(superposition, [status(thm), theory('equality')], [c_18113, c_11695])).
% 15.38/6.31  tff(c_19475, plain, ('#skF_2'('#skF_10', k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_9'))='#skF_10' | ~r2_hidden('#skF_2'('#skF_10', k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_9')), k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_9'))), inference(resolution, [status(thm)], [c_19463, c_18134])).
% 15.38/6.31  tff(c_19512, plain, ('#skF_2'('#skF_10', k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_9'))='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_19463, c_19475])).
% 15.38/6.31  tff(c_19514, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18952, c_19512])).
% 15.38/6.31  tff(c_19516, plain, (k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_10')!=k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_9')), inference(splitRight, [status(thm)], [c_11571])).
% 15.38/6.31  tff(c_46, plain, (![A_13, B_14, C_15, D_37]: ('#skF_4'(A_13, B_14, C_15, D_37)='#skF_3'(A_13, B_14, C_15, D_37) | ~r1_partfun1(C_15, '#skF_5'(A_13, B_14, C_15, D_37)) | ~v1_partfun1('#skF_5'(A_13, B_14, C_15, D_37), A_13) | ~m1_subset_1('#skF_5'(A_13, B_14, C_15, D_37), k1_zfmisc_1(k2_zfmisc_1(A_13, B_14))) | ~v1_funct_1('#skF_5'(A_13, B_14, C_15, D_37)) | k5_partfun1(A_13, B_14, C_15)=D_37 | ~m1_subset_1(C_15, k1_zfmisc_1(k2_zfmisc_1(A_13, B_14))) | ~v1_funct_1(C_15))), inference(cnfTransformation, [status(thm)], [f_72])).
% 15.38/6.31  tff(c_11551, plain, ('#skF_4'('#skF_7', k1_tarski('#skF_8'), '#skF_9', k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_10'))='#skF_3'('#skF_7', k1_tarski('#skF_8'), '#skF_9', k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_10')) | ~v1_partfun1('#skF_5'('#skF_7', k1_tarski('#skF_8'), '#skF_9', k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_10')), '#skF_7') | ~m1_subset_1('#skF_5'('#skF_7', k1_tarski('#skF_8'), '#skF_9', k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_10')), k1_zfmisc_1(k2_zfmisc_1('#skF_7', k1_tarski('#skF_8')))) | ~v1_funct_1('#skF_5'('#skF_7', k1_tarski('#skF_8'), '#skF_9', k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_10'))) | k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_10')=k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_9') | ~m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_7', k1_tarski('#skF_8')))) | ~v1_funct_1('#skF_9')), inference(resolution, [status(thm)], [c_11545, c_46])).
% 15.38/6.31  tff(c_11565, plain, ('#skF_4'('#skF_7', k1_tarski('#skF_8'), '#skF_9', k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_10'))='#skF_3'('#skF_7', k1_tarski('#skF_8'), '#skF_9', k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_10')) | k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_10')=k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_11308, c_11302, c_11304, c_11551])).
% 15.38/6.31  tff(c_19811, plain, ('#skF_4'('#skF_7', k1_tarski('#skF_8'), '#skF_9', k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_10'))='#skF_3'('#skF_7', k1_tarski('#skF_8'), '#skF_9', k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_10'))), inference(negUnitSimplification, [status(thm)], [c_19516, c_11565])).
% 15.38/6.31  tff(c_19515, plain, (v1_funct_1('#skF_4'('#skF_7', k1_tarski('#skF_8'), '#skF_9', k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_10')))), inference(splitRight, [status(thm)], [c_11571])).
% 15.38/6.31  tff(c_19818, plain, (v1_funct_1('#skF_3'('#skF_7', k1_tarski('#skF_8'), '#skF_9', k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_19811, c_19515])).
% 15.38/6.31  tff(c_48, plain, (![A_13, B_14, C_15, D_37]: (m1_subset_1('#skF_4'(A_13, B_14, C_15, D_37), k1_zfmisc_1(k2_zfmisc_1(A_13, B_14))) | ~r1_partfun1(C_15, '#skF_5'(A_13, B_14, C_15, D_37)) | ~v1_partfun1('#skF_5'(A_13, B_14, C_15, D_37), A_13) | ~m1_subset_1('#skF_5'(A_13, B_14, C_15, D_37), k1_zfmisc_1(k2_zfmisc_1(A_13, B_14))) | ~v1_funct_1('#skF_5'(A_13, B_14, C_15, D_37)) | k5_partfun1(A_13, B_14, C_15)=D_37 | ~m1_subset_1(C_15, k1_zfmisc_1(k2_zfmisc_1(A_13, B_14))) | ~v1_funct_1(C_15))), inference(cnfTransformation, [status(thm)], [f_72])).
% 15.38/6.31  tff(c_11548, plain, (m1_subset_1('#skF_4'('#skF_7', k1_tarski('#skF_8'), '#skF_9', k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_10')), k1_zfmisc_1(k2_zfmisc_1('#skF_7', k1_tarski('#skF_8')))) | ~v1_partfun1('#skF_5'('#skF_7', k1_tarski('#skF_8'), '#skF_9', k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_10')), '#skF_7') | ~m1_subset_1('#skF_5'('#skF_7', k1_tarski('#skF_8'), '#skF_9', k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_10')), k1_zfmisc_1(k2_zfmisc_1('#skF_7', k1_tarski('#skF_8')))) | ~v1_funct_1('#skF_5'('#skF_7', k1_tarski('#skF_8'), '#skF_9', k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_10'))) | k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_10')=k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_9') | ~m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_7', k1_tarski('#skF_8')))) | ~v1_funct_1('#skF_9')), inference(resolution, [status(thm)], [c_11545, c_48])).
% 15.38/6.31  tff(c_11562, plain, (m1_subset_1('#skF_4'('#skF_7', k1_tarski('#skF_8'), '#skF_9', k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_10')), k1_zfmisc_1(k2_zfmisc_1('#skF_7', k1_tarski('#skF_8')))) | k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_10')=k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_11308, c_11302, c_11304, c_11548])).
% 15.38/6.31  tff(c_19651, plain, (m1_subset_1('#skF_4'('#skF_7', k1_tarski('#skF_8'), '#skF_9', k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_10')), k1_zfmisc_1(k2_zfmisc_1('#skF_7', k1_tarski('#skF_8'))))), inference(negUnitSimplification, [status(thm)], [c_19516, c_11562])).
% 15.38/6.31  tff(c_19816, plain, (m1_subset_1('#skF_3'('#skF_7', k1_tarski('#skF_8'), '#skF_9', k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_10')), k1_zfmisc_1(k2_zfmisc_1('#skF_7', k1_tarski('#skF_8'))))), inference(demodulation, [status(thm), theory('equality')], [c_19811, c_19651])).
% 15.38/6.31  tff(c_20019, plain, (![C_60]: (r1_partfun1(C_60, '#skF_3'('#skF_7', k1_tarski('#skF_8'), '#skF_9', k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_10'))) | ~v1_funct_1('#skF_3'('#skF_7', k1_tarski('#skF_8'), '#skF_9', k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_10'))) | ~m1_subset_1(C_60, k1_zfmisc_1(k2_zfmisc_1('#skF_7', k1_tarski('#skF_8')))) | ~v1_funct_1(C_60))), inference(resolution, [status(thm)], [c_19816, c_68])).
% 15.38/6.31  tff(c_20070, plain, (![C_60]: (r1_partfun1(C_60, '#skF_3'('#skF_7', k1_tarski('#skF_8'), '#skF_9', k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_10'))) | ~m1_subset_1(C_60, k1_zfmisc_1(k2_zfmisc_1('#skF_7', k1_tarski('#skF_8')))) | ~v1_funct_1(C_60))), inference(demodulation, [status(thm), theory('equality')], [c_19818, c_20019])).
% 15.38/6.31  tff(c_11437, plain, (![C_60]: (r1_partfun1(C_60, '#skF_5'('#skF_7', k1_tarski('#skF_8'), '#skF_9', k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_10'))) | ~m1_subset_1(C_60, k1_zfmisc_1(k2_zfmisc_1('#skF_7', k1_tarski('#skF_8')))) | ~v1_funct_1(C_60))), inference(demodulation, [status(thm), theory('equality')], [c_11308, c_11383])).
% 15.38/6.31  tff(c_42, plain, (![C_15, A_13, B_14, D_37]: (r1_partfun1(C_15, '#skF_4'(A_13, B_14, C_15, D_37)) | ~r1_partfun1(C_15, '#skF_5'(A_13, B_14, C_15, D_37)) | ~v1_partfun1('#skF_5'(A_13, B_14, C_15, D_37), A_13) | ~m1_subset_1('#skF_5'(A_13, B_14, C_15, D_37), k1_zfmisc_1(k2_zfmisc_1(A_13, B_14))) | ~v1_funct_1('#skF_5'(A_13, B_14, C_15, D_37)) | k5_partfun1(A_13, B_14, C_15)=D_37 | ~m1_subset_1(C_15, k1_zfmisc_1(k2_zfmisc_1(A_13, B_14))) | ~v1_funct_1(C_15))), inference(cnfTransformation, [status(thm)], [f_72])).
% 15.38/6.31  tff(c_11358, plain, (r1_partfun1('#skF_9', '#skF_4'('#skF_7', k1_tarski('#skF_8'), '#skF_9', k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_10'))) | ~r1_partfun1('#skF_9', '#skF_5'('#skF_7', k1_tarski('#skF_8'), '#skF_9', k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_10'))) | ~v1_partfun1('#skF_5'('#skF_7', k1_tarski('#skF_8'), '#skF_9', k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_10')), '#skF_7') | ~v1_funct_1('#skF_5'('#skF_7', k1_tarski('#skF_8'), '#skF_9', k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_10'))) | k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_10')=k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_9') | ~m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_7', k1_tarski('#skF_8')))) | ~v1_funct_1('#skF_9')), inference(resolution, [status(thm)], [c_11302, c_42])).
% 15.38/6.31  tff(c_11404, plain, (r1_partfun1('#skF_9', '#skF_4'('#skF_7', k1_tarski('#skF_8'), '#skF_9', k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_10'))) | ~r1_partfun1('#skF_9', '#skF_5'('#skF_7', k1_tarski('#skF_8'), '#skF_9', k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_10'))) | k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_10')=k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_11308, c_11304, c_11358])).
% 15.38/6.31  tff(c_20265, plain, (r1_partfun1('#skF_9', '#skF_3'('#skF_7', k1_tarski('#skF_8'), '#skF_9', k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_10'))) | ~r1_partfun1('#skF_9', '#skF_5'('#skF_7', k1_tarski('#skF_8'), '#skF_9', k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_10'))) | k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_10')=k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_19811, c_11404])).
% 15.38/6.31  tff(c_20266, plain, (r1_partfun1('#skF_9', '#skF_3'('#skF_7', k1_tarski('#skF_8'), '#skF_9', k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_10'))) | ~r1_partfun1('#skF_9', '#skF_5'('#skF_7', k1_tarski('#skF_8'), '#skF_9', k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_10')))), inference(negUnitSimplification, [status(thm)], [c_19516, c_20265])).
% 15.38/6.31  tff(c_20267, plain, (~r1_partfun1('#skF_9', '#skF_5'('#skF_7', k1_tarski('#skF_8'), '#skF_9', k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_10')))), inference(splitLeft, [status(thm)], [c_20266])).
% 15.38/6.31  tff(c_20270, plain, (~m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_7', k1_tarski('#skF_8')))) | ~v1_funct_1('#skF_9')), inference(resolution, [status(thm)], [c_11437, c_20267])).
% 15.38/6.31  tff(c_20274, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_20270])).
% 15.38/6.31  tff(c_20276, plain, (r1_partfun1('#skF_9', '#skF_5'('#skF_7', k1_tarski('#skF_8'), '#skF_9', k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_10')))), inference(splitRight, [status(thm)], [c_20266])).
% 15.38/6.31  tff(c_44, plain, (![A_13, B_14, C_15, D_37]: (v1_partfun1('#skF_4'(A_13, B_14, C_15, D_37), A_13) | ~r1_partfun1(C_15, '#skF_5'(A_13, B_14, C_15, D_37)) | ~v1_partfun1('#skF_5'(A_13, B_14, C_15, D_37), A_13) | ~m1_subset_1('#skF_5'(A_13, B_14, C_15, D_37), k1_zfmisc_1(k2_zfmisc_1(A_13, B_14))) | ~v1_funct_1('#skF_5'(A_13, B_14, C_15, D_37)) | k5_partfun1(A_13, B_14, C_15)=D_37 | ~m1_subset_1(C_15, k1_zfmisc_1(k2_zfmisc_1(A_13, B_14))) | ~v1_funct_1(C_15))), inference(cnfTransformation, [status(thm)], [f_72])).
% 15.38/6.31  tff(c_11554, plain, (v1_partfun1('#skF_4'('#skF_7', k1_tarski('#skF_8'), '#skF_9', k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_10')), '#skF_7') | ~v1_partfun1('#skF_5'('#skF_7', k1_tarski('#skF_8'), '#skF_9', k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_10')), '#skF_7') | ~m1_subset_1('#skF_5'('#skF_7', k1_tarski('#skF_8'), '#skF_9', k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_10')), k1_zfmisc_1(k2_zfmisc_1('#skF_7', k1_tarski('#skF_8')))) | ~v1_funct_1('#skF_5'('#skF_7', k1_tarski('#skF_8'), '#skF_9', k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_10'))) | k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_10')=k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_9') | ~m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_7', k1_tarski('#skF_8')))) | ~v1_funct_1('#skF_9')), inference(resolution, [status(thm)], [c_11545, c_44])).
% 15.38/6.31  tff(c_11568, plain, (v1_partfun1('#skF_4'('#skF_7', k1_tarski('#skF_8'), '#skF_9', k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_10')), '#skF_7') | k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_10')=k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_11308, c_11302, c_11304, c_11554])).
% 15.38/6.31  tff(c_19546, plain, (v1_partfun1('#skF_4'('#skF_7', k1_tarski('#skF_8'), '#skF_9', k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_10')), '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_19516, c_11568])).
% 15.38/6.31  tff(c_19668, plain, (![C_15]: (r2_hidden('#skF_4'('#skF_7', k1_tarski('#skF_8'), '#skF_9', k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_10')), k5_partfun1('#skF_7', k1_tarski('#skF_8'), C_15)) | ~r1_partfun1(C_15, '#skF_4'('#skF_7', k1_tarski('#skF_8'), '#skF_9', k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_10'))) | ~v1_partfun1('#skF_4'('#skF_7', k1_tarski('#skF_8'), '#skF_9', k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_10')), '#skF_7') | ~v1_funct_1('#skF_4'('#skF_7', k1_tarski('#skF_8'), '#skF_9', k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_10'))) | ~m1_subset_1(C_15, k1_zfmisc_1(k2_zfmisc_1('#skF_7', k1_tarski('#skF_8')))) | ~v1_funct_1(C_15))), inference(resolution, [status(thm)], [c_19651, c_28])).
% 15.38/6.31  tff(c_19713, plain, (![C_15]: (r2_hidden('#skF_4'('#skF_7', k1_tarski('#skF_8'), '#skF_9', k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_10')), k5_partfun1('#skF_7', k1_tarski('#skF_8'), C_15)) | ~r1_partfun1(C_15, '#skF_4'('#skF_7', k1_tarski('#skF_8'), '#skF_9', k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_10'))) | ~m1_subset_1(C_15, k1_zfmisc_1(k2_zfmisc_1('#skF_7', k1_tarski('#skF_8')))) | ~v1_funct_1(C_15))), inference(demodulation, [status(thm), theory('equality')], [c_19515, c_19546, c_19668])).
% 15.38/6.31  tff(c_20327, plain, (![C_1038]: (r2_hidden('#skF_3'('#skF_7', k1_tarski('#skF_8'), '#skF_9', k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_10')), k5_partfun1('#skF_7', k1_tarski('#skF_8'), C_1038)) | ~r1_partfun1(C_1038, '#skF_3'('#skF_7', k1_tarski('#skF_8'), '#skF_9', k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_10'))) | ~m1_subset_1(C_1038, k1_zfmisc_1(k2_zfmisc_1('#skF_7', k1_tarski('#skF_8')))) | ~v1_funct_1(C_1038))), inference(demodulation, [status(thm), theory('equality')], [c_19811, c_19811, c_19713])).
% 15.38/6.31  tff(c_40, plain, (![A_13, B_14, C_15, D_37]: (~r2_hidden('#skF_3'(A_13, B_14, C_15, D_37), D_37) | ~r1_partfun1(C_15, '#skF_5'(A_13, B_14, C_15, D_37)) | ~v1_partfun1('#skF_5'(A_13, B_14, C_15, D_37), A_13) | ~m1_subset_1('#skF_5'(A_13, B_14, C_15, D_37), k1_zfmisc_1(k2_zfmisc_1(A_13, B_14))) | ~v1_funct_1('#skF_5'(A_13, B_14, C_15, D_37)) | k5_partfun1(A_13, B_14, C_15)=D_37 | ~m1_subset_1(C_15, k1_zfmisc_1(k2_zfmisc_1(A_13, B_14))) | ~v1_funct_1(C_15))), inference(cnfTransformation, [status(thm)], [f_72])).
% 15.38/6.31  tff(c_20333, plain, (~r1_partfun1('#skF_9', '#skF_5'('#skF_7', k1_tarski('#skF_8'), '#skF_9', k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_10'))) | ~v1_partfun1('#skF_5'('#skF_7', k1_tarski('#skF_8'), '#skF_9', k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_10')), '#skF_7') | ~m1_subset_1('#skF_5'('#skF_7', k1_tarski('#skF_8'), '#skF_9', k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_10')), k1_zfmisc_1(k2_zfmisc_1('#skF_7', k1_tarski('#skF_8')))) | ~v1_funct_1('#skF_5'('#skF_7', k1_tarski('#skF_8'), '#skF_9', k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_10'))) | k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_10')=k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_9') | ~m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_7', k1_tarski('#skF_8')))) | ~v1_funct_1('#skF_9') | ~r1_partfun1('#skF_10', '#skF_3'('#skF_7', k1_tarski('#skF_8'), '#skF_9', k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_10'))) | ~m1_subset_1('#skF_10', k1_zfmisc_1(k2_zfmisc_1('#skF_7', k1_tarski('#skF_8')))) | ~v1_funct_1('#skF_10')), inference(resolution, [status(thm)], [c_20327, c_40])).
% 15.38/6.31  tff(c_20342, plain, (k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_10')=k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_9') | ~r1_partfun1('#skF_10', '#skF_3'('#skF_7', k1_tarski('#skF_8'), '#skF_9', k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_74, c_82, c_80, c_11308, c_11302, c_11304, c_20276, c_20333])).
% 15.38/6.31  tff(c_20343, plain, (~r1_partfun1('#skF_10', '#skF_3'('#skF_7', k1_tarski('#skF_8'), '#skF_9', k5_partfun1('#skF_7', k1_tarski('#skF_8'), '#skF_10')))), inference(negUnitSimplification, [status(thm)], [c_19516, c_20342])).
% 15.38/6.31  tff(c_20347, plain, (~m1_subset_1('#skF_10', k1_zfmisc_1(k2_zfmisc_1('#skF_7', k1_tarski('#skF_8')))) | ~v1_funct_1('#skF_10')), inference(resolution, [status(thm)], [c_20070, c_20343])).
% 15.38/6.31  tff(c_20351, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_78, c_74, c_20347])).
% 15.38/6.31  tff(c_20352, plain, (k1_tarski('#skF_8')=k1_xboole_0), inference(splitRight, [status(thm)], [c_185])).
% 15.38/6.31  tff(c_24, plain, (![A_11, B_12]: (k2_zfmisc_1(A_11, k1_tarski(B_12))!=k1_xboole_0 | k1_xboole_0=A_11)), inference(cnfTransformation, [status(thm)], [f_51])).
% 15.38/6.31  tff(c_20362, plain, (![A_11]: (k2_zfmisc_1(A_11, k1_xboole_0)!=k1_xboole_0 | k1_xboole_0=A_11)), inference(superposition, [status(thm), theory('equality')], [c_20352, c_24])).
% 15.38/6.31  tff(c_20374, plain, (![A_11]: (k1_xboole_0=A_11)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_20362])).
% 15.38/6.31  tff(c_20354, plain, (k5_partfun1('#skF_7', k1_xboole_0, '#skF_9')!=k1_tarski('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_20352, c_72])).
% 15.38/6.31  tff(c_20711, plain, (k1_tarski('#skF_10')!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_20374, c_20354])).
% 15.38/6.31  tff(c_20831, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_20374, c_20711])).
% 15.38/6.31  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.38/6.31  
% 15.38/6.31  Inference rules
% 15.38/6.31  ----------------------
% 15.38/6.31  #Ref     : 0
% 15.38/6.31  #Sup     : 4433
% 15.38/6.31  #Fact    : 4
% 15.38/6.31  #Define  : 0
% 15.38/6.31  #Split   : 15
% 15.38/6.31  #Chain   : 0
% 15.38/6.31  #Close   : 0
% 15.38/6.31  
% 15.38/6.31  Ordering : KBO
% 15.38/6.31  
% 15.38/6.31  Simplification rules
% 15.38/6.31  ----------------------
% 15.38/6.31  #Subsume      : 409
% 15.38/6.31  #Demod        : 3725
% 15.38/6.31  #Tautology    : 951
% 15.38/6.31  #SimpNegUnit  : 129
% 15.38/6.31  #BackRed      : 181
% 15.38/6.31  
% 15.38/6.31  #Partial instantiations: 310
% 15.38/6.31  #Strategies tried      : 1
% 15.38/6.31  
% 15.38/6.31  Timing (in seconds)
% 15.38/6.31  ----------------------
% 15.38/6.32  Preprocessing        : 0.37
% 15.38/6.32  Parsing              : 0.18
% 15.38/6.32  CNF conversion       : 0.03
% 15.38/6.32  Main loop            : 5.14
% 15.38/6.32  Inferencing          : 1.55
% 15.38/6.32  Reduction            : 1.54
% 15.38/6.32  Demodulation         : 1.11
% 15.38/6.32  BG Simplification    : 0.19
% 15.38/6.32  Subsumption          : 1.50
% 15.38/6.32  Abstraction          : 0.31
% 15.38/6.32  MUC search           : 0.00
% 15.38/6.32  Cooper               : 0.00
% 15.38/6.32  Total                : 5.59
% 15.38/6.32  Index Insertion      : 0.00
% 15.38/6.32  Index Deletion       : 0.00
% 15.38/6.32  Index Matching       : 0.00
% 15.38/6.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
