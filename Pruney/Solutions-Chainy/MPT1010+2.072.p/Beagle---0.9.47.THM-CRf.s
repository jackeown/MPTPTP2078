%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:15 EST 2020

% Result     : Theorem 48.65s
% Output     : CNFRefutation 48.86s
% Verified   : 
% Statistics : Number of formulae       :  169 (2327 expanded)
%              Number of leaves         :   43 ( 805 expanded)
%              Depth                    :   13
%              Number of atoms          :  274 (5706 expanded)
%              Number of equality atoms :   97 (2206 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k3_mcart_1 > k1_relset_1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k3_tarski > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_4 > #skF_7 > #skF_3 > #skF_6 > #skF_9 > #skF_8 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_5',type,(
    '#skF_5': $i > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_mcart_1,type,(
    k3_mcart_1: ( $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_134,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,k1_tarski(B))
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
       => ( r2_hidden(C,A)
         => k1_funct_1(D,C) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_2)).

tff(f_85,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_89,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_123,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( ( B = k1_xboole_0
           => A = k1_xboole_0 )
         => ( v1_funct_2(C,A,B)
          <=> A = k1_relset_1(A,B,C) ) )
        & ( B = k1_xboole_0
         => ( A = k1_xboole_0
            | ( v1_funct_2(C,A,B)
            <=> C = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_76,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_funct_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_49,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,k1_tarski(D)))
    <=> ( r2_hidden(A,C)
        & B = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t129_zfmisc_1)).

tff(f_51,axiom,(
    ! [A] : k3_tarski(k1_tarski(A)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_zfmisc_1)).

tff(f_105,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D,E] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k3_mcart_1(C,D,E) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_mcart_1)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( B = k3_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] :
              ( r2_hidden(C,D)
              & r2_hidden(D,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tarski)).

tff(f_81,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_70,plain,(
    k1_funct_1('#skF_9','#skF_8') != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_72,plain,(
    r2_hidden('#skF_8','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_74,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_6',k1_tarski('#skF_7')))) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_124,plain,(
    ! [C_75,A_76,B_77] :
      ( v1_relat_1(C_75)
      | ~ m1_subset_1(C_75,k1_zfmisc_1(k2_zfmisc_1(A_76,B_77))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_128,plain,(
    v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_74,c_124])).

tff(c_78,plain,(
    v1_funct_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_76,plain,(
    v1_funct_2('#skF_9','#skF_6',k1_tarski('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_378,plain,(
    ! [A_140,B_141,C_142] :
      ( k1_relset_1(A_140,B_141,C_142) = k1_relat_1(C_142)
      | ~ m1_subset_1(C_142,k1_zfmisc_1(k2_zfmisc_1(A_140,B_141))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_382,plain,(
    k1_relset_1('#skF_6',k1_tarski('#skF_7'),'#skF_9') = k1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_74,c_378])).

tff(c_192813,plain,(
    ! [B_5271,A_5272,C_5273] :
      ( k1_xboole_0 = B_5271
      | k1_relset_1(A_5272,B_5271,C_5273) = A_5272
      | ~ v1_funct_2(C_5273,A_5272,B_5271)
      | ~ m1_subset_1(C_5273,k1_zfmisc_1(k2_zfmisc_1(A_5272,B_5271))) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_192816,plain,
    ( k1_tarski('#skF_7') = k1_xboole_0
    | k1_relset_1('#skF_6',k1_tarski('#skF_7'),'#skF_9') = '#skF_6'
    | ~ v1_funct_2('#skF_9','#skF_6',k1_tarski('#skF_7')) ),
    inference(resolution,[status(thm)],[c_74,c_192813])).

tff(c_192819,plain,
    ( k1_tarski('#skF_7') = k1_xboole_0
    | k1_relat_1('#skF_9') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_382,c_192816])).

tff(c_192820,plain,(
    k1_relat_1('#skF_9') = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_192819])).

tff(c_1259,plain,(
    ! [B_226,A_227] :
      ( r2_hidden(k4_tarski(B_226,k1_funct_1(A_227,B_226)),A_227)
      | ~ r2_hidden(B_226,k1_relat_1(A_227))
      | ~ v1_funct_1(A_227)
      | ~ v1_relat_1(A_227) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_36,plain,(
    ! [C_35,A_32,B_33] :
      ( r2_hidden(C_35,A_32)
      | ~ r2_hidden(C_35,B_33)
      | ~ m1_subset_1(B_33,k1_zfmisc_1(A_32)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_205148,plain,(
    ! [B_5623,A_5624,A_5625] :
      ( r2_hidden(k4_tarski(B_5623,k1_funct_1(A_5624,B_5623)),A_5625)
      | ~ m1_subset_1(A_5624,k1_zfmisc_1(A_5625))
      | ~ r2_hidden(B_5623,k1_relat_1(A_5624))
      | ~ v1_funct_1(A_5624)
      | ~ v1_relat_1(A_5624) ) ),
    inference(resolution,[status(thm)],[c_1259,c_36])).

tff(c_30,plain,(
    ! [D_30,B_28,A_27,C_29] :
      ( D_30 = B_28
      | ~ r2_hidden(k4_tarski(A_27,B_28),k2_zfmisc_1(C_29,k1_tarski(D_30))) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_233173,plain,(
    ! [A_6380,B_6381,D_6382,C_6383] :
      ( k1_funct_1(A_6380,B_6381) = D_6382
      | ~ m1_subset_1(A_6380,k1_zfmisc_1(k2_zfmisc_1(C_6383,k1_tarski(D_6382))))
      | ~ r2_hidden(B_6381,k1_relat_1(A_6380))
      | ~ v1_funct_1(A_6380)
      | ~ v1_relat_1(A_6380) ) ),
    inference(resolution,[status(thm)],[c_205148,c_30])).

tff(c_233177,plain,(
    ! [B_6381] :
      ( k1_funct_1('#skF_9',B_6381) = '#skF_7'
      | ~ r2_hidden(B_6381,k1_relat_1('#skF_9'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_74,c_233173])).

tff(c_233181,plain,(
    ! [B_6384] :
      ( k1_funct_1('#skF_9',B_6384) = '#skF_7'
      | ~ r2_hidden(B_6384,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_78,c_192820,c_233177])).

tff(c_233310,plain,(
    k1_funct_1('#skF_9','#skF_8') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_72,c_233181])).

tff(c_233350,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_233310])).

tff(c_233351,plain,(
    k1_tarski('#skF_7') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_192819])).

tff(c_34,plain,(
    ! [A_31] : k3_tarski(k1_tarski(A_31)) = A_31 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_233430,plain,(
    k3_tarski(k1_xboole_0) = '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_233351,c_34])).

tff(c_52,plain,(
    ! [A_49] :
      ( r2_hidden('#skF_5'(A_49),A_49)
      | k1_xboole_0 = A_49 ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_247,plain,(
    ! [A_115,C_116] :
      ( r2_hidden('#skF_4'(A_115,k3_tarski(A_115),C_116),A_115)
      | ~ r2_hidden(C_116,k3_tarski(A_115)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_46,plain,(
    ! [B_42,A_41] :
      ( ~ r1_tarski(B_42,A_41)
      | ~ r2_hidden(A_41,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_368,plain,(
    ! [A_138,C_139] :
      ( ~ r1_tarski(A_138,'#skF_4'(A_138,k3_tarski(A_138),C_139))
      | ~ r2_hidden(C_139,k3_tarski(A_138)) ) ),
    inference(resolution,[status(thm)],[c_247,c_46])).

tff(c_383,plain,(
    ! [C_143] : ~ r2_hidden(C_143,k3_tarski(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_2,c_368])).

tff(c_404,plain,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_52,c_383])).

tff(c_233445,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_233430,c_404])).

tff(c_233355,plain,(
    v1_funct_2('#skF_9','#skF_6',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_233351,c_76])).

tff(c_233495,plain,(
    v1_funct_2('#skF_9','#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_233445,c_233355])).

tff(c_233354,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_6',k1_xboole_0))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_233351,c_74])).

tff(c_233637,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_233445,c_233354])).

tff(c_60,plain,(
    ! [C_65,A_63] :
      ( k1_xboole_0 = C_65
      | ~ v1_funct_2(C_65,A_63,k1_xboole_0)
      | k1_xboole_0 = A_63
      | ~ m1_subset_1(C_65,k1_zfmisc_1(k2_zfmisc_1(A_63,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_247971,plain,(
    ! [C_6853,A_6854] :
      ( C_6853 = '#skF_7'
      | ~ v1_funct_2(C_6853,A_6854,'#skF_7')
      | A_6854 = '#skF_7'
      | ~ m1_subset_1(C_6853,k1_zfmisc_1(k2_zfmisc_1(A_6854,'#skF_7'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_233445,c_233445,c_233445,c_233445,c_60])).

tff(c_247974,plain,
    ( '#skF_7' = '#skF_9'
    | ~ v1_funct_2('#skF_9','#skF_6','#skF_7')
    | '#skF_7' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_233637,c_247971])).

tff(c_247977,plain,
    ( '#skF_7' = '#skF_9'
    | '#skF_7' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_233495,c_247974])).

tff(c_247978,plain,(
    '#skF_7' = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_247977])).

tff(c_377,plain,(
    ! [C_139] : ~ r2_hidden(C_139,k3_tarski(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_2,c_368])).

tff(c_405,plain,(
    ! [C_139] : ~ r2_hidden(C_139,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_404,c_377])).

tff(c_263,plain,(
    ! [A_31,C_116] :
      ( r2_hidden('#skF_4'(k1_tarski(A_31),A_31,C_116),k1_tarski(A_31))
      | ~ r2_hidden(C_116,k3_tarski(k1_tarski(A_31))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_247])).

tff(c_269,plain,(
    ! [A_31,C_116] :
      ( r2_hidden('#skF_4'(k1_tarski(A_31),A_31,C_116),k1_tarski(A_31))
      | ~ r2_hidden(C_116,A_31) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_263])).

tff(c_233410,plain,(
    ! [C_116] :
      ( r2_hidden('#skF_4'(k1_xboole_0,'#skF_7',C_116),k1_tarski('#skF_7'))
      | ~ r2_hidden(C_116,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_233351,c_269])).

tff(c_233440,plain,(
    ! [C_116] :
      ( r2_hidden('#skF_4'(k1_xboole_0,'#skF_7',C_116),k1_xboole_0)
      | ~ r2_hidden(C_116,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_233351,c_233410])).

tff(c_233441,plain,(
    ! [C_116] : ~ r2_hidden(C_116,'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_405,c_233440])).

tff(c_248182,plain,(
    ! [C_116] : ~ r2_hidden(C_116,'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_247978,c_233441])).

tff(c_248262,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_248182,c_72])).

tff(c_248263,plain,(
    '#skF_7' = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_247977])).

tff(c_2780,plain,(
    ! [B_330,A_331,C_332] :
      ( k1_xboole_0 = B_330
      | k1_relset_1(A_331,B_330,C_332) = A_331
      | ~ v1_funct_2(C_332,A_331,B_330)
      | ~ m1_subset_1(C_332,k1_zfmisc_1(k2_zfmisc_1(A_331,B_330))) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_2783,plain,
    ( k1_tarski('#skF_7') = k1_xboole_0
    | k1_relset_1('#skF_6',k1_tarski('#skF_7'),'#skF_9') = '#skF_6'
    | ~ v1_funct_2('#skF_9','#skF_6',k1_tarski('#skF_7')) ),
    inference(resolution,[status(thm)],[c_74,c_2780])).

tff(c_2786,plain,
    ( k1_tarski('#skF_7') = k1_xboole_0
    | k1_relat_1('#skF_9') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_382,c_2783])).

tff(c_2787,plain,(
    k1_relat_1('#skF_9') = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_2786])).

tff(c_18993,plain,(
    ! [B_753,A_754,A_755] :
      ( r2_hidden(k4_tarski(B_753,k1_funct_1(A_754,B_753)),A_755)
      | ~ m1_subset_1(A_754,k1_zfmisc_1(A_755))
      | ~ r2_hidden(B_753,k1_relat_1(A_754))
      | ~ v1_funct_1(A_754)
      | ~ v1_relat_1(A_754) ) ),
    inference(resolution,[status(thm)],[c_1259,c_36])).

tff(c_41104,plain,(
    ! [A_1282,B_1283,D_1284,C_1285] :
      ( k1_funct_1(A_1282,B_1283) = D_1284
      | ~ m1_subset_1(A_1282,k1_zfmisc_1(k2_zfmisc_1(C_1285,k1_tarski(D_1284))))
      | ~ r2_hidden(B_1283,k1_relat_1(A_1282))
      | ~ v1_funct_1(A_1282)
      | ~ v1_relat_1(A_1282) ) ),
    inference(resolution,[status(thm)],[c_18993,c_30])).

tff(c_41108,plain,(
    ! [B_1283] :
      ( k1_funct_1('#skF_9',B_1283) = '#skF_7'
      | ~ r2_hidden(B_1283,k1_relat_1('#skF_9'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_74,c_41104])).

tff(c_41112,plain,(
    ! [B_1286] :
      ( k1_funct_1('#skF_9',B_1286) = '#skF_7'
      | ~ r2_hidden(B_1286,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_78,c_2787,c_41108])).

tff(c_41238,plain,(
    k1_funct_1('#skF_9','#skF_8') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_72,c_41112])).

tff(c_41276,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_41238])).

tff(c_41277,plain,(
    k1_tarski('#skF_7') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_2786])).

tff(c_41382,plain,(
    k3_tarski(k1_xboole_0) = '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_41277,c_34])).

tff(c_41402,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_41382,c_404])).

tff(c_41283,plain,(
    v1_funct_2('#skF_9','#skF_6',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_41277,c_76])).

tff(c_41496,plain,(
    v1_funct_2('#skF_9','#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_41402,c_41283])).

tff(c_41282,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_6',k1_xboole_0))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_41277,c_74])).

tff(c_41659,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_41402,c_41282])).

tff(c_56308,plain,(
    ! [C_1745,A_1746] :
      ( C_1745 = '#skF_7'
      | ~ v1_funct_2(C_1745,A_1746,'#skF_7')
      | A_1746 = '#skF_7'
      | ~ m1_subset_1(C_1745,k1_zfmisc_1(k2_zfmisc_1(A_1746,'#skF_7'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_41402,c_41402,c_41402,c_41402,c_60])).

tff(c_56311,plain,
    ( '#skF_7' = '#skF_9'
    | ~ v1_funct_2('#skF_9','#skF_6','#skF_7')
    | '#skF_7' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_41659,c_56308])).

tff(c_56314,plain,
    ( '#skF_7' = '#skF_9'
    | '#skF_7' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_41496,c_56311])).

tff(c_56315,plain,(
    '#skF_7' = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_56314])).

tff(c_41362,plain,(
    ! [C_116] :
      ( r2_hidden('#skF_4'(k1_xboole_0,'#skF_7',C_116),k1_tarski('#skF_7'))
      | ~ r2_hidden(C_116,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_41277,c_269])).

tff(c_41397,plain,(
    ! [C_116] :
      ( r2_hidden('#skF_4'(k1_xboole_0,'#skF_7',C_116),k1_xboole_0)
      | ~ r2_hidden(C_116,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_41277,c_41362])).

tff(c_41398,plain,(
    ! [C_116] : ~ r2_hidden(C_116,'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_405,c_41397])).

tff(c_56526,plain,(
    ! [C_116] : ~ r2_hidden(C_116,'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56315,c_41398])).

tff(c_56596,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56526,c_72])).

tff(c_56597,plain,(
    '#skF_7' = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_56314])).

tff(c_1314,plain,(
    ! [B_226] :
      ( ~ r2_hidden(B_226,k1_relat_1(k1_xboole_0))
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_1259,c_405])).

tff(c_1324,plain,(
    ~ v1_relat_1(k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_1314])).

tff(c_41537,plain,(
    ~ v1_relat_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_41402,c_1324])).

tff(c_56810,plain,(
    ~ v1_relat_1('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56597,c_41537])).

tff(c_56815,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_56810])).

tff(c_56817,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_1314])).

tff(c_98705,plain,(
    ! [B_2756,A_2757,C_2758] :
      ( k1_xboole_0 = B_2756
      | k1_relset_1(A_2757,B_2756,C_2758) = A_2757
      | ~ v1_funct_2(C_2758,A_2757,B_2756)
      | ~ m1_subset_1(C_2758,k1_zfmisc_1(k2_zfmisc_1(A_2757,B_2756))) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_98708,plain,
    ( k1_tarski('#skF_7') = k1_xboole_0
    | k1_relset_1('#skF_6',k1_tarski('#skF_7'),'#skF_9') = '#skF_6'
    | ~ v1_funct_2('#skF_9','#skF_6',k1_tarski('#skF_7')) ),
    inference(resolution,[status(thm)],[c_74,c_98705])).

tff(c_98711,plain,
    ( k1_tarski('#skF_7') = k1_xboole_0
    | k1_relat_1('#skF_9') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_382,c_98708])).

tff(c_98712,plain,(
    k1_relat_1('#skF_9') = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_98711])).

tff(c_114875,plain,(
    ! [B_3212,A_3213,A_3214] :
      ( r2_hidden(k4_tarski(B_3212,k1_funct_1(A_3213,B_3212)),A_3214)
      | ~ m1_subset_1(A_3213,k1_zfmisc_1(A_3214))
      | ~ r2_hidden(B_3212,k1_relat_1(A_3213))
      | ~ v1_funct_1(A_3213)
      | ~ v1_relat_1(A_3213) ) ),
    inference(resolution,[status(thm)],[c_1259,c_36])).

tff(c_139015,plain,(
    ! [A_3700,B_3701,D_3702,C_3703] :
      ( k1_funct_1(A_3700,B_3701) = D_3702
      | ~ m1_subset_1(A_3700,k1_zfmisc_1(k2_zfmisc_1(C_3703,k1_tarski(D_3702))))
      | ~ r2_hidden(B_3701,k1_relat_1(A_3700))
      | ~ v1_funct_1(A_3700)
      | ~ v1_relat_1(A_3700) ) ),
    inference(resolution,[status(thm)],[c_114875,c_30])).

tff(c_139019,plain,(
    ! [B_3701] :
      ( k1_funct_1('#skF_9',B_3701) = '#skF_7'
      | ~ r2_hidden(B_3701,k1_relat_1('#skF_9'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_74,c_139015])).

tff(c_139023,plain,(
    ! [B_3704] :
      ( k1_funct_1('#skF_9',B_3704) = '#skF_7'
      | ~ r2_hidden(B_3704,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_78,c_98712,c_139019])).

tff(c_139127,plain,(
    k1_funct_1('#skF_9','#skF_8') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_72,c_139023])).

tff(c_139162,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_139127])).

tff(c_139163,plain,(
    k1_tarski('#skF_7') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_98711])).

tff(c_139245,plain,(
    k3_tarski(k1_xboole_0) = '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_139163,c_34])).

tff(c_139261,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_139245,c_404])).

tff(c_139167,plain,(
    v1_funct_2('#skF_9','#skF_6',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_139163,c_76])).

tff(c_139311,plain,(
    v1_funct_2('#skF_9','#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_139261,c_139167])).

tff(c_139166,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_6',k1_xboole_0))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_139163,c_74])).

tff(c_139434,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_139261,c_139166])).

tff(c_154442,plain,(
    ! [C_4169,A_4170] :
      ( C_4169 = '#skF_7'
      | ~ v1_funct_2(C_4169,A_4170,'#skF_7')
      | A_4170 = '#skF_7'
      | ~ m1_subset_1(C_4169,k1_zfmisc_1(k2_zfmisc_1(A_4170,'#skF_7'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_139261,c_139261,c_139261,c_139261,c_60])).

tff(c_154445,plain,
    ( '#skF_7' = '#skF_9'
    | ~ v1_funct_2('#skF_9','#skF_6','#skF_7')
    | '#skF_7' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_139434,c_154442])).

tff(c_154448,plain,
    ( '#skF_7' = '#skF_9'
    | '#skF_7' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_139311,c_154445])).

tff(c_154449,plain,(
    '#skF_7' = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_154448])).

tff(c_139225,plain,(
    ! [C_116] :
      ( r2_hidden('#skF_4'(k1_xboole_0,'#skF_7',C_116),k1_tarski('#skF_7'))
      | ~ r2_hidden(C_116,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_139163,c_269])).

tff(c_139256,plain,(
    ! [C_116] :
      ( r2_hidden('#skF_4'(k1_xboole_0,'#skF_7',C_116),k1_xboole_0)
      | ~ r2_hidden(C_116,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_139163,c_139225])).

tff(c_139257,plain,(
    ! [C_116] : ~ r2_hidden(C_116,'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_405,c_139256])).

tff(c_154650,plain,(
    ! [C_116] : ~ r2_hidden(C_116,'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_154449,c_139257])).

tff(c_154666,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_154650,c_72])).

tff(c_154667,plain,(
    '#skF_7' = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_154448])).

tff(c_56816,plain,(
    ! [B_226] :
      ( ~ v1_funct_1(k1_xboole_0)
      | ~ r2_hidden(B_226,k1_relat_1(k1_xboole_0)) ) ),
    inference(splitRight,[status(thm)],[c_1314])).

tff(c_56819,plain,(
    ~ v1_funct_1(k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_56816])).

tff(c_139329,plain,(
    ~ v1_funct_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_139261,c_56819])).

tff(c_154870,plain,(
    ~ v1_funct_1('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_154667,c_139329])).

tff(c_154876,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_154870])).

tff(c_154878,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_56816])).

tff(c_44,plain,(
    ! [A_36,B_39] :
      ( k1_funct_1(A_36,B_39) = k1_xboole_0
      | r2_hidden(B_39,k1_relat_1(A_36))
      | ~ v1_funct_1(A_36)
      | ~ v1_relat_1(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_154899,plain,(
    ! [B_4176] : ~ r2_hidden(B_4176,k1_relat_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_56816])).

tff(c_154939,plain,(
    ! [B_39] :
      ( k1_funct_1(k1_xboole_0,B_39) = k1_xboole_0
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_44,c_154899])).

tff(c_154963,plain,(
    ! [B_39] : k1_funct_1(k1_xboole_0,B_39) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_56817,c_154878,c_154939])).

tff(c_233505,plain,(
    ! [B_39] : k1_funct_1('#skF_7',B_39) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_233445,c_233445,c_154963])).

tff(c_248530,plain,(
    ! [B_39] : k1_funct_1('#skF_9',B_39) = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_248263,c_248263,c_233505])).

tff(c_248543,plain,(
    k1_funct_1('#skF_9','#skF_8') != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_248263,c_70])).

tff(c_248813,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_248530,c_248543])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.32  % Computer   : n002.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % DateTime   : Tue Dec  1 17:12:51 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.17/0.32  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 48.65/37.39  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 48.65/37.40  
% 48.65/37.40  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 48.65/37.40  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k3_mcart_1 > k1_relset_1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k3_tarski > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_4 > #skF_7 > #skF_3 > #skF_6 > #skF_9 > #skF_8 > #skF_2 > #skF_1
% 48.65/37.40  
% 48.65/37.40  %Foreground sorts:
% 48.65/37.40  
% 48.65/37.40  
% 48.65/37.40  %Background operators:
% 48.65/37.40  
% 48.65/37.40  
% 48.65/37.40  %Foreground operators:
% 48.65/37.40  tff('#skF_5', type, '#skF_5': $i > $i).
% 48.65/37.40  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 48.65/37.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 48.65/37.40  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 48.65/37.40  tff(k1_tarski, type, k1_tarski: $i > $i).
% 48.65/37.40  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 48.65/37.40  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 48.65/37.40  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 48.65/37.40  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 48.65/37.40  tff('#skF_7', type, '#skF_7': $i).
% 48.65/37.40  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 48.65/37.40  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 48.65/37.40  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 48.65/37.40  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 48.65/37.40  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 48.65/37.40  tff('#skF_6', type, '#skF_6': $i).
% 48.65/37.40  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 48.65/37.40  tff('#skF_9', type, '#skF_9': $i).
% 48.65/37.40  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 48.65/37.40  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 48.65/37.40  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 48.65/37.40  tff('#skF_8', type, '#skF_8': $i).
% 48.65/37.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 48.65/37.40  tff(k3_tarski, type, k3_tarski: $i > $i).
% 48.65/37.40  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 48.65/37.40  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 48.65/37.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 48.65/37.40  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 48.65/37.40  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 48.65/37.40  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 48.65/37.40  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 48.65/37.40  
% 48.86/37.43  tff(f_134, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_funct_2)).
% 48.86/37.43  tff(f_85, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 48.86/37.43  tff(f_89, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 48.86/37.43  tff(f_123, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 48.86/37.43  tff(f_76, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: ((r2_hidden(B, k1_relat_1(A)) => ((C = k1_funct_1(A, B)) <=> r2_hidden(k4_tarski(B, C), A))) & (~r2_hidden(B, k1_relat_1(A)) => ((C = k1_funct_1(A, B)) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_funct_1)).
% 48.86/37.43  tff(f_58, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 48.86/37.43  tff(f_49, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, k1_tarski(D))) <=> (r2_hidden(A, C) & (B = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t129_zfmisc_1)).
% 48.86/37.43  tff(f_51, axiom, (![A]: (k3_tarski(k1_tarski(A)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_zfmisc_1)).
% 48.86/37.43  tff(f_105, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k3_mcart_1(C, D, E)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_mcart_1)).
% 48.86/37.43  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 48.86/37.43  tff(f_43, axiom, (![A, B]: ((B = k3_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(C, D) & r2_hidden(D, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tarski)).
% 48.86/37.43  tff(f_81, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 48.86/37.43  tff(c_70, plain, (k1_funct_1('#skF_9', '#skF_8')!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_134])).
% 48.86/37.43  tff(c_72, plain, (r2_hidden('#skF_8', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_134])).
% 48.86/37.43  tff(c_74, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_6', k1_tarski('#skF_7'))))), inference(cnfTransformation, [status(thm)], [f_134])).
% 48.86/37.43  tff(c_124, plain, (![C_75, A_76, B_77]: (v1_relat_1(C_75) | ~m1_subset_1(C_75, k1_zfmisc_1(k2_zfmisc_1(A_76, B_77))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 48.86/37.43  tff(c_128, plain, (v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_74, c_124])).
% 48.86/37.43  tff(c_78, plain, (v1_funct_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_134])).
% 48.86/37.43  tff(c_76, plain, (v1_funct_2('#skF_9', '#skF_6', k1_tarski('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_134])).
% 48.86/37.43  tff(c_378, plain, (![A_140, B_141, C_142]: (k1_relset_1(A_140, B_141, C_142)=k1_relat_1(C_142) | ~m1_subset_1(C_142, k1_zfmisc_1(k2_zfmisc_1(A_140, B_141))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 48.86/37.43  tff(c_382, plain, (k1_relset_1('#skF_6', k1_tarski('#skF_7'), '#skF_9')=k1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_74, c_378])).
% 48.86/37.43  tff(c_192813, plain, (![B_5271, A_5272, C_5273]: (k1_xboole_0=B_5271 | k1_relset_1(A_5272, B_5271, C_5273)=A_5272 | ~v1_funct_2(C_5273, A_5272, B_5271) | ~m1_subset_1(C_5273, k1_zfmisc_1(k2_zfmisc_1(A_5272, B_5271))))), inference(cnfTransformation, [status(thm)], [f_123])).
% 48.86/37.43  tff(c_192816, plain, (k1_tarski('#skF_7')=k1_xboole_0 | k1_relset_1('#skF_6', k1_tarski('#skF_7'), '#skF_9')='#skF_6' | ~v1_funct_2('#skF_9', '#skF_6', k1_tarski('#skF_7'))), inference(resolution, [status(thm)], [c_74, c_192813])).
% 48.86/37.43  tff(c_192819, plain, (k1_tarski('#skF_7')=k1_xboole_0 | k1_relat_1('#skF_9')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_76, c_382, c_192816])).
% 48.86/37.43  tff(c_192820, plain, (k1_relat_1('#skF_9')='#skF_6'), inference(splitLeft, [status(thm)], [c_192819])).
% 48.86/37.43  tff(c_1259, plain, (![B_226, A_227]: (r2_hidden(k4_tarski(B_226, k1_funct_1(A_227, B_226)), A_227) | ~r2_hidden(B_226, k1_relat_1(A_227)) | ~v1_funct_1(A_227) | ~v1_relat_1(A_227))), inference(cnfTransformation, [status(thm)], [f_76])).
% 48.86/37.43  tff(c_36, plain, (![C_35, A_32, B_33]: (r2_hidden(C_35, A_32) | ~r2_hidden(C_35, B_33) | ~m1_subset_1(B_33, k1_zfmisc_1(A_32)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 48.86/37.43  tff(c_205148, plain, (![B_5623, A_5624, A_5625]: (r2_hidden(k4_tarski(B_5623, k1_funct_1(A_5624, B_5623)), A_5625) | ~m1_subset_1(A_5624, k1_zfmisc_1(A_5625)) | ~r2_hidden(B_5623, k1_relat_1(A_5624)) | ~v1_funct_1(A_5624) | ~v1_relat_1(A_5624))), inference(resolution, [status(thm)], [c_1259, c_36])).
% 48.86/37.43  tff(c_30, plain, (![D_30, B_28, A_27, C_29]: (D_30=B_28 | ~r2_hidden(k4_tarski(A_27, B_28), k2_zfmisc_1(C_29, k1_tarski(D_30))))), inference(cnfTransformation, [status(thm)], [f_49])).
% 48.86/37.43  tff(c_233173, plain, (![A_6380, B_6381, D_6382, C_6383]: (k1_funct_1(A_6380, B_6381)=D_6382 | ~m1_subset_1(A_6380, k1_zfmisc_1(k2_zfmisc_1(C_6383, k1_tarski(D_6382)))) | ~r2_hidden(B_6381, k1_relat_1(A_6380)) | ~v1_funct_1(A_6380) | ~v1_relat_1(A_6380))), inference(resolution, [status(thm)], [c_205148, c_30])).
% 48.86/37.43  tff(c_233177, plain, (![B_6381]: (k1_funct_1('#skF_9', B_6381)='#skF_7' | ~r2_hidden(B_6381, k1_relat_1('#skF_9')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_74, c_233173])).
% 48.86/37.43  tff(c_233181, plain, (![B_6384]: (k1_funct_1('#skF_9', B_6384)='#skF_7' | ~r2_hidden(B_6384, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_128, c_78, c_192820, c_233177])).
% 48.86/37.43  tff(c_233310, plain, (k1_funct_1('#skF_9', '#skF_8')='#skF_7'), inference(resolution, [status(thm)], [c_72, c_233181])).
% 48.86/37.43  tff(c_233350, plain, $false, inference(negUnitSimplification, [status(thm)], [c_70, c_233310])).
% 48.86/37.43  tff(c_233351, plain, (k1_tarski('#skF_7')=k1_xboole_0), inference(splitRight, [status(thm)], [c_192819])).
% 48.86/37.43  tff(c_34, plain, (![A_31]: (k3_tarski(k1_tarski(A_31))=A_31)), inference(cnfTransformation, [status(thm)], [f_51])).
% 48.86/37.43  tff(c_233430, plain, (k3_tarski(k1_xboole_0)='#skF_7'), inference(superposition, [status(thm), theory('equality')], [c_233351, c_34])).
% 48.86/37.43  tff(c_52, plain, (![A_49]: (r2_hidden('#skF_5'(A_49), A_49) | k1_xboole_0=A_49)), inference(cnfTransformation, [status(thm)], [f_105])).
% 48.86/37.43  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 48.86/37.43  tff(c_247, plain, (![A_115, C_116]: (r2_hidden('#skF_4'(A_115, k3_tarski(A_115), C_116), A_115) | ~r2_hidden(C_116, k3_tarski(A_115)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 48.86/37.43  tff(c_46, plain, (![B_42, A_41]: (~r1_tarski(B_42, A_41) | ~r2_hidden(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_81])).
% 48.86/37.43  tff(c_368, plain, (![A_138, C_139]: (~r1_tarski(A_138, '#skF_4'(A_138, k3_tarski(A_138), C_139)) | ~r2_hidden(C_139, k3_tarski(A_138)))), inference(resolution, [status(thm)], [c_247, c_46])).
% 48.86/37.43  tff(c_383, plain, (![C_143]: (~r2_hidden(C_143, k3_tarski(k1_xboole_0)))), inference(resolution, [status(thm)], [c_2, c_368])).
% 48.86/37.43  tff(c_404, plain, (k3_tarski(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_52, c_383])).
% 48.86/37.43  tff(c_233445, plain, (k1_xboole_0='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_233430, c_404])).
% 48.86/37.43  tff(c_233355, plain, (v1_funct_2('#skF_9', '#skF_6', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_233351, c_76])).
% 48.86/37.43  tff(c_233495, plain, (v1_funct_2('#skF_9', '#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_233445, c_233355])).
% 48.86/37.43  tff(c_233354, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_6', k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_233351, c_74])).
% 48.86/37.43  tff(c_233637, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_233445, c_233354])).
% 48.86/37.43  tff(c_60, plain, (![C_65, A_63]: (k1_xboole_0=C_65 | ~v1_funct_2(C_65, A_63, k1_xboole_0) | k1_xboole_0=A_63 | ~m1_subset_1(C_65, k1_zfmisc_1(k2_zfmisc_1(A_63, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_123])).
% 48.86/37.43  tff(c_247971, plain, (![C_6853, A_6854]: (C_6853='#skF_7' | ~v1_funct_2(C_6853, A_6854, '#skF_7') | A_6854='#skF_7' | ~m1_subset_1(C_6853, k1_zfmisc_1(k2_zfmisc_1(A_6854, '#skF_7'))))), inference(demodulation, [status(thm), theory('equality')], [c_233445, c_233445, c_233445, c_233445, c_60])).
% 48.86/37.43  tff(c_247974, plain, ('#skF_7'='#skF_9' | ~v1_funct_2('#skF_9', '#skF_6', '#skF_7') | '#skF_7'='#skF_6'), inference(resolution, [status(thm)], [c_233637, c_247971])).
% 48.86/37.43  tff(c_247977, plain, ('#skF_7'='#skF_9' | '#skF_7'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_233495, c_247974])).
% 48.86/37.43  tff(c_247978, plain, ('#skF_7'='#skF_6'), inference(splitLeft, [status(thm)], [c_247977])).
% 48.86/37.43  tff(c_377, plain, (![C_139]: (~r2_hidden(C_139, k3_tarski(k1_xboole_0)))), inference(resolution, [status(thm)], [c_2, c_368])).
% 48.86/37.43  tff(c_405, plain, (![C_139]: (~r2_hidden(C_139, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_404, c_377])).
% 48.86/37.43  tff(c_263, plain, (![A_31, C_116]: (r2_hidden('#skF_4'(k1_tarski(A_31), A_31, C_116), k1_tarski(A_31)) | ~r2_hidden(C_116, k3_tarski(k1_tarski(A_31))))), inference(superposition, [status(thm), theory('equality')], [c_34, c_247])).
% 48.86/37.43  tff(c_269, plain, (![A_31, C_116]: (r2_hidden('#skF_4'(k1_tarski(A_31), A_31, C_116), k1_tarski(A_31)) | ~r2_hidden(C_116, A_31))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_263])).
% 48.86/37.43  tff(c_233410, plain, (![C_116]: (r2_hidden('#skF_4'(k1_xboole_0, '#skF_7', C_116), k1_tarski('#skF_7')) | ~r2_hidden(C_116, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_233351, c_269])).
% 48.86/37.43  tff(c_233440, plain, (![C_116]: (r2_hidden('#skF_4'(k1_xboole_0, '#skF_7', C_116), k1_xboole_0) | ~r2_hidden(C_116, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_233351, c_233410])).
% 48.86/37.43  tff(c_233441, plain, (![C_116]: (~r2_hidden(C_116, '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_405, c_233440])).
% 48.86/37.43  tff(c_248182, plain, (![C_116]: (~r2_hidden(C_116, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_247978, c_233441])).
% 48.86/37.43  tff(c_248262, plain, $false, inference(negUnitSimplification, [status(thm)], [c_248182, c_72])).
% 48.86/37.43  tff(c_248263, plain, ('#skF_7'='#skF_9'), inference(splitRight, [status(thm)], [c_247977])).
% 48.86/37.43  tff(c_2780, plain, (![B_330, A_331, C_332]: (k1_xboole_0=B_330 | k1_relset_1(A_331, B_330, C_332)=A_331 | ~v1_funct_2(C_332, A_331, B_330) | ~m1_subset_1(C_332, k1_zfmisc_1(k2_zfmisc_1(A_331, B_330))))), inference(cnfTransformation, [status(thm)], [f_123])).
% 48.86/37.43  tff(c_2783, plain, (k1_tarski('#skF_7')=k1_xboole_0 | k1_relset_1('#skF_6', k1_tarski('#skF_7'), '#skF_9')='#skF_6' | ~v1_funct_2('#skF_9', '#skF_6', k1_tarski('#skF_7'))), inference(resolution, [status(thm)], [c_74, c_2780])).
% 48.86/37.43  tff(c_2786, plain, (k1_tarski('#skF_7')=k1_xboole_0 | k1_relat_1('#skF_9')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_76, c_382, c_2783])).
% 48.86/37.43  tff(c_2787, plain, (k1_relat_1('#skF_9')='#skF_6'), inference(splitLeft, [status(thm)], [c_2786])).
% 48.86/37.43  tff(c_18993, plain, (![B_753, A_754, A_755]: (r2_hidden(k4_tarski(B_753, k1_funct_1(A_754, B_753)), A_755) | ~m1_subset_1(A_754, k1_zfmisc_1(A_755)) | ~r2_hidden(B_753, k1_relat_1(A_754)) | ~v1_funct_1(A_754) | ~v1_relat_1(A_754))), inference(resolution, [status(thm)], [c_1259, c_36])).
% 48.86/37.43  tff(c_41104, plain, (![A_1282, B_1283, D_1284, C_1285]: (k1_funct_1(A_1282, B_1283)=D_1284 | ~m1_subset_1(A_1282, k1_zfmisc_1(k2_zfmisc_1(C_1285, k1_tarski(D_1284)))) | ~r2_hidden(B_1283, k1_relat_1(A_1282)) | ~v1_funct_1(A_1282) | ~v1_relat_1(A_1282))), inference(resolution, [status(thm)], [c_18993, c_30])).
% 48.86/37.43  tff(c_41108, plain, (![B_1283]: (k1_funct_1('#skF_9', B_1283)='#skF_7' | ~r2_hidden(B_1283, k1_relat_1('#skF_9')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_74, c_41104])).
% 48.86/37.43  tff(c_41112, plain, (![B_1286]: (k1_funct_1('#skF_9', B_1286)='#skF_7' | ~r2_hidden(B_1286, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_128, c_78, c_2787, c_41108])).
% 48.86/37.43  tff(c_41238, plain, (k1_funct_1('#skF_9', '#skF_8')='#skF_7'), inference(resolution, [status(thm)], [c_72, c_41112])).
% 48.86/37.43  tff(c_41276, plain, $false, inference(negUnitSimplification, [status(thm)], [c_70, c_41238])).
% 48.86/37.43  tff(c_41277, plain, (k1_tarski('#skF_7')=k1_xboole_0), inference(splitRight, [status(thm)], [c_2786])).
% 48.86/37.43  tff(c_41382, plain, (k3_tarski(k1_xboole_0)='#skF_7'), inference(superposition, [status(thm), theory('equality')], [c_41277, c_34])).
% 48.86/37.43  tff(c_41402, plain, (k1_xboole_0='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_41382, c_404])).
% 48.86/37.43  tff(c_41283, plain, (v1_funct_2('#skF_9', '#skF_6', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_41277, c_76])).
% 48.86/37.43  tff(c_41496, plain, (v1_funct_2('#skF_9', '#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_41402, c_41283])).
% 48.86/37.43  tff(c_41282, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_6', k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_41277, c_74])).
% 48.86/37.43  tff(c_41659, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_41402, c_41282])).
% 48.86/37.43  tff(c_56308, plain, (![C_1745, A_1746]: (C_1745='#skF_7' | ~v1_funct_2(C_1745, A_1746, '#skF_7') | A_1746='#skF_7' | ~m1_subset_1(C_1745, k1_zfmisc_1(k2_zfmisc_1(A_1746, '#skF_7'))))), inference(demodulation, [status(thm), theory('equality')], [c_41402, c_41402, c_41402, c_41402, c_60])).
% 48.86/37.43  tff(c_56311, plain, ('#skF_7'='#skF_9' | ~v1_funct_2('#skF_9', '#skF_6', '#skF_7') | '#skF_7'='#skF_6'), inference(resolution, [status(thm)], [c_41659, c_56308])).
% 48.86/37.43  tff(c_56314, plain, ('#skF_7'='#skF_9' | '#skF_7'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_41496, c_56311])).
% 48.86/37.43  tff(c_56315, plain, ('#skF_7'='#skF_6'), inference(splitLeft, [status(thm)], [c_56314])).
% 48.86/37.43  tff(c_41362, plain, (![C_116]: (r2_hidden('#skF_4'(k1_xboole_0, '#skF_7', C_116), k1_tarski('#skF_7')) | ~r2_hidden(C_116, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_41277, c_269])).
% 48.86/37.43  tff(c_41397, plain, (![C_116]: (r2_hidden('#skF_4'(k1_xboole_0, '#skF_7', C_116), k1_xboole_0) | ~r2_hidden(C_116, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_41277, c_41362])).
% 48.86/37.43  tff(c_41398, plain, (![C_116]: (~r2_hidden(C_116, '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_405, c_41397])).
% 48.86/37.43  tff(c_56526, plain, (![C_116]: (~r2_hidden(C_116, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_56315, c_41398])).
% 48.86/37.43  tff(c_56596, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56526, c_72])).
% 48.86/37.43  tff(c_56597, plain, ('#skF_7'='#skF_9'), inference(splitRight, [status(thm)], [c_56314])).
% 48.86/37.43  tff(c_1314, plain, (![B_226]: (~r2_hidden(B_226, k1_relat_1(k1_xboole_0)) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_1259, c_405])).
% 48.86/37.43  tff(c_1324, plain, (~v1_relat_1(k1_xboole_0)), inference(splitLeft, [status(thm)], [c_1314])).
% 48.86/37.43  tff(c_41537, plain, (~v1_relat_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_41402, c_1324])).
% 48.86/37.43  tff(c_56810, plain, (~v1_relat_1('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_56597, c_41537])).
% 48.86/37.43  tff(c_56815, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_128, c_56810])).
% 48.86/37.43  tff(c_56817, plain, (v1_relat_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_1314])).
% 48.86/37.43  tff(c_98705, plain, (![B_2756, A_2757, C_2758]: (k1_xboole_0=B_2756 | k1_relset_1(A_2757, B_2756, C_2758)=A_2757 | ~v1_funct_2(C_2758, A_2757, B_2756) | ~m1_subset_1(C_2758, k1_zfmisc_1(k2_zfmisc_1(A_2757, B_2756))))), inference(cnfTransformation, [status(thm)], [f_123])).
% 48.86/37.43  tff(c_98708, plain, (k1_tarski('#skF_7')=k1_xboole_0 | k1_relset_1('#skF_6', k1_tarski('#skF_7'), '#skF_9')='#skF_6' | ~v1_funct_2('#skF_9', '#skF_6', k1_tarski('#skF_7'))), inference(resolution, [status(thm)], [c_74, c_98705])).
% 48.86/37.43  tff(c_98711, plain, (k1_tarski('#skF_7')=k1_xboole_0 | k1_relat_1('#skF_9')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_76, c_382, c_98708])).
% 48.86/37.43  tff(c_98712, plain, (k1_relat_1('#skF_9')='#skF_6'), inference(splitLeft, [status(thm)], [c_98711])).
% 48.86/37.43  tff(c_114875, plain, (![B_3212, A_3213, A_3214]: (r2_hidden(k4_tarski(B_3212, k1_funct_1(A_3213, B_3212)), A_3214) | ~m1_subset_1(A_3213, k1_zfmisc_1(A_3214)) | ~r2_hidden(B_3212, k1_relat_1(A_3213)) | ~v1_funct_1(A_3213) | ~v1_relat_1(A_3213))), inference(resolution, [status(thm)], [c_1259, c_36])).
% 48.86/37.43  tff(c_139015, plain, (![A_3700, B_3701, D_3702, C_3703]: (k1_funct_1(A_3700, B_3701)=D_3702 | ~m1_subset_1(A_3700, k1_zfmisc_1(k2_zfmisc_1(C_3703, k1_tarski(D_3702)))) | ~r2_hidden(B_3701, k1_relat_1(A_3700)) | ~v1_funct_1(A_3700) | ~v1_relat_1(A_3700))), inference(resolution, [status(thm)], [c_114875, c_30])).
% 48.86/37.43  tff(c_139019, plain, (![B_3701]: (k1_funct_1('#skF_9', B_3701)='#skF_7' | ~r2_hidden(B_3701, k1_relat_1('#skF_9')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_74, c_139015])).
% 48.86/37.43  tff(c_139023, plain, (![B_3704]: (k1_funct_1('#skF_9', B_3704)='#skF_7' | ~r2_hidden(B_3704, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_128, c_78, c_98712, c_139019])).
% 48.86/37.43  tff(c_139127, plain, (k1_funct_1('#skF_9', '#skF_8')='#skF_7'), inference(resolution, [status(thm)], [c_72, c_139023])).
% 48.86/37.43  tff(c_139162, plain, $false, inference(negUnitSimplification, [status(thm)], [c_70, c_139127])).
% 48.86/37.43  tff(c_139163, plain, (k1_tarski('#skF_7')=k1_xboole_0), inference(splitRight, [status(thm)], [c_98711])).
% 48.86/37.43  tff(c_139245, plain, (k3_tarski(k1_xboole_0)='#skF_7'), inference(superposition, [status(thm), theory('equality')], [c_139163, c_34])).
% 48.86/37.43  tff(c_139261, plain, (k1_xboole_0='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_139245, c_404])).
% 48.86/37.43  tff(c_139167, plain, (v1_funct_2('#skF_9', '#skF_6', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_139163, c_76])).
% 48.86/37.43  tff(c_139311, plain, (v1_funct_2('#skF_9', '#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_139261, c_139167])).
% 48.86/37.43  tff(c_139166, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_6', k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_139163, c_74])).
% 48.86/37.43  tff(c_139434, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_139261, c_139166])).
% 48.86/37.43  tff(c_154442, plain, (![C_4169, A_4170]: (C_4169='#skF_7' | ~v1_funct_2(C_4169, A_4170, '#skF_7') | A_4170='#skF_7' | ~m1_subset_1(C_4169, k1_zfmisc_1(k2_zfmisc_1(A_4170, '#skF_7'))))), inference(demodulation, [status(thm), theory('equality')], [c_139261, c_139261, c_139261, c_139261, c_60])).
% 48.86/37.43  tff(c_154445, plain, ('#skF_7'='#skF_9' | ~v1_funct_2('#skF_9', '#skF_6', '#skF_7') | '#skF_7'='#skF_6'), inference(resolution, [status(thm)], [c_139434, c_154442])).
% 48.86/37.43  tff(c_154448, plain, ('#skF_7'='#skF_9' | '#skF_7'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_139311, c_154445])).
% 48.86/37.43  tff(c_154449, plain, ('#skF_7'='#skF_6'), inference(splitLeft, [status(thm)], [c_154448])).
% 48.86/37.43  tff(c_139225, plain, (![C_116]: (r2_hidden('#skF_4'(k1_xboole_0, '#skF_7', C_116), k1_tarski('#skF_7')) | ~r2_hidden(C_116, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_139163, c_269])).
% 48.86/37.43  tff(c_139256, plain, (![C_116]: (r2_hidden('#skF_4'(k1_xboole_0, '#skF_7', C_116), k1_xboole_0) | ~r2_hidden(C_116, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_139163, c_139225])).
% 48.86/37.43  tff(c_139257, plain, (![C_116]: (~r2_hidden(C_116, '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_405, c_139256])).
% 48.86/37.43  tff(c_154650, plain, (![C_116]: (~r2_hidden(C_116, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_154449, c_139257])).
% 48.86/37.43  tff(c_154666, plain, $false, inference(negUnitSimplification, [status(thm)], [c_154650, c_72])).
% 48.86/37.43  tff(c_154667, plain, ('#skF_7'='#skF_9'), inference(splitRight, [status(thm)], [c_154448])).
% 48.86/37.43  tff(c_56816, plain, (![B_226]: (~v1_funct_1(k1_xboole_0) | ~r2_hidden(B_226, k1_relat_1(k1_xboole_0)))), inference(splitRight, [status(thm)], [c_1314])).
% 48.86/37.43  tff(c_56819, plain, (~v1_funct_1(k1_xboole_0)), inference(splitLeft, [status(thm)], [c_56816])).
% 48.86/37.43  tff(c_139329, plain, (~v1_funct_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_139261, c_56819])).
% 48.86/37.43  tff(c_154870, plain, (~v1_funct_1('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_154667, c_139329])).
% 48.86/37.43  tff(c_154876, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_78, c_154870])).
% 48.86/37.43  tff(c_154878, plain, (v1_funct_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_56816])).
% 48.86/37.43  tff(c_44, plain, (![A_36, B_39]: (k1_funct_1(A_36, B_39)=k1_xboole_0 | r2_hidden(B_39, k1_relat_1(A_36)) | ~v1_funct_1(A_36) | ~v1_relat_1(A_36))), inference(cnfTransformation, [status(thm)], [f_76])).
% 48.86/37.43  tff(c_154899, plain, (![B_4176]: (~r2_hidden(B_4176, k1_relat_1(k1_xboole_0)))), inference(splitRight, [status(thm)], [c_56816])).
% 48.86/37.43  tff(c_154939, plain, (![B_39]: (k1_funct_1(k1_xboole_0, B_39)=k1_xboole_0 | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_44, c_154899])).
% 48.86/37.43  tff(c_154963, plain, (![B_39]: (k1_funct_1(k1_xboole_0, B_39)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_56817, c_154878, c_154939])).
% 48.86/37.43  tff(c_233505, plain, (![B_39]: (k1_funct_1('#skF_7', B_39)='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_233445, c_233445, c_154963])).
% 48.86/37.43  tff(c_248530, plain, (![B_39]: (k1_funct_1('#skF_9', B_39)='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_248263, c_248263, c_233505])).
% 48.86/37.43  tff(c_248543, plain, (k1_funct_1('#skF_9', '#skF_8')!='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_248263, c_70])).
% 48.86/37.43  tff(c_248813, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_248530, c_248543])).
% 48.86/37.43  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 48.86/37.43  
% 48.86/37.43  Inference rules
% 48.86/37.43  ----------------------
% 48.86/37.43  #Ref     : 0
% 48.86/37.43  #Sup     : 59954
% 48.86/37.43  #Fact    : 0
% 48.86/37.43  #Define  : 0
% 48.86/37.43  #Split   : 396
% 48.86/37.43  #Chain   : 0
% 48.86/37.43  #Close   : 0
% 48.86/37.43  
% 48.86/37.43  Ordering : KBO
% 48.86/37.43  
% 48.86/37.43  Simplification rules
% 48.86/37.43  ----------------------
% 48.86/37.43  #Subsume      : 24578
% 48.86/37.43  #Demod        : 45017
% 48.86/37.43  #Tautology    : 7892
% 48.86/37.43  #SimpNegUnit  : 3118
% 48.86/37.43  #BackRed      : 4279
% 48.86/37.43  
% 48.86/37.43  #Partial instantiations: 0
% 48.86/37.43  #Strategies tried      : 1
% 48.86/37.43  
% 48.86/37.43  Timing (in seconds)
% 48.86/37.43  ----------------------
% 48.86/37.43  Preprocessing        : 0.37
% 48.86/37.43  Parsing              : 0.19
% 48.86/37.43  CNF conversion       : 0.03
% 48.86/37.43  Main loop            : 36.23
% 48.86/37.43  Inferencing          : 5.37
% 48.86/37.43  Reduction            : 10.76
% 48.86/37.43  Demodulation         : 7.01
% 48.86/37.43  BG Simplification    : 0.61
% 48.86/37.43  Subsumption          : 16.55
% 48.86/37.43  Abstraction          : 1.13
% 48.86/37.43  MUC search           : 0.00
% 48.86/37.43  Cooper               : 0.00
% 48.86/37.43  Total                : 36.65
% 48.86/37.43  Index Insertion      : 0.00
% 48.86/37.43  Index Deletion       : 0.00
% 48.86/37.43  Index Matching       : 0.00
% 48.86/37.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
