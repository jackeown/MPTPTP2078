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
% DateTime   : Thu Dec  3 10:02:53 EST 2020

% Result     : Theorem 40.80s
% Output     : CNFRefutation 40.97s
% Verified   : 
% Statistics : Number of formulae       :  128 ( 507 expanded)
%              Number of leaves         :   31 ( 185 expanded)
%              Depth                    :   24
%              Number of atoms          :  290 (1327 expanded)
%              Number of equality atoms :  108 ( 567 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k4_tarski > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_4 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_1

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

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k11_relat_1,type,(
    k11_relat_1: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_98,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ( k1_relat_1(B) = k1_tarski(A)
         => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_57,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] : k11_relat_1(A,B) = k9_relat_1(A,k1_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_relat_1)).

tff(f_72,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_79,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r2_hidden(A,k1_relat_1(B))
      <=> k11_relat_1(B,A) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t205_relat_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ~ ( A != k1_tarski(B)
        & A != k1_xboole_0
        & ! [C] :
            ~ ( r2_hidden(C,A)
              & C != B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_zfmisc_1)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_89,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

tff(c_52,plain,(
    v1_relat_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_48,plain,(
    k1_tarski('#skF_5') = k1_relat_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_112,plain,(
    ! [A_41,B_42] :
      ( k9_relat_1(A_41,k1_tarski(B_42)) = k11_relat_1(A_41,B_42)
      | ~ v1_relat_1(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_125,plain,(
    ! [A_45] :
      ( k9_relat_1(A_45,k1_relat_1('#skF_6')) = k11_relat_1(A_45,'#skF_5')
      | ~ v1_relat_1(A_45) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_112])).

tff(c_34,plain,(
    ! [A_24] :
      ( k9_relat_1(A_24,k1_relat_1(A_24)) = k2_relat_1(A_24)
      | ~ v1_relat_1(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_132,plain,
    ( k11_relat_1('#skF_6','#skF_5') = k2_relat_1('#skF_6')
    | ~ v1_relat_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_125,c_34])).

tff(c_142,plain,(
    k11_relat_1('#skF_6','#skF_5') = k2_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_52,c_132])).

tff(c_57,plain,(
    ! [C_30] : r2_hidden(C_30,k1_tarski(C_30)) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_60,plain,(
    r2_hidden('#skF_5',k1_relat_1('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_57])).

tff(c_177,plain,(
    ! [B_49,A_50] :
      ( k11_relat_1(B_49,A_50) != k1_xboole_0
      | ~ r2_hidden(A_50,k1_relat_1(B_49))
      | ~ v1_relat_1(B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_183,plain,
    ( k11_relat_1('#skF_6','#skF_5') != k1_xboole_0
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_60,c_177])).

tff(c_187,plain,(
    k2_relat_1('#skF_6') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_142,c_183])).

tff(c_22,plain,(
    ! [A_12,B_13] :
      ( r2_hidden('#skF_3'(A_12,B_13),A_12)
      | k1_xboole_0 = A_12
      | k1_tarski(B_13) = A_12 ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_50,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_32,plain,(
    ! [A_18,B_19,C_20] :
      ( r2_hidden('#skF_4'(A_18,B_19,C_20),k1_relat_1(C_20))
      | ~ r2_hidden(A_18,k9_relat_1(C_20,B_19))
      | ~ v1_relat_1(C_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_40,plain,(
    ! [A_27,C_29] :
      ( r2_hidden(k4_tarski(A_27,k1_funct_1(C_29,A_27)),C_29)
      | ~ r2_hidden(A_27,k1_relat_1(C_29))
      | ~ v1_funct_1(C_29)
      | ~ v1_relat_1(C_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_24,plain,(
    ! [A_15,B_17] :
      ( k9_relat_1(A_15,k1_tarski(B_17)) = k11_relat_1(A_15,B_17)
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_4,plain,(
    ! [C_5] : r2_hidden(C_5,k1_tarski(C_5)) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_18328,plain,(
    ! [A_15623,C_15624,B_15625,D_15626] :
      ( r2_hidden(A_15623,k9_relat_1(C_15624,B_15625))
      | ~ r2_hidden(D_15626,B_15625)
      | ~ r2_hidden(k4_tarski(D_15626,A_15623),C_15624)
      | ~ r2_hidden(D_15626,k1_relat_1(C_15624))
      | ~ v1_relat_1(C_15624) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_24418,plain,(
    ! [A_25273,C_25274,C_25275] :
      ( r2_hidden(A_25273,k9_relat_1(C_25274,k1_tarski(C_25275)))
      | ~ r2_hidden(k4_tarski(C_25275,A_25273),C_25274)
      | ~ r2_hidden(C_25275,k1_relat_1(C_25274))
      | ~ v1_relat_1(C_25274) ) ),
    inference(resolution,[status(thm)],[c_4,c_18328])).

tff(c_127977,plain,(
    ! [A_109218,A_109219,B_109220] :
      ( r2_hidden(A_109218,k11_relat_1(A_109219,B_109220))
      | ~ r2_hidden(k4_tarski(B_109220,A_109218),A_109219)
      | ~ r2_hidden(B_109220,k1_relat_1(A_109219))
      | ~ v1_relat_1(A_109219)
      | ~ v1_relat_1(A_109219) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_24418])).

tff(c_128096,plain,(
    ! [C_29,A_27] :
      ( r2_hidden(k1_funct_1(C_29,A_27),k11_relat_1(C_29,A_27))
      | ~ r2_hidden(A_27,k1_relat_1(C_29))
      | ~ v1_funct_1(C_29)
      | ~ v1_relat_1(C_29) ) ),
    inference(resolution,[status(thm)],[c_40,c_127977])).

tff(c_30,plain,(
    ! [A_18,B_19,C_20] :
      ( r2_hidden(k4_tarski('#skF_4'(A_18,B_19,C_20),A_18),C_20)
      | ~ r2_hidden(A_18,k9_relat_1(C_20,B_19))
      | ~ v1_relat_1(C_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_44221,plain,(
    ! [C_67759,A_67760,A_67758,B_67761,C_67757] :
      ( r2_hidden(A_67760,k9_relat_1(C_67757,k1_relat_1(C_67759)))
      | ~ r2_hidden(k4_tarski('#skF_4'(A_67758,B_67761,C_67759),A_67760),C_67757)
      | ~ r2_hidden('#skF_4'(A_67758,B_67761,C_67759),k1_relat_1(C_67757))
      | ~ v1_relat_1(C_67757)
      | ~ r2_hidden(A_67758,k9_relat_1(C_67759,B_67761))
      | ~ v1_relat_1(C_67759) ) ),
    inference(resolution,[status(thm)],[c_32,c_18328])).

tff(c_189162,plain,(
    ! [A_123115,C_123116,B_123117] :
      ( r2_hidden(A_123115,k9_relat_1(C_123116,k1_relat_1(C_123116)))
      | ~ r2_hidden('#skF_4'(A_123115,B_123117,C_123116),k1_relat_1(C_123116))
      | ~ r2_hidden(A_123115,k9_relat_1(C_123116,B_123117))
      | ~ v1_relat_1(C_123116) ) ),
    inference(resolution,[status(thm)],[c_30,c_44221])).

tff(c_194781,plain,(
    ! [A_123933,C_123934,B_123935] :
      ( r2_hidden(A_123933,k9_relat_1(C_123934,k1_relat_1(C_123934)))
      | ~ r2_hidden(A_123933,k9_relat_1(C_123934,B_123935))
      | ~ v1_relat_1(C_123934) ) ),
    inference(resolution,[status(thm)],[c_32,c_189162])).

tff(c_197914,plain,(
    ! [A_125164,A_125165,B_125166] :
      ( r2_hidden(A_125164,k9_relat_1(A_125165,k1_relat_1(A_125165)))
      | ~ r2_hidden(A_125164,k11_relat_1(A_125165,B_125166))
      | ~ v1_relat_1(A_125165)
      | ~ v1_relat_1(A_125165) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_194781])).

tff(c_249238,plain,(
    ! [C_137240,A_137241] :
      ( r2_hidden(k1_funct_1(C_137240,A_137241),k9_relat_1(C_137240,k1_relat_1(C_137240)))
      | ~ r2_hidden(A_137241,k1_relat_1(C_137240))
      | ~ v1_funct_1(C_137240)
      | ~ v1_relat_1(C_137240) ) ),
    inference(resolution,[status(thm)],[c_128096,c_197914])).

tff(c_250305,plain,(
    ! [A_24,A_137241] :
      ( r2_hidden(k1_funct_1(A_24,A_137241),k2_relat_1(A_24))
      | ~ r2_hidden(A_137241,k1_relat_1(A_24))
      | ~ v1_funct_1(A_24)
      | ~ v1_relat_1(A_24)
      | ~ v1_relat_1(A_24) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_249238])).

tff(c_188,plain,(
    ! [A_51,B_52] :
      ( r2_hidden('#skF_3'(A_51,B_52),A_51)
      | k1_xboole_0 = A_51
      | k1_tarski(B_52) = A_51 ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_70,plain,(
    ! [C_32,A_33] :
      ( C_32 = A_33
      | ~ r2_hidden(C_32,k1_tarski(A_33)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_76,plain,(
    ! [C_32] :
      ( C_32 = '#skF_5'
      | ~ r2_hidden(C_32,k1_relat_1('#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_70])).

tff(c_202,plain,(
    ! [B_52] :
      ( '#skF_3'(k1_relat_1('#skF_6'),B_52) = '#skF_5'
      | k1_relat_1('#skF_6') = k1_xboole_0
      | k1_tarski(B_52) = k1_relat_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_188,c_76])).

tff(c_266,plain,(
    k1_relat_1('#skF_6') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_202])).

tff(c_269,plain,(
    r2_hidden('#skF_5',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_266,c_60])).

tff(c_146,plain,(
    ! [A_46,B_47] :
      ( r2_hidden(A_46,k1_relat_1(B_47))
      | k11_relat_1(B_47,A_46) = k1_xboole_0
      | ~ v1_relat_1(B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_150,plain,(
    ! [A_46] :
      ( A_46 = '#skF_5'
      | k11_relat_1('#skF_6',A_46) = k1_xboole_0
      | ~ v1_relat_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_146,c_76])).

tff(c_153,plain,(
    ! [A_46] :
      ( A_46 = '#skF_5'
      | k11_relat_1('#skF_6',A_46) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_150])).

tff(c_334,plain,(
    ! [A_64,B_65,C_66] :
      ( r2_hidden('#skF_4'(A_64,B_65,C_66),B_65)
      | ~ r2_hidden(A_64,k9_relat_1(C_66,B_65))
      | ~ v1_relat_1(C_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_2,plain,(
    ! [C_5,A_1] :
      ( C_5 = A_1
      | ~ r2_hidden(C_5,k1_tarski(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_968,plain,(
    ! [A_109,A_110,C_111] :
      ( '#skF_4'(A_109,k1_tarski(A_110),C_111) = A_110
      | ~ r2_hidden(A_109,k9_relat_1(C_111,k1_tarski(A_110)))
      | ~ v1_relat_1(C_111) ) ),
    inference(resolution,[status(thm)],[c_334,c_2])).

tff(c_14153,plain,(
    ! [A_3997,B_3998,A_3999] :
      ( '#skF_4'(A_3997,k1_tarski(B_3998),A_3999) = B_3998
      | ~ r2_hidden(A_3997,k11_relat_1(A_3999,B_3998))
      | ~ v1_relat_1(A_3999)
      | ~ v1_relat_1(A_3999) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_968])).

tff(c_14266,plain,(
    ! [A_3997,A_46] :
      ( '#skF_4'(A_3997,k1_tarski(A_46),'#skF_6') = A_46
      | ~ r2_hidden(A_3997,k1_xboole_0)
      | ~ v1_relat_1('#skF_6')
      | ~ v1_relat_1('#skF_6')
      | A_46 = '#skF_5' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_153,c_14153])).

tff(c_14289,plain,(
    ! [A_4058,A_4059] :
      ( '#skF_4'(A_4058,k1_tarski(A_4059),'#skF_6') = A_4059
      | ~ r2_hidden(A_4058,k1_xboole_0)
      | A_4059 = '#skF_5' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_52,c_14266])).

tff(c_660,plain,(
    ! [A_88,B_89,C_90] :
      ( r2_hidden('#skF_4'(A_88,B_89,C_90),k1_relat_1(C_90))
      | ~ r2_hidden(A_88,k9_relat_1(C_90,B_89))
      | ~ v1_relat_1(C_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_669,plain,(
    ! [A_88,B_89] :
      ( r2_hidden('#skF_4'(A_88,B_89,'#skF_6'),k1_xboole_0)
      | ~ r2_hidden(A_88,k9_relat_1('#skF_6',B_89))
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_266,c_660])).

tff(c_675,plain,(
    ! [A_91,B_92] :
      ( r2_hidden('#skF_4'(A_91,B_92,'#skF_6'),k1_xboole_0)
      | ~ r2_hidden(A_91,k9_relat_1('#skF_6',B_92)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_669])).

tff(c_268,plain,(
    ! [C_32] :
      ( C_32 = '#skF_5'
      | ~ r2_hidden(C_32,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_266,c_76])).

tff(c_688,plain,(
    ! [A_93,B_94] :
      ( '#skF_4'(A_93,B_94,'#skF_6') = '#skF_5'
      | ~ r2_hidden(A_93,k9_relat_1('#skF_6',B_94)) ) ),
    inference(resolution,[status(thm)],[c_675,c_268])).

tff(c_711,plain,(
    ! [A_93,B_17] :
      ( '#skF_4'(A_93,k1_tarski(B_17),'#skF_6') = '#skF_5'
      | ~ r2_hidden(A_93,k11_relat_1('#skF_6',B_17))
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_688])).

tff(c_724,plain,(
    ! [A_95,B_96] :
      ( '#skF_4'(A_95,k1_tarski(B_96),'#skF_6') = '#skF_5'
      | ~ r2_hidden(A_95,k11_relat_1('#skF_6',B_96)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_711])).

tff(c_749,plain,(
    ! [A_95,A_46] :
      ( '#skF_4'(A_95,k1_tarski(A_46),'#skF_6') = '#skF_5'
      | ~ r2_hidden(A_95,k1_xboole_0)
      | A_46 = '#skF_5' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_153,c_724])).

tff(c_14307,plain,(
    ! [A_4059,A_4058] :
      ( A_4059 = '#skF_5'
      | ~ r2_hidden(A_4058,k1_xboole_0)
      | A_4059 = '#skF_5'
      | ~ r2_hidden(A_4058,k1_xboole_0)
      | A_4059 = '#skF_5' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14289,c_749])).

tff(c_14790,plain,(
    ! [A_4180] :
      ( ~ r2_hidden(A_4180,k1_xboole_0)
      | ~ r2_hidden(A_4180,k1_xboole_0) ) ),
    inference(splitLeft,[status(thm)],[c_14307])).

tff(c_14809,plain,(
    ~ r2_hidden('#skF_5',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_269,c_14790])).

tff(c_14828,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_269,c_14809])).

tff(c_14829,plain,(
    ! [A_4059] :
      ( A_4059 = '#skF_5'
      | A_4059 = '#skF_5'
      | A_4059 = '#skF_5' ) ),
    inference(splitRight,[status(thm)],[c_14307])).

tff(c_14890,plain,(
    ! [A_4059] : A_4059 = '#skF_5' ),
    inference(factorization,[status(thm),theory(equality)],[c_14829])).

tff(c_15429,plain,(
    ! [A_10388] : A_10388 = '#skF_5' ),
    inference(factorization,[status(thm),theory(equality)],[c_14829])).

tff(c_46,plain,(
    k1_tarski(k1_funct_1('#skF_6','#skF_5')) != k2_relat_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_15584,plain,(
    k2_relat_1('#skF_6') != '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_15429,c_46])).

tff(c_15624,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_14890,c_15584])).

tff(c_15626,plain,(
    k1_relat_1('#skF_6') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_202])).

tff(c_15627,plain,(
    ! [B_11957] :
      ( '#skF_3'(k1_relat_1('#skF_6'),B_11957) = '#skF_5'
      | k1_tarski(B_11957) = k1_relat_1('#skF_6') ) ),
    inference(splitRight,[status(thm)],[c_202])).

tff(c_20,plain,(
    ! [A_12,B_13] :
      ( '#skF_3'(A_12,B_13) != B_13
      | k1_xboole_0 = A_12
      | k1_tarski(B_13) = A_12 ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_15635,plain,(
    ! [B_11957] :
      ( B_11957 != '#skF_5'
      | k1_relat_1('#skF_6') = k1_xboole_0
      | k1_tarski(B_11957) = k1_relat_1('#skF_6')
      | k1_tarski(B_11957) = k1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_15627,c_20])).

tff(c_15642,plain,(
    ! [B_11957] :
      ( B_11957 != '#skF_5'
      | k1_tarski(B_11957) = k1_relat_1('#skF_6')
      | k1_tarski(B_11957) = k1_relat_1('#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_15626,c_15635])).

tff(c_15676,plain,(
    ! [B_11959] :
      ( B_11959 != '#skF_5'
      | k1_tarski(B_11959) = k1_relat_1('#skF_6') ) ),
    inference(factorization,[status(thm),theory(equality)],[c_15642])).

tff(c_15781,plain,(
    ! [A_11971,B_11972] :
      ( k9_relat_1(A_11971,k1_relat_1('#skF_6')) = k11_relat_1(A_11971,B_11972)
      | ~ v1_relat_1(A_11971)
      | B_11972 != '#skF_5' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_15676,c_24])).

tff(c_15802,plain,(
    ! [B_11972] :
      ( k11_relat_1('#skF_6',B_11972) = k2_relat_1('#skF_6')
      | ~ v1_relat_1('#skF_6')
      | ~ v1_relat_1('#skF_6')
      | B_11972 != '#skF_5' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_15781,c_34])).

tff(c_15831,plain,(
    k11_relat_1('#skF_6','#skF_5') = k2_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_52,c_15802])).

tff(c_15976,plain,(
    ! [A_11984,B_11985,C_11986] :
      ( r2_hidden('#skF_4'(A_11984,B_11985,C_11986),k1_relat_1(C_11986))
      | ~ r2_hidden(A_11984,k9_relat_1(C_11986,B_11985))
      | ~ v1_relat_1(C_11986) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_15986,plain,(
    ! [A_11984,B_11985] :
      ( '#skF_4'(A_11984,B_11985,'#skF_6') = '#skF_5'
      | ~ r2_hidden(A_11984,k9_relat_1('#skF_6',B_11985))
      | ~ v1_relat_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_15976,c_76])).

tff(c_15993,plain,(
    ! [A_11984,B_11985] :
      ( '#skF_4'(A_11984,B_11985,'#skF_6') = '#skF_5'
      | ~ r2_hidden(A_11984,k9_relat_1('#skF_6',B_11985)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_15986])).

tff(c_249264,plain,(
    ! [A_137241] :
      ( '#skF_4'(k1_funct_1('#skF_6',A_137241),k1_relat_1('#skF_6'),'#skF_6') = '#skF_5'
      | ~ r2_hidden(A_137241,k1_relat_1('#skF_6'))
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_249238,c_15993])).

tff(c_251501,plain,(
    ! [A_137855] :
      ( '#skF_4'(k1_funct_1('#skF_6',A_137855),k1_relat_1('#skF_6'),'#skF_6') = '#skF_5'
      | ~ r2_hidden(A_137855,k1_relat_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_249264])).

tff(c_121,plain,(
    ! [A_41] :
      ( k9_relat_1(A_41,k1_relat_1('#skF_6')) = k11_relat_1(A_41,'#skF_5')
      | ~ v1_relat_1(A_41) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_112])).

tff(c_16103,plain,(
    ! [A_11992,B_11993,C_11994] :
      ( r2_hidden(k4_tarski('#skF_4'(A_11992,B_11993,C_11994),A_11992),C_11994)
      | ~ r2_hidden(A_11992,k9_relat_1(C_11994,B_11993))
      | ~ v1_relat_1(C_11994) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_42,plain,(
    ! [C_29,A_27,B_28] :
      ( k1_funct_1(C_29,A_27) = B_28
      | ~ r2_hidden(k4_tarski(A_27,B_28),C_29)
      | ~ v1_funct_1(C_29)
      | ~ v1_relat_1(C_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_21646,plain,(
    ! [C_20282,A_20283,B_20284] :
      ( k1_funct_1(C_20282,'#skF_4'(A_20283,B_20284,C_20282)) = A_20283
      | ~ v1_funct_1(C_20282)
      | ~ r2_hidden(A_20283,k9_relat_1(C_20282,B_20284))
      | ~ v1_relat_1(C_20282) ) ),
    inference(resolution,[status(thm)],[c_16103,c_42])).

tff(c_21682,plain,(
    ! [A_41,A_20283] :
      ( k1_funct_1(A_41,'#skF_4'(A_20283,k1_relat_1('#skF_6'),A_41)) = A_20283
      | ~ v1_funct_1(A_41)
      | ~ r2_hidden(A_20283,k11_relat_1(A_41,'#skF_5'))
      | ~ v1_relat_1(A_41)
      | ~ v1_relat_1(A_41) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_121,c_21646])).

tff(c_251536,plain,(
    ! [A_137855] :
      ( k1_funct_1('#skF_6',A_137855) = k1_funct_1('#skF_6','#skF_5')
      | ~ v1_funct_1('#skF_6')
      | ~ r2_hidden(k1_funct_1('#skF_6',A_137855),k11_relat_1('#skF_6','#skF_5'))
      | ~ v1_relat_1('#skF_6')
      | ~ v1_relat_1('#skF_6')
      | ~ r2_hidden(A_137855,k1_relat_1('#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_251501,c_21682])).

tff(c_261746,plain,(
    ! [A_139292] :
      ( k1_funct_1('#skF_6',A_139292) = k1_funct_1('#skF_6','#skF_5')
      | ~ r2_hidden(k1_funct_1('#skF_6',A_139292),k2_relat_1('#skF_6'))
      | ~ r2_hidden(A_139292,k1_relat_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_52,c_15831,c_50,c_251536])).

tff(c_261750,plain,(
    ! [A_137241] :
      ( k1_funct_1('#skF_6',A_137241) = k1_funct_1('#skF_6','#skF_5')
      | ~ r2_hidden(A_137241,k1_relat_1('#skF_6'))
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_250305,c_261746])).

tff(c_262186,plain,(
    ! [A_139496] :
      ( k1_funct_1('#skF_6',A_139496) = k1_funct_1('#skF_6','#skF_5')
      | ~ r2_hidden(A_139496,k1_relat_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_261750])).

tff(c_262551,plain,(
    ! [A_18,B_19] :
      ( k1_funct_1('#skF_6','#skF_4'(A_18,B_19,'#skF_6')) = k1_funct_1('#skF_6','#skF_5')
      | ~ r2_hidden(A_18,k9_relat_1('#skF_6',B_19))
      | ~ v1_relat_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_32,c_262186])).

tff(c_289446,plain,(
    ! [A_145022,B_145023] :
      ( k1_funct_1('#skF_6','#skF_4'(A_145022,B_145023,'#skF_6')) = k1_funct_1('#skF_6','#skF_5')
      | ~ r2_hidden(A_145022,k9_relat_1('#skF_6',B_145023)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_262551])).

tff(c_290038,plain,(
    ! [A_145022] :
      ( k1_funct_1('#skF_6','#skF_4'(A_145022,k1_relat_1('#skF_6'),'#skF_6')) = k1_funct_1('#skF_6','#skF_5')
      | ~ r2_hidden(A_145022,k2_relat_1('#skF_6'))
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_289446])).

tff(c_295683,plain,(
    ! [A_146049] :
      ( k1_funct_1('#skF_6','#skF_4'(A_146049,k1_relat_1('#skF_6'),'#skF_6')) = k1_funct_1('#skF_6','#skF_5')
      | ~ r2_hidden(A_146049,k2_relat_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_290038])).

tff(c_21686,plain,(
    ! [A_24,A_20283] :
      ( k1_funct_1(A_24,'#skF_4'(A_20283,k1_relat_1(A_24),A_24)) = A_20283
      | ~ v1_funct_1(A_24)
      | ~ r2_hidden(A_20283,k2_relat_1(A_24))
      | ~ v1_relat_1(A_24)
      | ~ v1_relat_1(A_24) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_21646])).

tff(c_295822,plain,(
    ! [A_146049] :
      ( k1_funct_1('#skF_6','#skF_5') = A_146049
      | ~ v1_funct_1('#skF_6')
      | ~ r2_hidden(A_146049,k2_relat_1('#skF_6'))
      | ~ v1_relat_1('#skF_6')
      | ~ v1_relat_1('#skF_6')
      | ~ r2_hidden(A_146049,k2_relat_1('#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_295683,c_21686])).

tff(c_297094,plain,(
    ! [A_146253] :
      ( k1_funct_1('#skF_6','#skF_5') = A_146253
      | ~ r2_hidden(A_146253,k2_relat_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_52,c_50,c_295822])).

tff(c_297349,plain,(
    ! [B_13] :
      ( '#skF_3'(k2_relat_1('#skF_6'),B_13) = k1_funct_1('#skF_6','#skF_5')
      | k2_relat_1('#skF_6') = k1_xboole_0
      | k2_relat_1('#skF_6') = k1_tarski(B_13) ) ),
    inference(resolution,[status(thm)],[c_22,c_297094])).

tff(c_297368,plain,(
    ! [B_146457] :
      ( '#skF_3'(k2_relat_1('#skF_6'),B_146457) = k1_funct_1('#skF_6','#skF_5')
      | k2_relat_1('#skF_6') = k1_tarski(B_146457) ) ),
    inference(negUnitSimplification,[status(thm)],[c_187,c_297349])).

tff(c_297394,plain,(
    ! [B_146457] :
      ( k1_funct_1('#skF_6','#skF_5') != B_146457
      | k2_relat_1('#skF_6') = k1_xboole_0
      | k2_relat_1('#skF_6') = k1_tarski(B_146457)
      | k2_relat_1('#skF_6') = k1_tarski(B_146457) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_297368,c_20])).

tff(c_299064,plain,(
    k1_tarski(k1_funct_1('#skF_6','#skF_5')) = k2_relat_1('#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_187,c_297394])).

tff(c_299068,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_299064,c_46])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n010.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:43:59 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 40.80/28.69  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 40.80/28.70  
% 40.80/28.70  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 40.80/28.71  %$ r2_hidden > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k4_tarski > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_4 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_1
% 40.80/28.71  
% 40.80/28.71  %Foreground sorts:
% 40.80/28.71  
% 40.80/28.71  
% 40.80/28.71  %Background operators:
% 40.80/28.71  
% 40.80/28.71  
% 40.80/28.71  %Foreground operators:
% 40.80/28.71  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 40.80/28.71  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 40.80/28.71  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 40.80/28.71  tff(k1_tarski, type, k1_tarski: $i > $i).
% 40.80/28.71  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 40.80/28.71  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 40.80/28.71  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 40.80/28.71  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 40.80/28.71  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 40.80/28.71  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 40.80/28.71  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 40.80/28.71  tff('#skF_5', type, '#skF_5': $i).
% 40.80/28.71  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 40.80/28.71  tff('#skF_6', type, '#skF_6': $i).
% 40.80/28.71  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 40.80/28.71  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 40.80/28.71  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 40.80/28.71  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 40.80/28.71  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 40.80/28.71  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 40.80/28.71  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 40.80/28.71  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 40.80/28.71  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 40.80/28.71  
% 40.97/28.73  tff(f_98, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_funct_1)).
% 40.97/28.73  tff(f_57, axiom, (![A]: (v1_relat_1(A) => (![B]: (k11_relat_1(A, B) = k9_relat_1(A, k1_tarski(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d16_relat_1)).
% 40.97/28.73  tff(f_72, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_relat_1)).
% 40.97/28.73  tff(f_32, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 40.97/28.73  tff(f_79, axiom, (![A, B]: (v1_relat_1(B) => (r2_hidden(A, k1_relat_1(B)) <=> ~(k11_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t205_relat_1)).
% 40.97/28.73  tff(f_52, axiom, (![A, B]: ~((~(A = k1_tarski(B)) & ~(A = k1_xboole_0)) & (![C]: ~(r2_hidden(C, A) & ~(C = B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_zfmisc_1)).
% 40.97/28.73  tff(f_68, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_relat_1)).
% 40.97/28.73  tff(f_89, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_1)).
% 40.97/28.73  tff(c_52, plain, (v1_relat_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_98])).
% 40.97/28.73  tff(c_48, plain, (k1_tarski('#skF_5')=k1_relat_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_98])).
% 40.97/28.73  tff(c_112, plain, (![A_41, B_42]: (k9_relat_1(A_41, k1_tarski(B_42))=k11_relat_1(A_41, B_42) | ~v1_relat_1(A_41))), inference(cnfTransformation, [status(thm)], [f_57])).
% 40.97/28.73  tff(c_125, plain, (![A_45]: (k9_relat_1(A_45, k1_relat_1('#skF_6'))=k11_relat_1(A_45, '#skF_5') | ~v1_relat_1(A_45))), inference(superposition, [status(thm), theory('equality')], [c_48, c_112])).
% 40.97/28.73  tff(c_34, plain, (![A_24]: (k9_relat_1(A_24, k1_relat_1(A_24))=k2_relat_1(A_24) | ~v1_relat_1(A_24))), inference(cnfTransformation, [status(thm)], [f_72])).
% 40.97/28.73  tff(c_132, plain, (k11_relat_1('#skF_6', '#skF_5')=k2_relat_1('#skF_6') | ~v1_relat_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_125, c_34])).
% 40.97/28.73  tff(c_142, plain, (k11_relat_1('#skF_6', '#skF_5')=k2_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_52, c_132])).
% 40.97/28.73  tff(c_57, plain, (![C_30]: (r2_hidden(C_30, k1_tarski(C_30)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 40.97/28.73  tff(c_60, plain, (r2_hidden('#skF_5', k1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_48, c_57])).
% 40.97/28.73  tff(c_177, plain, (![B_49, A_50]: (k11_relat_1(B_49, A_50)!=k1_xboole_0 | ~r2_hidden(A_50, k1_relat_1(B_49)) | ~v1_relat_1(B_49))), inference(cnfTransformation, [status(thm)], [f_79])).
% 40.97/28.73  tff(c_183, plain, (k11_relat_1('#skF_6', '#skF_5')!=k1_xboole_0 | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_60, c_177])).
% 40.97/28.73  tff(c_187, plain, (k2_relat_1('#skF_6')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_52, c_142, c_183])).
% 40.97/28.73  tff(c_22, plain, (![A_12, B_13]: (r2_hidden('#skF_3'(A_12, B_13), A_12) | k1_xboole_0=A_12 | k1_tarski(B_13)=A_12)), inference(cnfTransformation, [status(thm)], [f_52])).
% 40.97/28.73  tff(c_50, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_98])).
% 40.97/28.73  tff(c_32, plain, (![A_18, B_19, C_20]: (r2_hidden('#skF_4'(A_18, B_19, C_20), k1_relat_1(C_20)) | ~r2_hidden(A_18, k9_relat_1(C_20, B_19)) | ~v1_relat_1(C_20))), inference(cnfTransformation, [status(thm)], [f_68])).
% 40.97/28.73  tff(c_40, plain, (![A_27, C_29]: (r2_hidden(k4_tarski(A_27, k1_funct_1(C_29, A_27)), C_29) | ~r2_hidden(A_27, k1_relat_1(C_29)) | ~v1_funct_1(C_29) | ~v1_relat_1(C_29))), inference(cnfTransformation, [status(thm)], [f_89])).
% 40.97/28.73  tff(c_24, plain, (![A_15, B_17]: (k9_relat_1(A_15, k1_tarski(B_17))=k11_relat_1(A_15, B_17) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_57])).
% 40.97/28.73  tff(c_4, plain, (![C_5]: (r2_hidden(C_5, k1_tarski(C_5)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 40.97/28.73  tff(c_18328, plain, (![A_15623, C_15624, B_15625, D_15626]: (r2_hidden(A_15623, k9_relat_1(C_15624, B_15625)) | ~r2_hidden(D_15626, B_15625) | ~r2_hidden(k4_tarski(D_15626, A_15623), C_15624) | ~r2_hidden(D_15626, k1_relat_1(C_15624)) | ~v1_relat_1(C_15624))), inference(cnfTransformation, [status(thm)], [f_68])).
% 40.97/28.73  tff(c_24418, plain, (![A_25273, C_25274, C_25275]: (r2_hidden(A_25273, k9_relat_1(C_25274, k1_tarski(C_25275))) | ~r2_hidden(k4_tarski(C_25275, A_25273), C_25274) | ~r2_hidden(C_25275, k1_relat_1(C_25274)) | ~v1_relat_1(C_25274))), inference(resolution, [status(thm)], [c_4, c_18328])).
% 40.97/28.73  tff(c_127977, plain, (![A_109218, A_109219, B_109220]: (r2_hidden(A_109218, k11_relat_1(A_109219, B_109220)) | ~r2_hidden(k4_tarski(B_109220, A_109218), A_109219) | ~r2_hidden(B_109220, k1_relat_1(A_109219)) | ~v1_relat_1(A_109219) | ~v1_relat_1(A_109219))), inference(superposition, [status(thm), theory('equality')], [c_24, c_24418])).
% 40.97/28.73  tff(c_128096, plain, (![C_29, A_27]: (r2_hidden(k1_funct_1(C_29, A_27), k11_relat_1(C_29, A_27)) | ~r2_hidden(A_27, k1_relat_1(C_29)) | ~v1_funct_1(C_29) | ~v1_relat_1(C_29))), inference(resolution, [status(thm)], [c_40, c_127977])).
% 40.97/28.73  tff(c_30, plain, (![A_18, B_19, C_20]: (r2_hidden(k4_tarski('#skF_4'(A_18, B_19, C_20), A_18), C_20) | ~r2_hidden(A_18, k9_relat_1(C_20, B_19)) | ~v1_relat_1(C_20))), inference(cnfTransformation, [status(thm)], [f_68])).
% 40.97/28.73  tff(c_44221, plain, (![C_67759, A_67760, A_67758, B_67761, C_67757]: (r2_hidden(A_67760, k9_relat_1(C_67757, k1_relat_1(C_67759))) | ~r2_hidden(k4_tarski('#skF_4'(A_67758, B_67761, C_67759), A_67760), C_67757) | ~r2_hidden('#skF_4'(A_67758, B_67761, C_67759), k1_relat_1(C_67757)) | ~v1_relat_1(C_67757) | ~r2_hidden(A_67758, k9_relat_1(C_67759, B_67761)) | ~v1_relat_1(C_67759))), inference(resolution, [status(thm)], [c_32, c_18328])).
% 40.97/28.73  tff(c_189162, plain, (![A_123115, C_123116, B_123117]: (r2_hidden(A_123115, k9_relat_1(C_123116, k1_relat_1(C_123116))) | ~r2_hidden('#skF_4'(A_123115, B_123117, C_123116), k1_relat_1(C_123116)) | ~r2_hidden(A_123115, k9_relat_1(C_123116, B_123117)) | ~v1_relat_1(C_123116))), inference(resolution, [status(thm)], [c_30, c_44221])).
% 40.97/28.73  tff(c_194781, plain, (![A_123933, C_123934, B_123935]: (r2_hidden(A_123933, k9_relat_1(C_123934, k1_relat_1(C_123934))) | ~r2_hidden(A_123933, k9_relat_1(C_123934, B_123935)) | ~v1_relat_1(C_123934))), inference(resolution, [status(thm)], [c_32, c_189162])).
% 40.97/28.73  tff(c_197914, plain, (![A_125164, A_125165, B_125166]: (r2_hidden(A_125164, k9_relat_1(A_125165, k1_relat_1(A_125165))) | ~r2_hidden(A_125164, k11_relat_1(A_125165, B_125166)) | ~v1_relat_1(A_125165) | ~v1_relat_1(A_125165))), inference(superposition, [status(thm), theory('equality')], [c_24, c_194781])).
% 40.97/28.73  tff(c_249238, plain, (![C_137240, A_137241]: (r2_hidden(k1_funct_1(C_137240, A_137241), k9_relat_1(C_137240, k1_relat_1(C_137240))) | ~r2_hidden(A_137241, k1_relat_1(C_137240)) | ~v1_funct_1(C_137240) | ~v1_relat_1(C_137240))), inference(resolution, [status(thm)], [c_128096, c_197914])).
% 40.97/28.73  tff(c_250305, plain, (![A_24, A_137241]: (r2_hidden(k1_funct_1(A_24, A_137241), k2_relat_1(A_24)) | ~r2_hidden(A_137241, k1_relat_1(A_24)) | ~v1_funct_1(A_24) | ~v1_relat_1(A_24) | ~v1_relat_1(A_24))), inference(superposition, [status(thm), theory('equality')], [c_34, c_249238])).
% 40.97/28.73  tff(c_188, plain, (![A_51, B_52]: (r2_hidden('#skF_3'(A_51, B_52), A_51) | k1_xboole_0=A_51 | k1_tarski(B_52)=A_51)), inference(cnfTransformation, [status(thm)], [f_52])).
% 40.97/28.73  tff(c_70, plain, (![C_32, A_33]: (C_32=A_33 | ~r2_hidden(C_32, k1_tarski(A_33)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 40.97/28.73  tff(c_76, plain, (![C_32]: (C_32='#skF_5' | ~r2_hidden(C_32, k1_relat_1('#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_48, c_70])).
% 40.97/28.73  tff(c_202, plain, (![B_52]: ('#skF_3'(k1_relat_1('#skF_6'), B_52)='#skF_5' | k1_relat_1('#skF_6')=k1_xboole_0 | k1_tarski(B_52)=k1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_188, c_76])).
% 40.97/28.73  tff(c_266, plain, (k1_relat_1('#skF_6')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_202])).
% 40.97/28.73  tff(c_269, plain, (r2_hidden('#skF_5', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_266, c_60])).
% 40.97/28.73  tff(c_146, plain, (![A_46, B_47]: (r2_hidden(A_46, k1_relat_1(B_47)) | k11_relat_1(B_47, A_46)=k1_xboole_0 | ~v1_relat_1(B_47))), inference(cnfTransformation, [status(thm)], [f_79])).
% 40.97/28.73  tff(c_150, plain, (![A_46]: (A_46='#skF_5' | k11_relat_1('#skF_6', A_46)=k1_xboole_0 | ~v1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_146, c_76])).
% 40.97/28.73  tff(c_153, plain, (![A_46]: (A_46='#skF_5' | k11_relat_1('#skF_6', A_46)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_52, c_150])).
% 40.97/28.73  tff(c_334, plain, (![A_64, B_65, C_66]: (r2_hidden('#skF_4'(A_64, B_65, C_66), B_65) | ~r2_hidden(A_64, k9_relat_1(C_66, B_65)) | ~v1_relat_1(C_66))), inference(cnfTransformation, [status(thm)], [f_68])).
% 40.97/28.73  tff(c_2, plain, (![C_5, A_1]: (C_5=A_1 | ~r2_hidden(C_5, k1_tarski(A_1)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 40.97/28.73  tff(c_968, plain, (![A_109, A_110, C_111]: ('#skF_4'(A_109, k1_tarski(A_110), C_111)=A_110 | ~r2_hidden(A_109, k9_relat_1(C_111, k1_tarski(A_110))) | ~v1_relat_1(C_111))), inference(resolution, [status(thm)], [c_334, c_2])).
% 40.97/28.73  tff(c_14153, plain, (![A_3997, B_3998, A_3999]: ('#skF_4'(A_3997, k1_tarski(B_3998), A_3999)=B_3998 | ~r2_hidden(A_3997, k11_relat_1(A_3999, B_3998)) | ~v1_relat_1(A_3999) | ~v1_relat_1(A_3999))), inference(superposition, [status(thm), theory('equality')], [c_24, c_968])).
% 40.97/28.73  tff(c_14266, plain, (![A_3997, A_46]: ('#skF_4'(A_3997, k1_tarski(A_46), '#skF_6')=A_46 | ~r2_hidden(A_3997, k1_xboole_0) | ~v1_relat_1('#skF_6') | ~v1_relat_1('#skF_6') | A_46='#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_153, c_14153])).
% 40.97/28.73  tff(c_14289, plain, (![A_4058, A_4059]: ('#skF_4'(A_4058, k1_tarski(A_4059), '#skF_6')=A_4059 | ~r2_hidden(A_4058, k1_xboole_0) | A_4059='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_52, c_14266])).
% 40.97/28.73  tff(c_660, plain, (![A_88, B_89, C_90]: (r2_hidden('#skF_4'(A_88, B_89, C_90), k1_relat_1(C_90)) | ~r2_hidden(A_88, k9_relat_1(C_90, B_89)) | ~v1_relat_1(C_90))), inference(cnfTransformation, [status(thm)], [f_68])).
% 40.97/28.73  tff(c_669, plain, (![A_88, B_89]: (r2_hidden('#skF_4'(A_88, B_89, '#skF_6'), k1_xboole_0) | ~r2_hidden(A_88, k9_relat_1('#skF_6', B_89)) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_266, c_660])).
% 40.97/28.73  tff(c_675, plain, (![A_91, B_92]: (r2_hidden('#skF_4'(A_91, B_92, '#skF_6'), k1_xboole_0) | ~r2_hidden(A_91, k9_relat_1('#skF_6', B_92)))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_669])).
% 40.97/28.73  tff(c_268, plain, (![C_32]: (C_32='#skF_5' | ~r2_hidden(C_32, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_266, c_76])).
% 40.97/28.73  tff(c_688, plain, (![A_93, B_94]: ('#skF_4'(A_93, B_94, '#skF_6')='#skF_5' | ~r2_hidden(A_93, k9_relat_1('#skF_6', B_94)))), inference(resolution, [status(thm)], [c_675, c_268])).
% 40.97/28.73  tff(c_711, plain, (![A_93, B_17]: ('#skF_4'(A_93, k1_tarski(B_17), '#skF_6')='#skF_5' | ~r2_hidden(A_93, k11_relat_1('#skF_6', B_17)) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_24, c_688])).
% 40.97/28.73  tff(c_724, plain, (![A_95, B_96]: ('#skF_4'(A_95, k1_tarski(B_96), '#skF_6')='#skF_5' | ~r2_hidden(A_95, k11_relat_1('#skF_6', B_96)))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_711])).
% 40.97/28.73  tff(c_749, plain, (![A_95, A_46]: ('#skF_4'(A_95, k1_tarski(A_46), '#skF_6')='#skF_5' | ~r2_hidden(A_95, k1_xboole_0) | A_46='#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_153, c_724])).
% 40.97/28.73  tff(c_14307, plain, (![A_4059, A_4058]: (A_4059='#skF_5' | ~r2_hidden(A_4058, k1_xboole_0) | A_4059='#skF_5' | ~r2_hidden(A_4058, k1_xboole_0) | A_4059='#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_14289, c_749])).
% 40.97/28.73  tff(c_14790, plain, (![A_4180]: (~r2_hidden(A_4180, k1_xboole_0) | ~r2_hidden(A_4180, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_14307])).
% 40.97/28.73  tff(c_14809, plain, (~r2_hidden('#skF_5', k1_xboole_0)), inference(resolution, [status(thm)], [c_269, c_14790])).
% 40.97/28.73  tff(c_14828, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_269, c_14809])).
% 40.97/28.73  tff(c_14829, plain, (![A_4059]: (A_4059='#skF_5' | A_4059='#skF_5' | A_4059='#skF_5')), inference(splitRight, [status(thm)], [c_14307])).
% 40.97/28.73  tff(c_14890, plain, (![A_4059]: (A_4059='#skF_5')), inference(factorization, [status(thm), theory('equality')], [c_14829])).
% 40.97/28.73  tff(c_15429, plain, (![A_10388]: (A_10388='#skF_5')), inference(factorization, [status(thm), theory('equality')], [c_14829])).
% 40.97/28.73  tff(c_46, plain, (k1_tarski(k1_funct_1('#skF_6', '#skF_5'))!=k2_relat_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_98])).
% 40.97/28.73  tff(c_15584, plain, (k2_relat_1('#skF_6')!='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_15429, c_46])).
% 40.97/28.73  tff(c_15624, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_14890, c_15584])).
% 40.97/28.73  tff(c_15626, plain, (k1_relat_1('#skF_6')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_202])).
% 40.97/28.73  tff(c_15627, plain, (![B_11957]: ('#skF_3'(k1_relat_1('#skF_6'), B_11957)='#skF_5' | k1_tarski(B_11957)=k1_relat_1('#skF_6'))), inference(splitRight, [status(thm)], [c_202])).
% 40.97/28.73  tff(c_20, plain, (![A_12, B_13]: ('#skF_3'(A_12, B_13)!=B_13 | k1_xboole_0=A_12 | k1_tarski(B_13)=A_12)), inference(cnfTransformation, [status(thm)], [f_52])).
% 40.97/28.73  tff(c_15635, plain, (![B_11957]: (B_11957!='#skF_5' | k1_relat_1('#skF_6')=k1_xboole_0 | k1_tarski(B_11957)=k1_relat_1('#skF_6') | k1_tarski(B_11957)=k1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_15627, c_20])).
% 40.97/28.73  tff(c_15642, plain, (![B_11957]: (B_11957!='#skF_5' | k1_tarski(B_11957)=k1_relat_1('#skF_6') | k1_tarski(B_11957)=k1_relat_1('#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_15626, c_15635])).
% 40.97/28.73  tff(c_15676, plain, (![B_11959]: (B_11959!='#skF_5' | k1_tarski(B_11959)=k1_relat_1('#skF_6'))), inference(factorization, [status(thm), theory('equality')], [c_15642])).
% 40.97/28.73  tff(c_15781, plain, (![A_11971, B_11972]: (k9_relat_1(A_11971, k1_relat_1('#skF_6'))=k11_relat_1(A_11971, B_11972) | ~v1_relat_1(A_11971) | B_11972!='#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_15676, c_24])).
% 40.97/28.73  tff(c_15802, plain, (![B_11972]: (k11_relat_1('#skF_6', B_11972)=k2_relat_1('#skF_6') | ~v1_relat_1('#skF_6') | ~v1_relat_1('#skF_6') | B_11972!='#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_15781, c_34])).
% 40.97/28.73  tff(c_15831, plain, (k11_relat_1('#skF_6', '#skF_5')=k2_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_52, c_15802])).
% 40.97/28.73  tff(c_15976, plain, (![A_11984, B_11985, C_11986]: (r2_hidden('#skF_4'(A_11984, B_11985, C_11986), k1_relat_1(C_11986)) | ~r2_hidden(A_11984, k9_relat_1(C_11986, B_11985)) | ~v1_relat_1(C_11986))), inference(cnfTransformation, [status(thm)], [f_68])).
% 40.97/28.73  tff(c_15986, plain, (![A_11984, B_11985]: ('#skF_4'(A_11984, B_11985, '#skF_6')='#skF_5' | ~r2_hidden(A_11984, k9_relat_1('#skF_6', B_11985)) | ~v1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_15976, c_76])).
% 40.97/28.73  tff(c_15993, plain, (![A_11984, B_11985]: ('#skF_4'(A_11984, B_11985, '#skF_6')='#skF_5' | ~r2_hidden(A_11984, k9_relat_1('#skF_6', B_11985)))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_15986])).
% 40.97/28.73  tff(c_249264, plain, (![A_137241]: ('#skF_4'(k1_funct_1('#skF_6', A_137241), k1_relat_1('#skF_6'), '#skF_6')='#skF_5' | ~r2_hidden(A_137241, k1_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_249238, c_15993])).
% 40.97/28.73  tff(c_251501, plain, (![A_137855]: ('#skF_4'(k1_funct_1('#skF_6', A_137855), k1_relat_1('#skF_6'), '#skF_6')='#skF_5' | ~r2_hidden(A_137855, k1_relat_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_249264])).
% 40.97/28.73  tff(c_121, plain, (![A_41]: (k9_relat_1(A_41, k1_relat_1('#skF_6'))=k11_relat_1(A_41, '#skF_5') | ~v1_relat_1(A_41))), inference(superposition, [status(thm), theory('equality')], [c_48, c_112])).
% 40.97/28.73  tff(c_16103, plain, (![A_11992, B_11993, C_11994]: (r2_hidden(k4_tarski('#skF_4'(A_11992, B_11993, C_11994), A_11992), C_11994) | ~r2_hidden(A_11992, k9_relat_1(C_11994, B_11993)) | ~v1_relat_1(C_11994))), inference(cnfTransformation, [status(thm)], [f_68])).
% 40.97/28.73  tff(c_42, plain, (![C_29, A_27, B_28]: (k1_funct_1(C_29, A_27)=B_28 | ~r2_hidden(k4_tarski(A_27, B_28), C_29) | ~v1_funct_1(C_29) | ~v1_relat_1(C_29))), inference(cnfTransformation, [status(thm)], [f_89])).
% 40.97/28.73  tff(c_21646, plain, (![C_20282, A_20283, B_20284]: (k1_funct_1(C_20282, '#skF_4'(A_20283, B_20284, C_20282))=A_20283 | ~v1_funct_1(C_20282) | ~r2_hidden(A_20283, k9_relat_1(C_20282, B_20284)) | ~v1_relat_1(C_20282))), inference(resolution, [status(thm)], [c_16103, c_42])).
% 40.97/28.73  tff(c_21682, plain, (![A_41, A_20283]: (k1_funct_1(A_41, '#skF_4'(A_20283, k1_relat_1('#skF_6'), A_41))=A_20283 | ~v1_funct_1(A_41) | ~r2_hidden(A_20283, k11_relat_1(A_41, '#skF_5')) | ~v1_relat_1(A_41) | ~v1_relat_1(A_41))), inference(superposition, [status(thm), theory('equality')], [c_121, c_21646])).
% 40.97/28.73  tff(c_251536, plain, (![A_137855]: (k1_funct_1('#skF_6', A_137855)=k1_funct_1('#skF_6', '#skF_5') | ~v1_funct_1('#skF_6') | ~r2_hidden(k1_funct_1('#skF_6', A_137855), k11_relat_1('#skF_6', '#skF_5')) | ~v1_relat_1('#skF_6') | ~v1_relat_1('#skF_6') | ~r2_hidden(A_137855, k1_relat_1('#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_251501, c_21682])).
% 40.97/28.73  tff(c_261746, plain, (![A_139292]: (k1_funct_1('#skF_6', A_139292)=k1_funct_1('#skF_6', '#skF_5') | ~r2_hidden(k1_funct_1('#skF_6', A_139292), k2_relat_1('#skF_6')) | ~r2_hidden(A_139292, k1_relat_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_52, c_15831, c_50, c_251536])).
% 40.97/28.73  tff(c_261750, plain, (![A_137241]: (k1_funct_1('#skF_6', A_137241)=k1_funct_1('#skF_6', '#skF_5') | ~r2_hidden(A_137241, k1_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_250305, c_261746])).
% 40.97/28.73  tff(c_262186, plain, (![A_139496]: (k1_funct_1('#skF_6', A_139496)=k1_funct_1('#skF_6', '#skF_5') | ~r2_hidden(A_139496, k1_relat_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_261750])).
% 40.97/28.73  tff(c_262551, plain, (![A_18, B_19]: (k1_funct_1('#skF_6', '#skF_4'(A_18, B_19, '#skF_6'))=k1_funct_1('#skF_6', '#skF_5') | ~r2_hidden(A_18, k9_relat_1('#skF_6', B_19)) | ~v1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_32, c_262186])).
% 40.97/28.73  tff(c_289446, plain, (![A_145022, B_145023]: (k1_funct_1('#skF_6', '#skF_4'(A_145022, B_145023, '#skF_6'))=k1_funct_1('#skF_6', '#skF_5') | ~r2_hidden(A_145022, k9_relat_1('#skF_6', B_145023)))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_262551])).
% 40.97/28.73  tff(c_290038, plain, (![A_145022]: (k1_funct_1('#skF_6', '#skF_4'(A_145022, k1_relat_1('#skF_6'), '#skF_6'))=k1_funct_1('#skF_6', '#skF_5') | ~r2_hidden(A_145022, k2_relat_1('#skF_6')) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_34, c_289446])).
% 40.97/28.73  tff(c_295683, plain, (![A_146049]: (k1_funct_1('#skF_6', '#skF_4'(A_146049, k1_relat_1('#skF_6'), '#skF_6'))=k1_funct_1('#skF_6', '#skF_5') | ~r2_hidden(A_146049, k2_relat_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_290038])).
% 40.97/28.73  tff(c_21686, plain, (![A_24, A_20283]: (k1_funct_1(A_24, '#skF_4'(A_20283, k1_relat_1(A_24), A_24))=A_20283 | ~v1_funct_1(A_24) | ~r2_hidden(A_20283, k2_relat_1(A_24)) | ~v1_relat_1(A_24) | ~v1_relat_1(A_24))), inference(superposition, [status(thm), theory('equality')], [c_34, c_21646])).
% 40.97/28.73  tff(c_295822, plain, (![A_146049]: (k1_funct_1('#skF_6', '#skF_5')=A_146049 | ~v1_funct_1('#skF_6') | ~r2_hidden(A_146049, k2_relat_1('#skF_6')) | ~v1_relat_1('#skF_6') | ~v1_relat_1('#skF_6') | ~r2_hidden(A_146049, k2_relat_1('#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_295683, c_21686])).
% 40.97/28.73  tff(c_297094, plain, (![A_146253]: (k1_funct_1('#skF_6', '#skF_5')=A_146253 | ~r2_hidden(A_146253, k2_relat_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_52, c_50, c_295822])).
% 40.97/28.73  tff(c_297349, plain, (![B_13]: ('#skF_3'(k2_relat_1('#skF_6'), B_13)=k1_funct_1('#skF_6', '#skF_5') | k2_relat_1('#skF_6')=k1_xboole_0 | k2_relat_1('#skF_6')=k1_tarski(B_13))), inference(resolution, [status(thm)], [c_22, c_297094])).
% 40.97/28.73  tff(c_297368, plain, (![B_146457]: ('#skF_3'(k2_relat_1('#skF_6'), B_146457)=k1_funct_1('#skF_6', '#skF_5') | k2_relat_1('#skF_6')=k1_tarski(B_146457))), inference(negUnitSimplification, [status(thm)], [c_187, c_297349])).
% 40.97/28.73  tff(c_297394, plain, (![B_146457]: (k1_funct_1('#skF_6', '#skF_5')!=B_146457 | k2_relat_1('#skF_6')=k1_xboole_0 | k2_relat_1('#skF_6')=k1_tarski(B_146457) | k2_relat_1('#skF_6')=k1_tarski(B_146457))), inference(superposition, [status(thm), theory('equality')], [c_297368, c_20])).
% 40.97/28.73  tff(c_299064, plain, (k1_tarski(k1_funct_1('#skF_6', '#skF_5'))=k2_relat_1('#skF_6')), inference(negUnitSimplification, [status(thm)], [c_187, c_297394])).
% 40.97/28.73  tff(c_299068, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_299064, c_46])).
% 40.97/28.73  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 40.97/28.73  
% 40.97/28.73  Inference rules
% 40.97/28.73  ----------------------
% 40.97/28.73  #Ref     : 22
% 40.97/28.73  #Sup     : 40044
% 40.97/28.73  #Fact    : 39
% 40.97/28.73  #Define  : 0
% 40.97/28.73  #Split   : 29
% 40.97/28.73  #Chain   : 0
% 40.97/28.73  #Close   : 0
% 40.97/28.73  
% 40.97/28.73  Ordering : KBO
% 40.97/28.73  
% 40.97/28.73  Simplification rules
% 40.97/28.73  ----------------------
% 40.97/28.73  #Subsume      : 9399
% 40.97/28.73  #Demod        : 4640
% 40.97/28.73  #Tautology    : 3185
% 40.97/28.73  #SimpNegUnit  : 1118
% 40.97/28.73  #BackRed      : 72
% 40.97/28.73  
% 40.97/28.73  #Partial instantiations: 75661
% 40.97/28.73  #Strategies tried      : 1
% 40.97/28.73  
% 40.97/28.73  Timing (in seconds)
% 40.97/28.73  ----------------------
% 40.97/28.73  Preprocessing        : 0.31
% 40.97/28.73  Parsing              : 0.16
% 40.97/28.73  CNF conversion       : 0.02
% 40.97/28.73  Main loop            : 27.65
% 40.97/28.73  Inferencing          : 3.98
% 40.97/28.73  Reduction            : 5.35
% 40.97/28.73  Demodulation         : 3.61
% 40.97/28.73  BG Simplification    : 0.64
% 40.97/28.73  Subsumption          : 16.01
% 40.97/28.73  Abstraction          : 0.67
% 40.97/28.73  MUC search           : 0.00
% 40.97/28.73  Cooper               : 0.00
% 40.97/28.73  Total                : 28.01
% 40.97/28.73  Index Insertion      : 0.00
% 40.97/28.73  Index Deletion       : 0.00
% 40.97/28.73  Index Matching       : 0.00
% 40.97/28.73  BG Taut test         : 0.00
%------------------------------------------------------------------------------
