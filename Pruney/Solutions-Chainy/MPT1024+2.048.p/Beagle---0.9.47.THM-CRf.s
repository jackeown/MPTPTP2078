%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:28 EST 2020

% Result     : Theorem 3.85s
% Output     : CNFRefutation 3.85s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 275 expanded)
%              Number of leaves         :   40 ( 112 expanded)
%              Depth                    :   11
%              Number of atoms          :  204 ( 728 expanded)
%              Number of equality atoms :   47 ( 149 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_9 > #skF_4 > #skF_8 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_126,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [E] :
            ~ ( r2_hidden(E,k7_relset_1(A,B,D,C))
              & ! [F] :
                  ~ ( r2_hidden(F,A)
                    & r2_hidden(F,C)
                    & E = k1_funct_1(D,F) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t115_funct_2)).

tff(f_89,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_81,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k7_relset_1(A,B,C,D),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relset_1)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_55,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_53,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_72,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B,C] :
          ( C = k9_relat_1(A,B)
        <=> ! [D] :
              ( r2_hidden(D,C)
            <=> ? [E] :
                  ( r2_hidden(E,k1_relat_1(A))
                  & r2_hidden(E,B)
                  & D = k1_funct_1(A,E) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_funct_1)).

tff(f_85,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_107,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_77,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(c_62,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_609,plain,(
    ! [A_207,B_208,C_209,D_210] :
      ( k7_relset_1(A_207,B_208,C_209,D_210) = k9_relat_1(C_209,D_210)
      | ~ m1_subset_1(C_209,k1_zfmisc_1(k2_zfmisc_1(A_207,B_208))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_619,plain,(
    ! [D_211] : k7_relset_1('#skF_5','#skF_6','#skF_8',D_211) = k9_relat_1('#skF_8',D_211) ),
    inference(resolution,[status(thm)],[c_62,c_609])).

tff(c_40,plain,(
    ! [A_59,B_60,C_61,D_62] :
      ( m1_subset_1(k7_relset_1(A_59,B_60,C_61,D_62),k1_zfmisc_1(B_60))
      | ~ m1_subset_1(C_61,k1_zfmisc_1(k2_zfmisc_1(A_59,B_60))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_625,plain,(
    ! [D_211] :
      ( m1_subset_1(k9_relat_1('#skF_8',D_211),k1_zfmisc_1('#skF_6'))
      | ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_619,c_40])).

tff(c_643,plain,(
    ! [D_214] : m1_subset_1(k9_relat_1('#skF_8',D_214),k1_zfmisc_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_625])).

tff(c_8,plain,(
    ! [C_9,B_8,A_7] :
      ( ~ v1_xboole_0(C_9)
      | ~ m1_subset_1(B_8,k1_zfmisc_1(C_9))
      | ~ r2_hidden(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_652,plain,(
    ! [A_7,D_214] :
      ( ~ v1_xboole_0('#skF_6')
      | ~ r2_hidden(A_7,k9_relat_1('#skF_8',D_214)) ) ),
    inference(resolution,[status(thm)],[c_643,c_8])).

tff(c_655,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_652])).

tff(c_12,plain,(
    ! [A_13,B_14] : v1_relat_1(k2_zfmisc_1(A_13,B_14)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_74,plain,(
    ! [B_83,A_84] :
      ( v1_relat_1(B_83)
      | ~ m1_subset_1(B_83,k1_zfmisc_1(A_84))
      | ~ v1_relat_1(A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_77,plain,
    ( v1_relat_1('#skF_8')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_62,c_74])).

tff(c_80,plain,(
    v1_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_77])).

tff(c_66,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_16,plain,(
    ! [A_15,B_38,D_53] :
      ( k1_funct_1(A_15,'#skF_4'(A_15,B_38,k9_relat_1(A_15,B_38),D_53)) = D_53
      | ~ r2_hidden(D_53,k9_relat_1(A_15,B_38))
      | ~ v1_funct_1(A_15)
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_64,plain,(
    v1_funct_2('#skF_8','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_569,plain,(
    ! [A_195,B_196,C_197] :
      ( k1_relset_1(A_195,B_196,C_197) = k1_relat_1(C_197)
      | ~ m1_subset_1(C_197,k1_zfmisc_1(k2_zfmisc_1(A_195,B_196))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_573,plain,(
    k1_relset_1('#skF_5','#skF_6','#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_62,c_569])).

tff(c_711,plain,(
    ! [B_238,A_239,C_240] :
      ( k1_xboole_0 = B_238
      | k1_relset_1(A_239,B_238,C_240) = A_239
      | ~ v1_funct_2(C_240,A_239,B_238)
      | ~ m1_subset_1(C_240,k1_zfmisc_1(k2_zfmisc_1(A_239,B_238))) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_718,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_relset_1('#skF_5','#skF_6','#skF_8') = '#skF_5'
    | ~ v1_funct_2('#skF_8','#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_62,c_711])).

tff(c_722,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_relat_1('#skF_8') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_573,c_718])).

tff(c_723,plain,(
    k1_relat_1('#skF_8') = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_722])).

tff(c_950,plain,(
    ! [A_277,B_278,D_279] :
      ( r2_hidden('#skF_4'(A_277,B_278,k9_relat_1(A_277,B_278),D_279),k1_relat_1(A_277))
      | ~ r2_hidden(D_279,k9_relat_1(A_277,B_278))
      | ~ v1_funct_1(A_277)
      | ~ v1_relat_1(A_277) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_961,plain,(
    ! [B_278,D_279] :
      ( r2_hidden('#skF_4'('#skF_8',B_278,k9_relat_1('#skF_8',B_278),D_279),'#skF_5')
      | ~ r2_hidden(D_279,k9_relat_1('#skF_8',B_278))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_723,c_950])).

tff(c_973,plain,(
    ! [B_283,D_284] :
      ( r2_hidden('#skF_4'('#skF_8',B_283,k9_relat_1('#skF_8',B_283),D_284),'#skF_5')
      | ~ r2_hidden(D_284,k9_relat_1('#skF_8',B_283)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_66,c_961])).

tff(c_791,plain,(
    ! [A_249,B_250,D_251] :
      ( r2_hidden('#skF_4'(A_249,B_250,k9_relat_1(A_249,B_250),D_251),B_250)
      | ~ r2_hidden(D_251,k9_relat_1(A_249,B_250))
      | ~ v1_funct_1(A_249)
      | ~ v1_relat_1(A_249) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_58,plain,(
    ! [F_77] :
      ( k1_funct_1('#skF_8',F_77) != '#skF_9'
      | ~ r2_hidden(F_77,'#skF_7')
      | ~ r2_hidden(F_77,'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_820,plain,(
    ! [A_249,D_251] :
      ( k1_funct_1('#skF_8','#skF_4'(A_249,'#skF_7',k9_relat_1(A_249,'#skF_7'),D_251)) != '#skF_9'
      | ~ r2_hidden('#skF_4'(A_249,'#skF_7',k9_relat_1(A_249,'#skF_7'),D_251),'#skF_5')
      | ~ r2_hidden(D_251,k9_relat_1(A_249,'#skF_7'))
      | ~ v1_funct_1(A_249)
      | ~ v1_relat_1(A_249) ) ),
    inference(resolution,[status(thm)],[c_791,c_58])).

tff(c_977,plain,(
    ! [D_284] :
      ( k1_funct_1('#skF_8','#skF_4'('#skF_8','#skF_7',k9_relat_1('#skF_8','#skF_7'),D_284)) != '#skF_9'
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8')
      | ~ r2_hidden(D_284,k9_relat_1('#skF_8','#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_973,c_820])).

tff(c_993,plain,(
    ! [D_287] :
      ( k1_funct_1('#skF_8','#skF_4'('#skF_8','#skF_7',k9_relat_1('#skF_8','#skF_7'),D_287)) != '#skF_9'
      | ~ r2_hidden(D_287,k9_relat_1('#skF_8','#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_66,c_977])).

tff(c_997,plain,(
    ! [D_53] :
      ( D_53 != '#skF_9'
      | ~ r2_hidden(D_53,k9_relat_1('#skF_8','#skF_7'))
      | ~ r2_hidden(D_53,k9_relat_1('#skF_8','#skF_7'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_993])).

tff(c_1001,plain,(
    ~ r2_hidden('#skF_9',k9_relat_1('#skF_8','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_66,c_997])).

tff(c_616,plain,(
    ! [D_210] : k7_relset_1('#skF_5','#skF_6','#skF_8',D_210) = k9_relat_1('#skF_8',D_210) ),
    inference(resolution,[status(thm)],[c_62,c_609])).

tff(c_60,plain,(
    r2_hidden('#skF_9',k7_relset_1('#skF_5','#skF_6','#skF_8','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_618,plain,(
    r2_hidden('#skF_9',k9_relat_1('#skF_8','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_616,c_60])).

tff(c_1003,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1001,c_618])).

tff(c_1004,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_722])).

tff(c_110,plain,(
    ! [A_99,B_100,C_101] :
      ( k1_relset_1(A_99,B_100,C_101) = k1_relat_1(C_101)
      | ~ m1_subset_1(C_101,k1_zfmisc_1(k2_zfmisc_1(A_99,B_100))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_114,plain,(
    k1_relset_1('#skF_5','#skF_6','#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_62,c_110])).

tff(c_232,plain,(
    ! [B_133,A_134,C_135] :
      ( k1_xboole_0 = B_133
      | k1_relset_1(A_134,B_133,C_135) = A_134
      | ~ v1_funct_2(C_135,A_134,B_133)
      | ~ m1_subset_1(C_135,k1_zfmisc_1(k2_zfmisc_1(A_134,B_133))) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_239,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_relset_1('#skF_5','#skF_6','#skF_8') = '#skF_5'
    | ~ v1_funct_2('#skF_8','#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_62,c_232])).

tff(c_243,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_relat_1('#skF_8') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_114,c_239])).

tff(c_244,plain,(
    k1_relat_1('#skF_8') = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_243])).

tff(c_446,plain,(
    ! [A_172,B_173,D_174] :
      ( r2_hidden('#skF_4'(A_172,B_173,k9_relat_1(A_172,B_173),D_174),k1_relat_1(A_172))
      | ~ r2_hidden(D_174,k9_relat_1(A_172,B_173))
      | ~ v1_funct_1(A_172)
      | ~ v1_relat_1(A_172) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_457,plain,(
    ! [B_173,D_174] :
      ( r2_hidden('#skF_4'('#skF_8',B_173,k9_relat_1('#skF_8',B_173),D_174),'#skF_5')
      | ~ r2_hidden(D_174,k9_relat_1('#skF_8',B_173))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_244,c_446])).

tff(c_474,plain,(
    ! [B_176,D_177] :
      ( r2_hidden('#skF_4'('#skF_8',B_176,k9_relat_1('#skF_8',B_176),D_177),'#skF_5')
      | ~ r2_hidden(D_177,k9_relat_1('#skF_8',B_176)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_66,c_457])).

tff(c_302,plain,(
    ! [A_149,B_150,D_151] :
      ( r2_hidden('#skF_4'(A_149,B_150,k9_relat_1(A_149,B_150),D_151),B_150)
      | ~ r2_hidden(D_151,k9_relat_1(A_149,B_150))
      | ~ v1_funct_1(A_149)
      | ~ v1_relat_1(A_149) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_331,plain,(
    ! [A_149,D_151] :
      ( k1_funct_1('#skF_8','#skF_4'(A_149,'#skF_7',k9_relat_1(A_149,'#skF_7'),D_151)) != '#skF_9'
      | ~ r2_hidden('#skF_4'(A_149,'#skF_7',k9_relat_1(A_149,'#skF_7'),D_151),'#skF_5')
      | ~ r2_hidden(D_151,k9_relat_1(A_149,'#skF_7'))
      | ~ v1_funct_1(A_149)
      | ~ v1_relat_1(A_149) ) ),
    inference(resolution,[status(thm)],[c_302,c_58])).

tff(c_478,plain,(
    ! [D_177] :
      ( k1_funct_1('#skF_8','#skF_4'('#skF_8','#skF_7',k9_relat_1('#skF_8','#skF_7'),D_177)) != '#skF_9'
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8')
      | ~ r2_hidden(D_177,k9_relat_1('#skF_8','#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_474,c_331])).

tff(c_511,plain,(
    ! [D_183] :
      ( k1_funct_1('#skF_8','#skF_4'('#skF_8','#skF_7',k9_relat_1('#skF_8','#skF_7'),D_183)) != '#skF_9'
      | ~ r2_hidden(D_183,k9_relat_1('#skF_8','#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_66,c_478])).

tff(c_515,plain,(
    ! [D_53] :
      ( D_53 != '#skF_9'
      | ~ r2_hidden(D_53,k9_relat_1('#skF_8','#skF_7'))
      | ~ r2_hidden(D_53,k9_relat_1('#skF_8','#skF_7'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_511])).

tff(c_518,plain,(
    ~ r2_hidden('#skF_9',k9_relat_1('#skF_8','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_66,c_515])).

tff(c_150,plain,(
    ! [A_110,B_111,C_112,D_113] :
      ( k7_relset_1(A_110,B_111,C_112,D_113) = k9_relat_1(C_112,D_113)
      | ~ m1_subset_1(C_112,k1_zfmisc_1(k2_zfmisc_1(A_110,B_111))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_157,plain,(
    ! [D_113] : k7_relset_1('#skF_5','#skF_6','#skF_8',D_113) = k9_relat_1('#skF_8',D_113) ),
    inference(resolution,[status(thm)],[c_62,c_150])).

tff(c_159,plain,(
    r2_hidden('#skF_9',k9_relat_1('#skF_8','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_157,c_60])).

tff(c_520,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_518,c_159])).

tff(c_521,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_243])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_82,plain,(
    ! [A_86,B_87] :
      ( r2_hidden(A_86,B_87)
      | v1_xboole_0(B_87)
      | ~ m1_subset_1(A_86,B_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_38,plain,(
    ! [B_58,A_57] :
      ( ~ r1_tarski(B_58,A_57)
      | ~ r2_hidden(A_57,B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_92,plain,(
    ! [B_88,A_89] :
      ( ~ r1_tarski(B_88,A_89)
      | v1_xboole_0(B_88)
      | ~ m1_subset_1(A_89,B_88) ) ),
    inference(resolution,[status(thm)],[c_82,c_38])).

tff(c_96,plain,(
    ! [A_1] :
      ( v1_xboole_0(k1_xboole_0)
      | ~ m1_subset_1(A_1,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_2,c_92])).

tff(c_97,plain,(
    ! [A_1] : ~ m1_subset_1(A_1,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_96])).

tff(c_528,plain,(
    ! [A_1] : ~ m1_subset_1(A_1,'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_521,c_97])).

tff(c_160,plain,(
    ! [D_114] : k7_relset_1('#skF_5','#skF_6','#skF_8',D_114) = k9_relat_1('#skF_8',D_114) ),
    inference(resolution,[status(thm)],[c_62,c_150])).

tff(c_166,plain,(
    ! [D_114] :
      ( m1_subset_1(k9_relat_1('#skF_8',D_114),k1_zfmisc_1('#skF_6'))
      | ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_160,c_40])).

tff(c_178,plain,(
    ! [D_115] : m1_subset_1(k9_relat_1('#skF_8',D_115),k1_zfmisc_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_166])).

tff(c_6,plain,(
    ! [A_4,C_6,B_5] :
      ( m1_subset_1(A_4,C_6)
      | ~ m1_subset_1(B_5,k1_zfmisc_1(C_6))
      | ~ r2_hidden(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_197,plain,(
    ! [A_118,D_119] :
      ( m1_subset_1(A_118,'#skF_6')
      | ~ r2_hidden(A_118,k9_relat_1('#skF_8',D_119)) ) ),
    inference(resolution,[status(thm)],[c_178,c_6])).

tff(c_205,plain,(
    m1_subset_1('#skF_9','#skF_6') ),
    inference(resolution,[status(thm)],[c_159,c_197])).

tff(c_556,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_528,c_205])).

tff(c_557,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_96])).

tff(c_1012,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1004,c_557])).

tff(c_1015,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_655,c_1012])).

tff(c_1016,plain,(
    ! [A_7,D_214] : ~ r2_hidden(A_7,k9_relat_1('#skF_8',D_214)) ),
    inference(splitRight,[status(thm)],[c_652])).

tff(c_1019,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1016,c_618])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n008.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:34:45 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.85/1.64  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.85/1.65  
% 3.85/1.65  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.85/1.66  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_9 > #skF_4 > #skF_8 > #skF_3
% 3.85/1.66  
% 3.85/1.66  %Foreground sorts:
% 3.85/1.66  
% 3.85/1.66  
% 3.85/1.66  %Background operators:
% 3.85/1.66  
% 3.85/1.66  
% 3.85/1.66  %Foreground operators:
% 3.85/1.66  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.85/1.66  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.85/1.66  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.85/1.66  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.85/1.66  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.85/1.66  tff('#skF_7', type, '#skF_7': $i).
% 3.85/1.66  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.85/1.66  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 3.85/1.66  tff('#skF_5', type, '#skF_5': $i).
% 3.85/1.66  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.85/1.66  tff('#skF_6', type, '#skF_6': $i).
% 3.85/1.66  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.85/1.66  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.85/1.66  tff('#skF_9', type, '#skF_9': $i).
% 3.85/1.66  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.85/1.66  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.85/1.66  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.85/1.66  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 3.85/1.66  tff('#skF_8', type, '#skF_8': $i).
% 3.85/1.66  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.85/1.66  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.85/1.66  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.85/1.66  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.85/1.66  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.85/1.66  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.85/1.66  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.85/1.66  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.85/1.66  
% 3.85/1.68  tff(f_126, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: ~(r2_hidden(E, k7_relset_1(A, B, D, C)) & (![F]: ~((r2_hidden(F, A) & r2_hidden(F, C)) & (E = k1_funct_1(D, F)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t115_funct_2)).
% 3.85/1.68  tff(f_89, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 3.85/1.68  tff(f_81, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k7_relset_1(A, B, C, D), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relset_1)).
% 3.85/1.68  tff(f_46, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 3.85/1.68  tff(f_55, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.85/1.68  tff(f_53, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.85/1.68  tff(f_72, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: ((C = k9_relat_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E]: ((r2_hidden(E, k1_relat_1(A)) & r2_hidden(E, B)) & (D = k1_funct_1(A, E)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_funct_1)).
% 3.85/1.68  tff(f_85, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.85/1.68  tff(f_107, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 3.85/1.68  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.85/1.68  tff(f_33, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 3.85/1.68  tff(f_77, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 3.85/1.68  tff(f_39, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 3.85/1.68  tff(c_62, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.85/1.68  tff(c_609, plain, (![A_207, B_208, C_209, D_210]: (k7_relset_1(A_207, B_208, C_209, D_210)=k9_relat_1(C_209, D_210) | ~m1_subset_1(C_209, k1_zfmisc_1(k2_zfmisc_1(A_207, B_208))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.85/1.68  tff(c_619, plain, (![D_211]: (k7_relset_1('#skF_5', '#skF_6', '#skF_8', D_211)=k9_relat_1('#skF_8', D_211))), inference(resolution, [status(thm)], [c_62, c_609])).
% 3.85/1.68  tff(c_40, plain, (![A_59, B_60, C_61, D_62]: (m1_subset_1(k7_relset_1(A_59, B_60, C_61, D_62), k1_zfmisc_1(B_60)) | ~m1_subset_1(C_61, k1_zfmisc_1(k2_zfmisc_1(A_59, B_60))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.85/1.68  tff(c_625, plain, (![D_211]: (m1_subset_1(k9_relat_1('#skF_8', D_211), k1_zfmisc_1('#skF_6')) | ~m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6'))))), inference(superposition, [status(thm), theory('equality')], [c_619, c_40])).
% 3.85/1.68  tff(c_643, plain, (![D_214]: (m1_subset_1(k9_relat_1('#skF_8', D_214), k1_zfmisc_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_625])).
% 3.85/1.68  tff(c_8, plain, (![C_9, B_8, A_7]: (~v1_xboole_0(C_9) | ~m1_subset_1(B_8, k1_zfmisc_1(C_9)) | ~r2_hidden(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.85/1.68  tff(c_652, plain, (![A_7, D_214]: (~v1_xboole_0('#skF_6') | ~r2_hidden(A_7, k9_relat_1('#skF_8', D_214)))), inference(resolution, [status(thm)], [c_643, c_8])).
% 3.85/1.68  tff(c_655, plain, (~v1_xboole_0('#skF_6')), inference(splitLeft, [status(thm)], [c_652])).
% 3.85/1.68  tff(c_12, plain, (![A_13, B_14]: (v1_relat_1(k2_zfmisc_1(A_13, B_14)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.85/1.68  tff(c_74, plain, (![B_83, A_84]: (v1_relat_1(B_83) | ~m1_subset_1(B_83, k1_zfmisc_1(A_84)) | ~v1_relat_1(A_84))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.85/1.68  tff(c_77, plain, (v1_relat_1('#skF_8') | ~v1_relat_1(k2_zfmisc_1('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_62, c_74])).
% 3.85/1.68  tff(c_80, plain, (v1_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_77])).
% 3.85/1.68  tff(c_66, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.85/1.68  tff(c_16, plain, (![A_15, B_38, D_53]: (k1_funct_1(A_15, '#skF_4'(A_15, B_38, k9_relat_1(A_15, B_38), D_53))=D_53 | ~r2_hidden(D_53, k9_relat_1(A_15, B_38)) | ~v1_funct_1(A_15) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.85/1.68  tff(c_64, plain, (v1_funct_2('#skF_8', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.85/1.68  tff(c_569, plain, (![A_195, B_196, C_197]: (k1_relset_1(A_195, B_196, C_197)=k1_relat_1(C_197) | ~m1_subset_1(C_197, k1_zfmisc_1(k2_zfmisc_1(A_195, B_196))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.85/1.68  tff(c_573, plain, (k1_relset_1('#skF_5', '#skF_6', '#skF_8')=k1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_62, c_569])).
% 3.85/1.68  tff(c_711, plain, (![B_238, A_239, C_240]: (k1_xboole_0=B_238 | k1_relset_1(A_239, B_238, C_240)=A_239 | ~v1_funct_2(C_240, A_239, B_238) | ~m1_subset_1(C_240, k1_zfmisc_1(k2_zfmisc_1(A_239, B_238))))), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.85/1.68  tff(c_718, plain, (k1_xboole_0='#skF_6' | k1_relset_1('#skF_5', '#skF_6', '#skF_8')='#skF_5' | ~v1_funct_2('#skF_8', '#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_62, c_711])).
% 3.85/1.68  tff(c_722, plain, (k1_xboole_0='#skF_6' | k1_relat_1('#skF_8')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_573, c_718])).
% 3.85/1.68  tff(c_723, plain, (k1_relat_1('#skF_8')='#skF_5'), inference(splitLeft, [status(thm)], [c_722])).
% 3.85/1.68  tff(c_950, plain, (![A_277, B_278, D_279]: (r2_hidden('#skF_4'(A_277, B_278, k9_relat_1(A_277, B_278), D_279), k1_relat_1(A_277)) | ~r2_hidden(D_279, k9_relat_1(A_277, B_278)) | ~v1_funct_1(A_277) | ~v1_relat_1(A_277))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.85/1.68  tff(c_961, plain, (![B_278, D_279]: (r2_hidden('#skF_4'('#skF_8', B_278, k9_relat_1('#skF_8', B_278), D_279), '#skF_5') | ~r2_hidden(D_279, k9_relat_1('#skF_8', B_278)) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_723, c_950])).
% 3.85/1.68  tff(c_973, plain, (![B_283, D_284]: (r2_hidden('#skF_4'('#skF_8', B_283, k9_relat_1('#skF_8', B_283), D_284), '#skF_5') | ~r2_hidden(D_284, k9_relat_1('#skF_8', B_283)))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_66, c_961])).
% 3.85/1.68  tff(c_791, plain, (![A_249, B_250, D_251]: (r2_hidden('#skF_4'(A_249, B_250, k9_relat_1(A_249, B_250), D_251), B_250) | ~r2_hidden(D_251, k9_relat_1(A_249, B_250)) | ~v1_funct_1(A_249) | ~v1_relat_1(A_249))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.85/1.68  tff(c_58, plain, (![F_77]: (k1_funct_1('#skF_8', F_77)!='#skF_9' | ~r2_hidden(F_77, '#skF_7') | ~r2_hidden(F_77, '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.85/1.68  tff(c_820, plain, (![A_249, D_251]: (k1_funct_1('#skF_8', '#skF_4'(A_249, '#skF_7', k9_relat_1(A_249, '#skF_7'), D_251))!='#skF_9' | ~r2_hidden('#skF_4'(A_249, '#skF_7', k9_relat_1(A_249, '#skF_7'), D_251), '#skF_5') | ~r2_hidden(D_251, k9_relat_1(A_249, '#skF_7')) | ~v1_funct_1(A_249) | ~v1_relat_1(A_249))), inference(resolution, [status(thm)], [c_791, c_58])).
% 3.85/1.68  tff(c_977, plain, (![D_284]: (k1_funct_1('#skF_8', '#skF_4'('#skF_8', '#skF_7', k9_relat_1('#skF_8', '#skF_7'), D_284))!='#skF_9' | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~r2_hidden(D_284, k9_relat_1('#skF_8', '#skF_7')))), inference(resolution, [status(thm)], [c_973, c_820])).
% 3.85/1.68  tff(c_993, plain, (![D_287]: (k1_funct_1('#skF_8', '#skF_4'('#skF_8', '#skF_7', k9_relat_1('#skF_8', '#skF_7'), D_287))!='#skF_9' | ~r2_hidden(D_287, k9_relat_1('#skF_8', '#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_66, c_977])).
% 3.85/1.68  tff(c_997, plain, (![D_53]: (D_53!='#skF_9' | ~r2_hidden(D_53, k9_relat_1('#skF_8', '#skF_7')) | ~r2_hidden(D_53, k9_relat_1('#skF_8', '#skF_7')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_16, c_993])).
% 3.85/1.68  tff(c_1001, plain, (~r2_hidden('#skF_9', k9_relat_1('#skF_8', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_66, c_997])).
% 3.85/1.68  tff(c_616, plain, (![D_210]: (k7_relset_1('#skF_5', '#skF_6', '#skF_8', D_210)=k9_relat_1('#skF_8', D_210))), inference(resolution, [status(thm)], [c_62, c_609])).
% 3.85/1.68  tff(c_60, plain, (r2_hidden('#skF_9', k7_relset_1('#skF_5', '#skF_6', '#skF_8', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.85/1.68  tff(c_618, plain, (r2_hidden('#skF_9', k9_relat_1('#skF_8', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_616, c_60])).
% 3.85/1.68  tff(c_1003, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1001, c_618])).
% 3.85/1.68  tff(c_1004, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_722])).
% 3.85/1.68  tff(c_110, plain, (![A_99, B_100, C_101]: (k1_relset_1(A_99, B_100, C_101)=k1_relat_1(C_101) | ~m1_subset_1(C_101, k1_zfmisc_1(k2_zfmisc_1(A_99, B_100))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.85/1.68  tff(c_114, plain, (k1_relset_1('#skF_5', '#skF_6', '#skF_8')=k1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_62, c_110])).
% 3.85/1.68  tff(c_232, plain, (![B_133, A_134, C_135]: (k1_xboole_0=B_133 | k1_relset_1(A_134, B_133, C_135)=A_134 | ~v1_funct_2(C_135, A_134, B_133) | ~m1_subset_1(C_135, k1_zfmisc_1(k2_zfmisc_1(A_134, B_133))))), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.85/1.68  tff(c_239, plain, (k1_xboole_0='#skF_6' | k1_relset_1('#skF_5', '#skF_6', '#skF_8')='#skF_5' | ~v1_funct_2('#skF_8', '#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_62, c_232])).
% 3.85/1.68  tff(c_243, plain, (k1_xboole_0='#skF_6' | k1_relat_1('#skF_8')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_114, c_239])).
% 3.85/1.68  tff(c_244, plain, (k1_relat_1('#skF_8')='#skF_5'), inference(splitLeft, [status(thm)], [c_243])).
% 3.85/1.68  tff(c_446, plain, (![A_172, B_173, D_174]: (r2_hidden('#skF_4'(A_172, B_173, k9_relat_1(A_172, B_173), D_174), k1_relat_1(A_172)) | ~r2_hidden(D_174, k9_relat_1(A_172, B_173)) | ~v1_funct_1(A_172) | ~v1_relat_1(A_172))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.85/1.68  tff(c_457, plain, (![B_173, D_174]: (r2_hidden('#skF_4'('#skF_8', B_173, k9_relat_1('#skF_8', B_173), D_174), '#skF_5') | ~r2_hidden(D_174, k9_relat_1('#skF_8', B_173)) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_244, c_446])).
% 3.85/1.68  tff(c_474, plain, (![B_176, D_177]: (r2_hidden('#skF_4'('#skF_8', B_176, k9_relat_1('#skF_8', B_176), D_177), '#skF_5') | ~r2_hidden(D_177, k9_relat_1('#skF_8', B_176)))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_66, c_457])).
% 3.85/1.68  tff(c_302, plain, (![A_149, B_150, D_151]: (r2_hidden('#skF_4'(A_149, B_150, k9_relat_1(A_149, B_150), D_151), B_150) | ~r2_hidden(D_151, k9_relat_1(A_149, B_150)) | ~v1_funct_1(A_149) | ~v1_relat_1(A_149))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.85/1.68  tff(c_331, plain, (![A_149, D_151]: (k1_funct_1('#skF_8', '#skF_4'(A_149, '#skF_7', k9_relat_1(A_149, '#skF_7'), D_151))!='#skF_9' | ~r2_hidden('#skF_4'(A_149, '#skF_7', k9_relat_1(A_149, '#skF_7'), D_151), '#skF_5') | ~r2_hidden(D_151, k9_relat_1(A_149, '#skF_7')) | ~v1_funct_1(A_149) | ~v1_relat_1(A_149))), inference(resolution, [status(thm)], [c_302, c_58])).
% 3.85/1.68  tff(c_478, plain, (![D_177]: (k1_funct_1('#skF_8', '#skF_4'('#skF_8', '#skF_7', k9_relat_1('#skF_8', '#skF_7'), D_177))!='#skF_9' | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~r2_hidden(D_177, k9_relat_1('#skF_8', '#skF_7')))), inference(resolution, [status(thm)], [c_474, c_331])).
% 3.85/1.68  tff(c_511, plain, (![D_183]: (k1_funct_1('#skF_8', '#skF_4'('#skF_8', '#skF_7', k9_relat_1('#skF_8', '#skF_7'), D_183))!='#skF_9' | ~r2_hidden(D_183, k9_relat_1('#skF_8', '#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_66, c_478])).
% 3.85/1.68  tff(c_515, plain, (![D_53]: (D_53!='#skF_9' | ~r2_hidden(D_53, k9_relat_1('#skF_8', '#skF_7')) | ~r2_hidden(D_53, k9_relat_1('#skF_8', '#skF_7')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_16, c_511])).
% 3.85/1.68  tff(c_518, plain, (~r2_hidden('#skF_9', k9_relat_1('#skF_8', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_66, c_515])).
% 3.85/1.68  tff(c_150, plain, (![A_110, B_111, C_112, D_113]: (k7_relset_1(A_110, B_111, C_112, D_113)=k9_relat_1(C_112, D_113) | ~m1_subset_1(C_112, k1_zfmisc_1(k2_zfmisc_1(A_110, B_111))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.85/1.68  tff(c_157, plain, (![D_113]: (k7_relset_1('#skF_5', '#skF_6', '#skF_8', D_113)=k9_relat_1('#skF_8', D_113))), inference(resolution, [status(thm)], [c_62, c_150])).
% 3.85/1.68  tff(c_159, plain, (r2_hidden('#skF_9', k9_relat_1('#skF_8', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_157, c_60])).
% 3.85/1.68  tff(c_520, plain, $false, inference(negUnitSimplification, [status(thm)], [c_518, c_159])).
% 3.85/1.68  tff(c_521, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_243])).
% 3.85/1.68  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.85/1.68  tff(c_82, plain, (![A_86, B_87]: (r2_hidden(A_86, B_87) | v1_xboole_0(B_87) | ~m1_subset_1(A_86, B_87))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.85/1.68  tff(c_38, plain, (![B_58, A_57]: (~r1_tarski(B_58, A_57) | ~r2_hidden(A_57, B_58))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.85/1.68  tff(c_92, plain, (![B_88, A_89]: (~r1_tarski(B_88, A_89) | v1_xboole_0(B_88) | ~m1_subset_1(A_89, B_88))), inference(resolution, [status(thm)], [c_82, c_38])).
% 3.85/1.68  tff(c_96, plain, (![A_1]: (v1_xboole_0(k1_xboole_0) | ~m1_subset_1(A_1, k1_xboole_0))), inference(resolution, [status(thm)], [c_2, c_92])).
% 3.85/1.68  tff(c_97, plain, (![A_1]: (~m1_subset_1(A_1, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_96])).
% 3.85/1.68  tff(c_528, plain, (![A_1]: (~m1_subset_1(A_1, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_521, c_97])).
% 3.85/1.68  tff(c_160, plain, (![D_114]: (k7_relset_1('#skF_5', '#skF_6', '#skF_8', D_114)=k9_relat_1('#skF_8', D_114))), inference(resolution, [status(thm)], [c_62, c_150])).
% 3.85/1.68  tff(c_166, plain, (![D_114]: (m1_subset_1(k9_relat_1('#skF_8', D_114), k1_zfmisc_1('#skF_6')) | ~m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6'))))), inference(superposition, [status(thm), theory('equality')], [c_160, c_40])).
% 3.85/1.68  tff(c_178, plain, (![D_115]: (m1_subset_1(k9_relat_1('#skF_8', D_115), k1_zfmisc_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_166])).
% 3.85/1.68  tff(c_6, plain, (![A_4, C_6, B_5]: (m1_subset_1(A_4, C_6) | ~m1_subset_1(B_5, k1_zfmisc_1(C_6)) | ~r2_hidden(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.85/1.68  tff(c_197, plain, (![A_118, D_119]: (m1_subset_1(A_118, '#skF_6') | ~r2_hidden(A_118, k9_relat_1('#skF_8', D_119)))), inference(resolution, [status(thm)], [c_178, c_6])).
% 3.85/1.68  tff(c_205, plain, (m1_subset_1('#skF_9', '#skF_6')), inference(resolution, [status(thm)], [c_159, c_197])).
% 3.85/1.68  tff(c_556, plain, $false, inference(negUnitSimplification, [status(thm)], [c_528, c_205])).
% 3.85/1.68  tff(c_557, plain, (v1_xboole_0(k1_xboole_0)), inference(splitRight, [status(thm)], [c_96])).
% 3.85/1.68  tff(c_1012, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1004, c_557])).
% 3.85/1.68  tff(c_1015, plain, $false, inference(negUnitSimplification, [status(thm)], [c_655, c_1012])).
% 3.85/1.68  tff(c_1016, plain, (![A_7, D_214]: (~r2_hidden(A_7, k9_relat_1('#skF_8', D_214)))), inference(splitRight, [status(thm)], [c_652])).
% 3.85/1.68  tff(c_1019, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1016, c_618])).
% 3.85/1.68  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.85/1.68  
% 3.85/1.68  Inference rules
% 3.85/1.68  ----------------------
% 3.85/1.68  #Ref     : 0
% 3.85/1.68  #Sup     : 188
% 3.85/1.68  #Fact    : 0
% 3.85/1.68  #Define  : 0
% 3.85/1.68  #Split   : 27
% 3.85/1.68  #Chain   : 0
% 3.85/1.68  #Close   : 0
% 3.85/1.68  
% 3.85/1.68  Ordering : KBO
% 3.85/1.68  
% 3.85/1.68  Simplification rules
% 3.85/1.68  ----------------------
% 3.85/1.68  #Subsume      : 21
% 3.85/1.68  #Demod        : 103
% 3.85/1.68  #Tautology    : 26
% 3.85/1.68  #SimpNegUnit  : 15
% 3.85/1.68  #BackRed      : 27
% 3.85/1.68  
% 3.85/1.68  #Partial instantiations: 0
% 3.85/1.68  #Strategies tried      : 1
% 3.85/1.68  
% 3.85/1.68  Timing (in seconds)
% 3.85/1.68  ----------------------
% 3.85/1.68  Preprocessing        : 0.37
% 3.85/1.68  Parsing              : 0.18
% 3.85/1.68  CNF conversion       : 0.03
% 3.85/1.68  Main loop            : 0.52
% 3.85/1.68  Inferencing          : 0.19
% 3.85/1.69  Reduction            : 0.15
% 3.85/1.69  Demodulation         : 0.10
% 3.85/1.69  BG Simplification    : 0.03
% 3.85/1.69  Subsumption          : 0.10
% 3.85/1.69  Abstraction          : 0.03
% 3.85/1.69  MUC search           : 0.00
% 3.85/1.69  Cooper               : 0.00
% 3.85/1.69  Total                : 0.93
% 3.85/1.69  Index Insertion      : 0.00
% 3.85/1.69  Index Deletion       : 0.00
% 3.85/1.69  Index Matching       : 0.00
% 3.85/1.69  BG Taut test         : 0.00
%------------------------------------------------------------------------------
