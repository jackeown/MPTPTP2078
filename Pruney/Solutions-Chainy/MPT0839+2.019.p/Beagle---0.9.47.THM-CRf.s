%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:24 EST 2020

% Result     : Theorem 4.80s
% Output     : CNFRefutation 4.80s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 262 expanded)
%              Number of leaves         :   42 ( 103 expanded)
%              Depth                    :   17
%              Number of atoms          :  171 ( 468 expanded)
%              Number of equality atoms :   34 (  99 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_subset_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_123,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ~ v1_xboole_0(B)
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
               => ~ ( k2_relset_1(B,A,C) != k1_xboole_0
                    & ! [D] :
                        ( m1_subset_1(D,B)
                       => ~ r2_hidden(D,k1_relset_1(B,A,C)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_relset_1)).

tff(f_96,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_37,axiom,(
    ? [A] : v1_xboole_0(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_xboole_0)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_43,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_45,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => v1_xboole_0(k2_zfmisc_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_zfmisc_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_88,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k1_relat_1(k7_relat_1(C,B)))
      <=> ( r2_hidden(A,B)
          & r2_hidden(A,k1_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_relat_1)).

tff(f_102,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C)))
     => ( r1_tarski(k1_relat_1(D),B)
       => m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_relset_1)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_64,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_xboole_0(k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc11_relat_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_92,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(c_50,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_3300,plain,(
    ! [A_357,B_358,C_359] :
      ( k2_relset_1(A_357,B_358,C_359) = k2_relat_1(C_359)
      | ~ m1_subset_1(C_359,k1_zfmisc_1(k2_zfmisc_1(A_357,B_358))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_3324,plain,(
    k2_relset_1('#skF_4','#skF_3','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_3300])).

tff(c_8,plain,(
    v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_66,plain,(
    ! [A_53] :
      ( k1_xboole_0 = A_53
      | ~ v1_xboole_0(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_70,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_8,c_66])).

tff(c_48,plain,(
    k2_relset_1('#skF_4','#skF_3','#skF_5') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_83,plain,(
    k2_relset_1('#skF_4','#skF_3','#skF_5') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_48])).

tff(c_3326,plain,(
    k2_relat_1('#skF_5') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3324,c_83])).

tff(c_12,plain,(
    ! [A_8] : k2_subset_1(A_8) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_14,plain,(
    ! [A_9] : m1_subset_1(k2_subset_1(A_9),k1_zfmisc_1(A_9)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_55,plain,(
    ! [A_9] : m1_subset_1(A_9,k1_zfmisc_1(A_9)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_14])).

tff(c_181,plain,(
    ! [A_70,B_71] :
      ( r1_tarski(A_70,B_71)
      | ~ m1_subset_1(A_70,k1_zfmisc_1(B_71)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_194,plain,(
    ! [A_9] : r1_tarski(A_9,A_9) ),
    inference(resolution,[status(thm)],[c_55,c_181])).

tff(c_117,plain,(
    ! [A_62,B_63] :
      ( v1_xboole_0(k2_zfmisc_1(A_62,B_63))
      | ~ v1_xboole_0(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_6,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_71,plain,(
    ! [A_5] :
      ( A_5 = '#skF_2'
      | ~ v1_xboole_0(A_5) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_6])).

tff(c_127,plain,(
    ! [A_65,B_66] :
      ( k2_zfmisc_1(A_65,B_66) = '#skF_2'
      | ~ v1_xboole_0(A_65) ) ),
    inference(resolution,[status(thm)],[c_117,c_71])).

tff(c_136,plain,(
    ! [B_66] : k2_zfmisc_1('#skF_2',B_66) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_8,c_127])).

tff(c_1547,plain,(
    ! [A_207,B_208,C_209] :
      ( k2_relset_1(A_207,B_208,C_209) = k2_relat_1(C_209)
      | ~ m1_subset_1(C_209,k1_zfmisc_1(k2_zfmisc_1(A_207,B_208))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_1571,plain,(
    k2_relset_1('#skF_4','#skF_3','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_1547])).

tff(c_1573,plain,(
    k2_relat_1('#skF_5') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1571,c_83])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_253,plain,(
    ! [C_79,A_80,B_81] :
      ( v1_relat_1(C_79)
      | ~ m1_subset_1(C_79,k1_zfmisc_1(k2_zfmisc_1(A_80,B_81))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_275,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_253])).

tff(c_1365,plain,(
    ! [C_190,A_191,B_192] :
      ( v4_relat_1(C_190,A_191)
      | ~ m1_subset_1(C_190,k1_zfmisc_1(k2_zfmisc_1(A_191,B_192))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_1389,plain,(
    v4_relat_1('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_1365])).

tff(c_26,plain,(
    ! [B_19,A_18] :
      ( k7_relat_1(B_19,A_18) = B_19
      | ~ v4_relat_1(B_19,A_18)
      | ~ v1_relat_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_1393,plain,
    ( k7_relat_1('#skF_5','#skF_4') = '#skF_5'
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_1389,c_26])).

tff(c_1396,plain,(
    k7_relat_1('#skF_5','#skF_4') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_275,c_1393])).

tff(c_1424,plain,(
    ! [A_195,B_196,C_197] :
      ( r2_hidden(A_195,B_196)
      | ~ r2_hidden(A_195,k1_relat_1(k7_relat_1(C_197,B_196)))
      | ~ v1_relat_1(C_197) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_1430,plain,(
    ! [A_195] :
      ( r2_hidden(A_195,'#skF_4')
      | ~ r2_hidden(A_195,k1_relat_1('#skF_5'))
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1396,c_1424])).

tff(c_1473,plain,(
    ! [A_201] :
      ( r2_hidden(A_201,'#skF_4')
      | ~ r2_hidden(A_201,k1_relat_1('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_275,c_1430])).

tff(c_1478,plain,
    ( r2_hidden('#skF_1'(k1_relat_1('#skF_5')),'#skF_4')
    | v1_xboole_0(k1_relat_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_4,c_1473])).

tff(c_1479,plain,(
    v1_xboole_0(k1_relat_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_1478])).

tff(c_1490,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_1479,c_71])).

tff(c_1877,plain,(
    ! [D_232,B_233,C_234,A_235] :
      ( m1_subset_1(D_232,k1_zfmisc_1(k2_zfmisc_1(B_233,C_234)))
      | ~ r1_tarski(k1_relat_1(D_232),B_233)
      | ~ m1_subset_1(D_232,k1_zfmisc_1(k2_zfmisc_1(A_235,C_234))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_1891,plain,(
    ! [B_233] :
      ( m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(B_233,'#skF_3')))
      | ~ r1_tarski(k1_relat_1('#skF_5'),B_233) ) ),
    inference(resolution,[status(thm)],[c_50,c_1877])).

tff(c_1922,plain,(
    ! [B_237] :
      ( m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(B_237,'#skF_3')))
      | ~ r1_tarski('#skF_2',B_237) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1490,c_1891])).

tff(c_1956,plain,
    ( m1_subset_1('#skF_5',k1_zfmisc_1('#skF_2'))
    | ~ r1_tarski('#skF_2','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_136,c_1922])).

tff(c_1970,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_194,c_1956])).

tff(c_22,plain,(
    ! [C_16,B_15,A_14] :
      ( ~ v1_xboole_0(C_16)
      | ~ m1_subset_1(B_15,k1_zfmisc_1(C_16))
      | ~ r2_hidden(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_1993,plain,(
    ! [A_14] :
      ( ~ v1_xboole_0('#skF_2')
      | ~ r2_hidden(A_14,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_1970,c_22])).

tff(c_2016,plain,(
    ! [A_238] : ~ r2_hidden(A_238,'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_1993])).

tff(c_2021,plain,(
    v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_4,c_2016])).

tff(c_84,plain,(
    ! [A_57] :
      ( v1_xboole_0(k2_relat_1(A_57))
      | ~ v1_xboole_0(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_88,plain,(
    ! [A_57] :
      ( k2_relat_1(A_57) = '#skF_2'
      | ~ v1_xboole_0(A_57) ) ),
    inference(resolution,[status(thm)],[c_84,c_71])).

tff(c_2045,plain,(
    k2_relat_1('#skF_5') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_2021,c_88])).

tff(c_2053,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1573,c_2045])).

tff(c_2054,plain,(
    r2_hidden('#skF_1'(k1_relat_1('#skF_5')),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_1478])).

tff(c_16,plain,(
    ! [A_10,B_11] :
      ( m1_subset_1(A_10,B_11)
      | ~ r2_hidden(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_2065,plain,(
    m1_subset_1('#skF_1'(k1_relat_1('#skF_5')),'#skF_4') ),
    inference(resolution,[status(thm)],[c_2054,c_16])).

tff(c_2130,plain,(
    ! [A_245,B_246,C_247] :
      ( k1_relset_1(A_245,B_246,C_247) = k1_relat_1(C_247)
      | ~ m1_subset_1(C_247,k1_zfmisc_1(k2_zfmisc_1(A_245,B_246))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_2154,plain,(
    k1_relset_1('#skF_4','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_2130])).

tff(c_137,plain,(
    ! [D_67] :
      ( ~ r2_hidden(D_67,k1_relset_1('#skF_4','#skF_3','#skF_5'))
      | ~ m1_subset_1(D_67,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_142,plain,
    ( ~ m1_subset_1('#skF_1'(k1_relset_1('#skF_4','#skF_3','#skF_5')),'#skF_4')
    | v1_xboole_0(k1_relset_1('#skF_4','#skF_3','#skF_5')) ),
    inference(resolution,[status(thm)],[c_4,c_137])).

tff(c_341,plain,(
    ~ m1_subset_1('#skF_1'(k1_relset_1('#skF_4','#skF_3','#skF_5')),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_142])).

tff(c_2156,plain,(
    ~ m1_subset_1('#skF_1'(k1_relat_1('#skF_5')),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2154,c_341])).

tff(c_2160,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2065,c_2156])).

tff(c_2161,plain,(
    v1_xboole_0(k1_relset_1('#skF_4','#skF_3','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_142])).

tff(c_2173,plain,(
    k1_relset_1('#skF_4','#skF_3','#skF_5') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_2161,c_71])).

tff(c_3087,plain,(
    ! [A_337,B_338,C_339] :
      ( k1_relset_1(A_337,B_338,C_339) = k1_relat_1(C_339)
      | ~ m1_subset_1(C_339,k1_zfmisc_1(k2_zfmisc_1(A_337,B_338))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_3104,plain,(
    k1_relset_1('#skF_4','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_3087])).

tff(c_3112,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2173,c_3104])).

tff(c_3518,plain,(
    ! [D_371,B_372,C_373,A_374] :
      ( m1_subset_1(D_371,k1_zfmisc_1(k2_zfmisc_1(B_372,C_373)))
      | ~ r1_tarski(k1_relat_1(D_371),B_372)
      | ~ m1_subset_1(D_371,k1_zfmisc_1(k2_zfmisc_1(A_374,C_373))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_3532,plain,(
    ! [B_372] :
      ( m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(B_372,'#skF_3')))
      | ~ r1_tarski(k1_relat_1('#skF_5'),B_372) ) ),
    inference(resolution,[status(thm)],[c_50,c_3518])).

tff(c_3588,plain,(
    ! [B_378] :
      ( m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(B_378,'#skF_3')))
      | ~ r1_tarski('#skF_2',B_378) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3112,c_3532])).

tff(c_3622,plain,
    ( m1_subset_1('#skF_5',k1_zfmisc_1('#skF_2'))
    | ~ r1_tarski('#skF_2','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_136,c_3588])).

tff(c_3636,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_194,c_3622])).

tff(c_18,plain,(
    ! [A_12,B_13] :
      ( r1_tarski(A_12,B_13)
      | ~ m1_subset_1(A_12,k1_zfmisc_1(B_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_3657,plain,(
    r1_tarski('#skF_5','#skF_2') ),
    inference(resolution,[status(thm)],[c_3636,c_18])).

tff(c_20,plain,(
    ! [A_12,B_13] :
      ( m1_subset_1(A_12,k1_zfmisc_1(B_13))
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_2208,plain,(
    ! [C_252,B_253,A_254] :
      ( ~ v1_xboole_0(C_252)
      | ~ m1_subset_1(B_253,k1_zfmisc_1(C_252))
      | ~ r2_hidden(A_254,B_253) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_2973,plain,(
    ! [B_322,A_323,A_324] :
      ( ~ v1_xboole_0(B_322)
      | ~ r2_hidden(A_323,A_324)
      | ~ r1_tarski(A_324,B_322) ) ),
    inference(resolution,[status(thm)],[c_20,c_2208])).

tff(c_2976,plain,(
    ! [B_322,A_1] :
      ( ~ v1_xboole_0(B_322)
      | ~ r1_tarski(A_1,B_322)
      | v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_4,c_2973])).

tff(c_3673,plain,
    ( ~ v1_xboole_0('#skF_2')
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_3657,c_2976])).

tff(c_3679,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_3673])).

tff(c_3686,plain,(
    k2_relat_1('#skF_5') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_3679,c_88])).

tff(c_3694,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3326,c_3686])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n022.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:33:55 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.80/1.91  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.80/1.92  
% 4.80/1.92  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.80/1.92  %$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_subset_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4
% 4.80/1.92  
% 4.80/1.92  %Foreground sorts:
% 4.80/1.92  
% 4.80/1.92  
% 4.80/1.92  %Background operators:
% 4.80/1.92  
% 4.80/1.92  
% 4.80/1.92  %Foreground operators:
% 4.80/1.92  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.80/1.92  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.80/1.92  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.80/1.92  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 4.80/1.92  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.80/1.92  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.80/1.92  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.80/1.92  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.80/1.92  tff('#skF_5', type, '#skF_5': $i).
% 4.80/1.92  tff('#skF_2', type, '#skF_2': $i).
% 4.80/1.92  tff('#skF_3', type, '#skF_3': $i).
% 4.80/1.92  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.80/1.92  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.80/1.92  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.80/1.92  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.80/1.92  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.80/1.92  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.80/1.92  tff('#skF_4', type, '#skF_4': $i).
% 4.80/1.92  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.80/1.92  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.80/1.92  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 4.80/1.92  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.80/1.92  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.80/1.92  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.80/1.92  
% 4.80/1.94  tff(f_123, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => ~(~(k2_relset_1(B, A, C) = k1_xboole_0) & (![D]: (m1_subset_1(D, B) => ~r2_hidden(D, k1_relset_1(B, A, C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_relset_1)).
% 4.80/1.94  tff(f_96, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 4.80/1.94  tff(f_37, axiom, (?[A]: v1_xboole_0(A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc1_xboole_0)).
% 4.80/1.94  tff(f_35, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 4.80/1.94  tff(f_43, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 4.80/1.94  tff(f_45, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 4.80/1.94  tff(f_53, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 4.80/1.94  tff(f_41, axiom, (![A, B]: (v1_xboole_0(A) => v1_xboole_0(k2_zfmisc_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_zfmisc_1)).
% 4.80/1.94  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 4.80/1.94  tff(f_82, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.80/1.94  tff(f_88, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.80/1.94  tff(f_70, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 4.80/1.94  tff(f_78, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k1_relat_1(k7_relat_1(C, B))) <=> (r2_hidden(A, B) & r2_hidden(A, k1_relat_1(C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_relat_1)).
% 4.80/1.94  tff(f_102, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C))) => (r1_tarski(k1_relat_1(D), B) => m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_relset_1)).
% 4.80/1.94  tff(f_60, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 4.80/1.94  tff(f_64, axiom, (![A]: (v1_xboole_0(A) => v1_xboole_0(k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc11_relat_1)).
% 4.80/1.94  tff(f_49, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 4.80/1.94  tff(f_92, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.80/1.94  tff(c_50, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_123])).
% 4.80/1.94  tff(c_3300, plain, (![A_357, B_358, C_359]: (k2_relset_1(A_357, B_358, C_359)=k2_relat_1(C_359) | ~m1_subset_1(C_359, k1_zfmisc_1(k2_zfmisc_1(A_357, B_358))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.80/1.94  tff(c_3324, plain, (k2_relset_1('#skF_4', '#skF_3', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_50, c_3300])).
% 4.80/1.94  tff(c_8, plain, (v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.80/1.94  tff(c_66, plain, (![A_53]: (k1_xboole_0=A_53 | ~v1_xboole_0(A_53))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.80/1.94  tff(c_70, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_8, c_66])).
% 4.80/1.94  tff(c_48, plain, (k2_relset_1('#skF_4', '#skF_3', '#skF_5')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_123])).
% 4.80/1.94  tff(c_83, plain, (k2_relset_1('#skF_4', '#skF_3', '#skF_5')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_48])).
% 4.80/1.94  tff(c_3326, plain, (k2_relat_1('#skF_5')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_3324, c_83])).
% 4.80/1.94  tff(c_12, plain, (![A_8]: (k2_subset_1(A_8)=A_8)), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.80/1.94  tff(c_14, plain, (![A_9]: (m1_subset_1(k2_subset_1(A_9), k1_zfmisc_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.80/1.94  tff(c_55, plain, (![A_9]: (m1_subset_1(A_9, k1_zfmisc_1(A_9)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_14])).
% 4.80/1.94  tff(c_181, plain, (![A_70, B_71]: (r1_tarski(A_70, B_71) | ~m1_subset_1(A_70, k1_zfmisc_1(B_71)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.80/1.94  tff(c_194, plain, (![A_9]: (r1_tarski(A_9, A_9))), inference(resolution, [status(thm)], [c_55, c_181])).
% 4.80/1.94  tff(c_117, plain, (![A_62, B_63]: (v1_xboole_0(k2_zfmisc_1(A_62, B_63)) | ~v1_xboole_0(A_62))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.80/1.94  tff(c_6, plain, (![A_5]: (k1_xboole_0=A_5 | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.80/1.94  tff(c_71, plain, (![A_5]: (A_5='#skF_2' | ~v1_xboole_0(A_5))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_6])).
% 4.80/1.94  tff(c_127, plain, (![A_65, B_66]: (k2_zfmisc_1(A_65, B_66)='#skF_2' | ~v1_xboole_0(A_65))), inference(resolution, [status(thm)], [c_117, c_71])).
% 4.80/1.94  tff(c_136, plain, (![B_66]: (k2_zfmisc_1('#skF_2', B_66)='#skF_2')), inference(resolution, [status(thm)], [c_8, c_127])).
% 4.80/1.94  tff(c_1547, plain, (![A_207, B_208, C_209]: (k2_relset_1(A_207, B_208, C_209)=k2_relat_1(C_209) | ~m1_subset_1(C_209, k1_zfmisc_1(k2_zfmisc_1(A_207, B_208))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.80/1.94  tff(c_1571, plain, (k2_relset_1('#skF_4', '#skF_3', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_50, c_1547])).
% 4.80/1.94  tff(c_1573, plain, (k2_relat_1('#skF_5')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1571, c_83])).
% 4.80/1.94  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.80/1.94  tff(c_253, plain, (![C_79, A_80, B_81]: (v1_relat_1(C_79) | ~m1_subset_1(C_79, k1_zfmisc_1(k2_zfmisc_1(A_80, B_81))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.80/1.94  tff(c_275, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_50, c_253])).
% 4.80/1.94  tff(c_1365, plain, (![C_190, A_191, B_192]: (v4_relat_1(C_190, A_191) | ~m1_subset_1(C_190, k1_zfmisc_1(k2_zfmisc_1(A_191, B_192))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.80/1.94  tff(c_1389, plain, (v4_relat_1('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_50, c_1365])).
% 4.80/1.94  tff(c_26, plain, (![B_19, A_18]: (k7_relat_1(B_19, A_18)=B_19 | ~v4_relat_1(B_19, A_18) | ~v1_relat_1(B_19))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.80/1.94  tff(c_1393, plain, (k7_relat_1('#skF_5', '#skF_4')='#skF_5' | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_1389, c_26])).
% 4.80/1.94  tff(c_1396, plain, (k7_relat_1('#skF_5', '#skF_4')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_275, c_1393])).
% 4.80/1.94  tff(c_1424, plain, (![A_195, B_196, C_197]: (r2_hidden(A_195, B_196) | ~r2_hidden(A_195, k1_relat_1(k7_relat_1(C_197, B_196))) | ~v1_relat_1(C_197))), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.80/1.94  tff(c_1430, plain, (![A_195]: (r2_hidden(A_195, '#skF_4') | ~r2_hidden(A_195, k1_relat_1('#skF_5')) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_1396, c_1424])).
% 4.80/1.94  tff(c_1473, plain, (![A_201]: (r2_hidden(A_201, '#skF_4') | ~r2_hidden(A_201, k1_relat_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_275, c_1430])).
% 4.80/1.94  tff(c_1478, plain, (r2_hidden('#skF_1'(k1_relat_1('#skF_5')), '#skF_4') | v1_xboole_0(k1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_4, c_1473])).
% 4.80/1.94  tff(c_1479, plain, (v1_xboole_0(k1_relat_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_1478])).
% 4.80/1.94  tff(c_1490, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(resolution, [status(thm)], [c_1479, c_71])).
% 4.80/1.94  tff(c_1877, plain, (![D_232, B_233, C_234, A_235]: (m1_subset_1(D_232, k1_zfmisc_1(k2_zfmisc_1(B_233, C_234))) | ~r1_tarski(k1_relat_1(D_232), B_233) | ~m1_subset_1(D_232, k1_zfmisc_1(k2_zfmisc_1(A_235, C_234))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 4.80/1.94  tff(c_1891, plain, (![B_233]: (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(B_233, '#skF_3'))) | ~r1_tarski(k1_relat_1('#skF_5'), B_233))), inference(resolution, [status(thm)], [c_50, c_1877])).
% 4.80/1.94  tff(c_1922, plain, (![B_237]: (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(B_237, '#skF_3'))) | ~r1_tarski('#skF_2', B_237))), inference(demodulation, [status(thm), theory('equality')], [c_1490, c_1891])).
% 4.80/1.94  tff(c_1956, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_2')) | ~r1_tarski('#skF_2', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_136, c_1922])).
% 4.80/1.94  tff(c_1970, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_194, c_1956])).
% 4.80/1.94  tff(c_22, plain, (![C_16, B_15, A_14]: (~v1_xboole_0(C_16) | ~m1_subset_1(B_15, k1_zfmisc_1(C_16)) | ~r2_hidden(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.80/1.94  tff(c_1993, plain, (![A_14]: (~v1_xboole_0('#skF_2') | ~r2_hidden(A_14, '#skF_5'))), inference(resolution, [status(thm)], [c_1970, c_22])).
% 4.80/1.94  tff(c_2016, plain, (![A_238]: (~r2_hidden(A_238, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_1993])).
% 4.80/1.94  tff(c_2021, plain, (v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_4, c_2016])).
% 4.80/1.94  tff(c_84, plain, (![A_57]: (v1_xboole_0(k2_relat_1(A_57)) | ~v1_xboole_0(A_57))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.80/1.94  tff(c_88, plain, (![A_57]: (k2_relat_1(A_57)='#skF_2' | ~v1_xboole_0(A_57))), inference(resolution, [status(thm)], [c_84, c_71])).
% 4.80/1.94  tff(c_2045, plain, (k2_relat_1('#skF_5')='#skF_2'), inference(resolution, [status(thm)], [c_2021, c_88])).
% 4.80/1.94  tff(c_2053, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1573, c_2045])).
% 4.80/1.94  tff(c_2054, plain, (r2_hidden('#skF_1'(k1_relat_1('#skF_5')), '#skF_4')), inference(splitRight, [status(thm)], [c_1478])).
% 4.80/1.94  tff(c_16, plain, (![A_10, B_11]: (m1_subset_1(A_10, B_11) | ~r2_hidden(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.80/1.94  tff(c_2065, plain, (m1_subset_1('#skF_1'(k1_relat_1('#skF_5')), '#skF_4')), inference(resolution, [status(thm)], [c_2054, c_16])).
% 4.80/1.94  tff(c_2130, plain, (![A_245, B_246, C_247]: (k1_relset_1(A_245, B_246, C_247)=k1_relat_1(C_247) | ~m1_subset_1(C_247, k1_zfmisc_1(k2_zfmisc_1(A_245, B_246))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.80/1.94  tff(c_2154, plain, (k1_relset_1('#skF_4', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_50, c_2130])).
% 4.80/1.94  tff(c_137, plain, (![D_67]: (~r2_hidden(D_67, k1_relset_1('#skF_4', '#skF_3', '#skF_5')) | ~m1_subset_1(D_67, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_123])).
% 4.80/1.94  tff(c_142, plain, (~m1_subset_1('#skF_1'(k1_relset_1('#skF_4', '#skF_3', '#skF_5')), '#skF_4') | v1_xboole_0(k1_relset_1('#skF_4', '#skF_3', '#skF_5'))), inference(resolution, [status(thm)], [c_4, c_137])).
% 4.80/1.94  tff(c_341, plain, (~m1_subset_1('#skF_1'(k1_relset_1('#skF_4', '#skF_3', '#skF_5')), '#skF_4')), inference(splitLeft, [status(thm)], [c_142])).
% 4.80/1.94  tff(c_2156, plain, (~m1_subset_1('#skF_1'(k1_relat_1('#skF_5')), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2154, c_341])).
% 4.80/1.94  tff(c_2160, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2065, c_2156])).
% 4.80/1.94  tff(c_2161, plain, (v1_xboole_0(k1_relset_1('#skF_4', '#skF_3', '#skF_5'))), inference(splitRight, [status(thm)], [c_142])).
% 4.80/1.94  tff(c_2173, plain, (k1_relset_1('#skF_4', '#skF_3', '#skF_5')='#skF_2'), inference(resolution, [status(thm)], [c_2161, c_71])).
% 4.80/1.94  tff(c_3087, plain, (![A_337, B_338, C_339]: (k1_relset_1(A_337, B_338, C_339)=k1_relat_1(C_339) | ~m1_subset_1(C_339, k1_zfmisc_1(k2_zfmisc_1(A_337, B_338))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.80/1.94  tff(c_3104, plain, (k1_relset_1('#skF_4', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_50, c_3087])).
% 4.80/1.94  tff(c_3112, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2173, c_3104])).
% 4.80/1.94  tff(c_3518, plain, (![D_371, B_372, C_373, A_374]: (m1_subset_1(D_371, k1_zfmisc_1(k2_zfmisc_1(B_372, C_373))) | ~r1_tarski(k1_relat_1(D_371), B_372) | ~m1_subset_1(D_371, k1_zfmisc_1(k2_zfmisc_1(A_374, C_373))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 4.80/1.94  tff(c_3532, plain, (![B_372]: (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(B_372, '#skF_3'))) | ~r1_tarski(k1_relat_1('#skF_5'), B_372))), inference(resolution, [status(thm)], [c_50, c_3518])).
% 4.80/1.94  tff(c_3588, plain, (![B_378]: (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(B_378, '#skF_3'))) | ~r1_tarski('#skF_2', B_378))), inference(demodulation, [status(thm), theory('equality')], [c_3112, c_3532])).
% 4.80/1.94  tff(c_3622, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_2')) | ~r1_tarski('#skF_2', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_136, c_3588])).
% 4.80/1.94  tff(c_3636, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_194, c_3622])).
% 4.80/1.94  tff(c_18, plain, (![A_12, B_13]: (r1_tarski(A_12, B_13) | ~m1_subset_1(A_12, k1_zfmisc_1(B_13)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.80/1.94  tff(c_3657, plain, (r1_tarski('#skF_5', '#skF_2')), inference(resolution, [status(thm)], [c_3636, c_18])).
% 4.80/1.94  tff(c_20, plain, (![A_12, B_13]: (m1_subset_1(A_12, k1_zfmisc_1(B_13)) | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.80/1.94  tff(c_2208, plain, (![C_252, B_253, A_254]: (~v1_xboole_0(C_252) | ~m1_subset_1(B_253, k1_zfmisc_1(C_252)) | ~r2_hidden(A_254, B_253))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.80/1.94  tff(c_2973, plain, (![B_322, A_323, A_324]: (~v1_xboole_0(B_322) | ~r2_hidden(A_323, A_324) | ~r1_tarski(A_324, B_322))), inference(resolution, [status(thm)], [c_20, c_2208])).
% 4.80/1.94  tff(c_2976, plain, (![B_322, A_1]: (~v1_xboole_0(B_322) | ~r1_tarski(A_1, B_322) | v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_4, c_2973])).
% 4.80/1.94  tff(c_3673, plain, (~v1_xboole_0('#skF_2') | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_3657, c_2976])).
% 4.80/1.94  tff(c_3679, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_3673])).
% 4.80/1.94  tff(c_3686, plain, (k2_relat_1('#skF_5')='#skF_2'), inference(resolution, [status(thm)], [c_3679, c_88])).
% 4.80/1.94  tff(c_3694, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3326, c_3686])).
% 4.80/1.94  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.80/1.94  
% 4.80/1.94  Inference rules
% 4.80/1.94  ----------------------
% 4.80/1.94  #Ref     : 0
% 4.80/1.94  #Sup     : 820
% 4.80/1.94  #Fact    : 0
% 4.80/1.94  #Define  : 0
% 4.80/1.94  #Split   : 12
% 4.80/1.94  #Chain   : 0
% 4.80/1.94  #Close   : 0
% 4.80/1.94  
% 4.80/1.94  Ordering : KBO
% 4.80/1.94  
% 4.80/1.94  Simplification rules
% 4.80/1.94  ----------------------
% 4.80/1.94  #Subsume      : 59
% 4.80/1.94  #Demod        : 484
% 4.80/1.94  #Tautology    : 373
% 4.80/1.94  #SimpNegUnit  : 11
% 4.80/1.94  #BackRed      : 30
% 4.80/1.94  
% 4.80/1.94  #Partial instantiations: 0
% 4.80/1.94  #Strategies tried      : 1
% 4.80/1.94  
% 4.80/1.94  Timing (in seconds)
% 4.80/1.94  ----------------------
% 4.80/1.95  Preprocessing        : 0.36
% 4.80/1.95  Parsing              : 0.19
% 4.80/1.95  CNF conversion       : 0.03
% 4.80/1.95  Main loop            : 0.76
% 4.80/1.95  Inferencing          : 0.27
% 4.80/1.95  Reduction            : 0.25
% 4.80/1.95  Demodulation         : 0.17
% 4.80/1.95  BG Simplification    : 0.03
% 4.80/1.95  Subsumption          : 0.14
% 4.80/1.95  Abstraction          : 0.04
% 4.80/1.95  MUC search           : 0.00
% 4.80/1.95  Cooper               : 0.00
% 4.80/1.95  Total                : 1.16
% 4.80/1.95  Index Insertion      : 0.00
% 4.80/1.95  Index Deletion       : 0.00
% 4.80/1.95  Index Matching       : 0.00
% 4.80/1.95  BG Taut test         : 0.00
%------------------------------------------------------------------------------
