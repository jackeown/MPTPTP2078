%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:46 EST 2020

% Result     : Theorem 3.67s
% Output     : CNFRefutation 3.67s
% Verified   : 
% Statistics : Number of formulae       :  127 ( 826 expanded)
%              Number of leaves         :   29 ( 283 expanded)
%              Depth                    :   15
%              Number of atoms          :  258 (2355 expanded)
%              Number of equality atoms :   67 ( 706 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k4_mcart_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k4_mcart_1,type,(
    k4_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_106,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ( v1_funct_1(A)
          & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
          & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_32,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_95,axiom,(
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

tff(f_77,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D,E,F] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k4_mcart_1(C,D,E,F) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_mcart_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_38,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k1_relset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_relset_1)).

tff(c_46,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_8,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1561,plain,(
    ! [C_352,A_353,B_354] :
      ( m1_subset_1(C_352,k1_zfmisc_1(k2_zfmisc_1(A_353,B_354)))
      | ~ r1_tarski(k2_relat_1(C_352),B_354)
      | ~ r1_tarski(k1_relat_1(C_352),A_353)
      | ~ v1_relat_1(C_352) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_771,plain,(
    ! [C_221,A_222,B_223] :
      ( m1_subset_1(C_221,k1_zfmisc_1(k2_zfmisc_1(A_222,B_223)))
      | ~ r1_tarski(k2_relat_1(C_221),B_223)
      | ~ r1_tarski(k1_relat_1(C_221),A_222)
      | ~ v1_relat_1(C_221) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_20,plain,(
    ! [A_11,B_12,C_13] :
      ( k1_relset_1(A_11,B_12,C_13) = k1_relat_1(C_13)
      | ~ m1_subset_1(C_13,k1_zfmisc_1(k2_zfmisc_1(A_11,B_12))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1076,plain,(
    ! [A_265,B_266,C_267] :
      ( k1_relset_1(A_265,B_266,C_267) = k1_relat_1(C_267)
      | ~ r1_tarski(k2_relat_1(C_267),B_266)
      | ~ r1_tarski(k1_relat_1(C_267),A_265)
      | ~ v1_relat_1(C_267) ) ),
    inference(resolution,[status(thm)],[c_771,c_20])).

tff(c_1081,plain,(
    ! [A_268,C_269] :
      ( k1_relset_1(A_268,k2_relat_1(C_269),C_269) = k1_relat_1(C_269)
      | ~ r1_tarski(k1_relat_1(C_269),A_268)
      | ~ v1_relat_1(C_269) ) ),
    inference(resolution,[status(thm)],[c_8,c_1076])).

tff(c_1088,plain,(
    ! [C_269] :
      ( k1_relset_1(k1_relat_1(C_269),k2_relat_1(C_269),C_269) = k1_relat_1(C_269)
      | ~ v1_relat_1(C_269) ) ),
    inference(resolution,[status(thm)],[c_8,c_1081])).

tff(c_22,plain,(
    ! [C_16,A_14,B_15] :
      ( m1_subset_1(C_16,k1_zfmisc_1(k2_zfmisc_1(A_14,B_15)))
      | ~ r1_tarski(k2_relat_1(C_16),B_15)
      | ~ r1_tarski(k1_relat_1(C_16),A_14)
      | ~ v1_relat_1(C_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_929,plain,(
    ! [B_239,C_240,A_241] :
      ( k1_xboole_0 = B_239
      | v1_funct_2(C_240,A_241,B_239)
      | k1_relset_1(A_241,B_239,C_240) != A_241
      | ~ m1_subset_1(C_240,k1_zfmisc_1(k2_zfmisc_1(A_241,B_239))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_1285,plain,(
    ! [B_306,C_307,A_308] :
      ( k1_xboole_0 = B_306
      | v1_funct_2(C_307,A_308,B_306)
      | k1_relset_1(A_308,B_306,C_307) != A_308
      | ~ r1_tarski(k2_relat_1(C_307),B_306)
      | ~ r1_tarski(k1_relat_1(C_307),A_308)
      | ~ v1_relat_1(C_307) ) ),
    inference(resolution,[status(thm)],[c_22,c_929])).

tff(c_1290,plain,(
    ! [C_309,A_310] :
      ( k2_relat_1(C_309) = k1_xboole_0
      | v1_funct_2(C_309,A_310,k2_relat_1(C_309))
      | k1_relset_1(A_310,k2_relat_1(C_309),C_309) != A_310
      | ~ r1_tarski(k1_relat_1(C_309),A_310)
      | ~ v1_relat_1(C_309) ) ),
    inference(resolution,[status(thm)],[c_8,c_1285])).

tff(c_44,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_42,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'),k2_relat_1('#skF_2'))))
    | ~ v1_funct_2('#skF_2',k1_relat_1('#skF_2'),k2_relat_1('#skF_2'))
    | ~ v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_48,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'),k2_relat_1('#skF_2'))))
    | ~ v1_funct_2('#skF_2',k1_relat_1('#skF_2'),k2_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42])).

tff(c_96,plain,(
    ~ v1_funct_2('#skF_2',k1_relat_1('#skF_2'),k2_relat_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_1297,plain,
    ( k2_relat_1('#skF_2') = k1_xboole_0
    | k1_relset_1(k1_relat_1('#skF_2'),k2_relat_1('#skF_2'),'#skF_2') != k1_relat_1('#skF_2')
    | ~ r1_tarski(k1_relat_1('#skF_2'),k1_relat_1('#skF_2'))
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_1290,c_96])).

tff(c_1302,plain,
    ( k2_relat_1('#skF_2') = k1_xboole_0
    | k1_relset_1(k1_relat_1('#skF_2'),k2_relat_1('#skF_2'),'#skF_2') != k1_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_8,c_1297])).

tff(c_1303,plain,(
    k1_relset_1(k1_relat_1('#skF_2'),k2_relat_1('#skF_2'),'#skF_2') != k1_relat_1('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_1302])).

tff(c_1309,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1088,c_1303])).

tff(c_1315,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_1309])).

tff(c_1316,plain,(
    k2_relat_1('#skF_2') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_1302])).

tff(c_24,plain,(
    ! [A_17] :
      ( r2_hidden('#skF_1'(A_17),A_17)
      | k1_xboole_0 = A_17 ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_12,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_16,plain,(
    ! [C_7,B_6,A_5] :
      ( ~ v1_xboole_0(C_7)
      | ~ m1_subset_1(B_6,k1_zfmisc_1(C_7))
      | ~ r2_hidden(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1187,plain,(
    ! [A_282,B_283,A_284,C_285] :
      ( ~ v1_xboole_0(k2_zfmisc_1(A_282,B_283))
      | ~ r2_hidden(A_284,C_285)
      | ~ r1_tarski(k2_relat_1(C_285),B_283)
      | ~ r1_tarski(k1_relat_1(C_285),A_282)
      | ~ v1_relat_1(C_285) ) ),
    inference(resolution,[status(thm)],[c_771,c_16])).

tff(c_1191,plain,(
    ! [A_284,C_285,A_3] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(A_284,C_285)
      | ~ r1_tarski(k2_relat_1(C_285),k1_xboole_0)
      | ~ r1_tarski(k1_relat_1(C_285),A_3)
      | ~ v1_relat_1(C_285) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_1187])).

tff(c_1232,plain,(
    ! [A_298,C_299,A_300] :
      ( ~ r2_hidden(A_298,C_299)
      | ~ r1_tarski(k2_relat_1(C_299),k1_xboole_0)
      | ~ r1_tarski(k1_relat_1(C_299),A_300)
      | ~ v1_relat_1(C_299) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_1191])).

tff(c_1235,plain,(
    ! [A_17,A_300] :
      ( ~ r1_tarski(k2_relat_1(A_17),k1_xboole_0)
      | ~ r1_tarski(k1_relat_1(A_17),A_300)
      | ~ v1_relat_1(A_17)
      | k1_xboole_0 = A_17 ) ),
    inference(resolution,[status(thm)],[c_24,c_1232])).

tff(c_1329,plain,(
    ! [A_300] :
      ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
      | ~ r1_tarski(k1_relat_1('#skF_2'),A_300)
      | ~ v1_relat_1('#skF_2')
      | k1_xboole_0 = '#skF_2' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1316,c_1235])).

tff(c_1348,plain,(
    ! [A_300] :
      ( ~ r1_tarski(k1_relat_1('#skF_2'),A_300)
      | k1_xboole_0 = '#skF_2' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_8,c_1329])).

tff(c_1359,plain,(
    ! [A_311] : ~ r1_tarski(k1_relat_1('#skF_2'),A_311) ),
    inference(splitLeft,[status(thm)],[c_1348])).

tff(c_1364,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_8,c_1359])).

tff(c_1365,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_1348])).

tff(c_145,plain,(
    ! [C_83,A_84,B_85] :
      ( m1_subset_1(C_83,k1_zfmisc_1(k2_zfmisc_1(A_84,B_85)))
      | ~ r1_tarski(k2_relat_1(C_83),B_85)
      | ~ r1_tarski(k1_relat_1(C_83),A_84)
      | ~ v1_relat_1(C_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_292,plain,(
    ! [A_120,B_121,C_122] :
      ( k1_relset_1(A_120,B_121,C_122) = k1_relat_1(C_122)
      | ~ r1_tarski(k2_relat_1(C_122),B_121)
      | ~ r1_tarski(k1_relat_1(C_122),A_120)
      | ~ v1_relat_1(C_122) ) ),
    inference(resolution,[status(thm)],[c_145,c_20])).

tff(c_313,plain,(
    ! [A_126,C_127] :
      ( k1_relset_1(A_126,k2_relat_1(C_127),C_127) = k1_relat_1(C_127)
      | ~ r1_tarski(k1_relat_1(C_127),A_126)
      | ~ v1_relat_1(C_127) ) ),
    inference(resolution,[status(thm)],[c_8,c_292])).

tff(c_317,plain,(
    ! [C_127] :
      ( k1_relset_1(k1_relat_1(C_127),k2_relat_1(C_127),C_127) = k1_relat_1(C_127)
      | ~ v1_relat_1(C_127) ) ),
    inference(resolution,[status(thm)],[c_8,c_313])).

tff(c_222,plain,(
    ! [B_108,C_109,A_110] :
      ( k1_xboole_0 = B_108
      | v1_funct_2(C_109,A_110,B_108)
      | k1_relset_1(A_110,B_108,C_109) != A_110
      | ~ m1_subset_1(C_109,k1_zfmisc_1(k2_zfmisc_1(A_110,B_108))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_433,plain,(
    ! [B_165,C_166,A_167] :
      ( k1_xboole_0 = B_165
      | v1_funct_2(C_166,A_167,B_165)
      | k1_relset_1(A_167,B_165,C_166) != A_167
      | ~ r1_tarski(k2_relat_1(C_166),B_165)
      | ~ r1_tarski(k1_relat_1(C_166),A_167)
      | ~ v1_relat_1(C_166) ) ),
    inference(resolution,[status(thm)],[c_22,c_222])).

tff(c_444,plain,(
    ! [C_170,A_171] :
      ( k2_relat_1(C_170) = k1_xboole_0
      | v1_funct_2(C_170,A_171,k2_relat_1(C_170))
      | k1_relset_1(A_171,k2_relat_1(C_170),C_170) != A_171
      | ~ r1_tarski(k1_relat_1(C_170),A_171)
      | ~ v1_relat_1(C_170) ) ),
    inference(resolution,[status(thm)],[c_8,c_433])).

tff(c_447,plain,
    ( k2_relat_1('#skF_2') = k1_xboole_0
    | k1_relset_1(k1_relat_1('#skF_2'),k2_relat_1('#skF_2'),'#skF_2') != k1_relat_1('#skF_2')
    | ~ r1_tarski(k1_relat_1('#skF_2'),k1_relat_1('#skF_2'))
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_444,c_96])).

tff(c_450,plain,
    ( k2_relat_1('#skF_2') = k1_xboole_0
    | k1_relset_1(k1_relat_1('#skF_2'),k2_relat_1('#skF_2'),'#skF_2') != k1_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_8,c_447])).

tff(c_451,plain,(
    k1_relset_1(k1_relat_1('#skF_2'),k2_relat_1('#skF_2'),'#skF_2') != k1_relat_1('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_450])).

tff(c_454,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_317,c_451])).

tff(c_458,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_454])).

tff(c_459,plain,(
    k2_relat_1('#skF_2') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_450])).

tff(c_338,plain,(
    ! [A_132,B_133,A_134,C_135] :
      ( ~ v1_xboole_0(k2_zfmisc_1(A_132,B_133))
      | ~ r2_hidden(A_134,C_135)
      | ~ r1_tarski(k2_relat_1(C_135),B_133)
      | ~ r1_tarski(k1_relat_1(C_135),A_132)
      | ~ v1_relat_1(C_135) ) ),
    inference(resolution,[status(thm)],[c_145,c_16])).

tff(c_342,plain,(
    ! [A_134,C_135,A_3] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(A_134,C_135)
      | ~ r1_tarski(k2_relat_1(C_135),k1_xboole_0)
      | ~ r1_tarski(k1_relat_1(C_135),A_3)
      | ~ v1_relat_1(C_135) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_338])).

tff(c_376,plain,(
    ! [A_147,C_148,A_149] :
      ( ~ r2_hidden(A_147,C_148)
      | ~ r1_tarski(k2_relat_1(C_148),k1_xboole_0)
      | ~ r1_tarski(k1_relat_1(C_148),A_149)
      | ~ v1_relat_1(C_148) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_342])).

tff(c_379,plain,(
    ! [A_17,A_149] :
      ( ~ r1_tarski(k2_relat_1(A_17),k1_xboole_0)
      | ~ r1_tarski(k1_relat_1(A_17),A_149)
      | ~ v1_relat_1(A_17)
      | k1_xboole_0 = A_17 ) ),
    inference(resolution,[status(thm)],[c_24,c_376])).

tff(c_471,plain,(
    ! [A_149] :
      ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
      | ~ r1_tarski(k1_relat_1('#skF_2'),A_149)
      | ~ v1_relat_1('#skF_2')
      | k1_xboole_0 = '#skF_2' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_459,c_379])).

tff(c_488,plain,(
    ! [A_149] :
      ( ~ r1_tarski(k1_relat_1('#skF_2'),A_149)
      | k1_xboole_0 = '#skF_2' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_8,c_471])).

tff(c_506,plain,(
    ! [A_175] : ~ r1_tarski(k1_relat_1('#skF_2'),A_175) ),
    inference(splitLeft,[status(thm)],[c_488])).

tff(c_511,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_8,c_506])).

tff(c_512,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_488])).

tff(c_30,plain,(
    ! [A_35] :
      ( v1_funct_2(k1_xboole_0,A_35,k1_xboole_0)
      | k1_xboole_0 = A_35
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_35,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_51,plain,(
    ! [A_35] :
      ( v1_funct_2(k1_xboole_0,A_35,k1_xboole_0)
      | k1_xboole_0 = A_35
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_30])).

tff(c_98,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_51])).

tff(c_546,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_512,c_512,c_98])).

tff(c_156,plain,(
    ! [C_83,A_3] :
      ( m1_subset_1(C_83,k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski(k2_relat_1(C_83),k1_xboole_0)
      | ~ r1_tarski(k1_relat_1(C_83),A_3)
      | ~ v1_relat_1(C_83) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_145])).

tff(c_478,plain,(
    ! [A_3] :
      ( m1_subset_1('#skF_2',k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
      | ~ r1_tarski(k1_relat_1('#skF_2'),A_3)
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_459,c_156])).

tff(c_494,plain,(
    ! [A_3] :
      ( m1_subset_1('#skF_2',k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski(k1_relat_1('#skF_2'),A_3) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_8,c_478])).

tff(c_632,plain,(
    ! [A_3] :
      ( m1_subset_1('#skF_2',k1_zfmisc_1('#skF_2'))
      | ~ r1_tarski(k1_relat_1('#skF_2'),A_3) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_512,c_494])).

tff(c_634,plain,(
    ! [A_182] : ~ r1_tarski(k1_relat_1('#skF_2'),A_182) ),
    inference(negUnitSimplification,[status(thm)],[c_546,c_632])).

tff(c_639,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_8,c_634])).

tff(c_641,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_51])).

tff(c_660,plain,(
    ! [A_194,B_195,C_196] :
      ( k1_relset_1(A_194,B_195,C_196) = k1_relat_1(C_196)
      | ~ m1_subset_1(C_196,k1_zfmisc_1(k2_zfmisc_1(A_194,B_195))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_678,plain,(
    ! [A_200,C_201] :
      ( k1_relset_1(A_200,k1_xboole_0,C_201) = k1_relat_1(C_201)
      | ~ m1_subset_1(C_201,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_660])).

tff(c_681,plain,(
    ! [A_200] : k1_relset_1(A_200,k1_xboole_0,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_641,c_678])).

tff(c_709,plain,(
    ! [A_214,B_215,C_216] :
      ( m1_subset_1(k1_relset_1(A_214,B_215,C_216),k1_zfmisc_1(A_214))
      | ~ m1_subset_1(C_216,k1_zfmisc_1(k2_zfmisc_1(A_214,B_215))) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_724,plain,(
    ! [A_200] :
      ( m1_subset_1(k1_relat_1(k1_xboole_0),k1_zfmisc_1(A_200))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_200,k1_xboole_0))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_681,c_709])).

tff(c_738,plain,(
    ! [A_217] : m1_subset_1(k1_relat_1(k1_xboole_0),k1_zfmisc_1(A_217)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_641,c_12,c_724])).

tff(c_754,plain,(
    ! [A_217,A_5] :
      ( ~ v1_xboole_0(A_217)
      | ~ r2_hidden(A_5,k1_relat_1(k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_738,c_16])).

tff(c_765,plain,(
    ! [A_220] : ~ r2_hidden(A_220,k1_relat_1(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_754])).

tff(c_770,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_24,c_765])).

tff(c_735,plain,(
    ! [A_200] : m1_subset_1(k1_relat_1(k1_xboole_0),k1_zfmisc_1(A_200)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_641,c_12,c_724])).

tff(c_794,plain,(
    ! [A_224] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_224)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_770,c_735])).

tff(c_804,plain,(
    ! [A_11,B_12] : k1_relset_1(A_11,B_12,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_794,c_20])).

tff(c_812,plain,(
    ! [A_11,B_12] : k1_relset_1(A_11,B_12,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_770,c_804])).

tff(c_786,plain,(
    ! [A_200] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_200)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_770,c_735])).

tff(c_14,plain,(
    ! [B_4] : k2_zfmisc_1(k1_xboole_0,B_4) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_34,plain,(
    ! [C_37,B_36] :
      ( v1_funct_2(C_37,k1_xboole_0,B_36)
      | k1_relset_1(k1_xboole_0,B_36,C_37) != k1_xboole_0
      | ~ m1_subset_1(C_37,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_36))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_860,plain,(
    ! [C_229,B_230] :
      ( v1_funct_2(C_229,k1_xboole_0,B_230)
      | k1_relset_1(k1_xboole_0,B_230,C_229) != k1_xboole_0
      | ~ m1_subset_1(C_229,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_34])).

tff(c_863,plain,(
    ! [B_230] :
      ( v1_funct_2(k1_xboole_0,k1_xboole_0,B_230)
      | k1_relset_1(k1_xboole_0,B_230,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_786,c_860])).

tff(c_869,plain,(
    ! [B_230] : v1_funct_2(k1_xboole_0,k1_xboole_0,B_230) ),
    inference(demodulation,[status(thm),theory(equality)],[c_812,c_863])).

tff(c_1392,plain,(
    ! [B_230] : v1_funct_2('#skF_2','#skF_2',B_230) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1365,c_1365,c_869])).

tff(c_1396,plain,(
    k1_relat_1('#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1365,c_1365,c_770])).

tff(c_1318,plain,(
    ~ v1_funct_2('#skF_2',k1_relat_1('#skF_2'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1316,c_96])).

tff(c_1366,plain,(
    ~ v1_funct_2('#skF_2',k1_relat_1('#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1365,c_1318])).

tff(c_1459,plain,(
    ~ v1_funct_2('#skF_2','#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1396,c_1366])).

tff(c_1514,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1392,c_1459])).

tff(c_1515,plain,(
    ! [A_217] : ~ v1_xboole_0(A_217) ),
    inference(splitRight,[status(thm)],[c_754])).

tff(c_1517,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1515,c_2])).

tff(c_1518,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'),k2_relat_1('#skF_2')))) ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_1569,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_2'),k2_relat_1('#skF_2'))
    | ~ r1_tarski(k1_relat_1('#skF_2'),k1_relat_1('#skF_2'))
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_1561,c_1518])).

tff(c_1581,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_8,c_8,c_1569])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:01:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.67/1.57  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.67/1.58  
% 3.67/1.58  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.67/1.58  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k4_mcart_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2
% 3.67/1.58  
% 3.67/1.58  %Foreground sorts:
% 3.67/1.58  
% 3.67/1.58  
% 3.67/1.58  %Background operators:
% 3.67/1.58  
% 3.67/1.58  
% 3.67/1.58  %Foreground operators:
% 3.67/1.58  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.67/1.58  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.67/1.58  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.67/1.58  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.67/1.58  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.67/1.58  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.67/1.58  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.67/1.58  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.67/1.58  tff('#skF_2', type, '#skF_2': $i).
% 3.67/1.58  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.67/1.58  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.67/1.58  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.67/1.58  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.67/1.58  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.67/1.58  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.67/1.58  tff(k4_mcart_1, type, k4_mcart_1: ($i * $i * $i * $i) > $i).
% 3.67/1.58  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.67/1.58  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.67/1.58  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.67/1.58  
% 3.67/1.60  tff(f_106, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_funct_2)).
% 3.67/1.60  tff(f_32, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.67/1.60  tff(f_61, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_relset_1)).
% 3.67/1.60  tff(f_53, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.67/1.60  tff(f_95, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 3.67/1.60  tff(f_77, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E, F]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k4_mcart_1(C, D, E, F)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_mcart_1)).
% 3.67/1.60  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.67/1.60  tff(f_38, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 3.67/1.60  tff(f_45, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 3.67/1.60  tff(f_49, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k1_relset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_relset_1)).
% 3.67/1.60  tff(c_46, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.67/1.60  tff(c_8, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.67/1.60  tff(c_1561, plain, (![C_352, A_353, B_354]: (m1_subset_1(C_352, k1_zfmisc_1(k2_zfmisc_1(A_353, B_354))) | ~r1_tarski(k2_relat_1(C_352), B_354) | ~r1_tarski(k1_relat_1(C_352), A_353) | ~v1_relat_1(C_352))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.67/1.60  tff(c_771, plain, (![C_221, A_222, B_223]: (m1_subset_1(C_221, k1_zfmisc_1(k2_zfmisc_1(A_222, B_223))) | ~r1_tarski(k2_relat_1(C_221), B_223) | ~r1_tarski(k1_relat_1(C_221), A_222) | ~v1_relat_1(C_221))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.67/1.60  tff(c_20, plain, (![A_11, B_12, C_13]: (k1_relset_1(A_11, B_12, C_13)=k1_relat_1(C_13) | ~m1_subset_1(C_13, k1_zfmisc_1(k2_zfmisc_1(A_11, B_12))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.67/1.60  tff(c_1076, plain, (![A_265, B_266, C_267]: (k1_relset_1(A_265, B_266, C_267)=k1_relat_1(C_267) | ~r1_tarski(k2_relat_1(C_267), B_266) | ~r1_tarski(k1_relat_1(C_267), A_265) | ~v1_relat_1(C_267))), inference(resolution, [status(thm)], [c_771, c_20])).
% 3.67/1.60  tff(c_1081, plain, (![A_268, C_269]: (k1_relset_1(A_268, k2_relat_1(C_269), C_269)=k1_relat_1(C_269) | ~r1_tarski(k1_relat_1(C_269), A_268) | ~v1_relat_1(C_269))), inference(resolution, [status(thm)], [c_8, c_1076])).
% 3.67/1.60  tff(c_1088, plain, (![C_269]: (k1_relset_1(k1_relat_1(C_269), k2_relat_1(C_269), C_269)=k1_relat_1(C_269) | ~v1_relat_1(C_269))), inference(resolution, [status(thm)], [c_8, c_1081])).
% 3.67/1.60  tff(c_22, plain, (![C_16, A_14, B_15]: (m1_subset_1(C_16, k1_zfmisc_1(k2_zfmisc_1(A_14, B_15))) | ~r1_tarski(k2_relat_1(C_16), B_15) | ~r1_tarski(k1_relat_1(C_16), A_14) | ~v1_relat_1(C_16))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.67/1.60  tff(c_929, plain, (![B_239, C_240, A_241]: (k1_xboole_0=B_239 | v1_funct_2(C_240, A_241, B_239) | k1_relset_1(A_241, B_239, C_240)!=A_241 | ~m1_subset_1(C_240, k1_zfmisc_1(k2_zfmisc_1(A_241, B_239))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.67/1.60  tff(c_1285, plain, (![B_306, C_307, A_308]: (k1_xboole_0=B_306 | v1_funct_2(C_307, A_308, B_306) | k1_relset_1(A_308, B_306, C_307)!=A_308 | ~r1_tarski(k2_relat_1(C_307), B_306) | ~r1_tarski(k1_relat_1(C_307), A_308) | ~v1_relat_1(C_307))), inference(resolution, [status(thm)], [c_22, c_929])).
% 3.67/1.60  tff(c_1290, plain, (![C_309, A_310]: (k2_relat_1(C_309)=k1_xboole_0 | v1_funct_2(C_309, A_310, k2_relat_1(C_309)) | k1_relset_1(A_310, k2_relat_1(C_309), C_309)!=A_310 | ~r1_tarski(k1_relat_1(C_309), A_310) | ~v1_relat_1(C_309))), inference(resolution, [status(thm)], [c_8, c_1285])).
% 3.67/1.60  tff(c_44, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.67/1.60  tff(c_42, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'), k2_relat_1('#skF_2')))) | ~v1_funct_2('#skF_2', k1_relat_1('#skF_2'), k2_relat_1('#skF_2')) | ~v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.67/1.60  tff(c_48, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'), k2_relat_1('#skF_2')))) | ~v1_funct_2('#skF_2', k1_relat_1('#skF_2'), k2_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42])).
% 3.67/1.60  tff(c_96, plain, (~v1_funct_2('#skF_2', k1_relat_1('#skF_2'), k2_relat_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_48])).
% 3.67/1.60  tff(c_1297, plain, (k2_relat_1('#skF_2')=k1_xboole_0 | k1_relset_1(k1_relat_1('#skF_2'), k2_relat_1('#skF_2'), '#skF_2')!=k1_relat_1('#skF_2') | ~r1_tarski(k1_relat_1('#skF_2'), k1_relat_1('#skF_2')) | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_1290, c_96])).
% 3.67/1.60  tff(c_1302, plain, (k2_relat_1('#skF_2')=k1_xboole_0 | k1_relset_1(k1_relat_1('#skF_2'), k2_relat_1('#skF_2'), '#skF_2')!=k1_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_8, c_1297])).
% 3.67/1.60  tff(c_1303, plain, (k1_relset_1(k1_relat_1('#skF_2'), k2_relat_1('#skF_2'), '#skF_2')!=k1_relat_1('#skF_2')), inference(splitLeft, [status(thm)], [c_1302])).
% 3.67/1.60  tff(c_1309, plain, (~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1088, c_1303])).
% 3.67/1.60  tff(c_1315, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_1309])).
% 3.67/1.60  tff(c_1316, plain, (k2_relat_1('#skF_2')=k1_xboole_0), inference(splitRight, [status(thm)], [c_1302])).
% 3.67/1.60  tff(c_24, plain, (![A_17]: (r2_hidden('#skF_1'(A_17), A_17) | k1_xboole_0=A_17)), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.67/1.60  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 3.67/1.60  tff(c_12, plain, (![A_3]: (k2_zfmisc_1(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.67/1.60  tff(c_16, plain, (![C_7, B_6, A_5]: (~v1_xboole_0(C_7) | ~m1_subset_1(B_6, k1_zfmisc_1(C_7)) | ~r2_hidden(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.67/1.60  tff(c_1187, plain, (![A_282, B_283, A_284, C_285]: (~v1_xboole_0(k2_zfmisc_1(A_282, B_283)) | ~r2_hidden(A_284, C_285) | ~r1_tarski(k2_relat_1(C_285), B_283) | ~r1_tarski(k1_relat_1(C_285), A_282) | ~v1_relat_1(C_285))), inference(resolution, [status(thm)], [c_771, c_16])).
% 3.67/1.60  tff(c_1191, plain, (![A_284, C_285, A_3]: (~v1_xboole_0(k1_xboole_0) | ~r2_hidden(A_284, C_285) | ~r1_tarski(k2_relat_1(C_285), k1_xboole_0) | ~r1_tarski(k1_relat_1(C_285), A_3) | ~v1_relat_1(C_285))), inference(superposition, [status(thm), theory('equality')], [c_12, c_1187])).
% 3.67/1.60  tff(c_1232, plain, (![A_298, C_299, A_300]: (~r2_hidden(A_298, C_299) | ~r1_tarski(k2_relat_1(C_299), k1_xboole_0) | ~r1_tarski(k1_relat_1(C_299), A_300) | ~v1_relat_1(C_299))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_1191])).
% 3.67/1.60  tff(c_1235, plain, (![A_17, A_300]: (~r1_tarski(k2_relat_1(A_17), k1_xboole_0) | ~r1_tarski(k1_relat_1(A_17), A_300) | ~v1_relat_1(A_17) | k1_xboole_0=A_17)), inference(resolution, [status(thm)], [c_24, c_1232])).
% 3.67/1.60  tff(c_1329, plain, (![A_300]: (~r1_tarski(k1_xboole_0, k1_xboole_0) | ~r1_tarski(k1_relat_1('#skF_2'), A_300) | ~v1_relat_1('#skF_2') | k1_xboole_0='#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1316, c_1235])).
% 3.67/1.60  tff(c_1348, plain, (![A_300]: (~r1_tarski(k1_relat_1('#skF_2'), A_300) | k1_xboole_0='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_8, c_1329])).
% 3.67/1.60  tff(c_1359, plain, (![A_311]: (~r1_tarski(k1_relat_1('#skF_2'), A_311))), inference(splitLeft, [status(thm)], [c_1348])).
% 3.67/1.60  tff(c_1364, plain, $false, inference(resolution, [status(thm)], [c_8, c_1359])).
% 3.67/1.60  tff(c_1365, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_1348])).
% 3.67/1.60  tff(c_145, plain, (![C_83, A_84, B_85]: (m1_subset_1(C_83, k1_zfmisc_1(k2_zfmisc_1(A_84, B_85))) | ~r1_tarski(k2_relat_1(C_83), B_85) | ~r1_tarski(k1_relat_1(C_83), A_84) | ~v1_relat_1(C_83))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.67/1.60  tff(c_292, plain, (![A_120, B_121, C_122]: (k1_relset_1(A_120, B_121, C_122)=k1_relat_1(C_122) | ~r1_tarski(k2_relat_1(C_122), B_121) | ~r1_tarski(k1_relat_1(C_122), A_120) | ~v1_relat_1(C_122))), inference(resolution, [status(thm)], [c_145, c_20])).
% 3.67/1.60  tff(c_313, plain, (![A_126, C_127]: (k1_relset_1(A_126, k2_relat_1(C_127), C_127)=k1_relat_1(C_127) | ~r1_tarski(k1_relat_1(C_127), A_126) | ~v1_relat_1(C_127))), inference(resolution, [status(thm)], [c_8, c_292])).
% 3.67/1.60  tff(c_317, plain, (![C_127]: (k1_relset_1(k1_relat_1(C_127), k2_relat_1(C_127), C_127)=k1_relat_1(C_127) | ~v1_relat_1(C_127))), inference(resolution, [status(thm)], [c_8, c_313])).
% 3.67/1.60  tff(c_222, plain, (![B_108, C_109, A_110]: (k1_xboole_0=B_108 | v1_funct_2(C_109, A_110, B_108) | k1_relset_1(A_110, B_108, C_109)!=A_110 | ~m1_subset_1(C_109, k1_zfmisc_1(k2_zfmisc_1(A_110, B_108))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.67/1.60  tff(c_433, plain, (![B_165, C_166, A_167]: (k1_xboole_0=B_165 | v1_funct_2(C_166, A_167, B_165) | k1_relset_1(A_167, B_165, C_166)!=A_167 | ~r1_tarski(k2_relat_1(C_166), B_165) | ~r1_tarski(k1_relat_1(C_166), A_167) | ~v1_relat_1(C_166))), inference(resolution, [status(thm)], [c_22, c_222])).
% 3.67/1.60  tff(c_444, plain, (![C_170, A_171]: (k2_relat_1(C_170)=k1_xboole_0 | v1_funct_2(C_170, A_171, k2_relat_1(C_170)) | k1_relset_1(A_171, k2_relat_1(C_170), C_170)!=A_171 | ~r1_tarski(k1_relat_1(C_170), A_171) | ~v1_relat_1(C_170))), inference(resolution, [status(thm)], [c_8, c_433])).
% 3.67/1.60  tff(c_447, plain, (k2_relat_1('#skF_2')=k1_xboole_0 | k1_relset_1(k1_relat_1('#skF_2'), k2_relat_1('#skF_2'), '#skF_2')!=k1_relat_1('#skF_2') | ~r1_tarski(k1_relat_1('#skF_2'), k1_relat_1('#skF_2')) | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_444, c_96])).
% 3.67/1.60  tff(c_450, plain, (k2_relat_1('#skF_2')=k1_xboole_0 | k1_relset_1(k1_relat_1('#skF_2'), k2_relat_1('#skF_2'), '#skF_2')!=k1_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_8, c_447])).
% 3.67/1.60  tff(c_451, plain, (k1_relset_1(k1_relat_1('#skF_2'), k2_relat_1('#skF_2'), '#skF_2')!=k1_relat_1('#skF_2')), inference(splitLeft, [status(thm)], [c_450])).
% 3.67/1.60  tff(c_454, plain, (~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_317, c_451])).
% 3.67/1.60  tff(c_458, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_454])).
% 3.67/1.60  tff(c_459, plain, (k2_relat_1('#skF_2')=k1_xboole_0), inference(splitRight, [status(thm)], [c_450])).
% 3.67/1.60  tff(c_338, plain, (![A_132, B_133, A_134, C_135]: (~v1_xboole_0(k2_zfmisc_1(A_132, B_133)) | ~r2_hidden(A_134, C_135) | ~r1_tarski(k2_relat_1(C_135), B_133) | ~r1_tarski(k1_relat_1(C_135), A_132) | ~v1_relat_1(C_135))), inference(resolution, [status(thm)], [c_145, c_16])).
% 3.67/1.60  tff(c_342, plain, (![A_134, C_135, A_3]: (~v1_xboole_0(k1_xboole_0) | ~r2_hidden(A_134, C_135) | ~r1_tarski(k2_relat_1(C_135), k1_xboole_0) | ~r1_tarski(k1_relat_1(C_135), A_3) | ~v1_relat_1(C_135))), inference(superposition, [status(thm), theory('equality')], [c_12, c_338])).
% 3.67/1.60  tff(c_376, plain, (![A_147, C_148, A_149]: (~r2_hidden(A_147, C_148) | ~r1_tarski(k2_relat_1(C_148), k1_xboole_0) | ~r1_tarski(k1_relat_1(C_148), A_149) | ~v1_relat_1(C_148))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_342])).
% 3.67/1.60  tff(c_379, plain, (![A_17, A_149]: (~r1_tarski(k2_relat_1(A_17), k1_xboole_0) | ~r1_tarski(k1_relat_1(A_17), A_149) | ~v1_relat_1(A_17) | k1_xboole_0=A_17)), inference(resolution, [status(thm)], [c_24, c_376])).
% 3.67/1.60  tff(c_471, plain, (![A_149]: (~r1_tarski(k1_xboole_0, k1_xboole_0) | ~r1_tarski(k1_relat_1('#skF_2'), A_149) | ~v1_relat_1('#skF_2') | k1_xboole_0='#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_459, c_379])).
% 3.67/1.60  tff(c_488, plain, (![A_149]: (~r1_tarski(k1_relat_1('#skF_2'), A_149) | k1_xboole_0='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_8, c_471])).
% 3.67/1.60  tff(c_506, plain, (![A_175]: (~r1_tarski(k1_relat_1('#skF_2'), A_175))), inference(splitLeft, [status(thm)], [c_488])).
% 3.67/1.60  tff(c_511, plain, $false, inference(resolution, [status(thm)], [c_8, c_506])).
% 3.67/1.60  tff(c_512, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_488])).
% 3.67/1.60  tff(c_30, plain, (![A_35]: (v1_funct_2(k1_xboole_0, A_35, k1_xboole_0) | k1_xboole_0=A_35 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_35, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.67/1.60  tff(c_51, plain, (![A_35]: (v1_funct_2(k1_xboole_0, A_35, k1_xboole_0) | k1_xboole_0=A_35 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_30])).
% 3.67/1.60  tff(c_98, plain, (~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_51])).
% 3.67/1.60  tff(c_546, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_512, c_512, c_98])).
% 3.67/1.60  tff(c_156, plain, (![C_83, A_3]: (m1_subset_1(C_83, k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k2_relat_1(C_83), k1_xboole_0) | ~r1_tarski(k1_relat_1(C_83), A_3) | ~v1_relat_1(C_83))), inference(superposition, [status(thm), theory('equality')], [c_12, c_145])).
% 3.67/1.60  tff(c_478, plain, (![A_3]: (m1_subset_1('#skF_2', k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k1_xboole_0, k1_xboole_0) | ~r1_tarski(k1_relat_1('#skF_2'), A_3) | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_459, c_156])).
% 3.67/1.60  tff(c_494, plain, (![A_3]: (m1_subset_1('#skF_2', k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k1_relat_1('#skF_2'), A_3))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_8, c_478])).
% 3.67/1.60  tff(c_632, plain, (![A_3]: (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_2')) | ~r1_tarski(k1_relat_1('#skF_2'), A_3))), inference(demodulation, [status(thm), theory('equality')], [c_512, c_494])).
% 3.67/1.60  tff(c_634, plain, (![A_182]: (~r1_tarski(k1_relat_1('#skF_2'), A_182))), inference(negUnitSimplification, [status(thm)], [c_546, c_632])).
% 3.67/1.60  tff(c_639, plain, $false, inference(resolution, [status(thm)], [c_8, c_634])).
% 3.67/1.60  tff(c_641, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(splitRight, [status(thm)], [c_51])).
% 3.67/1.60  tff(c_660, plain, (![A_194, B_195, C_196]: (k1_relset_1(A_194, B_195, C_196)=k1_relat_1(C_196) | ~m1_subset_1(C_196, k1_zfmisc_1(k2_zfmisc_1(A_194, B_195))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.67/1.60  tff(c_678, plain, (![A_200, C_201]: (k1_relset_1(A_200, k1_xboole_0, C_201)=k1_relat_1(C_201) | ~m1_subset_1(C_201, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_660])).
% 3.67/1.60  tff(c_681, plain, (![A_200]: (k1_relset_1(A_200, k1_xboole_0, k1_xboole_0)=k1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_641, c_678])).
% 3.67/1.60  tff(c_709, plain, (![A_214, B_215, C_216]: (m1_subset_1(k1_relset_1(A_214, B_215, C_216), k1_zfmisc_1(A_214)) | ~m1_subset_1(C_216, k1_zfmisc_1(k2_zfmisc_1(A_214, B_215))))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.67/1.60  tff(c_724, plain, (![A_200]: (m1_subset_1(k1_relat_1(k1_xboole_0), k1_zfmisc_1(A_200)) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_200, k1_xboole_0))))), inference(superposition, [status(thm), theory('equality')], [c_681, c_709])).
% 3.67/1.60  tff(c_738, plain, (![A_217]: (m1_subset_1(k1_relat_1(k1_xboole_0), k1_zfmisc_1(A_217)))), inference(demodulation, [status(thm), theory('equality')], [c_641, c_12, c_724])).
% 3.67/1.60  tff(c_754, plain, (![A_217, A_5]: (~v1_xboole_0(A_217) | ~r2_hidden(A_5, k1_relat_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_738, c_16])).
% 3.67/1.60  tff(c_765, plain, (![A_220]: (~r2_hidden(A_220, k1_relat_1(k1_xboole_0)))), inference(splitLeft, [status(thm)], [c_754])).
% 3.67/1.60  tff(c_770, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_24, c_765])).
% 3.67/1.60  tff(c_735, plain, (![A_200]: (m1_subset_1(k1_relat_1(k1_xboole_0), k1_zfmisc_1(A_200)))), inference(demodulation, [status(thm), theory('equality')], [c_641, c_12, c_724])).
% 3.67/1.60  tff(c_794, plain, (![A_224]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_224)))), inference(demodulation, [status(thm), theory('equality')], [c_770, c_735])).
% 3.67/1.60  tff(c_804, plain, (![A_11, B_12]: (k1_relset_1(A_11, B_12, k1_xboole_0)=k1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_794, c_20])).
% 3.67/1.60  tff(c_812, plain, (![A_11, B_12]: (k1_relset_1(A_11, B_12, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_770, c_804])).
% 3.67/1.60  tff(c_786, plain, (![A_200]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_200)))), inference(demodulation, [status(thm), theory('equality')], [c_770, c_735])).
% 3.67/1.60  tff(c_14, plain, (![B_4]: (k2_zfmisc_1(k1_xboole_0, B_4)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.67/1.60  tff(c_34, plain, (![C_37, B_36]: (v1_funct_2(C_37, k1_xboole_0, B_36) | k1_relset_1(k1_xboole_0, B_36, C_37)!=k1_xboole_0 | ~m1_subset_1(C_37, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_36))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.67/1.60  tff(c_860, plain, (![C_229, B_230]: (v1_funct_2(C_229, k1_xboole_0, B_230) | k1_relset_1(k1_xboole_0, B_230, C_229)!=k1_xboole_0 | ~m1_subset_1(C_229, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_34])).
% 3.67/1.60  tff(c_863, plain, (![B_230]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_230) | k1_relset_1(k1_xboole_0, B_230, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_786, c_860])).
% 3.67/1.60  tff(c_869, plain, (![B_230]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_230))), inference(demodulation, [status(thm), theory('equality')], [c_812, c_863])).
% 3.67/1.60  tff(c_1392, plain, (![B_230]: (v1_funct_2('#skF_2', '#skF_2', B_230))), inference(demodulation, [status(thm), theory('equality')], [c_1365, c_1365, c_869])).
% 3.67/1.60  tff(c_1396, plain, (k1_relat_1('#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1365, c_1365, c_770])).
% 3.67/1.60  tff(c_1318, plain, (~v1_funct_2('#skF_2', k1_relat_1('#skF_2'), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1316, c_96])).
% 3.67/1.60  tff(c_1366, plain, (~v1_funct_2('#skF_2', k1_relat_1('#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1365, c_1318])).
% 3.67/1.60  tff(c_1459, plain, (~v1_funct_2('#skF_2', '#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1396, c_1366])).
% 3.67/1.60  tff(c_1514, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1392, c_1459])).
% 3.67/1.60  tff(c_1515, plain, (![A_217]: (~v1_xboole_0(A_217))), inference(splitRight, [status(thm)], [c_754])).
% 3.67/1.60  tff(c_1517, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1515, c_2])).
% 3.67/1.60  tff(c_1518, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'), k2_relat_1('#skF_2'))))), inference(splitRight, [status(thm)], [c_48])).
% 3.67/1.60  tff(c_1569, plain, (~r1_tarski(k2_relat_1('#skF_2'), k2_relat_1('#skF_2')) | ~r1_tarski(k1_relat_1('#skF_2'), k1_relat_1('#skF_2')) | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_1561, c_1518])).
% 3.67/1.60  tff(c_1581, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_8, c_8, c_1569])).
% 3.67/1.60  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.67/1.60  
% 3.67/1.60  Inference rules
% 3.67/1.60  ----------------------
% 3.67/1.60  #Ref     : 0
% 3.67/1.60  #Sup     : 312
% 3.67/1.60  #Fact    : 0
% 3.67/1.60  #Define  : 0
% 3.67/1.60  #Split   : 9
% 3.67/1.60  #Chain   : 0
% 3.67/1.60  #Close   : 0
% 3.67/1.60  
% 3.67/1.60  Ordering : KBO
% 3.67/1.60  
% 3.67/1.60  Simplification rules
% 3.67/1.60  ----------------------
% 3.67/1.60  #Subsume      : 49
% 3.67/1.60  #Demod        : 404
% 3.67/1.60  #Tautology    : 127
% 3.67/1.60  #SimpNegUnit  : 3
% 3.67/1.60  #BackRed      : 92
% 3.67/1.60  
% 3.67/1.60  #Partial instantiations: 0
% 3.67/1.60  #Strategies tried      : 1
% 3.67/1.60  
% 3.67/1.60  Timing (in seconds)
% 3.67/1.60  ----------------------
% 3.67/1.61  Preprocessing        : 0.31
% 3.67/1.61  Parsing              : 0.16
% 3.67/1.61  CNF conversion       : 0.02
% 3.67/1.61  Main loop            : 0.53
% 3.67/1.61  Inferencing          : 0.19
% 3.67/1.61  Reduction            : 0.16
% 3.67/1.61  Demodulation         : 0.11
% 3.67/1.61  BG Simplification    : 0.03
% 3.67/1.61  Subsumption          : 0.11
% 3.67/1.61  Abstraction          : 0.03
% 3.67/1.61  MUC search           : 0.00
% 3.67/1.61  Cooper               : 0.00
% 3.67/1.61  Total                : 0.89
% 3.67/1.61  Index Insertion      : 0.00
% 3.67/1.61  Index Deletion       : 0.00
% 3.67/1.61  Index Matching       : 0.00
% 3.67/1.61  BG Taut test         : 0.00
%------------------------------------------------------------------------------
