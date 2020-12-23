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
% DateTime   : Thu Dec  3 10:08:33 EST 2020

% Result     : Theorem 7.96s
% Output     : CNFRefutation 8.10s
% Verified   : 
% Statistics : Number of formulae       :  153 ( 380 expanded)
%              Number of leaves         :   32 ( 139 expanded)
%              Depth                    :   10
%              Number of atoms          :  296 (1138 expanded)
%              Number of equality atoms :   15 (  33 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k7_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_8 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_108,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ~ v1_xboole_0(B)
           => ! [C] :
                ( ~ v1_xboole_0(C)
               => ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(C,A)))
                   => ! [E] :
                        ( m1_subset_1(E,A)
                       => ( r2_hidden(E,k7_relset_1(C,A,D,B))
                        <=> ? [F] :
                              ( m1_subset_1(F,C)
                              & r2_hidden(k4_tarski(F,E),D)
                              & r2_hidden(F,B) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_relset_1)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_81,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
       => ( r2_hidden(A,k1_relat_1(C))
          & r2_hidden(B,k2_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_relat_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(f_54,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_44,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_37,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(c_36,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_4748,plain,(
    ! [C_846,A_847,B_848] :
      ( v1_relat_1(C_846)
      | ~ m1_subset_1(C_846,k1_zfmisc_1(k2_zfmisc_1(A_847,B_848))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_4757,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_36,c_4748])).

tff(c_7224,plain,(
    ! [A_1282,B_1283,C_1284,D_1285] :
      ( k7_relset_1(A_1282,B_1283,C_1284,D_1285) = k9_relat_1(C_1284,D_1285)
      | ~ m1_subset_1(C_1284,k1_zfmisc_1(k2_zfmisc_1(A_1282,B_1283))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_7235,plain,(
    ! [D_1285] : k7_relset_1('#skF_5','#skF_3','#skF_6',D_1285) = k9_relat_1('#skF_6',D_1285) ),
    inference(resolution,[status(thm)],[c_36,c_7224])).

tff(c_80,plain,(
    ! [C_128,A_129,B_130] :
      ( v1_relat_1(C_128)
      | ~ m1_subset_1(C_128,k1_zfmisc_1(k2_zfmisc_1(A_129,B_130))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_89,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_36,c_80])).

tff(c_3453,plain,(
    ! [A_696,B_697,C_698,D_699] :
      ( k7_relset_1(A_696,B_697,C_698,D_699) = k9_relat_1(C_698,D_699)
      | ~ m1_subset_1(C_698,k1_zfmisc_1(k2_zfmisc_1(A_696,B_697))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_3464,plain,(
    ! [D_699] : k7_relset_1('#skF_5','#skF_3','#skF_6',D_699) = k9_relat_1('#skF_6',D_699) ),
    inference(resolution,[status(thm)],[c_36,c_3453])).

tff(c_1598,plain,(
    ! [A_409,B_410,C_411,D_412] :
      ( k7_relset_1(A_409,B_410,C_411,D_412) = k9_relat_1(C_411,D_412)
      | ~ m1_subset_1(C_411,k1_zfmisc_1(k2_zfmisc_1(A_409,B_410))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_1609,plain,(
    ! [D_412] : k7_relset_1('#skF_5','#skF_3','#skF_6',D_412) = k9_relat_1('#skF_6',D_412) ),
    inference(resolution,[status(thm)],[c_36,c_1598])).

tff(c_58,plain,
    ( r2_hidden('#skF_7',k7_relset_1('#skF_5','#skF_3','#skF_6','#skF_4'))
    | m1_subset_1('#skF_8','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_120,plain,(
    m1_subset_1('#skF_8','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_50,plain,
    ( r2_hidden('#skF_7',k7_relset_1('#skF_5','#skF_3','#skF_6','#skF_4'))
    | r2_hidden('#skF_8','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_71,plain,(
    r2_hidden('#skF_8','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_54,plain,
    ( r2_hidden('#skF_7',k7_relset_1('#skF_5','#skF_3','#skF_6','#skF_4'))
    | r2_hidden(k4_tarski('#skF_8','#skF_7'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_168,plain,(
    r2_hidden(k4_tarski('#skF_8','#skF_7'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_426,plain,(
    ! [A_195,B_196,C_197,D_198] :
      ( k7_relset_1(A_195,B_196,C_197,D_198) = k9_relat_1(C_197,D_198)
      | ~ m1_subset_1(C_197,k1_zfmisc_1(k2_zfmisc_1(A_195,B_196))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_441,plain,(
    ! [D_198] : k7_relset_1('#skF_5','#skF_3','#skF_6',D_198) = k9_relat_1('#skF_6',D_198) ),
    inference(resolution,[status(thm)],[c_36,c_426])).

tff(c_44,plain,(
    ! [F_121] :
      ( ~ r2_hidden(F_121,'#skF_4')
      | ~ r2_hidden(k4_tarski(F_121,'#skF_7'),'#skF_6')
      | ~ m1_subset_1(F_121,'#skF_5')
      | ~ r2_hidden('#skF_7',k7_relset_1('#skF_5','#skF_3','#skF_6','#skF_4')) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_468,plain,(
    ! [F_121] :
      ( ~ r2_hidden(F_121,'#skF_4')
      | ~ r2_hidden(k4_tarski(F_121,'#skF_7'),'#skF_6')
      | ~ m1_subset_1(F_121,'#skF_5')
      | ~ r2_hidden('#skF_7',k9_relat_1('#skF_6','#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_441,c_44])).

tff(c_469,plain,(
    ~ r2_hidden('#skF_7',k9_relat_1('#skF_6','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_468])).

tff(c_28,plain,(
    ! [A_23,C_25,B_24] :
      ( r2_hidden(A_23,k1_relat_1(C_25))
      | ~ r2_hidden(k4_tarski(A_23,B_24),C_25)
      | ~ v1_relat_1(C_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_171,plain,
    ( r2_hidden('#skF_8',k1_relat_1('#skF_6'))
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_168,c_28])).

tff(c_185,plain,(
    r2_hidden('#skF_8',k1_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_171])).

tff(c_590,plain,(
    ! [A_224,C_225,B_226,D_227] :
      ( r2_hidden(A_224,k9_relat_1(C_225,B_226))
      | ~ r2_hidden(D_227,B_226)
      | ~ r2_hidden(k4_tarski(D_227,A_224),C_225)
      | ~ r2_hidden(D_227,k1_relat_1(C_225))
      | ~ v1_relat_1(C_225) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_809,plain,(
    ! [A_255,C_256] :
      ( r2_hidden(A_255,k9_relat_1(C_256,'#skF_4'))
      | ~ r2_hidden(k4_tarski('#skF_8',A_255),C_256)
      | ~ r2_hidden('#skF_8',k1_relat_1(C_256))
      | ~ v1_relat_1(C_256) ) ),
    inference(resolution,[status(thm)],[c_71,c_590])).

tff(c_823,plain,
    ( r2_hidden('#skF_7',k9_relat_1('#skF_6','#skF_4'))
    | ~ r2_hidden('#skF_8',k1_relat_1('#skF_6'))
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_168,c_809])).

tff(c_833,plain,(
    r2_hidden('#skF_7',k9_relat_1('#skF_6','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_185,c_823])).

tff(c_835,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_469,c_833])).

tff(c_960,plain,(
    ! [F_270] :
      ( ~ r2_hidden(F_270,'#skF_4')
      | ~ r2_hidden(k4_tarski(F_270,'#skF_7'),'#skF_6')
      | ~ m1_subset_1(F_270,'#skF_5') ) ),
    inference(splitRight,[status(thm)],[c_468])).

tff(c_971,plain,
    ( ~ r2_hidden('#skF_8','#skF_4')
    | ~ m1_subset_1('#skF_8','#skF_5') ),
    inference(resolution,[status(thm)],[c_168,c_960])).

tff(c_984,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_71,c_971])).

tff(c_985,plain,(
    r2_hidden('#skF_7',k7_relset_1('#skF_5','#skF_3','#skF_6','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_1669,plain,(
    r2_hidden('#skF_7',k9_relat_1('#skF_6','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1609,c_985])).

tff(c_1610,plain,(
    ! [A_413,B_414,C_415] :
      ( r2_hidden(k4_tarski('#skF_2'(A_413,B_414,C_415),A_413),C_415)
      | ~ r2_hidden(A_413,k9_relat_1(C_415,B_414))
      | ~ v1_relat_1(C_415) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_14,plain,(
    ! [A_13,B_14] :
      ( m1_subset_1(A_13,B_14)
      | ~ r2_hidden(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_2020,plain,(
    ! [A_476,B_477,C_478] :
      ( m1_subset_1(k4_tarski('#skF_2'(A_476,B_477,C_478),A_476),C_478)
      | ~ r2_hidden(A_476,k9_relat_1(C_478,B_477))
      | ~ v1_relat_1(C_478) ) ),
    inference(resolution,[status(thm)],[c_1610,c_14])).

tff(c_16,plain,(
    ! [A_15,B_16] :
      ( r2_hidden(A_15,B_16)
      | v1_xboole_0(B_16)
      | ~ m1_subset_1(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_109,plain,(
    ! [C_141,A_142,B_143] :
      ( r2_hidden(C_141,A_142)
      | ~ r2_hidden(C_141,B_143)
      | ~ m1_subset_1(B_143,k1_zfmisc_1(A_142)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_1035,plain,(
    ! [A_282,A_283,B_284] :
      ( r2_hidden(A_282,A_283)
      | ~ m1_subset_1(B_284,k1_zfmisc_1(A_283))
      | v1_xboole_0(B_284)
      | ~ m1_subset_1(A_282,B_284) ) ),
    inference(resolution,[status(thm)],[c_16,c_109])).

tff(c_1046,plain,(
    ! [A_282] :
      ( r2_hidden(A_282,k2_zfmisc_1('#skF_5','#skF_3'))
      | v1_xboole_0('#skF_6')
      | ~ m1_subset_1(A_282,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_36,c_1035])).

tff(c_1047,plain,(
    v1_xboole_0('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_1046])).

tff(c_1142,plain,(
    ! [A_314,B_315,C_316,D_317] :
      ( k7_relset_1(A_314,B_315,C_316,D_317) = k9_relat_1(C_316,D_317)
      | ~ m1_subset_1(C_316,k1_zfmisc_1(k2_zfmisc_1(A_314,B_315))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_1153,plain,(
    ! [D_317] : k7_relset_1('#skF_5','#skF_3','#skF_6',D_317) = k9_relat_1('#skF_6',D_317) ),
    inference(resolution,[status(thm)],[c_36,c_1142])).

tff(c_1157,plain,(
    r2_hidden('#skF_7',k9_relat_1('#skF_6','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1153,c_985])).

tff(c_1291,plain,(
    ! [A_346,B_347,C_348] :
      ( r2_hidden(k4_tarski('#skF_2'(A_346,B_347,C_348),A_346),C_348)
      | ~ r2_hidden(A_346,k9_relat_1(C_348,B_347))
      | ~ v1_relat_1(C_348) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1347,plain,(
    ! [C_349,A_350,B_351] :
      ( ~ v1_xboole_0(C_349)
      | ~ r2_hidden(A_350,k9_relat_1(C_349,B_351))
      | ~ v1_relat_1(C_349) ) ),
    inference(resolution,[status(thm)],[c_1291,c_2])).

tff(c_1354,plain,
    ( ~ v1_xboole_0('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_1157,c_1347])).

tff(c_1375,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_1047,c_1354])).

tff(c_1378,plain,(
    ! [A_352] :
      ( r2_hidden(A_352,k2_zfmisc_1('#skF_5','#skF_3'))
      | ~ m1_subset_1(A_352,'#skF_6') ) ),
    inference(splitRight,[status(thm)],[c_1046])).

tff(c_10,plain,(
    ! [A_5,C_7,B_6,D_8] :
      ( r2_hidden(A_5,C_7)
      | ~ r2_hidden(k4_tarski(A_5,B_6),k2_zfmisc_1(C_7,D_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1406,plain,(
    ! [A_5,B_6] :
      ( r2_hidden(A_5,'#skF_5')
      | ~ m1_subset_1(k4_tarski(A_5,B_6),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_1378,c_10])).

tff(c_2070,plain,(
    ! [A_476,B_477] :
      ( r2_hidden('#skF_2'(A_476,B_477,'#skF_6'),'#skF_5')
      | ~ r2_hidden(A_476,k9_relat_1('#skF_6',B_477))
      | ~ v1_relat_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_2020,c_1406])).

tff(c_2246,plain,(
    ! [A_490,B_491] :
      ( r2_hidden('#skF_2'(A_490,B_491,'#skF_6'),'#skF_5')
      | ~ r2_hidden(A_490,k9_relat_1('#skF_6',B_491)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_2070])).

tff(c_2264,plain,(
    ! [A_492,B_493] :
      ( m1_subset_1('#skF_2'(A_492,B_493,'#skF_6'),'#skF_5')
      | ~ r2_hidden(A_492,k9_relat_1('#skF_6',B_493)) ) ),
    inference(resolution,[status(thm)],[c_2246,c_14])).

tff(c_2288,plain,(
    m1_subset_1('#skF_2'('#skF_7','#skF_4','#skF_6'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_1669,c_2264])).

tff(c_20,plain,(
    ! [A_17,B_18,C_19] :
      ( r2_hidden('#skF_2'(A_17,B_18,C_19),B_18)
      | ~ r2_hidden(A_17,k9_relat_1(C_19,B_18))
      | ~ v1_relat_1(C_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_986,plain,(
    ~ r2_hidden(k4_tarski('#skF_8','#skF_7'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_52,plain,(
    ! [F_121] :
      ( ~ r2_hidden(F_121,'#skF_4')
      | ~ r2_hidden(k4_tarski(F_121,'#skF_7'),'#skF_6')
      | ~ m1_subset_1(F_121,'#skF_5')
      | r2_hidden(k4_tarski('#skF_8','#skF_7'),'#skF_6') ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_1481,plain,(
    ! [F_121] :
      ( ~ r2_hidden(F_121,'#skF_4')
      | ~ r2_hidden(k4_tarski(F_121,'#skF_7'),'#skF_6')
      | ~ m1_subset_1(F_121,'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_986,c_52])).

tff(c_1625,plain,(
    ! [B_414] :
      ( ~ r2_hidden('#skF_2'('#skF_7',B_414,'#skF_6'),'#skF_4')
      | ~ m1_subset_1('#skF_2'('#skF_7',B_414,'#skF_6'),'#skF_5')
      | ~ r2_hidden('#skF_7',k9_relat_1('#skF_6',B_414))
      | ~ v1_relat_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_1610,c_1481])).

tff(c_2775,plain,(
    ! [B_550] :
      ( ~ r2_hidden('#skF_2'('#skF_7',B_550,'#skF_6'),'#skF_4')
      | ~ m1_subset_1('#skF_2'('#skF_7',B_550,'#skF_6'),'#skF_5')
      | ~ r2_hidden('#skF_7',k9_relat_1('#skF_6',B_550)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_1625])).

tff(c_2783,plain,
    ( ~ m1_subset_1('#skF_2'('#skF_7','#skF_4','#skF_6'),'#skF_5')
    | ~ r2_hidden('#skF_7',k9_relat_1('#skF_6','#skF_4'))
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_20,c_2775])).

tff(c_2793,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_1669,c_2288,c_2783])).

tff(c_2794,plain,(
    r2_hidden('#skF_7',k7_relset_1('#skF_5','#skF_3','#skF_6','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_3468,plain,(
    r2_hidden('#skF_7',k9_relat_1('#skF_6','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3464,c_2794])).

tff(c_3520,plain,(
    ! [A_702,B_703,C_704] :
      ( r2_hidden(k4_tarski('#skF_2'(A_702,B_703,C_704),A_702),C_704)
      | ~ r2_hidden(A_702,k9_relat_1(C_704,B_703))
      | ~ v1_relat_1(C_704) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_3874,plain,(
    ! [A_760,B_761,C_762] :
      ( m1_subset_1(k4_tarski('#skF_2'(A_760,B_761,C_762),A_760),C_762)
      | ~ r2_hidden(A_760,k9_relat_1(C_762,B_761))
      | ~ v1_relat_1(C_762) ) ),
    inference(resolution,[status(thm)],[c_3520,c_14])).

tff(c_2863,plain,(
    ! [A_568,A_569,B_570] :
      ( r2_hidden(A_568,A_569)
      | ~ m1_subset_1(B_570,k1_zfmisc_1(A_569))
      | v1_xboole_0(B_570)
      | ~ m1_subset_1(A_568,B_570) ) ),
    inference(resolution,[status(thm)],[c_16,c_109])).

tff(c_2874,plain,(
    ! [A_568] :
      ( r2_hidden(A_568,k2_zfmisc_1('#skF_5','#skF_3'))
      | v1_xboole_0('#skF_6')
      | ~ m1_subset_1(A_568,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_36,c_2863])).

tff(c_2875,plain,(
    v1_xboole_0('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_2874])).

tff(c_2974,plain,(
    ! [A_598,B_599,C_600,D_601] :
      ( k7_relset_1(A_598,B_599,C_600,D_601) = k9_relat_1(C_600,D_601)
      | ~ m1_subset_1(C_600,k1_zfmisc_1(k2_zfmisc_1(A_598,B_599))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_2985,plain,(
    ! [D_601] : k7_relset_1('#skF_5','#skF_3','#skF_6',D_601) = k9_relat_1('#skF_6',D_601) ),
    inference(resolution,[status(thm)],[c_36,c_2974])).

tff(c_2989,plain,(
    r2_hidden('#skF_7',k9_relat_1('#skF_6','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2985,c_2794])).

tff(c_3124,plain,(
    ! [A_626,B_627,C_628] :
      ( r2_hidden(k4_tarski('#skF_2'(A_626,B_627,C_628),A_626),C_628)
      | ~ r2_hidden(A_626,k9_relat_1(C_628,B_627))
      | ~ v1_relat_1(C_628) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_3180,plain,(
    ! [C_629,A_630,B_631] :
      ( ~ v1_xboole_0(C_629)
      | ~ r2_hidden(A_630,k9_relat_1(C_629,B_631))
      | ~ v1_relat_1(C_629) ) ),
    inference(resolution,[status(thm)],[c_3124,c_2])).

tff(c_3187,plain,
    ( ~ v1_xboole_0('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_2989,c_3180])).

tff(c_3208,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_2875,c_3187])).

tff(c_3211,plain,(
    ! [A_632] :
      ( r2_hidden(A_632,k2_zfmisc_1('#skF_5','#skF_3'))
      | ~ m1_subset_1(A_632,'#skF_6') ) ),
    inference(splitRight,[status(thm)],[c_2874])).

tff(c_3239,plain,(
    ! [A_5,B_6] :
      ( r2_hidden(A_5,'#skF_5')
      | ~ m1_subset_1(k4_tarski(A_5,B_6),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_3211,c_10])).

tff(c_3924,plain,(
    ! [A_760,B_761] :
      ( r2_hidden('#skF_2'(A_760,B_761,'#skF_6'),'#skF_5')
      | ~ r2_hidden(A_760,k9_relat_1('#skF_6',B_761))
      | ~ v1_relat_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_3874,c_3239])).

tff(c_4022,plain,(
    ! [A_770,B_771] :
      ( r2_hidden('#skF_2'(A_770,B_771,'#skF_6'),'#skF_5')
      | ~ r2_hidden(A_770,k9_relat_1('#skF_6',B_771)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_3924])).

tff(c_4037,plain,(
    ! [A_772,B_773] :
      ( m1_subset_1('#skF_2'(A_772,B_773,'#skF_6'),'#skF_5')
      | ~ r2_hidden(A_772,k9_relat_1('#skF_6',B_773)) ) ),
    inference(resolution,[status(thm)],[c_4022,c_14])).

tff(c_4062,plain,(
    m1_subset_1('#skF_2'('#skF_7','#skF_4','#skF_6'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_3468,c_4037])).

tff(c_2795,plain,(
    ~ m1_subset_1('#skF_8','#skF_5') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_56,plain,(
    ! [F_121] :
      ( ~ r2_hidden(F_121,'#skF_4')
      | ~ r2_hidden(k4_tarski(F_121,'#skF_7'),'#skF_6')
      | ~ m1_subset_1(F_121,'#skF_5')
      | m1_subset_1('#skF_8','#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_2855,plain,(
    ! [F_121] :
      ( ~ r2_hidden(F_121,'#skF_4')
      | ~ r2_hidden(k4_tarski(F_121,'#skF_7'),'#skF_6')
      | ~ m1_subset_1(F_121,'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_2795,c_56])).

tff(c_3539,plain,(
    ! [B_703] :
      ( ~ r2_hidden('#skF_2'('#skF_7',B_703,'#skF_6'),'#skF_4')
      | ~ m1_subset_1('#skF_2'('#skF_7',B_703,'#skF_6'),'#skF_5')
      | ~ r2_hidden('#skF_7',k9_relat_1('#skF_6',B_703))
      | ~ v1_relat_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_3520,c_2855])).

tff(c_4703,plain,(
    ! [B_843] :
      ( ~ r2_hidden('#skF_2'('#skF_7',B_843,'#skF_6'),'#skF_4')
      | ~ m1_subset_1('#skF_2'('#skF_7',B_843,'#skF_6'),'#skF_5')
      | ~ r2_hidden('#skF_7',k9_relat_1('#skF_6',B_843)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_3539])).

tff(c_4711,plain,
    ( ~ m1_subset_1('#skF_2'('#skF_7','#skF_4','#skF_6'),'#skF_5')
    | ~ r2_hidden('#skF_7',k9_relat_1('#skF_6','#skF_4'))
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_20,c_4703])).

tff(c_4721,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_3468,c_4062,c_4711])).

tff(c_4722,plain,(
    r2_hidden('#skF_7',k7_relset_1('#skF_5','#skF_3','#skF_6','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_7239,plain,(
    r2_hidden('#skF_7',k9_relat_1('#skF_6','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7235,c_4722])).

tff(c_7291,plain,(
    ! [A_1288,B_1289,C_1290] :
      ( r2_hidden(k4_tarski('#skF_2'(A_1288,B_1289,C_1290),A_1288),C_1290)
      | ~ r2_hidden(A_1288,k9_relat_1(C_1290,B_1289))
      | ~ v1_relat_1(C_1290) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_7627,plain,(
    ! [A_1349,B_1350,C_1351] :
      ( m1_subset_1(k4_tarski('#skF_2'(A_1349,B_1350,C_1351),A_1349),C_1351)
      | ~ r2_hidden(A_1349,k9_relat_1(C_1351,B_1350))
      | ~ v1_relat_1(C_1351) ) ),
    inference(resolution,[status(thm)],[c_7291,c_14])).

tff(c_4758,plain,(
    ! [C_849,A_850,B_851] :
      ( r2_hidden(C_849,A_850)
      | ~ r2_hidden(C_849,B_851)
      | ~ m1_subset_1(B_851,k1_zfmisc_1(A_850)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_6613,plain,(
    ! [A_1149,A_1150,B_1151] :
      ( r2_hidden(A_1149,A_1150)
      | ~ m1_subset_1(B_1151,k1_zfmisc_1(A_1150))
      | v1_xboole_0(B_1151)
      | ~ m1_subset_1(A_1149,B_1151) ) ),
    inference(resolution,[status(thm)],[c_16,c_4758])).

tff(c_6624,plain,(
    ! [A_1149] :
      ( r2_hidden(A_1149,k2_zfmisc_1('#skF_5','#skF_3'))
      | v1_xboole_0('#skF_6')
      | ~ m1_subset_1(A_1149,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_36,c_6613])).

tff(c_6625,plain,(
    v1_xboole_0('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_6624])).

tff(c_6822,plain,(
    ! [A_1208,B_1209,C_1210,D_1211] :
      ( k7_relset_1(A_1208,B_1209,C_1210,D_1211) = k9_relat_1(C_1210,D_1211)
      | ~ m1_subset_1(C_1210,k1_zfmisc_1(k2_zfmisc_1(A_1208,B_1209))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_6833,plain,(
    ! [D_1211] : k7_relset_1('#skF_5','#skF_3','#skF_6',D_1211) = k9_relat_1('#skF_6',D_1211) ),
    inference(resolution,[status(thm)],[c_36,c_6822])).

tff(c_6837,plain,(
    r2_hidden('#skF_7',k9_relat_1('#skF_6','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6833,c_4722])).

tff(c_6890,plain,(
    ! [A_1214,B_1215,C_1216] :
      ( r2_hidden(k4_tarski('#skF_2'(A_1214,B_1215,C_1216),A_1214),C_1216)
      | ~ r2_hidden(A_1214,k9_relat_1(C_1216,B_1215))
      | ~ v1_relat_1(C_1216) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_6946,plain,(
    ! [C_1217,A_1218,B_1219] :
      ( ~ v1_xboole_0(C_1217)
      | ~ r2_hidden(A_1218,k9_relat_1(C_1217,B_1219))
      | ~ v1_relat_1(C_1217) ) ),
    inference(resolution,[status(thm)],[c_6890,c_2])).

tff(c_6953,plain,
    ( ~ v1_xboole_0('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_6837,c_6946])).

tff(c_6974,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4757,c_6625,c_6953])).

tff(c_6977,plain,(
    ! [A_1220] :
      ( r2_hidden(A_1220,k2_zfmisc_1('#skF_5','#skF_3'))
      | ~ m1_subset_1(A_1220,'#skF_6') ) ),
    inference(splitRight,[status(thm)],[c_6624])).

tff(c_7005,plain,(
    ! [A_5,B_6] :
      ( r2_hidden(A_5,'#skF_5')
      | ~ m1_subset_1(k4_tarski(A_5,B_6),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_6977,c_10])).

tff(c_7673,plain,(
    ! [A_1349,B_1350] :
      ( r2_hidden('#skF_2'(A_1349,B_1350,'#skF_6'),'#skF_5')
      | ~ r2_hidden(A_1349,k9_relat_1('#skF_6',B_1350))
      | ~ v1_relat_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_7627,c_7005])).

tff(c_7775,plain,(
    ! [A_1358,B_1359] :
      ( r2_hidden('#skF_2'(A_1358,B_1359,'#skF_6'),'#skF_5')
      | ~ r2_hidden(A_1358,k9_relat_1('#skF_6',B_1359)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4757,c_7673])).

tff(c_7790,plain,(
    ! [A_1360,B_1361] :
      ( m1_subset_1('#skF_2'(A_1360,B_1361,'#skF_6'),'#skF_5')
      | ~ r2_hidden(A_1360,k9_relat_1('#skF_6',B_1361)) ) ),
    inference(resolution,[status(thm)],[c_7775,c_14])).

tff(c_7815,plain,(
    m1_subset_1('#skF_2'('#skF_7','#skF_4','#skF_6'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_7239,c_7790])).

tff(c_4723,plain,(
    ~ r2_hidden('#skF_8','#skF_4') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_48,plain,(
    ! [F_121] :
      ( ~ r2_hidden(F_121,'#skF_4')
      | ~ r2_hidden(k4_tarski(F_121,'#skF_7'),'#skF_6')
      | ~ m1_subset_1(F_121,'#skF_5')
      | r2_hidden('#skF_8','#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_7009,plain,(
    ! [F_121] :
      ( ~ r2_hidden(F_121,'#skF_4')
      | ~ r2_hidden(k4_tarski(F_121,'#skF_7'),'#skF_6')
      | ~ m1_subset_1(F_121,'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_4723,c_48])).

tff(c_7310,plain,(
    ! [B_1289] :
      ( ~ r2_hidden('#skF_2'('#skF_7',B_1289,'#skF_6'),'#skF_4')
      | ~ m1_subset_1('#skF_2'('#skF_7',B_1289,'#skF_6'),'#skF_5')
      | ~ r2_hidden('#skF_7',k9_relat_1('#skF_6',B_1289))
      | ~ v1_relat_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_7291,c_7009])).

tff(c_8518,plain,(
    ! [B_1437] :
      ( ~ r2_hidden('#skF_2'('#skF_7',B_1437,'#skF_6'),'#skF_4')
      | ~ m1_subset_1('#skF_2'('#skF_7',B_1437,'#skF_6'),'#skF_5')
      | ~ r2_hidden('#skF_7',k9_relat_1('#skF_6',B_1437)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4757,c_7310])).

tff(c_8526,plain,
    ( ~ m1_subset_1('#skF_2'('#skF_7','#skF_4','#skF_6'),'#skF_5')
    | ~ r2_hidden('#skF_7',k9_relat_1('#skF_6','#skF_4'))
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_20,c_8518])).

tff(c_8536,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4757,c_7239,c_7815,c_8526])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:00:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.96/2.77  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.96/2.79  
% 7.96/2.79  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.96/2.79  %$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k7_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_8 > #skF_4
% 7.96/2.79  
% 7.96/2.79  %Foreground sorts:
% 7.96/2.79  
% 7.96/2.79  
% 7.96/2.79  %Background operators:
% 7.96/2.79  
% 7.96/2.79  
% 7.96/2.79  %Foreground operators:
% 7.96/2.79  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.96/2.79  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.96/2.79  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 7.96/2.79  tff('#skF_1', type, '#skF_1': $i > $i).
% 7.96/2.79  tff('#skF_7', type, '#skF_7': $i).
% 7.96/2.79  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.96/2.79  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 7.96/2.79  tff('#skF_5', type, '#skF_5': $i).
% 7.96/2.79  tff('#skF_6', type, '#skF_6': $i).
% 7.96/2.79  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 7.96/2.79  tff('#skF_3', type, '#skF_3': $i).
% 7.96/2.79  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 7.96/2.79  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.96/2.79  tff('#skF_8', type, '#skF_8': $i).
% 7.96/2.79  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.96/2.79  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.96/2.79  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.96/2.79  tff('#skF_4', type, '#skF_4': $i).
% 7.96/2.79  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.96/2.79  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 7.96/2.79  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.96/2.79  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.96/2.79  
% 8.10/2.84  tff(f_108, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (~v1_xboole_0(C) => (![D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, A))) => (![E]: (m1_subset_1(E, A) => (r2_hidden(E, k7_relset_1(C, A, D, B)) <=> (?[F]: ((m1_subset_1(F, C) & r2_hidden(k4_tarski(F, E), D)) & r2_hidden(F, B)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_relset_1)).
% 8.10/2.84  tff(f_77, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 8.10/2.84  tff(f_81, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 8.10/2.84  tff(f_73, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) => (r2_hidden(A, k1_relat_1(C)) & r2_hidden(B, k2_relat_1(C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_relat_1)).
% 8.10/2.84  tff(f_65, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t143_relat_1)).
% 8.10/2.84  tff(f_48, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 8.10/2.84  tff(f_54, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 8.10/2.84  tff(f_44, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 8.10/2.84  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 8.10/2.84  tff(f_37, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 8.10/2.84  tff(c_36, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_108])).
% 8.10/2.84  tff(c_4748, plain, (![C_846, A_847, B_848]: (v1_relat_1(C_846) | ~m1_subset_1(C_846, k1_zfmisc_1(k2_zfmisc_1(A_847, B_848))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 8.10/2.84  tff(c_4757, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_36, c_4748])).
% 8.10/2.84  tff(c_7224, plain, (![A_1282, B_1283, C_1284, D_1285]: (k7_relset_1(A_1282, B_1283, C_1284, D_1285)=k9_relat_1(C_1284, D_1285) | ~m1_subset_1(C_1284, k1_zfmisc_1(k2_zfmisc_1(A_1282, B_1283))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 8.10/2.84  tff(c_7235, plain, (![D_1285]: (k7_relset_1('#skF_5', '#skF_3', '#skF_6', D_1285)=k9_relat_1('#skF_6', D_1285))), inference(resolution, [status(thm)], [c_36, c_7224])).
% 8.10/2.84  tff(c_80, plain, (![C_128, A_129, B_130]: (v1_relat_1(C_128) | ~m1_subset_1(C_128, k1_zfmisc_1(k2_zfmisc_1(A_129, B_130))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 8.10/2.84  tff(c_89, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_36, c_80])).
% 8.10/2.84  tff(c_3453, plain, (![A_696, B_697, C_698, D_699]: (k7_relset_1(A_696, B_697, C_698, D_699)=k9_relat_1(C_698, D_699) | ~m1_subset_1(C_698, k1_zfmisc_1(k2_zfmisc_1(A_696, B_697))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 8.10/2.84  tff(c_3464, plain, (![D_699]: (k7_relset_1('#skF_5', '#skF_3', '#skF_6', D_699)=k9_relat_1('#skF_6', D_699))), inference(resolution, [status(thm)], [c_36, c_3453])).
% 8.10/2.84  tff(c_1598, plain, (![A_409, B_410, C_411, D_412]: (k7_relset_1(A_409, B_410, C_411, D_412)=k9_relat_1(C_411, D_412) | ~m1_subset_1(C_411, k1_zfmisc_1(k2_zfmisc_1(A_409, B_410))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 8.10/2.84  tff(c_1609, plain, (![D_412]: (k7_relset_1('#skF_5', '#skF_3', '#skF_6', D_412)=k9_relat_1('#skF_6', D_412))), inference(resolution, [status(thm)], [c_36, c_1598])).
% 8.10/2.84  tff(c_58, plain, (r2_hidden('#skF_7', k7_relset_1('#skF_5', '#skF_3', '#skF_6', '#skF_4')) | m1_subset_1('#skF_8', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_108])).
% 8.10/2.84  tff(c_120, plain, (m1_subset_1('#skF_8', '#skF_5')), inference(splitLeft, [status(thm)], [c_58])).
% 8.10/2.84  tff(c_50, plain, (r2_hidden('#skF_7', k7_relset_1('#skF_5', '#skF_3', '#skF_6', '#skF_4')) | r2_hidden('#skF_8', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_108])).
% 8.10/2.84  tff(c_71, plain, (r2_hidden('#skF_8', '#skF_4')), inference(splitLeft, [status(thm)], [c_50])).
% 8.10/2.84  tff(c_54, plain, (r2_hidden('#skF_7', k7_relset_1('#skF_5', '#skF_3', '#skF_6', '#skF_4')) | r2_hidden(k4_tarski('#skF_8', '#skF_7'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_108])).
% 8.10/2.84  tff(c_168, plain, (r2_hidden(k4_tarski('#skF_8', '#skF_7'), '#skF_6')), inference(splitLeft, [status(thm)], [c_54])).
% 8.10/2.84  tff(c_426, plain, (![A_195, B_196, C_197, D_198]: (k7_relset_1(A_195, B_196, C_197, D_198)=k9_relat_1(C_197, D_198) | ~m1_subset_1(C_197, k1_zfmisc_1(k2_zfmisc_1(A_195, B_196))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 8.10/2.84  tff(c_441, plain, (![D_198]: (k7_relset_1('#skF_5', '#skF_3', '#skF_6', D_198)=k9_relat_1('#skF_6', D_198))), inference(resolution, [status(thm)], [c_36, c_426])).
% 8.10/2.84  tff(c_44, plain, (![F_121]: (~r2_hidden(F_121, '#skF_4') | ~r2_hidden(k4_tarski(F_121, '#skF_7'), '#skF_6') | ~m1_subset_1(F_121, '#skF_5') | ~r2_hidden('#skF_7', k7_relset_1('#skF_5', '#skF_3', '#skF_6', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_108])).
% 8.10/2.84  tff(c_468, plain, (![F_121]: (~r2_hidden(F_121, '#skF_4') | ~r2_hidden(k4_tarski(F_121, '#skF_7'), '#skF_6') | ~m1_subset_1(F_121, '#skF_5') | ~r2_hidden('#skF_7', k9_relat_1('#skF_6', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_441, c_44])).
% 8.10/2.84  tff(c_469, plain, (~r2_hidden('#skF_7', k9_relat_1('#skF_6', '#skF_4'))), inference(splitLeft, [status(thm)], [c_468])).
% 8.10/2.84  tff(c_28, plain, (![A_23, C_25, B_24]: (r2_hidden(A_23, k1_relat_1(C_25)) | ~r2_hidden(k4_tarski(A_23, B_24), C_25) | ~v1_relat_1(C_25))), inference(cnfTransformation, [status(thm)], [f_73])).
% 8.10/2.84  tff(c_171, plain, (r2_hidden('#skF_8', k1_relat_1('#skF_6')) | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_168, c_28])).
% 8.10/2.84  tff(c_185, plain, (r2_hidden('#skF_8', k1_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_89, c_171])).
% 8.10/2.84  tff(c_590, plain, (![A_224, C_225, B_226, D_227]: (r2_hidden(A_224, k9_relat_1(C_225, B_226)) | ~r2_hidden(D_227, B_226) | ~r2_hidden(k4_tarski(D_227, A_224), C_225) | ~r2_hidden(D_227, k1_relat_1(C_225)) | ~v1_relat_1(C_225))), inference(cnfTransformation, [status(thm)], [f_65])).
% 8.10/2.84  tff(c_809, plain, (![A_255, C_256]: (r2_hidden(A_255, k9_relat_1(C_256, '#skF_4')) | ~r2_hidden(k4_tarski('#skF_8', A_255), C_256) | ~r2_hidden('#skF_8', k1_relat_1(C_256)) | ~v1_relat_1(C_256))), inference(resolution, [status(thm)], [c_71, c_590])).
% 8.10/2.84  tff(c_823, plain, (r2_hidden('#skF_7', k9_relat_1('#skF_6', '#skF_4')) | ~r2_hidden('#skF_8', k1_relat_1('#skF_6')) | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_168, c_809])).
% 8.10/2.84  tff(c_833, plain, (r2_hidden('#skF_7', k9_relat_1('#skF_6', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_89, c_185, c_823])).
% 8.10/2.84  tff(c_835, plain, $false, inference(negUnitSimplification, [status(thm)], [c_469, c_833])).
% 8.10/2.84  tff(c_960, plain, (![F_270]: (~r2_hidden(F_270, '#skF_4') | ~r2_hidden(k4_tarski(F_270, '#skF_7'), '#skF_6') | ~m1_subset_1(F_270, '#skF_5'))), inference(splitRight, [status(thm)], [c_468])).
% 8.10/2.84  tff(c_971, plain, (~r2_hidden('#skF_8', '#skF_4') | ~m1_subset_1('#skF_8', '#skF_5')), inference(resolution, [status(thm)], [c_168, c_960])).
% 8.10/2.84  tff(c_984, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_120, c_71, c_971])).
% 8.10/2.84  tff(c_985, plain, (r2_hidden('#skF_7', k7_relset_1('#skF_5', '#skF_3', '#skF_6', '#skF_4'))), inference(splitRight, [status(thm)], [c_54])).
% 8.10/2.84  tff(c_1669, plain, (r2_hidden('#skF_7', k9_relat_1('#skF_6', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1609, c_985])).
% 8.10/2.84  tff(c_1610, plain, (![A_413, B_414, C_415]: (r2_hidden(k4_tarski('#skF_2'(A_413, B_414, C_415), A_413), C_415) | ~r2_hidden(A_413, k9_relat_1(C_415, B_414)) | ~v1_relat_1(C_415))), inference(cnfTransformation, [status(thm)], [f_65])).
% 8.10/2.84  tff(c_14, plain, (![A_13, B_14]: (m1_subset_1(A_13, B_14) | ~r2_hidden(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_48])).
% 8.10/2.84  tff(c_2020, plain, (![A_476, B_477, C_478]: (m1_subset_1(k4_tarski('#skF_2'(A_476, B_477, C_478), A_476), C_478) | ~r2_hidden(A_476, k9_relat_1(C_478, B_477)) | ~v1_relat_1(C_478))), inference(resolution, [status(thm)], [c_1610, c_14])).
% 8.10/2.84  tff(c_16, plain, (![A_15, B_16]: (r2_hidden(A_15, B_16) | v1_xboole_0(B_16) | ~m1_subset_1(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_54])).
% 8.10/2.84  tff(c_109, plain, (![C_141, A_142, B_143]: (r2_hidden(C_141, A_142) | ~r2_hidden(C_141, B_143) | ~m1_subset_1(B_143, k1_zfmisc_1(A_142)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 8.10/2.84  tff(c_1035, plain, (![A_282, A_283, B_284]: (r2_hidden(A_282, A_283) | ~m1_subset_1(B_284, k1_zfmisc_1(A_283)) | v1_xboole_0(B_284) | ~m1_subset_1(A_282, B_284))), inference(resolution, [status(thm)], [c_16, c_109])).
% 8.10/2.84  tff(c_1046, plain, (![A_282]: (r2_hidden(A_282, k2_zfmisc_1('#skF_5', '#skF_3')) | v1_xboole_0('#skF_6') | ~m1_subset_1(A_282, '#skF_6'))), inference(resolution, [status(thm)], [c_36, c_1035])).
% 8.10/2.84  tff(c_1047, plain, (v1_xboole_0('#skF_6')), inference(splitLeft, [status(thm)], [c_1046])).
% 8.10/2.84  tff(c_1142, plain, (![A_314, B_315, C_316, D_317]: (k7_relset_1(A_314, B_315, C_316, D_317)=k9_relat_1(C_316, D_317) | ~m1_subset_1(C_316, k1_zfmisc_1(k2_zfmisc_1(A_314, B_315))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 8.10/2.84  tff(c_1153, plain, (![D_317]: (k7_relset_1('#skF_5', '#skF_3', '#skF_6', D_317)=k9_relat_1('#skF_6', D_317))), inference(resolution, [status(thm)], [c_36, c_1142])).
% 8.10/2.84  tff(c_1157, plain, (r2_hidden('#skF_7', k9_relat_1('#skF_6', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1153, c_985])).
% 8.10/2.84  tff(c_1291, plain, (![A_346, B_347, C_348]: (r2_hidden(k4_tarski('#skF_2'(A_346, B_347, C_348), A_346), C_348) | ~r2_hidden(A_346, k9_relat_1(C_348, B_347)) | ~v1_relat_1(C_348))), inference(cnfTransformation, [status(thm)], [f_65])).
% 8.10/2.84  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.10/2.84  tff(c_1347, plain, (![C_349, A_350, B_351]: (~v1_xboole_0(C_349) | ~r2_hidden(A_350, k9_relat_1(C_349, B_351)) | ~v1_relat_1(C_349))), inference(resolution, [status(thm)], [c_1291, c_2])).
% 8.10/2.84  tff(c_1354, plain, (~v1_xboole_0('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_1157, c_1347])).
% 8.10/2.84  tff(c_1375, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_89, c_1047, c_1354])).
% 8.10/2.84  tff(c_1378, plain, (![A_352]: (r2_hidden(A_352, k2_zfmisc_1('#skF_5', '#skF_3')) | ~m1_subset_1(A_352, '#skF_6'))), inference(splitRight, [status(thm)], [c_1046])).
% 8.10/2.84  tff(c_10, plain, (![A_5, C_7, B_6, D_8]: (r2_hidden(A_5, C_7) | ~r2_hidden(k4_tarski(A_5, B_6), k2_zfmisc_1(C_7, D_8)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 8.10/2.84  tff(c_1406, plain, (![A_5, B_6]: (r2_hidden(A_5, '#skF_5') | ~m1_subset_1(k4_tarski(A_5, B_6), '#skF_6'))), inference(resolution, [status(thm)], [c_1378, c_10])).
% 8.10/2.84  tff(c_2070, plain, (![A_476, B_477]: (r2_hidden('#skF_2'(A_476, B_477, '#skF_6'), '#skF_5') | ~r2_hidden(A_476, k9_relat_1('#skF_6', B_477)) | ~v1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_2020, c_1406])).
% 8.10/2.84  tff(c_2246, plain, (![A_490, B_491]: (r2_hidden('#skF_2'(A_490, B_491, '#skF_6'), '#skF_5') | ~r2_hidden(A_490, k9_relat_1('#skF_6', B_491)))), inference(demodulation, [status(thm), theory('equality')], [c_89, c_2070])).
% 8.10/2.84  tff(c_2264, plain, (![A_492, B_493]: (m1_subset_1('#skF_2'(A_492, B_493, '#skF_6'), '#skF_5') | ~r2_hidden(A_492, k9_relat_1('#skF_6', B_493)))), inference(resolution, [status(thm)], [c_2246, c_14])).
% 8.10/2.84  tff(c_2288, plain, (m1_subset_1('#skF_2'('#skF_7', '#skF_4', '#skF_6'), '#skF_5')), inference(resolution, [status(thm)], [c_1669, c_2264])).
% 8.10/2.84  tff(c_20, plain, (![A_17, B_18, C_19]: (r2_hidden('#skF_2'(A_17, B_18, C_19), B_18) | ~r2_hidden(A_17, k9_relat_1(C_19, B_18)) | ~v1_relat_1(C_19))), inference(cnfTransformation, [status(thm)], [f_65])).
% 8.10/2.84  tff(c_986, plain, (~r2_hidden(k4_tarski('#skF_8', '#skF_7'), '#skF_6')), inference(splitRight, [status(thm)], [c_54])).
% 8.10/2.84  tff(c_52, plain, (![F_121]: (~r2_hidden(F_121, '#skF_4') | ~r2_hidden(k4_tarski(F_121, '#skF_7'), '#skF_6') | ~m1_subset_1(F_121, '#skF_5') | r2_hidden(k4_tarski('#skF_8', '#skF_7'), '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_108])).
% 8.10/2.84  tff(c_1481, plain, (![F_121]: (~r2_hidden(F_121, '#skF_4') | ~r2_hidden(k4_tarski(F_121, '#skF_7'), '#skF_6') | ~m1_subset_1(F_121, '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_986, c_52])).
% 8.10/2.84  tff(c_1625, plain, (![B_414]: (~r2_hidden('#skF_2'('#skF_7', B_414, '#skF_6'), '#skF_4') | ~m1_subset_1('#skF_2'('#skF_7', B_414, '#skF_6'), '#skF_5') | ~r2_hidden('#skF_7', k9_relat_1('#skF_6', B_414)) | ~v1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_1610, c_1481])).
% 8.10/2.84  tff(c_2775, plain, (![B_550]: (~r2_hidden('#skF_2'('#skF_7', B_550, '#skF_6'), '#skF_4') | ~m1_subset_1('#skF_2'('#skF_7', B_550, '#skF_6'), '#skF_5') | ~r2_hidden('#skF_7', k9_relat_1('#skF_6', B_550)))), inference(demodulation, [status(thm), theory('equality')], [c_89, c_1625])).
% 8.10/2.84  tff(c_2783, plain, (~m1_subset_1('#skF_2'('#skF_7', '#skF_4', '#skF_6'), '#skF_5') | ~r2_hidden('#skF_7', k9_relat_1('#skF_6', '#skF_4')) | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_20, c_2775])).
% 8.10/2.84  tff(c_2793, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_89, c_1669, c_2288, c_2783])).
% 8.10/2.84  tff(c_2794, plain, (r2_hidden('#skF_7', k7_relset_1('#skF_5', '#skF_3', '#skF_6', '#skF_4'))), inference(splitRight, [status(thm)], [c_58])).
% 8.10/2.84  tff(c_3468, plain, (r2_hidden('#skF_7', k9_relat_1('#skF_6', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_3464, c_2794])).
% 8.10/2.84  tff(c_3520, plain, (![A_702, B_703, C_704]: (r2_hidden(k4_tarski('#skF_2'(A_702, B_703, C_704), A_702), C_704) | ~r2_hidden(A_702, k9_relat_1(C_704, B_703)) | ~v1_relat_1(C_704))), inference(cnfTransformation, [status(thm)], [f_65])).
% 8.10/2.84  tff(c_3874, plain, (![A_760, B_761, C_762]: (m1_subset_1(k4_tarski('#skF_2'(A_760, B_761, C_762), A_760), C_762) | ~r2_hidden(A_760, k9_relat_1(C_762, B_761)) | ~v1_relat_1(C_762))), inference(resolution, [status(thm)], [c_3520, c_14])).
% 8.10/2.84  tff(c_2863, plain, (![A_568, A_569, B_570]: (r2_hidden(A_568, A_569) | ~m1_subset_1(B_570, k1_zfmisc_1(A_569)) | v1_xboole_0(B_570) | ~m1_subset_1(A_568, B_570))), inference(resolution, [status(thm)], [c_16, c_109])).
% 8.10/2.84  tff(c_2874, plain, (![A_568]: (r2_hidden(A_568, k2_zfmisc_1('#skF_5', '#skF_3')) | v1_xboole_0('#skF_6') | ~m1_subset_1(A_568, '#skF_6'))), inference(resolution, [status(thm)], [c_36, c_2863])).
% 8.10/2.84  tff(c_2875, plain, (v1_xboole_0('#skF_6')), inference(splitLeft, [status(thm)], [c_2874])).
% 8.10/2.84  tff(c_2974, plain, (![A_598, B_599, C_600, D_601]: (k7_relset_1(A_598, B_599, C_600, D_601)=k9_relat_1(C_600, D_601) | ~m1_subset_1(C_600, k1_zfmisc_1(k2_zfmisc_1(A_598, B_599))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 8.10/2.84  tff(c_2985, plain, (![D_601]: (k7_relset_1('#skF_5', '#skF_3', '#skF_6', D_601)=k9_relat_1('#skF_6', D_601))), inference(resolution, [status(thm)], [c_36, c_2974])).
% 8.10/2.84  tff(c_2989, plain, (r2_hidden('#skF_7', k9_relat_1('#skF_6', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_2985, c_2794])).
% 8.10/2.84  tff(c_3124, plain, (![A_626, B_627, C_628]: (r2_hidden(k4_tarski('#skF_2'(A_626, B_627, C_628), A_626), C_628) | ~r2_hidden(A_626, k9_relat_1(C_628, B_627)) | ~v1_relat_1(C_628))), inference(cnfTransformation, [status(thm)], [f_65])).
% 8.10/2.84  tff(c_3180, plain, (![C_629, A_630, B_631]: (~v1_xboole_0(C_629) | ~r2_hidden(A_630, k9_relat_1(C_629, B_631)) | ~v1_relat_1(C_629))), inference(resolution, [status(thm)], [c_3124, c_2])).
% 8.10/2.84  tff(c_3187, plain, (~v1_xboole_0('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_2989, c_3180])).
% 8.10/2.84  tff(c_3208, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_89, c_2875, c_3187])).
% 8.10/2.84  tff(c_3211, plain, (![A_632]: (r2_hidden(A_632, k2_zfmisc_1('#skF_5', '#skF_3')) | ~m1_subset_1(A_632, '#skF_6'))), inference(splitRight, [status(thm)], [c_2874])).
% 8.10/2.84  tff(c_3239, plain, (![A_5, B_6]: (r2_hidden(A_5, '#skF_5') | ~m1_subset_1(k4_tarski(A_5, B_6), '#skF_6'))), inference(resolution, [status(thm)], [c_3211, c_10])).
% 8.10/2.84  tff(c_3924, plain, (![A_760, B_761]: (r2_hidden('#skF_2'(A_760, B_761, '#skF_6'), '#skF_5') | ~r2_hidden(A_760, k9_relat_1('#skF_6', B_761)) | ~v1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_3874, c_3239])).
% 8.10/2.84  tff(c_4022, plain, (![A_770, B_771]: (r2_hidden('#skF_2'(A_770, B_771, '#skF_6'), '#skF_5') | ~r2_hidden(A_770, k9_relat_1('#skF_6', B_771)))), inference(demodulation, [status(thm), theory('equality')], [c_89, c_3924])).
% 8.10/2.84  tff(c_4037, plain, (![A_772, B_773]: (m1_subset_1('#skF_2'(A_772, B_773, '#skF_6'), '#skF_5') | ~r2_hidden(A_772, k9_relat_1('#skF_6', B_773)))), inference(resolution, [status(thm)], [c_4022, c_14])).
% 8.10/2.84  tff(c_4062, plain, (m1_subset_1('#skF_2'('#skF_7', '#skF_4', '#skF_6'), '#skF_5')), inference(resolution, [status(thm)], [c_3468, c_4037])).
% 8.10/2.84  tff(c_2795, plain, (~m1_subset_1('#skF_8', '#skF_5')), inference(splitRight, [status(thm)], [c_58])).
% 8.10/2.84  tff(c_56, plain, (![F_121]: (~r2_hidden(F_121, '#skF_4') | ~r2_hidden(k4_tarski(F_121, '#skF_7'), '#skF_6') | ~m1_subset_1(F_121, '#skF_5') | m1_subset_1('#skF_8', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_108])).
% 8.10/2.84  tff(c_2855, plain, (![F_121]: (~r2_hidden(F_121, '#skF_4') | ~r2_hidden(k4_tarski(F_121, '#skF_7'), '#skF_6') | ~m1_subset_1(F_121, '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_2795, c_56])).
% 8.10/2.84  tff(c_3539, plain, (![B_703]: (~r2_hidden('#skF_2'('#skF_7', B_703, '#skF_6'), '#skF_4') | ~m1_subset_1('#skF_2'('#skF_7', B_703, '#skF_6'), '#skF_5') | ~r2_hidden('#skF_7', k9_relat_1('#skF_6', B_703)) | ~v1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_3520, c_2855])).
% 8.10/2.84  tff(c_4703, plain, (![B_843]: (~r2_hidden('#skF_2'('#skF_7', B_843, '#skF_6'), '#skF_4') | ~m1_subset_1('#skF_2'('#skF_7', B_843, '#skF_6'), '#skF_5') | ~r2_hidden('#skF_7', k9_relat_1('#skF_6', B_843)))), inference(demodulation, [status(thm), theory('equality')], [c_89, c_3539])).
% 8.10/2.84  tff(c_4711, plain, (~m1_subset_1('#skF_2'('#skF_7', '#skF_4', '#skF_6'), '#skF_5') | ~r2_hidden('#skF_7', k9_relat_1('#skF_6', '#skF_4')) | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_20, c_4703])).
% 8.10/2.84  tff(c_4721, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_89, c_3468, c_4062, c_4711])).
% 8.10/2.84  tff(c_4722, plain, (r2_hidden('#skF_7', k7_relset_1('#skF_5', '#skF_3', '#skF_6', '#skF_4'))), inference(splitRight, [status(thm)], [c_50])).
% 8.10/2.84  tff(c_7239, plain, (r2_hidden('#skF_7', k9_relat_1('#skF_6', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_7235, c_4722])).
% 8.10/2.84  tff(c_7291, plain, (![A_1288, B_1289, C_1290]: (r2_hidden(k4_tarski('#skF_2'(A_1288, B_1289, C_1290), A_1288), C_1290) | ~r2_hidden(A_1288, k9_relat_1(C_1290, B_1289)) | ~v1_relat_1(C_1290))), inference(cnfTransformation, [status(thm)], [f_65])).
% 8.10/2.84  tff(c_7627, plain, (![A_1349, B_1350, C_1351]: (m1_subset_1(k4_tarski('#skF_2'(A_1349, B_1350, C_1351), A_1349), C_1351) | ~r2_hidden(A_1349, k9_relat_1(C_1351, B_1350)) | ~v1_relat_1(C_1351))), inference(resolution, [status(thm)], [c_7291, c_14])).
% 8.10/2.84  tff(c_4758, plain, (![C_849, A_850, B_851]: (r2_hidden(C_849, A_850) | ~r2_hidden(C_849, B_851) | ~m1_subset_1(B_851, k1_zfmisc_1(A_850)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 8.10/2.84  tff(c_6613, plain, (![A_1149, A_1150, B_1151]: (r2_hidden(A_1149, A_1150) | ~m1_subset_1(B_1151, k1_zfmisc_1(A_1150)) | v1_xboole_0(B_1151) | ~m1_subset_1(A_1149, B_1151))), inference(resolution, [status(thm)], [c_16, c_4758])).
% 8.10/2.84  tff(c_6624, plain, (![A_1149]: (r2_hidden(A_1149, k2_zfmisc_1('#skF_5', '#skF_3')) | v1_xboole_0('#skF_6') | ~m1_subset_1(A_1149, '#skF_6'))), inference(resolution, [status(thm)], [c_36, c_6613])).
% 8.10/2.84  tff(c_6625, plain, (v1_xboole_0('#skF_6')), inference(splitLeft, [status(thm)], [c_6624])).
% 8.10/2.84  tff(c_6822, plain, (![A_1208, B_1209, C_1210, D_1211]: (k7_relset_1(A_1208, B_1209, C_1210, D_1211)=k9_relat_1(C_1210, D_1211) | ~m1_subset_1(C_1210, k1_zfmisc_1(k2_zfmisc_1(A_1208, B_1209))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 8.10/2.84  tff(c_6833, plain, (![D_1211]: (k7_relset_1('#skF_5', '#skF_3', '#skF_6', D_1211)=k9_relat_1('#skF_6', D_1211))), inference(resolution, [status(thm)], [c_36, c_6822])).
% 8.10/2.84  tff(c_6837, plain, (r2_hidden('#skF_7', k9_relat_1('#skF_6', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_6833, c_4722])).
% 8.10/2.84  tff(c_6890, plain, (![A_1214, B_1215, C_1216]: (r2_hidden(k4_tarski('#skF_2'(A_1214, B_1215, C_1216), A_1214), C_1216) | ~r2_hidden(A_1214, k9_relat_1(C_1216, B_1215)) | ~v1_relat_1(C_1216))), inference(cnfTransformation, [status(thm)], [f_65])).
% 8.10/2.84  tff(c_6946, plain, (![C_1217, A_1218, B_1219]: (~v1_xboole_0(C_1217) | ~r2_hidden(A_1218, k9_relat_1(C_1217, B_1219)) | ~v1_relat_1(C_1217))), inference(resolution, [status(thm)], [c_6890, c_2])).
% 8.10/2.84  tff(c_6953, plain, (~v1_xboole_0('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_6837, c_6946])).
% 8.10/2.84  tff(c_6974, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4757, c_6625, c_6953])).
% 8.10/2.84  tff(c_6977, plain, (![A_1220]: (r2_hidden(A_1220, k2_zfmisc_1('#skF_5', '#skF_3')) | ~m1_subset_1(A_1220, '#skF_6'))), inference(splitRight, [status(thm)], [c_6624])).
% 8.10/2.84  tff(c_7005, plain, (![A_5, B_6]: (r2_hidden(A_5, '#skF_5') | ~m1_subset_1(k4_tarski(A_5, B_6), '#skF_6'))), inference(resolution, [status(thm)], [c_6977, c_10])).
% 8.10/2.84  tff(c_7673, plain, (![A_1349, B_1350]: (r2_hidden('#skF_2'(A_1349, B_1350, '#skF_6'), '#skF_5') | ~r2_hidden(A_1349, k9_relat_1('#skF_6', B_1350)) | ~v1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_7627, c_7005])).
% 8.10/2.84  tff(c_7775, plain, (![A_1358, B_1359]: (r2_hidden('#skF_2'(A_1358, B_1359, '#skF_6'), '#skF_5') | ~r2_hidden(A_1358, k9_relat_1('#skF_6', B_1359)))), inference(demodulation, [status(thm), theory('equality')], [c_4757, c_7673])).
% 8.10/2.84  tff(c_7790, plain, (![A_1360, B_1361]: (m1_subset_1('#skF_2'(A_1360, B_1361, '#skF_6'), '#skF_5') | ~r2_hidden(A_1360, k9_relat_1('#skF_6', B_1361)))), inference(resolution, [status(thm)], [c_7775, c_14])).
% 8.10/2.84  tff(c_7815, plain, (m1_subset_1('#skF_2'('#skF_7', '#skF_4', '#skF_6'), '#skF_5')), inference(resolution, [status(thm)], [c_7239, c_7790])).
% 8.10/2.84  tff(c_4723, plain, (~r2_hidden('#skF_8', '#skF_4')), inference(splitRight, [status(thm)], [c_50])).
% 8.10/2.84  tff(c_48, plain, (![F_121]: (~r2_hidden(F_121, '#skF_4') | ~r2_hidden(k4_tarski(F_121, '#skF_7'), '#skF_6') | ~m1_subset_1(F_121, '#skF_5') | r2_hidden('#skF_8', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_108])).
% 8.10/2.84  tff(c_7009, plain, (![F_121]: (~r2_hidden(F_121, '#skF_4') | ~r2_hidden(k4_tarski(F_121, '#skF_7'), '#skF_6') | ~m1_subset_1(F_121, '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_4723, c_48])).
% 8.10/2.84  tff(c_7310, plain, (![B_1289]: (~r2_hidden('#skF_2'('#skF_7', B_1289, '#skF_6'), '#skF_4') | ~m1_subset_1('#skF_2'('#skF_7', B_1289, '#skF_6'), '#skF_5') | ~r2_hidden('#skF_7', k9_relat_1('#skF_6', B_1289)) | ~v1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_7291, c_7009])).
% 8.10/2.84  tff(c_8518, plain, (![B_1437]: (~r2_hidden('#skF_2'('#skF_7', B_1437, '#skF_6'), '#skF_4') | ~m1_subset_1('#skF_2'('#skF_7', B_1437, '#skF_6'), '#skF_5') | ~r2_hidden('#skF_7', k9_relat_1('#skF_6', B_1437)))), inference(demodulation, [status(thm), theory('equality')], [c_4757, c_7310])).
% 8.10/2.84  tff(c_8526, plain, (~m1_subset_1('#skF_2'('#skF_7', '#skF_4', '#skF_6'), '#skF_5') | ~r2_hidden('#skF_7', k9_relat_1('#skF_6', '#skF_4')) | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_20, c_8518])).
% 8.10/2.84  tff(c_8536, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4757, c_7239, c_7815, c_8526])).
% 8.10/2.84  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.10/2.84  
% 8.10/2.84  Inference rules
% 8.10/2.84  ----------------------
% 8.10/2.84  #Ref     : 0
% 8.10/2.84  #Sup     : 1801
% 8.10/2.84  #Fact    : 0
% 8.10/2.84  #Define  : 0
% 8.10/2.84  #Split   : 43
% 8.10/2.84  #Chain   : 0
% 8.10/2.84  #Close   : 0
% 8.10/2.84  
% 8.10/2.84  Ordering : KBO
% 8.10/2.84  
% 8.10/2.84  Simplification rules
% 8.10/2.84  ----------------------
% 8.10/2.84  #Subsume      : 190
% 8.10/2.84  #Demod        : 195
% 8.10/2.84  #Tautology    : 84
% 8.10/2.84  #SimpNegUnit  : 34
% 8.10/2.84  #BackRed      : 32
% 8.10/2.84  
% 8.10/2.84  #Partial instantiations: 0
% 8.10/2.84  #Strategies tried      : 1
% 8.10/2.84  
% 8.10/2.84  Timing (in seconds)
% 8.10/2.84  ----------------------
% 8.10/2.85  Preprocessing        : 0.33
% 8.10/2.85  Parsing              : 0.18
% 8.10/2.85  CNF conversion       : 0.03
% 8.10/2.85  Main loop            : 1.64
% 8.10/2.85  Inferencing          : 0.62
% 8.10/2.85  Reduction            : 0.40
% 8.10/2.85  Demodulation         : 0.25
% 8.10/2.85  BG Simplification    : 0.06
% 8.10/2.85  Subsumption          : 0.41
% 8.10/2.85  Abstraction          : 0.07
% 8.10/2.85  MUC search           : 0.00
% 8.10/2.85  Cooper               : 0.00
% 8.32/2.85  Total                : 2.05
% 8.32/2.85  Index Insertion      : 0.00
% 8.32/2.85  Index Deletion       : 0.00
% 8.32/2.85  Index Matching       : 0.00
% 8.32/2.85  BG Taut test         : 0.00
%------------------------------------------------------------------------------
