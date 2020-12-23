%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:38 EST 2020

% Result     : Theorem 4.13s
% Output     : CNFRefutation 4.73s
% Verified   : 
% Statistics : Number of formulae       :  146 ( 370 expanded)
%              Number of leaves         :   35 ( 137 expanded)
%              Depth                    :    9
%              Number of atoms          :  270 (1059 expanded)
%              Number of equality atoms :   14 (  28 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k8_relset_1 > k4_tarski > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > #skF_1 > #skF_11 > #skF_7 > #skF_10 > #skF_6 > #skF_5 > #skF_2 > #skF_9 > #skF_4 > #skF_8 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

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

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_76,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_118,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ~ v1_xboole_0(B)
           => ! [C] :
                ( ~ v1_xboole_0(C)
               => ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C)))
                   => ! [E] :
                        ( m1_subset_1(E,A)
                       => ( r2_hidden(E,k8_relset_1(A,C,D,B))
                        <=> ? [F] :
                              ( m1_subset_1(F,C)
                              & r2_hidden(k4_tarski(E,F),D)
                              & r2_hidden(F,B) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_relset_1)).

tff(f_61,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_87,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k10_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k2_relat_1(C))
            & r2_hidden(k4_tarski(A,D),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_relat_1)).

tff(f_91,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_74,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( C = k10_relat_1(A,B)
        <=> ! [D] :
              ( r2_hidden(D,C)
            <=> ? [E] :
                  ( r2_hidden(k4_tarski(D,E),A)
                  & r2_hidden(E,B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d14_relat_1)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_31,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(c_36,plain,(
    ! [A_60,B_61] : v1_relat_1(k2_zfmisc_1(A_60,B_61)) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_50,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_8'))) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_80,plain,(
    ! [B_167,A_168] :
      ( v1_relat_1(B_167)
      | ~ m1_subset_1(B_167,k1_zfmisc_1(A_168))
      | ~ v1_relat_1(A_168) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_83,plain,
    ( v1_relat_1('#skF_9')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_6','#skF_8')) ),
    inference(resolution,[status(thm)],[c_50,c_80])).

tff(c_86,plain,(
    v1_relat_1('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_83])).

tff(c_2372,plain,(
    ! [A_649,B_650,C_651] :
      ( r2_hidden(k4_tarski(A_649,'#skF_5'(A_649,B_650,C_651)),C_651)
      | ~ r2_hidden(A_649,k10_relat_1(C_651,B_650))
      | ~ v1_relat_1(C_651) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_1627,plain,(
    ! [A_497,B_498,C_499,D_500] :
      ( k8_relset_1(A_497,B_498,C_499,D_500) = k10_relat_1(C_499,D_500)
      | ~ m1_subset_1(C_499,k1_zfmisc_1(k2_zfmisc_1(A_497,B_498))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_1630,plain,(
    ! [D_500] : k8_relset_1('#skF_6','#skF_8','#skF_9',D_500) = k10_relat_1('#skF_9',D_500) ),
    inference(resolution,[status(thm)],[c_50,c_1627])).

tff(c_1523,plain,(
    ! [A_469,B_470,C_471] :
      ( r2_hidden(k4_tarski(A_469,'#skF_5'(A_469,B_470,C_471)),C_471)
      | ~ r2_hidden(A_469,k10_relat_1(C_471,B_470))
      | ~ v1_relat_1(C_471) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_892,plain,(
    ! [A_334,B_335,C_336,D_337] :
      ( k8_relset_1(A_334,B_335,C_336,D_337) = k10_relat_1(C_336,D_337)
      | ~ m1_subset_1(C_336,k1_zfmisc_1(k2_zfmisc_1(A_334,B_335))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_895,plain,(
    ! [D_337] : k8_relset_1('#skF_6','#skF_8','#skF_9',D_337) = k10_relat_1('#skF_9',D_337) ),
    inference(resolution,[status(thm)],[c_50,c_892])).

tff(c_383,plain,(
    ! [A_244,B_245,C_246,D_247] :
      ( k8_relset_1(A_244,B_245,C_246,D_247) = k10_relat_1(C_246,D_247)
      | ~ m1_subset_1(C_246,k1_zfmisc_1(k2_zfmisc_1(A_244,B_245))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_386,plain,(
    ! [D_247] : k8_relset_1('#skF_6','#skF_8','#skF_9',D_247) = k10_relat_1('#skF_9',D_247) ),
    inference(resolution,[status(thm)],[c_50,c_383])).

tff(c_72,plain,
    ( r2_hidden('#skF_10',k8_relset_1('#skF_6','#skF_8','#skF_9','#skF_7'))
    | m1_subset_1('#skF_11','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_87,plain,(
    m1_subset_1('#skF_11','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_72])).

tff(c_64,plain,
    ( r2_hidden('#skF_10',k8_relset_1('#skF_6','#skF_8','#skF_9','#skF_7'))
    | r2_hidden('#skF_11','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_108,plain,(
    r2_hidden('#skF_11','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_68,plain,
    ( r2_hidden('#skF_10',k8_relset_1('#skF_6','#skF_8','#skF_9','#skF_7'))
    | r2_hidden(k4_tarski('#skF_10','#skF_11'),'#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_113,plain,(
    r2_hidden(k4_tarski('#skF_10','#skF_11'),'#skF_9') ),
    inference(splitLeft,[status(thm)],[c_68])).

tff(c_178,plain,(
    ! [D_210,A_211,B_212,E_213] :
      ( r2_hidden(D_210,k10_relat_1(A_211,B_212))
      | ~ r2_hidden(E_213,B_212)
      | ~ r2_hidden(k4_tarski(D_210,E_213),A_211)
      | ~ v1_relat_1(A_211) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_216,plain,(
    ! [D_216,A_217] :
      ( r2_hidden(D_216,k10_relat_1(A_217,'#skF_7'))
      | ~ r2_hidden(k4_tarski(D_216,'#skF_11'),A_217)
      | ~ v1_relat_1(A_217) ) ),
    inference(resolution,[status(thm)],[c_108,c_178])).

tff(c_223,plain,
    ( r2_hidden('#skF_10',k10_relat_1('#skF_9','#skF_7'))
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_113,c_216])).

tff(c_233,plain,(
    r2_hidden('#skF_10',k10_relat_1('#skF_9','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_223])).

tff(c_147,plain,(
    ! [A_198,B_199,C_200,D_201] :
      ( k8_relset_1(A_198,B_199,C_200,D_201) = k10_relat_1(C_200,D_201)
      | ~ m1_subset_1(C_200,k1_zfmisc_1(k2_zfmisc_1(A_198,B_199))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_150,plain,(
    ! [D_201] : k8_relset_1('#skF_6','#skF_8','#skF_9',D_201) = k10_relat_1('#skF_9',D_201) ),
    inference(resolution,[status(thm)],[c_50,c_147])).

tff(c_58,plain,(
    ! [F_160] :
      ( ~ r2_hidden(F_160,'#skF_7')
      | ~ r2_hidden(k4_tarski('#skF_10',F_160),'#skF_9')
      | ~ m1_subset_1(F_160,'#skF_8')
      | ~ r2_hidden('#skF_10',k8_relset_1('#skF_6','#skF_8','#skF_9','#skF_7')) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_325,plain,(
    ! [F_229] :
      ( ~ r2_hidden(F_229,'#skF_7')
      | ~ r2_hidden(k4_tarski('#skF_10',F_229),'#skF_9')
      | ~ m1_subset_1(F_229,'#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_233,c_150,c_58])).

tff(c_332,plain,
    ( ~ r2_hidden('#skF_11','#skF_7')
    | ~ m1_subset_1('#skF_11','#skF_8') ),
    inference(resolution,[status(thm)],[c_113,c_325])).

tff(c_342,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_108,c_332])).

tff(c_343,plain,(
    r2_hidden('#skF_10',k8_relset_1('#skF_6','#skF_8','#skF_9','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_388,plain,(
    r2_hidden('#skF_10',k10_relat_1('#skF_9','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_386,c_343])).

tff(c_565,plain,(
    ! [A_289,B_290,C_291] :
      ( r2_hidden(k4_tarski(A_289,'#skF_5'(A_289,B_290,C_291)),C_291)
      | ~ r2_hidden(A_289,k10_relat_1(C_291,B_290))
      | ~ v1_relat_1(C_291) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_88,plain,(
    ! [C_169,B_170,A_171] :
      ( ~ v1_xboole_0(C_169)
      | ~ m1_subset_1(B_170,k1_zfmisc_1(C_169))
      | ~ r2_hidden(A_171,B_170) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_91,plain,(
    ! [A_171] :
      ( ~ v1_xboole_0(k2_zfmisc_1('#skF_6','#skF_8'))
      | ~ r2_hidden(A_171,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_50,c_88])).

tff(c_92,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_6','#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_91])).

tff(c_98,plain,(
    ! [A_176,C_177,B_178] :
      ( m1_subset_1(A_176,C_177)
      | ~ m1_subset_1(B_178,k1_zfmisc_1(C_177))
      | ~ r2_hidden(A_176,B_178) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_101,plain,(
    ! [A_176] :
      ( m1_subset_1(A_176,k2_zfmisc_1('#skF_6','#skF_8'))
      | ~ r2_hidden(A_176,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_50,c_98])).

tff(c_10,plain,(
    ! [A_7,B_8] :
      ( r2_hidden(A_7,B_8)
      | v1_xboole_0(B_8)
      | ~ m1_subset_1(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_103,plain,(
    ! [B_180,D_181,A_182,C_183] :
      ( r2_hidden(B_180,D_181)
      | ~ r2_hidden(k4_tarski(A_182,B_180),k2_zfmisc_1(C_183,D_181)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_439,plain,(
    ! [B_259,D_260,C_261,A_262] :
      ( r2_hidden(B_259,D_260)
      | v1_xboole_0(k2_zfmisc_1(C_261,D_260))
      | ~ m1_subset_1(k4_tarski(A_262,B_259),k2_zfmisc_1(C_261,D_260)) ) ),
    inference(resolution,[status(thm)],[c_10,c_103])).

tff(c_446,plain,(
    ! [B_259,A_262] :
      ( r2_hidden(B_259,'#skF_8')
      | v1_xboole_0(k2_zfmisc_1('#skF_6','#skF_8'))
      | ~ r2_hidden(k4_tarski(A_262,B_259),'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_101,c_439])).

tff(c_450,plain,(
    ! [B_259,A_262] :
      ( r2_hidden(B_259,'#skF_8')
      | ~ r2_hidden(k4_tarski(A_262,B_259),'#skF_9') ) ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_446])).

tff(c_571,plain,(
    ! [A_289,B_290] :
      ( r2_hidden('#skF_5'(A_289,B_290,'#skF_9'),'#skF_8')
      | ~ r2_hidden(A_289,k10_relat_1('#skF_9',B_290))
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_565,c_450])).

tff(c_694,plain,(
    ! [A_299,B_300] :
      ( r2_hidden('#skF_5'(A_299,B_300,'#skF_9'),'#skF_8')
      | ~ r2_hidden(A_299,k10_relat_1('#skF_9',B_300)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_571])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( m1_subset_1(A_5,B_6)
      | ~ r2_hidden(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_702,plain,(
    ! [A_301,B_302] :
      ( m1_subset_1('#skF_5'(A_301,B_302,'#skF_9'),'#skF_8')
      | ~ r2_hidden(A_301,k10_relat_1('#skF_9',B_302)) ) ),
    inference(resolution,[status(thm)],[c_694,c_8])).

tff(c_733,plain,(
    m1_subset_1('#skF_5'('#skF_10','#skF_7','#skF_9'),'#skF_8') ),
    inference(resolution,[status(thm)],[c_388,c_702])).

tff(c_40,plain,(
    ! [A_62,B_63,C_64] :
      ( r2_hidden('#skF_5'(A_62,B_63,C_64),B_63)
      | ~ r2_hidden(A_62,k10_relat_1(C_64,B_63))
      | ~ v1_relat_1(C_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_344,plain,(
    ~ r2_hidden(k4_tarski('#skF_10','#skF_11'),'#skF_9') ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_66,plain,(
    ! [F_160] :
      ( ~ r2_hidden(F_160,'#skF_7')
      | ~ r2_hidden(k4_tarski('#skF_10',F_160),'#skF_9')
      | ~ m1_subset_1(F_160,'#skF_8')
      | r2_hidden(k4_tarski('#skF_10','#skF_11'),'#skF_9') ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_431,plain,(
    ! [F_160] :
      ( ~ r2_hidden(F_160,'#skF_7')
      | ~ r2_hidden(k4_tarski('#skF_10',F_160),'#skF_9')
      | ~ m1_subset_1(F_160,'#skF_8') ) ),
    inference(negUnitSimplification,[status(thm)],[c_344,c_66])).

tff(c_575,plain,(
    ! [B_290] :
      ( ~ r2_hidden('#skF_5'('#skF_10',B_290,'#skF_9'),'#skF_7')
      | ~ m1_subset_1('#skF_5'('#skF_10',B_290,'#skF_9'),'#skF_8')
      | ~ r2_hidden('#skF_10',k10_relat_1('#skF_9',B_290))
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_565,c_431])).

tff(c_831,plain,(
    ! [B_317] :
      ( ~ r2_hidden('#skF_5'('#skF_10',B_317,'#skF_9'),'#skF_7')
      | ~ m1_subset_1('#skF_5'('#skF_10',B_317,'#skF_9'),'#skF_8')
      | ~ r2_hidden('#skF_10',k10_relat_1('#skF_9',B_317)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_575])).

tff(c_835,plain,
    ( ~ m1_subset_1('#skF_5'('#skF_10','#skF_7','#skF_9'),'#skF_8')
    | ~ r2_hidden('#skF_10',k10_relat_1('#skF_9','#skF_7'))
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_40,c_831])).

tff(c_842,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_388,c_733,c_835])).

tff(c_843,plain,(
    r2_hidden('#skF_10',k8_relset_1('#skF_6','#skF_8','#skF_9','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_897,plain,(
    r2_hidden('#skF_10',k10_relat_1('#skF_9','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_895,c_843])).

tff(c_42,plain,(
    ! [A_62,B_63,C_64] :
      ( r2_hidden(k4_tarski(A_62,'#skF_5'(A_62,B_63,C_64)),C_64)
      | ~ r2_hidden(A_62,k10_relat_1(C_64,B_63))
      | ~ v1_relat_1(C_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_941,plain,(
    ! [B_348,D_349,C_350,A_351] :
      ( r2_hidden(B_348,D_349)
      | v1_xboole_0(k2_zfmisc_1(C_350,D_349))
      | ~ m1_subset_1(k4_tarski(A_351,B_348),k2_zfmisc_1(C_350,D_349)) ) ),
    inference(resolution,[status(thm)],[c_10,c_103])).

tff(c_948,plain,(
    ! [B_348,A_351] :
      ( r2_hidden(B_348,'#skF_8')
      | v1_xboole_0(k2_zfmisc_1('#skF_6','#skF_8'))
      | ~ r2_hidden(k4_tarski(A_351,B_348),'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_101,c_941])).

tff(c_990,plain,(
    ! [B_355,A_356] :
      ( r2_hidden(B_355,'#skF_8')
      | ~ r2_hidden(k4_tarski(A_356,B_355),'#skF_9') ) ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_948])).

tff(c_994,plain,(
    ! [A_62,B_63] :
      ( r2_hidden('#skF_5'(A_62,B_63,'#skF_9'),'#skF_8')
      | ~ r2_hidden(A_62,k10_relat_1('#skF_9',B_63))
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_42,c_990])).

tff(c_1046,plain,(
    ! [A_363,B_364] :
      ( r2_hidden('#skF_5'(A_363,B_364,'#skF_9'),'#skF_8')
      | ~ r2_hidden(A_363,k10_relat_1('#skF_9',B_364)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_994])).

tff(c_1051,plain,(
    ! [A_365,B_366] :
      ( m1_subset_1('#skF_5'(A_365,B_366,'#skF_9'),'#skF_8')
      | ~ r2_hidden(A_365,k10_relat_1('#skF_9',B_366)) ) ),
    inference(resolution,[status(thm)],[c_1046,c_8])).

tff(c_1068,plain,(
    m1_subset_1('#skF_5'('#skF_10','#skF_7','#skF_9'),'#skF_8') ),
    inference(resolution,[status(thm)],[c_897,c_1051])).

tff(c_953,plain,(
    ! [A_352,B_353,C_354] :
      ( r2_hidden(k4_tarski(A_352,'#skF_5'(A_352,B_353,C_354)),C_354)
      | ~ r2_hidden(A_352,k10_relat_1(C_354,B_353))
      | ~ v1_relat_1(C_354) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_844,plain,(
    ~ r2_hidden('#skF_11','#skF_7') ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_62,plain,(
    ! [F_160] :
      ( ~ r2_hidden(F_160,'#skF_7')
      | ~ r2_hidden(k4_tarski('#skF_10',F_160),'#skF_9')
      | ~ m1_subset_1(F_160,'#skF_8')
      | r2_hidden('#skF_11','#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_884,plain,(
    ! [F_160] :
      ( ~ r2_hidden(F_160,'#skF_7')
      | ~ r2_hidden(k4_tarski('#skF_10',F_160),'#skF_9')
      | ~ m1_subset_1(F_160,'#skF_8') ) ),
    inference(negUnitSimplification,[status(thm)],[c_844,c_62])).

tff(c_961,plain,(
    ! [B_353] :
      ( ~ r2_hidden('#skF_5'('#skF_10',B_353,'#skF_9'),'#skF_7')
      | ~ m1_subset_1('#skF_5'('#skF_10',B_353,'#skF_9'),'#skF_8')
      | ~ r2_hidden('#skF_10',k10_relat_1('#skF_9',B_353))
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_953,c_884])).

tff(c_1326,plain,(
    ! [B_403] :
      ( ~ r2_hidden('#skF_5'('#skF_10',B_403,'#skF_9'),'#skF_7')
      | ~ m1_subset_1('#skF_5'('#skF_10',B_403,'#skF_9'),'#skF_8')
      | ~ r2_hidden('#skF_10',k10_relat_1('#skF_9',B_403)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_961])).

tff(c_1330,plain,
    ( ~ m1_subset_1('#skF_5'('#skF_10','#skF_7','#skF_9'),'#skF_8')
    | ~ r2_hidden('#skF_10',k10_relat_1('#skF_9','#skF_7'))
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_40,c_1326])).

tff(c_1337,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_897,c_1068,c_1330])).

tff(c_1338,plain,(
    ! [A_171] : ~ r2_hidden(A_171,'#skF_9') ),
    inference(splitRight,[status(thm)],[c_91])).

tff(c_1548,plain,(
    ! [A_469,B_470] :
      ( ~ r2_hidden(A_469,k10_relat_1('#skF_9',B_470))
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_1523,c_1338])).

tff(c_1564,plain,(
    ! [A_469,B_470] : ~ r2_hidden(A_469,k10_relat_1('#skF_9',B_470)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_1548])).

tff(c_1435,plain,(
    ! [A_441,B_442,C_443,D_444] :
      ( k8_relset_1(A_441,B_442,C_443,D_444) = k10_relat_1(C_443,D_444)
      | ~ m1_subset_1(C_443,k1_zfmisc_1(k2_zfmisc_1(A_441,B_442))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_1438,plain,(
    ! [D_444] : k8_relset_1('#skF_6','#skF_8','#skF_9',D_444) = k10_relat_1('#skF_9',D_444) ),
    inference(resolution,[status(thm)],[c_50,c_1435])).

tff(c_1362,plain,(
    r2_hidden('#skF_10',k8_relset_1('#skF_6','#skF_8','#skF_9','#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_1338,c_68])).

tff(c_1440,plain,(
    r2_hidden('#skF_10',k10_relat_1('#skF_9','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1438,c_1362])).

tff(c_1567,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1564,c_1440])).

tff(c_1568,plain,(
    r2_hidden('#skF_10',k8_relset_1('#skF_6','#skF_8','#skF_9','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_1632,plain,(
    r2_hidden('#skF_10',k10_relat_1('#skF_9','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1630,c_1568])).

tff(c_1704,plain,(
    ! [A_526,B_527,C_528] :
      ( r2_hidden(k4_tarski(A_526,'#skF_5'(A_526,B_527,C_528)),C_528)
      | ~ r2_hidden(A_526,k10_relat_1(C_528,B_527))
      | ~ v1_relat_1(C_528) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_1579,plain,(
    ! [C_472,B_473,A_474] :
      ( ~ v1_xboole_0(C_472)
      | ~ m1_subset_1(B_473,k1_zfmisc_1(C_472))
      | ~ r2_hidden(A_474,B_473) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_1582,plain,(
    ! [A_474] :
      ( ~ v1_xboole_0(k2_zfmisc_1('#skF_6','#skF_8'))
      | ~ r2_hidden(A_474,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_50,c_1579])).

tff(c_1587,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_6','#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_1582])).

tff(c_1583,plain,(
    ! [A_475,C_476,B_477] :
      ( m1_subset_1(A_475,C_476)
      | ~ m1_subset_1(B_477,k1_zfmisc_1(C_476))
      | ~ r2_hidden(A_475,B_477) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1586,plain,(
    ! [A_475] :
      ( m1_subset_1(A_475,k2_zfmisc_1('#skF_6','#skF_8'))
      | ~ r2_hidden(A_475,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_50,c_1583])).

tff(c_1590,plain,(
    ! [B_479,D_480,A_481,C_482] :
      ( r2_hidden(B_479,D_480)
      | ~ r2_hidden(k4_tarski(A_481,B_479),k2_zfmisc_1(C_482,D_480)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1686,plain,(
    ! [B_520,D_521,C_522,A_523] :
      ( r2_hidden(B_520,D_521)
      | v1_xboole_0(k2_zfmisc_1(C_522,D_521))
      | ~ m1_subset_1(k4_tarski(A_523,B_520),k2_zfmisc_1(C_522,D_521)) ) ),
    inference(resolution,[status(thm)],[c_10,c_1590])).

tff(c_1693,plain,(
    ! [B_520,A_523] :
      ( r2_hidden(B_520,'#skF_8')
      | v1_xboole_0(k2_zfmisc_1('#skF_6','#skF_8'))
      | ~ r2_hidden(k4_tarski(A_523,B_520),'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_1586,c_1686])).

tff(c_1697,plain,(
    ! [B_520,A_523] :
      ( r2_hidden(B_520,'#skF_8')
      | ~ r2_hidden(k4_tarski(A_523,B_520),'#skF_9') ) ),
    inference(negUnitSimplification,[status(thm)],[c_1587,c_1693])).

tff(c_1708,plain,(
    ! [A_526,B_527] :
      ( r2_hidden('#skF_5'(A_526,B_527,'#skF_9'),'#skF_8')
      | ~ r2_hidden(A_526,k10_relat_1('#skF_9',B_527))
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_1704,c_1697])).

tff(c_1816,plain,(
    ! [A_539,B_540] :
      ( r2_hidden('#skF_5'(A_539,B_540,'#skF_9'),'#skF_8')
      | ~ r2_hidden(A_539,k10_relat_1('#skF_9',B_540)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_1708])).

tff(c_1824,plain,(
    ! [A_541,B_542] :
      ( m1_subset_1('#skF_5'(A_541,B_542,'#skF_9'),'#skF_8')
      | ~ r2_hidden(A_541,k10_relat_1('#skF_9',B_542)) ) ),
    inference(resolution,[status(thm)],[c_1816,c_8])).

tff(c_1841,plain,(
    m1_subset_1('#skF_5'('#skF_10','#skF_7','#skF_9'),'#skF_8') ),
    inference(resolution,[status(thm)],[c_1632,c_1824])).

tff(c_1569,plain,(
    ~ m1_subset_1('#skF_11','#skF_8') ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_70,plain,(
    ! [F_160] :
      ( ~ r2_hidden(F_160,'#skF_7')
      | ~ r2_hidden(k4_tarski('#skF_10',F_160),'#skF_9')
      | ~ m1_subset_1(F_160,'#skF_8')
      | m1_subset_1('#skF_11','#skF_8') ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_1652,plain,(
    ! [F_160] :
      ( ~ r2_hidden(F_160,'#skF_7')
      | ~ r2_hidden(k4_tarski('#skF_10',F_160),'#skF_9')
      | ~ m1_subset_1(F_160,'#skF_8') ) ),
    inference(negUnitSimplification,[status(thm)],[c_1569,c_70])).

tff(c_1716,plain,(
    ! [B_527] :
      ( ~ r2_hidden('#skF_5'('#skF_10',B_527,'#skF_9'),'#skF_7')
      | ~ m1_subset_1('#skF_5'('#skF_10',B_527,'#skF_9'),'#skF_8')
      | ~ r2_hidden('#skF_10',k10_relat_1('#skF_9',B_527))
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_1704,c_1652])).

tff(c_2152,plain,(
    ! [B_580] :
      ( ~ r2_hidden('#skF_5'('#skF_10',B_580,'#skF_9'),'#skF_7')
      | ~ m1_subset_1('#skF_5'('#skF_10',B_580,'#skF_9'),'#skF_8')
      | ~ r2_hidden('#skF_10',k10_relat_1('#skF_9',B_580)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_1716])).

tff(c_2156,plain,
    ( ~ m1_subset_1('#skF_5'('#skF_10','#skF_7','#skF_9'),'#skF_8')
    | ~ r2_hidden('#skF_10',k10_relat_1('#skF_9','#skF_7'))
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_40,c_2152])).

tff(c_2163,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_1632,c_1841,c_2156])).

tff(c_2164,plain,(
    ! [A_474] : ~ r2_hidden(A_474,'#skF_9') ),
    inference(splitRight,[status(thm)],[c_1582])).

tff(c_2397,plain,(
    ! [A_649,B_650] :
      ( ~ r2_hidden(A_649,k10_relat_1('#skF_9',B_650))
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_2372,c_2164])).

tff(c_2413,plain,(
    ! [A_649,B_650] : ~ r2_hidden(A_649,k10_relat_1('#skF_9',B_650)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_2397])).

tff(c_2249,plain,(
    ! [A_615,B_616,C_617,D_618] :
      ( k8_relset_1(A_615,B_616,C_617,D_618) = k10_relat_1(C_617,D_618)
      | ~ m1_subset_1(C_617,k1_zfmisc_1(k2_zfmisc_1(A_615,B_616))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_2252,plain,(
    ! [D_618] : k8_relset_1('#skF_6','#skF_8','#skF_9',D_618) = k10_relat_1('#skF_9',D_618) ),
    inference(resolution,[status(thm)],[c_50,c_2249])).

tff(c_2255,plain,(
    r2_hidden('#skF_10',k10_relat_1('#skF_9','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2252,c_1568])).

tff(c_2416,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2413,c_2255])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:30:27 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.13/1.74  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.47/1.77  
% 4.47/1.77  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.55/1.78  %$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k8_relset_1 > k4_tarski > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > #skF_1 > #skF_11 > #skF_7 > #skF_10 > #skF_6 > #skF_5 > #skF_2 > #skF_9 > #skF_4 > #skF_8 > #skF_3
% 4.55/1.78  
% 4.55/1.78  %Foreground sorts:
% 4.55/1.78  
% 4.55/1.78  
% 4.55/1.78  %Background operators:
% 4.55/1.78  
% 4.55/1.78  
% 4.55/1.78  %Foreground operators:
% 4.55/1.78  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 4.55/1.78  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.55/1.78  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.55/1.78  tff('#skF_11', type, '#skF_11': $i).
% 4.55/1.78  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 4.55/1.78  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 4.55/1.78  tff('#skF_7', type, '#skF_7': $i).
% 4.55/1.78  tff('#skF_10', type, '#skF_10': $i).
% 4.55/1.78  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.55/1.78  tff('#skF_6', type, '#skF_6': $i).
% 4.55/1.78  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 4.55/1.78  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.55/1.78  tff('#skF_9', type, '#skF_9': $i).
% 4.55/1.78  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.55/1.78  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 4.55/1.78  tff('#skF_8', type, '#skF_8': $i).
% 4.55/1.78  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.55/1.78  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 4.55/1.78  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.55/1.78  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.55/1.78  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 4.55/1.78  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.55/1.78  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.55/1.78  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.55/1.78  
% 4.73/1.82  tff(f_76, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 4.73/1.82  tff(f_118, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (~v1_xboole_0(C) => (![D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C))) => (![E]: (m1_subset_1(E, A) => (r2_hidden(E, k8_relset_1(A, C, D, B)) <=> (?[F]: ((m1_subset_1(F, C) & r2_hidden(k4_tarski(E, F), D)) & r2_hidden(F, B)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t53_relset_1)).
% 4.73/1.82  tff(f_61, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 4.73/1.82  tff(f_87, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k10_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k2_relat_1(C)) & r2_hidden(k4_tarski(A, D), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t166_relat_1)).
% 4.73/1.82  tff(f_91, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 4.73/1.82  tff(f_74, axiom, (![A]: (v1_relat_1(A) => (![B, C]: ((C = k10_relat_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E]: (r2_hidden(k4_tarski(D, E), A) & r2_hidden(E, B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d14_relat_1)).
% 4.73/1.82  tff(f_54, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 4.73/1.82  tff(f_47, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 4.73/1.82  tff(f_41, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 4.73/1.82  tff(f_31, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 4.73/1.82  tff(f_35, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 4.73/1.82  tff(c_36, plain, (![A_60, B_61]: (v1_relat_1(k2_zfmisc_1(A_60, B_61)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.73/1.82  tff(c_50, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_8')))), inference(cnfTransformation, [status(thm)], [f_118])).
% 4.73/1.82  tff(c_80, plain, (![B_167, A_168]: (v1_relat_1(B_167) | ~m1_subset_1(B_167, k1_zfmisc_1(A_168)) | ~v1_relat_1(A_168))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.73/1.82  tff(c_83, plain, (v1_relat_1('#skF_9') | ~v1_relat_1(k2_zfmisc_1('#skF_6', '#skF_8'))), inference(resolution, [status(thm)], [c_50, c_80])).
% 4.73/1.82  tff(c_86, plain, (v1_relat_1('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_83])).
% 4.73/1.82  tff(c_2372, plain, (![A_649, B_650, C_651]: (r2_hidden(k4_tarski(A_649, '#skF_5'(A_649, B_650, C_651)), C_651) | ~r2_hidden(A_649, k10_relat_1(C_651, B_650)) | ~v1_relat_1(C_651))), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.73/1.82  tff(c_1627, plain, (![A_497, B_498, C_499, D_500]: (k8_relset_1(A_497, B_498, C_499, D_500)=k10_relat_1(C_499, D_500) | ~m1_subset_1(C_499, k1_zfmisc_1(k2_zfmisc_1(A_497, B_498))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.73/1.82  tff(c_1630, plain, (![D_500]: (k8_relset_1('#skF_6', '#skF_8', '#skF_9', D_500)=k10_relat_1('#skF_9', D_500))), inference(resolution, [status(thm)], [c_50, c_1627])).
% 4.73/1.82  tff(c_1523, plain, (![A_469, B_470, C_471]: (r2_hidden(k4_tarski(A_469, '#skF_5'(A_469, B_470, C_471)), C_471) | ~r2_hidden(A_469, k10_relat_1(C_471, B_470)) | ~v1_relat_1(C_471))), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.73/1.82  tff(c_892, plain, (![A_334, B_335, C_336, D_337]: (k8_relset_1(A_334, B_335, C_336, D_337)=k10_relat_1(C_336, D_337) | ~m1_subset_1(C_336, k1_zfmisc_1(k2_zfmisc_1(A_334, B_335))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.73/1.82  tff(c_895, plain, (![D_337]: (k8_relset_1('#skF_6', '#skF_8', '#skF_9', D_337)=k10_relat_1('#skF_9', D_337))), inference(resolution, [status(thm)], [c_50, c_892])).
% 4.73/1.82  tff(c_383, plain, (![A_244, B_245, C_246, D_247]: (k8_relset_1(A_244, B_245, C_246, D_247)=k10_relat_1(C_246, D_247) | ~m1_subset_1(C_246, k1_zfmisc_1(k2_zfmisc_1(A_244, B_245))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.73/1.82  tff(c_386, plain, (![D_247]: (k8_relset_1('#skF_6', '#skF_8', '#skF_9', D_247)=k10_relat_1('#skF_9', D_247))), inference(resolution, [status(thm)], [c_50, c_383])).
% 4.73/1.82  tff(c_72, plain, (r2_hidden('#skF_10', k8_relset_1('#skF_6', '#skF_8', '#skF_9', '#skF_7')) | m1_subset_1('#skF_11', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_118])).
% 4.73/1.82  tff(c_87, plain, (m1_subset_1('#skF_11', '#skF_8')), inference(splitLeft, [status(thm)], [c_72])).
% 4.73/1.82  tff(c_64, plain, (r2_hidden('#skF_10', k8_relset_1('#skF_6', '#skF_8', '#skF_9', '#skF_7')) | r2_hidden('#skF_11', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_118])).
% 4.73/1.82  tff(c_108, plain, (r2_hidden('#skF_11', '#skF_7')), inference(splitLeft, [status(thm)], [c_64])).
% 4.73/1.82  tff(c_68, plain, (r2_hidden('#skF_10', k8_relset_1('#skF_6', '#skF_8', '#skF_9', '#skF_7')) | r2_hidden(k4_tarski('#skF_10', '#skF_11'), '#skF_9')), inference(cnfTransformation, [status(thm)], [f_118])).
% 4.73/1.82  tff(c_113, plain, (r2_hidden(k4_tarski('#skF_10', '#skF_11'), '#skF_9')), inference(splitLeft, [status(thm)], [c_68])).
% 4.73/1.82  tff(c_178, plain, (![D_210, A_211, B_212, E_213]: (r2_hidden(D_210, k10_relat_1(A_211, B_212)) | ~r2_hidden(E_213, B_212) | ~r2_hidden(k4_tarski(D_210, E_213), A_211) | ~v1_relat_1(A_211))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.73/1.82  tff(c_216, plain, (![D_216, A_217]: (r2_hidden(D_216, k10_relat_1(A_217, '#skF_7')) | ~r2_hidden(k4_tarski(D_216, '#skF_11'), A_217) | ~v1_relat_1(A_217))), inference(resolution, [status(thm)], [c_108, c_178])).
% 4.73/1.82  tff(c_223, plain, (r2_hidden('#skF_10', k10_relat_1('#skF_9', '#skF_7')) | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_113, c_216])).
% 4.73/1.82  tff(c_233, plain, (r2_hidden('#skF_10', k10_relat_1('#skF_9', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_223])).
% 4.73/1.82  tff(c_147, plain, (![A_198, B_199, C_200, D_201]: (k8_relset_1(A_198, B_199, C_200, D_201)=k10_relat_1(C_200, D_201) | ~m1_subset_1(C_200, k1_zfmisc_1(k2_zfmisc_1(A_198, B_199))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.73/1.82  tff(c_150, plain, (![D_201]: (k8_relset_1('#skF_6', '#skF_8', '#skF_9', D_201)=k10_relat_1('#skF_9', D_201))), inference(resolution, [status(thm)], [c_50, c_147])).
% 4.73/1.82  tff(c_58, plain, (![F_160]: (~r2_hidden(F_160, '#skF_7') | ~r2_hidden(k4_tarski('#skF_10', F_160), '#skF_9') | ~m1_subset_1(F_160, '#skF_8') | ~r2_hidden('#skF_10', k8_relset_1('#skF_6', '#skF_8', '#skF_9', '#skF_7')))), inference(cnfTransformation, [status(thm)], [f_118])).
% 4.73/1.82  tff(c_325, plain, (![F_229]: (~r2_hidden(F_229, '#skF_7') | ~r2_hidden(k4_tarski('#skF_10', F_229), '#skF_9') | ~m1_subset_1(F_229, '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_233, c_150, c_58])).
% 4.73/1.82  tff(c_332, plain, (~r2_hidden('#skF_11', '#skF_7') | ~m1_subset_1('#skF_11', '#skF_8')), inference(resolution, [status(thm)], [c_113, c_325])).
% 4.73/1.82  tff(c_342, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_87, c_108, c_332])).
% 4.73/1.82  tff(c_343, plain, (r2_hidden('#skF_10', k8_relset_1('#skF_6', '#skF_8', '#skF_9', '#skF_7'))), inference(splitRight, [status(thm)], [c_68])).
% 4.73/1.82  tff(c_388, plain, (r2_hidden('#skF_10', k10_relat_1('#skF_9', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_386, c_343])).
% 4.73/1.82  tff(c_565, plain, (![A_289, B_290, C_291]: (r2_hidden(k4_tarski(A_289, '#skF_5'(A_289, B_290, C_291)), C_291) | ~r2_hidden(A_289, k10_relat_1(C_291, B_290)) | ~v1_relat_1(C_291))), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.73/1.82  tff(c_88, plain, (![C_169, B_170, A_171]: (~v1_xboole_0(C_169) | ~m1_subset_1(B_170, k1_zfmisc_1(C_169)) | ~r2_hidden(A_171, B_170))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.73/1.82  tff(c_91, plain, (![A_171]: (~v1_xboole_0(k2_zfmisc_1('#skF_6', '#skF_8')) | ~r2_hidden(A_171, '#skF_9'))), inference(resolution, [status(thm)], [c_50, c_88])).
% 4.73/1.82  tff(c_92, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_6', '#skF_8'))), inference(splitLeft, [status(thm)], [c_91])).
% 4.73/1.82  tff(c_98, plain, (![A_176, C_177, B_178]: (m1_subset_1(A_176, C_177) | ~m1_subset_1(B_178, k1_zfmisc_1(C_177)) | ~r2_hidden(A_176, B_178))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.73/1.82  tff(c_101, plain, (![A_176]: (m1_subset_1(A_176, k2_zfmisc_1('#skF_6', '#skF_8')) | ~r2_hidden(A_176, '#skF_9'))), inference(resolution, [status(thm)], [c_50, c_98])).
% 4.73/1.82  tff(c_10, plain, (![A_7, B_8]: (r2_hidden(A_7, B_8) | v1_xboole_0(B_8) | ~m1_subset_1(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.73/1.82  tff(c_103, plain, (![B_180, D_181, A_182, C_183]: (r2_hidden(B_180, D_181) | ~r2_hidden(k4_tarski(A_182, B_180), k2_zfmisc_1(C_183, D_181)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.73/1.82  tff(c_439, plain, (![B_259, D_260, C_261, A_262]: (r2_hidden(B_259, D_260) | v1_xboole_0(k2_zfmisc_1(C_261, D_260)) | ~m1_subset_1(k4_tarski(A_262, B_259), k2_zfmisc_1(C_261, D_260)))), inference(resolution, [status(thm)], [c_10, c_103])).
% 4.73/1.82  tff(c_446, plain, (![B_259, A_262]: (r2_hidden(B_259, '#skF_8') | v1_xboole_0(k2_zfmisc_1('#skF_6', '#skF_8')) | ~r2_hidden(k4_tarski(A_262, B_259), '#skF_9'))), inference(resolution, [status(thm)], [c_101, c_439])).
% 4.73/1.82  tff(c_450, plain, (![B_259, A_262]: (r2_hidden(B_259, '#skF_8') | ~r2_hidden(k4_tarski(A_262, B_259), '#skF_9'))), inference(negUnitSimplification, [status(thm)], [c_92, c_446])).
% 4.73/1.82  tff(c_571, plain, (![A_289, B_290]: (r2_hidden('#skF_5'(A_289, B_290, '#skF_9'), '#skF_8') | ~r2_hidden(A_289, k10_relat_1('#skF_9', B_290)) | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_565, c_450])).
% 4.73/1.82  tff(c_694, plain, (![A_299, B_300]: (r2_hidden('#skF_5'(A_299, B_300, '#skF_9'), '#skF_8') | ~r2_hidden(A_299, k10_relat_1('#skF_9', B_300)))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_571])).
% 4.73/1.82  tff(c_8, plain, (![A_5, B_6]: (m1_subset_1(A_5, B_6) | ~r2_hidden(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.73/1.82  tff(c_702, plain, (![A_301, B_302]: (m1_subset_1('#skF_5'(A_301, B_302, '#skF_9'), '#skF_8') | ~r2_hidden(A_301, k10_relat_1('#skF_9', B_302)))), inference(resolution, [status(thm)], [c_694, c_8])).
% 4.73/1.82  tff(c_733, plain, (m1_subset_1('#skF_5'('#skF_10', '#skF_7', '#skF_9'), '#skF_8')), inference(resolution, [status(thm)], [c_388, c_702])).
% 4.73/1.82  tff(c_40, plain, (![A_62, B_63, C_64]: (r2_hidden('#skF_5'(A_62, B_63, C_64), B_63) | ~r2_hidden(A_62, k10_relat_1(C_64, B_63)) | ~v1_relat_1(C_64))), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.73/1.82  tff(c_344, plain, (~r2_hidden(k4_tarski('#skF_10', '#skF_11'), '#skF_9')), inference(splitRight, [status(thm)], [c_68])).
% 4.73/1.82  tff(c_66, plain, (![F_160]: (~r2_hidden(F_160, '#skF_7') | ~r2_hidden(k4_tarski('#skF_10', F_160), '#skF_9') | ~m1_subset_1(F_160, '#skF_8') | r2_hidden(k4_tarski('#skF_10', '#skF_11'), '#skF_9'))), inference(cnfTransformation, [status(thm)], [f_118])).
% 4.73/1.82  tff(c_431, plain, (![F_160]: (~r2_hidden(F_160, '#skF_7') | ~r2_hidden(k4_tarski('#skF_10', F_160), '#skF_9') | ~m1_subset_1(F_160, '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_344, c_66])).
% 4.73/1.82  tff(c_575, plain, (![B_290]: (~r2_hidden('#skF_5'('#skF_10', B_290, '#skF_9'), '#skF_7') | ~m1_subset_1('#skF_5'('#skF_10', B_290, '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k10_relat_1('#skF_9', B_290)) | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_565, c_431])).
% 4.73/1.82  tff(c_831, plain, (![B_317]: (~r2_hidden('#skF_5'('#skF_10', B_317, '#skF_9'), '#skF_7') | ~m1_subset_1('#skF_5'('#skF_10', B_317, '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k10_relat_1('#skF_9', B_317)))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_575])).
% 4.73/1.82  tff(c_835, plain, (~m1_subset_1('#skF_5'('#skF_10', '#skF_7', '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k10_relat_1('#skF_9', '#skF_7')) | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_40, c_831])).
% 4.73/1.82  tff(c_842, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_86, c_388, c_733, c_835])).
% 4.73/1.82  tff(c_843, plain, (r2_hidden('#skF_10', k8_relset_1('#skF_6', '#skF_8', '#skF_9', '#skF_7'))), inference(splitRight, [status(thm)], [c_64])).
% 4.73/1.82  tff(c_897, plain, (r2_hidden('#skF_10', k10_relat_1('#skF_9', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_895, c_843])).
% 4.73/1.82  tff(c_42, plain, (![A_62, B_63, C_64]: (r2_hidden(k4_tarski(A_62, '#skF_5'(A_62, B_63, C_64)), C_64) | ~r2_hidden(A_62, k10_relat_1(C_64, B_63)) | ~v1_relat_1(C_64))), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.73/1.82  tff(c_941, plain, (![B_348, D_349, C_350, A_351]: (r2_hidden(B_348, D_349) | v1_xboole_0(k2_zfmisc_1(C_350, D_349)) | ~m1_subset_1(k4_tarski(A_351, B_348), k2_zfmisc_1(C_350, D_349)))), inference(resolution, [status(thm)], [c_10, c_103])).
% 4.73/1.82  tff(c_948, plain, (![B_348, A_351]: (r2_hidden(B_348, '#skF_8') | v1_xboole_0(k2_zfmisc_1('#skF_6', '#skF_8')) | ~r2_hidden(k4_tarski(A_351, B_348), '#skF_9'))), inference(resolution, [status(thm)], [c_101, c_941])).
% 4.73/1.82  tff(c_990, plain, (![B_355, A_356]: (r2_hidden(B_355, '#skF_8') | ~r2_hidden(k4_tarski(A_356, B_355), '#skF_9'))), inference(negUnitSimplification, [status(thm)], [c_92, c_948])).
% 4.73/1.82  tff(c_994, plain, (![A_62, B_63]: (r2_hidden('#skF_5'(A_62, B_63, '#skF_9'), '#skF_8') | ~r2_hidden(A_62, k10_relat_1('#skF_9', B_63)) | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_42, c_990])).
% 4.73/1.82  tff(c_1046, plain, (![A_363, B_364]: (r2_hidden('#skF_5'(A_363, B_364, '#skF_9'), '#skF_8') | ~r2_hidden(A_363, k10_relat_1('#skF_9', B_364)))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_994])).
% 4.73/1.82  tff(c_1051, plain, (![A_365, B_366]: (m1_subset_1('#skF_5'(A_365, B_366, '#skF_9'), '#skF_8') | ~r2_hidden(A_365, k10_relat_1('#skF_9', B_366)))), inference(resolution, [status(thm)], [c_1046, c_8])).
% 4.73/1.82  tff(c_1068, plain, (m1_subset_1('#skF_5'('#skF_10', '#skF_7', '#skF_9'), '#skF_8')), inference(resolution, [status(thm)], [c_897, c_1051])).
% 4.73/1.82  tff(c_953, plain, (![A_352, B_353, C_354]: (r2_hidden(k4_tarski(A_352, '#skF_5'(A_352, B_353, C_354)), C_354) | ~r2_hidden(A_352, k10_relat_1(C_354, B_353)) | ~v1_relat_1(C_354))), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.73/1.82  tff(c_844, plain, (~r2_hidden('#skF_11', '#skF_7')), inference(splitRight, [status(thm)], [c_64])).
% 4.73/1.82  tff(c_62, plain, (![F_160]: (~r2_hidden(F_160, '#skF_7') | ~r2_hidden(k4_tarski('#skF_10', F_160), '#skF_9') | ~m1_subset_1(F_160, '#skF_8') | r2_hidden('#skF_11', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_118])).
% 4.73/1.82  tff(c_884, plain, (![F_160]: (~r2_hidden(F_160, '#skF_7') | ~r2_hidden(k4_tarski('#skF_10', F_160), '#skF_9') | ~m1_subset_1(F_160, '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_844, c_62])).
% 4.73/1.82  tff(c_961, plain, (![B_353]: (~r2_hidden('#skF_5'('#skF_10', B_353, '#skF_9'), '#skF_7') | ~m1_subset_1('#skF_5'('#skF_10', B_353, '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k10_relat_1('#skF_9', B_353)) | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_953, c_884])).
% 4.73/1.82  tff(c_1326, plain, (![B_403]: (~r2_hidden('#skF_5'('#skF_10', B_403, '#skF_9'), '#skF_7') | ~m1_subset_1('#skF_5'('#skF_10', B_403, '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k10_relat_1('#skF_9', B_403)))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_961])).
% 4.73/1.82  tff(c_1330, plain, (~m1_subset_1('#skF_5'('#skF_10', '#skF_7', '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k10_relat_1('#skF_9', '#skF_7')) | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_40, c_1326])).
% 4.73/1.82  tff(c_1337, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_86, c_897, c_1068, c_1330])).
% 4.73/1.82  tff(c_1338, plain, (![A_171]: (~r2_hidden(A_171, '#skF_9'))), inference(splitRight, [status(thm)], [c_91])).
% 4.73/1.82  tff(c_1548, plain, (![A_469, B_470]: (~r2_hidden(A_469, k10_relat_1('#skF_9', B_470)) | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_1523, c_1338])).
% 4.73/1.82  tff(c_1564, plain, (![A_469, B_470]: (~r2_hidden(A_469, k10_relat_1('#skF_9', B_470)))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_1548])).
% 4.73/1.82  tff(c_1435, plain, (![A_441, B_442, C_443, D_444]: (k8_relset_1(A_441, B_442, C_443, D_444)=k10_relat_1(C_443, D_444) | ~m1_subset_1(C_443, k1_zfmisc_1(k2_zfmisc_1(A_441, B_442))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.73/1.82  tff(c_1438, plain, (![D_444]: (k8_relset_1('#skF_6', '#skF_8', '#skF_9', D_444)=k10_relat_1('#skF_9', D_444))), inference(resolution, [status(thm)], [c_50, c_1435])).
% 4.73/1.82  tff(c_1362, plain, (r2_hidden('#skF_10', k8_relset_1('#skF_6', '#skF_8', '#skF_9', '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_1338, c_68])).
% 4.73/1.82  tff(c_1440, plain, (r2_hidden('#skF_10', k10_relat_1('#skF_9', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_1438, c_1362])).
% 4.73/1.82  tff(c_1567, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1564, c_1440])).
% 4.73/1.82  tff(c_1568, plain, (r2_hidden('#skF_10', k8_relset_1('#skF_6', '#skF_8', '#skF_9', '#skF_7'))), inference(splitRight, [status(thm)], [c_72])).
% 4.73/1.82  tff(c_1632, plain, (r2_hidden('#skF_10', k10_relat_1('#skF_9', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_1630, c_1568])).
% 4.73/1.82  tff(c_1704, plain, (![A_526, B_527, C_528]: (r2_hidden(k4_tarski(A_526, '#skF_5'(A_526, B_527, C_528)), C_528) | ~r2_hidden(A_526, k10_relat_1(C_528, B_527)) | ~v1_relat_1(C_528))), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.73/1.82  tff(c_1579, plain, (![C_472, B_473, A_474]: (~v1_xboole_0(C_472) | ~m1_subset_1(B_473, k1_zfmisc_1(C_472)) | ~r2_hidden(A_474, B_473))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.73/1.82  tff(c_1582, plain, (![A_474]: (~v1_xboole_0(k2_zfmisc_1('#skF_6', '#skF_8')) | ~r2_hidden(A_474, '#skF_9'))), inference(resolution, [status(thm)], [c_50, c_1579])).
% 4.73/1.82  tff(c_1587, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_6', '#skF_8'))), inference(splitLeft, [status(thm)], [c_1582])).
% 4.73/1.82  tff(c_1583, plain, (![A_475, C_476, B_477]: (m1_subset_1(A_475, C_476) | ~m1_subset_1(B_477, k1_zfmisc_1(C_476)) | ~r2_hidden(A_475, B_477))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.73/1.82  tff(c_1586, plain, (![A_475]: (m1_subset_1(A_475, k2_zfmisc_1('#skF_6', '#skF_8')) | ~r2_hidden(A_475, '#skF_9'))), inference(resolution, [status(thm)], [c_50, c_1583])).
% 4.73/1.82  tff(c_1590, plain, (![B_479, D_480, A_481, C_482]: (r2_hidden(B_479, D_480) | ~r2_hidden(k4_tarski(A_481, B_479), k2_zfmisc_1(C_482, D_480)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.73/1.82  tff(c_1686, plain, (![B_520, D_521, C_522, A_523]: (r2_hidden(B_520, D_521) | v1_xboole_0(k2_zfmisc_1(C_522, D_521)) | ~m1_subset_1(k4_tarski(A_523, B_520), k2_zfmisc_1(C_522, D_521)))), inference(resolution, [status(thm)], [c_10, c_1590])).
% 4.73/1.82  tff(c_1693, plain, (![B_520, A_523]: (r2_hidden(B_520, '#skF_8') | v1_xboole_0(k2_zfmisc_1('#skF_6', '#skF_8')) | ~r2_hidden(k4_tarski(A_523, B_520), '#skF_9'))), inference(resolution, [status(thm)], [c_1586, c_1686])).
% 4.73/1.82  tff(c_1697, plain, (![B_520, A_523]: (r2_hidden(B_520, '#skF_8') | ~r2_hidden(k4_tarski(A_523, B_520), '#skF_9'))), inference(negUnitSimplification, [status(thm)], [c_1587, c_1693])).
% 4.73/1.82  tff(c_1708, plain, (![A_526, B_527]: (r2_hidden('#skF_5'(A_526, B_527, '#skF_9'), '#skF_8') | ~r2_hidden(A_526, k10_relat_1('#skF_9', B_527)) | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_1704, c_1697])).
% 4.73/1.82  tff(c_1816, plain, (![A_539, B_540]: (r2_hidden('#skF_5'(A_539, B_540, '#skF_9'), '#skF_8') | ~r2_hidden(A_539, k10_relat_1('#skF_9', B_540)))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_1708])).
% 4.73/1.82  tff(c_1824, plain, (![A_541, B_542]: (m1_subset_1('#skF_5'(A_541, B_542, '#skF_9'), '#skF_8') | ~r2_hidden(A_541, k10_relat_1('#skF_9', B_542)))), inference(resolution, [status(thm)], [c_1816, c_8])).
% 4.73/1.82  tff(c_1841, plain, (m1_subset_1('#skF_5'('#skF_10', '#skF_7', '#skF_9'), '#skF_8')), inference(resolution, [status(thm)], [c_1632, c_1824])).
% 4.73/1.82  tff(c_1569, plain, (~m1_subset_1('#skF_11', '#skF_8')), inference(splitRight, [status(thm)], [c_72])).
% 4.73/1.82  tff(c_70, plain, (![F_160]: (~r2_hidden(F_160, '#skF_7') | ~r2_hidden(k4_tarski('#skF_10', F_160), '#skF_9') | ~m1_subset_1(F_160, '#skF_8') | m1_subset_1('#skF_11', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_118])).
% 4.73/1.82  tff(c_1652, plain, (![F_160]: (~r2_hidden(F_160, '#skF_7') | ~r2_hidden(k4_tarski('#skF_10', F_160), '#skF_9') | ~m1_subset_1(F_160, '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_1569, c_70])).
% 4.73/1.82  tff(c_1716, plain, (![B_527]: (~r2_hidden('#skF_5'('#skF_10', B_527, '#skF_9'), '#skF_7') | ~m1_subset_1('#skF_5'('#skF_10', B_527, '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k10_relat_1('#skF_9', B_527)) | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_1704, c_1652])).
% 4.73/1.82  tff(c_2152, plain, (![B_580]: (~r2_hidden('#skF_5'('#skF_10', B_580, '#skF_9'), '#skF_7') | ~m1_subset_1('#skF_5'('#skF_10', B_580, '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k10_relat_1('#skF_9', B_580)))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_1716])).
% 4.73/1.82  tff(c_2156, plain, (~m1_subset_1('#skF_5'('#skF_10', '#skF_7', '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k10_relat_1('#skF_9', '#skF_7')) | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_40, c_2152])).
% 4.73/1.82  tff(c_2163, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_86, c_1632, c_1841, c_2156])).
% 4.73/1.82  tff(c_2164, plain, (![A_474]: (~r2_hidden(A_474, '#skF_9'))), inference(splitRight, [status(thm)], [c_1582])).
% 4.73/1.82  tff(c_2397, plain, (![A_649, B_650]: (~r2_hidden(A_649, k10_relat_1('#skF_9', B_650)) | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_2372, c_2164])).
% 4.73/1.82  tff(c_2413, plain, (![A_649, B_650]: (~r2_hidden(A_649, k10_relat_1('#skF_9', B_650)))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_2397])).
% 4.73/1.82  tff(c_2249, plain, (![A_615, B_616, C_617, D_618]: (k8_relset_1(A_615, B_616, C_617, D_618)=k10_relat_1(C_617, D_618) | ~m1_subset_1(C_617, k1_zfmisc_1(k2_zfmisc_1(A_615, B_616))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.73/1.82  tff(c_2252, plain, (![D_618]: (k8_relset_1('#skF_6', '#skF_8', '#skF_9', D_618)=k10_relat_1('#skF_9', D_618))), inference(resolution, [status(thm)], [c_50, c_2249])).
% 4.73/1.82  tff(c_2255, plain, (r2_hidden('#skF_10', k10_relat_1('#skF_9', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_2252, c_1568])).
% 4.73/1.82  tff(c_2416, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2413, c_2255])).
% 4.73/1.82  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.73/1.82  
% 4.73/1.82  Inference rules
% 4.73/1.82  ----------------------
% 4.73/1.82  #Ref     : 0
% 4.73/1.82  #Sup     : 450
% 4.73/1.82  #Fact    : 0
% 4.73/1.82  #Define  : 0
% 4.73/1.82  #Split   : 16
% 4.73/1.82  #Chain   : 0
% 4.73/1.82  #Close   : 0
% 4.73/1.82  
% 4.73/1.82  Ordering : KBO
% 4.73/1.82  
% 4.73/1.82  Simplification rules
% 4.73/1.82  ----------------------
% 4.73/1.82  #Subsume      : 34
% 4.73/1.82  #Demod        : 150
% 4.73/1.82  #Tautology    : 74
% 4.73/1.82  #SimpNegUnit  : 21
% 4.73/1.82  #BackRed      : 12
% 4.73/1.82  
% 4.73/1.82  #Partial instantiations: 0
% 4.73/1.82  #Strategies tried      : 1
% 4.73/1.82  
% 4.73/1.82  Timing (in seconds)
% 4.73/1.82  ----------------------
% 4.73/1.83  Preprocessing        : 0.34
% 4.73/1.83  Parsing              : 0.17
% 4.73/1.83  CNF conversion       : 0.04
% 4.73/1.83  Main loop            : 0.65
% 4.73/1.83  Inferencing          : 0.26
% 4.73/1.83  Reduction            : 0.19
% 4.73/1.83  Demodulation         : 0.12
% 4.73/1.83  BG Simplification    : 0.03
% 4.73/1.83  Subsumption          : 0.13
% 4.73/1.83  Abstraction          : 0.03
% 4.73/1.83  MUC search           : 0.00
% 4.73/1.83  Cooper               : 0.00
% 4.73/1.83  Total                : 1.09
% 4.73/1.83  Index Insertion      : 0.00
% 4.73/1.83  Index Deletion       : 0.00
% 4.73/1.83  Index Matching       : 0.00
% 4.73/1.83  BG Taut test         : 0.00
%------------------------------------------------------------------------------
