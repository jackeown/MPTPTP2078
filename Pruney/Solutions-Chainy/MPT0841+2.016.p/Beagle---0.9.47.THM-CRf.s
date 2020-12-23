%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:34 EST 2020

% Result     : Theorem 4.44s
% Output     : CNFRefutation 4.58s
% Verified   : 
% Statistics : Number of formulae       :  145 ( 370 expanded)
%              Number of leaves         :   35 ( 137 expanded)
%              Depth                    :    9
%              Number of atoms          :  267 (1059 expanded)
%              Number of equality atoms :   14 (  28 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k7_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_11 > #skF_7 > #skF_10 > #skF_6 > #skF_5 > #skF_2 > #skF_9 > #skF_4 > #skF_8 > #skF_3

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

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

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
                    ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(C,A)))
                   => ! [E] :
                        ( m1_subset_1(E,A)
                       => ( r2_hidden(E,k7_relset_1(C,A,D,B))
                        <=> ? [F] :
                              ( m1_subset_1(F,C)
                              & r2_hidden(k4_tarski(F,E),D)
                              & r2_hidden(F,B) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_relset_1)).

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
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_91,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_74,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( C = k9_relat_1(A,B)
        <=> ! [D] :
              ( r2_hidden(D,C)
            <=> ? [E] :
                  ( r2_hidden(k4_tarski(E,D),A)
                  & r2_hidden(E,B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_relat_1)).

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
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_8','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_80,plain,(
    ! [B_167,A_168] :
      ( v1_relat_1(B_167)
      | ~ m1_subset_1(B_167,k1_zfmisc_1(A_168))
      | ~ v1_relat_1(A_168) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_83,plain,
    ( v1_relat_1('#skF_9')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_8','#skF_6')) ),
    inference(resolution,[status(thm)],[c_50,c_80])).

tff(c_86,plain,(
    v1_relat_1('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_83])).

tff(c_2356,plain,(
    ! [A_650,B_651,C_652] :
      ( r2_hidden(k4_tarski('#skF_5'(A_650,B_651,C_652),A_650),C_652)
      | ~ r2_hidden(A_650,k9_relat_1(C_652,B_651))
      | ~ v1_relat_1(C_652) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_1611,plain,(
    ! [A_498,B_499,C_500,D_501] :
      ( k7_relset_1(A_498,B_499,C_500,D_501) = k9_relat_1(C_500,D_501)
      | ~ m1_subset_1(C_500,k1_zfmisc_1(k2_zfmisc_1(A_498,B_499))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_1614,plain,(
    ! [D_501] : k7_relset_1('#skF_8','#skF_6','#skF_9',D_501) = k9_relat_1('#skF_9',D_501) ),
    inference(resolution,[status(thm)],[c_50,c_1611])).

tff(c_1507,plain,(
    ! [A_470,B_471,C_472] :
      ( r2_hidden(k4_tarski('#skF_5'(A_470,B_471,C_472),A_470),C_472)
      | ~ r2_hidden(A_470,k9_relat_1(C_472,B_471))
      | ~ v1_relat_1(C_472) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_893,plain,(
    ! [A_334,B_335,C_336,D_337] :
      ( k7_relset_1(A_334,B_335,C_336,D_337) = k9_relat_1(C_336,D_337)
      | ~ m1_subset_1(C_336,k1_zfmisc_1(k2_zfmisc_1(A_334,B_335))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_896,plain,(
    ! [D_337] : k7_relset_1('#skF_8','#skF_6','#skF_9',D_337) = k9_relat_1('#skF_9',D_337) ),
    inference(resolution,[status(thm)],[c_50,c_893])).

tff(c_384,plain,(
    ! [A_244,B_245,C_246,D_247] :
      ( k7_relset_1(A_244,B_245,C_246,D_247) = k9_relat_1(C_246,D_247)
      | ~ m1_subset_1(C_246,k1_zfmisc_1(k2_zfmisc_1(A_244,B_245))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_387,plain,(
    ! [D_247] : k7_relset_1('#skF_8','#skF_6','#skF_9',D_247) = k9_relat_1('#skF_9',D_247) ),
    inference(resolution,[status(thm)],[c_50,c_384])).

tff(c_72,plain,
    ( r2_hidden('#skF_10',k7_relset_1('#skF_8','#skF_6','#skF_9','#skF_7'))
    | m1_subset_1('#skF_11','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_87,plain,(
    m1_subset_1('#skF_11','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_72])).

tff(c_64,plain,
    ( r2_hidden('#skF_10',k7_relset_1('#skF_8','#skF_6','#skF_9','#skF_7'))
    | r2_hidden('#skF_11','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_108,plain,(
    r2_hidden('#skF_11','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_68,plain,
    ( r2_hidden('#skF_10',k7_relset_1('#skF_8','#skF_6','#skF_9','#skF_7'))
    | r2_hidden(k4_tarski('#skF_11','#skF_10'),'#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_113,plain,(
    r2_hidden(k4_tarski('#skF_11','#skF_10'),'#skF_9') ),
    inference(splitLeft,[status(thm)],[c_68])).

tff(c_178,plain,(
    ! [D_210,A_211,B_212,E_213] :
      ( r2_hidden(D_210,k9_relat_1(A_211,B_212))
      | ~ r2_hidden(E_213,B_212)
      | ~ r2_hidden(k4_tarski(E_213,D_210),A_211)
      | ~ v1_relat_1(A_211) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_216,plain,(
    ! [D_216,A_217] :
      ( r2_hidden(D_216,k9_relat_1(A_217,'#skF_7'))
      | ~ r2_hidden(k4_tarski('#skF_11',D_216),A_217)
      | ~ v1_relat_1(A_217) ) ),
    inference(resolution,[status(thm)],[c_108,c_178])).

tff(c_223,plain,
    ( r2_hidden('#skF_10',k9_relat_1('#skF_9','#skF_7'))
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_113,c_216])).

tff(c_233,plain,(
    r2_hidden('#skF_10',k9_relat_1('#skF_9','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_223])).

tff(c_147,plain,(
    ! [A_198,B_199,C_200,D_201] :
      ( k7_relset_1(A_198,B_199,C_200,D_201) = k9_relat_1(C_200,D_201)
      | ~ m1_subset_1(C_200,k1_zfmisc_1(k2_zfmisc_1(A_198,B_199))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_150,plain,(
    ! [D_201] : k7_relset_1('#skF_8','#skF_6','#skF_9',D_201) = k9_relat_1('#skF_9',D_201) ),
    inference(resolution,[status(thm)],[c_50,c_147])).

tff(c_58,plain,(
    ! [F_160] :
      ( ~ r2_hidden(F_160,'#skF_7')
      | ~ r2_hidden(k4_tarski(F_160,'#skF_10'),'#skF_9')
      | ~ m1_subset_1(F_160,'#skF_8')
      | ~ r2_hidden('#skF_10',k7_relset_1('#skF_8','#skF_6','#skF_9','#skF_7')) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_326,plain,(
    ! [F_229] :
      ( ~ r2_hidden(F_229,'#skF_7')
      | ~ r2_hidden(k4_tarski(F_229,'#skF_10'),'#skF_9')
      | ~ m1_subset_1(F_229,'#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_233,c_150,c_58])).

tff(c_333,plain,
    ( ~ r2_hidden('#skF_11','#skF_7')
    | ~ m1_subset_1('#skF_11','#skF_8') ),
    inference(resolution,[status(thm)],[c_113,c_326])).

tff(c_343,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_108,c_333])).

tff(c_344,plain,(
    r2_hidden('#skF_10',k7_relset_1('#skF_8','#skF_6','#skF_9','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_389,plain,(
    r2_hidden('#skF_10',k9_relat_1('#skF_9','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_387,c_344])).

tff(c_566,plain,(
    ! [A_289,B_290,C_291] :
      ( r2_hidden(k4_tarski('#skF_5'(A_289,B_290,C_291),A_289),C_291)
      | ~ r2_hidden(A_289,k9_relat_1(C_291,B_290))
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
      ( ~ v1_xboole_0(k2_zfmisc_1('#skF_8','#skF_6'))
      | ~ r2_hidden(A_171,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_50,c_88])).

tff(c_92,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_8','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_91])).

tff(c_98,plain,(
    ! [A_176,C_177,B_178] :
      ( m1_subset_1(A_176,C_177)
      | ~ m1_subset_1(B_178,k1_zfmisc_1(C_177))
      | ~ r2_hidden(A_176,B_178) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_101,plain,(
    ! [A_176] :
      ( m1_subset_1(A_176,k2_zfmisc_1('#skF_8','#skF_6'))
      | ~ r2_hidden(A_176,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_50,c_98])).

tff(c_10,plain,(
    ! [A_7,B_8] :
      ( r2_hidden(A_7,B_8)
      | v1_xboole_0(B_8)
      | ~ m1_subset_1(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_93,plain,(
    ! [A_172,C_173,B_174,D_175] :
      ( r2_hidden(A_172,C_173)
      | ~ r2_hidden(k4_tarski(A_172,B_174),k2_zfmisc_1(C_173,D_175)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_415,plain,(
    ! [A_252,C_253,D_254,B_255] :
      ( r2_hidden(A_252,C_253)
      | v1_xboole_0(k2_zfmisc_1(C_253,D_254))
      | ~ m1_subset_1(k4_tarski(A_252,B_255),k2_zfmisc_1(C_253,D_254)) ) ),
    inference(resolution,[status(thm)],[c_10,c_93])).

tff(c_422,plain,(
    ! [A_252,B_255] :
      ( r2_hidden(A_252,'#skF_8')
      | v1_xboole_0(k2_zfmisc_1('#skF_8','#skF_6'))
      | ~ r2_hidden(k4_tarski(A_252,B_255),'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_101,c_415])).

tff(c_426,plain,(
    ! [A_252,B_255] :
      ( r2_hidden(A_252,'#skF_8')
      | ~ r2_hidden(k4_tarski(A_252,B_255),'#skF_9') ) ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_422])).

tff(c_580,plain,(
    ! [A_289,B_290] :
      ( r2_hidden('#skF_5'(A_289,B_290,'#skF_9'),'#skF_8')
      | ~ r2_hidden(A_289,k9_relat_1('#skF_9',B_290))
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_566,c_426])).

tff(c_695,plain,(
    ! [A_299,B_300] :
      ( r2_hidden('#skF_5'(A_299,B_300,'#skF_9'),'#skF_8')
      | ~ r2_hidden(A_299,k9_relat_1('#skF_9',B_300)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_580])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( m1_subset_1(A_5,B_6)
      | ~ r2_hidden(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_703,plain,(
    ! [A_301,B_302] :
      ( m1_subset_1('#skF_5'(A_301,B_302,'#skF_9'),'#skF_8')
      | ~ r2_hidden(A_301,k9_relat_1('#skF_9',B_302)) ) ),
    inference(resolution,[status(thm)],[c_695,c_8])).

tff(c_734,plain,(
    m1_subset_1('#skF_5'('#skF_10','#skF_7','#skF_9'),'#skF_8') ),
    inference(resolution,[status(thm)],[c_389,c_703])).

tff(c_40,plain,(
    ! [A_62,B_63,C_64] :
      ( r2_hidden('#skF_5'(A_62,B_63,C_64),B_63)
      | ~ r2_hidden(A_62,k9_relat_1(C_64,B_63))
      | ~ v1_relat_1(C_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_345,plain,(
    ~ r2_hidden(k4_tarski('#skF_11','#skF_10'),'#skF_9') ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_66,plain,(
    ! [F_160] :
      ( ~ r2_hidden(F_160,'#skF_7')
      | ~ r2_hidden(k4_tarski(F_160,'#skF_10'),'#skF_9')
      | ~ m1_subset_1(F_160,'#skF_8')
      | r2_hidden(k4_tarski('#skF_11','#skF_10'),'#skF_9') ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_432,plain,(
    ! [F_160] :
      ( ~ r2_hidden(F_160,'#skF_7')
      | ~ r2_hidden(k4_tarski(F_160,'#skF_10'),'#skF_9')
      | ~ m1_subset_1(F_160,'#skF_8') ) ),
    inference(negUnitSimplification,[status(thm)],[c_345,c_66])).

tff(c_576,plain,(
    ! [B_290] :
      ( ~ r2_hidden('#skF_5'('#skF_10',B_290,'#skF_9'),'#skF_7')
      | ~ m1_subset_1('#skF_5'('#skF_10',B_290,'#skF_9'),'#skF_8')
      | ~ r2_hidden('#skF_10',k9_relat_1('#skF_9',B_290))
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_566,c_432])).

tff(c_832,plain,(
    ! [B_317] :
      ( ~ r2_hidden('#skF_5'('#skF_10',B_317,'#skF_9'),'#skF_7')
      | ~ m1_subset_1('#skF_5'('#skF_10',B_317,'#skF_9'),'#skF_8')
      | ~ r2_hidden('#skF_10',k9_relat_1('#skF_9',B_317)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_576])).

tff(c_836,plain,
    ( ~ m1_subset_1('#skF_5'('#skF_10','#skF_7','#skF_9'),'#skF_8')
    | ~ r2_hidden('#skF_10',k9_relat_1('#skF_9','#skF_7'))
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_40,c_832])).

tff(c_843,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_389,c_734,c_836])).

tff(c_844,plain,(
    r2_hidden('#skF_10',k7_relset_1('#skF_8','#skF_6','#skF_9','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_898,plain,(
    r2_hidden('#skF_10',k9_relat_1('#skF_9','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_896,c_844])).

tff(c_954,plain,(
    ! [A_352,B_353,C_354] :
      ( r2_hidden(k4_tarski('#skF_5'(A_352,B_353,C_354),A_352),C_354)
      | ~ r2_hidden(A_352,k9_relat_1(C_354,B_353))
      | ~ v1_relat_1(C_354) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_924,plain,(
    ! [A_342,C_343,D_344,B_345] :
      ( r2_hidden(A_342,C_343)
      | v1_xboole_0(k2_zfmisc_1(C_343,D_344))
      | ~ m1_subset_1(k4_tarski(A_342,B_345),k2_zfmisc_1(C_343,D_344)) ) ),
    inference(resolution,[status(thm)],[c_10,c_93])).

tff(c_931,plain,(
    ! [A_342,B_345] :
      ( r2_hidden(A_342,'#skF_8')
      | v1_xboole_0(k2_zfmisc_1('#skF_8','#skF_6'))
      | ~ r2_hidden(k4_tarski(A_342,B_345),'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_101,c_924])).

tff(c_935,plain,(
    ! [A_342,B_345] :
      ( r2_hidden(A_342,'#skF_8')
      | ~ r2_hidden(k4_tarski(A_342,B_345),'#skF_9') ) ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_931])).

tff(c_958,plain,(
    ! [A_352,B_353] :
      ( r2_hidden('#skF_5'(A_352,B_353,'#skF_9'),'#skF_8')
      | ~ r2_hidden(A_352,k9_relat_1('#skF_9',B_353))
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_954,c_935])).

tff(c_1047,plain,(
    ! [A_363,B_364] :
      ( r2_hidden('#skF_5'(A_363,B_364,'#skF_9'),'#skF_8')
      | ~ r2_hidden(A_363,k9_relat_1('#skF_9',B_364)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_958])).

tff(c_1052,plain,(
    ! [A_365,B_366] :
      ( m1_subset_1('#skF_5'(A_365,B_366,'#skF_9'),'#skF_8')
      | ~ r2_hidden(A_365,k9_relat_1('#skF_9',B_366)) ) ),
    inference(resolution,[status(thm)],[c_1047,c_8])).

tff(c_1069,plain,(
    m1_subset_1('#skF_5'('#skF_10','#skF_7','#skF_9'),'#skF_8') ),
    inference(resolution,[status(thm)],[c_898,c_1052])).

tff(c_845,plain,(
    ~ r2_hidden('#skF_11','#skF_7') ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_62,plain,(
    ! [F_160] :
      ( ~ r2_hidden(F_160,'#skF_7')
      | ~ r2_hidden(k4_tarski(F_160,'#skF_10'),'#skF_9')
      | ~ m1_subset_1(F_160,'#skF_8')
      | r2_hidden('#skF_11','#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_885,plain,(
    ! [F_160] :
      ( ~ r2_hidden(F_160,'#skF_7')
      | ~ r2_hidden(k4_tarski(F_160,'#skF_10'),'#skF_9')
      | ~ m1_subset_1(F_160,'#skF_8') ) ),
    inference(negUnitSimplification,[status(thm)],[c_845,c_62])).

tff(c_962,plain,(
    ! [B_353] :
      ( ~ r2_hidden('#skF_5'('#skF_10',B_353,'#skF_9'),'#skF_7')
      | ~ m1_subset_1('#skF_5'('#skF_10',B_353,'#skF_9'),'#skF_8')
      | ~ r2_hidden('#skF_10',k9_relat_1('#skF_9',B_353))
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_954,c_885])).

tff(c_1310,plain,(
    ! [B_404] :
      ( ~ r2_hidden('#skF_5'('#skF_10',B_404,'#skF_9'),'#skF_7')
      | ~ m1_subset_1('#skF_5'('#skF_10',B_404,'#skF_9'),'#skF_8')
      | ~ r2_hidden('#skF_10',k9_relat_1('#skF_9',B_404)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_962])).

tff(c_1314,plain,
    ( ~ m1_subset_1('#skF_5'('#skF_10','#skF_7','#skF_9'),'#skF_8')
    | ~ r2_hidden('#skF_10',k9_relat_1('#skF_9','#skF_7'))
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_40,c_1310])).

tff(c_1321,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_898,c_1069,c_1314])).

tff(c_1322,plain,(
    ! [A_171] : ~ r2_hidden(A_171,'#skF_9') ),
    inference(splitRight,[status(thm)],[c_91])).

tff(c_1532,plain,(
    ! [A_470,B_471] :
      ( ~ r2_hidden(A_470,k9_relat_1('#skF_9',B_471))
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_1507,c_1322])).

tff(c_1548,plain,(
    ! [A_470,B_471] : ~ r2_hidden(A_470,k9_relat_1('#skF_9',B_471)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_1532])).

tff(c_1419,plain,(
    ! [A_442,B_443,C_444,D_445] :
      ( k7_relset_1(A_442,B_443,C_444,D_445) = k9_relat_1(C_444,D_445)
      | ~ m1_subset_1(C_444,k1_zfmisc_1(k2_zfmisc_1(A_442,B_443))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_1422,plain,(
    ! [D_445] : k7_relset_1('#skF_8','#skF_6','#skF_9',D_445) = k9_relat_1('#skF_9',D_445) ),
    inference(resolution,[status(thm)],[c_50,c_1419])).

tff(c_1346,plain,(
    r2_hidden('#skF_10',k7_relset_1('#skF_8','#skF_6','#skF_9','#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_1322,c_68])).

tff(c_1424,plain,(
    r2_hidden('#skF_10',k9_relat_1('#skF_9','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1422,c_1346])).

tff(c_1551,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1548,c_1424])).

tff(c_1552,plain,(
    r2_hidden('#skF_10',k7_relset_1('#skF_8','#skF_6','#skF_9','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_1616,plain,(
    r2_hidden('#skF_10',k9_relat_1('#skF_9','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1614,c_1552])).

tff(c_1688,plain,(
    ! [A_527,B_528,C_529] :
      ( r2_hidden(k4_tarski('#skF_5'(A_527,B_528,C_529),A_527),C_529)
      | ~ r2_hidden(A_527,k9_relat_1(C_529,B_528))
      | ~ v1_relat_1(C_529) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_1563,plain,(
    ! [C_473,B_474,A_475] :
      ( ~ v1_xboole_0(C_473)
      | ~ m1_subset_1(B_474,k1_zfmisc_1(C_473))
      | ~ r2_hidden(A_475,B_474) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_1566,plain,(
    ! [A_475] :
      ( ~ v1_xboole_0(k2_zfmisc_1('#skF_8','#skF_6'))
      | ~ r2_hidden(A_475,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_50,c_1563])).

tff(c_1571,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_8','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_1566])).

tff(c_1567,plain,(
    ! [A_476,C_477,B_478] :
      ( m1_subset_1(A_476,C_477)
      | ~ m1_subset_1(B_478,k1_zfmisc_1(C_477))
      | ~ r2_hidden(A_476,B_478) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1570,plain,(
    ! [A_476] :
      ( m1_subset_1(A_476,k2_zfmisc_1('#skF_8','#skF_6'))
      | ~ r2_hidden(A_476,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_50,c_1567])).

tff(c_1579,plain,(
    ! [A_484,C_485,B_486,D_487] :
      ( r2_hidden(A_484,C_485)
      | ~ r2_hidden(k4_tarski(A_484,B_486),k2_zfmisc_1(C_485,D_487)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1652,plain,(
    ! [A_515,C_516,D_517,B_518] :
      ( r2_hidden(A_515,C_516)
      | v1_xboole_0(k2_zfmisc_1(C_516,D_517))
      | ~ m1_subset_1(k4_tarski(A_515,B_518),k2_zfmisc_1(C_516,D_517)) ) ),
    inference(resolution,[status(thm)],[c_10,c_1579])).

tff(c_1659,plain,(
    ! [A_515,B_518] :
      ( r2_hidden(A_515,'#skF_8')
      | v1_xboole_0(k2_zfmisc_1('#skF_8','#skF_6'))
      | ~ r2_hidden(k4_tarski(A_515,B_518),'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_1570,c_1652])).

tff(c_1663,plain,(
    ! [A_515,B_518] :
      ( r2_hidden(A_515,'#skF_8')
      | ~ r2_hidden(k4_tarski(A_515,B_518),'#skF_9') ) ),
    inference(negUnitSimplification,[status(thm)],[c_1571,c_1659])).

tff(c_1696,plain,(
    ! [A_527,B_528] :
      ( r2_hidden('#skF_5'(A_527,B_528,'#skF_9'),'#skF_8')
      | ~ r2_hidden(A_527,k9_relat_1('#skF_9',B_528))
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_1688,c_1663])).

tff(c_1800,plain,(
    ! [A_540,B_541] :
      ( r2_hidden('#skF_5'(A_540,B_541,'#skF_9'),'#skF_8')
      | ~ r2_hidden(A_540,k9_relat_1('#skF_9',B_541)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_1696])).

tff(c_1808,plain,(
    ! [A_542,B_543] :
      ( m1_subset_1('#skF_5'(A_542,B_543,'#skF_9'),'#skF_8')
      | ~ r2_hidden(A_542,k9_relat_1('#skF_9',B_543)) ) ),
    inference(resolution,[status(thm)],[c_1800,c_8])).

tff(c_1825,plain,(
    m1_subset_1('#skF_5'('#skF_10','#skF_7','#skF_9'),'#skF_8') ),
    inference(resolution,[status(thm)],[c_1616,c_1808])).

tff(c_1553,plain,(
    ~ m1_subset_1('#skF_11','#skF_8') ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_70,plain,(
    ! [F_160] :
      ( ~ r2_hidden(F_160,'#skF_7')
      | ~ r2_hidden(k4_tarski(F_160,'#skF_10'),'#skF_9')
      | ~ m1_subset_1(F_160,'#skF_8')
      | m1_subset_1('#skF_11','#skF_8') ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_1636,plain,(
    ! [F_160] :
      ( ~ r2_hidden(F_160,'#skF_7')
      | ~ r2_hidden(k4_tarski(F_160,'#skF_10'),'#skF_9')
      | ~ m1_subset_1(F_160,'#skF_8') ) ),
    inference(negUnitSimplification,[status(thm)],[c_1553,c_70])).

tff(c_1700,plain,(
    ! [B_528] :
      ( ~ r2_hidden('#skF_5'('#skF_10',B_528,'#skF_9'),'#skF_7')
      | ~ m1_subset_1('#skF_5'('#skF_10',B_528,'#skF_9'),'#skF_8')
      | ~ r2_hidden('#skF_10',k9_relat_1('#skF_9',B_528))
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_1688,c_1636])).

tff(c_2136,plain,(
    ! [B_581] :
      ( ~ r2_hidden('#skF_5'('#skF_10',B_581,'#skF_9'),'#skF_7')
      | ~ m1_subset_1('#skF_5'('#skF_10',B_581,'#skF_9'),'#skF_8')
      | ~ r2_hidden('#skF_10',k9_relat_1('#skF_9',B_581)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_1700])).

tff(c_2140,plain,
    ( ~ m1_subset_1('#skF_5'('#skF_10','#skF_7','#skF_9'),'#skF_8')
    | ~ r2_hidden('#skF_10',k9_relat_1('#skF_9','#skF_7'))
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_40,c_2136])).

tff(c_2147,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_1616,c_1825,c_2140])).

tff(c_2148,plain,(
    ! [A_475] : ~ r2_hidden(A_475,'#skF_9') ),
    inference(splitRight,[status(thm)],[c_1566])).

tff(c_2381,plain,(
    ! [A_650,B_651] :
      ( ~ r2_hidden(A_650,k9_relat_1('#skF_9',B_651))
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_2356,c_2148])).

tff(c_2397,plain,(
    ! [A_650,B_651] : ~ r2_hidden(A_650,k9_relat_1('#skF_9',B_651)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_2381])).

tff(c_2233,plain,(
    ! [A_616,B_617,C_618,D_619] :
      ( k7_relset_1(A_616,B_617,C_618,D_619) = k9_relat_1(C_618,D_619)
      | ~ m1_subset_1(C_618,k1_zfmisc_1(k2_zfmisc_1(A_616,B_617))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_2236,plain,(
    ! [D_619] : k7_relset_1('#skF_8','#skF_6','#skF_9',D_619) = k9_relat_1('#skF_9',D_619) ),
    inference(resolution,[status(thm)],[c_50,c_2233])).

tff(c_2239,plain,(
    r2_hidden('#skF_10',k9_relat_1('#skF_9','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2236,c_1552])).

tff(c_2400,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2397,c_2239])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:18:17 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.44/1.80  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.44/1.83  
% 4.44/1.83  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.58/1.83  %$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k7_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_11 > #skF_7 > #skF_10 > #skF_6 > #skF_5 > #skF_2 > #skF_9 > #skF_4 > #skF_8 > #skF_3
% 4.58/1.83  
% 4.58/1.83  %Foreground sorts:
% 4.58/1.83  
% 4.58/1.83  
% 4.58/1.83  %Background operators:
% 4.58/1.83  
% 4.58/1.83  
% 4.58/1.83  %Foreground operators:
% 4.58/1.83  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 4.58/1.83  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.58/1.83  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.58/1.83  tff('#skF_11', type, '#skF_11': $i).
% 4.58/1.83  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 4.58/1.83  tff('#skF_7', type, '#skF_7': $i).
% 4.58/1.83  tff('#skF_10', type, '#skF_10': $i).
% 4.58/1.83  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 4.58/1.83  tff('#skF_6', type, '#skF_6': $i).
% 4.58/1.83  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 4.58/1.83  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 4.58/1.83  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.58/1.83  tff('#skF_9', type, '#skF_9': $i).
% 4.58/1.83  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.58/1.83  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 4.58/1.83  tff('#skF_8', type, '#skF_8': $i).
% 4.58/1.83  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.58/1.83  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.58/1.83  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.58/1.83  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 4.58/1.83  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.58/1.83  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.58/1.83  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.58/1.83  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.58/1.83  
% 4.58/1.86  tff(f_76, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 4.58/1.86  tff(f_118, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (~v1_xboole_0(C) => (![D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, A))) => (![E]: (m1_subset_1(E, A) => (r2_hidden(E, k7_relset_1(C, A, D, B)) <=> (?[F]: ((m1_subset_1(F, C) & r2_hidden(k4_tarski(F, E), D)) & r2_hidden(F, B)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_relset_1)).
% 4.58/1.86  tff(f_61, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 4.58/1.86  tff(f_87, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_relat_1)).
% 4.58/1.86  tff(f_91, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 4.58/1.86  tff(f_74, axiom, (![A]: (v1_relat_1(A) => (![B, C]: ((C = k9_relat_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E]: (r2_hidden(k4_tarski(E, D), A) & r2_hidden(E, B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d13_relat_1)).
% 4.58/1.86  tff(f_54, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 4.58/1.86  tff(f_47, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 4.58/1.86  tff(f_41, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 4.58/1.86  tff(f_31, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 4.58/1.86  tff(f_35, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 4.58/1.86  tff(c_36, plain, (![A_60, B_61]: (v1_relat_1(k2_zfmisc_1(A_60, B_61)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.58/1.86  tff(c_50, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_8', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_118])).
% 4.58/1.86  tff(c_80, plain, (![B_167, A_168]: (v1_relat_1(B_167) | ~m1_subset_1(B_167, k1_zfmisc_1(A_168)) | ~v1_relat_1(A_168))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.58/1.86  tff(c_83, plain, (v1_relat_1('#skF_9') | ~v1_relat_1(k2_zfmisc_1('#skF_8', '#skF_6'))), inference(resolution, [status(thm)], [c_50, c_80])).
% 4.58/1.86  tff(c_86, plain, (v1_relat_1('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_83])).
% 4.58/1.86  tff(c_2356, plain, (![A_650, B_651, C_652]: (r2_hidden(k4_tarski('#skF_5'(A_650, B_651, C_652), A_650), C_652) | ~r2_hidden(A_650, k9_relat_1(C_652, B_651)) | ~v1_relat_1(C_652))), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.58/1.86  tff(c_1611, plain, (![A_498, B_499, C_500, D_501]: (k7_relset_1(A_498, B_499, C_500, D_501)=k9_relat_1(C_500, D_501) | ~m1_subset_1(C_500, k1_zfmisc_1(k2_zfmisc_1(A_498, B_499))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.58/1.86  tff(c_1614, plain, (![D_501]: (k7_relset_1('#skF_8', '#skF_6', '#skF_9', D_501)=k9_relat_1('#skF_9', D_501))), inference(resolution, [status(thm)], [c_50, c_1611])).
% 4.58/1.86  tff(c_1507, plain, (![A_470, B_471, C_472]: (r2_hidden(k4_tarski('#skF_5'(A_470, B_471, C_472), A_470), C_472) | ~r2_hidden(A_470, k9_relat_1(C_472, B_471)) | ~v1_relat_1(C_472))), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.58/1.86  tff(c_893, plain, (![A_334, B_335, C_336, D_337]: (k7_relset_1(A_334, B_335, C_336, D_337)=k9_relat_1(C_336, D_337) | ~m1_subset_1(C_336, k1_zfmisc_1(k2_zfmisc_1(A_334, B_335))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.58/1.86  tff(c_896, plain, (![D_337]: (k7_relset_1('#skF_8', '#skF_6', '#skF_9', D_337)=k9_relat_1('#skF_9', D_337))), inference(resolution, [status(thm)], [c_50, c_893])).
% 4.58/1.86  tff(c_384, plain, (![A_244, B_245, C_246, D_247]: (k7_relset_1(A_244, B_245, C_246, D_247)=k9_relat_1(C_246, D_247) | ~m1_subset_1(C_246, k1_zfmisc_1(k2_zfmisc_1(A_244, B_245))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.58/1.86  tff(c_387, plain, (![D_247]: (k7_relset_1('#skF_8', '#skF_6', '#skF_9', D_247)=k9_relat_1('#skF_9', D_247))), inference(resolution, [status(thm)], [c_50, c_384])).
% 4.58/1.86  tff(c_72, plain, (r2_hidden('#skF_10', k7_relset_1('#skF_8', '#skF_6', '#skF_9', '#skF_7')) | m1_subset_1('#skF_11', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_118])).
% 4.58/1.86  tff(c_87, plain, (m1_subset_1('#skF_11', '#skF_8')), inference(splitLeft, [status(thm)], [c_72])).
% 4.58/1.86  tff(c_64, plain, (r2_hidden('#skF_10', k7_relset_1('#skF_8', '#skF_6', '#skF_9', '#skF_7')) | r2_hidden('#skF_11', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_118])).
% 4.58/1.86  tff(c_108, plain, (r2_hidden('#skF_11', '#skF_7')), inference(splitLeft, [status(thm)], [c_64])).
% 4.58/1.86  tff(c_68, plain, (r2_hidden('#skF_10', k7_relset_1('#skF_8', '#skF_6', '#skF_9', '#skF_7')) | r2_hidden(k4_tarski('#skF_11', '#skF_10'), '#skF_9')), inference(cnfTransformation, [status(thm)], [f_118])).
% 4.58/1.86  tff(c_113, plain, (r2_hidden(k4_tarski('#skF_11', '#skF_10'), '#skF_9')), inference(splitLeft, [status(thm)], [c_68])).
% 4.58/1.86  tff(c_178, plain, (![D_210, A_211, B_212, E_213]: (r2_hidden(D_210, k9_relat_1(A_211, B_212)) | ~r2_hidden(E_213, B_212) | ~r2_hidden(k4_tarski(E_213, D_210), A_211) | ~v1_relat_1(A_211))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.58/1.86  tff(c_216, plain, (![D_216, A_217]: (r2_hidden(D_216, k9_relat_1(A_217, '#skF_7')) | ~r2_hidden(k4_tarski('#skF_11', D_216), A_217) | ~v1_relat_1(A_217))), inference(resolution, [status(thm)], [c_108, c_178])).
% 4.58/1.86  tff(c_223, plain, (r2_hidden('#skF_10', k9_relat_1('#skF_9', '#skF_7')) | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_113, c_216])).
% 4.58/1.86  tff(c_233, plain, (r2_hidden('#skF_10', k9_relat_1('#skF_9', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_223])).
% 4.58/1.86  tff(c_147, plain, (![A_198, B_199, C_200, D_201]: (k7_relset_1(A_198, B_199, C_200, D_201)=k9_relat_1(C_200, D_201) | ~m1_subset_1(C_200, k1_zfmisc_1(k2_zfmisc_1(A_198, B_199))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.58/1.86  tff(c_150, plain, (![D_201]: (k7_relset_1('#skF_8', '#skF_6', '#skF_9', D_201)=k9_relat_1('#skF_9', D_201))), inference(resolution, [status(thm)], [c_50, c_147])).
% 4.58/1.86  tff(c_58, plain, (![F_160]: (~r2_hidden(F_160, '#skF_7') | ~r2_hidden(k4_tarski(F_160, '#skF_10'), '#skF_9') | ~m1_subset_1(F_160, '#skF_8') | ~r2_hidden('#skF_10', k7_relset_1('#skF_8', '#skF_6', '#skF_9', '#skF_7')))), inference(cnfTransformation, [status(thm)], [f_118])).
% 4.58/1.86  tff(c_326, plain, (![F_229]: (~r2_hidden(F_229, '#skF_7') | ~r2_hidden(k4_tarski(F_229, '#skF_10'), '#skF_9') | ~m1_subset_1(F_229, '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_233, c_150, c_58])).
% 4.58/1.86  tff(c_333, plain, (~r2_hidden('#skF_11', '#skF_7') | ~m1_subset_1('#skF_11', '#skF_8')), inference(resolution, [status(thm)], [c_113, c_326])).
% 4.58/1.86  tff(c_343, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_87, c_108, c_333])).
% 4.58/1.86  tff(c_344, plain, (r2_hidden('#skF_10', k7_relset_1('#skF_8', '#skF_6', '#skF_9', '#skF_7'))), inference(splitRight, [status(thm)], [c_68])).
% 4.58/1.86  tff(c_389, plain, (r2_hidden('#skF_10', k9_relat_1('#skF_9', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_387, c_344])).
% 4.58/1.86  tff(c_566, plain, (![A_289, B_290, C_291]: (r2_hidden(k4_tarski('#skF_5'(A_289, B_290, C_291), A_289), C_291) | ~r2_hidden(A_289, k9_relat_1(C_291, B_290)) | ~v1_relat_1(C_291))), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.58/1.86  tff(c_88, plain, (![C_169, B_170, A_171]: (~v1_xboole_0(C_169) | ~m1_subset_1(B_170, k1_zfmisc_1(C_169)) | ~r2_hidden(A_171, B_170))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.58/1.86  tff(c_91, plain, (![A_171]: (~v1_xboole_0(k2_zfmisc_1('#skF_8', '#skF_6')) | ~r2_hidden(A_171, '#skF_9'))), inference(resolution, [status(thm)], [c_50, c_88])).
% 4.58/1.86  tff(c_92, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_8', '#skF_6'))), inference(splitLeft, [status(thm)], [c_91])).
% 4.58/1.86  tff(c_98, plain, (![A_176, C_177, B_178]: (m1_subset_1(A_176, C_177) | ~m1_subset_1(B_178, k1_zfmisc_1(C_177)) | ~r2_hidden(A_176, B_178))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.58/1.86  tff(c_101, plain, (![A_176]: (m1_subset_1(A_176, k2_zfmisc_1('#skF_8', '#skF_6')) | ~r2_hidden(A_176, '#skF_9'))), inference(resolution, [status(thm)], [c_50, c_98])).
% 4.58/1.86  tff(c_10, plain, (![A_7, B_8]: (r2_hidden(A_7, B_8) | v1_xboole_0(B_8) | ~m1_subset_1(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.58/1.86  tff(c_93, plain, (![A_172, C_173, B_174, D_175]: (r2_hidden(A_172, C_173) | ~r2_hidden(k4_tarski(A_172, B_174), k2_zfmisc_1(C_173, D_175)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.58/1.86  tff(c_415, plain, (![A_252, C_253, D_254, B_255]: (r2_hidden(A_252, C_253) | v1_xboole_0(k2_zfmisc_1(C_253, D_254)) | ~m1_subset_1(k4_tarski(A_252, B_255), k2_zfmisc_1(C_253, D_254)))), inference(resolution, [status(thm)], [c_10, c_93])).
% 4.58/1.86  tff(c_422, plain, (![A_252, B_255]: (r2_hidden(A_252, '#skF_8') | v1_xboole_0(k2_zfmisc_1('#skF_8', '#skF_6')) | ~r2_hidden(k4_tarski(A_252, B_255), '#skF_9'))), inference(resolution, [status(thm)], [c_101, c_415])).
% 4.58/1.86  tff(c_426, plain, (![A_252, B_255]: (r2_hidden(A_252, '#skF_8') | ~r2_hidden(k4_tarski(A_252, B_255), '#skF_9'))), inference(negUnitSimplification, [status(thm)], [c_92, c_422])).
% 4.58/1.86  tff(c_580, plain, (![A_289, B_290]: (r2_hidden('#skF_5'(A_289, B_290, '#skF_9'), '#skF_8') | ~r2_hidden(A_289, k9_relat_1('#skF_9', B_290)) | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_566, c_426])).
% 4.58/1.86  tff(c_695, plain, (![A_299, B_300]: (r2_hidden('#skF_5'(A_299, B_300, '#skF_9'), '#skF_8') | ~r2_hidden(A_299, k9_relat_1('#skF_9', B_300)))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_580])).
% 4.58/1.86  tff(c_8, plain, (![A_5, B_6]: (m1_subset_1(A_5, B_6) | ~r2_hidden(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.58/1.86  tff(c_703, plain, (![A_301, B_302]: (m1_subset_1('#skF_5'(A_301, B_302, '#skF_9'), '#skF_8') | ~r2_hidden(A_301, k9_relat_1('#skF_9', B_302)))), inference(resolution, [status(thm)], [c_695, c_8])).
% 4.58/1.86  tff(c_734, plain, (m1_subset_1('#skF_5'('#skF_10', '#skF_7', '#skF_9'), '#skF_8')), inference(resolution, [status(thm)], [c_389, c_703])).
% 4.58/1.86  tff(c_40, plain, (![A_62, B_63, C_64]: (r2_hidden('#skF_5'(A_62, B_63, C_64), B_63) | ~r2_hidden(A_62, k9_relat_1(C_64, B_63)) | ~v1_relat_1(C_64))), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.58/1.86  tff(c_345, plain, (~r2_hidden(k4_tarski('#skF_11', '#skF_10'), '#skF_9')), inference(splitRight, [status(thm)], [c_68])).
% 4.58/1.86  tff(c_66, plain, (![F_160]: (~r2_hidden(F_160, '#skF_7') | ~r2_hidden(k4_tarski(F_160, '#skF_10'), '#skF_9') | ~m1_subset_1(F_160, '#skF_8') | r2_hidden(k4_tarski('#skF_11', '#skF_10'), '#skF_9'))), inference(cnfTransformation, [status(thm)], [f_118])).
% 4.58/1.86  tff(c_432, plain, (![F_160]: (~r2_hidden(F_160, '#skF_7') | ~r2_hidden(k4_tarski(F_160, '#skF_10'), '#skF_9') | ~m1_subset_1(F_160, '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_345, c_66])).
% 4.58/1.86  tff(c_576, plain, (![B_290]: (~r2_hidden('#skF_5'('#skF_10', B_290, '#skF_9'), '#skF_7') | ~m1_subset_1('#skF_5'('#skF_10', B_290, '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k9_relat_1('#skF_9', B_290)) | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_566, c_432])).
% 4.58/1.86  tff(c_832, plain, (![B_317]: (~r2_hidden('#skF_5'('#skF_10', B_317, '#skF_9'), '#skF_7') | ~m1_subset_1('#skF_5'('#skF_10', B_317, '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k9_relat_1('#skF_9', B_317)))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_576])).
% 4.58/1.86  tff(c_836, plain, (~m1_subset_1('#skF_5'('#skF_10', '#skF_7', '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k9_relat_1('#skF_9', '#skF_7')) | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_40, c_832])).
% 4.58/1.86  tff(c_843, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_86, c_389, c_734, c_836])).
% 4.58/1.86  tff(c_844, plain, (r2_hidden('#skF_10', k7_relset_1('#skF_8', '#skF_6', '#skF_9', '#skF_7'))), inference(splitRight, [status(thm)], [c_64])).
% 4.58/1.86  tff(c_898, plain, (r2_hidden('#skF_10', k9_relat_1('#skF_9', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_896, c_844])).
% 4.58/1.86  tff(c_954, plain, (![A_352, B_353, C_354]: (r2_hidden(k4_tarski('#skF_5'(A_352, B_353, C_354), A_352), C_354) | ~r2_hidden(A_352, k9_relat_1(C_354, B_353)) | ~v1_relat_1(C_354))), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.58/1.86  tff(c_924, plain, (![A_342, C_343, D_344, B_345]: (r2_hidden(A_342, C_343) | v1_xboole_0(k2_zfmisc_1(C_343, D_344)) | ~m1_subset_1(k4_tarski(A_342, B_345), k2_zfmisc_1(C_343, D_344)))), inference(resolution, [status(thm)], [c_10, c_93])).
% 4.58/1.86  tff(c_931, plain, (![A_342, B_345]: (r2_hidden(A_342, '#skF_8') | v1_xboole_0(k2_zfmisc_1('#skF_8', '#skF_6')) | ~r2_hidden(k4_tarski(A_342, B_345), '#skF_9'))), inference(resolution, [status(thm)], [c_101, c_924])).
% 4.58/1.86  tff(c_935, plain, (![A_342, B_345]: (r2_hidden(A_342, '#skF_8') | ~r2_hidden(k4_tarski(A_342, B_345), '#skF_9'))), inference(negUnitSimplification, [status(thm)], [c_92, c_931])).
% 4.58/1.86  tff(c_958, plain, (![A_352, B_353]: (r2_hidden('#skF_5'(A_352, B_353, '#skF_9'), '#skF_8') | ~r2_hidden(A_352, k9_relat_1('#skF_9', B_353)) | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_954, c_935])).
% 4.58/1.86  tff(c_1047, plain, (![A_363, B_364]: (r2_hidden('#skF_5'(A_363, B_364, '#skF_9'), '#skF_8') | ~r2_hidden(A_363, k9_relat_1('#skF_9', B_364)))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_958])).
% 4.58/1.86  tff(c_1052, plain, (![A_365, B_366]: (m1_subset_1('#skF_5'(A_365, B_366, '#skF_9'), '#skF_8') | ~r2_hidden(A_365, k9_relat_1('#skF_9', B_366)))), inference(resolution, [status(thm)], [c_1047, c_8])).
% 4.58/1.86  tff(c_1069, plain, (m1_subset_1('#skF_5'('#skF_10', '#skF_7', '#skF_9'), '#skF_8')), inference(resolution, [status(thm)], [c_898, c_1052])).
% 4.58/1.86  tff(c_845, plain, (~r2_hidden('#skF_11', '#skF_7')), inference(splitRight, [status(thm)], [c_64])).
% 4.58/1.86  tff(c_62, plain, (![F_160]: (~r2_hidden(F_160, '#skF_7') | ~r2_hidden(k4_tarski(F_160, '#skF_10'), '#skF_9') | ~m1_subset_1(F_160, '#skF_8') | r2_hidden('#skF_11', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_118])).
% 4.58/1.86  tff(c_885, plain, (![F_160]: (~r2_hidden(F_160, '#skF_7') | ~r2_hidden(k4_tarski(F_160, '#skF_10'), '#skF_9') | ~m1_subset_1(F_160, '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_845, c_62])).
% 4.58/1.86  tff(c_962, plain, (![B_353]: (~r2_hidden('#skF_5'('#skF_10', B_353, '#skF_9'), '#skF_7') | ~m1_subset_1('#skF_5'('#skF_10', B_353, '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k9_relat_1('#skF_9', B_353)) | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_954, c_885])).
% 4.58/1.86  tff(c_1310, plain, (![B_404]: (~r2_hidden('#skF_5'('#skF_10', B_404, '#skF_9'), '#skF_7') | ~m1_subset_1('#skF_5'('#skF_10', B_404, '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k9_relat_1('#skF_9', B_404)))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_962])).
% 4.58/1.86  tff(c_1314, plain, (~m1_subset_1('#skF_5'('#skF_10', '#skF_7', '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k9_relat_1('#skF_9', '#skF_7')) | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_40, c_1310])).
% 4.58/1.86  tff(c_1321, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_86, c_898, c_1069, c_1314])).
% 4.58/1.86  tff(c_1322, plain, (![A_171]: (~r2_hidden(A_171, '#skF_9'))), inference(splitRight, [status(thm)], [c_91])).
% 4.58/1.86  tff(c_1532, plain, (![A_470, B_471]: (~r2_hidden(A_470, k9_relat_1('#skF_9', B_471)) | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_1507, c_1322])).
% 4.58/1.86  tff(c_1548, plain, (![A_470, B_471]: (~r2_hidden(A_470, k9_relat_1('#skF_9', B_471)))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_1532])).
% 4.58/1.86  tff(c_1419, plain, (![A_442, B_443, C_444, D_445]: (k7_relset_1(A_442, B_443, C_444, D_445)=k9_relat_1(C_444, D_445) | ~m1_subset_1(C_444, k1_zfmisc_1(k2_zfmisc_1(A_442, B_443))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.58/1.86  tff(c_1422, plain, (![D_445]: (k7_relset_1('#skF_8', '#skF_6', '#skF_9', D_445)=k9_relat_1('#skF_9', D_445))), inference(resolution, [status(thm)], [c_50, c_1419])).
% 4.58/1.86  tff(c_1346, plain, (r2_hidden('#skF_10', k7_relset_1('#skF_8', '#skF_6', '#skF_9', '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_1322, c_68])).
% 4.58/1.86  tff(c_1424, plain, (r2_hidden('#skF_10', k9_relat_1('#skF_9', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_1422, c_1346])).
% 4.58/1.86  tff(c_1551, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1548, c_1424])).
% 4.58/1.86  tff(c_1552, plain, (r2_hidden('#skF_10', k7_relset_1('#skF_8', '#skF_6', '#skF_9', '#skF_7'))), inference(splitRight, [status(thm)], [c_72])).
% 4.58/1.86  tff(c_1616, plain, (r2_hidden('#skF_10', k9_relat_1('#skF_9', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_1614, c_1552])).
% 4.58/1.86  tff(c_1688, plain, (![A_527, B_528, C_529]: (r2_hidden(k4_tarski('#skF_5'(A_527, B_528, C_529), A_527), C_529) | ~r2_hidden(A_527, k9_relat_1(C_529, B_528)) | ~v1_relat_1(C_529))), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.58/1.86  tff(c_1563, plain, (![C_473, B_474, A_475]: (~v1_xboole_0(C_473) | ~m1_subset_1(B_474, k1_zfmisc_1(C_473)) | ~r2_hidden(A_475, B_474))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.58/1.86  tff(c_1566, plain, (![A_475]: (~v1_xboole_0(k2_zfmisc_1('#skF_8', '#skF_6')) | ~r2_hidden(A_475, '#skF_9'))), inference(resolution, [status(thm)], [c_50, c_1563])).
% 4.58/1.86  tff(c_1571, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_8', '#skF_6'))), inference(splitLeft, [status(thm)], [c_1566])).
% 4.58/1.86  tff(c_1567, plain, (![A_476, C_477, B_478]: (m1_subset_1(A_476, C_477) | ~m1_subset_1(B_478, k1_zfmisc_1(C_477)) | ~r2_hidden(A_476, B_478))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.58/1.86  tff(c_1570, plain, (![A_476]: (m1_subset_1(A_476, k2_zfmisc_1('#skF_8', '#skF_6')) | ~r2_hidden(A_476, '#skF_9'))), inference(resolution, [status(thm)], [c_50, c_1567])).
% 4.58/1.86  tff(c_1579, plain, (![A_484, C_485, B_486, D_487]: (r2_hidden(A_484, C_485) | ~r2_hidden(k4_tarski(A_484, B_486), k2_zfmisc_1(C_485, D_487)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.58/1.86  tff(c_1652, plain, (![A_515, C_516, D_517, B_518]: (r2_hidden(A_515, C_516) | v1_xboole_0(k2_zfmisc_1(C_516, D_517)) | ~m1_subset_1(k4_tarski(A_515, B_518), k2_zfmisc_1(C_516, D_517)))), inference(resolution, [status(thm)], [c_10, c_1579])).
% 4.58/1.86  tff(c_1659, plain, (![A_515, B_518]: (r2_hidden(A_515, '#skF_8') | v1_xboole_0(k2_zfmisc_1('#skF_8', '#skF_6')) | ~r2_hidden(k4_tarski(A_515, B_518), '#skF_9'))), inference(resolution, [status(thm)], [c_1570, c_1652])).
% 4.58/1.86  tff(c_1663, plain, (![A_515, B_518]: (r2_hidden(A_515, '#skF_8') | ~r2_hidden(k4_tarski(A_515, B_518), '#skF_9'))), inference(negUnitSimplification, [status(thm)], [c_1571, c_1659])).
% 4.58/1.86  tff(c_1696, plain, (![A_527, B_528]: (r2_hidden('#skF_5'(A_527, B_528, '#skF_9'), '#skF_8') | ~r2_hidden(A_527, k9_relat_1('#skF_9', B_528)) | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_1688, c_1663])).
% 4.58/1.86  tff(c_1800, plain, (![A_540, B_541]: (r2_hidden('#skF_5'(A_540, B_541, '#skF_9'), '#skF_8') | ~r2_hidden(A_540, k9_relat_1('#skF_9', B_541)))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_1696])).
% 4.58/1.86  tff(c_1808, plain, (![A_542, B_543]: (m1_subset_1('#skF_5'(A_542, B_543, '#skF_9'), '#skF_8') | ~r2_hidden(A_542, k9_relat_1('#skF_9', B_543)))), inference(resolution, [status(thm)], [c_1800, c_8])).
% 4.58/1.86  tff(c_1825, plain, (m1_subset_1('#skF_5'('#skF_10', '#skF_7', '#skF_9'), '#skF_8')), inference(resolution, [status(thm)], [c_1616, c_1808])).
% 4.58/1.86  tff(c_1553, plain, (~m1_subset_1('#skF_11', '#skF_8')), inference(splitRight, [status(thm)], [c_72])).
% 4.58/1.86  tff(c_70, plain, (![F_160]: (~r2_hidden(F_160, '#skF_7') | ~r2_hidden(k4_tarski(F_160, '#skF_10'), '#skF_9') | ~m1_subset_1(F_160, '#skF_8') | m1_subset_1('#skF_11', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_118])).
% 4.58/1.86  tff(c_1636, plain, (![F_160]: (~r2_hidden(F_160, '#skF_7') | ~r2_hidden(k4_tarski(F_160, '#skF_10'), '#skF_9') | ~m1_subset_1(F_160, '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_1553, c_70])).
% 4.58/1.86  tff(c_1700, plain, (![B_528]: (~r2_hidden('#skF_5'('#skF_10', B_528, '#skF_9'), '#skF_7') | ~m1_subset_1('#skF_5'('#skF_10', B_528, '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k9_relat_1('#skF_9', B_528)) | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_1688, c_1636])).
% 4.58/1.86  tff(c_2136, plain, (![B_581]: (~r2_hidden('#skF_5'('#skF_10', B_581, '#skF_9'), '#skF_7') | ~m1_subset_1('#skF_5'('#skF_10', B_581, '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k9_relat_1('#skF_9', B_581)))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_1700])).
% 4.58/1.86  tff(c_2140, plain, (~m1_subset_1('#skF_5'('#skF_10', '#skF_7', '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k9_relat_1('#skF_9', '#skF_7')) | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_40, c_2136])).
% 4.58/1.86  tff(c_2147, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_86, c_1616, c_1825, c_2140])).
% 4.58/1.86  tff(c_2148, plain, (![A_475]: (~r2_hidden(A_475, '#skF_9'))), inference(splitRight, [status(thm)], [c_1566])).
% 4.58/1.86  tff(c_2381, plain, (![A_650, B_651]: (~r2_hidden(A_650, k9_relat_1('#skF_9', B_651)) | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_2356, c_2148])).
% 4.58/1.86  tff(c_2397, plain, (![A_650, B_651]: (~r2_hidden(A_650, k9_relat_1('#skF_9', B_651)))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_2381])).
% 4.58/1.86  tff(c_2233, plain, (![A_616, B_617, C_618, D_619]: (k7_relset_1(A_616, B_617, C_618, D_619)=k9_relat_1(C_618, D_619) | ~m1_subset_1(C_618, k1_zfmisc_1(k2_zfmisc_1(A_616, B_617))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.58/1.86  tff(c_2236, plain, (![D_619]: (k7_relset_1('#skF_8', '#skF_6', '#skF_9', D_619)=k9_relat_1('#skF_9', D_619))), inference(resolution, [status(thm)], [c_50, c_2233])).
% 4.58/1.86  tff(c_2239, plain, (r2_hidden('#skF_10', k9_relat_1('#skF_9', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_2236, c_1552])).
% 4.58/1.86  tff(c_2400, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2397, c_2239])).
% 4.58/1.86  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.58/1.86  
% 4.58/1.86  Inference rules
% 4.58/1.86  ----------------------
% 4.58/1.86  #Ref     : 0
% 4.58/1.86  #Sup     : 449
% 4.58/1.86  #Fact    : 0
% 4.58/1.86  #Define  : 0
% 4.58/1.86  #Split   : 16
% 4.58/1.86  #Chain   : 0
% 4.58/1.86  #Close   : 0
% 4.58/1.86  
% 4.58/1.86  Ordering : KBO
% 4.58/1.86  
% 4.58/1.86  Simplification rules
% 4.58/1.86  ----------------------
% 4.58/1.86  #Subsume      : 33
% 4.58/1.86  #Demod        : 145
% 4.58/1.86  #Tautology    : 72
% 4.58/1.86  #SimpNegUnit  : 21
% 4.58/1.86  #BackRed      : 12
% 4.58/1.86  
% 4.58/1.86  #Partial instantiations: 0
% 4.58/1.86  #Strategies tried      : 1
% 4.58/1.86  
% 4.58/1.86  Timing (in seconds)
% 4.58/1.86  ----------------------
% 4.58/1.86  Preprocessing        : 0.35
% 4.58/1.86  Parsing              : 0.17
% 4.58/1.86  CNF conversion       : 0.04
% 4.58/1.86  Main loop            : 0.66
% 4.58/1.86  Inferencing          : 0.26
% 4.58/1.86  Reduction            : 0.19
% 4.58/1.86  Demodulation         : 0.12
% 4.58/1.86  BG Simplification    : 0.03
% 4.58/1.86  Subsumption          : 0.13
% 4.58/1.86  Abstraction          : 0.03
% 4.58/1.86  MUC search           : 0.00
% 4.58/1.86  Cooper               : 0.00
% 4.58/1.86  Total                : 1.07
% 4.58/1.86  Index Insertion      : 0.00
% 4.58/1.86  Index Deletion       : 0.00
% 4.58/1.86  Index Matching       : 0.00
% 4.58/1.86  BG Taut test         : 0.00
%------------------------------------------------------------------------------
