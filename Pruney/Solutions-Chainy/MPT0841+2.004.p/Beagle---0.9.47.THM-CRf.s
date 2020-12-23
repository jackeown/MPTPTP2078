%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:32 EST 2020

% Result     : Theorem 5.84s
% Output     : CNFRefutation 5.84s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 251 expanded)
%              Number of leaves         :   32 (  98 expanded)
%              Depth                    :    8
%              Number of atoms          :  209 ( 742 expanded)
%              Number of equality atoms :   10 (  22 expanded)
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

tff(f_101,negated_conjecture,(
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

tff(f_70,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_74,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_55,axiom,(
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

tff(f_66,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_31,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(c_44,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_8','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_68,plain,(
    ! [C_157,A_158,B_159] :
      ( v1_relat_1(C_157)
      | ~ m1_subset_1(C_157,k1_zfmisc_1(k2_zfmisc_1(A_158,B_159))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_72,plain,(
    v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_44,c_68])).

tff(c_2780,plain,(
    ! [A_619,B_620,C_621,D_622] :
      ( k7_relset_1(A_619,B_620,C_621,D_622) = k9_relat_1(C_621,D_622)
      | ~ m1_subset_1(C_621,k1_zfmisc_1(k2_zfmisc_1(A_619,B_620))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_2783,plain,(
    ! [D_622] : k7_relset_1('#skF_8','#skF_6','#skF_9',D_622) = k9_relat_1('#skF_9',D_622) ),
    inference(resolution,[status(thm)],[c_44,c_2780])).

tff(c_1644,plain,(
    ! [A_437,B_438,C_439,D_440] :
      ( k7_relset_1(A_437,B_438,C_439,D_440) = k9_relat_1(C_439,D_440)
      | ~ m1_subset_1(C_439,k1_zfmisc_1(k2_zfmisc_1(A_437,B_438))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_1647,plain,(
    ! [D_440] : k7_relset_1('#skF_8','#skF_6','#skF_9',D_440) = k9_relat_1('#skF_9',D_440) ),
    inference(resolution,[status(thm)],[c_44,c_1644])).

tff(c_375,plain,(
    ! [A_237,B_238,C_239,D_240] :
      ( k7_relset_1(A_237,B_238,C_239,D_240) = k9_relat_1(C_239,D_240)
      | ~ m1_subset_1(C_239,k1_zfmisc_1(k2_zfmisc_1(A_237,B_238))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_378,plain,(
    ! [D_240] : k7_relset_1('#skF_8','#skF_6','#skF_9',D_240) = k9_relat_1('#skF_9',D_240) ),
    inference(resolution,[status(thm)],[c_44,c_375])).

tff(c_66,plain,
    ( r2_hidden('#skF_10',k7_relset_1('#skF_8','#skF_6','#skF_9','#skF_7'))
    | m1_subset_1('#skF_11','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_79,plain,(
    m1_subset_1('#skF_11','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_58,plain,
    ( r2_hidden('#skF_10',k7_relset_1('#skF_8','#skF_6','#skF_9','#skF_7'))
    | r2_hidden('#skF_11','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_74,plain,(
    r2_hidden('#skF_11','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_62,plain,
    ( r2_hidden('#skF_10',k7_relset_1('#skF_8','#skF_6','#skF_9','#skF_7'))
    | r2_hidden(k4_tarski('#skF_11','#skF_10'),'#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_86,plain,(
    r2_hidden(k4_tarski('#skF_11','#skF_10'),'#skF_9') ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_220,plain,(
    ! [D_209,A_210,B_211,E_212] :
      ( r2_hidden(D_209,k9_relat_1(A_210,B_211))
      | ~ r2_hidden(E_212,B_211)
      | ~ r2_hidden(k4_tarski(E_212,D_209),A_210)
      | ~ v1_relat_1(A_210) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_270,plain,(
    ! [D_216,A_217] :
      ( r2_hidden(D_216,k9_relat_1(A_217,'#skF_7'))
      | ~ r2_hidden(k4_tarski('#skF_11',D_216),A_217)
      | ~ v1_relat_1(A_217) ) ),
    inference(resolution,[status(thm)],[c_74,c_220])).

tff(c_280,plain,
    ( r2_hidden('#skF_10',k9_relat_1('#skF_9','#skF_7'))
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_86,c_270])).

tff(c_285,plain,(
    r2_hidden('#skF_10',k9_relat_1('#skF_9','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_280])).

tff(c_202,plain,(
    ! [A_201,B_202,C_203,D_204] :
      ( k7_relset_1(A_201,B_202,C_203,D_204) = k9_relat_1(C_203,D_204)
      | ~ m1_subset_1(C_203,k1_zfmisc_1(k2_zfmisc_1(A_201,B_202))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_209,plain,(
    ! [D_204] : k7_relset_1('#skF_8','#skF_6','#skF_9',D_204) = k9_relat_1('#skF_9',D_204) ),
    inference(resolution,[status(thm)],[c_44,c_202])).

tff(c_52,plain,(
    ! [F_154] :
      ( ~ r2_hidden(F_154,'#skF_7')
      | ~ r2_hidden(k4_tarski(F_154,'#skF_10'),'#skF_9')
      | ~ m1_subset_1(F_154,'#skF_8')
      | ~ r2_hidden('#skF_10',k7_relset_1('#skF_8','#skF_6','#skF_9','#skF_7')) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_303,plain,(
    ! [F_218] :
      ( ~ r2_hidden(F_218,'#skF_7')
      | ~ r2_hidden(k4_tarski(F_218,'#skF_10'),'#skF_9')
      | ~ m1_subset_1(F_218,'#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_285,c_209,c_52])).

tff(c_314,plain,
    ( ~ r2_hidden('#skF_11','#skF_7')
    | ~ m1_subset_1('#skF_11','#skF_8') ),
    inference(resolution,[status(thm)],[c_86,c_303])).

tff(c_324,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_74,c_314])).

tff(c_325,plain,(
    r2_hidden('#skF_10',k7_relset_1('#skF_8','#skF_6','#skF_9','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_381,plain,(
    r2_hidden('#skF_10',k9_relat_1('#skF_9','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_378,c_325])).

tff(c_32,plain,(
    ! [A_53,B_54,C_55] :
      ( r2_hidden('#skF_5'(A_53,B_54,C_55),B_54)
      | ~ r2_hidden(A_53,k9_relat_1(C_55,B_54))
      | ~ v1_relat_1(C_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_450,plain,(
    ! [A_257,B_258,C_259] :
      ( r2_hidden(k4_tarski('#skF_5'(A_257,B_258,C_259),A_257),C_259)
      | ~ r2_hidden(A_257,k9_relat_1(C_259,B_258))
      | ~ v1_relat_1(C_259) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_326,plain,(
    ~ r2_hidden(k4_tarski('#skF_11','#skF_10'),'#skF_9') ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_60,plain,(
    ! [F_154] :
      ( ~ r2_hidden(F_154,'#skF_7')
      | ~ r2_hidden(k4_tarski(F_154,'#skF_10'),'#skF_9')
      | ~ m1_subset_1(F_154,'#skF_8')
      | r2_hidden(k4_tarski('#skF_11','#skF_10'),'#skF_9') ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_421,plain,(
    ! [F_154] :
      ( ~ r2_hidden(F_154,'#skF_7')
      | ~ r2_hidden(k4_tarski(F_154,'#skF_10'),'#skF_9')
      | ~ m1_subset_1(F_154,'#skF_8') ) ),
    inference(negUnitSimplification,[status(thm)],[c_326,c_60])).

tff(c_454,plain,(
    ! [B_258] :
      ( ~ r2_hidden('#skF_5'('#skF_10',B_258,'#skF_9'),'#skF_7')
      | ~ m1_subset_1('#skF_5'('#skF_10',B_258,'#skF_9'),'#skF_8')
      | ~ r2_hidden('#skF_10',k9_relat_1('#skF_9',B_258))
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_450,c_421])).

tff(c_561,plain,(
    ! [B_282] :
      ( ~ r2_hidden('#skF_5'('#skF_10',B_282,'#skF_9'),'#skF_7')
      | ~ m1_subset_1('#skF_5'('#skF_10',B_282,'#skF_9'),'#skF_8')
      | ~ r2_hidden('#skF_10',k9_relat_1('#skF_9',B_282)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_454])).

tff(c_569,plain,
    ( ~ m1_subset_1('#skF_5'('#skF_10','#skF_7','#skF_9'),'#skF_8')
    | ~ r2_hidden('#skF_10',k9_relat_1('#skF_9','#skF_7'))
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_32,c_561])).

tff(c_575,plain,(
    ~ m1_subset_1('#skF_5'('#skF_10','#skF_7','#skF_9'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_381,c_569])).

tff(c_8,plain,(
    ! [C_8,A_5,B_6] :
      ( r2_hidden(C_8,A_5)
      | ~ r2_hidden(C_8,B_6)
      | ~ m1_subset_1(B_6,k1_zfmisc_1(A_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_920,plain,(
    ! [A_338,B_339,C_340,A_341] :
      ( r2_hidden(k4_tarski('#skF_5'(A_338,B_339,C_340),A_338),A_341)
      | ~ m1_subset_1(C_340,k1_zfmisc_1(A_341))
      | ~ r2_hidden(A_338,k9_relat_1(C_340,B_339))
      | ~ v1_relat_1(C_340) ) ),
    inference(resolution,[status(thm)],[c_450,c_8])).

tff(c_6,plain,(
    ! [A_1,C_3,B_2,D_4] :
      ( r2_hidden(A_1,C_3)
      | ~ r2_hidden(k4_tarski(A_1,B_2),k2_zfmisc_1(C_3,D_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1451,plain,(
    ! [C_403,D_401,B_405,A_402,C_404] :
      ( r2_hidden('#skF_5'(A_402,B_405,C_403),C_404)
      | ~ m1_subset_1(C_403,k1_zfmisc_1(k2_zfmisc_1(C_404,D_401)))
      | ~ r2_hidden(A_402,k9_relat_1(C_403,B_405))
      | ~ v1_relat_1(C_403) ) ),
    inference(resolution,[status(thm)],[c_920,c_6])).

tff(c_1486,plain,(
    ! [A_402,B_405] :
      ( r2_hidden('#skF_5'(A_402,B_405,'#skF_9'),'#skF_8')
      | ~ r2_hidden(A_402,k9_relat_1('#skF_9',B_405))
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_44,c_1451])).

tff(c_1501,plain,(
    ! [A_406,B_407] :
      ( r2_hidden('#skF_5'(A_406,B_407,'#skF_9'),'#skF_8')
      | ~ r2_hidden(A_406,k9_relat_1('#skF_9',B_407)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_1486])).

tff(c_10,plain,(
    ! [A_9,B_10] :
      ( m1_subset_1(A_9,B_10)
      | ~ r2_hidden(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_1512,plain,(
    ! [A_408,B_409] :
      ( m1_subset_1('#skF_5'(A_408,B_409,'#skF_9'),'#skF_8')
      | ~ r2_hidden(A_408,k9_relat_1('#skF_9',B_409)) ) ),
    inference(resolution,[status(thm)],[c_1501,c_10])).

tff(c_1563,plain,(
    m1_subset_1('#skF_5'('#skF_10','#skF_7','#skF_9'),'#skF_8') ),
    inference(resolution,[status(thm)],[c_381,c_1512])).

tff(c_1585,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_575,c_1563])).

tff(c_1586,plain,(
    r2_hidden('#skF_10',k7_relset_1('#skF_8','#skF_6','#skF_9','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_1650,plain,(
    r2_hidden('#skF_10',k9_relat_1('#skF_9','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1647,c_1586])).

tff(c_1719,plain,(
    ! [A_456,B_457,C_458] :
      ( r2_hidden(k4_tarski('#skF_5'(A_456,B_457,C_458),A_456),C_458)
      | ~ r2_hidden(A_456,k9_relat_1(C_458,B_457))
      | ~ v1_relat_1(C_458) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_1587,plain,(
    ~ m1_subset_1('#skF_11','#skF_8') ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_64,plain,(
    ! [F_154] :
      ( ~ r2_hidden(F_154,'#skF_7')
      | ~ r2_hidden(k4_tarski(F_154,'#skF_10'),'#skF_9')
      | ~ m1_subset_1(F_154,'#skF_8')
      | m1_subset_1('#skF_11','#skF_8') ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_1632,plain,(
    ! [F_154] :
      ( ~ r2_hidden(F_154,'#skF_7')
      | ~ r2_hidden(k4_tarski(F_154,'#skF_10'),'#skF_9')
      | ~ m1_subset_1(F_154,'#skF_8') ) ),
    inference(negUnitSimplification,[status(thm)],[c_1587,c_64])).

tff(c_1725,plain,(
    ! [B_457] :
      ( ~ r2_hidden('#skF_5'('#skF_10',B_457,'#skF_9'),'#skF_7')
      | ~ m1_subset_1('#skF_5'('#skF_10',B_457,'#skF_9'),'#skF_8')
      | ~ r2_hidden('#skF_10',k9_relat_1('#skF_9',B_457))
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_1719,c_1632])).

tff(c_1827,plain,(
    ! [B_476] :
      ( ~ r2_hidden('#skF_5'('#skF_10',B_476,'#skF_9'),'#skF_7')
      | ~ m1_subset_1('#skF_5'('#skF_10',B_476,'#skF_9'),'#skF_8')
      | ~ r2_hidden('#skF_10',k9_relat_1('#skF_9',B_476)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_1725])).

tff(c_1835,plain,
    ( ~ m1_subset_1('#skF_5'('#skF_10','#skF_7','#skF_9'),'#skF_8')
    | ~ r2_hidden('#skF_10',k9_relat_1('#skF_9','#skF_7'))
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_32,c_1827])).

tff(c_1841,plain,(
    ~ m1_subset_1('#skF_5'('#skF_10','#skF_7','#skF_9'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_1650,c_1835])).

tff(c_2159,plain,(
    ! [A_538,B_539,C_540,A_541] :
      ( r2_hidden(k4_tarski('#skF_5'(A_538,B_539,C_540),A_538),A_541)
      | ~ m1_subset_1(C_540,k1_zfmisc_1(A_541))
      | ~ r2_hidden(A_538,k9_relat_1(C_540,B_539))
      | ~ v1_relat_1(C_540) ) ),
    inference(resolution,[status(thm)],[c_1719,c_8])).

tff(c_2583,plain,(
    ! [C_584,B_587,D_586,C_588,A_585] :
      ( r2_hidden('#skF_5'(A_585,B_587,C_584),C_588)
      | ~ m1_subset_1(C_584,k1_zfmisc_1(k2_zfmisc_1(C_588,D_586)))
      | ~ r2_hidden(A_585,k9_relat_1(C_584,B_587))
      | ~ v1_relat_1(C_584) ) ),
    inference(resolution,[status(thm)],[c_2159,c_6])).

tff(c_2609,plain,(
    ! [A_585,B_587] :
      ( r2_hidden('#skF_5'(A_585,B_587,'#skF_9'),'#skF_8')
      | ~ r2_hidden(A_585,k9_relat_1('#skF_9',B_587))
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_44,c_2583])).

tff(c_2650,plain,(
    ! [A_593,B_594] :
      ( r2_hidden('#skF_5'(A_593,B_594,'#skF_9'),'#skF_8')
      | ~ r2_hidden(A_593,k9_relat_1('#skF_9',B_594)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_2609])).

tff(c_2661,plain,(
    ! [A_595,B_596] :
      ( m1_subset_1('#skF_5'(A_595,B_596,'#skF_9'),'#skF_8')
      | ~ r2_hidden(A_595,k9_relat_1('#skF_9',B_596)) ) ),
    inference(resolution,[status(thm)],[c_2650,c_10])).

tff(c_2712,plain,(
    m1_subset_1('#skF_5'('#skF_10','#skF_7','#skF_9'),'#skF_8') ),
    inference(resolution,[status(thm)],[c_1650,c_2661])).

tff(c_2734,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1841,c_2712])).

tff(c_2735,plain,(
    r2_hidden('#skF_10',k7_relset_1('#skF_8','#skF_6','#skF_9','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_2786,plain,(
    r2_hidden('#skF_10',k9_relat_1('#skF_9','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2783,c_2735])).

tff(c_2849,plain,(
    ! [A_640,B_641,C_642] :
      ( r2_hidden(k4_tarski('#skF_5'(A_640,B_641,C_642),A_640),C_642)
      | ~ r2_hidden(A_640,k9_relat_1(C_642,B_641))
      | ~ v1_relat_1(C_642) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_2736,plain,(
    ~ r2_hidden('#skF_11','#skF_7') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_56,plain,(
    ! [F_154] :
      ( ~ r2_hidden(F_154,'#skF_7')
      | ~ r2_hidden(k4_tarski(F_154,'#skF_10'),'#skF_9')
      | ~ m1_subset_1(F_154,'#skF_8')
      | r2_hidden('#skF_11','#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_2818,plain,(
    ! [F_154] :
      ( ~ r2_hidden(F_154,'#skF_7')
      | ~ r2_hidden(k4_tarski(F_154,'#skF_10'),'#skF_9')
      | ~ m1_subset_1(F_154,'#skF_8') ) ),
    inference(negUnitSimplification,[status(thm)],[c_2736,c_56])).

tff(c_2855,plain,(
    ! [B_641] :
      ( ~ r2_hidden('#skF_5'('#skF_10',B_641,'#skF_9'),'#skF_7')
      | ~ m1_subset_1('#skF_5'('#skF_10',B_641,'#skF_9'),'#skF_8')
      | ~ r2_hidden('#skF_10',k9_relat_1('#skF_9',B_641))
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_2849,c_2818])).

tff(c_2939,plain,(
    ! [B_656] :
      ( ~ r2_hidden('#skF_5'('#skF_10',B_656,'#skF_9'),'#skF_7')
      | ~ m1_subset_1('#skF_5'('#skF_10',B_656,'#skF_9'),'#skF_8')
      | ~ r2_hidden('#skF_10',k9_relat_1('#skF_9',B_656)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_2855])).

tff(c_2943,plain,
    ( ~ m1_subset_1('#skF_5'('#skF_10','#skF_7','#skF_9'),'#skF_8')
    | ~ r2_hidden('#skF_10',k9_relat_1('#skF_9','#skF_7'))
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_32,c_2939])).

tff(c_2946,plain,(
    ~ m1_subset_1('#skF_5'('#skF_10','#skF_7','#skF_9'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_2786,c_2943])).

tff(c_3286,plain,(
    ! [A_712,B_713,C_714,A_715] :
      ( r2_hidden(k4_tarski('#skF_5'(A_712,B_713,C_714),A_712),A_715)
      | ~ m1_subset_1(C_714,k1_zfmisc_1(A_715))
      | ~ r2_hidden(A_712,k9_relat_1(C_714,B_713))
      | ~ v1_relat_1(C_714) ) ),
    inference(resolution,[status(thm)],[c_2849,c_8])).

tff(c_3710,plain,(
    ! [D_768,B_767,A_766,C_770,C_769] :
      ( r2_hidden('#skF_5'(A_766,B_767,C_769),C_770)
      | ~ m1_subset_1(C_769,k1_zfmisc_1(k2_zfmisc_1(C_770,D_768)))
      | ~ r2_hidden(A_766,k9_relat_1(C_769,B_767))
      | ~ v1_relat_1(C_769) ) ),
    inference(resolution,[status(thm)],[c_3286,c_6])).

tff(c_3742,plain,(
    ! [A_766,B_767] :
      ( r2_hidden('#skF_5'(A_766,B_767,'#skF_9'),'#skF_8')
      | ~ r2_hidden(A_766,k9_relat_1('#skF_9',B_767))
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_44,c_3710])).

tff(c_3756,plain,(
    ! [A_771,B_772] :
      ( r2_hidden('#skF_5'(A_771,B_772,'#skF_9'),'#skF_8')
      | ~ r2_hidden(A_771,k9_relat_1('#skF_9',B_772)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_3742])).

tff(c_3767,plain,(
    ! [A_773,B_774] :
      ( m1_subset_1('#skF_5'(A_773,B_774,'#skF_9'),'#skF_8')
      | ~ r2_hidden(A_773,k9_relat_1('#skF_9',B_774)) ) ),
    inference(resolution,[status(thm)],[c_3756,c_10])).

tff(c_3818,plain,(
    m1_subset_1('#skF_5'('#skF_10','#skF_7','#skF_9'),'#skF_8') ),
    inference(resolution,[status(thm)],[c_2786,c_3767])).

tff(c_3840,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2946,c_3818])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n015.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:57:38 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.84/2.16  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.84/2.17  
% 5.84/2.17  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.84/2.17  %$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k7_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_11 > #skF_7 > #skF_10 > #skF_6 > #skF_5 > #skF_2 > #skF_9 > #skF_4 > #skF_8 > #skF_3
% 5.84/2.17  
% 5.84/2.17  %Foreground sorts:
% 5.84/2.17  
% 5.84/2.17  
% 5.84/2.17  %Background operators:
% 5.84/2.17  
% 5.84/2.17  
% 5.84/2.17  %Foreground operators:
% 5.84/2.17  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 5.84/2.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.84/2.17  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.84/2.17  tff('#skF_11', type, '#skF_11': $i).
% 5.84/2.17  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 5.84/2.17  tff('#skF_7', type, '#skF_7': $i).
% 5.84/2.17  tff('#skF_10', type, '#skF_10': $i).
% 5.84/2.17  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 5.84/2.17  tff('#skF_6', type, '#skF_6': $i).
% 5.84/2.17  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 5.84/2.17  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 5.84/2.17  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 5.84/2.17  tff('#skF_9', type, '#skF_9': $i).
% 5.84/2.17  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.84/2.17  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 5.84/2.17  tff('#skF_8', type, '#skF_8': $i).
% 5.84/2.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.84/2.17  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.84/2.17  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.84/2.17  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 5.84/2.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.84/2.17  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.84/2.17  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.84/2.17  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.84/2.17  
% 5.84/2.19  tff(f_101, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (~v1_xboole_0(C) => (![D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, A))) => (![E]: (m1_subset_1(E, A) => (r2_hidden(E, k7_relset_1(C, A, D, B)) <=> (?[F]: ((m1_subset_1(F, C) & r2_hidden(k4_tarski(F, E), D)) & r2_hidden(F, B)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_relset_1)).
% 5.84/2.19  tff(f_70, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 5.84/2.19  tff(f_74, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 5.84/2.19  tff(f_55, axiom, (![A]: (v1_relat_1(A) => (![B, C]: ((C = k9_relat_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E]: (r2_hidden(k4_tarski(E, D), A) & r2_hidden(E, B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d13_relat_1)).
% 5.84/2.19  tff(f_66, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_relat_1)).
% 5.84/2.19  tff(f_38, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 5.84/2.19  tff(f_31, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 5.84/2.19  tff(f_42, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 5.84/2.19  tff(c_44, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_8', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_101])).
% 5.84/2.19  tff(c_68, plain, (![C_157, A_158, B_159]: (v1_relat_1(C_157) | ~m1_subset_1(C_157, k1_zfmisc_1(k2_zfmisc_1(A_158, B_159))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 5.84/2.19  tff(c_72, plain, (v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_44, c_68])).
% 5.84/2.19  tff(c_2780, plain, (![A_619, B_620, C_621, D_622]: (k7_relset_1(A_619, B_620, C_621, D_622)=k9_relat_1(C_621, D_622) | ~m1_subset_1(C_621, k1_zfmisc_1(k2_zfmisc_1(A_619, B_620))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 5.84/2.19  tff(c_2783, plain, (![D_622]: (k7_relset_1('#skF_8', '#skF_6', '#skF_9', D_622)=k9_relat_1('#skF_9', D_622))), inference(resolution, [status(thm)], [c_44, c_2780])).
% 5.84/2.19  tff(c_1644, plain, (![A_437, B_438, C_439, D_440]: (k7_relset_1(A_437, B_438, C_439, D_440)=k9_relat_1(C_439, D_440) | ~m1_subset_1(C_439, k1_zfmisc_1(k2_zfmisc_1(A_437, B_438))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 5.84/2.19  tff(c_1647, plain, (![D_440]: (k7_relset_1('#skF_8', '#skF_6', '#skF_9', D_440)=k9_relat_1('#skF_9', D_440))), inference(resolution, [status(thm)], [c_44, c_1644])).
% 5.84/2.19  tff(c_375, plain, (![A_237, B_238, C_239, D_240]: (k7_relset_1(A_237, B_238, C_239, D_240)=k9_relat_1(C_239, D_240) | ~m1_subset_1(C_239, k1_zfmisc_1(k2_zfmisc_1(A_237, B_238))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 5.84/2.19  tff(c_378, plain, (![D_240]: (k7_relset_1('#skF_8', '#skF_6', '#skF_9', D_240)=k9_relat_1('#skF_9', D_240))), inference(resolution, [status(thm)], [c_44, c_375])).
% 5.84/2.19  tff(c_66, plain, (r2_hidden('#skF_10', k7_relset_1('#skF_8', '#skF_6', '#skF_9', '#skF_7')) | m1_subset_1('#skF_11', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_101])).
% 5.84/2.19  tff(c_79, plain, (m1_subset_1('#skF_11', '#skF_8')), inference(splitLeft, [status(thm)], [c_66])).
% 5.84/2.19  tff(c_58, plain, (r2_hidden('#skF_10', k7_relset_1('#skF_8', '#skF_6', '#skF_9', '#skF_7')) | r2_hidden('#skF_11', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_101])).
% 5.84/2.19  tff(c_74, plain, (r2_hidden('#skF_11', '#skF_7')), inference(splitLeft, [status(thm)], [c_58])).
% 5.84/2.19  tff(c_62, plain, (r2_hidden('#skF_10', k7_relset_1('#skF_8', '#skF_6', '#skF_9', '#skF_7')) | r2_hidden(k4_tarski('#skF_11', '#skF_10'), '#skF_9')), inference(cnfTransformation, [status(thm)], [f_101])).
% 5.84/2.19  tff(c_86, plain, (r2_hidden(k4_tarski('#skF_11', '#skF_10'), '#skF_9')), inference(splitLeft, [status(thm)], [c_62])).
% 5.84/2.19  tff(c_220, plain, (![D_209, A_210, B_211, E_212]: (r2_hidden(D_209, k9_relat_1(A_210, B_211)) | ~r2_hidden(E_212, B_211) | ~r2_hidden(k4_tarski(E_212, D_209), A_210) | ~v1_relat_1(A_210))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.84/2.19  tff(c_270, plain, (![D_216, A_217]: (r2_hidden(D_216, k9_relat_1(A_217, '#skF_7')) | ~r2_hidden(k4_tarski('#skF_11', D_216), A_217) | ~v1_relat_1(A_217))), inference(resolution, [status(thm)], [c_74, c_220])).
% 5.84/2.19  tff(c_280, plain, (r2_hidden('#skF_10', k9_relat_1('#skF_9', '#skF_7')) | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_86, c_270])).
% 5.84/2.19  tff(c_285, plain, (r2_hidden('#skF_10', k9_relat_1('#skF_9', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_280])).
% 5.84/2.19  tff(c_202, plain, (![A_201, B_202, C_203, D_204]: (k7_relset_1(A_201, B_202, C_203, D_204)=k9_relat_1(C_203, D_204) | ~m1_subset_1(C_203, k1_zfmisc_1(k2_zfmisc_1(A_201, B_202))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 5.84/2.19  tff(c_209, plain, (![D_204]: (k7_relset_1('#skF_8', '#skF_6', '#skF_9', D_204)=k9_relat_1('#skF_9', D_204))), inference(resolution, [status(thm)], [c_44, c_202])).
% 5.84/2.19  tff(c_52, plain, (![F_154]: (~r2_hidden(F_154, '#skF_7') | ~r2_hidden(k4_tarski(F_154, '#skF_10'), '#skF_9') | ~m1_subset_1(F_154, '#skF_8') | ~r2_hidden('#skF_10', k7_relset_1('#skF_8', '#skF_6', '#skF_9', '#skF_7')))), inference(cnfTransformation, [status(thm)], [f_101])).
% 5.84/2.19  tff(c_303, plain, (![F_218]: (~r2_hidden(F_218, '#skF_7') | ~r2_hidden(k4_tarski(F_218, '#skF_10'), '#skF_9') | ~m1_subset_1(F_218, '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_285, c_209, c_52])).
% 5.84/2.19  tff(c_314, plain, (~r2_hidden('#skF_11', '#skF_7') | ~m1_subset_1('#skF_11', '#skF_8')), inference(resolution, [status(thm)], [c_86, c_303])).
% 5.84/2.19  tff(c_324, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_79, c_74, c_314])).
% 5.84/2.19  tff(c_325, plain, (r2_hidden('#skF_10', k7_relset_1('#skF_8', '#skF_6', '#skF_9', '#skF_7'))), inference(splitRight, [status(thm)], [c_62])).
% 5.84/2.19  tff(c_381, plain, (r2_hidden('#skF_10', k9_relat_1('#skF_9', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_378, c_325])).
% 5.84/2.19  tff(c_32, plain, (![A_53, B_54, C_55]: (r2_hidden('#skF_5'(A_53, B_54, C_55), B_54) | ~r2_hidden(A_53, k9_relat_1(C_55, B_54)) | ~v1_relat_1(C_55))), inference(cnfTransformation, [status(thm)], [f_66])).
% 5.84/2.19  tff(c_450, plain, (![A_257, B_258, C_259]: (r2_hidden(k4_tarski('#skF_5'(A_257, B_258, C_259), A_257), C_259) | ~r2_hidden(A_257, k9_relat_1(C_259, B_258)) | ~v1_relat_1(C_259))), inference(cnfTransformation, [status(thm)], [f_66])).
% 5.84/2.19  tff(c_326, plain, (~r2_hidden(k4_tarski('#skF_11', '#skF_10'), '#skF_9')), inference(splitRight, [status(thm)], [c_62])).
% 5.84/2.19  tff(c_60, plain, (![F_154]: (~r2_hidden(F_154, '#skF_7') | ~r2_hidden(k4_tarski(F_154, '#skF_10'), '#skF_9') | ~m1_subset_1(F_154, '#skF_8') | r2_hidden(k4_tarski('#skF_11', '#skF_10'), '#skF_9'))), inference(cnfTransformation, [status(thm)], [f_101])).
% 5.84/2.19  tff(c_421, plain, (![F_154]: (~r2_hidden(F_154, '#skF_7') | ~r2_hidden(k4_tarski(F_154, '#skF_10'), '#skF_9') | ~m1_subset_1(F_154, '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_326, c_60])).
% 5.84/2.19  tff(c_454, plain, (![B_258]: (~r2_hidden('#skF_5'('#skF_10', B_258, '#skF_9'), '#skF_7') | ~m1_subset_1('#skF_5'('#skF_10', B_258, '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k9_relat_1('#skF_9', B_258)) | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_450, c_421])).
% 5.84/2.19  tff(c_561, plain, (![B_282]: (~r2_hidden('#skF_5'('#skF_10', B_282, '#skF_9'), '#skF_7') | ~m1_subset_1('#skF_5'('#skF_10', B_282, '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k9_relat_1('#skF_9', B_282)))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_454])).
% 5.84/2.19  tff(c_569, plain, (~m1_subset_1('#skF_5'('#skF_10', '#skF_7', '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k9_relat_1('#skF_9', '#skF_7')) | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_32, c_561])).
% 5.84/2.19  tff(c_575, plain, (~m1_subset_1('#skF_5'('#skF_10', '#skF_7', '#skF_9'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_381, c_569])).
% 5.84/2.19  tff(c_8, plain, (![C_8, A_5, B_6]: (r2_hidden(C_8, A_5) | ~r2_hidden(C_8, B_6) | ~m1_subset_1(B_6, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.84/2.19  tff(c_920, plain, (![A_338, B_339, C_340, A_341]: (r2_hidden(k4_tarski('#skF_5'(A_338, B_339, C_340), A_338), A_341) | ~m1_subset_1(C_340, k1_zfmisc_1(A_341)) | ~r2_hidden(A_338, k9_relat_1(C_340, B_339)) | ~v1_relat_1(C_340))), inference(resolution, [status(thm)], [c_450, c_8])).
% 5.84/2.19  tff(c_6, plain, (![A_1, C_3, B_2, D_4]: (r2_hidden(A_1, C_3) | ~r2_hidden(k4_tarski(A_1, B_2), k2_zfmisc_1(C_3, D_4)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.84/2.19  tff(c_1451, plain, (![C_403, D_401, B_405, A_402, C_404]: (r2_hidden('#skF_5'(A_402, B_405, C_403), C_404) | ~m1_subset_1(C_403, k1_zfmisc_1(k2_zfmisc_1(C_404, D_401))) | ~r2_hidden(A_402, k9_relat_1(C_403, B_405)) | ~v1_relat_1(C_403))), inference(resolution, [status(thm)], [c_920, c_6])).
% 5.84/2.19  tff(c_1486, plain, (![A_402, B_405]: (r2_hidden('#skF_5'(A_402, B_405, '#skF_9'), '#skF_8') | ~r2_hidden(A_402, k9_relat_1('#skF_9', B_405)) | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_44, c_1451])).
% 5.84/2.19  tff(c_1501, plain, (![A_406, B_407]: (r2_hidden('#skF_5'(A_406, B_407, '#skF_9'), '#skF_8') | ~r2_hidden(A_406, k9_relat_1('#skF_9', B_407)))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_1486])).
% 5.84/2.19  tff(c_10, plain, (![A_9, B_10]: (m1_subset_1(A_9, B_10) | ~r2_hidden(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_42])).
% 5.84/2.19  tff(c_1512, plain, (![A_408, B_409]: (m1_subset_1('#skF_5'(A_408, B_409, '#skF_9'), '#skF_8') | ~r2_hidden(A_408, k9_relat_1('#skF_9', B_409)))), inference(resolution, [status(thm)], [c_1501, c_10])).
% 5.84/2.19  tff(c_1563, plain, (m1_subset_1('#skF_5'('#skF_10', '#skF_7', '#skF_9'), '#skF_8')), inference(resolution, [status(thm)], [c_381, c_1512])).
% 5.84/2.19  tff(c_1585, plain, $false, inference(negUnitSimplification, [status(thm)], [c_575, c_1563])).
% 5.84/2.19  tff(c_1586, plain, (r2_hidden('#skF_10', k7_relset_1('#skF_8', '#skF_6', '#skF_9', '#skF_7'))), inference(splitRight, [status(thm)], [c_66])).
% 5.84/2.19  tff(c_1650, plain, (r2_hidden('#skF_10', k9_relat_1('#skF_9', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_1647, c_1586])).
% 5.84/2.19  tff(c_1719, plain, (![A_456, B_457, C_458]: (r2_hidden(k4_tarski('#skF_5'(A_456, B_457, C_458), A_456), C_458) | ~r2_hidden(A_456, k9_relat_1(C_458, B_457)) | ~v1_relat_1(C_458))), inference(cnfTransformation, [status(thm)], [f_66])).
% 5.84/2.19  tff(c_1587, plain, (~m1_subset_1('#skF_11', '#skF_8')), inference(splitRight, [status(thm)], [c_66])).
% 5.84/2.19  tff(c_64, plain, (![F_154]: (~r2_hidden(F_154, '#skF_7') | ~r2_hidden(k4_tarski(F_154, '#skF_10'), '#skF_9') | ~m1_subset_1(F_154, '#skF_8') | m1_subset_1('#skF_11', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_101])).
% 5.84/2.19  tff(c_1632, plain, (![F_154]: (~r2_hidden(F_154, '#skF_7') | ~r2_hidden(k4_tarski(F_154, '#skF_10'), '#skF_9') | ~m1_subset_1(F_154, '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_1587, c_64])).
% 5.84/2.19  tff(c_1725, plain, (![B_457]: (~r2_hidden('#skF_5'('#skF_10', B_457, '#skF_9'), '#skF_7') | ~m1_subset_1('#skF_5'('#skF_10', B_457, '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k9_relat_1('#skF_9', B_457)) | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_1719, c_1632])).
% 5.84/2.19  tff(c_1827, plain, (![B_476]: (~r2_hidden('#skF_5'('#skF_10', B_476, '#skF_9'), '#skF_7') | ~m1_subset_1('#skF_5'('#skF_10', B_476, '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k9_relat_1('#skF_9', B_476)))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_1725])).
% 5.84/2.19  tff(c_1835, plain, (~m1_subset_1('#skF_5'('#skF_10', '#skF_7', '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k9_relat_1('#skF_9', '#skF_7')) | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_32, c_1827])).
% 5.84/2.19  tff(c_1841, plain, (~m1_subset_1('#skF_5'('#skF_10', '#skF_7', '#skF_9'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_1650, c_1835])).
% 5.84/2.19  tff(c_2159, plain, (![A_538, B_539, C_540, A_541]: (r2_hidden(k4_tarski('#skF_5'(A_538, B_539, C_540), A_538), A_541) | ~m1_subset_1(C_540, k1_zfmisc_1(A_541)) | ~r2_hidden(A_538, k9_relat_1(C_540, B_539)) | ~v1_relat_1(C_540))), inference(resolution, [status(thm)], [c_1719, c_8])).
% 5.84/2.19  tff(c_2583, plain, (![C_584, B_587, D_586, C_588, A_585]: (r2_hidden('#skF_5'(A_585, B_587, C_584), C_588) | ~m1_subset_1(C_584, k1_zfmisc_1(k2_zfmisc_1(C_588, D_586))) | ~r2_hidden(A_585, k9_relat_1(C_584, B_587)) | ~v1_relat_1(C_584))), inference(resolution, [status(thm)], [c_2159, c_6])).
% 5.84/2.19  tff(c_2609, plain, (![A_585, B_587]: (r2_hidden('#skF_5'(A_585, B_587, '#skF_9'), '#skF_8') | ~r2_hidden(A_585, k9_relat_1('#skF_9', B_587)) | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_44, c_2583])).
% 5.84/2.19  tff(c_2650, plain, (![A_593, B_594]: (r2_hidden('#skF_5'(A_593, B_594, '#skF_9'), '#skF_8') | ~r2_hidden(A_593, k9_relat_1('#skF_9', B_594)))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_2609])).
% 5.84/2.19  tff(c_2661, plain, (![A_595, B_596]: (m1_subset_1('#skF_5'(A_595, B_596, '#skF_9'), '#skF_8') | ~r2_hidden(A_595, k9_relat_1('#skF_9', B_596)))), inference(resolution, [status(thm)], [c_2650, c_10])).
% 5.84/2.19  tff(c_2712, plain, (m1_subset_1('#skF_5'('#skF_10', '#skF_7', '#skF_9'), '#skF_8')), inference(resolution, [status(thm)], [c_1650, c_2661])).
% 5.84/2.19  tff(c_2734, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1841, c_2712])).
% 5.84/2.19  tff(c_2735, plain, (r2_hidden('#skF_10', k7_relset_1('#skF_8', '#skF_6', '#skF_9', '#skF_7'))), inference(splitRight, [status(thm)], [c_58])).
% 5.84/2.19  tff(c_2786, plain, (r2_hidden('#skF_10', k9_relat_1('#skF_9', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_2783, c_2735])).
% 5.84/2.19  tff(c_2849, plain, (![A_640, B_641, C_642]: (r2_hidden(k4_tarski('#skF_5'(A_640, B_641, C_642), A_640), C_642) | ~r2_hidden(A_640, k9_relat_1(C_642, B_641)) | ~v1_relat_1(C_642))), inference(cnfTransformation, [status(thm)], [f_66])).
% 5.84/2.19  tff(c_2736, plain, (~r2_hidden('#skF_11', '#skF_7')), inference(splitRight, [status(thm)], [c_58])).
% 5.84/2.19  tff(c_56, plain, (![F_154]: (~r2_hidden(F_154, '#skF_7') | ~r2_hidden(k4_tarski(F_154, '#skF_10'), '#skF_9') | ~m1_subset_1(F_154, '#skF_8') | r2_hidden('#skF_11', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_101])).
% 5.84/2.19  tff(c_2818, plain, (![F_154]: (~r2_hidden(F_154, '#skF_7') | ~r2_hidden(k4_tarski(F_154, '#skF_10'), '#skF_9') | ~m1_subset_1(F_154, '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_2736, c_56])).
% 5.84/2.19  tff(c_2855, plain, (![B_641]: (~r2_hidden('#skF_5'('#skF_10', B_641, '#skF_9'), '#skF_7') | ~m1_subset_1('#skF_5'('#skF_10', B_641, '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k9_relat_1('#skF_9', B_641)) | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_2849, c_2818])).
% 5.84/2.19  tff(c_2939, plain, (![B_656]: (~r2_hidden('#skF_5'('#skF_10', B_656, '#skF_9'), '#skF_7') | ~m1_subset_1('#skF_5'('#skF_10', B_656, '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k9_relat_1('#skF_9', B_656)))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_2855])).
% 5.84/2.19  tff(c_2943, plain, (~m1_subset_1('#skF_5'('#skF_10', '#skF_7', '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k9_relat_1('#skF_9', '#skF_7')) | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_32, c_2939])).
% 5.84/2.19  tff(c_2946, plain, (~m1_subset_1('#skF_5'('#skF_10', '#skF_7', '#skF_9'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_2786, c_2943])).
% 5.84/2.19  tff(c_3286, plain, (![A_712, B_713, C_714, A_715]: (r2_hidden(k4_tarski('#skF_5'(A_712, B_713, C_714), A_712), A_715) | ~m1_subset_1(C_714, k1_zfmisc_1(A_715)) | ~r2_hidden(A_712, k9_relat_1(C_714, B_713)) | ~v1_relat_1(C_714))), inference(resolution, [status(thm)], [c_2849, c_8])).
% 5.84/2.19  tff(c_3710, plain, (![D_768, B_767, A_766, C_770, C_769]: (r2_hidden('#skF_5'(A_766, B_767, C_769), C_770) | ~m1_subset_1(C_769, k1_zfmisc_1(k2_zfmisc_1(C_770, D_768))) | ~r2_hidden(A_766, k9_relat_1(C_769, B_767)) | ~v1_relat_1(C_769))), inference(resolution, [status(thm)], [c_3286, c_6])).
% 5.84/2.19  tff(c_3742, plain, (![A_766, B_767]: (r2_hidden('#skF_5'(A_766, B_767, '#skF_9'), '#skF_8') | ~r2_hidden(A_766, k9_relat_1('#skF_9', B_767)) | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_44, c_3710])).
% 5.84/2.19  tff(c_3756, plain, (![A_771, B_772]: (r2_hidden('#skF_5'(A_771, B_772, '#skF_9'), '#skF_8') | ~r2_hidden(A_771, k9_relat_1('#skF_9', B_772)))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_3742])).
% 5.84/2.19  tff(c_3767, plain, (![A_773, B_774]: (m1_subset_1('#skF_5'(A_773, B_774, '#skF_9'), '#skF_8') | ~r2_hidden(A_773, k9_relat_1('#skF_9', B_774)))), inference(resolution, [status(thm)], [c_3756, c_10])).
% 5.84/2.19  tff(c_3818, plain, (m1_subset_1('#skF_5'('#skF_10', '#skF_7', '#skF_9'), '#skF_8')), inference(resolution, [status(thm)], [c_2786, c_3767])).
% 5.84/2.19  tff(c_3840, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2946, c_3818])).
% 5.84/2.19  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.84/2.19  
% 5.84/2.19  Inference rules
% 5.84/2.19  ----------------------
% 5.84/2.19  #Ref     : 0
% 5.84/2.19  #Sup     : 828
% 5.84/2.19  #Fact    : 0
% 5.84/2.19  #Define  : 0
% 5.84/2.19  #Split   : 9
% 5.84/2.19  #Chain   : 0
% 5.84/2.19  #Close   : 0
% 5.84/2.19  
% 5.84/2.19  Ordering : KBO
% 5.84/2.19  
% 5.84/2.19  Simplification rules
% 5.84/2.19  ----------------------
% 5.84/2.19  #Subsume      : 34
% 5.84/2.19  #Demod        : 87
% 5.84/2.19  #Tautology    : 38
% 5.84/2.19  #SimpNegUnit  : 6
% 5.84/2.19  #BackRed      : 9
% 5.84/2.19  
% 5.84/2.19  #Partial instantiations: 0
% 5.84/2.19  #Strategies tried      : 1
% 5.84/2.19  
% 5.84/2.19  Timing (in seconds)
% 5.84/2.19  ----------------------
% 5.84/2.20  Preprocessing        : 0.32
% 5.84/2.20  Parsing              : 0.16
% 5.84/2.20  CNF conversion       : 0.04
% 5.84/2.20  Main loop            : 1.04
% 5.84/2.20  Inferencing          : 0.41
% 5.84/2.20  Reduction            : 0.27
% 5.84/2.20  Demodulation         : 0.18
% 5.84/2.20  BG Simplification    : 0.05
% 5.84/2.20  Subsumption          : 0.21
% 5.84/2.20  Abstraction          : 0.06
% 5.84/2.20  MUC search           : 0.00
% 5.84/2.20  Cooper               : 0.00
% 5.84/2.20  Total                : 1.41
% 5.84/2.20  Index Insertion      : 0.00
% 5.84/2.20  Index Deletion       : 0.00
% 5.84/2.20  Index Matching       : 0.00
% 5.84/2.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
