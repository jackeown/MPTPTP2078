%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:33 EST 2020

% Result     : Theorem 4.68s
% Output     : CNFRefutation 4.68s
% Verified   : 
% Statistics : Number of formulae       :  131 ( 302 expanded)
%              Number of leaves         :   38 ( 118 expanded)
%              Depth                    :    9
%              Number of atoms          :  248 ( 849 expanded)
%              Number of equality atoms :   10 (  22 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k7_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_11 > #skF_6 > #skF_4 > #skF_7 > #skF_10 > #skF_2 > #skF_9 > #skF_8 > #skF_5 > #skF_3 > #skF_1 > #skF_12

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_112,negated_conjecture,(
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

tff(f_81,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_64,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_43,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_85,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_56,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( C = k9_relat_1(A,B)
        <=> ! [D] :
              ( r2_hidden(D,C)
            <=> ? [E] :
                  ( r2_hidden(k4_tarski(E,D),A)
                  & r2_hidden(E,B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_relat_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(c_52,plain,(
    m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_9','#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_1680,plain,(
    ! [C_505,A_506,B_507] :
      ( v4_relat_1(C_505,A_506)
      | ~ m1_subset_1(C_505,k1_zfmisc_1(k2_zfmisc_1(A_506,B_507))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_1689,plain,(
    v4_relat_1('#skF_10','#skF_9') ),
    inference(resolution,[status(thm)],[c_52,c_1680])).

tff(c_34,plain,(
    ! [A_55,B_56] : v1_relat_1(k2_zfmisc_1(A_55,B_56)) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_77,plain,(
    ! [B_163,A_164] :
      ( v1_relat_1(B_163)
      | ~ m1_subset_1(B_163,k1_zfmisc_1(A_164))
      | ~ v1_relat_1(A_164) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_80,plain,
    ( v1_relat_1('#skF_10')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_9','#skF_7')) ),
    inference(resolution,[status(thm)],[c_52,c_77])).

tff(c_83,plain,(
    v1_relat_1('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_80])).

tff(c_1788,plain,(
    ! [A_536,B_537,C_538,D_539] :
      ( k7_relset_1(A_536,B_537,C_538,D_539) = k9_relat_1(C_538,D_539)
      | ~ m1_subset_1(C_538,k1_zfmisc_1(k2_zfmisc_1(A_536,B_537))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_1799,plain,(
    ! [D_539] : k7_relset_1('#skF_9','#skF_7','#skF_10',D_539) = k9_relat_1('#skF_10',D_539) ),
    inference(resolution,[status(thm)],[c_52,c_1788])).

tff(c_117,plain,(
    ! [C_175,A_176,B_177] :
      ( v4_relat_1(C_175,A_176)
      | ~ m1_subset_1(C_175,k1_zfmisc_1(k2_zfmisc_1(A_176,B_177))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_126,plain,(
    v4_relat_1('#skF_10','#skF_9') ),
    inference(resolution,[status(thm)],[c_52,c_117])).

tff(c_1137,plain,(
    ! [A_398,B_399,C_400,D_401] :
      ( k7_relset_1(A_398,B_399,C_400,D_401) = k9_relat_1(C_400,D_401)
      | ~ m1_subset_1(C_400,k1_zfmisc_1(k2_zfmisc_1(A_398,B_399))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_1148,plain,(
    ! [D_401] : k7_relset_1('#skF_9','#skF_7','#skF_10',D_401) = k9_relat_1('#skF_10',D_401) ),
    inference(resolution,[status(thm)],[c_52,c_1137])).

tff(c_477,plain,(
    ! [A_266,B_267,C_268,D_269] :
      ( k7_relset_1(A_266,B_267,C_268,D_269) = k9_relat_1(C_268,D_269)
      | ~ m1_subset_1(C_268,k1_zfmisc_1(k2_zfmisc_1(A_266,B_267))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_488,plain,(
    ! [D_269] : k7_relset_1('#skF_9','#skF_7','#skF_10',D_269) = k9_relat_1('#skF_10',D_269) ),
    inference(resolution,[status(thm)],[c_52,c_477])).

tff(c_90,plain,(
    ! [A_167,B_168] :
      ( r2_hidden('#skF_1'(A_167,B_168),A_167)
      | r1_tarski(A_167,B_168) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_98,plain,(
    ! [A_167] : r1_tarski(A_167,A_167) ),
    inference(resolution,[status(thm)],[c_90,c_4])).

tff(c_74,plain,
    ( r2_hidden('#skF_11',k7_relset_1('#skF_9','#skF_7','#skF_10','#skF_8'))
    | m1_subset_1('#skF_12','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_127,plain,(
    m1_subset_1('#skF_12','#skF_9') ),
    inference(splitLeft,[status(thm)],[c_74])).

tff(c_66,plain,
    ( r2_hidden('#skF_11',k7_relset_1('#skF_9','#skF_7','#skF_10','#skF_8'))
    | r2_hidden('#skF_12','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_84,plain,(
    r2_hidden('#skF_12','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_70,plain,
    ( r2_hidden('#skF_11',k7_relset_1('#skF_9','#skF_7','#skF_10','#skF_8'))
    | r2_hidden(k4_tarski('#skF_12','#skF_11'),'#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_169,plain,(
    r2_hidden(k4_tarski('#skF_12','#skF_11'),'#skF_10') ),
    inference(splitLeft,[status(thm)],[c_70])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_175,plain,(
    ! [B_2] :
      ( r2_hidden(k4_tarski('#skF_12','#skF_11'),B_2)
      | ~ r1_tarski('#skF_10',B_2) ) ),
    inference(resolution,[status(thm)],[c_169,c_2])).

tff(c_320,plain,(
    ! [D_234,A_235,B_236,E_237] :
      ( r2_hidden(D_234,k9_relat_1(A_235,B_236))
      | ~ r2_hidden(E_237,B_236)
      | ~ r2_hidden(k4_tarski(E_237,D_234),A_235)
      | ~ v1_relat_1(A_235) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_345,plain,(
    ! [D_238,A_239] :
      ( r2_hidden(D_238,k9_relat_1(A_239,'#skF_8'))
      | ~ r2_hidden(k4_tarski('#skF_12',D_238),A_239)
      | ~ v1_relat_1(A_239) ) ),
    inference(resolution,[status(thm)],[c_84,c_320])).

tff(c_351,plain,
    ( r2_hidden('#skF_11',k9_relat_1('#skF_10','#skF_8'))
    | ~ v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_169,c_345])).

tff(c_355,plain,(
    r2_hidden('#skF_11',k9_relat_1('#skF_10','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_351])).

tff(c_293,plain,(
    ! [A_223,B_224,C_225,D_226] :
      ( k7_relset_1(A_223,B_224,C_225,D_226) = k9_relat_1(C_225,D_226)
      | ~ m1_subset_1(C_225,k1_zfmisc_1(k2_zfmisc_1(A_223,B_224))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_308,plain,(
    ! [D_226] : k7_relset_1('#skF_9','#skF_7','#skF_10',D_226) = k9_relat_1('#skF_10',D_226) ),
    inference(resolution,[status(thm)],[c_52,c_293])).

tff(c_60,plain,(
    ! [F_158] :
      ( ~ r2_hidden(F_158,'#skF_8')
      | ~ r2_hidden(k4_tarski(F_158,'#skF_11'),'#skF_10')
      | ~ m1_subset_1(F_158,'#skF_9')
      | ~ r2_hidden('#skF_11',k7_relset_1('#skF_9','#skF_7','#skF_10','#skF_8')) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_373,plain,(
    ! [F_240] :
      ( ~ r2_hidden(F_240,'#skF_8')
      | ~ r2_hidden(k4_tarski(F_240,'#skF_11'),'#skF_10')
      | ~ m1_subset_1(F_240,'#skF_9') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_355,c_308,c_60])).

tff(c_377,plain,
    ( ~ r2_hidden('#skF_12','#skF_8')
    | ~ m1_subset_1('#skF_12','#skF_9')
    | ~ r1_tarski('#skF_10','#skF_10') ),
    inference(resolution,[status(thm)],[c_175,c_373])).

tff(c_384,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_127,c_84,c_377])).

tff(c_385,plain,(
    r2_hidden('#skF_11',k7_relset_1('#skF_9','#skF_7','#skF_10','#skF_8')) ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_491,plain,(
    r2_hidden('#skF_11',k9_relat_1('#skF_10','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_488,c_385])).

tff(c_32,plain,(
    ! [B_54,A_53] :
      ( r1_tarski(k1_relat_1(B_54),A_53)
      | ~ v4_relat_1(B_54,A_53)
      | ~ v1_relat_1(B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_469,plain,(
    ! [A_263,B_264,C_265] :
      ( r2_hidden('#skF_6'(A_263,B_264,C_265),k1_relat_1(C_265))
      | ~ r2_hidden(A_263,k9_relat_1(C_265,B_264))
      | ~ v1_relat_1(C_265) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_812,plain,(
    ! [A_341,B_342,C_343,B_344] :
      ( r2_hidden('#skF_6'(A_341,B_342,C_343),B_344)
      | ~ r1_tarski(k1_relat_1(C_343),B_344)
      | ~ r2_hidden(A_341,k9_relat_1(C_343,B_342))
      | ~ v1_relat_1(C_343) ) ),
    inference(resolution,[status(thm)],[c_469,c_2])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(A_6,B_7)
      | ~ r2_hidden(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_888,plain,(
    ! [A_352,B_353,C_354,B_355] :
      ( m1_subset_1('#skF_6'(A_352,B_353,C_354),B_355)
      | ~ r1_tarski(k1_relat_1(C_354),B_355)
      | ~ r2_hidden(A_352,k9_relat_1(C_354,B_353))
      | ~ v1_relat_1(C_354) ) ),
    inference(resolution,[status(thm)],[c_812,c_8])).

tff(c_932,plain,(
    ! [A_358,B_359,B_360,A_361] :
      ( m1_subset_1('#skF_6'(A_358,B_359,B_360),A_361)
      | ~ r2_hidden(A_358,k9_relat_1(B_360,B_359))
      | ~ v4_relat_1(B_360,A_361)
      | ~ v1_relat_1(B_360) ) ),
    inference(resolution,[status(thm)],[c_32,c_888])).

tff(c_959,plain,(
    ! [A_361] :
      ( m1_subset_1('#skF_6'('#skF_11','#skF_8','#skF_10'),A_361)
      | ~ v4_relat_1('#skF_10',A_361)
      | ~ v1_relat_1('#skF_10') ) ),
    inference(resolution,[status(thm)],[c_491,c_932])).

tff(c_988,plain,(
    ! [A_362] :
      ( m1_subset_1('#skF_6'('#skF_11','#skF_8','#skF_10'),A_362)
      | ~ v4_relat_1('#skF_10',A_362) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_959])).

tff(c_38,plain,(
    ! [A_57,B_58,C_59] :
      ( r2_hidden('#skF_6'(A_57,B_58,C_59),B_58)
      | ~ r2_hidden(A_57,k9_relat_1(C_59,B_58))
      | ~ v1_relat_1(C_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_531,plain,(
    ! [A_280,B_281,C_282] :
      ( r2_hidden(k4_tarski('#skF_6'(A_280,B_281,C_282),A_280),C_282)
      | ~ r2_hidden(A_280,k9_relat_1(C_282,B_281))
      | ~ v1_relat_1(C_282) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_386,plain,(
    ~ r2_hidden(k4_tarski('#skF_12','#skF_11'),'#skF_10') ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_68,plain,(
    ! [F_158] :
      ( ~ r2_hidden(F_158,'#skF_8')
      | ~ r2_hidden(k4_tarski(F_158,'#skF_11'),'#skF_10')
      | ~ m1_subset_1(F_158,'#skF_9')
      | r2_hidden(k4_tarski('#skF_12','#skF_11'),'#skF_10') ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_514,plain,(
    ! [F_158] :
      ( ~ r2_hidden(F_158,'#skF_8')
      | ~ r2_hidden(k4_tarski(F_158,'#skF_11'),'#skF_10')
      | ~ m1_subset_1(F_158,'#skF_9') ) ),
    inference(negUnitSimplification,[status(thm)],[c_386,c_68])).

tff(c_535,plain,(
    ! [B_281] :
      ( ~ r2_hidden('#skF_6'('#skF_11',B_281,'#skF_10'),'#skF_8')
      | ~ m1_subset_1('#skF_6'('#skF_11',B_281,'#skF_10'),'#skF_9')
      | ~ r2_hidden('#skF_11',k9_relat_1('#skF_10',B_281))
      | ~ v1_relat_1('#skF_10') ) ),
    inference(resolution,[status(thm)],[c_531,c_514])).

tff(c_678,plain,(
    ! [B_320] :
      ( ~ r2_hidden('#skF_6'('#skF_11',B_320,'#skF_10'),'#skF_8')
      | ~ m1_subset_1('#skF_6'('#skF_11',B_320,'#skF_10'),'#skF_9')
      | ~ r2_hidden('#skF_11',k9_relat_1('#skF_10',B_320)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_535])).

tff(c_686,plain,
    ( ~ m1_subset_1('#skF_6'('#skF_11','#skF_8','#skF_10'),'#skF_9')
    | ~ r2_hidden('#skF_11',k9_relat_1('#skF_10','#skF_8'))
    | ~ v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_38,c_678])).

tff(c_692,plain,(
    ~ m1_subset_1('#skF_6'('#skF_11','#skF_8','#skF_10'),'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_491,c_686])).

tff(c_991,plain,(
    ~ v4_relat_1('#skF_10','#skF_9') ),
    inference(resolution,[status(thm)],[c_988,c_692])).

tff(c_1010,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_991])).

tff(c_1011,plain,(
    r2_hidden('#skF_11',k7_relset_1('#skF_9','#skF_7','#skF_10','#skF_8')) ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_1152,plain,(
    r2_hidden('#skF_11',k9_relat_1('#skF_10','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1148,c_1011])).

tff(c_1182,plain,(
    ! [A_404,B_405,C_406] :
      ( r2_hidden('#skF_6'(A_404,B_405,C_406),k1_relat_1(C_406))
      | ~ r2_hidden(A_404,k9_relat_1(C_406,B_405))
      | ~ v1_relat_1(C_406) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_1492,plain,(
    ! [A_479,B_480,C_481,B_482] :
      ( r2_hidden('#skF_6'(A_479,B_480,C_481),B_482)
      | ~ r1_tarski(k1_relat_1(C_481),B_482)
      | ~ r2_hidden(A_479,k9_relat_1(C_481,B_480))
      | ~ v1_relat_1(C_481) ) ),
    inference(resolution,[status(thm)],[c_1182,c_2])).

tff(c_1570,plain,(
    ! [A_487,B_488,C_489,B_490] :
      ( m1_subset_1('#skF_6'(A_487,B_488,C_489),B_490)
      | ~ r1_tarski(k1_relat_1(C_489),B_490)
      | ~ r2_hidden(A_487,k9_relat_1(C_489,B_488))
      | ~ v1_relat_1(C_489) ) ),
    inference(resolution,[status(thm)],[c_1492,c_8])).

tff(c_1578,plain,(
    ! [A_491,B_492,B_493,A_494] :
      ( m1_subset_1('#skF_6'(A_491,B_492,B_493),A_494)
      | ~ r2_hidden(A_491,k9_relat_1(B_493,B_492))
      | ~ v4_relat_1(B_493,A_494)
      | ~ v1_relat_1(B_493) ) ),
    inference(resolution,[status(thm)],[c_32,c_1570])).

tff(c_1603,plain,(
    ! [A_494] :
      ( m1_subset_1('#skF_6'('#skF_11','#skF_8','#skF_10'),A_494)
      | ~ v4_relat_1('#skF_10',A_494)
      | ~ v1_relat_1('#skF_10') ) ),
    inference(resolution,[status(thm)],[c_1152,c_1578])).

tff(c_1631,plain,(
    ! [A_495] :
      ( m1_subset_1('#skF_6'('#skF_11','#skF_8','#skF_10'),A_495)
      | ~ v4_relat_1('#skF_10',A_495) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_1603])).

tff(c_1191,plain,(
    ! [A_410,B_411,C_412] :
      ( r2_hidden(k4_tarski('#skF_6'(A_410,B_411,C_412),A_410),C_412)
      | ~ r2_hidden(A_410,k9_relat_1(C_412,B_411))
      | ~ v1_relat_1(C_412) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_1012,plain,(
    ~ m1_subset_1('#skF_12','#skF_9') ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_72,plain,(
    ! [F_158] :
      ( ~ r2_hidden(F_158,'#skF_8')
      | ~ r2_hidden(k4_tarski(F_158,'#skF_11'),'#skF_10')
      | ~ m1_subset_1(F_158,'#skF_9')
      | m1_subset_1('#skF_12','#skF_9') ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_1107,plain,(
    ! [F_158] :
      ( ~ r2_hidden(F_158,'#skF_8')
      | ~ r2_hidden(k4_tarski(F_158,'#skF_11'),'#skF_10')
      | ~ m1_subset_1(F_158,'#skF_9') ) ),
    inference(negUnitSimplification,[status(thm)],[c_1012,c_72])).

tff(c_1198,plain,(
    ! [B_411] :
      ( ~ r2_hidden('#skF_6'('#skF_11',B_411,'#skF_10'),'#skF_8')
      | ~ m1_subset_1('#skF_6'('#skF_11',B_411,'#skF_10'),'#skF_9')
      | ~ r2_hidden('#skF_11',k9_relat_1('#skF_10',B_411))
      | ~ v1_relat_1('#skF_10') ) ),
    inference(resolution,[status(thm)],[c_1191,c_1107])).

tff(c_1330,plain,(
    ! [B_450] :
      ( ~ r2_hidden('#skF_6'('#skF_11',B_450,'#skF_10'),'#skF_8')
      | ~ m1_subset_1('#skF_6'('#skF_11',B_450,'#skF_10'),'#skF_9')
      | ~ r2_hidden('#skF_11',k9_relat_1('#skF_10',B_450)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_1198])).

tff(c_1334,plain,
    ( ~ m1_subset_1('#skF_6'('#skF_11','#skF_8','#skF_10'),'#skF_9')
    | ~ r2_hidden('#skF_11',k9_relat_1('#skF_10','#skF_8'))
    | ~ v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_38,c_1330])).

tff(c_1337,plain,(
    ~ m1_subset_1('#skF_6'('#skF_11','#skF_8','#skF_10'),'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_1152,c_1334])).

tff(c_1634,plain,(
    ~ v4_relat_1('#skF_10','#skF_9') ),
    inference(resolution,[status(thm)],[c_1631,c_1337])).

tff(c_1653,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_1634])).

tff(c_1654,plain,(
    r2_hidden('#skF_11',k7_relset_1('#skF_9','#skF_7','#skF_10','#skF_8')) ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_1802,plain,(
    r2_hidden('#skF_11',k9_relat_1('#skF_10','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1799,c_1654])).

tff(c_1825,plain,(
    ! [A_541,B_542,C_543] :
      ( r2_hidden('#skF_6'(A_541,B_542,C_543),k1_relat_1(C_543))
      | ~ r2_hidden(A_541,k9_relat_1(C_543,B_542))
      | ~ v1_relat_1(C_543) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_2151,plain,(
    ! [A_608,B_609,C_610,B_611] :
      ( r2_hidden('#skF_6'(A_608,B_609,C_610),B_611)
      | ~ r1_tarski(k1_relat_1(C_610),B_611)
      | ~ r2_hidden(A_608,k9_relat_1(C_610,B_609))
      | ~ v1_relat_1(C_610) ) ),
    inference(resolution,[status(thm)],[c_1825,c_2])).

tff(c_2218,plain,(
    ! [A_620,B_621,C_622,B_623] :
      ( m1_subset_1('#skF_6'(A_620,B_621,C_622),B_623)
      | ~ r1_tarski(k1_relat_1(C_622),B_623)
      | ~ r2_hidden(A_620,k9_relat_1(C_622,B_621))
      | ~ v1_relat_1(C_622) ) ),
    inference(resolution,[status(thm)],[c_2151,c_8])).

tff(c_2245,plain,(
    ! [A_627,B_628,B_629,A_630] :
      ( m1_subset_1('#skF_6'(A_627,B_628,B_629),A_630)
      | ~ r2_hidden(A_627,k9_relat_1(B_629,B_628))
      | ~ v4_relat_1(B_629,A_630)
      | ~ v1_relat_1(B_629) ) ),
    inference(resolution,[status(thm)],[c_32,c_2218])).

tff(c_2273,plain,(
    ! [A_630] :
      ( m1_subset_1('#skF_6'('#skF_11','#skF_8','#skF_10'),A_630)
      | ~ v4_relat_1('#skF_10',A_630)
      | ~ v1_relat_1('#skF_10') ) ),
    inference(resolution,[status(thm)],[c_1802,c_2245])).

tff(c_2298,plain,(
    ! [A_631] :
      ( m1_subset_1('#skF_6'('#skF_11','#skF_8','#skF_10'),A_631)
      | ~ v4_relat_1('#skF_10',A_631) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_2273])).

tff(c_1904,plain,(
    ! [A_574,B_575,C_576] :
      ( r2_hidden(k4_tarski('#skF_6'(A_574,B_575,C_576),A_574),C_576)
      | ~ r2_hidden(A_574,k9_relat_1(C_576,B_575))
      | ~ v1_relat_1(C_576) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_1655,plain,(
    ~ r2_hidden('#skF_12','#skF_8') ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_64,plain,(
    ! [F_158] :
      ( ~ r2_hidden(F_158,'#skF_8')
      | ~ r2_hidden(k4_tarski(F_158,'#skF_11'),'#skF_10')
      | ~ m1_subset_1(F_158,'#skF_9')
      | r2_hidden('#skF_12','#skF_8') ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_1786,plain,(
    ! [F_158] :
      ( ~ r2_hidden(F_158,'#skF_8')
      | ~ r2_hidden(k4_tarski(F_158,'#skF_11'),'#skF_10')
      | ~ m1_subset_1(F_158,'#skF_9') ) ),
    inference(negUnitSimplification,[status(thm)],[c_1655,c_64])).

tff(c_1910,plain,(
    ! [B_575] :
      ( ~ r2_hidden('#skF_6'('#skF_11',B_575,'#skF_10'),'#skF_8')
      | ~ m1_subset_1('#skF_6'('#skF_11',B_575,'#skF_10'),'#skF_9')
      | ~ r2_hidden('#skF_11',k9_relat_1('#skF_10',B_575))
      | ~ v1_relat_1('#skF_10') ) ),
    inference(resolution,[status(thm)],[c_1904,c_1786])).

tff(c_2090,plain,(
    ! [B_599] :
      ( ~ r2_hidden('#skF_6'('#skF_11',B_599,'#skF_10'),'#skF_8')
      | ~ m1_subset_1('#skF_6'('#skF_11',B_599,'#skF_10'),'#skF_9')
      | ~ r2_hidden('#skF_11',k9_relat_1('#skF_10',B_599)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_1910])).

tff(c_2098,plain,
    ( ~ m1_subset_1('#skF_6'('#skF_11','#skF_8','#skF_10'),'#skF_9')
    | ~ r2_hidden('#skF_11',k9_relat_1('#skF_10','#skF_8'))
    | ~ v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_38,c_2090])).

tff(c_2104,plain,(
    ~ m1_subset_1('#skF_6'('#skF_11','#skF_8','#skF_10'),'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_1802,c_2098])).

tff(c_2301,plain,(
    ~ v4_relat_1('#skF_10','#skF_9') ),
    inference(resolution,[status(thm)],[c_2298,c_2104])).

tff(c_2320,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1689,c_2301])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:45:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.68/1.88  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.68/1.89  
% 4.68/1.89  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.68/1.89  %$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k7_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_11 > #skF_6 > #skF_4 > #skF_7 > #skF_10 > #skF_2 > #skF_9 > #skF_8 > #skF_5 > #skF_3 > #skF_1 > #skF_12
% 4.68/1.89  
% 4.68/1.89  %Foreground sorts:
% 4.68/1.89  
% 4.68/1.89  
% 4.68/1.89  %Background operators:
% 4.68/1.89  
% 4.68/1.89  
% 4.68/1.89  %Foreground operators:
% 4.68/1.89  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.68/1.89  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.68/1.89  tff('#skF_11', type, '#skF_11': $i).
% 4.68/1.89  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 4.68/1.89  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 4.68/1.89  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 4.68/1.89  tff('#skF_7', type, '#skF_7': $i).
% 4.68/1.89  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.68/1.89  tff('#skF_10', type, '#skF_10': $i).
% 4.68/1.89  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 4.68/1.89  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 4.68/1.89  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.68/1.89  tff('#skF_9', type, '#skF_9': $i).
% 4.68/1.89  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.68/1.89  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.68/1.89  tff('#skF_8', type, '#skF_8': $i).
% 4.68/1.89  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.68/1.89  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i) > $i).
% 4.68/1.89  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.68/1.89  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.68/1.89  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 4.68/1.89  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.68/1.89  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.68/1.89  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.68/1.89  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.68/1.89  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.68/1.89  tff('#skF_12', type, '#skF_12': $i).
% 4.68/1.89  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.68/1.89  
% 4.68/1.91  tff(f_112, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (~v1_xboole_0(C) => (![D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, A))) => (![E]: (m1_subset_1(E, A) => (r2_hidden(E, k7_relset_1(C, A, D, B)) <=> (?[F]: ((m1_subset_1(F, C) & r2_hidden(k4_tarski(F, E), D)) & r2_hidden(F, B)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_relset_1)).
% 4.68/1.91  tff(f_81, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.68/1.91  tff(f_64, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 4.68/1.91  tff(f_43, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 4.68/1.91  tff(f_85, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 4.68/1.91  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 4.68/1.91  tff(f_56, axiom, (![A]: (v1_relat_1(A) => (![B, C]: ((C = k9_relat_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E]: (r2_hidden(k4_tarski(E, D), A) & r2_hidden(E, B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d13_relat_1)).
% 4.68/1.91  tff(f_62, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 4.68/1.91  tff(f_75, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t143_relat_1)).
% 4.68/1.91  tff(f_36, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 4.68/1.91  tff(c_52, plain, (m1_subset_1('#skF_10', k1_zfmisc_1(k2_zfmisc_1('#skF_9', '#skF_7')))), inference(cnfTransformation, [status(thm)], [f_112])).
% 4.68/1.91  tff(c_1680, plain, (![C_505, A_506, B_507]: (v4_relat_1(C_505, A_506) | ~m1_subset_1(C_505, k1_zfmisc_1(k2_zfmisc_1(A_506, B_507))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.68/1.91  tff(c_1689, plain, (v4_relat_1('#skF_10', '#skF_9')), inference(resolution, [status(thm)], [c_52, c_1680])).
% 4.68/1.91  tff(c_34, plain, (![A_55, B_56]: (v1_relat_1(k2_zfmisc_1(A_55, B_56)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.68/1.91  tff(c_77, plain, (![B_163, A_164]: (v1_relat_1(B_163) | ~m1_subset_1(B_163, k1_zfmisc_1(A_164)) | ~v1_relat_1(A_164))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.68/1.91  tff(c_80, plain, (v1_relat_1('#skF_10') | ~v1_relat_1(k2_zfmisc_1('#skF_9', '#skF_7'))), inference(resolution, [status(thm)], [c_52, c_77])).
% 4.68/1.91  tff(c_83, plain, (v1_relat_1('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_80])).
% 4.68/1.91  tff(c_1788, plain, (![A_536, B_537, C_538, D_539]: (k7_relset_1(A_536, B_537, C_538, D_539)=k9_relat_1(C_538, D_539) | ~m1_subset_1(C_538, k1_zfmisc_1(k2_zfmisc_1(A_536, B_537))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.68/1.91  tff(c_1799, plain, (![D_539]: (k7_relset_1('#skF_9', '#skF_7', '#skF_10', D_539)=k9_relat_1('#skF_10', D_539))), inference(resolution, [status(thm)], [c_52, c_1788])).
% 4.68/1.91  tff(c_117, plain, (![C_175, A_176, B_177]: (v4_relat_1(C_175, A_176) | ~m1_subset_1(C_175, k1_zfmisc_1(k2_zfmisc_1(A_176, B_177))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.68/1.91  tff(c_126, plain, (v4_relat_1('#skF_10', '#skF_9')), inference(resolution, [status(thm)], [c_52, c_117])).
% 4.68/1.91  tff(c_1137, plain, (![A_398, B_399, C_400, D_401]: (k7_relset_1(A_398, B_399, C_400, D_401)=k9_relat_1(C_400, D_401) | ~m1_subset_1(C_400, k1_zfmisc_1(k2_zfmisc_1(A_398, B_399))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.68/1.91  tff(c_1148, plain, (![D_401]: (k7_relset_1('#skF_9', '#skF_7', '#skF_10', D_401)=k9_relat_1('#skF_10', D_401))), inference(resolution, [status(thm)], [c_52, c_1137])).
% 4.68/1.91  tff(c_477, plain, (![A_266, B_267, C_268, D_269]: (k7_relset_1(A_266, B_267, C_268, D_269)=k9_relat_1(C_268, D_269) | ~m1_subset_1(C_268, k1_zfmisc_1(k2_zfmisc_1(A_266, B_267))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.68/1.91  tff(c_488, plain, (![D_269]: (k7_relset_1('#skF_9', '#skF_7', '#skF_10', D_269)=k9_relat_1('#skF_10', D_269))), inference(resolution, [status(thm)], [c_52, c_477])).
% 4.68/1.91  tff(c_90, plain, (![A_167, B_168]: (r2_hidden('#skF_1'(A_167, B_168), A_167) | r1_tarski(A_167, B_168))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.68/1.91  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.68/1.91  tff(c_98, plain, (![A_167]: (r1_tarski(A_167, A_167))), inference(resolution, [status(thm)], [c_90, c_4])).
% 4.68/1.91  tff(c_74, plain, (r2_hidden('#skF_11', k7_relset_1('#skF_9', '#skF_7', '#skF_10', '#skF_8')) | m1_subset_1('#skF_12', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_112])).
% 4.68/1.91  tff(c_127, plain, (m1_subset_1('#skF_12', '#skF_9')), inference(splitLeft, [status(thm)], [c_74])).
% 4.68/1.91  tff(c_66, plain, (r2_hidden('#skF_11', k7_relset_1('#skF_9', '#skF_7', '#skF_10', '#skF_8')) | r2_hidden('#skF_12', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_112])).
% 4.68/1.91  tff(c_84, plain, (r2_hidden('#skF_12', '#skF_8')), inference(splitLeft, [status(thm)], [c_66])).
% 4.68/1.91  tff(c_70, plain, (r2_hidden('#skF_11', k7_relset_1('#skF_9', '#skF_7', '#skF_10', '#skF_8')) | r2_hidden(k4_tarski('#skF_12', '#skF_11'), '#skF_10')), inference(cnfTransformation, [status(thm)], [f_112])).
% 4.68/1.91  tff(c_169, plain, (r2_hidden(k4_tarski('#skF_12', '#skF_11'), '#skF_10')), inference(splitLeft, [status(thm)], [c_70])).
% 4.68/1.91  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.68/1.91  tff(c_175, plain, (![B_2]: (r2_hidden(k4_tarski('#skF_12', '#skF_11'), B_2) | ~r1_tarski('#skF_10', B_2))), inference(resolution, [status(thm)], [c_169, c_2])).
% 4.68/1.91  tff(c_320, plain, (![D_234, A_235, B_236, E_237]: (r2_hidden(D_234, k9_relat_1(A_235, B_236)) | ~r2_hidden(E_237, B_236) | ~r2_hidden(k4_tarski(E_237, D_234), A_235) | ~v1_relat_1(A_235))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.68/1.91  tff(c_345, plain, (![D_238, A_239]: (r2_hidden(D_238, k9_relat_1(A_239, '#skF_8')) | ~r2_hidden(k4_tarski('#skF_12', D_238), A_239) | ~v1_relat_1(A_239))), inference(resolution, [status(thm)], [c_84, c_320])).
% 4.68/1.91  tff(c_351, plain, (r2_hidden('#skF_11', k9_relat_1('#skF_10', '#skF_8')) | ~v1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_169, c_345])).
% 4.68/1.91  tff(c_355, plain, (r2_hidden('#skF_11', k9_relat_1('#skF_10', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_83, c_351])).
% 4.68/1.91  tff(c_293, plain, (![A_223, B_224, C_225, D_226]: (k7_relset_1(A_223, B_224, C_225, D_226)=k9_relat_1(C_225, D_226) | ~m1_subset_1(C_225, k1_zfmisc_1(k2_zfmisc_1(A_223, B_224))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.68/1.91  tff(c_308, plain, (![D_226]: (k7_relset_1('#skF_9', '#skF_7', '#skF_10', D_226)=k9_relat_1('#skF_10', D_226))), inference(resolution, [status(thm)], [c_52, c_293])).
% 4.68/1.91  tff(c_60, plain, (![F_158]: (~r2_hidden(F_158, '#skF_8') | ~r2_hidden(k4_tarski(F_158, '#skF_11'), '#skF_10') | ~m1_subset_1(F_158, '#skF_9') | ~r2_hidden('#skF_11', k7_relset_1('#skF_9', '#skF_7', '#skF_10', '#skF_8')))), inference(cnfTransformation, [status(thm)], [f_112])).
% 4.68/1.91  tff(c_373, plain, (![F_240]: (~r2_hidden(F_240, '#skF_8') | ~r2_hidden(k4_tarski(F_240, '#skF_11'), '#skF_10') | ~m1_subset_1(F_240, '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_355, c_308, c_60])).
% 4.68/1.91  tff(c_377, plain, (~r2_hidden('#skF_12', '#skF_8') | ~m1_subset_1('#skF_12', '#skF_9') | ~r1_tarski('#skF_10', '#skF_10')), inference(resolution, [status(thm)], [c_175, c_373])).
% 4.68/1.91  tff(c_384, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_98, c_127, c_84, c_377])).
% 4.68/1.91  tff(c_385, plain, (r2_hidden('#skF_11', k7_relset_1('#skF_9', '#skF_7', '#skF_10', '#skF_8'))), inference(splitRight, [status(thm)], [c_70])).
% 4.68/1.91  tff(c_491, plain, (r2_hidden('#skF_11', k9_relat_1('#skF_10', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_488, c_385])).
% 4.68/1.91  tff(c_32, plain, (![B_54, A_53]: (r1_tarski(k1_relat_1(B_54), A_53) | ~v4_relat_1(B_54, A_53) | ~v1_relat_1(B_54))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.68/1.91  tff(c_469, plain, (![A_263, B_264, C_265]: (r2_hidden('#skF_6'(A_263, B_264, C_265), k1_relat_1(C_265)) | ~r2_hidden(A_263, k9_relat_1(C_265, B_264)) | ~v1_relat_1(C_265))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.68/1.91  tff(c_812, plain, (![A_341, B_342, C_343, B_344]: (r2_hidden('#skF_6'(A_341, B_342, C_343), B_344) | ~r1_tarski(k1_relat_1(C_343), B_344) | ~r2_hidden(A_341, k9_relat_1(C_343, B_342)) | ~v1_relat_1(C_343))), inference(resolution, [status(thm)], [c_469, c_2])).
% 4.68/1.91  tff(c_8, plain, (![A_6, B_7]: (m1_subset_1(A_6, B_7) | ~r2_hidden(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.68/1.91  tff(c_888, plain, (![A_352, B_353, C_354, B_355]: (m1_subset_1('#skF_6'(A_352, B_353, C_354), B_355) | ~r1_tarski(k1_relat_1(C_354), B_355) | ~r2_hidden(A_352, k9_relat_1(C_354, B_353)) | ~v1_relat_1(C_354))), inference(resolution, [status(thm)], [c_812, c_8])).
% 4.68/1.91  tff(c_932, plain, (![A_358, B_359, B_360, A_361]: (m1_subset_1('#skF_6'(A_358, B_359, B_360), A_361) | ~r2_hidden(A_358, k9_relat_1(B_360, B_359)) | ~v4_relat_1(B_360, A_361) | ~v1_relat_1(B_360))), inference(resolution, [status(thm)], [c_32, c_888])).
% 4.68/1.91  tff(c_959, plain, (![A_361]: (m1_subset_1('#skF_6'('#skF_11', '#skF_8', '#skF_10'), A_361) | ~v4_relat_1('#skF_10', A_361) | ~v1_relat_1('#skF_10'))), inference(resolution, [status(thm)], [c_491, c_932])).
% 4.68/1.91  tff(c_988, plain, (![A_362]: (m1_subset_1('#skF_6'('#skF_11', '#skF_8', '#skF_10'), A_362) | ~v4_relat_1('#skF_10', A_362))), inference(demodulation, [status(thm), theory('equality')], [c_83, c_959])).
% 4.68/1.91  tff(c_38, plain, (![A_57, B_58, C_59]: (r2_hidden('#skF_6'(A_57, B_58, C_59), B_58) | ~r2_hidden(A_57, k9_relat_1(C_59, B_58)) | ~v1_relat_1(C_59))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.68/1.91  tff(c_531, plain, (![A_280, B_281, C_282]: (r2_hidden(k4_tarski('#skF_6'(A_280, B_281, C_282), A_280), C_282) | ~r2_hidden(A_280, k9_relat_1(C_282, B_281)) | ~v1_relat_1(C_282))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.68/1.91  tff(c_386, plain, (~r2_hidden(k4_tarski('#skF_12', '#skF_11'), '#skF_10')), inference(splitRight, [status(thm)], [c_70])).
% 4.68/1.91  tff(c_68, plain, (![F_158]: (~r2_hidden(F_158, '#skF_8') | ~r2_hidden(k4_tarski(F_158, '#skF_11'), '#skF_10') | ~m1_subset_1(F_158, '#skF_9') | r2_hidden(k4_tarski('#skF_12', '#skF_11'), '#skF_10'))), inference(cnfTransformation, [status(thm)], [f_112])).
% 4.68/1.91  tff(c_514, plain, (![F_158]: (~r2_hidden(F_158, '#skF_8') | ~r2_hidden(k4_tarski(F_158, '#skF_11'), '#skF_10') | ~m1_subset_1(F_158, '#skF_9'))), inference(negUnitSimplification, [status(thm)], [c_386, c_68])).
% 4.68/1.91  tff(c_535, plain, (![B_281]: (~r2_hidden('#skF_6'('#skF_11', B_281, '#skF_10'), '#skF_8') | ~m1_subset_1('#skF_6'('#skF_11', B_281, '#skF_10'), '#skF_9') | ~r2_hidden('#skF_11', k9_relat_1('#skF_10', B_281)) | ~v1_relat_1('#skF_10'))), inference(resolution, [status(thm)], [c_531, c_514])).
% 4.68/1.91  tff(c_678, plain, (![B_320]: (~r2_hidden('#skF_6'('#skF_11', B_320, '#skF_10'), '#skF_8') | ~m1_subset_1('#skF_6'('#skF_11', B_320, '#skF_10'), '#skF_9') | ~r2_hidden('#skF_11', k9_relat_1('#skF_10', B_320)))), inference(demodulation, [status(thm), theory('equality')], [c_83, c_535])).
% 4.68/1.91  tff(c_686, plain, (~m1_subset_1('#skF_6'('#skF_11', '#skF_8', '#skF_10'), '#skF_9') | ~r2_hidden('#skF_11', k9_relat_1('#skF_10', '#skF_8')) | ~v1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_38, c_678])).
% 4.68/1.91  tff(c_692, plain, (~m1_subset_1('#skF_6'('#skF_11', '#skF_8', '#skF_10'), '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_83, c_491, c_686])).
% 4.68/1.91  tff(c_991, plain, (~v4_relat_1('#skF_10', '#skF_9')), inference(resolution, [status(thm)], [c_988, c_692])).
% 4.68/1.91  tff(c_1010, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_126, c_991])).
% 4.68/1.91  tff(c_1011, plain, (r2_hidden('#skF_11', k7_relset_1('#skF_9', '#skF_7', '#skF_10', '#skF_8'))), inference(splitRight, [status(thm)], [c_74])).
% 4.68/1.91  tff(c_1152, plain, (r2_hidden('#skF_11', k9_relat_1('#skF_10', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_1148, c_1011])).
% 4.68/1.91  tff(c_1182, plain, (![A_404, B_405, C_406]: (r2_hidden('#skF_6'(A_404, B_405, C_406), k1_relat_1(C_406)) | ~r2_hidden(A_404, k9_relat_1(C_406, B_405)) | ~v1_relat_1(C_406))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.68/1.91  tff(c_1492, plain, (![A_479, B_480, C_481, B_482]: (r2_hidden('#skF_6'(A_479, B_480, C_481), B_482) | ~r1_tarski(k1_relat_1(C_481), B_482) | ~r2_hidden(A_479, k9_relat_1(C_481, B_480)) | ~v1_relat_1(C_481))), inference(resolution, [status(thm)], [c_1182, c_2])).
% 4.68/1.91  tff(c_1570, plain, (![A_487, B_488, C_489, B_490]: (m1_subset_1('#skF_6'(A_487, B_488, C_489), B_490) | ~r1_tarski(k1_relat_1(C_489), B_490) | ~r2_hidden(A_487, k9_relat_1(C_489, B_488)) | ~v1_relat_1(C_489))), inference(resolution, [status(thm)], [c_1492, c_8])).
% 4.68/1.91  tff(c_1578, plain, (![A_491, B_492, B_493, A_494]: (m1_subset_1('#skF_6'(A_491, B_492, B_493), A_494) | ~r2_hidden(A_491, k9_relat_1(B_493, B_492)) | ~v4_relat_1(B_493, A_494) | ~v1_relat_1(B_493))), inference(resolution, [status(thm)], [c_32, c_1570])).
% 4.68/1.91  tff(c_1603, plain, (![A_494]: (m1_subset_1('#skF_6'('#skF_11', '#skF_8', '#skF_10'), A_494) | ~v4_relat_1('#skF_10', A_494) | ~v1_relat_1('#skF_10'))), inference(resolution, [status(thm)], [c_1152, c_1578])).
% 4.68/1.91  tff(c_1631, plain, (![A_495]: (m1_subset_1('#skF_6'('#skF_11', '#skF_8', '#skF_10'), A_495) | ~v4_relat_1('#skF_10', A_495))), inference(demodulation, [status(thm), theory('equality')], [c_83, c_1603])).
% 4.68/1.91  tff(c_1191, plain, (![A_410, B_411, C_412]: (r2_hidden(k4_tarski('#skF_6'(A_410, B_411, C_412), A_410), C_412) | ~r2_hidden(A_410, k9_relat_1(C_412, B_411)) | ~v1_relat_1(C_412))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.68/1.91  tff(c_1012, plain, (~m1_subset_1('#skF_12', '#skF_9')), inference(splitRight, [status(thm)], [c_74])).
% 4.68/1.91  tff(c_72, plain, (![F_158]: (~r2_hidden(F_158, '#skF_8') | ~r2_hidden(k4_tarski(F_158, '#skF_11'), '#skF_10') | ~m1_subset_1(F_158, '#skF_9') | m1_subset_1('#skF_12', '#skF_9'))), inference(cnfTransformation, [status(thm)], [f_112])).
% 4.68/1.91  tff(c_1107, plain, (![F_158]: (~r2_hidden(F_158, '#skF_8') | ~r2_hidden(k4_tarski(F_158, '#skF_11'), '#skF_10') | ~m1_subset_1(F_158, '#skF_9'))), inference(negUnitSimplification, [status(thm)], [c_1012, c_72])).
% 4.68/1.91  tff(c_1198, plain, (![B_411]: (~r2_hidden('#skF_6'('#skF_11', B_411, '#skF_10'), '#skF_8') | ~m1_subset_1('#skF_6'('#skF_11', B_411, '#skF_10'), '#skF_9') | ~r2_hidden('#skF_11', k9_relat_1('#skF_10', B_411)) | ~v1_relat_1('#skF_10'))), inference(resolution, [status(thm)], [c_1191, c_1107])).
% 4.68/1.91  tff(c_1330, plain, (![B_450]: (~r2_hidden('#skF_6'('#skF_11', B_450, '#skF_10'), '#skF_8') | ~m1_subset_1('#skF_6'('#skF_11', B_450, '#skF_10'), '#skF_9') | ~r2_hidden('#skF_11', k9_relat_1('#skF_10', B_450)))), inference(demodulation, [status(thm), theory('equality')], [c_83, c_1198])).
% 4.68/1.91  tff(c_1334, plain, (~m1_subset_1('#skF_6'('#skF_11', '#skF_8', '#skF_10'), '#skF_9') | ~r2_hidden('#skF_11', k9_relat_1('#skF_10', '#skF_8')) | ~v1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_38, c_1330])).
% 4.68/1.91  tff(c_1337, plain, (~m1_subset_1('#skF_6'('#skF_11', '#skF_8', '#skF_10'), '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_83, c_1152, c_1334])).
% 4.68/1.91  tff(c_1634, plain, (~v4_relat_1('#skF_10', '#skF_9')), inference(resolution, [status(thm)], [c_1631, c_1337])).
% 4.68/1.91  tff(c_1653, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_126, c_1634])).
% 4.68/1.91  tff(c_1654, plain, (r2_hidden('#skF_11', k7_relset_1('#skF_9', '#skF_7', '#skF_10', '#skF_8'))), inference(splitRight, [status(thm)], [c_66])).
% 4.68/1.91  tff(c_1802, plain, (r2_hidden('#skF_11', k9_relat_1('#skF_10', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_1799, c_1654])).
% 4.68/1.91  tff(c_1825, plain, (![A_541, B_542, C_543]: (r2_hidden('#skF_6'(A_541, B_542, C_543), k1_relat_1(C_543)) | ~r2_hidden(A_541, k9_relat_1(C_543, B_542)) | ~v1_relat_1(C_543))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.68/1.91  tff(c_2151, plain, (![A_608, B_609, C_610, B_611]: (r2_hidden('#skF_6'(A_608, B_609, C_610), B_611) | ~r1_tarski(k1_relat_1(C_610), B_611) | ~r2_hidden(A_608, k9_relat_1(C_610, B_609)) | ~v1_relat_1(C_610))), inference(resolution, [status(thm)], [c_1825, c_2])).
% 4.68/1.91  tff(c_2218, plain, (![A_620, B_621, C_622, B_623]: (m1_subset_1('#skF_6'(A_620, B_621, C_622), B_623) | ~r1_tarski(k1_relat_1(C_622), B_623) | ~r2_hidden(A_620, k9_relat_1(C_622, B_621)) | ~v1_relat_1(C_622))), inference(resolution, [status(thm)], [c_2151, c_8])).
% 4.68/1.91  tff(c_2245, plain, (![A_627, B_628, B_629, A_630]: (m1_subset_1('#skF_6'(A_627, B_628, B_629), A_630) | ~r2_hidden(A_627, k9_relat_1(B_629, B_628)) | ~v4_relat_1(B_629, A_630) | ~v1_relat_1(B_629))), inference(resolution, [status(thm)], [c_32, c_2218])).
% 4.68/1.91  tff(c_2273, plain, (![A_630]: (m1_subset_1('#skF_6'('#skF_11', '#skF_8', '#skF_10'), A_630) | ~v4_relat_1('#skF_10', A_630) | ~v1_relat_1('#skF_10'))), inference(resolution, [status(thm)], [c_1802, c_2245])).
% 4.68/1.91  tff(c_2298, plain, (![A_631]: (m1_subset_1('#skF_6'('#skF_11', '#skF_8', '#skF_10'), A_631) | ~v4_relat_1('#skF_10', A_631))), inference(demodulation, [status(thm), theory('equality')], [c_83, c_2273])).
% 4.68/1.91  tff(c_1904, plain, (![A_574, B_575, C_576]: (r2_hidden(k4_tarski('#skF_6'(A_574, B_575, C_576), A_574), C_576) | ~r2_hidden(A_574, k9_relat_1(C_576, B_575)) | ~v1_relat_1(C_576))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.68/1.91  tff(c_1655, plain, (~r2_hidden('#skF_12', '#skF_8')), inference(splitRight, [status(thm)], [c_66])).
% 4.68/1.91  tff(c_64, plain, (![F_158]: (~r2_hidden(F_158, '#skF_8') | ~r2_hidden(k4_tarski(F_158, '#skF_11'), '#skF_10') | ~m1_subset_1(F_158, '#skF_9') | r2_hidden('#skF_12', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_112])).
% 4.68/1.91  tff(c_1786, plain, (![F_158]: (~r2_hidden(F_158, '#skF_8') | ~r2_hidden(k4_tarski(F_158, '#skF_11'), '#skF_10') | ~m1_subset_1(F_158, '#skF_9'))), inference(negUnitSimplification, [status(thm)], [c_1655, c_64])).
% 4.68/1.91  tff(c_1910, plain, (![B_575]: (~r2_hidden('#skF_6'('#skF_11', B_575, '#skF_10'), '#skF_8') | ~m1_subset_1('#skF_6'('#skF_11', B_575, '#skF_10'), '#skF_9') | ~r2_hidden('#skF_11', k9_relat_1('#skF_10', B_575)) | ~v1_relat_1('#skF_10'))), inference(resolution, [status(thm)], [c_1904, c_1786])).
% 4.68/1.91  tff(c_2090, plain, (![B_599]: (~r2_hidden('#skF_6'('#skF_11', B_599, '#skF_10'), '#skF_8') | ~m1_subset_1('#skF_6'('#skF_11', B_599, '#skF_10'), '#skF_9') | ~r2_hidden('#skF_11', k9_relat_1('#skF_10', B_599)))), inference(demodulation, [status(thm), theory('equality')], [c_83, c_1910])).
% 4.68/1.91  tff(c_2098, plain, (~m1_subset_1('#skF_6'('#skF_11', '#skF_8', '#skF_10'), '#skF_9') | ~r2_hidden('#skF_11', k9_relat_1('#skF_10', '#skF_8')) | ~v1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_38, c_2090])).
% 4.68/1.91  tff(c_2104, plain, (~m1_subset_1('#skF_6'('#skF_11', '#skF_8', '#skF_10'), '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_83, c_1802, c_2098])).
% 4.68/1.91  tff(c_2301, plain, (~v4_relat_1('#skF_10', '#skF_9')), inference(resolution, [status(thm)], [c_2298, c_2104])).
% 4.68/1.91  tff(c_2320, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1689, c_2301])).
% 4.68/1.91  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.68/1.91  
% 4.68/1.91  Inference rules
% 4.68/1.91  ----------------------
% 4.68/1.91  #Ref     : 0
% 4.68/1.91  #Sup     : 492
% 4.68/1.91  #Fact    : 0
% 4.68/1.91  #Define  : 0
% 4.68/1.91  #Split   : 10
% 4.68/1.91  #Chain   : 0
% 4.68/1.91  #Close   : 0
% 4.68/1.91  
% 4.68/1.91  Ordering : KBO
% 4.68/1.91  
% 4.68/1.91  Simplification rules
% 4.68/1.91  ----------------------
% 4.68/1.91  #Subsume      : 33
% 4.68/1.91  #Demod        : 85
% 4.68/1.91  #Tautology    : 35
% 4.68/1.91  #SimpNegUnit  : 3
% 4.68/1.91  #BackRed      : 9
% 4.68/1.91  
% 4.68/1.91  #Partial instantiations: 0
% 4.68/1.91  #Strategies tried      : 1
% 4.68/1.91  
% 4.68/1.91  Timing (in seconds)
% 4.68/1.91  ----------------------
% 4.96/1.91  Preprocessing        : 0.36
% 4.96/1.91  Parsing              : 0.18
% 4.96/1.91  CNF conversion       : 0.04
% 4.96/1.91  Main loop            : 0.77
% 4.96/1.91  Inferencing          : 0.31
% 4.96/1.92  Reduction            : 0.20
% 4.96/1.92  Demodulation         : 0.13
% 4.96/1.92  BG Simplification    : 0.04
% 4.96/1.92  Subsumption          : 0.15
% 4.96/1.92  Abstraction          : 0.04
% 4.96/1.92  MUC search           : 0.00
% 4.96/1.92  Cooper               : 0.00
% 4.96/1.92  Total                : 1.18
% 4.96/1.92  Index Insertion      : 0.00
% 4.96/1.92  Index Deletion       : 0.00
% 4.96/1.92  Index Matching       : 0.00
% 4.96/1.92  BG Taut test         : 0.00
%------------------------------------------------------------------------------
