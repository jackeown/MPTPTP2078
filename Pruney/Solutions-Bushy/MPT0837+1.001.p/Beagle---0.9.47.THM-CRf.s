%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0837+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:55 EST 2020

% Result     : Theorem 5.98s
% Output     : CNFRefutation 5.98s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 197 expanded)
%              Number of leaves         :   29 (  78 expanded)
%              Depth                    :    8
%              Number of atoms          :  128 ( 443 expanded)
%              Number of equality atoms :    8 (  34 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v1_xboole_0 > k2_relset_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > #skF_4 > #skF_7 > #skF_3 > #skF_10 > #skF_5 > #skF_6 > #skF_9 > #skF_8 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_32,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

tff(f_84,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ~ v1_xboole_0(B)
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
               => ! [D] :
                    ( r2_hidden(D,k2_relset_1(B,A,C))
                  <=> ? [E] :
                        ( m1_subset_1(E,B)
                        & r2_hidden(k4_tarski(E,D),C) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_relset_1)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_52,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_42,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_zfmisc_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(c_4200,plain,(
    ! [A_540,C_541] :
      ( r2_hidden(k4_tarski('#skF_4'(A_540,k2_relat_1(A_540),C_541),C_541),A_540)
      | ~ r2_hidden(C_541,k2_relat_1(A_540)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_30,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_4068,plain,(
    ! [A_501,B_502,C_503] :
      ( k2_relset_1(A_501,B_502,C_503) = k2_relat_1(C_503)
      | ~ m1_subset_1(C_503,k1_zfmisc_1(k2_zfmisc_1(A_501,B_502))) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_4072,plain,(
    k2_relset_1('#skF_6','#skF_5','#skF_7') = k2_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_30,c_4068])).

tff(c_1335,plain,(
    ! [A_238,B_239,C_240] :
      ( k2_relset_1(A_238,B_239,C_240) = k2_relat_1(C_240)
      | ~ m1_subset_1(C_240,k1_zfmisc_1(k2_zfmisc_1(A_238,B_239))) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_1339,plain,(
    k2_relset_1('#skF_6','#skF_5','#skF_7') = k2_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_30,c_1335])).

tff(c_46,plain,
    ( m1_subset_1('#skF_9','#skF_6')
    | r2_hidden('#skF_10',k2_relset_1('#skF_6','#skF_5','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_58,plain,(
    r2_hidden('#skF_10',k2_relset_1('#skF_6','#skF_5','#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_1341,plain,(
    r2_hidden('#skF_10',k2_relat_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1339,c_58])).

tff(c_2,plain,(
    ! [A_1,C_16] :
      ( r2_hidden(k4_tarski('#skF_4'(A_1,k2_relat_1(A_1),C_16),C_16),A_1)
      | ~ r2_hidden(C_16,k2_relat_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_53,plain,(
    ! [C_83,B_84,A_85] :
      ( ~ v1_xboole_0(C_83)
      | ~ m1_subset_1(B_84,k1_zfmisc_1(C_83))
      | ~ r2_hidden(A_85,B_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_56,plain,(
    ! [A_85] :
      ( ~ v1_xboole_0(k2_zfmisc_1('#skF_6','#skF_5'))
      | ~ r2_hidden(A_85,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_30,c_53])).

tff(c_57,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_6','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_1317,plain,(
    ! [A_229,C_230,B_231] :
      ( m1_subset_1(A_229,C_230)
      | ~ m1_subset_1(B_231,k1_zfmisc_1(C_230))
      | ~ r2_hidden(A_229,B_231) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1320,plain,(
    ! [A_229] :
      ( m1_subset_1(A_229,k2_zfmisc_1('#skF_6','#skF_5'))
      | ~ r2_hidden(A_229,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_30,c_1317])).

tff(c_24,plain,(
    ! [A_29,B_30] :
      ( r2_hidden(A_29,B_30)
      | v1_xboole_0(B_30)
      | ~ m1_subset_1(A_29,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_1312,plain,(
    ! [A_225,C_226,B_227,D_228] :
      ( r2_hidden(A_225,C_226)
      | ~ r2_hidden(k4_tarski(A_225,B_227),k2_zfmisc_1(C_226,D_228)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_3807,plain,(
    ! [A_470,C_471,D_472,B_473] :
      ( r2_hidden(A_470,C_471)
      | v1_xboole_0(k2_zfmisc_1(C_471,D_472))
      | ~ m1_subset_1(k4_tarski(A_470,B_473),k2_zfmisc_1(C_471,D_472)) ) ),
    inference(resolution,[status(thm)],[c_24,c_1312])).

tff(c_3818,plain,(
    ! [A_470,B_473] :
      ( r2_hidden(A_470,'#skF_6')
      | v1_xboole_0(k2_zfmisc_1('#skF_6','#skF_5'))
      | ~ r2_hidden(k4_tarski(A_470,B_473),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_1320,c_3807])).

tff(c_3824,plain,(
    ! [A_474,B_475] :
      ( r2_hidden(A_474,'#skF_6')
      | ~ r2_hidden(k4_tarski(A_474,B_475),'#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_57,c_3818])).

tff(c_4008,plain,(
    ! [C_484] :
      ( r2_hidden('#skF_4'('#skF_7',k2_relat_1('#skF_7'),C_484),'#skF_6')
      | ~ r2_hidden(C_484,k2_relat_1('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_2,c_3824])).

tff(c_22,plain,(
    ! [A_27,B_28] :
      ( m1_subset_1(A_27,B_28)
      | ~ r2_hidden(A_27,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_4019,plain,(
    ! [C_485] :
      ( m1_subset_1('#skF_4'('#skF_7',k2_relat_1('#skF_7'),C_485),'#skF_6')
      | ~ r2_hidden(C_485,k2_relat_1('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_4008,c_22])).

tff(c_2407,plain,(
    ! [A_346,C_347,D_348,B_349] :
      ( r2_hidden(A_346,C_347)
      | v1_xboole_0(k2_zfmisc_1(C_347,D_348))
      | ~ m1_subset_1(k4_tarski(A_346,B_349),k2_zfmisc_1(C_347,D_348)) ) ),
    inference(resolution,[status(thm)],[c_24,c_1312])).

tff(c_2418,plain,(
    ! [A_346,B_349] :
      ( r2_hidden(A_346,'#skF_6')
      | v1_xboole_0(k2_zfmisc_1('#skF_6','#skF_5'))
      | ~ r2_hidden(k4_tarski(A_346,B_349),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_1320,c_2407])).

tff(c_2424,plain,(
    ! [A_350,B_351] :
      ( r2_hidden(A_350,'#skF_6')
      | ~ r2_hidden(k4_tarski(A_350,B_351),'#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_57,c_2418])).

tff(c_2491,plain,(
    ! [C_354] :
      ( r2_hidden('#skF_4'('#skF_7',k2_relat_1('#skF_7'),C_354),'#skF_6')
      | ~ r2_hidden(C_354,k2_relat_1('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_2,c_2424])).

tff(c_2505,plain,(
    ! [C_355] :
      ( m1_subset_1('#skF_4'('#skF_7',k2_relat_1('#skF_7'),C_355),'#skF_6')
      | ~ r2_hidden(C_355,k2_relat_1('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_2491,c_22])).

tff(c_1365,plain,(
    ! [A_245,C_246] :
      ( r2_hidden(k4_tarski('#skF_4'(A_245,k2_relat_1(A_245),C_246),C_246),A_245)
      | ~ r2_hidden(C_246,k2_relat_1(A_245)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_38,plain,(
    ! [E_78] :
      ( r2_hidden(k4_tarski('#skF_9','#skF_8'),'#skF_7')
      | ~ r2_hidden(k4_tarski(E_78,'#skF_10'),'#skF_7')
      | ~ m1_subset_1(E_78,'#skF_6') ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_1346,plain,(
    ! [E_78] :
      ( ~ r2_hidden(k4_tarski(E_78,'#skF_10'),'#skF_7')
      | ~ m1_subset_1(E_78,'#skF_6') ) ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_1369,plain,
    ( ~ m1_subset_1('#skF_4'('#skF_7',k2_relat_1('#skF_7'),'#skF_10'),'#skF_6')
    | ~ r2_hidden('#skF_10',k2_relat_1('#skF_7')) ),
    inference(resolution,[status(thm)],[c_1365,c_1346])).

tff(c_1389,plain,(
    ~ m1_subset_1('#skF_4'('#skF_7',k2_relat_1('#skF_7'),'#skF_10'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1341,c_1369])).

tff(c_2508,plain,(
    ~ r2_hidden('#skF_10',k2_relat_1('#skF_7')) ),
    inference(resolution,[status(thm)],[c_2505,c_1389])).

tff(c_2512,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1341,c_2508])).

tff(c_2513,plain,(
    r2_hidden(k4_tarski('#skF_9','#skF_8'),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_4,plain,(
    ! [C_16,A_1,D_19] :
      ( r2_hidden(C_16,k2_relat_1(A_1))
      | ~ r2_hidden(k4_tarski(D_19,C_16),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_2528,plain,(
    r2_hidden('#skF_8',k2_relat_1('#skF_7')) ),
    inference(resolution,[status(thm)],[c_2513,c_4])).

tff(c_36,plain,(
    ! [E_78] :
      ( ~ r2_hidden('#skF_8',k2_relset_1('#skF_6','#skF_5','#skF_7'))
      | ~ r2_hidden(k4_tarski(E_78,'#skF_10'),'#skF_7')
      | ~ m1_subset_1(E_78,'#skF_6') ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_2567,plain,(
    ! [E_358] :
      ( ~ r2_hidden(k4_tarski(E_358,'#skF_10'),'#skF_7')
      | ~ m1_subset_1(E_358,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2528,c_1339,c_36])).

tff(c_2571,plain,
    ( ~ m1_subset_1('#skF_4'('#skF_7',k2_relat_1('#skF_7'),'#skF_10'),'#skF_6')
    | ~ r2_hidden('#skF_10',k2_relat_1('#skF_7')) ),
    inference(resolution,[status(thm)],[c_2,c_2567])).

tff(c_2577,plain,(
    ~ m1_subset_1('#skF_4'('#skF_7',k2_relat_1('#skF_7'),'#skF_10'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1341,c_2571])).

tff(c_4022,plain,(
    ~ r2_hidden('#skF_10',k2_relat_1('#skF_7')) ),
    inference(resolution,[status(thm)],[c_4019,c_2577])).

tff(c_4026,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1341,c_4022])).

tff(c_4028,plain,(
    ~ r2_hidden('#skF_10',k2_relset_1('#skF_6','#skF_5','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_4073,plain,(
    ~ r2_hidden('#skF_10',k2_relat_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4072,c_4028])).

tff(c_44,plain,
    ( r2_hidden(k4_tarski('#skF_9','#skF_8'),'#skF_7')
    | r2_hidden('#skF_10',k2_relset_1('#skF_6','#skF_5','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_4049,plain,(
    r2_hidden(k4_tarski('#skF_9','#skF_8'),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_4028,c_44])).

tff(c_4056,plain,(
    r2_hidden('#skF_8',k2_relat_1('#skF_7')) ),
    inference(resolution,[status(thm)],[c_4049,c_4])).

tff(c_42,plain,
    ( ~ r2_hidden('#skF_8',k2_relset_1('#skF_6','#skF_5','#skF_7'))
    | r2_hidden('#skF_10',k2_relset_1('#skF_6','#skF_5','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_4084,plain,(
    r2_hidden('#skF_10',k2_relat_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4072,c_4056,c_4072,c_42])).

tff(c_4085,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4073,c_4084])).

tff(c_4086,plain,(
    ! [A_85] : ~ r2_hidden(A_85,'#skF_7') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_4225,plain,(
    ! [C_541] : ~ r2_hidden(C_541,k2_relat_1('#skF_7')) ),
    inference(resolution,[status(thm)],[c_4200,c_4086])).

tff(c_4125,plain,(
    ! [A_523,B_524,C_525] :
      ( k2_relset_1(A_523,B_524,C_525) = k2_relat_1(C_525)
      | ~ m1_subset_1(C_525,k1_zfmisc_1(k2_zfmisc_1(A_523,B_524))) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_4129,plain,(
    k2_relset_1('#skF_6','#skF_5','#skF_7') = k2_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_30,c_4125])).

tff(c_4096,plain,(
    r2_hidden('#skF_10',k2_relset_1('#skF_6','#skF_5','#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_4131,plain,(
    r2_hidden('#skF_10',k2_relat_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4129,c_4096])).

tff(c_4228,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4225,c_4131])).

tff(c_4230,plain,(
    ~ r2_hidden('#skF_10',k2_relset_1('#skF_6','#skF_5','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_4256,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4230,c_4086,c_44])).

%------------------------------------------------------------------------------
