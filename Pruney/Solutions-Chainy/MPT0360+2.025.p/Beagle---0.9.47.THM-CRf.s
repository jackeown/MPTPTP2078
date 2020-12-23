%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:21 EST 2020

% Result     : Theorem 14.55s
% Output     : CNFRefutation 14.83s
% Verified   : 
% Statistics : Number of formulae       :  195 (1490 expanded)
%              Number of leaves         :   32 ( 497 expanded)
%              Depth                    :   18
%              Number of atoms          :  320 (3042 expanded)
%              Number of equality atoms :   52 ( 611 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k3_subset_1 > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_39,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_90,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_61,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_63,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_73,axiom,(
    ! [A] : k2_subset_1(A) = k3_subset_1(A,k1_subset_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_subset_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_99,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(A))
       => ( ( r1_tarski(B,C)
            & r1_tarski(B,k3_subset_1(A,C)) )
         => B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_subset_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_82,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_tarski(B,k3_subset_1(A,C))
           => r1_tarski(C,k3_subset_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_subset_1)).

tff(f_88,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( r1_tarski(k3_subset_1(A,B),B)
      <=> B = k2_subset_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_subset_1)).

tff(c_8,plain,(
    ! [A_8] : r1_tarski(k1_xboole_0,A_8) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_46,plain,(
    ! [A_29] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_29)) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_30,plain,(
    ! [A_16] : k1_subset_1(A_16) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_32,plain,(
    ! [A_17] : k2_subset_1(A_17) = A_17 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_38,plain,(
    ! [A_22] : k3_subset_1(A_22,k1_subset_1(A_22)) = k2_subset_1(A_22) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_57,plain,(
    ! [A_22] : k3_subset_1(A_22,k1_subset_1(A_22)) = A_22 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_38])).

tff(c_58,plain,(
    ! [A_22] : k3_subset_1(A_22,k1_xboole_0) = A_22 ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_57])).

tff(c_21469,plain,(
    ! [A_367,B_368] :
      ( m1_subset_1(k3_subset_1(A_367,B_368),k1_zfmisc_1(A_367))
      | ~ m1_subset_1(B_368,k1_zfmisc_1(A_367)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_21483,plain,(
    ! [A_22] :
      ( m1_subset_1(A_22,k1_zfmisc_1(A_22))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_22)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_21469])).

tff(c_21489,plain,(
    ! [A_22] : m1_subset_1(A_22,k1_zfmisc_1(A_22)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_21483])).

tff(c_21280,plain,(
    ! [B_348,A_349] :
      ( r2_hidden(B_348,A_349)
      | ~ m1_subset_1(B_348,A_349)
      | v1_xboole_0(A_349) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_10,plain,(
    ! [C_13,A_9] :
      ( r1_tarski(C_13,A_9)
      | ~ r2_hidden(C_13,k1_zfmisc_1(A_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_21520,plain,(
    ! [B_372,A_373] :
      ( r1_tarski(B_372,A_373)
      | ~ m1_subset_1(B_372,k1_zfmisc_1(A_373))
      | v1_xboole_0(k1_zfmisc_1(A_373)) ) ),
    inference(resolution,[status(thm)],[c_21280,c_10])).

tff(c_21553,plain,(
    ! [A_374] :
      ( r1_tarski(A_374,A_374)
      | v1_xboole_0(k1_zfmisc_1(A_374)) ) ),
    inference(resolution,[status(thm)],[c_21489,c_21520])).

tff(c_92,plain,(
    ! [C_38,A_39] :
      ( r2_hidden(C_38,k1_zfmisc_1(A_39))
      | ~ r1_tarski(C_38,A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_96,plain,(
    ! [A_39,C_38] :
      ( ~ v1_xboole_0(k1_zfmisc_1(A_39))
      | ~ r1_tarski(C_38,A_39) ) ),
    inference(resolution,[status(thm)],[c_92,c_2])).

tff(c_21747,plain,(
    ! [C_381,A_382] :
      ( ~ r1_tarski(C_381,A_382)
      | r1_tarski(A_382,A_382) ) ),
    inference(resolution,[status(thm)],[c_21553,c_96])).

tff(c_21782,plain,(
    ! [A_8] : r1_tarski(A_8,A_8) ),
    inference(resolution,[status(thm)],[c_8,c_21747])).

tff(c_48,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_52,plain,(
    r1_tarski('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_54,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_108,plain,(
    ! [B_44,A_45] :
      ( v1_xboole_0(B_44)
      | ~ m1_subset_1(B_44,A_45)
      | ~ v1_xboole_0(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_116,plain,
    ( v1_xboole_0('#skF_6')
    | ~ v1_xboole_0(k1_zfmisc_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_54,c_108])).

tff(c_21265,plain,(
    ~ v1_xboole_0(k1_zfmisc_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_116])).

tff(c_21540,plain,
    ( r1_tarski('#skF_6','#skF_4')
    | v1_xboole_0(k1_zfmisc_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_54,c_21520])).

tff(c_21549,plain,(
    r1_tarski('#skF_6','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_21265,c_21540])).

tff(c_6,plain,(
    ! [A_5,C_7,B_6] :
      ( r1_tarski(A_5,C_7)
      | ~ r1_tarski(B_6,C_7)
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_21840,plain,(
    ! [A_386] :
      ( r1_tarski(A_386,'#skF_4')
      | ~ r1_tarski(A_386,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_21549,c_6])).

tff(c_21865,plain,(
    r1_tarski('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_21840])).

tff(c_21392,plain,(
    ! [A_361,B_362] :
      ( k3_subset_1(A_361,k3_subset_1(A_361,B_362)) = B_362
      | ~ m1_subset_1(B_362,k1_zfmisc_1(A_361)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_21400,plain,(
    ! [A_29] : k3_subset_1(A_29,k3_subset_1(A_29,k1_xboole_0)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_46,c_21392])).

tff(c_21406,plain,(
    ! [A_29] : k3_subset_1(A_29,A_29) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_21400])).

tff(c_12,plain,(
    ! [C_13,A_9] :
      ( r2_hidden(C_13,k1_zfmisc_1(A_9))
      | ~ r1_tarski(C_13,A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_21266,plain,(
    ! [B_345,A_346] :
      ( m1_subset_1(B_345,A_346)
      | ~ r2_hidden(B_345,A_346)
      | v1_xboole_0(A_346) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_21273,plain,(
    ! [C_13,A_9] :
      ( m1_subset_1(C_13,k1_zfmisc_1(A_9))
      | v1_xboole_0(k1_zfmisc_1(A_9))
      | ~ r1_tarski(C_13,A_9) ) ),
    inference(resolution,[status(thm)],[c_12,c_21266])).

tff(c_50,plain,(
    r1_tarski('#skF_5',k3_subset_1('#skF_4','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_22568,plain,(
    ! [C_420,A_421,B_422] :
      ( r1_tarski(C_420,k3_subset_1(A_421,B_422))
      | ~ r1_tarski(B_422,k3_subset_1(A_421,C_420))
      | ~ m1_subset_1(C_420,k1_zfmisc_1(A_421))
      | ~ m1_subset_1(B_422,k1_zfmisc_1(A_421)) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_22593,plain,
    ( r1_tarski('#skF_6',k3_subset_1('#skF_4','#skF_5'))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1('#skF_4'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_50,c_22568])).

tff(c_22616,plain,
    ( r1_tarski('#skF_6',k3_subset_1('#skF_4','#skF_5'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_22593])).

tff(c_22671,plain,(
    ~ m1_subset_1('#skF_5',k1_zfmisc_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_22616])).

tff(c_22674,plain,
    ( v1_xboole_0(k1_zfmisc_1('#skF_4'))
    | ~ r1_tarski('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_21273,c_22671])).

tff(c_22680,plain,(
    v1_xboole_0(k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_21865,c_22674])).

tff(c_22682,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_21265,c_22680])).

tff(c_22684,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_22616])).

tff(c_34,plain,(
    ! [A_18,B_19] :
      ( m1_subset_1(k3_subset_1(A_18,B_19),k1_zfmisc_1(A_18))
      | ~ m1_subset_1(B_19,k1_zfmisc_1(A_18)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_21302,plain,(
    ! [A_352,C_353,B_354] :
      ( r1_tarski(A_352,C_353)
      | ~ r1_tarski(B_354,C_353)
      | ~ r1_tarski(A_352,B_354) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_21351,plain,(
    ! [A_358] :
      ( r1_tarski(A_358,k3_subset_1('#skF_4','#skF_6'))
      | ~ r1_tarski(A_358,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_50,c_21302])).

tff(c_21665,plain,(
    ! [A_378,A_379] :
      ( r1_tarski(A_378,k3_subset_1('#skF_4','#skF_6'))
      | ~ r1_tarski(A_378,A_379)
      | ~ r1_tarski(A_379,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_21351,c_6])).

tff(c_21691,plain,
    ( r1_tarski('#skF_6',k3_subset_1('#skF_4','#skF_6'))
    | ~ r1_tarski('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_21549,c_21665])).

tff(c_21900,plain,(
    ~ r1_tarski('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_21691])).

tff(c_36,plain,(
    ! [A_20,B_21] :
      ( k3_subset_1(A_20,k3_subset_1(A_20,B_21)) = B_21
      | ~ m1_subset_1(B_21,k1_zfmisc_1(A_20)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_22699,plain,(
    k3_subset_1('#skF_4',k3_subset_1('#skF_4','#skF_5')) = '#skF_5' ),
    inference(resolution,[status(thm)],[c_22684,c_36])).

tff(c_22586,plain,(
    ! [A_29,B_422] :
      ( r1_tarski(A_29,k3_subset_1(A_29,B_422))
      | ~ r1_tarski(B_422,k1_xboole_0)
      | ~ m1_subset_1(A_29,k1_zfmisc_1(A_29))
      | ~ m1_subset_1(B_422,k1_zfmisc_1(A_29)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_21406,c_22568])).

tff(c_23992,plain,(
    ! [A_461,B_462] :
      ( r1_tarski(A_461,k3_subset_1(A_461,B_462))
      | ~ r1_tarski(B_462,k1_xboole_0)
      | ~ m1_subset_1(B_462,k1_zfmisc_1(A_461)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_21489,c_22586])).

tff(c_24018,plain,
    ( r1_tarski('#skF_4','#skF_5')
    | ~ r1_tarski(k3_subset_1('#skF_4','#skF_5'),k1_xboole_0)
    | ~ m1_subset_1(k3_subset_1('#skF_4','#skF_5'),k1_zfmisc_1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_22699,c_23992])).

tff(c_24040,plain,
    ( ~ r1_tarski(k3_subset_1('#skF_4','#skF_5'),k1_xboole_0)
    | ~ m1_subset_1(k3_subset_1('#skF_4','#skF_5'),k1_zfmisc_1('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_21900,c_24018])).

tff(c_24048,plain,(
    ~ m1_subset_1(k3_subset_1('#skF_4','#skF_5'),k1_zfmisc_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_24040])).

tff(c_24112,plain,(
    ~ m1_subset_1('#skF_5',k1_zfmisc_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_34,c_24048])).

tff(c_24122,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22684,c_24112])).

tff(c_24124,plain,(
    m1_subset_1(k3_subset_1('#skF_4','#skF_5'),k1_zfmisc_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_24040])).

tff(c_22683,plain,(
    r1_tarski('#skF_6',k3_subset_1('#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_22616])).

tff(c_22800,plain,(
    ! [A_429] :
      ( r1_tarski(A_429,k3_subset_1('#skF_4','#skF_5'))
      | ~ r1_tarski(A_429,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_22683,c_6])).

tff(c_23341,plain,(
    ! [A_449,A_450] :
      ( r1_tarski(A_449,k3_subset_1('#skF_4','#skF_5'))
      | ~ r1_tarski(A_449,A_450)
      | ~ r1_tarski(A_450,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_22800,c_6])).

tff(c_23393,plain,
    ( r1_tarski('#skF_5',k3_subset_1('#skF_4','#skF_5'))
    | ~ r1_tarski('#skF_6','#skF_6') ),
    inference(resolution,[status(thm)],[c_52,c_23341])).

tff(c_23430,plain,(
    r1_tarski('#skF_5',k3_subset_1('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_21782,c_23393])).

tff(c_22870,plain,(
    ! [A_432,B_433] :
      ( k3_subset_1(A_432,k3_subset_1(A_432,k3_subset_1(A_432,B_433))) = k3_subset_1(A_432,B_433)
      | ~ m1_subset_1(B_433,k1_zfmisc_1(A_432)) ) ),
    inference(resolution,[status(thm)],[c_21469,c_36])).

tff(c_44,plain,(
    ! [A_27,B_28] :
      ( k2_subset_1(A_27) = B_28
      | ~ r1_tarski(k3_subset_1(A_27,B_28),B_28)
      | ~ m1_subset_1(B_28,k1_zfmisc_1(A_27)) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_55,plain,(
    ! [B_28,A_27] :
      ( B_28 = A_27
      | ~ r1_tarski(k3_subset_1(A_27,B_28),B_28)
      | ~ m1_subset_1(B_28,k1_zfmisc_1(A_27)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_44])).

tff(c_38996,plain,(
    ! [A_681,B_682] :
      ( k3_subset_1(A_681,k3_subset_1(A_681,B_682)) = A_681
      | ~ r1_tarski(k3_subset_1(A_681,B_682),k3_subset_1(A_681,k3_subset_1(A_681,B_682)))
      | ~ m1_subset_1(k3_subset_1(A_681,k3_subset_1(A_681,B_682)),k1_zfmisc_1(A_681))
      | ~ m1_subset_1(B_682,k1_zfmisc_1(A_681)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22870,c_55])).

tff(c_39063,plain,
    ( k3_subset_1('#skF_4',k3_subset_1('#skF_4',k3_subset_1('#skF_4','#skF_5'))) = '#skF_4'
    | ~ r1_tarski('#skF_5',k3_subset_1('#skF_4',k3_subset_1('#skF_4',k3_subset_1('#skF_4','#skF_5'))))
    | ~ m1_subset_1(k3_subset_1('#skF_4',k3_subset_1('#skF_4',k3_subset_1('#skF_4','#skF_5'))),k1_zfmisc_1('#skF_4'))
    | ~ m1_subset_1(k3_subset_1('#skF_4','#skF_5'),k1_zfmisc_1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_22699,c_38996])).

tff(c_39108,plain,(
    k3_subset_1('#skF_4','#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24124,c_24124,c_22699,c_23430,c_22699,c_22699,c_39063])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_98,plain,(
    ! [C_42,A_43] :
      ( r1_tarski(C_42,A_43)
      | ~ r2_hidden(C_42,k1_zfmisc_1(A_43)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_107,plain,(
    ! [A_43] :
      ( r1_tarski('#skF_1'(k1_zfmisc_1(A_43)),A_43)
      | v1_xboole_0(k1_zfmisc_1(A_43)) ) ),
    inference(resolution,[status(thm)],[c_4,c_98])).

tff(c_22598,plain,(
    ! [C_420,A_421] :
      ( r1_tarski(C_420,k3_subset_1(A_421,k1_xboole_0))
      | ~ m1_subset_1(C_420,k1_zfmisc_1(A_421))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_421)) ) ),
    inference(resolution,[status(thm)],[c_8,c_22568])).

tff(c_22621,plain,(
    ! [C_420,A_421] :
      ( r1_tarski(C_420,A_421)
      | ~ m1_subset_1(C_420,k1_zfmisc_1(A_421)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_58,c_22598])).

tff(c_24136,plain,(
    r1_tarski(k3_subset_1('#skF_4','#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_24124,c_22621])).

tff(c_24156,plain,(
    ! [A_464] :
      ( r1_tarski(A_464,'#skF_4')
      | ~ r1_tarski(A_464,k3_subset_1('#skF_4','#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_24136,c_6])).

tff(c_24245,plain,
    ( r1_tarski('#skF_1'(k1_zfmisc_1(k3_subset_1('#skF_4','#skF_5'))),'#skF_4')
    | v1_xboole_0(k1_zfmisc_1(k3_subset_1('#skF_4','#skF_5'))) ),
    inference(resolution,[status(thm)],[c_107,c_24156])).

tff(c_27695,plain,(
    v1_xboole_0(k1_zfmisc_1(k3_subset_1('#skF_4','#skF_5'))) ),
    inference(splitLeft,[status(thm)],[c_24245])).

tff(c_27880,plain,(
    ! [C_38] : ~ r1_tarski(C_38,k3_subset_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_27695,c_96])).

tff(c_22292,plain,(
    ! [A_411,B_412] :
      ( r1_tarski('#skF_2'(A_411,B_412),A_411)
      | r2_hidden('#skF_3'(A_411,B_412),B_412)
      | k1_zfmisc_1(A_411) = B_412 ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_23849,plain,(
    ! [A_459,A_460] :
      ( r1_tarski('#skF_3'(A_459,k1_zfmisc_1(A_460)),A_460)
      | r1_tarski('#skF_2'(A_459,k1_zfmisc_1(A_460)),A_459)
      | k1_zfmisc_1(A_460) = k1_zfmisc_1(A_459) ) ),
    inference(resolution,[status(thm)],[c_22292,c_10])).

tff(c_21317,plain,(
    ! [A_352] :
      ( r1_tarski(A_352,'#skF_6')
      | ~ r1_tarski(A_352,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_52,c_21302])).

tff(c_25921,plain,(
    ! [A_493] :
      ( r1_tarski('#skF_3'(A_493,k1_zfmisc_1('#skF_5')),'#skF_6')
      | r1_tarski('#skF_2'(A_493,k1_zfmisc_1('#skF_5')),A_493)
      | k1_zfmisc_1(A_493) = k1_zfmisc_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_23849,c_21317])).

tff(c_16,plain,(
    ! [A_9,B_10] :
      ( r1_tarski('#skF_2'(A_9,B_10),A_9)
      | ~ r1_tarski('#skF_3'(A_9,B_10),A_9)
      | k1_zfmisc_1(A_9) = B_10 ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_26008,plain,
    ( r1_tarski('#skF_2'('#skF_6',k1_zfmisc_1('#skF_5')),'#skF_6')
    | k1_zfmisc_1('#skF_5') = k1_zfmisc_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_25921,c_16])).

tff(c_26068,plain,(
    k1_zfmisc_1('#skF_5') = k1_zfmisc_1('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_26008])).

tff(c_42,plain,(
    ! [A_27] :
      ( r1_tarski(k3_subset_1(A_27,k2_subset_1(A_27)),k2_subset_1(A_27))
      | ~ m1_subset_1(k2_subset_1(A_27),k1_zfmisc_1(A_27)) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_56,plain,(
    ! [A_27] :
      ( r1_tarski(k3_subset_1(A_27,A_27),A_27)
      | ~ m1_subset_1(A_27,k1_zfmisc_1(A_27)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_32,c_32,c_42])).

tff(c_21318,plain,(
    ! [A_355,A_356] :
      ( r1_tarski(A_355,A_356)
      | ~ r1_tarski(A_355,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_8,c_21302])).

tff(c_21331,plain,(
    ! [A_356] :
      ( r1_tarski('#skF_1'(k1_zfmisc_1(k1_xboole_0)),A_356)
      | v1_xboole_0(k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_107,c_21318])).

tff(c_21355,plain,(
    v1_xboole_0(k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_21331])).

tff(c_21359,plain,(
    ! [C_359] : ~ r1_tarski(C_359,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_21355,c_96])).

tff(c_21363,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_56,c_21359])).

tff(c_21374,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_21363])).

tff(c_21375,plain,(
    ! [A_356] : r1_tarski('#skF_1'(k1_zfmisc_1(k1_xboole_0)),A_356) ),
    inference(splitRight,[status(thm)],[c_21331])).

tff(c_21334,plain,(
    ! [A_357] :
      ( r1_tarski(A_357,'#skF_6')
      | ~ r1_tarski(A_357,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_52,c_21302])).

tff(c_21348,plain,
    ( r1_tarski('#skF_1'(k1_zfmisc_1('#skF_5')),'#skF_6')
    | v1_xboole_0(k1_zfmisc_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_107,c_21334])).

tff(c_21431,plain,(
    v1_xboole_0(k1_zfmisc_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_21348])).

tff(c_21436,plain,(
    ! [C_364] : ~ r1_tarski(C_364,'#skF_5') ),
    inference(resolution,[status(thm)],[c_21431,c_96])).

tff(c_21448,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_21375,c_21436])).

tff(c_21450,plain,(
    ~ v1_xboole_0(k1_zfmisc_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_21348])).

tff(c_22158,plain,(
    ! [A_408,B_409] :
      ( r1_tarski(k3_subset_1(A_408,B_409),A_408)
      | v1_xboole_0(k1_zfmisc_1(A_408))
      | ~ m1_subset_1(B_409,k1_zfmisc_1(A_408)) ) ),
    inference(resolution,[status(thm)],[c_34,c_21520])).

tff(c_22204,plain,(
    ! [B_409] :
      ( r1_tarski(k3_subset_1('#skF_5',B_409),'#skF_6')
      | v1_xboole_0(k1_zfmisc_1('#skF_5'))
      | ~ m1_subset_1(B_409,k1_zfmisc_1('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_22158,c_21317])).

tff(c_22375,plain,(
    ! [B_414] :
      ( r1_tarski(k3_subset_1('#skF_5',B_414),'#skF_6')
      | ~ m1_subset_1(B_414,k1_zfmisc_1('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_21450,c_22204])).

tff(c_22397,plain,
    ( '#skF_5' = '#skF_6'
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_22375,c_55])).

tff(c_22403,plain,(
    ~ m1_subset_1('#skF_6',k1_zfmisc_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_22397])).

tff(c_26084,plain,(
    ~ m1_subset_1('#skF_6',k1_zfmisc_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26068,c_22403])).

tff(c_26093,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_21489,c_26084])).

tff(c_26094,plain,(
    r1_tarski('#skF_2'('#skF_6',k1_zfmisc_1('#skF_5')),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_26008])).

tff(c_22821,plain,(
    ! [A_5,A_429] :
      ( r1_tarski(A_5,k3_subset_1('#skF_4','#skF_5'))
      | ~ r1_tarski(A_5,A_429)
      | ~ r1_tarski(A_429,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_22800,c_6])).

tff(c_26109,plain,
    ( r1_tarski('#skF_2'('#skF_6',k1_zfmisc_1('#skF_5')),k3_subset_1('#skF_4','#skF_5'))
    | ~ r1_tarski('#skF_6','#skF_6') ),
    inference(resolution,[status(thm)],[c_26094,c_22821])).

tff(c_26120,plain,(
    r1_tarski('#skF_2'('#skF_6',k1_zfmisc_1('#skF_5')),k3_subset_1('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_21782,c_26109])).

tff(c_27898,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_27880,c_26120])).

tff(c_27900,plain,(
    ~ v1_xboole_0(k1_zfmisc_1(k3_subset_1('#skF_4','#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_24245])).

tff(c_22631,plain,(
    ! [C_423,A_424] :
      ( r1_tarski(C_423,A_424)
      | ~ m1_subset_1(C_423,k1_zfmisc_1(A_424)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_58,c_22598])).

tff(c_22663,plain,(
    ! [A_18,B_19] :
      ( r1_tarski(k3_subset_1(A_18,B_19),A_18)
      | ~ m1_subset_1(B_19,k1_zfmisc_1(A_18)) ) ),
    inference(resolution,[status(thm)],[c_34,c_22631])).

tff(c_33075,plain,(
    ! [B_613] :
      ( r1_tarski(k3_subset_1(k3_subset_1('#skF_4','#skF_5'),B_613),'#skF_4')
      | ~ m1_subset_1(B_613,k1_zfmisc_1(k3_subset_1('#skF_4','#skF_5'))) ) ),
    inference(resolution,[status(thm)],[c_22663,c_24156])).

tff(c_33111,plain,
    ( k3_subset_1('#skF_4','#skF_5') = '#skF_4'
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k3_subset_1('#skF_4','#skF_5'))) ),
    inference(resolution,[status(thm)],[c_33075,c_55])).

tff(c_33119,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(k3_subset_1('#skF_4','#skF_5'))) ),
    inference(splitLeft,[status(thm)],[c_33111])).

tff(c_33122,plain,
    ( v1_xboole_0(k1_zfmisc_1(k3_subset_1('#skF_4','#skF_5')))
    | ~ r1_tarski('#skF_4',k3_subset_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_21273,c_33119])).

tff(c_33128,plain,(
    ~ r1_tarski('#skF_4',k3_subset_1('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_27900,c_33122])).

tff(c_39136,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_39108,c_33128])).

tff(c_39167,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_21782,c_39136])).

tff(c_39168,plain,(
    k3_subset_1('#skF_4','#skF_5') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_33111])).

tff(c_21965,plain,(
    ! [C_392,A_393] :
      ( m1_subset_1(C_392,k1_zfmisc_1(A_393))
      | v1_xboole_0(k1_zfmisc_1(A_393))
      | ~ r1_tarski(C_392,A_393) ) ),
    inference(resolution,[status(thm)],[c_12,c_21266])).

tff(c_24335,plain,(
    ! [A_468,C_469] :
      ( k3_subset_1(A_468,k3_subset_1(A_468,C_469)) = C_469
      | v1_xboole_0(k1_zfmisc_1(A_468))
      | ~ r1_tarski(C_469,A_468) ) ),
    inference(resolution,[status(thm)],[c_21965,c_36])).

tff(c_25253,plain,(
    ! [C_477,A_478,C_479] :
      ( ~ r1_tarski(C_477,A_478)
      | k3_subset_1(A_478,k3_subset_1(A_478,C_479)) = C_479
      | ~ r1_tarski(C_479,A_478) ) ),
    inference(resolution,[status(thm)],[c_24335,c_96])).

tff(c_25363,plain,(
    ! [A_8,C_479] :
      ( k3_subset_1(A_8,k3_subset_1(A_8,C_479)) = C_479
      | ~ r1_tarski(C_479,A_8) ) ),
    inference(resolution,[status(thm)],[c_8,c_25253])).

tff(c_39246,plain,
    ( k3_subset_1('#skF_4','#skF_4') = '#skF_5'
    | ~ r1_tarski('#skF_5','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_39168,c_25363])).

tff(c_39298,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_21865,c_21406,c_39246])).

tff(c_39300,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_39298])).

tff(c_39301,plain,(
    '#skF_5' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_22397])).

tff(c_21449,plain,(
    r1_tarski('#skF_1'(k1_zfmisc_1('#skF_5')),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_21348])).

tff(c_21692,plain,
    ( r1_tarski('#skF_1'(k1_zfmisc_1('#skF_5')),k3_subset_1('#skF_4','#skF_6'))
    | ~ r1_tarski('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_21449,c_21665])).

tff(c_21991,plain,(
    ~ r1_tarski('#skF_6','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_21692])).

tff(c_39305,plain,(
    ~ r1_tarski('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_39301,c_21991])).

tff(c_39322,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_21782,c_39305])).

tff(c_39324,plain,(
    r1_tarski('#skF_6','#skF_5') ),
    inference(splitRight,[status(thm)],[c_21692])).

tff(c_21407,plain,(
    k3_subset_1('#skF_4',k3_subset_1('#skF_4','#skF_6')) = '#skF_6' ),
    inference(resolution,[status(thm)],[c_54,c_21392])).

tff(c_21602,plain,(
    ! [B_375,A_376] :
      ( B_375 = A_376
      | ~ r1_tarski(k3_subset_1(A_376,B_375),B_375)
      | ~ m1_subset_1(B_375,k1_zfmisc_1(A_376)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_44])).

tff(c_21605,plain,
    ( k3_subset_1('#skF_4','#skF_6') = '#skF_4'
    | ~ r1_tarski('#skF_6',k3_subset_1('#skF_4','#skF_6'))
    | ~ m1_subset_1(k3_subset_1('#skF_4','#skF_6'),k1_zfmisc_1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_21407,c_21602])).

tff(c_39325,plain,(
    ~ m1_subset_1(k3_subset_1('#skF_4','#skF_6'),k1_zfmisc_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_21605])).

tff(c_39356,plain,(
    ~ m1_subset_1('#skF_6',k1_zfmisc_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_34,c_39325])).

tff(c_39366,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_39356])).

tff(c_39368,plain,(
    m1_subset_1(k3_subset_1('#skF_4','#skF_6'),k1_zfmisc_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_21605])).

tff(c_21315,plain,(
    ! [A_352] :
      ( r1_tarski(A_352,k3_subset_1('#skF_4','#skF_6'))
      | ~ r1_tarski(A_352,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_50,c_21302])).

tff(c_39452,plain,(
    ! [A_686] :
      ( k3_subset_1('#skF_4','#skF_6') = A_686
      | ~ m1_subset_1(k3_subset_1('#skF_4','#skF_6'),k1_zfmisc_1(A_686))
      | ~ r1_tarski(k3_subset_1(A_686,k3_subset_1('#skF_4','#skF_6')),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_21315,c_21602])).

tff(c_39458,plain,
    ( k3_subset_1('#skF_4','#skF_6') = '#skF_4'
    | ~ m1_subset_1(k3_subset_1('#skF_4','#skF_6'),k1_zfmisc_1('#skF_4'))
    | ~ r1_tarski('#skF_6','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_21407,c_39452])).

tff(c_39465,plain,(
    k3_subset_1('#skF_4','#skF_6') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_39324,c_39368,c_39458])).

tff(c_39474,plain,(
    k3_subset_1('#skF_4','#skF_4') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_39465,c_21407])).

tff(c_39503,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_39474,c_21406])).

tff(c_39525,plain,(
    '#skF_5' != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_39503,c_48])).

tff(c_21615,plain,(
    ! [A_22] :
      ( k1_xboole_0 = A_22
      | ~ r1_tarski(A_22,k1_xboole_0)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_22)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_21602])).

tff(c_21621,plain,(
    ! [A_22] :
      ( k1_xboole_0 = A_22
      | ~ r1_tarski(A_22,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_21615])).

tff(c_39749,plain,(
    ! [A_698] :
      ( A_698 = '#skF_6'
      | ~ r1_tarski(A_698,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_39503,c_39503,c_21621])).

tff(c_39769,plain,(
    '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_52,c_39749])).

tff(c_39781,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_39525,c_39769])).

tff(c_39783,plain,(
    v1_xboole_0(k1_zfmisc_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_116])).

tff(c_39787,plain,(
    ! [C_699] : ~ r1_tarski(C_699,'#skF_4') ),
    inference(resolution,[status(thm)],[c_39783,c_96])).

tff(c_39792,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_8,c_39787])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n017.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:37:16 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 14.55/6.45  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.55/6.47  
% 14.55/6.47  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.55/6.47  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k3_subset_1 > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2
% 14.55/6.47  
% 14.55/6.47  %Foreground sorts:
% 14.55/6.47  
% 14.55/6.47  
% 14.55/6.47  %Background operators:
% 14.55/6.47  
% 14.55/6.47  
% 14.55/6.47  %Foreground operators:
% 14.55/6.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 14.55/6.47  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 14.55/6.47  tff('#skF_1', type, '#skF_1': $i > $i).
% 14.55/6.47  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 14.55/6.47  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 14.55/6.47  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 14.55/6.47  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 14.55/6.47  tff('#skF_5', type, '#skF_5': $i).
% 14.55/6.47  tff('#skF_6', type, '#skF_6': $i).
% 14.55/6.47  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 14.55/6.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 14.55/6.47  tff('#skF_4', type, '#skF_4': $i).
% 14.55/6.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 14.55/6.47  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 14.55/6.47  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 14.55/6.47  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 14.55/6.47  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 14.55/6.47  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 14.55/6.47  
% 14.83/6.50  tff(f_39, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 14.83/6.50  tff(f_90, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 14.83/6.50  tff(f_61, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_subset_1)).
% 14.83/6.50  tff(f_63, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 14.83/6.50  tff(f_73, axiom, (![A]: (k2_subset_1(A) = k3_subset_1(A, k1_subset_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_subset_1)).
% 14.83/6.50  tff(f_67, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 14.83/6.50  tff(f_59, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 14.83/6.50  tff(f_46, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 14.83/6.50  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 14.83/6.50  tff(f_99, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => ((r1_tarski(B, C) & r1_tarski(B, k3_subset_1(A, C))) => (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_subset_1)).
% 14.83/6.50  tff(f_37, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 14.83/6.50  tff(f_71, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 14.83/6.50  tff(f_82, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(B, k3_subset_1(A, C)) => r1_tarski(C, k3_subset_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_subset_1)).
% 14.83/6.50  tff(f_88, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (r1_tarski(k3_subset_1(A, B), B) <=> (B = k2_subset_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_subset_1)).
% 14.83/6.50  tff(c_8, plain, (![A_8]: (r1_tarski(k1_xboole_0, A_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 14.83/6.50  tff(c_46, plain, (![A_29]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_29)))), inference(cnfTransformation, [status(thm)], [f_90])).
% 14.83/6.50  tff(c_30, plain, (![A_16]: (k1_subset_1(A_16)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_61])).
% 14.83/6.50  tff(c_32, plain, (![A_17]: (k2_subset_1(A_17)=A_17)), inference(cnfTransformation, [status(thm)], [f_63])).
% 14.83/6.50  tff(c_38, plain, (![A_22]: (k3_subset_1(A_22, k1_subset_1(A_22))=k2_subset_1(A_22))), inference(cnfTransformation, [status(thm)], [f_73])).
% 14.83/6.50  tff(c_57, plain, (![A_22]: (k3_subset_1(A_22, k1_subset_1(A_22))=A_22)), inference(demodulation, [status(thm), theory('equality')], [c_32, c_38])).
% 14.83/6.50  tff(c_58, plain, (![A_22]: (k3_subset_1(A_22, k1_xboole_0)=A_22)), inference(demodulation, [status(thm), theory('equality')], [c_30, c_57])).
% 14.83/6.50  tff(c_21469, plain, (![A_367, B_368]: (m1_subset_1(k3_subset_1(A_367, B_368), k1_zfmisc_1(A_367)) | ~m1_subset_1(B_368, k1_zfmisc_1(A_367)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 14.83/6.50  tff(c_21483, plain, (![A_22]: (m1_subset_1(A_22, k1_zfmisc_1(A_22)) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_22)))), inference(superposition, [status(thm), theory('equality')], [c_58, c_21469])).
% 14.83/6.50  tff(c_21489, plain, (![A_22]: (m1_subset_1(A_22, k1_zfmisc_1(A_22)))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_21483])).
% 14.83/6.50  tff(c_21280, plain, (![B_348, A_349]: (r2_hidden(B_348, A_349) | ~m1_subset_1(B_348, A_349) | v1_xboole_0(A_349))), inference(cnfTransformation, [status(thm)], [f_59])).
% 14.83/6.50  tff(c_10, plain, (![C_13, A_9]: (r1_tarski(C_13, A_9) | ~r2_hidden(C_13, k1_zfmisc_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 14.83/6.50  tff(c_21520, plain, (![B_372, A_373]: (r1_tarski(B_372, A_373) | ~m1_subset_1(B_372, k1_zfmisc_1(A_373)) | v1_xboole_0(k1_zfmisc_1(A_373)))), inference(resolution, [status(thm)], [c_21280, c_10])).
% 14.83/6.50  tff(c_21553, plain, (![A_374]: (r1_tarski(A_374, A_374) | v1_xboole_0(k1_zfmisc_1(A_374)))), inference(resolution, [status(thm)], [c_21489, c_21520])).
% 14.83/6.50  tff(c_92, plain, (![C_38, A_39]: (r2_hidden(C_38, k1_zfmisc_1(A_39)) | ~r1_tarski(C_38, A_39))), inference(cnfTransformation, [status(thm)], [f_46])).
% 14.83/6.50  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 14.83/6.50  tff(c_96, plain, (![A_39, C_38]: (~v1_xboole_0(k1_zfmisc_1(A_39)) | ~r1_tarski(C_38, A_39))), inference(resolution, [status(thm)], [c_92, c_2])).
% 14.83/6.50  tff(c_21747, plain, (![C_381, A_382]: (~r1_tarski(C_381, A_382) | r1_tarski(A_382, A_382))), inference(resolution, [status(thm)], [c_21553, c_96])).
% 14.83/6.50  tff(c_21782, plain, (![A_8]: (r1_tarski(A_8, A_8))), inference(resolution, [status(thm)], [c_8, c_21747])).
% 14.83/6.50  tff(c_48, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_99])).
% 14.83/6.50  tff(c_52, plain, (r1_tarski('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_99])).
% 14.83/6.50  tff(c_54, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_99])).
% 14.83/6.50  tff(c_108, plain, (![B_44, A_45]: (v1_xboole_0(B_44) | ~m1_subset_1(B_44, A_45) | ~v1_xboole_0(A_45))), inference(cnfTransformation, [status(thm)], [f_59])).
% 14.83/6.50  tff(c_116, plain, (v1_xboole_0('#skF_6') | ~v1_xboole_0(k1_zfmisc_1('#skF_4'))), inference(resolution, [status(thm)], [c_54, c_108])).
% 14.83/6.50  tff(c_21265, plain, (~v1_xboole_0(k1_zfmisc_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_116])).
% 14.83/6.50  tff(c_21540, plain, (r1_tarski('#skF_6', '#skF_4') | v1_xboole_0(k1_zfmisc_1('#skF_4'))), inference(resolution, [status(thm)], [c_54, c_21520])).
% 14.83/6.50  tff(c_21549, plain, (r1_tarski('#skF_6', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_21265, c_21540])).
% 14.83/6.50  tff(c_6, plain, (![A_5, C_7, B_6]: (r1_tarski(A_5, C_7) | ~r1_tarski(B_6, C_7) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 14.83/6.50  tff(c_21840, plain, (![A_386]: (r1_tarski(A_386, '#skF_4') | ~r1_tarski(A_386, '#skF_6'))), inference(resolution, [status(thm)], [c_21549, c_6])).
% 14.83/6.50  tff(c_21865, plain, (r1_tarski('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_52, c_21840])).
% 14.83/6.50  tff(c_21392, plain, (![A_361, B_362]: (k3_subset_1(A_361, k3_subset_1(A_361, B_362))=B_362 | ~m1_subset_1(B_362, k1_zfmisc_1(A_361)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 14.83/6.50  tff(c_21400, plain, (![A_29]: (k3_subset_1(A_29, k3_subset_1(A_29, k1_xboole_0))=k1_xboole_0)), inference(resolution, [status(thm)], [c_46, c_21392])).
% 14.83/6.50  tff(c_21406, plain, (![A_29]: (k3_subset_1(A_29, A_29)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_58, c_21400])).
% 14.83/6.50  tff(c_12, plain, (![C_13, A_9]: (r2_hidden(C_13, k1_zfmisc_1(A_9)) | ~r1_tarski(C_13, A_9))), inference(cnfTransformation, [status(thm)], [f_46])).
% 14.83/6.50  tff(c_21266, plain, (![B_345, A_346]: (m1_subset_1(B_345, A_346) | ~r2_hidden(B_345, A_346) | v1_xboole_0(A_346))), inference(cnfTransformation, [status(thm)], [f_59])).
% 14.83/6.50  tff(c_21273, plain, (![C_13, A_9]: (m1_subset_1(C_13, k1_zfmisc_1(A_9)) | v1_xboole_0(k1_zfmisc_1(A_9)) | ~r1_tarski(C_13, A_9))), inference(resolution, [status(thm)], [c_12, c_21266])).
% 14.83/6.50  tff(c_50, plain, (r1_tarski('#skF_5', k3_subset_1('#skF_4', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_99])).
% 14.83/6.50  tff(c_22568, plain, (![C_420, A_421, B_422]: (r1_tarski(C_420, k3_subset_1(A_421, B_422)) | ~r1_tarski(B_422, k3_subset_1(A_421, C_420)) | ~m1_subset_1(C_420, k1_zfmisc_1(A_421)) | ~m1_subset_1(B_422, k1_zfmisc_1(A_421)))), inference(cnfTransformation, [status(thm)], [f_82])).
% 14.83/6.50  tff(c_22593, plain, (r1_tarski('#skF_6', k3_subset_1('#skF_4', '#skF_5')) | ~m1_subset_1('#skF_6', k1_zfmisc_1('#skF_4')) | ~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_4'))), inference(resolution, [status(thm)], [c_50, c_22568])).
% 14.83/6.50  tff(c_22616, plain, (r1_tarski('#skF_6', k3_subset_1('#skF_4', '#skF_5')) | ~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_22593])).
% 14.83/6.50  tff(c_22671, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_22616])).
% 14.83/6.50  tff(c_22674, plain, (v1_xboole_0(k1_zfmisc_1('#skF_4')) | ~r1_tarski('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_21273, c_22671])).
% 14.83/6.50  tff(c_22680, plain, (v1_xboole_0(k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_21865, c_22674])).
% 14.83/6.50  tff(c_22682, plain, $false, inference(negUnitSimplification, [status(thm)], [c_21265, c_22680])).
% 14.83/6.50  tff(c_22684, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_4'))), inference(splitRight, [status(thm)], [c_22616])).
% 14.83/6.50  tff(c_34, plain, (![A_18, B_19]: (m1_subset_1(k3_subset_1(A_18, B_19), k1_zfmisc_1(A_18)) | ~m1_subset_1(B_19, k1_zfmisc_1(A_18)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 14.83/6.50  tff(c_21302, plain, (![A_352, C_353, B_354]: (r1_tarski(A_352, C_353) | ~r1_tarski(B_354, C_353) | ~r1_tarski(A_352, B_354))), inference(cnfTransformation, [status(thm)], [f_37])).
% 14.83/6.50  tff(c_21351, plain, (![A_358]: (r1_tarski(A_358, k3_subset_1('#skF_4', '#skF_6')) | ~r1_tarski(A_358, '#skF_5'))), inference(resolution, [status(thm)], [c_50, c_21302])).
% 14.83/6.50  tff(c_21665, plain, (![A_378, A_379]: (r1_tarski(A_378, k3_subset_1('#skF_4', '#skF_6')) | ~r1_tarski(A_378, A_379) | ~r1_tarski(A_379, '#skF_5'))), inference(resolution, [status(thm)], [c_21351, c_6])).
% 14.83/6.50  tff(c_21691, plain, (r1_tarski('#skF_6', k3_subset_1('#skF_4', '#skF_6')) | ~r1_tarski('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_21549, c_21665])).
% 14.83/6.50  tff(c_21900, plain, (~r1_tarski('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_21691])).
% 14.83/6.50  tff(c_36, plain, (![A_20, B_21]: (k3_subset_1(A_20, k3_subset_1(A_20, B_21))=B_21 | ~m1_subset_1(B_21, k1_zfmisc_1(A_20)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 14.83/6.50  tff(c_22699, plain, (k3_subset_1('#skF_4', k3_subset_1('#skF_4', '#skF_5'))='#skF_5'), inference(resolution, [status(thm)], [c_22684, c_36])).
% 14.83/6.50  tff(c_22586, plain, (![A_29, B_422]: (r1_tarski(A_29, k3_subset_1(A_29, B_422)) | ~r1_tarski(B_422, k1_xboole_0) | ~m1_subset_1(A_29, k1_zfmisc_1(A_29)) | ~m1_subset_1(B_422, k1_zfmisc_1(A_29)))), inference(superposition, [status(thm), theory('equality')], [c_21406, c_22568])).
% 14.83/6.50  tff(c_23992, plain, (![A_461, B_462]: (r1_tarski(A_461, k3_subset_1(A_461, B_462)) | ~r1_tarski(B_462, k1_xboole_0) | ~m1_subset_1(B_462, k1_zfmisc_1(A_461)))), inference(demodulation, [status(thm), theory('equality')], [c_21489, c_22586])).
% 14.83/6.50  tff(c_24018, plain, (r1_tarski('#skF_4', '#skF_5') | ~r1_tarski(k3_subset_1('#skF_4', '#skF_5'), k1_xboole_0) | ~m1_subset_1(k3_subset_1('#skF_4', '#skF_5'), k1_zfmisc_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_22699, c_23992])).
% 14.83/6.50  tff(c_24040, plain, (~r1_tarski(k3_subset_1('#skF_4', '#skF_5'), k1_xboole_0) | ~m1_subset_1(k3_subset_1('#skF_4', '#skF_5'), k1_zfmisc_1('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_21900, c_24018])).
% 14.83/6.50  tff(c_24048, plain, (~m1_subset_1(k3_subset_1('#skF_4', '#skF_5'), k1_zfmisc_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_24040])).
% 14.83/6.50  tff(c_24112, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_4'))), inference(resolution, [status(thm)], [c_34, c_24048])).
% 14.83/6.50  tff(c_24122, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22684, c_24112])).
% 14.83/6.50  tff(c_24124, plain, (m1_subset_1(k3_subset_1('#skF_4', '#skF_5'), k1_zfmisc_1('#skF_4'))), inference(splitRight, [status(thm)], [c_24040])).
% 14.83/6.50  tff(c_22683, plain, (r1_tarski('#skF_6', k3_subset_1('#skF_4', '#skF_5'))), inference(splitRight, [status(thm)], [c_22616])).
% 14.83/6.50  tff(c_22800, plain, (![A_429]: (r1_tarski(A_429, k3_subset_1('#skF_4', '#skF_5')) | ~r1_tarski(A_429, '#skF_6'))), inference(resolution, [status(thm)], [c_22683, c_6])).
% 14.83/6.50  tff(c_23341, plain, (![A_449, A_450]: (r1_tarski(A_449, k3_subset_1('#skF_4', '#skF_5')) | ~r1_tarski(A_449, A_450) | ~r1_tarski(A_450, '#skF_6'))), inference(resolution, [status(thm)], [c_22800, c_6])).
% 14.83/6.50  tff(c_23393, plain, (r1_tarski('#skF_5', k3_subset_1('#skF_4', '#skF_5')) | ~r1_tarski('#skF_6', '#skF_6')), inference(resolution, [status(thm)], [c_52, c_23341])).
% 14.83/6.50  tff(c_23430, plain, (r1_tarski('#skF_5', k3_subset_1('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_21782, c_23393])).
% 14.83/6.50  tff(c_22870, plain, (![A_432, B_433]: (k3_subset_1(A_432, k3_subset_1(A_432, k3_subset_1(A_432, B_433)))=k3_subset_1(A_432, B_433) | ~m1_subset_1(B_433, k1_zfmisc_1(A_432)))), inference(resolution, [status(thm)], [c_21469, c_36])).
% 14.83/6.50  tff(c_44, plain, (![A_27, B_28]: (k2_subset_1(A_27)=B_28 | ~r1_tarski(k3_subset_1(A_27, B_28), B_28) | ~m1_subset_1(B_28, k1_zfmisc_1(A_27)))), inference(cnfTransformation, [status(thm)], [f_88])).
% 14.83/6.50  tff(c_55, plain, (![B_28, A_27]: (B_28=A_27 | ~r1_tarski(k3_subset_1(A_27, B_28), B_28) | ~m1_subset_1(B_28, k1_zfmisc_1(A_27)))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_44])).
% 14.83/6.50  tff(c_38996, plain, (![A_681, B_682]: (k3_subset_1(A_681, k3_subset_1(A_681, B_682))=A_681 | ~r1_tarski(k3_subset_1(A_681, B_682), k3_subset_1(A_681, k3_subset_1(A_681, B_682))) | ~m1_subset_1(k3_subset_1(A_681, k3_subset_1(A_681, B_682)), k1_zfmisc_1(A_681)) | ~m1_subset_1(B_682, k1_zfmisc_1(A_681)))), inference(superposition, [status(thm), theory('equality')], [c_22870, c_55])).
% 14.83/6.50  tff(c_39063, plain, (k3_subset_1('#skF_4', k3_subset_1('#skF_4', k3_subset_1('#skF_4', '#skF_5')))='#skF_4' | ~r1_tarski('#skF_5', k3_subset_1('#skF_4', k3_subset_1('#skF_4', k3_subset_1('#skF_4', '#skF_5')))) | ~m1_subset_1(k3_subset_1('#skF_4', k3_subset_1('#skF_4', k3_subset_1('#skF_4', '#skF_5'))), k1_zfmisc_1('#skF_4')) | ~m1_subset_1(k3_subset_1('#skF_4', '#skF_5'), k1_zfmisc_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_22699, c_38996])).
% 14.83/6.50  tff(c_39108, plain, (k3_subset_1('#skF_4', '#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_24124, c_24124, c_22699, c_23430, c_22699, c_22699, c_39063])).
% 14.83/6.50  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 14.83/6.50  tff(c_98, plain, (![C_42, A_43]: (r1_tarski(C_42, A_43) | ~r2_hidden(C_42, k1_zfmisc_1(A_43)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 14.83/6.50  tff(c_107, plain, (![A_43]: (r1_tarski('#skF_1'(k1_zfmisc_1(A_43)), A_43) | v1_xboole_0(k1_zfmisc_1(A_43)))), inference(resolution, [status(thm)], [c_4, c_98])).
% 14.83/6.50  tff(c_22598, plain, (![C_420, A_421]: (r1_tarski(C_420, k3_subset_1(A_421, k1_xboole_0)) | ~m1_subset_1(C_420, k1_zfmisc_1(A_421)) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_421)))), inference(resolution, [status(thm)], [c_8, c_22568])).
% 14.83/6.50  tff(c_22621, plain, (![C_420, A_421]: (r1_tarski(C_420, A_421) | ~m1_subset_1(C_420, k1_zfmisc_1(A_421)))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_58, c_22598])).
% 14.83/6.50  tff(c_24136, plain, (r1_tarski(k3_subset_1('#skF_4', '#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_24124, c_22621])).
% 14.83/6.50  tff(c_24156, plain, (![A_464]: (r1_tarski(A_464, '#skF_4') | ~r1_tarski(A_464, k3_subset_1('#skF_4', '#skF_5')))), inference(resolution, [status(thm)], [c_24136, c_6])).
% 14.83/6.50  tff(c_24245, plain, (r1_tarski('#skF_1'(k1_zfmisc_1(k3_subset_1('#skF_4', '#skF_5'))), '#skF_4') | v1_xboole_0(k1_zfmisc_1(k3_subset_1('#skF_4', '#skF_5')))), inference(resolution, [status(thm)], [c_107, c_24156])).
% 14.83/6.50  tff(c_27695, plain, (v1_xboole_0(k1_zfmisc_1(k3_subset_1('#skF_4', '#skF_5')))), inference(splitLeft, [status(thm)], [c_24245])).
% 14.83/6.50  tff(c_27880, plain, (![C_38]: (~r1_tarski(C_38, k3_subset_1('#skF_4', '#skF_5')))), inference(resolution, [status(thm)], [c_27695, c_96])).
% 14.83/6.50  tff(c_22292, plain, (![A_411, B_412]: (r1_tarski('#skF_2'(A_411, B_412), A_411) | r2_hidden('#skF_3'(A_411, B_412), B_412) | k1_zfmisc_1(A_411)=B_412)), inference(cnfTransformation, [status(thm)], [f_46])).
% 14.83/6.50  tff(c_23849, plain, (![A_459, A_460]: (r1_tarski('#skF_3'(A_459, k1_zfmisc_1(A_460)), A_460) | r1_tarski('#skF_2'(A_459, k1_zfmisc_1(A_460)), A_459) | k1_zfmisc_1(A_460)=k1_zfmisc_1(A_459))), inference(resolution, [status(thm)], [c_22292, c_10])).
% 14.83/6.50  tff(c_21317, plain, (![A_352]: (r1_tarski(A_352, '#skF_6') | ~r1_tarski(A_352, '#skF_5'))), inference(resolution, [status(thm)], [c_52, c_21302])).
% 14.83/6.50  tff(c_25921, plain, (![A_493]: (r1_tarski('#skF_3'(A_493, k1_zfmisc_1('#skF_5')), '#skF_6') | r1_tarski('#skF_2'(A_493, k1_zfmisc_1('#skF_5')), A_493) | k1_zfmisc_1(A_493)=k1_zfmisc_1('#skF_5'))), inference(resolution, [status(thm)], [c_23849, c_21317])).
% 14.83/6.50  tff(c_16, plain, (![A_9, B_10]: (r1_tarski('#skF_2'(A_9, B_10), A_9) | ~r1_tarski('#skF_3'(A_9, B_10), A_9) | k1_zfmisc_1(A_9)=B_10)), inference(cnfTransformation, [status(thm)], [f_46])).
% 14.83/6.50  tff(c_26008, plain, (r1_tarski('#skF_2'('#skF_6', k1_zfmisc_1('#skF_5')), '#skF_6') | k1_zfmisc_1('#skF_5')=k1_zfmisc_1('#skF_6')), inference(resolution, [status(thm)], [c_25921, c_16])).
% 14.83/6.50  tff(c_26068, plain, (k1_zfmisc_1('#skF_5')=k1_zfmisc_1('#skF_6')), inference(splitLeft, [status(thm)], [c_26008])).
% 14.83/6.50  tff(c_42, plain, (![A_27]: (r1_tarski(k3_subset_1(A_27, k2_subset_1(A_27)), k2_subset_1(A_27)) | ~m1_subset_1(k2_subset_1(A_27), k1_zfmisc_1(A_27)))), inference(cnfTransformation, [status(thm)], [f_88])).
% 14.83/6.50  tff(c_56, plain, (![A_27]: (r1_tarski(k3_subset_1(A_27, A_27), A_27) | ~m1_subset_1(A_27, k1_zfmisc_1(A_27)))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_32, c_32, c_42])).
% 14.83/6.50  tff(c_21318, plain, (![A_355, A_356]: (r1_tarski(A_355, A_356) | ~r1_tarski(A_355, k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_21302])).
% 14.83/6.50  tff(c_21331, plain, (![A_356]: (r1_tarski('#skF_1'(k1_zfmisc_1(k1_xboole_0)), A_356) | v1_xboole_0(k1_zfmisc_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_107, c_21318])).
% 14.83/6.50  tff(c_21355, plain, (v1_xboole_0(k1_zfmisc_1(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_21331])).
% 14.83/6.50  tff(c_21359, plain, (![C_359]: (~r1_tarski(C_359, k1_xboole_0))), inference(resolution, [status(thm)], [c_21355, c_96])).
% 14.83/6.50  tff(c_21363, plain, (~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_56, c_21359])).
% 14.83/6.50  tff(c_21374, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_21363])).
% 14.83/6.50  tff(c_21375, plain, (![A_356]: (r1_tarski('#skF_1'(k1_zfmisc_1(k1_xboole_0)), A_356))), inference(splitRight, [status(thm)], [c_21331])).
% 14.83/6.50  tff(c_21334, plain, (![A_357]: (r1_tarski(A_357, '#skF_6') | ~r1_tarski(A_357, '#skF_5'))), inference(resolution, [status(thm)], [c_52, c_21302])).
% 14.83/6.50  tff(c_21348, plain, (r1_tarski('#skF_1'(k1_zfmisc_1('#skF_5')), '#skF_6') | v1_xboole_0(k1_zfmisc_1('#skF_5'))), inference(resolution, [status(thm)], [c_107, c_21334])).
% 14.83/6.50  tff(c_21431, plain, (v1_xboole_0(k1_zfmisc_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_21348])).
% 14.83/6.50  tff(c_21436, plain, (![C_364]: (~r1_tarski(C_364, '#skF_5'))), inference(resolution, [status(thm)], [c_21431, c_96])).
% 14.83/6.50  tff(c_21448, plain, $false, inference(resolution, [status(thm)], [c_21375, c_21436])).
% 14.83/6.50  tff(c_21450, plain, (~v1_xboole_0(k1_zfmisc_1('#skF_5'))), inference(splitRight, [status(thm)], [c_21348])).
% 14.83/6.50  tff(c_22158, plain, (![A_408, B_409]: (r1_tarski(k3_subset_1(A_408, B_409), A_408) | v1_xboole_0(k1_zfmisc_1(A_408)) | ~m1_subset_1(B_409, k1_zfmisc_1(A_408)))), inference(resolution, [status(thm)], [c_34, c_21520])).
% 14.83/6.50  tff(c_22204, plain, (![B_409]: (r1_tarski(k3_subset_1('#skF_5', B_409), '#skF_6') | v1_xboole_0(k1_zfmisc_1('#skF_5')) | ~m1_subset_1(B_409, k1_zfmisc_1('#skF_5')))), inference(resolution, [status(thm)], [c_22158, c_21317])).
% 14.83/6.50  tff(c_22375, plain, (![B_414]: (r1_tarski(k3_subset_1('#skF_5', B_414), '#skF_6') | ~m1_subset_1(B_414, k1_zfmisc_1('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_21450, c_22204])).
% 14.83/6.50  tff(c_22397, plain, ('#skF_5'='#skF_6' | ~m1_subset_1('#skF_6', k1_zfmisc_1('#skF_5'))), inference(resolution, [status(thm)], [c_22375, c_55])).
% 14.83/6.50  tff(c_22403, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_22397])).
% 14.83/6.50  tff(c_26084, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_26068, c_22403])).
% 14.83/6.50  tff(c_26093, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_21489, c_26084])).
% 14.83/6.50  tff(c_26094, plain, (r1_tarski('#skF_2'('#skF_6', k1_zfmisc_1('#skF_5')), '#skF_6')), inference(splitRight, [status(thm)], [c_26008])).
% 14.83/6.50  tff(c_22821, plain, (![A_5, A_429]: (r1_tarski(A_5, k3_subset_1('#skF_4', '#skF_5')) | ~r1_tarski(A_5, A_429) | ~r1_tarski(A_429, '#skF_6'))), inference(resolution, [status(thm)], [c_22800, c_6])).
% 14.83/6.50  tff(c_26109, plain, (r1_tarski('#skF_2'('#skF_6', k1_zfmisc_1('#skF_5')), k3_subset_1('#skF_4', '#skF_5')) | ~r1_tarski('#skF_6', '#skF_6')), inference(resolution, [status(thm)], [c_26094, c_22821])).
% 14.83/6.50  tff(c_26120, plain, (r1_tarski('#skF_2'('#skF_6', k1_zfmisc_1('#skF_5')), k3_subset_1('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_21782, c_26109])).
% 14.83/6.50  tff(c_27898, plain, $false, inference(negUnitSimplification, [status(thm)], [c_27880, c_26120])).
% 14.83/6.50  tff(c_27900, plain, (~v1_xboole_0(k1_zfmisc_1(k3_subset_1('#skF_4', '#skF_5')))), inference(splitRight, [status(thm)], [c_24245])).
% 14.83/6.50  tff(c_22631, plain, (![C_423, A_424]: (r1_tarski(C_423, A_424) | ~m1_subset_1(C_423, k1_zfmisc_1(A_424)))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_58, c_22598])).
% 14.83/6.50  tff(c_22663, plain, (![A_18, B_19]: (r1_tarski(k3_subset_1(A_18, B_19), A_18) | ~m1_subset_1(B_19, k1_zfmisc_1(A_18)))), inference(resolution, [status(thm)], [c_34, c_22631])).
% 14.83/6.50  tff(c_33075, plain, (![B_613]: (r1_tarski(k3_subset_1(k3_subset_1('#skF_4', '#skF_5'), B_613), '#skF_4') | ~m1_subset_1(B_613, k1_zfmisc_1(k3_subset_1('#skF_4', '#skF_5'))))), inference(resolution, [status(thm)], [c_22663, c_24156])).
% 14.83/6.50  tff(c_33111, plain, (k3_subset_1('#skF_4', '#skF_5')='#skF_4' | ~m1_subset_1('#skF_4', k1_zfmisc_1(k3_subset_1('#skF_4', '#skF_5')))), inference(resolution, [status(thm)], [c_33075, c_55])).
% 14.83/6.50  tff(c_33119, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k3_subset_1('#skF_4', '#skF_5')))), inference(splitLeft, [status(thm)], [c_33111])).
% 14.83/6.50  tff(c_33122, plain, (v1_xboole_0(k1_zfmisc_1(k3_subset_1('#skF_4', '#skF_5'))) | ~r1_tarski('#skF_4', k3_subset_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_21273, c_33119])).
% 14.83/6.50  tff(c_33128, plain, (~r1_tarski('#skF_4', k3_subset_1('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_27900, c_33122])).
% 14.83/6.50  tff(c_39136, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_39108, c_33128])).
% 14.83/6.50  tff(c_39167, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_21782, c_39136])).
% 14.83/6.50  tff(c_39168, plain, (k3_subset_1('#skF_4', '#skF_5')='#skF_4'), inference(splitRight, [status(thm)], [c_33111])).
% 14.83/6.50  tff(c_21965, plain, (![C_392, A_393]: (m1_subset_1(C_392, k1_zfmisc_1(A_393)) | v1_xboole_0(k1_zfmisc_1(A_393)) | ~r1_tarski(C_392, A_393))), inference(resolution, [status(thm)], [c_12, c_21266])).
% 14.83/6.50  tff(c_24335, plain, (![A_468, C_469]: (k3_subset_1(A_468, k3_subset_1(A_468, C_469))=C_469 | v1_xboole_0(k1_zfmisc_1(A_468)) | ~r1_tarski(C_469, A_468))), inference(resolution, [status(thm)], [c_21965, c_36])).
% 14.83/6.50  tff(c_25253, plain, (![C_477, A_478, C_479]: (~r1_tarski(C_477, A_478) | k3_subset_1(A_478, k3_subset_1(A_478, C_479))=C_479 | ~r1_tarski(C_479, A_478))), inference(resolution, [status(thm)], [c_24335, c_96])).
% 14.83/6.50  tff(c_25363, plain, (![A_8, C_479]: (k3_subset_1(A_8, k3_subset_1(A_8, C_479))=C_479 | ~r1_tarski(C_479, A_8))), inference(resolution, [status(thm)], [c_8, c_25253])).
% 14.83/6.50  tff(c_39246, plain, (k3_subset_1('#skF_4', '#skF_4')='#skF_5' | ~r1_tarski('#skF_5', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_39168, c_25363])).
% 14.83/6.50  tff(c_39298, plain, (k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_21865, c_21406, c_39246])).
% 14.83/6.50  tff(c_39300, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_39298])).
% 14.83/6.50  tff(c_39301, plain, ('#skF_5'='#skF_6'), inference(splitRight, [status(thm)], [c_22397])).
% 14.83/6.50  tff(c_21449, plain, (r1_tarski('#skF_1'(k1_zfmisc_1('#skF_5')), '#skF_6')), inference(splitRight, [status(thm)], [c_21348])).
% 14.83/6.50  tff(c_21692, plain, (r1_tarski('#skF_1'(k1_zfmisc_1('#skF_5')), k3_subset_1('#skF_4', '#skF_6')) | ~r1_tarski('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_21449, c_21665])).
% 14.83/6.50  tff(c_21991, plain, (~r1_tarski('#skF_6', '#skF_5')), inference(splitLeft, [status(thm)], [c_21692])).
% 14.83/6.50  tff(c_39305, plain, (~r1_tarski('#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_39301, c_21991])).
% 14.83/6.50  tff(c_39322, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_21782, c_39305])).
% 14.83/6.50  tff(c_39324, plain, (r1_tarski('#skF_6', '#skF_5')), inference(splitRight, [status(thm)], [c_21692])).
% 14.83/6.50  tff(c_21407, plain, (k3_subset_1('#skF_4', k3_subset_1('#skF_4', '#skF_6'))='#skF_6'), inference(resolution, [status(thm)], [c_54, c_21392])).
% 14.83/6.50  tff(c_21602, plain, (![B_375, A_376]: (B_375=A_376 | ~r1_tarski(k3_subset_1(A_376, B_375), B_375) | ~m1_subset_1(B_375, k1_zfmisc_1(A_376)))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_44])).
% 14.83/6.50  tff(c_21605, plain, (k3_subset_1('#skF_4', '#skF_6')='#skF_4' | ~r1_tarski('#skF_6', k3_subset_1('#skF_4', '#skF_6')) | ~m1_subset_1(k3_subset_1('#skF_4', '#skF_6'), k1_zfmisc_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_21407, c_21602])).
% 14.83/6.50  tff(c_39325, plain, (~m1_subset_1(k3_subset_1('#skF_4', '#skF_6'), k1_zfmisc_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_21605])).
% 14.83/6.50  tff(c_39356, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1('#skF_4'))), inference(resolution, [status(thm)], [c_34, c_39325])).
% 14.83/6.50  tff(c_39366, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_39356])).
% 14.83/6.50  tff(c_39368, plain, (m1_subset_1(k3_subset_1('#skF_4', '#skF_6'), k1_zfmisc_1('#skF_4'))), inference(splitRight, [status(thm)], [c_21605])).
% 14.83/6.50  tff(c_21315, plain, (![A_352]: (r1_tarski(A_352, k3_subset_1('#skF_4', '#skF_6')) | ~r1_tarski(A_352, '#skF_5'))), inference(resolution, [status(thm)], [c_50, c_21302])).
% 14.83/6.50  tff(c_39452, plain, (![A_686]: (k3_subset_1('#skF_4', '#skF_6')=A_686 | ~m1_subset_1(k3_subset_1('#skF_4', '#skF_6'), k1_zfmisc_1(A_686)) | ~r1_tarski(k3_subset_1(A_686, k3_subset_1('#skF_4', '#skF_6')), '#skF_5'))), inference(resolution, [status(thm)], [c_21315, c_21602])).
% 14.83/6.50  tff(c_39458, plain, (k3_subset_1('#skF_4', '#skF_6')='#skF_4' | ~m1_subset_1(k3_subset_1('#skF_4', '#skF_6'), k1_zfmisc_1('#skF_4')) | ~r1_tarski('#skF_6', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_21407, c_39452])).
% 14.83/6.50  tff(c_39465, plain, (k3_subset_1('#skF_4', '#skF_6')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_39324, c_39368, c_39458])).
% 14.83/6.50  tff(c_39474, plain, (k3_subset_1('#skF_4', '#skF_4')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_39465, c_21407])).
% 14.83/6.50  tff(c_39503, plain, (k1_xboole_0='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_39474, c_21406])).
% 14.83/6.50  tff(c_39525, plain, ('#skF_5'!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_39503, c_48])).
% 14.83/6.50  tff(c_21615, plain, (![A_22]: (k1_xboole_0=A_22 | ~r1_tarski(A_22, k1_xboole_0) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_22)))), inference(superposition, [status(thm), theory('equality')], [c_58, c_21602])).
% 14.83/6.50  tff(c_21621, plain, (![A_22]: (k1_xboole_0=A_22 | ~r1_tarski(A_22, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_21615])).
% 14.83/6.50  tff(c_39749, plain, (![A_698]: (A_698='#skF_6' | ~r1_tarski(A_698, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_39503, c_39503, c_21621])).
% 14.83/6.50  tff(c_39769, plain, ('#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_52, c_39749])).
% 14.83/6.50  tff(c_39781, plain, $false, inference(negUnitSimplification, [status(thm)], [c_39525, c_39769])).
% 14.83/6.50  tff(c_39783, plain, (v1_xboole_0(k1_zfmisc_1('#skF_4'))), inference(splitRight, [status(thm)], [c_116])).
% 14.83/6.50  tff(c_39787, plain, (![C_699]: (~r1_tarski(C_699, '#skF_4'))), inference(resolution, [status(thm)], [c_39783, c_96])).
% 14.83/6.50  tff(c_39792, plain, $false, inference(resolution, [status(thm)], [c_8, c_39787])).
% 14.83/6.50  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.83/6.50  
% 14.83/6.50  Inference rules
% 14.83/6.50  ----------------------
% 14.83/6.50  #Ref     : 0
% 14.83/6.50  #Sup     : 8768
% 14.83/6.50  #Fact    : 0
% 14.83/6.50  #Define  : 0
% 14.83/6.50  #Split   : 68
% 14.83/6.50  #Chain   : 0
% 14.83/6.50  #Close   : 0
% 14.83/6.50  
% 14.83/6.50  Ordering : KBO
% 14.83/6.50  
% 14.83/6.50  Simplification rules
% 14.83/6.50  ----------------------
% 14.83/6.50  #Subsume      : 3077
% 14.83/6.50  #Demod        : 4819
% 14.83/6.50  #Tautology    : 2055
% 14.83/6.50  #SimpNegUnit  : 503
% 14.83/6.50  #BackRed      : 532
% 14.83/6.50  
% 14.83/6.50  #Partial instantiations: 0
% 14.83/6.50  #Strategies tried      : 1
% 14.83/6.50  
% 14.83/6.50  Timing (in seconds)
% 14.83/6.50  ----------------------
% 14.83/6.50  Preprocessing        : 0.31
% 14.83/6.50  Parsing              : 0.16
% 14.83/6.50  CNF conversion       : 0.02
% 14.83/6.50  Main loop            : 5.40
% 14.83/6.50  Inferencing          : 1.12
% 14.83/6.50  Reduction            : 2.03
% 14.83/6.50  Demodulation         : 1.48
% 14.83/6.50  BG Simplification    : 0.12
% 14.83/6.50  Subsumption          : 1.78
% 14.83/6.50  Abstraction          : 0.18
% 14.83/6.50  MUC search           : 0.00
% 14.83/6.50  Cooper               : 0.00
% 14.83/6.50  Total                : 5.77
% 14.83/6.50  Index Insertion      : 0.00
% 14.83/6.50  Index Deletion       : 0.00
% 14.83/6.50  Index Matching       : 0.00
% 14.83/6.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
