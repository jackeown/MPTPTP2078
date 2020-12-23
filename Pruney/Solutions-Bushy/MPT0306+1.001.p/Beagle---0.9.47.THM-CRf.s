%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0306+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:05 EST 2020

% Result     : Theorem 8.52s
% Output     : CNFRefutation 8.52s
% Verified   : 
% Statistics : Number of formulae       :   50 (  71 expanded)
%              Number of leaves         :   20 (  35 expanded)
%              Depth                    :    8
%              Number of atoms          :   77 ( 149 expanded)
%              Number of equality atoms :    4 (  18 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k4_tarski > k2_zfmisc_1 > #nlpp > #skF_1 > #skF_4 > #skF_10 > #skF_2 > #skF_6 > #skF_9 > #skF_8 > #skF_5 > #skF_3 > #skF_7

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i * $i ) > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_50,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(A,B)
       => ( r1_tarski(k2_zfmisc_1(A,C),k2_zfmisc_1(B,C))
          & r1_tarski(k2_zfmisc_1(C,A),k2_zfmisc_1(C,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t118_zfmisc_1)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( C = k2_zfmisc_1(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ? [E,F] :
              ( r2_hidden(E,A)
              & r2_hidden(F,B)
              & D = k4_tarski(E,F) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).

tff(c_30,plain,(
    ! [A_35,B_36] :
      ( r2_hidden('#skF_7'(A_35,B_36),A_35)
      | r1_tarski(A_35,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_34,plain,(
    r1_tarski('#skF_8','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_8,plain,(
    ! [A_1,B_2,D_28] :
      ( r2_hidden('#skF_5'(A_1,B_2,k2_zfmisc_1(A_1,B_2),D_28),A_1)
      | ~ r2_hidden(D_28,k2_zfmisc_1(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_64,plain,(
    ! [A_58,B_59,D_60] :
      ( r2_hidden('#skF_6'(A_58,B_59,k2_zfmisc_1(A_58,B_59),D_60),B_59)
      | ~ r2_hidden(D_60,k2_zfmisc_1(A_58,B_59)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_26,plain,(
    ! [C_39,B_36,A_35] :
      ( r2_hidden(C_39,B_36)
      | ~ r2_hidden(C_39,A_35)
      | ~ r1_tarski(A_35,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_67,plain,(
    ! [A_58,B_59,D_60,B_36] :
      ( r2_hidden('#skF_6'(A_58,B_59,k2_zfmisc_1(A_58,B_59),D_60),B_36)
      | ~ r1_tarski(B_59,B_36)
      | ~ r2_hidden(D_60,k2_zfmisc_1(A_58,B_59)) ) ),
    inference(resolution,[status(thm)],[c_64,c_26])).

tff(c_2263,plain,(
    ! [A_407,B_408,D_409] :
      ( k4_tarski('#skF_5'(A_407,B_408,k2_zfmisc_1(A_407,B_408),D_409),'#skF_6'(A_407,B_408,k2_zfmisc_1(A_407,B_408),D_409)) = D_409
      | ~ r2_hidden(D_409,k2_zfmisc_1(A_407,B_408)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_2,plain,(
    ! [E_33,F_34,A_1,B_2] :
      ( r2_hidden(k4_tarski(E_33,F_34),k2_zfmisc_1(A_1,B_2))
      | ~ r2_hidden(F_34,B_2)
      | ~ r2_hidden(E_33,A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_3554,plain,(
    ! [B_610,A_612,B_611,D_609,A_613] :
      ( r2_hidden(D_609,k2_zfmisc_1(A_612,B_611))
      | ~ r2_hidden('#skF_6'(A_613,B_610,k2_zfmisc_1(A_613,B_610),D_609),B_611)
      | ~ r2_hidden('#skF_5'(A_613,B_610,k2_zfmisc_1(A_613,B_610),D_609),A_612)
      | ~ r2_hidden(D_609,k2_zfmisc_1(A_613,B_610)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2263,c_2])).

tff(c_8211,plain,(
    ! [A_834,D_836,B_835,B_832,A_833] :
      ( r2_hidden(D_836,k2_zfmisc_1(A_833,B_835))
      | ~ r2_hidden('#skF_5'(A_834,B_832,k2_zfmisc_1(A_834,B_832),D_836),A_833)
      | ~ r1_tarski(B_832,B_835)
      | ~ r2_hidden(D_836,k2_zfmisc_1(A_834,B_832)) ) ),
    inference(resolution,[status(thm)],[c_67,c_3554])).

tff(c_8239,plain,(
    ! [D_837,A_838,B_839,B_840] :
      ( r2_hidden(D_837,k2_zfmisc_1(A_838,B_839))
      | ~ r1_tarski(B_840,B_839)
      | ~ r2_hidden(D_837,k2_zfmisc_1(A_838,B_840)) ) ),
    inference(resolution,[status(thm)],[c_8,c_8211])).

tff(c_8264,plain,(
    ! [D_841,A_842] :
      ( r2_hidden(D_841,k2_zfmisc_1(A_842,'#skF_9'))
      | ~ r2_hidden(D_841,k2_zfmisc_1(A_842,'#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_34,c_8239])).

tff(c_28,plain,(
    ! [A_35,B_36] :
      ( ~ r2_hidden('#skF_7'(A_35,B_36),B_36)
      | r1_tarski(A_35,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_9050,plain,(
    ! [A_857,A_858] :
      ( r1_tarski(A_857,k2_zfmisc_1(A_858,'#skF_9'))
      | ~ r2_hidden('#skF_7'(A_857,k2_zfmisc_1(A_858,'#skF_9')),k2_zfmisc_1(A_858,'#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_8264,c_28])).

tff(c_9100,plain,(
    ! [A_858] : r1_tarski(k2_zfmisc_1(A_858,'#skF_8'),k2_zfmisc_1(A_858,'#skF_9')) ),
    inference(resolution,[status(thm)],[c_30,c_9050])).

tff(c_60,plain,(
    ! [A_55,B_56,D_57] :
      ( r2_hidden('#skF_5'(A_55,B_56,k2_zfmisc_1(A_55,B_56),D_57),A_55)
      | ~ r2_hidden(D_57,k2_zfmisc_1(A_55,B_56)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_63,plain,(
    ! [A_55,B_56,D_57,B_36] :
      ( r2_hidden('#skF_5'(A_55,B_56,k2_zfmisc_1(A_55,B_56),D_57),B_36)
      | ~ r1_tarski(A_55,B_36)
      | ~ r2_hidden(D_57,k2_zfmisc_1(A_55,B_56)) ) ),
    inference(resolution,[status(thm)],[c_60,c_26])).

tff(c_6,plain,(
    ! [A_1,B_2,D_28] :
      ( r2_hidden('#skF_6'(A_1,B_2,k2_zfmisc_1(A_1,B_2),D_28),B_2)
      | ~ r2_hidden(D_28,k2_zfmisc_1(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_183,plain,(
    ! [A_98,B_99,D_100] :
      ( k4_tarski('#skF_5'(A_98,B_99,k2_zfmisc_1(A_98,B_99),D_100),'#skF_6'(A_98,B_99,k2_zfmisc_1(A_98,B_99),D_100)) = D_100
      | ~ r2_hidden(D_100,k2_zfmisc_1(A_98,B_99)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_1679,plain,(
    ! [B_350,B_352,A_351,A_354,D_353] :
      ( r2_hidden(D_353,k2_zfmisc_1(A_354,B_352))
      | ~ r2_hidden('#skF_6'(A_351,B_350,k2_zfmisc_1(A_351,B_350),D_353),B_352)
      | ~ r2_hidden('#skF_5'(A_351,B_350,k2_zfmisc_1(A_351,B_350),D_353),A_354)
      | ~ r2_hidden(D_353,k2_zfmisc_1(A_351,B_350)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_183,c_2])).

tff(c_1692,plain,(
    ! [D_355,A_356,B_357,A_358] :
      ( r2_hidden(D_355,k2_zfmisc_1(A_356,B_357))
      | ~ r2_hidden('#skF_5'(A_358,B_357,k2_zfmisc_1(A_358,B_357),D_355),A_356)
      | ~ r2_hidden(D_355,k2_zfmisc_1(A_358,B_357)) ) ),
    inference(resolution,[status(thm)],[c_6,c_1679])).

tff(c_1709,plain,(
    ! [D_359,B_360,B_361,A_362] :
      ( r2_hidden(D_359,k2_zfmisc_1(B_360,B_361))
      | ~ r1_tarski(A_362,B_360)
      | ~ r2_hidden(D_359,k2_zfmisc_1(A_362,B_361)) ) ),
    inference(resolution,[status(thm)],[c_63,c_1692])).

tff(c_1719,plain,(
    ! [D_363,B_364] :
      ( r2_hidden(D_363,k2_zfmisc_1('#skF_9',B_364))
      | ~ r2_hidden(D_363,k2_zfmisc_1('#skF_8',B_364)) ) ),
    inference(resolution,[status(thm)],[c_34,c_1709])).

tff(c_2134,plain,(
    ! [A_373,B_374] :
      ( r1_tarski(A_373,k2_zfmisc_1('#skF_9',B_374))
      | ~ r2_hidden('#skF_7'(A_373,k2_zfmisc_1('#skF_9',B_374)),k2_zfmisc_1('#skF_8',B_374)) ) ),
    inference(resolution,[status(thm)],[c_1719,c_28])).

tff(c_2149,plain,(
    ! [B_374] : r1_tarski(k2_zfmisc_1('#skF_8',B_374),k2_zfmisc_1('#skF_9',B_374)) ),
    inference(resolution,[status(thm)],[c_30,c_2134])).

tff(c_32,plain,
    ( ~ r1_tarski(k2_zfmisc_1('#skF_10','#skF_8'),k2_zfmisc_1('#skF_10','#skF_9'))
    | ~ r1_tarski(k2_zfmisc_1('#skF_8','#skF_10'),k2_zfmisc_1('#skF_9','#skF_10')) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_68,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_8','#skF_10'),k2_zfmisc_1('#skF_9','#skF_10')) ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_2152,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2149,c_68])).

tff(c_2153,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_10','#skF_8'),k2_zfmisc_1('#skF_10','#skF_9')) ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_9103,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_9100,c_2153])).

%------------------------------------------------------------------------------
