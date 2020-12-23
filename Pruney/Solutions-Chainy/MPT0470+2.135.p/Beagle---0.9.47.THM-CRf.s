%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:19 EST 2020

% Result     : Theorem 8.59s
% Output     : CNFRefutation 8.59s
% Verified   : 
% Statistics : Number of formulae       :  158 (1338 expanded)
%              Number of leaves         :   28 ( 427 expanded)
%              Depth                    :   21
%              Number of atoms          :  463 (3653 expanded)
%              Number of equality atoms :   82 ( 455 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k5_relat_1 > k4_xboole_0 > k4_tarski > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_6 > #skF_4 > #skF_5 > #skF_9 > #skF_7 > #skF_3 > #skF_2 > #skF_8 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k4_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_relat_1)).

tff(f_71,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ( k5_relat_1(k1_xboole_0,A) = k1_xboole_0
          & k5_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_relat_1)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_60,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => ( C = k5_relat_1(A,B)
              <=> ! [D,E] :
                    ( r2_hidden(k4_tarski(D,E),C)
                  <=> ? [F] :
                        ( r2_hidden(k4_tarski(D,F),A)
                        & r2_hidden(k4_tarski(F,E),B) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_relat_1)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r1_tarski(A,B)
        <=> ! [C,D] :
              ( r2_hidden(k4_tarski(C,D),A)
             => r2_hidden(k4_tarski(C,D),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_relat_1)).

tff(f_32,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(c_4,plain,(
    ! [A_2,B_3] : k4_xboole_0(A_2,k2_xboole_0(A_2,B_3)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_46,plain,(
    ! [A_129,B_130] :
      ( v1_relat_1(k4_xboole_0(A_129,B_130))
      | ~ v1_relat_1(A_129) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_49,plain,(
    ! [A_2] :
      ( v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_2) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_46])).

tff(c_51,plain,(
    ! [A_2] : ~ v1_relat_1(A_2) ),
    inference(splitLeft,[status(thm)],[c_49])).

tff(c_36,plain,(
    v1_relat_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_54,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_51,c_36])).

tff(c_55,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_49])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_162,plain,(
    ! [A_174,B_175,C_176] :
      ( r2_hidden(k4_tarski('#skF_6'(A_174,B_175,C_176),'#skF_5'(A_174,B_175,C_176)),B_175)
      | r2_hidden(k4_tarski('#skF_7'(A_174,B_175,C_176),'#skF_8'(A_174,B_175,C_176)),C_176)
      | k5_relat_1(A_174,B_175) = C_176
      | ~ v1_relat_1(C_176)
      | ~ v1_relat_1(B_175)
      | ~ v1_relat_1(A_174) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_8,plain,(
    ! [C_21,D_22,B_16,A_6] :
      ( r2_hidden(k4_tarski(C_21,D_22),B_16)
      | ~ r2_hidden(k4_tarski(C_21,D_22),A_6)
      | ~ r1_tarski(A_6,B_16)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_5404,plain,(
    ! [A_612,B_613,C_614,B_615] :
      ( r2_hidden(k4_tarski('#skF_7'(A_612,B_613,C_614),'#skF_8'(A_612,B_613,C_614)),B_615)
      | ~ r1_tarski(C_614,B_615)
      | r2_hidden(k4_tarski('#skF_6'(A_612,B_613,C_614),'#skF_5'(A_612,B_613,C_614)),B_613)
      | k5_relat_1(A_612,B_613) = C_614
      | ~ v1_relat_1(C_614)
      | ~ v1_relat_1(B_613)
      | ~ v1_relat_1(A_612) ) ),
    inference(resolution,[status(thm)],[c_162,c_8])).

tff(c_6,plain,(
    ! [A_4,B_5] : ~ r2_hidden(A_4,k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_6031,plain,(
    ! [C_714,A_715,B_716,B_717] :
      ( ~ r1_tarski(C_714,k2_zfmisc_1(k4_tarski('#skF_7'(A_715,B_716,C_714),'#skF_8'(A_715,B_716,C_714)),B_717))
      | r2_hidden(k4_tarski('#skF_6'(A_715,B_716,C_714),'#skF_5'(A_715,B_716,C_714)),B_716)
      | k5_relat_1(A_715,B_716) = C_714
      | ~ v1_relat_1(C_714)
      | ~ v1_relat_1(B_716)
      | ~ v1_relat_1(A_715) ) ),
    inference(resolution,[status(thm)],[c_5404,c_6])).

tff(c_6034,plain,(
    ! [A_715,B_716] :
      ( r2_hidden(k4_tarski('#skF_6'(A_715,B_716,k1_xboole_0),'#skF_5'(A_715,B_716,k1_xboole_0)),B_716)
      | k5_relat_1(A_715,B_716) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(B_716)
      | ~ v1_relat_1(A_715) ) ),
    inference(resolution,[status(thm)],[c_2,c_6031])).

tff(c_6038,plain,(
    ! [A_718,B_719] :
      ( r2_hidden(k4_tarski('#skF_6'(A_718,B_719,k1_xboole_0),'#skF_5'(A_718,B_719,k1_xboole_0)),B_719)
      | k5_relat_1(A_718,B_719) = k1_xboole_0
      | ~ v1_relat_1(B_719)
      | ~ v1_relat_1(A_718) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_6034])).

tff(c_6045,plain,(
    ! [A_720,B_721,B_722] :
      ( r2_hidden(k4_tarski('#skF_6'(A_720,B_721,k1_xboole_0),'#skF_5'(A_720,B_721,k1_xboole_0)),B_722)
      | ~ r1_tarski(B_721,B_722)
      | k5_relat_1(A_720,B_721) = k1_xboole_0
      | ~ v1_relat_1(B_721)
      | ~ v1_relat_1(A_720) ) ),
    inference(resolution,[status(thm)],[c_6038,c_8])).

tff(c_6057,plain,(
    ! [B_723,A_724,B_725] :
      ( ~ r1_tarski(B_723,k2_zfmisc_1(k4_tarski('#skF_6'(A_724,B_723,k1_xboole_0),'#skF_5'(A_724,B_723,k1_xboole_0)),B_725))
      | k5_relat_1(A_724,B_723) = k1_xboole_0
      | ~ v1_relat_1(B_723)
      | ~ v1_relat_1(A_724) ) ),
    inference(resolution,[status(thm)],[c_6045,c_6])).

tff(c_6061,plain,(
    ! [A_724] :
      ( k5_relat_1(A_724,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_724) ) ),
    inference(resolution,[status(thm)],[c_2,c_6057])).

tff(c_6088,plain,(
    ! [A_732] :
      ( k5_relat_1(A_732,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_732) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_6061])).

tff(c_6098,plain,(
    k5_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_55,c_6088])).

tff(c_142,plain,(
    ! [D_164,E_165,A_166,B_167] :
      ( r2_hidden(k4_tarski(D_164,'#skF_3'(D_164,E_165,k5_relat_1(A_166,B_167),B_167,A_166)),A_166)
      | ~ r2_hidden(k4_tarski(D_164,E_165),k5_relat_1(A_166,B_167))
      | ~ v1_relat_1(k5_relat_1(A_166,B_167))
      | ~ v1_relat_1(B_167)
      | ~ v1_relat_1(A_166) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_650,plain,(
    ! [B_249,D_248,B_247,A_251,E_250] :
      ( r2_hidden(k4_tarski(D_248,'#skF_3'(D_248,E_250,k5_relat_1(A_251,B_247),B_247,A_251)),B_249)
      | ~ r1_tarski(A_251,B_249)
      | ~ r2_hidden(k4_tarski(D_248,E_250),k5_relat_1(A_251,B_247))
      | ~ v1_relat_1(k5_relat_1(A_251,B_247))
      | ~ v1_relat_1(B_247)
      | ~ v1_relat_1(A_251) ) ),
    inference(resolution,[status(thm)],[c_142,c_8])).

tff(c_4923,plain,(
    ! [B_568,D_569,A_570,E_567,B_566] :
      ( ~ r1_tarski(A_570,k2_zfmisc_1(k4_tarski(D_569,'#skF_3'(D_569,E_567,k5_relat_1(A_570,B_568),B_568,A_570)),B_566))
      | ~ r2_hidden(k4_tarski(D_569,E_567),k5_relat_1(A_570,B_568))
      | ~ v1_relat_1(k5_relat_1(A_570,B_568))
      | ~ v1_relat_1(B_568)
      | ~ v1_relat_1(A_570) ) ),
    inference(resolution,[status(thm)],[c_650,c_6])).

tff(c_4927,plain,(
    ! [D_569,E_567,B_568] :
      ( ~ r2_hidden(k4_tarski(D_569,E_567),k5_relat_1(k1_xboole_0,B_568))
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_568))
      | ~ v1_relat_1(B_568)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_2,c_4923])).

tff(c_4930,plain,(
    ! [D_569,E_567,B_568] :
      ( ~ r2_hidden(k4_tarski(D_569,E_567),k5_relat_1(k1_xboole_0,B_568))
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_568))
      | ~ v1_relat_1(B_568) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_4927])).

tff(c_5934,plain,(
    ! [B_696,C_697,A_698,B_699] :
      ( ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_696))
      | ~ v1_relat_1(B_696)
      | ~ r1_tarski(C_697,k5_relat_1(k1_xboole_0,B_696))
      | r2_hidden(k4_tarski('#skF_6'(A_698,B_699,C_697),'#skF_5'(A_698,B_699,C_697)),B_699)
      | k5_relat_1(A_698,B_699) = C_697
      | ~ v1_relat_1(C_697)
      | ~ v1_relat_1(B_699)
      | ~ v1_relat_1(A_698) ) ),
    inference(resolution,[status(thm)],[c_5404,c_4930])).

tff(c_5955,plain,(
    ! [B_696,A_698,B_699] :
      ( ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_696))
      | ~ v1_relat_1(B_696)
      | r2_hidden(k4_tarski('#skF_6'(A_698,B_699,k1_xboole_0),'#skF_5'(A_698,B_699,k1_xboole_0)),B_699)
      | k5_relat_1(A_698,B_699) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(B_699)
      | ~ v1_relat_1(A_698) ) ),
    inference(resolution,[status(thm)],[c_2,c_5934])).

tff(c_5964,plain,(
    ! [B_696,A_698,B_699] :
      ( ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_696))
      | ~ v1_relat_1(B_696)
      | r2_hidden(k4_tarski('#skF_6'(A_698,B_699,k1_xboole_0),'#skF_5'(A_698,B_699,k1_xboole_0)),B_699)
      | k5_relat_1(A_698,B_699) = k1_xboole_0
      | ~ v1_relat_1(B_699)
      | ~ v1_relat_1(A_698) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_5955])).

tff(c_5965,plain,(
    ! [B_696] :
      ( ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_696))
      | ~ v1_relat_1(B_696) ) ),
    inference(splitLeft,[status(thm)],[c_5964])).

tff(c_6113,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_6098,c_5965])).

tff(c_6165,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_55,c_6113])).

tff(c_6167,plain,(
    ! [A_733,B_734] :
      ( r2_hidden(k4_tarski('#skF_6'(A_733,B_734,k1_xboole_0),'#skF_5'(A_733,B_734,k1_xboole_0)),B_734)
      | k5_relat_1(A_733,B_734) = k1_xboole_0
      | ~ v1_relat_1(B_734)
      | ~ v1_relat_1(A_733) ) ),
    inference(splitRight,[status(thm)],[c_5964])).

tff(c_6189,plain,(
    ! [A_735,B_736,B_737] :
      ( r2_hidden(k4_tarski('#skF_6'(A_735,B_736,k1_xboole_0),'#skF_5'(A_735,B_736,k1_xboole_0)),B_737)
      | ~ r1_tarski(B_736,B_737)
      | k5_relat_1(A_735,B_736) = k1_xboole_0
      | ~ v1_relat_1(B_736)
      | ~ v1_relat_1(A_735) ) ),
    inference(resolution,[status(thm)],[c_6167,c_8])).

tff(c_6276,plain,(
    ! [B_748,A_749,B_750] :
      ( ~ r1_tarski(B_748,k2_zfmisc_1(k4_tarski('#skF_6'(A_749,B_748,k1_xboole_0),'#skF_5'(A_749,B_748,k1_xboole_0)),B_750))
      | k5_relat_1(A_749,B_748) = k1_xboole_0
      | ~ v1_relat_1(B_748)
      | ~ v1_relat_1(A_749) ) ),
    inference(resolution,[status(thm)],[c_6189,c_6])).

tff(c_6280,plain,(
    ! [A_749] :
      ( k5_relat_1(A_749,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_749) ) ),
    inference(resolution,[status(thm)],[c_2,c_6276])).

tff(c_6284,plain,(
    ! [A_751] :
      ( k5_relat_1(A_751,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_751) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_6280])).

tff(c_6294,plain,(
    k5_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_55,c_6284])).

tff(c_6217,plain,(
    ! [B_740,B_741,A_742] :
      ( ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_740))
      | ~ v1_relat_1(B_740)
      | ~ r1_tarski(B_741,k5_relat_1(k1_xboole_0,B_740))
      | k5_relat_1(A_742,B_741) = k1_xboole_0
      | ~ v1_relat_1(B_741)
      | ~ v1_relat_1(A_742) ) ),
    inference(resolution,[status(thm)],[c_6189,c_4930])).

tff(c_6238,plain,(
    ! [B_740,A_742] :
      ( ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_740))
      | ~ v1_relat_1(B_740)
      | k5_relat_1(A_742,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_742) ) ),
    inference(resolution,[status(thm)],[c_2,c_6217])).

tff(c_6247,plain,(
    ! [B_740,A_742] :
      ( ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_740))
      | ~ v1_relat_1(B_740)
      | k5_relat_1(A_742,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_742) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_6238])).

tff(c_6248,plain,(
    ! [B_740] :
      ( ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_740))
      | ~ v1_relat_1(B_740) ) ),
    inference(splitLeft,[status(thm)],[c_6247])).

tff(c_6300,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_6294,c_6248])).

tff(c_6346,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_55,c_6300])).

tff(c_6381,plain,(
    ! [A_755] :
      ( k5_relat_1(A_755,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_755) ) ),
    inference(splitRight,[status(thm)],[c_6247])).

tff(c_6391,plain,(
    k5_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_55,c_6381])).

tff(c_34,plain,
    ( k5_relat_1('#skF_9',k1_xboole_0) != k1_xboole_0
    | k5_relat_1(k1_xboole_0,'#skF_9') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_50,plain,(
    k5_relat_1(k1_xboole_0,'#skF_9') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_2109,plain,(
    ! [A_374,B_375,C_376,B_377] :
      ( r2_hidden(k4_tarski('#skF_6'(A_374,B_375,C_376),'#skF_5'(A_374,B_375,C_376)),B_377)
      | ~ r1_tarski(B_375,B_377)
      | r2_hidden(k4_tarski('#skF_7'(A_374,B_375,C_376),'#skF_8'(A_374,B_375,C_376)),C_376)
      | k5_relat_1(A_374,B_375) = C_376
      | ~ v1_relat_1(C_376)
      | ~ v1_relat_1(B_375)
      | ~ v1_relat_1(A_374) ) ),
    inference(resolution,[status(thm)],[c_162,c_8])).

tff(c_2895,plain,(
    ! [B_494,A_495,C_496,B_497] :
      ( ~ r1_tarski(B_494,k2_zfmisc_1(k4_tarski('#skF_6'(A_495,B_494,C_496),'#skF_5'(A_495,B_494,C_496)),B_497))
      | r2_hidden(k4_tarski('#skF_7'(A_495,B_494,C_496),'#skF_8'(A_495,B_494,C_496)),C_496)
      | k5_relat_1(A_495,B_494) = C_496
      | ~ v1_relat_1(C_496)
      | ~ v1_relat_1(B_494)
      | ~ v1_relat_1(A_495) ) ),
    inference(resolution,[status(thm)],[c_2109,c_6])).

tff(c_2898,plain,(
    ! [A_495,C_496] :
      ( r2_hidden(k4_tarski('#skF_7'(A_495,k1_xboole_0,C_496),'#skF_8'(A_495,k1_xboole_0,C_496)),C_496)
      | k5_relat_1(A_495,k1_xboole_0) = C_496
      | ~ v1_relat_1(C_496)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_495) ) ),
    inference(resolution,[status(thm)],[c_2,c_2895])).

tff(c_2902,plain,(
    ! [A_498,C_499] :
      ( r2_hidden(k4_tarski('#skF_7'(A_498,k1_xboole_0,C_499),'#skF_8'(A_498,k1_xboole_0,C_499)),C_499)
      | k5_relat_1(A_498,k1_xboole_0) = C_499
      | ~ v1_relat_1(C_499)
      | ~ v1_relat_1(A_498) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_2898])).

tff(c_2921,plain,(
    ! [A_500,C_501,B_502] :
      ( r2_hidden(k4_tarski('#skF_7'(A_500,k1_xboole_0,C_501),'#skF_8'(A_500,k1_xboole_0,C_501)),B_502)
      | ~ r1_tarski(C_501,B_502)
      | k5_relat_1(A_500,k1_xboole_0) = C_501
      | ~ v1_relat_1(C_501)
      | ~ v1_relat_1(A_500) ) ),
    inference(resolution,[status(thm)],[c_2902,c_8])).

tff(c_2945,plain,(
    ! [C_503,A_504,B_505] :
      ( ~ r1_tarski(C_503,k2_zfmisc_1(k4_tarski('#skF_7'(A_504,k1_xboole_0,C_503),'#skF_8'(A_504,k1_xboole_0,C_503)),B_505))
      | k5_relat_1(A_504,k1_xboole_0) = C_503
      | ~ v1_relat_1(C_503)
      | ~ v1_relat_1(A_504) ) ),
    inference(resolution,[status(thm)],[c_2921,c_6])).

tff(c_2949,plain,(
    ! [A_504] :
      ( k5_relat_1(A_504,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_504) ) ),
    inference(resolution,[status(thm)],[c_2,c_2945])).

tff(c_2953,plain,(
    ! [A_506] :
      ( k5_relat_1(A_506,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_506) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_2949])).

tff(c_2963,plain,(
    k5_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_55,c_2953])).

tff(c_122,plain,(
    ! [D_158,E_159,A_160,B_161] :
      ( r2_hidden(k4_tarski('#skF_3'(D_158,E_159,k5_relat_1(A_160,B_161),B_161,A_160),E_159),B_161)
      | ~ r2_hidden(k4_tarski(D_158,E_159),k5_relat_1(A_160,B_161))
      | ~ v1_relat_1(k5_relat_1(A_160,B_161))
      | ~ v1_relat_1(B_161)
      | ~ v1_relat_1(A_160) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_175,plain,(
    ! [A_181,E_177,B_178,B_179,D_180] :
      ( r2_hidden(k4_tarski('#skF_3'(D_180,E_177,k5_relat_1(A_181,B_178),B_178,A_181),E_177),B_179)
      | ~ r1_tarski(B_178,B_179)
      | ~ r2_hidden(k4_tarski(D_180,E_177),k5_relat_1(A_181,B_178))
      | ~ v1_relat_1(k5_relat_1(A_181,B_178))
      | ~ v1_relat_1(B_178)
      | ~ v1_relat_1(A_181) ) ),
    inference(resolution,[status(thm)],[c_122,c_8])).

tff(c_187,plain,(
    ! [A_185,D_182,B_186,B_184,E_183] :
      ( ~ r1_tarski(B_186,k2_zfmisc_1(k4_tarski('#skF_3'(D_182,E_183,k5_relat_1(A_185,B_186),B_186,A_185),E_183),B_184))
      | ~ r2_hidden(k4_tarski(D_182,E_183),k5_relat_1(A_185,B_186))
      | ~ v1_relat_1(k5_relat_1(A_185,B_186))
      | ~ v1_relat_1(B_186)
      | ~ v1_relat_1(A_185) ) ),
    inference(resolution,[status(thm)],[c_175,c_6])).

tff(c_191,plain,(
    ! [D_182,E_183,A_185] :
      ( ~ r2_hidden(k4_tarski(D_182,E_183),k5_relat_1(A_185,k1_xboole_0))
      | ~ v1_relat_1(k5_relat_1(A_185,k1_xboole_0))
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_185) ) ),
    inference(resolution,[status(thm)],[c_2,c_187])).

tff(c_194,plain,(
    ! [D_182,E_183,A_185] :
      ( ~ r2_hidden(k4_tarski(D_182,E_183),k5_relat_1(A_185,k1_xboole_0))
      | ~ v1_relat_1(k5_relat_1(A_185,k1_xboole_0))
      | ~ v1_relat_1(A_185) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_191])).

tff(c_677,plain,(
    ! [A_252,A_256,E_253,D_255,B_254] :
      ( ~ v1_relat_1(k5_relat_1(A_252,k1_xboole_0))
      | ~ v1_relat_1(A_252)
      | ~ r1_tarski(A_256,k5_relat_1(A_252,k1_xboole_0))
      | ~ r2_hidden(k4_tarski(D_255,E_253),k5_relat_1(A_256,B_254))
      | ~ v1_relat_1(k5_relat_1(A_256,B_254))
      | ~ v1_relat_1(B_254)
      | ~ v1_relat_1(A_256) ) ),
    inference(resolution,[status(thm)],[c_650,c_194])).

tff(c_695,plain,(
    ! [A_252,D_255,E_253,B_254] :
      ( ~ v1_relat_1(k5_relat_1(A_252,k1_xboole_0))
      | ~ v1_relat_1(A_252)
      | ~ r2_hidden(k4_tarski(D_255,E_253),k5_relat_1(k1_xboole_0,B_254))
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_254))
      | ~ v1_relat_1(B_254)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_2,c_677])).

tff(c_703,plain,(
    ! [A_252,D_255,E_253,B_254] :
      ( ~ v1_relat_1(k5_relat_1(A_252,k1_xboole_0))
      | ~ v1_relat_1(A_252)
      | ~ r2_hidden(k4_tarski(D_255,E_253),k5_relat_1(k1_xboole_0,B_254))
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_254))
      | ~ v1_relat_1(B_254) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_695])).

tff(c_704,plain,(
    ! [D_255,E_253,B_254] :
      ( ~ r2_hidden(k4_tarski(D_255,E_253),k5_relat_1(k1_xboole_0,B_254))
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_254))
      | ~ v1_relat_1(B_254) ) ),
    inference(splitLeft,[status(thm)],[c_703])).

tff(c_2832,plain,(
    ! [B_484,B_485,A_486,C_487] :
      ( ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_484))
      | ~ v1_relat_1(B_484)
      | ~ r1_tarski(B_485,k5_relat_1(k1_xboole_0,B_484))
      | r2_hidden(k4_tarski('#skF_7'(A_486,B_485,C_487),'#skF_8'(A_486,B_485,C_487)),C_487)
      | k5_relat_1(A_486,B_485) = C_487
      | ~ v1_relat_1(C_487)
      | ~ v1_relat_1(B_485)
      | ~ v1_relat_1(A_486) ) ),
    inference(resolution,[status(thm)],[c_2109,c_704])).

tff(c_2853,plain,(
    ! [B_484,A_486,C_487] :
      ( ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_484))
      | ~ v1_relat_1(B_484)
      | r2_hidden(k4_tarski('#skF_7'(A_486,k1_xboole_0,C_487),'#skF_8'(A_486,k1_xboole_0,C_487)),C_487)
      | k5_relat_1(A_486,k1_xboole_0) = C_487
      | ~ v1_relat_1(C_487)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_486) ) ),
    inference(resolution,[status(thm)],[c_2,c_2832])).

tff(c_2862,plain,(
    ! [B_484,A_486,C_487] :
      ( ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_484))
      | ~ v1_relat_1(B_484)
      | r2_hidden(k4_tarski('#skF_7'(A_486,k1_xboole_0,C_487),'#skF_8'(A_486,k1_xboole_0,C_487)),C_487)
      | k5_relat_1(A_486,k1_xboole_0) = C_487
      | ~ v1_relat_1(C_487)
      | ~ v1_relat_1(A_486) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_2853])).

tff(c_2863,plain,(
    ! [B_484] :
      ( ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_484))
      | ~ v1_relat_1(B_484) ) ),
    inference(splitLeft,[status(thm)],[c_2862])).

tff(c_2972,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_2963,c_2863])).

tff(c_3029,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_55,c_2972])).

tff(c_3099,plain,(
    ! [A_512,C_513] :
      ( r2_hidden(k4_tarski('#skF_7'(A_512,k1_xboole_0,C_513),'#skF_8'(A_512,k1_xboole_0,C_513)),C_513)
      | k5_relat_1(A_512,k1_xboole_0) = C_513
      | ~ v1_relat_1(C_513)
      | ~ v1_relat_1(A_512) ) ),
    inference(splitRight,[status(thm)],[c_2862])).

tff(c_3140,plain,(
    ! [A_516,C_517,B_518] :
      ( r2_hidden(k4_tarski('#skF_7'(A_516,k1_xboole_0,C_517),'#skF_8'(A_516,k1_xboole_0,C_517)),B_518)
      | ~ r1_tarski(C_517,B_518)
      | k5_relat_1(A_516,k1_xboole_0) = C_517
      | ~ v1_relat_1(C_517)
      | ~ v1_relat_1(A_516) ) ),
    inference(resolution,[status(thm)],[c_3099,c_8])).

tff(c_3183,plain,(
    ! [C_519,A_520,B_521] :
      ( ~ r1_tarski(C_519,k2_zfmisc_1(k4_tarski('#skF_7'(A_520,k1_xboole_0,C_519),'#skF_8'(A_520,k1_xboole_0,C_519)),B_521))
      | k5_relat_1(A_520,k1_xboole_0) = C_519
      | ~ v1_relat_1(C_519)
      | ~ v1_relat_1(A_520) ) ),
    inference(resolution,[status(thm)],[c_3140,c_6])).

tff(c_3207,plain,(
    ! [A_520] :
      ( k5_relat_1(A_520,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_520) ) ),
    inference(resolution,[status(thm)],[c_2,c_3183])).

tff(c_3216,plain,(
    ! [A_522] :
      ( k5_relat_1(A_522,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_522) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_3207])).

tff(c_3226,plain,(
    k5_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_55,c_3216])).

tff(c_2328,plain,(
    ! [A_405,B_406,C_407,B_408] :
      ( r2_hidden(k4_tarski('#skF_7'(A_405,B_406,C_407),'#skF_8'(A_405,B_406,C_407)),B_408)
      | ~ r1_tarski(C_407,B_408)
      | r2_hidden(k4_tarski('#skF_6'(A_405,B_406,C_407),'#skF_5'(A_405,B_406,C_407)),B_406)
      | k5_relat_1(A_405,B_406) = C_407
      | ~ v1_relat_1(C_407)
      | ~ v1_relat_1(B_406)
      | ~ v1_relat_1(A_405) ) ),
    inference(resolution,[status(thm)],[c_162,c_8])).

tff(c_2651,plain,(
    ! [A_465,C_466,A_467,B_468] :
      ( ~ v1_relat_1(k5_relat_1(A_465,k1_xboole_0))
      | ~ v1_relat_1(A_465)
      | ~ r1_tarski(C_466,k5_relat_1(A_465,k1_xboole_0))
      | r2_hidden(k4_tarski('#skF_6'(A_467,B_468,C_466),'#skF_5'(A_467,B_468,C_466)),B_468)
      | k5_relat_1(A_467,B_468) = C_466
      | ~ v1_relat_1(C_466)
      | ~ v1_relat_1(B_468)
      | ~ v1_relat_1(A_467) ) ),
    inference(resolution,[status(thm)],[c_2328,c_194])).

tff(c_2687,plain,(
    ! [A_465,A_467,B_468] :
      ( ~ v1_relat_1(k5_relat_1(A_465,k1_xboole_0))
      | ~ v1_relat_1(A_465)
      | r2_hidden(k4_tarski('#skF_6'(A_467,B_468,k1_xboole_0),'#skF_5'(A_467,B_468,k1_xboole_0)),B_468)
      | k5_relat_1(A_467,B_468) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(B_468)
      | ~ v1_relat_1(A_467) ) ),
    inference(resolution,[status(thm)],[c_2,c_2651])).

tff(c_2701,plain,(
    ! [A_465,A_467,B_468] :
      ( ~ v1_relat_1(k5_relat_1(A_465,k1_xboole_0))
      | ~ v1_relat_1(A_465)
      | r2_hidden(k4_tarski('#skF_6'(A_467,B_468,k1_xboole_0),'#skF_5'(A_467,B_468,k1_xboole_0)),B_468)
      | k5_relat_1(A_467,B_468) = k1_xboole_0
      | ~ v1_relat_1(B_468)
      | ~ v1_relat_1(A_467) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_2687])).

tff(c_2702,plain,(
    ! [A_465] :
      ( ~ v1_relat_1(k5_relat_1(A_465,k1_xboole_0))
      | ~ v1_relat_1(A_465) ) ),
    inference(splitLeft,[status(thm)],[c_2701])).

tff(c_3245,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_3226,c_2702])).

tff(c_3370,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_55,c_3245])).

tff(c_3372,plain,(
    ! [A_523,B_524] :
      ( r2_hidden(k4_tarski('#skF_6'(A_523,B_524,k1_xboole_0),'#skF_5'(A_523,B_524,k1_xboole_0)),B_524)
      | k5_relat_1(A_523,B_524) = k1_xboole_0
      | ~ v1_relat_1(B_524)
      | ~ v1_relat_1(A_523) ) ),
    inference(splitRight,[status(thm)],[c_2701])).

tff(c_3456,plain,(
    ! [A_535,B_536,B_537] :
      ( r2_hidden(k4_tarski('#skF_6'(A_535,B_536,k1_xboole_0),'#skF_5'(A_535,B_536,k1_xboole_0)),B_537)
      | ~ r1_tarski(B_536,B_537)
      | k5_relat_1(A_535,B_536) = k1_xboole_0
      | ~ v1_relat_1(B_536)
      | ~ v1_relat_1(A_535) ) ),
    inference(resolution,[status(thm)],[c_3372,c_8])).

tff(c_3550,plain,(
    ! [B_541,A_542,B_543] :
      ( ~ r1_tarski(B_541,k2_zfmisc_1(k4_tarski('#skF_6'(A_542,B_541,k1_xboole_0),'#skF_5'(A_542,B_541,k1_xboole_0)),B_543))
      | k5_relat_1(A_542,B_541) = k1_xboole_0
      | ~ v1_relat_1(B_541)
      | ~ v1_relat_1(A_542) ) ),
    inference(resolution,[status(thm)],[c_3456,c_6])).

tff(c_3594,plain,(
    ! [A_542] :
      ( k5_relat_1(A_542,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_542) ) ),
    inference(resolution,[status(thm)],[c_2,c_3550])).

tff(c_3609,plain,(
    ! [A_545] :
      ( k5_relat_1(A_545,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_545) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_3594])).

tff(c_3619,plain,(
    k5_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_55,c_3609])).

tff(c_3498,plain,(
    ! [B_538,B_539,A_540] :
      ( ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_538))
      | ~ v1_relat_1(B_538)
      | ~ r1_tarski(B_539,k5_relat_1(k1_xboole_0,B_538))
      | k5_relat_1(A_540,B_539) = k1_xboole_0
      | ~ v1_relat_1(B_539)
      | ~ v1_relat_1(A_540) ) ),
    inference(resolution,[status(thm)],[c_3456,c_704])).

tff(c_3534,plain,(
    ! [B_538,A_540] :
      ( ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_538))
      | ~ v1_relat_1(B_538)
      | k5_relat_1(A_540,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_540) ) ),
    inference(resolution,[status(thm)],[c_2,c_3498])).

tff(c_3548,plain,(
    ! [B_538,A_540] :
      ( ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_538))
      | ~ v1_relat_1(B_538)
      | k5_relat_1(A_540,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_540) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_3534])).

tff(c_3549,plain,(
    ! [B_538] :
      ( ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_538))
      | ~ v1_relat_1(B_538) ) ),
    inference(splitLeft,[status(thm)],[c_3548])).

tff(c_3625,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_3619,c_3549])).

tff(c_3747,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_55,c_3625])).

tff(c_3749,plain,(
    ! [A_546] :
      ( k5_relat_1(A_546,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_546) ) ),
    inference(splitRight,[status(thm)],[c_3548])).

tff(c_3761,plain,(
    k5_relat_1('#skF_9',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_36,c_3749])).

tff(c_3759,plain,(
    k5_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_55,c_3749])).

tff(c_24,plain,(
    ! [A_23,B_75,C_101] :
      ( r2_hidden(k4_tarski('#skF_4'(A_23,B_75,C_101),'#skF_6'(A_23,B_75,C_101)),A_23)
      | r2_hidden(k4_tarski('#skF_7'(A_23,B_75,C_101),'#skF_8'(A_23,B_75,C_101)),C_101)
      | k5_relat_1(A_23,B_75) = C_101
      | ~ v1_relat_1(C_101)
      | ~ v1_relat_1(B_75)
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_706,plain,(
    ! [D_261,E_262,B_263] :
      ( ~ r2_hidden(k4_tarski(D_261,E_262),k5_relat_1(k1_xboole_0,B_263))
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_263))
      | ~ v1_relat_1(B_263) ) ),
    inference(splitLeft,[status(thm)],[c_703])).

tff(c_2496,plain,(
    ! [B_433,A_434,B_435] :
      ( ~ v1_relat_1(B_433)
      | r2_hidden(k4_tarski('#skF_4'(A_434,B_435,k5_relat_1(k1_xboole_0,B_433)),'#skF_6'(A_434,B_435,k5_relat_1(k1_xboole_0,B_433))),A_434)
      | k5_relat_1(k1_xboole_0,B_433) = k5_relat_1(A_434,B_435)
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_433))
      | ~ v1_relat_1(B_435)
      | ~ v1_relat_1(A_434) ) ),
    inference(resolution,[status(thm)],[c_24,c_706])).

tff(c_2530,plain,(
    ! [A_185,B_433,B_435] :
      ( ~ v1_relat_1(A_185)
      | ~ v1_relat_1(B_433)
      | k5_relat_1(k5_relat_1(A_185,k1_xboole_0),B_435) = k5_relat_1(k1_xboole_0,B_433)
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_433))
      | ~ v1_relat_1(B_435)
      | ~ v1_relat_1(k5_relat_1(A_185,k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_2496,c_194])).

tff(c_3787,plain,(
    ! [A_185,B_435] :
      ( ~ v1_relat_1(A_185)
      | ~ v1_relat_1(k1_xboole_0)
      | k5_relat_1(k5_relat_1(A_185,k1_xboole_0),B_435) = k5_relat_1(k1_xboole_0,k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(B_435)
      | ~ v1_relat_1(k5_relat_1(A_185,k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3759,c_2530])).

tff(c_4890,plain,(
    ! [A_558,B_559] :
      ( ~ v1_relat_1(A_558)
      | k5_relat_1(k5_relat_1(A_558,k1_xboole_0),B_559) = k1_xboole_0
      | ~ v1_relat_1(B_559)
      | ~ v1_relat_1(k5_relat_1(A_558,k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_3759,c_55,c_3787])).

tff(c_4894,plain,(
    ! [B_559] :
      ( ~ v1_relat_1('#skF_9')
      | k5_relat_1(k5_relat_1('#skF_9',k1_xboole_0),B_559) = k1_xboole_0
      | ~ v1_relat_1(B_559)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3761,c_4890])).

tff(c_4903,plain,(
    ! [B_560] :
      ( k5_relat_1(k1_xboole_0,B_560) = k1_xboole_0
      | ~ v1_relat_1(B_560) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_3761,c_36,c_4894])).

tff(c_4912,plain,(
    k5_relat_1(k1_xboole_0,'#skF_9') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_36,c_4903])).

tff(c_4919,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_4912])).

tff(c_4920,plain,(
    ! [A_252] :
      ( ~ v1_relat_1(k5_relat_1(A_252,k1_xboole_0))
      | ~ v1_relat_1(A_252) ) ),
    inference(splitRight,[status(thm)],[c_703])).

tff(c_6486,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_6391,c_4920])).

tff(c_6583,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_55,c_6486])).

tff(c_6584,plain,(
    k5_relat_1('#skF_9',k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_6590,plain,(
    ! [A_2] : ~ v1_relat_1(A_2) ),
    inference(splitLeft,[status(thm)],[c_49])).

tff(c_6594,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6590,c_36])).

tff(c_6595,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_49])).

tff(c_7056,plain,(
    ! [A_858,B_859,C_860] :
      ( r2_hidden(k4_tarski('#skF_6'(A_858,B_859,C_860),'#skF_5'(A_858,B_859,C_860)),B_859)
      | r2_hidden(k4_tarski('#skF_7'(A_858,B_859,C_860),'#skF_8'(A_858,B_859,C_860)),C_860)
      | k5_relat_1(A_858,B_859) = C_860
      | ~ v1_relat_1(C_860)
      | ~ v1_relat_1(B_859)
      | ~ v1_relat_1(A_858) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_6585,plain,(
    k5_relat_1(k1_xboole_0,'#skF_9') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_6721,plain,(
    ! [D_803,E_804,A_805,B_806] :
      ( r2_hidden(k4_tarski(D_803,'#skF_3'(D_803,E_804,k5_relat_1(A_805,B_806),B_806,A_805)),A_805)
      | ~ r2_hidden(k4_tarski(D_803,E_804),k5_relat_1(A_805,B_806))
      | ~ v1_relat_1(k5_relat_1(A_805,B_806))
      | ~ v1_relat_1(B_806)
      | ~ v1_relat_1(A_805) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_6728,plain,(
    ! [D_803,E_804] :
      ( r2_hidden(k4_tarski(D_803,'#skF_3'(D_803,E_804,k1_xboole_0,'#skF_9',k1_xboole_0)),k1_xboole_0)
      | ~ r2_hidden(k4_tarski(D_803,E_804),k5_relat_1(k1_xboole_0,'#skF_9'))
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,'#skF_9'))
      | ~ v1_relat_1('#skF_9')
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6585,c_6721])).

tff(c_6733,plain,(
    ! [D_807,E_808] :
      ( r2_hidden(k4_tarski(D_807,'#skF_3'(D_807,E_808,k1_xboole_0,'#skF_9',k1_xboole_0)),k1_xboole_0)
      | ~ r2_hidden(k4_tarski(D_807,E_808),k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6595,c_36,c_6595,c_6585,c_6585,c_6728])).

tff(c_6737,plain,(
    ! [D_807,E_808,B_16] :
      ( r2_hidden(k4_tarski(D_807,'#skF_3'(D_807,E_808,k1_xboole_0,'#skF_9',k1_xboole_0)),B_16)
      | ~ r1_tarski(k1_xboole_0,B_16)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ r2_hidden(k4_tarski(D_807,E_808),k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_6733,c_8])).

tff(c_6744,plain,(
    ! [D_809,E_810,B_811] :
      ( r2_hidden(k4_tarski(D_809,'#skF_3'(D_809,E_810,k1_xboole_0,'#skF_9',k1_xboole_0)),B_811)
      | ~ r2_hidden(k4_tarski(D_809,E_810),k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6595,c_2,c_6737])).

tff(c_6754,plain,(
    ! [D_809,E_810] : ~ r2_hidden(k4_tarski(D_809,E_810),k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_6744,c_6])).

tff(c_7080,plain,(
    ! [A_858,C_860] :
      ( r2_hidden(k4_tarski('#skF_7'(A_858,k1_xboole_0,C_860),'#skF_8'(A_858,k1_xboole_0,C_860)),C_860)
      | k5_relat_1(A_858,k1_xboole_0) = C_860
      | ~ v1_relat_1(C_860)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_858) ) ),
    inference(resolution,[status(thm)],[c_7056,c_6754])).

tff(c_7128,plain,(
    ! [A_861,C_862] :
      ( r2_hidden(k4_tarski('#skF_7'(A_861,k1_xboole_0,C_862),'#skF_8'(A_861,k1_xboole_0,C_862)),C_862)
      | k5_relat_1(A_861,k1_xboole_0) = C_862
      | ~ v1_relat_1(C_862)
      | ~ v1_relat_1(A_861) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6595,c_7080])).

tff(c_7152,plain,(
    ! [A_861] :
      ( k5_relat_1(A_861,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_861) ) ),
    inference(resolution,[status(thm)],[c_7128,c_6754])).

tff(c_7167,plain,(
    ! [A_863] :
      ( k5_relat_1(A_863,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_863) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6595,c_7152])).

tff(c_7176,plain,(
    k5_relat_1('#skF_9',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_36,c_7167])).

tff(c_7182,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6584,c_7176])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:31:05 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.59/3.15  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.59/3.17  
% 8.59/3.17  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.59/3.17  %$ r2_hidden > r1_tarski > v1_relat_1 > k5_relat_1 > k4_xboole_0 > k4_tarski > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_6 > #skF_4 > #skF_5 > #skF_9 > #skF_7 > #skF_3 > #skF_2 > #skF_8 > #skF_1
% 8.59/3.17  
% 8.59/3.17  %Foreground sorts:
% 8.59/3.17  
% 8.59/3.17  
% 8.59/3.17  %Background operators:
% 8.59/3.17  
% 8.59/3.17  
% 8.59/3.17  %Foreground operators:
% 8.59/3.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.59/3.17  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.59/3.17  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 8.59/3.17  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 8.59/3.17  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 8.59/3.17  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.59/3.17  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 8.59/3.17  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 8.59/3.17  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.59/3.17  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 8.59/3.17  tff('#skF_9', type, '#skF_9': $i).
% 8.59/3.17  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 8.59/3.17  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i * $i) > $i).
% 8.59/3.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.59/3.17  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 8.59/3.17  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 8.59/3.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.59/3.17  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 8.59/3.17  tff('#skF_8', type, '#skF_8': ($i * $i * $i) > $i).
% 8.59/3.17  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 8.59/3.17  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 8.59/3.17  
% 8.59/3.20  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 8.59/3.20  tff(f_64, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_relat_1)).
% 8.59/3.20  tff(f_71, negated_conjecture, ~(![A]: (v1_relat_1(A) => ((k5_relat_1(k1_xboole_0, A) = k1_xboole_0) & (k5_relat_1(A, k1_xboole_0) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_relat_1)).
% 8.59/3.20  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 8.59/3.20  tff(f_60, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => ((C = k5_relat_1(A, B)) <=> (![D, E]: (r2_hidden(k4_tarski(D, E), C) <=> (?[F]: (r2_hidden(k4_tarski(D, F), A) & r2_hidden(k4_tarski(F, E), B)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_relat_1)).
% 8.59/3.20  tff(f_42, axiom, (![A]: (v1_relat_1(A) => (![B]: (r1_tarski(A, B) <=> (![C, D]: (r2_hidden(k4_tarski(C, D), A) => r2_hidden(k4_tarski(C, D), B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_relat_1)).
% 8.59/3.20  tff(f_32, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 8.59/3.20  tff(c_4, plain, (![A_2, B_3]: (k4_xboole_0(A_2, k2_xboole_0(A_2, B_3))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 8.59/3.20  tff(c_46, plain, (![A_129, B_130]: (v1_relat_1(k4_xboole_0(A_129, B_130)) | ~v1_relat_1(A_129))), inference(cnfTransformation, [status(thm)], [f_64])).
% 8.59/3.20  tff(c_49, plain, (![A_2]: (v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_2))), inference(superposition, [status(thm), theory('equality')], [c_4, c_46])).
% 8.59/3.20  tff(c_51, plain, (![A_2]: (~v1_relat_1(A_2))), inference(splitLeft, [status(thm)], [c_49])).
% 8.59/3.20  tff(c_36, plain, (v1_relat_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_71])).
% 8.59/3.20  tff(c_54, plain, $false, inference(negUnitSimplification, [status(thm)], [c_51, c_36])).
% 8.59/3.20  tff(c_55, plain, (v1_relat_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_49])).
% 8.59/3.20  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 8.59/3.20  tff(c_162, plain, (![A_174, B_175, C_176]: (r2_hidden(k4_tarski('#skF_6'(A_174, B_175, C_176), '#skF_5'(A_174, B_175, C_176)), B_175) | r2_hidden(k4_tarski('#skF_7'(A_174, B_175, C_176), '#skF_8'(A_174, B_175, C_176)), C_176) | k5_relat_1(A_174, B_175)=C_176 | ~v1_relat_1(C_176) | ~v1_relat_1(B_175) | ~v1_relat_1(A_174))), inference(cnfTransformation, [status(thm)], [f_60])).
% 8.59/3.20  tff(c_8, plain, (![C_21, D_22, B_16, A_6]: (r2_hidden(k4_tarski(C_21, D_22), B_16) | ~r2_hidden(k4_tarski(C_21, D_22), A_6) | ~r1_tarski(A_6, B_16) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_42])).
% 8.59/3.20  tff(c_5404, plain, (![A_612, B_613, C_614, B_615]: (r2_hidden(k4_tarski('#skF_7'(A_612, B_613, C_614), '#skF_8'(A_612, B_613, C_614)), B_615) | ~r1_tarski(C_614, B_615) | r2_hidden(k4_tarski('#skF_6'(A_612, B_613, C_614), '#skF_5'(A_612, B_613, C_614)), B_613) | k5_relat_1(A_612, B_613)=C_614 | ~v1_relat_1(C_614) | ~v1_relat_1(B_613) | ~v1_relat_1(A_612))), inference(resolution, [status(thm)], [c_162, c_8])).
% 8.59/3.20  tff(c_6, plain, (![A_4, B_5]: (~r2_hidden(A_4, k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 8.59/3.20  tff(c_6031, plain, (![C_714, A_715, B_716, B_717]: (~r1_tarski(C_714, k2_zfmisc_1(k4_tarski('#skF_7'(A_715, B_716, C_714), '#skF_8'(A_715, B_716, C_714)), B_717)) | r2_hidden(k4_tarski('#skF_6'(A_715, B_716, C_714), '#skF_5'(A_715, B_716, C_714)), B_716) | k5_relat_1(A_715, B_716)=C_714 | ~v1_relat_1(C_714) | ~v1_relat_1(B_716) | ~v1_relat_1(A_715))), inference(resolution, [status(thm)], [c_5404, c_6])).
% 8.59/3.20  tff(c_6034, plain, (![A_715, B_716]: (r2_hidden(k4_tarski('#skF_6'(A_715, B_716, k1_xboole_0), '#skF_5'(A_715, B_716, k1_xboole_0)), B_716) | k5_relat_1(A_715, B_716)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(B_716) | ~v1_relat_1(A_715))), inference(resolution, [status(thm)], [c_2, c_6031])).
% 8.59/3.20  tff(c_6038, plain, (![A_718, B_719]: (r2_hidden(k4_tarski('#skF_6'(A_718, B_719, k1_xboole_0), '#skF_5'(A_718, B_719, k1_xboole_0)), B_719) | k5_relat_1(A_718, B_719)=k1_xboole_0 | ~v1_relat_1(B_719) | ~v1_relat_1(A_718))), inference(demodulation, [status(thm), theory('equality')], [c_55, c_6034])).
% 8.59/3.20  tff(c_6045, plain, (![A_720, B_721, B_722]: (r2_hidden(k4_tarski('#skF_6'(A_720, B_721, k1_xboole_0), '#skF_5'(A_720, B_721, k1_xboole_0)), B_722) | ~r1_tarski(B_721, B_722) | k5_relat_1(A_720, B_721)=k1_xboole_0 | ~v1_relat_1(B_721) | ~v1_relat_1(A_720))), inference(resolution, [status(thm)], [c_6038, c_8])).
% 8.59/3.20  tff(c_6057, plain, (![B_723, A_724, B_725]: (~r1_tarski(B_723, k2_zfmisc_1(k4_tarski('#skF_6'(A_724, B_723, k1_xboole_0), '#skF_5'(A_724, B_723, k1_xboole_0)), B_725)) | k5_relat_1(A_724, B_723)=k1_xboole_0 | ~v1_relat_1(B_723) | ~v1_relat_1(A_724))), inference(resolution, [status(thm)], [c_6045, c_6])).
% 8.59/3.20  tff(c_6061, plain, (![A_724]: (k5_relat_1(A_724, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_724))), inference(resolution, [status(thm)], [c_2, c_6057])).
% 8.59/3.20  tff(c_6088, plain, (![A_732]: (k5_relat_1(A_732, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_732))), inference(demodulation, [status(thm), theory('equality')], [c_55, c_6061])).
% 8.59/3.20  tff(c_6098, plain, (k5_relat_1(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_55, c_6088])).
% 8.59/3.20  tff(c_142, plain, (![D_164, E_165, A_166, B_167]: (r2_hidden(k4_tarski(D_164, '#skF_3'(D_164, E_165, k5_relat_1(A_166, B_167), B_167, A_166)), A_166) | ~r2_hidden(k4_tarski(D_164, E_165), k5_relat_1(A_166, B_167)) | ~v1_relat_1(k5_relat_1(A_166, B_167)) | ~v1_relat_1(B_167) | ~v1_relat_1(A_166))), inference(cnfTransformation, [status(thm)], [f_60])).
% 8.59/3.20  tff(c_650, plain, (![B_249, D_248, B_247, A_251, E_250]: (r2_hidden(k4_tarski(D_248, '#skF_3'(D_248, E_250, k5_relat_1(A_251, B_247), B_247, A_251)), B_249) | ~r1_tarski(A_251, B_249) | ~r2_hidden(k4_tarski(D_248, E_250), k5_relat_1(A_251, B_247)) | ~v1_relat_1(k5_relat_1(A_251, B_247)) | ~v1_relat_1(B_247) | ~v1_relat_1(A_251))), inference(resolution, [status(thm)], [c_142, c_8])).
% 8.59/3.20  tff(c_4923, plain, (![B_568, D_569, A_570, E_567, B_566]: (~r1_tarski(A_570, k2_zfmisc_1(k4_tarski(D_569, '#skF_3'(D_569, E_567, k5_relat_1(A_570, B_568), B_568, A_570)), B_566)) | ~r2_hidden(k4_tarski(D_569, E_567), k5_relat_1(A_570, B_568)) | ~v1_relat_1(k5_relat_1(A_570, B_568)) | ~v1_relat_1(B_568) | ~v1_relat_1(A_570))), inference(resolution, [status(thm)], [c_650, c_6])).
% 8.59/3.20  tff(c_4927, plain, (![D_569, E_567, B_568]: (~r2_hidden(k4_tarski(D_569, E_567), k5_relat_1(k1_xboole_0, B_568)) | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_568)) | ~v1_relat_1(B_568) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_2, c_4923])).
% 8.59/3.20  tff(c_4930, plain, (![D_569, E_567, B_568]: (~r2_hidden(k4_tarski(D_569, E_567), k5_relat_1(k1_xboole_0, B_568)) | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_568)) | ~v1_relat_1(B_568))), inference(demodulation, [status(thm), theory('equality')], [c_55, c_4927])).
% 8.59/3.20  tff(c_5934, plain, (![B_696, C_697, A_698, B_699]: (~v1_relat_1(k5_relat_1(k1_xboole_0, B_696)) | ~v1_relat_1(B_696) | ~r1_tarski(C_697, k5_relat_1(k1_xboole_0, B_696)) | r2_hidden(k4_tarski('#skF_6'(A_698, B_699, C_697), '#skF_5'(A_698, B_699, C_697)), B_699) | k5_relat_1(A_698, B_699)=C_697 | ~v1_relat_1(C_697) | ~v1_relat_1(B_699) | ~v1_relat_1(A_698))), inference(resolution, [status(thm)], [c_5404, c_4930])).
% 8.59/3.20  tff(c_5955, plain, (![B_696, A_698, B_699]: (~v1_relat_1(k5_relat_1(k1_xboole_0, B_696)) | ~v1_relat_1(B_696) | r2_hidden(k4_tarski('#skF_6'(A_698, B_699, k1_xboole_0), '#skF_5'(A_698, B_699, k1_xboole_0)), B_699) | k5_relat_1(A_698, B_699)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(B_699) | ~v1_relat_1(A_698))), inference(resolution, [status(thm)], [c_2, c_5934])).
% 8.59/3.20  tff(c_5964, plain, (![B_696, A_698, B_699]: (~v1_relat_1(k5_relat_1(k1_xboole_0, B_696)) | ~v1_relat_1(B_696) | r2_hidden(k4_tarski('#skF_6'(A_698, B_699, k1_xboole_0), '#skF_5'(A_698, B_699, k1_xboole_0)), B_699) | k5_relat_1(A_698, B_699)=k1_xboole_0 | ~v1_relat_1(B_699) | ~v1_relat_1(A_698))), inference(demodulation, [status(thm), theory('equality')], [c_55, c_5955])).
% 8.59/3.20  tff(c_5965, plain, (![B_696]: (~v1_relat_1(k5_relat_1(k1_xboole_0, B_696)) | ~v1_relat_1(B_696))), inference(splitLeft, [status(thm)], [c_5964])).
% 8.59/3.20  tff(c_6113, plain, (~v1_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_6098, c_5965])).
% 8.59/3.20  tff(c_6165, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_55, c_55, c_6113])).
% 8.59/3.20  tff(c_6167, plain, (![A_733, B_734]: (r2_hidden(k4_tarski('#skF_6'(A_733, B_734, k1_xboole_0), '#skF_5'(A_733, B_734, k1_xboole_0)), B_734) | k5_relat_1(A_733, B_734)=k1_xboole_0 | ~v1_relat_1(B_734) | ~v1_relat_1(A_733))), inference(splitRight, [status(thm)], [c_5964])).
% 8.59/3.20  tff(c_6189, plain, (![A_735, B_736, B_737]: (r2_hidden(k4_tarski('#skF_6'(A_735, B_736, k1_xboole_0), '#skF_5'(A_735, B_736, k1_xboole_0)), B_737) | ~r1_tarski(B_736, B_737) | k5_relat_1(A_735, B_736)=k1_xboole_0 | ~v1_relat_1(B_736) | ~v1_relat_1(A_735))), inference(resolution, [status(thm)], [c_6167, c_8])).
% 8.59/3.20  tff(c_6276, plain, (![B_748, A_749, B_750]: (~r1_tarski(B_748, k2_zfmisc_1(k4_tarski('#skF_6'(A_749, B_748, k1_xboole_0), '#skF_5'(A_749, B_748, k1_xboole_0)), B_750)) | k5_relat_1(A_749, B_748)=k1_xboole_0 | ~v1_relat_1(B_748) | ~v1_relat_1(A_749))), inference(resolution, [status(thm)], [c_6189, c_6])).
% 8.59/3.20  tff(c_6280, plain, (![A_749]: (k5_relat_1(A_749, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_749))), inference(resolution, [status(thm)], [c_2, c_6276])).
% 8.59/3.20  tff(c_6284, plain, (![A_751]: (k5_relat_1(A_751, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_751))), inference(demodulation, [status(thm), theory('equality')], [c_55, c_6280])).
% 8.59/3.20  tff(c_6294, plain, (k5_relat_1(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_55, c_6284])).
% 8.59/3.20  tff(c_6217, plain, (![B_740, B_741, A_742]: (~v1_relat_1(k5_relat_1(k1_xboole_0, B_740)) | ~v1_relat_1(B_740) | ~r1_tarski(B_741, k5_relat_1(k1_xboole_0, B_740)) | k5_relat_1(A_742, B_741)=k1_xboole_0 | ~v1_relat_1(B_741) | ~v1_relat_1(A_742))), inference(resolution, [status(thm)], [c_6189, c_4930])).
% 8.59/3.20  tff(c_6238, plain, (![B_740, A_742]: (~v1_relat_1(k5_relat_1(k1_xboole_0, B_740)) | ~v1_relat_1(B_740) | k5_relat_1(A_742, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_742))), inference(resolution, [status(thm)], [c_2, c_6217])).
% 8.59/3.20  tff(c_6247, plain, (![B_740, A_742]: (~v1_relat_1(k5_relat_1(k1_xboole_0, B_740)) | ~v1_relat_1(B_740) | k5_relat_1(A_742, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_742))), inference(demodulation, [status(thm), theory('equality')], [c_55, c_6238])).
% 8.59/3.20  tff(c_6248, plain, (![B_740]: (~v1_relat_1(k5_relat_1(k1_xboole_0, B_740)) | ~v1_relat_1(B_740))), inference(splitLeft, [status(thm)], [c_6247])).
% 8.59/3.20  tff(c_6300, plain, (~v1_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_6294, c_6248])).
% 8.59/3.20  tff(c_6346, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_55, c_55, c_6300])).
% 8.59/3.20  tff(c_6381, plain, (![A_755]: (k5_relat_1(A_755, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_755))), inference(splitRight, [status(thm)], [c_6247])).
% 8.59/3.20  tff(c_6391, plain, (k5_relat_1(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_55, c_6381])).
% 8.59/3.20  tff(c_34, plain, (k5_relat_1('#skF_9', k1_xboole_0)!=k1_xboole_0 | k5_relat_1(k1_xboole_0, '#skF_9')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_71])).
% 8.59/3.20  tff(c_50, plain, (k5_relat_1(k1_xboole_0, '#skF_9')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_34])).
% 8.59/3.20  tff(c_2109, plain, (![A_374, B_375, C_376, B_377]: (r2_hidden(k4_tarski('#skF_6'(A_374, B_375, C_376), '#skF_5'(A_374, B_375, C_376)), B_377) | ~r1_tarski(B_375, B_377) | r2_hidden(k4_tarski('#skF_7'(A_374, B_375, C_376), '#skF_8'(A_374, B_375, C_376)), C_376) | k5_relat_1(A_374, B_375)=C_376 | ~v1_relat_1(C_376) | ~v1_relat_1(B_375) | ~v1_relat_1(A_374))), inference(resolution, [status(thm)], [c_162, c_8])).
% 8.59/3.20  tff(c_2895, plain, (![B_494, A_495, C_496, B_497]: (~r1_tarski(B_494, k2_zfmisc_1(k4_tarski('#skF_6'(A_495, B_494, C_496), '#skF_5'(A_495, B_494, C_496)), B_497)) | r2_hidden(k4_tarski('#skF_7'(A_495, B_494, C_496), '#skF_8'(A_495, B_494, C_496)), C_496) | k5_relat_1(A_495, B_494)=C_496 | ~v1_relat_1(C_496) | ~v1_relat_1(B_494) | ~v1_relat_1(A_495))), inference(resolution, [status(thm)], [c_2109, c_6])).
% 8.59/3.20  tff(c_2898, plain, (![A_495, C_496]: (r2_hidden(k4_tarski('#skF_7'(A_495, k1_xboole_0, C_496), '#skF_8'(A_495, k1_xboole_0, C_496)), C_496) | k5_relat_1(A_495, k1_xboole_0)=C_496 | ~v1_relat_1(C_496) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_495))), inference(resolution, [status(thm)], [c_2, c_2895])).
% 8.59/3.20  tff(c_2902, plain, (![A_498, C_499]: (r2_hidden(k4_tarski('#skF_7'(A_498, k1_xboole_0, C_499), '#skF_8'(A_498, k1_xboole_0, C_499)), C_499) | k5_relat_1(A_498, k1_xboole_0)=C_499 | ~v1_relat_1(C_499) | ~v1_relat_1(A_498))), inference(demodulation, [status(thm), theory('equality')], [c_55, c_2898])).
% 8.59/3.20  tff(c_2921, plain, (![A_500, C_501, B_502]: (r2_hidden(k4_tarski('#skF_7'(A_500, k1_xboole_0, C_501), '#skF_8'(A_500, k1_xboole_0, C_501)), B_502) | ~r1_tarski(C_501, B_502) | k5_relat_1(A_500, k1_xboole_0)=C_501 | ~v1_relat_1(C_501) | ~v1_relat_1(A_500))), inference(resolution, [status(thm)], [c_2902, c_8])).
% 8.59/3.20  tff(c_2945, plain, (![C_503, A_504, B_505]: (~r1_tarski(C_503, k2_zfmisc_1(k4_tarski('#skF_7'(A_504, k1_xboole_0, C_503), '#skF_8'(A_504, k1_xboole_0, C_503)), B_505)) | k5_relat_1(A_504, k1_xboole_0)=C_503 | ~v1_relat_1(C_503) | ~v1_relat_1(A_504))), inference(resolution, [status(thm)], [c_2921, c_6])).
% 8.59/3.20  tff(c_2949, plain, (![A_504]: (k5_relat_1(A_504, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_504))), inference(resolution, [status(thm)], [c_2, c_2945])).
% 8.59/3.20  tff(c_2953, plain, (![A_506]: (k5_relat_1(A_506, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_506))), inference(demodulation, [status(thm), theory('equality')], [c_55, c_2949])).
% 8.59/3.20  tff(c_2963, plain, (k5_relat_1(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_55, c_2953])).
% 8.59/3.20  tff(c_122, plain, (![D_158, E_159, A_160, B_161]: (r2_hidden(k4_tarski('#skF_3'(D_158, E_159, k5_relat_1(A_160, B_161), B_161, A_160), E_159), B_161) | ~r2_hidden(k4_tarski(D_158, E_159), k5_relat_1(A_160, B_161)) | ~v1_relat_1(k5_relat_1(A_160, B_161)) | ~v1_relat_1(B_161) | ~v1_relat_1(A_160))), inference(cnfTransformation, [status(thm)], [f_60])).
% 8.59/3.20  tff(c_175, plain, (![A_181, E_177, B_178, B_179, D_180]: (r2_hidden(k4_tarski('#skF_3'(D_180, E_177, k5_relat_1(A_181, B_178), B_178, A_181), E_177), B_179) | ~r1_tarski(B_178, B_179) | ~r2_hidden(k4_tarski(D_180, E_177), k5_relat_1(A_181, B_178)) | ~v1_relat_1(k5_relat_1(A_181, B_178)) | ~v1_relat_1(B_178) | ~v1_relat_1(A_181))), inference(resolution, [status(thm)], [c_122, c_8])).
% 8.59/3.20  tff(c_187, plain, (![A_185, D_182, B_186, B_184, E_183]: (~r1_tarski(B_186, k2_zfmisc_1(k4_tarski('#skF_3'(D_182, E_183, k5_relat_1(A_185, B_186), B_186, A_185), E_183), B_184)) | ~r2_hidden(k4_tarski(D_182, E_183), k5_relat_1(A_185, B_186)) | ~v1_relat_1(k5_relat_1(A_185, B_186)) | ~v1_relat_1(B_186) | ~v1_relat_1(A_185))), inference(resolution, [status(thm)], [c_175, c_6])).
% 8.59/3.20  tff(c_191, plain, (![D_182, E_183, A_185]: (~r2_hidden(k4_tarski(D_182, E_183), k5_relat_1(A_185, k1_xboole_0)) | ~v1_relat_1(k5_relat_1(A_185, k1_xboole_0)) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_185))), inference(resolution, [status(thm)], [c_2, c_187])).
% 8.59/3.20  tff(c_194, plain, (![D_182, E_183, A_185]: (~r2_hidden(k4_tarski(D_182, E_183), k5_relat_1(A_185, k1_xboole_0)) | ~v1_relat_1(k5_relat_1(A_185, k1_xboole_0)) | ~v1_relat_1(A_185))), inference(demodulation, [status(thm), theory('equality')], [c_55, c_191])).
% 8.59/3.20  tff(c_677, plain, (![A_252, A_256, E_253, D_255, B_254]: (~v1_relat_1(k5_relat_1(A_252, k1_xboole_0)) | ~v1_relat_1(A_252) | ~r1_tarski(A_256, k5_relat_1(A_252, k1_xboole_0)) | ~r2_hidden(k4_tarski(D_255, E_253), k5_relat_1(A_256, B_254)) | ~v1_relat_1(k5_relat_1(A_256, B_254)) | ~v1_relat_1(B_254) | ~v1_relat_1(A_256))), inference(resolution, [status(thm)], [c_650, c_194])).
% 8.59/3.20  tff(c_695, plain, (![A_252, D_255, E_253, B_254]: (~v1_relat_1(k5_relat_1(A_252, k1_xboole_0)) | ~v1_relat_1(A_252) | ~r2_hidden(k4_tarski(D_255, E_253), k5_relat_1(k1_xboole_0, B_254)) | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_254)) | ~v1_relat_1(B_254) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_2, c_677])).
% 8.59/3.20  tff(c_703, plain, (![A_252, D_255, E_253, B_254]: (~v1_relat_1(k5_relat_1(A_252, k1_xboole_0)) | ~v1_relat_1(A_252) | ~r2_hidden(k4_tarski(D_255, E_253), k5_relat_1(k1_xboole_0, B_254)) | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_254)) | ~v1_relat_1(B_254))), inference(demodulation, [status(thm), theory('equality')], [c_55, c_695])).
% 8.59/3.20  tff(c_704, plain, (![D_255, E_253, B_254]: (~r2_hidden(k4_tarski(D_255, E_253), k5_relat_1(k1_xboole_0, B_254)) | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_254)) | ~v1_relat_1(B_254))), inference(splitLeft, [status(thm)], [c_703])).
% 8.59/3.20  tff(c_2832, plain, (![B_484, B_485, A_486, C_487]: (~v1_relat_1(k5_relat_1(k1_xboole_0, B_484)) | ~v1_relat_1(B_484) | ~r1_tarski(B_485, k5_relat_1(k1_xboole_0, B_484)) | r2_hidden(k4_tarski('#skF_7'(A_486, B_485, C_487), '#skF_8'(A_486, B_485, C_487)), C_487) | k5_relat_1(A_486, B_485)=C_487 | ~v1_relat_1(C_487) | ~v1_relat_1(B_485) | ~v1_relat_1(A_486))), inference(resolution, [status(thm)], [c_2109, c_704])).
% 8.59/3.20  tff(c_2853, plain, (![B_484, A_486, C_487]: (~v1_relat_1(k5_relat_1(k1_xboole_0, B_484)) | ~v1_relat_1(B_484) | r2_hidden(k4_tarski('#skF_7'(A_486, k1_xboole_0, C_487), '#skF_8'(A_486, k1_xboole_0, C_487)), C_487) | k5_relat_1(A_486, k1_xboole_0)=C_487 | ~v1_relat_1(C_487) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_486))), inference(resolution, [status(thm)], [c_2, c_2832])).
% 8.59/3.20  tff(c_2862, plain, (![B_484, A_486, C_487]: (~v1_relat_1(k5_relat_1(k1_xboole_0, B_484)) | ~v1_relat_1(B_484) | r2_hidden(k4_tarski('#skF_7'(A_486, k1_xboole_0, C_487), '#skF_8'(A_486, k1_xboole_0, C_487)), C_487) | k5_relat_1(A_486, k1_xboole_0)=C_487 | ~v1_relat_1(C_487) | ~v1_relat_1(A_486))), inference(demodulation, [status(thm), theory('equality')], [c_55, c_2853])).
% 8.59/3.20  tff(c_2863, plain, (![B_484]: (~v1_relat_1(k5_relat_1(k1_xboole_0, B_484)) | ~v1_relat_1(B_484))), inference(splitLeft, [status(thm)], [c_2862])).
% 8.59/3.20  tff(c_2972, plain, (~v1_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2963, c_2863])).
% 8.59/3.20  tff(c_3029, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_55, c_55, c_2972])).
% 8.59/3.20  tff(c_3099, plain, (![A_512, C_513]: (r2_hidden(k4_tarski('#skF_7'(A_512, k1_xboole_0, C_513), '#skF_8'(A_512, k1_xboole_0, C_513)), C_513) | k5_relat_1(A_512, k1_xboole_0)=C_513 | ~v1_relat_1(C_513) | ~v1_relat_1(A_512))), inference(splitRight, [status(thm)], [c_2862])).
% 8.59/3.20  tff(c_3140, plain, (![A_516, C_517, B_518]: (r2_hidden(k4_tarski('#skF_7'(A_516, k1_xboole_0, C_517), '#skF_8'(A_516, k1_xboole_0, C_517)), B_518) | ~r1_tarski(C_517, B_518) | k5_relat_1(A_516, k1_xboole_0)=C_517 | ~v1_relat_1(C_517) | ~v1_relat_1(A_516))), inference(resolution, [status(thm)], [c_3099, c_8])).
% 8.59/3.20  tff(c_3183, plain, (![C_519, A_520, B_521]: (~r1_tarski(C_519, k2_zfmisc_1(k4_tarski('#skF_7'(A_520, k1_xboole_0, C_519), '#skF_8'(A_520, k1_xboole_0, C_519)), B_521)) | k5_relat_1(A_520, k1_xboole_0)=C_519 | ~v1_relat_1(C_519) | ~v1_relat_1(A_520))), inference(resolution, [status(thm)], [c_3140, c_6])).
% 8.59/3.20  tff(c_3207, plain, (![A_520]: (k5_relat_1(A_520, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_520))), inference(resolution, [status(thm)], [c_2, c_3183])).
% 8.59/3.20  tff(c_3216, plain, (![A_522]: (k5_relat_1(A_522, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_522))), inference(demodulation, [status(thm), theory('equality')], [c_55, c_3207])).
% 8.59/3.20  tff(c_3226, plain, (k5_relat_1(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_55, c_3216])).
% 8.59/3.20  tff(c_2328, plain, (![A_405, B_406, C_407, B_408]: (r2_hidden(k4_tarski('#skF_7'(A_405, B_406, C_407), '#skF_8'(A_405, B_406, C_407)), B_408) | ~r1_tarski(C_407, B_408) | r2_hidden(k4_tarski('#skF_6'(A_405, B_406, C_407), '#skF_5'(A_405, B_406, C_407)), B_406) | k5_relat_1(A_405, B_406)=C_407 | ~v1_relat_1(C_407) | ~v1_relat_1(B_406) | ~v1_relat_1(A_405))), inference(resolution, [status(thm)], [c_162, c_8])).
% 8.59/3.20  tff(c_2651, plain, (![A_465, C_466, A_467, B_468]: (~v1_relat_1(k5_relat_1(A_465, k1_xboole_0)) | ~v1_relat_1(A_465) | ~r1_tarski(C_466, k5_relat_1(A_465, k1_xboole_0)) | r2_hidden(k4_tarski('#skF_6'(A_467, B_468, C_466), '#skF_5'(A_467, B_468, C_466)), B_468) | k5_relat_1(A_467, B_468)=C_466 | ~v1_relat_1(C_466) | ~v1_relat_1(B_468) | ~v1_relat_1(A_467))), inference(resolution, [status(thm)], [c_2328, c_194])).
% 8.59/3.20  tff(c_2687, plain, (![A_465, A_467, B_468]: (~v1_relat_1(k5_relat_1(A_465, k1_xboole_0)) | ~v1_relat_1(A_465) | r2_hidden(k4_tarski('#skF_6'(A_467, B_468, k1_xboole_0), '#skF_5'(A_467, B_468, k1_xboole_0)), B_468) | k5_relat_1(A_467, B_468)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(B_468) | ~v1_relat_1(A_467))), inference(resolution, [status(thm)], [c_2, c_2651])).
% 8.59/3.20  tff(c_2701, plain, (![A_465, A_467, B_468]: (~v1_relat_1(k5_relat_1(A_465, k1_xboole_0)) | ~v1_relat_1(A_465) | r2_hidden(k4_tarski('#skF_6'(A_467, B_468, k1_xboole_0), '#skF_5'(A_467, B_468, k1_xboole_0)), B_468) | k5_relat_1(A_467, B_468)=k1_xboole_0 | ~v1_relat_1(B_468) | ~v1_relat_1(A_467))), inference(demodulation, [status(thm), theory('equality')], [c_55, c_2687])).
% 8.59/3.20  tff(c_2702, plain, (![A_465]: (~v1_relat_1(k5_relat_1(A_465, k1_xboole_0)) | ~v1_relat_1(A_465))), inference(splitLeft, [status(thm)], [c_2701])).
% 8.59/3.20  tff(c_3245, plain, (~v1_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_3226, c_2702])).
% 8.59/3.20  tff(c_3370, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_55, c_55, c_3245])).
% 8.59/3.20  tff(c_3372, plain, (![A_523, B_524]: (r2_hidden(k4_tarski('#skF_6'(A_523, B_524, k1_xboole_0), '#skF_5'(A_523, B_524, k1_xboole_0)), B_524) | k5_relat_1(A_523, B_524)=k1_xboole_0 | ~v1_relat_1(B_524) | ~v1_relat_1(A_523))), inference(splitRight, [status(thm)], [c_2701])).
% 8.59/3.20  tff(c_3456, plain, (![A_535, B_536, B_537]: (r2_hidden(k4_tarski('#skF_6'(A_535, B_536, k1_xboole_0), '#skF_5'(A_535, B_536, k1_xboole_0)), B_537) | ~r1_tarski(B_536, B_537) | k5_relat_1(A_535, B_536)=k1_xboole_0 | ~v1_relat_1(B_536) | ~v1_relat_1(A_535))), inference(resolution, [status(thm)], [c_3372, c_8])).
% 8.59/3.20  tff(c_3550, plain, (![B_541, A_542, B_543]: (~r1_tarski(B_541, k2_zfmisc_1(k4_tarski('#skF_6'(A_542, B_541, k1_xboole_0), '#skF_5'(A_542, B_541, k1_xboole_0)), B_543)) | k5_relat_1(A_542, B_541)=k1_xboole_0 | ~v1_relat_1(B_541) | ~v1_relat_1(A_542))), inference(resolution, [status(thm)], [c_3456, c_6])).
% 8.59/3.20  tff(c_3594, plain, (![A_542]: (k5_relat_1(A_542, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_542))), inference(resolution, [status(thm)], [c_2, c_3550])).
% 8.59/3.20  tff(c_3609, plain, (![A_545]: (k5_relat_1(A_545, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_545))), inference(demodulation, [status(thm), theory('equality')], [c_55, c_3594])).
% 8.59/3.20  tff(c_3619, plain, (k5_relat_1(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_55, c_3609])).
% 8.59/3.20  tff(c_3498, plain, (![B_538, B_539, A_540]: (~v1_relat_1(k5_relat_1(k1_xboole_0, B_538)) | ~v1_relat_1(B_538) | ~r1_tarski(B_539, k5_relat_1(k1_xboole_0, B_538)) | k5_relat_1(A_540, B_539)=k1_xboole_0 | ~v1_relat_1(B_539) | ~v1_relat_1(A_540))), inference(resolution, [status(thm)], [c_3456, c_704])).
% 8.59/3.20  tff(c_3534, plain, (![B_538, A_540]: (~v1_relat_1(k5_relat_1(k1_xboole_0, B_538)) | ~v1_relat_1(B_538) | k5_relat_1(A_540, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_540))), inference(resolution, [status(thm)], [c_2, c_3498])).
% 8.59/3.20  tff(c_3548, plain, (![B_538, A_540]: (~v1_relat_1(k5_relat_1(k1_xboole_0, B_538)) | ~v1_relat_1(B_538) | k5_relat_1(A_540, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_540))), inference(demodulation, [status(thm), theory('equality')], [c_55, c_3534])).
% 8.59/3.20  tff(c_3549, plain, (![B_538]: (~v1_relat_1(k5_relat_1(k1_xboole_0, B_538)) | ~v1_relat_1(B_538))), inference(splitLeft, [status(thm)], [c_3548])).
% 8.59/3.20  tff(c_3625, plain, (~v1_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_3619, c_3549])).
% 8.59/3.20  tff(c_3747, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_55, c_55, c_3625])).
% 8.59/3.20  tff(c_3749, plain, (![A_546]: (k5_relat_1(A_546, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_546))), inference(splitRight, [status(thm)], [c_3548])).
% 8.59/3.20  tff(c_3761, plain, (k5_relat_1('#skF_9', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_36, c_3749])).
% 8.59/3.20  tff(c_3759, plain, (k5_relat_1(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_55, c_3749])).
% 8.59/3.20  tff(c_24, plain, (![A_23, B_75, C_101]: (r2_hidden(k4_tarski('#skF_4'(A_23, B_75, C_101), '#skF_6'(A_23, B_75, C_101)), A_23) | r2_hidden(k4_tarski('#skF_7'(A_23, B_75, C_101), '#skF_8'(A_23, B_75, C_101)), C_101) | k5_relat_1(A_23, B_75)=C_101 | ~v1_relat_1(C_101) | ~v1_relat_1(B_75) | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_60])).
% 8.59/3.20  tff(c_706, plain, (![D_261, E_262, B_263]: (~r2_hidden(k4_tarski(D_261, E_262), k5_relat_1(k1_xboole_0, B_263)) | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_263)) | ~v1_relat_1(B_263))), inference(splitLeft, [status(thm)], [c_703])).
% 8.59/3.20  tff(c_2496, plain, (![B_433, A_434, B_435]: (~v1_relat_1(B_433) | r2_hidden(k4_tarski('#skF_4'(A_434, B_435, k5_relat_1(k1_xboole_0, B_433)), '#skF_6'(A_434, B_435, k5_relat_1(k1_xboole_0, B_433))), A_434) | k5_relat_1(k1_xboole_0, B_433)=k5_relat_1(A_434, B_435) | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_433)) | ~v1_relat_1(B_435) | ~v1_relat_1(A_434))), inference(resolution, [status(thm)], [c_24, c_706])).
% 8.59/3.20  tff(c_2530, plain, (![A_185, B_433, B_435]: (~v1_relat_1(A_185) | ~v1_relat_1(B_433) | k5_relat_1(k5_relat_1(A_185, k1_xboole_0), B_435)=k5_relat_1(k1_xboole_0, B_433) | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_433)) | ~v1_relat_1(B_435) | ~v1_relat_1(k5_relat_1(A_185, k1_xboole_0)))), inference(resolution, [status(thm)], [c_2496, c_194])).
% 8.59/3.20  tff(c_3787, plain, (![A_185, B_435]: (~v1_relat_1(A_185) | ~v1_relat_1(k1_xboole_0) | k5_relat_1(k5_relat_1(A_185, k1_xboole_0), B_435)=k5_relat_1(k1_xboole_0, k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(B_435) | ~v1_relat_1(k5_relat_1(A_185, k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_3759, c_2530])).
% 8.59/3.20  tff(c_4890, plain, (![A_558, B_559]: (~v1_relat_1(A_558) | k5_relat_1(k5_relat_1(A_558, k1_xboole_0), B_559)=k1_xboole_0 | ~v1_relat_1(B_559) | ~v1_relat_1(k5_relat_1(A_558, k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_55, c_3759, c_55, c_3787])).
% 8.59/3.20  tff(c_4894, plain, (![B_559]: (~v1_relat_1('#skF_9') | k5_relat_1(k5_relat_1('#skF_9', k1_xboole_0), B_559)=k1_xboole_0 | ~v1_relat_1(B_559) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_3761, c_4890])).
% 8.59/3.20  tff(c_4903, plain, (![B_560]: (k5_relat_1(k1_xboole_0, B_560)=k1_xboole_0 | ~v1_relat_1(B_560))), inference(demodulation, [status(thm), theory('equality')], [c_55, c_3761, c_36, c_4894])).
% 8.59/3.20  tff(c_4912, plain, (k5_relat_1(k1_xboole_0, '#skF_9')=k1_xboole_0), inference(resolution, [status(thm)], [c_36, c_4903])).
% 8.59/3.20  tff(c_4919, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_4912])).
% 8.59/3.20  tff(c_4920, plain, (![A_252]: (~v1_relat_1(k5_relat_1(A_252, k1_xboole_0)) | ~v1_relat_1(A_252))), inference(splitRight, [status(thm)], [c_703])).
% 8.59/3.20  tff(c_6486, plain, (~v1_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_6391, c_4920])).
% 8.59/3.20  tff(c_6583, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_55, c_55, c_6486])).
% 8.59/3.20  tff(c_6584, plain, (k5_relat_1('#skF_9', k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_34])).
% 8.59/3.20  tff(c_6590, plain, (![A_2]: (~v1_relat_1(A_2))), inference(splitLeft, [status(thm)], [c_49])).
% 8.59/3.20  tff(c_6594, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6590, c_36])).
% 8.59/3.20  tff(c_6595, plain, (v1_relat_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_49])).
% 8.59/3.20  tff(c_7056, plain, (![A_858, B_859, C_860]: (r2_hidden(k4_tarski('#skF_6'(A_858, B_859, C_860), '#skF_5'(A_858, B_859, C_860)), B_859) | r2_hidden(k4_tarski('#skF_7'(A_858, B_859, C_860), '#skF_8'(A_858, B_859, C_860)), C_860) | k5_relat_1(A_858, B_859)=C_860 | ~v1_relat_1(C_860) | ~v1_relat_1(B_859) | ~v1_relat_1(A_858))), inference(cnfTransformation, [status(thm)], [f_60])).
% 8.59/3.20  tff(c_6585, plain, (k5_relat_1(k1_xboole_0, '#skF_9')=k1_xboole_0), inference(splitRight, [status(thm)], [c_34])).
% 8.59/3.20  tff(c_6721, plain, (![D_803, E_804, A_805, B_806]: (r2_hidden(k4_tarski(D_803, '#skF_3'(D_803, E_804, k5_relat_1(A_805, B_806), B_806, A_805)), A_805) | ~r2_hidden(k4_tarski(D_803, E_804), k5_relat_1(A_805, B_806)) | ~v1_relat_1(k5_relat_1(A_805, B_806)) | ~v1_relat_1(B_806) | ~v1_relat_1(A_805))), inference(cnfTransformation, [status(thm)], [f_60])).
% 8.59/3.20  tff(c_6728, plain, (![D_803, E_804]: (r2_hidden(k4_tarski(D_803, '#skF_3'(D_803, E_804, k1_xboole_0, '#skF_9', k1_xboole_0)), k1_xboole_0) | ~r2_hidden(k4_tarski(D_803, E_804), k5_relat_1(k1_xboole_0, '#skF_9')) | ~v1_relat_1(k5_relat_1(k1_xboole_0, '#skF_9')) | ~v1_relat_1('#skF_9') | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_6585, c_6721])).
% 8.59/3.20  tff(c_6733, plain, (![D_807, E_808]: (r2_hidden(k4_tarski(D_807, '#skF_3'(D_807, E_808, k1_xboole_0, '#skF_9', k1_xboole_0)), k1_xboole_0) | ~r2_hidden(k4_tarski(D_807, E_808), k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_6595, c_36, c_6595, c_6585, c_6585, c_6728])).
% 8.59/3.20  tff(c_6737, plain, (![D_807, E_808, B_16]: (r2_hidden(k4_tarski(D_807, '#skF_3'(D_807, E_808, k1_xboole_0, '#skF_9', k1_xboole_0)), B_16) | ~r1_tarski(k1_xboole_0, B_16) | ~v1_relat_1(k1_xboole_0) | ~r2_hidden(k4_tarski(D_807, E_808), k1_xboole_0))), inference(resolution, [status(thm)], [c_6733, c_8])).
% 8.59/3.20  tff(c_6744, plain, (![D_809, E_810, B_811]: (r2_hidden(k4_tarski(D_809, '#skF_3'(D_809, E_810, k1_xboole_0, '#skF_9', k1_xboole_0)), B_811) | ~r2_hidden(k4_tarski(D_809, E_810), k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_6595, c_2, c_6737])).
% 8.59/3.20  tff(c_6754, plain, (![D_809, E_810]: (~r2_hidden(k4_tarski(D_809, E_810), k1_xboole_0))), inference(resolution, [status(thm)], [c_6744, c_6])).
% 8.59/3.20  tff(c_7080, plain, (![A_858, C_860]: (r2_hidden(k4_tarski('#skF_7'(A_858, k1_xboole_0, C_860), '#skF_8'(A_858, k1_xboole_0, C_860)), C_860) | k5_relat_1(A_858, k1_xboole_0)=C_860 | ~v1_relat_1(C_860) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_858))), inference(resolution, [status(thm)], [c_7056, c_6754])).
% 8.59/3.20  tff(c_7128, plain, (![A_861, C_862]: (r2_hidden(k4_tarski('#skF_7'(A_861, k1_xboole_0, C_862), '#skF_8'(A_861, k1_xboole_0, C_862)), C_862) | k5_relat_1(A_861, k1_xboole_0)=C_862 | ~v1_relat_1(C_862) | ~v1_relat_1(A_861))), inference(demodulation, [status(thm), theory('equality')], [c_6595, c_7080])).
% 8.59/3.20  tff(c_7152, plain, (![A_861]: (k5_relat_1(A_861, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_861))), inference(resolution, [status(thm)], [c_7128, c_6754])).
% 8.59/3.20  tff(c_7167, plain, (![A_863]: (k5_relat_1(A_863, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_863))), inference(demodulation, [status(thm), theory('equality')], [c_6595, c_7152])).
% 8.59/3.20  tff(c_7176, plain, (k5_relat_1('#skF_9', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_36, c_7167])).
% 8.59/3.20  tff(c_7182, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6584, c_7176])).
% 8.59/3.20  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.59/3.20  
% 8.59/3.20  Inference rules
% 8.59/3.20  ----------------------
% 8.59/3.20  #Ref     : 0
% 8.59/3.20  #Sup     : 1587
% 8.59/3.20  #Fact    : 0
% 8.59/3.20  #Define  : 0
% 8.59/3.20  #Split   : 10
% 8.59/3.20  #Chain   : 0
% 8.59/3.20  #Close   : 0
% 8.59/3.20  
% 8.59/3.20  Ordering : KBO
% 8.59/3.20  
% 8.59/3.20  Simplification rules
% 8.59/3.20  ----------------------
% 8.59/3.20  #Subsume      : 654
% 8.59/3.20  #Demod        : 964
% 8.59/3.20  #Tautology    : 70
% 8.59/3.20  #SimpNegUnit  : 13
% 8.59/3.20  #BackRed      : 2
% 8.59/3.20  
% 8.59/3.20  #Partial instantiations: 0
% 8.59/3.20  #Strategies tried      : 1
% 8.59/3.20  
% 8.59/3.20  Timing (in seconds)
% 8.59/3.20  ----------------------
% 8.59/3.20  Preprocessing        : 0.29
% 8.59/3.20  Parsing              : 0.15
% 8.59/3.20  CNF conversion       : 0.03
% 8.59/3.20  Main loop            : 2.07
% 8.59/3.20  Inferencing          : 0.47
% 8.59/3.20  Reduction            : 0.30
% 8.59/3.20  Demodulation         : 0.20
% 8.59/3.20  BG Simplification    : 0.05
% 8.59/3.20  Subsumption          : 1.15
% 8.59/3.20  Abstraction          : 0.07
% 8.59/3.20  MUC search           : 0.00
% 8.59/3.20  Cooper               : 0.00
% 8.59/3.20  Total                : 2.41
% 8.59/3.20  Index Insertion      : 0.00
% 8.59/3.20  Index Deletion       : 0.00
% 8.59/3.20  Index Matching       : 0.00
% 8.59/3.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
