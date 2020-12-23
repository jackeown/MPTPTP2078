%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:26 EST 2020

% Result     : Theorem 7.95s
% Output     : CNFRefutation 7.95s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 293 expanded)
%              Number of leaves         :   28 ( 107 expanded)
%              Depth                    :    9
%              Number of atoms          :  125 ( 566 expanded)
%              Number of equality atoms :   27 ( 128 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_8 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_63,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_84,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( r1_tarski(k2_zfmisc_1(A,B),k2_zfmisc_1(C,D))
       => ( k2_zfmisc_1(A,B) = k1_xboole_0
          | ( r1_tarski(A,C)
            & r1_tarski(B,D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_59,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_61,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_55,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_69,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(c_36,plain,(
    ! [A_21] : r1_xboole_0(A_21,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_50,plain,
    ( ~ r1_tarski('#skF_6','#skF_8')
    | ~ r1_tarski('#skF_5','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_104,plain,(
    ~ r1_tarski('#skF_5','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_106,plain,(
    ! [A_36,B_37] : k4_xboole_0(A_36,k4_xboole_0(A_36,B_37)) = k3_xboole_0(A_36,B_37) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_34,plain,(
    ! [A_20] : k4_xboole_0(k1_xboole_0,A_20) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_116,plain,(
    ! [B_37] : k3_xboole_0(k1_xboole_0,B_37) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_106,c_34])).

tff(c_869,plain,(
    ! [A_126,B_127,C_128] :
      ( r2_hidden('#skF_2'(A_126,B_127,C_128),A_126)
      | r2_hidden('#skF_3'(A_126,B_127,C_128),C_128)
      | k3_xboole_0(A_126,B_127) = C_128 ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_191,plain,(
    ! [A_44,B_45,C_46] :
      ( ~ r1_xboole_0(A_44,B_45)
      | ~ r2_hidden(C_46,k3_xboole_0(A_44,B_45)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_198,plain,(
    ! [B_37,C_46] :
      ( ~ r1_xboole_0(k1_xboole_0,B_37)
      | ~ r2_hidden(C_46,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_116,c_191])).

tff(c_200,plain,(
    ! [C_46] : ~ r2_hidden(C_46,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_198])).

tff(c_879,plain,(
    ! [B_127,C_128] :
      ( r2_hidden('#skF_3'(k1_xboole_0,B_127,C_128),C_128)
      | k3_xboole_0(k1_xboole_0,B_127) = C_128 ) ),
    inference(resolution,[status(thm)],[c_869,c_200])).

tff(c_916,plain,(
    ! [B_127,C_128] :
      ( r2_hidden('#skF_3'(k1_xboole_0,B_127,C_128),C_128)
      | k1_xboole_0 = C_128 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_879])).

tff(c_54,plain,(
    r1_tarski(k2_zfmisc_1('#skF_5','#skF_6'),k2_zfmisc_1('#skF_7','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_559,plain,(
    ! [A_102,B_103,C_104,D_105] :
      ( r2_hidden(k4_tarski(A_102,B_103),k2_zfmisc_1(C_104,D_105))
      | ~ r2_hidden(B_103,D_105)
      | ~ r2_hidden(A_102,C_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_6205,plain,(
    ! [A_350,B_349,C_346,D_347,B_348] :
      ( r2_hidden(k4_tarski(A_350,B_348),B_349)
      | ~ r1_tarski(k2_zfmisc_1(C_346,D_347),B_349)
      | ~ r2_hidden(B_348,D_347)
      | ~ r2_hidden(A_350,C_346) ) ),
    inference(resolution,[status(thm)],[c_559,c_2])).

tff(c_6303,plain,(
    ! [A_354,B_355] :
      ( r2_hidden(k4_tarski(A_354,B_355),k2_zfmisc_1('#skF_7','#skF_8'))
      | ~ r2_hidden(B_355,'#skF_6')
      | ~ r2_hidden(A_354,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_54,c_6205])).

tff(c_42,plain,(
    ! [A_22,C_24,B_23,D_25] :
      ( r2_hidden(A_22,C_24)
      | ~ r2_hidden(k4_tarski(A_22,B_23),k2_zfmisc_1(C_24,D_25)) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_6316,plain,(
    ! [A_354,B_355] :
      ( r2_hidden(A_354,'#skF_7')
      | ~ r2_hidden(B_355,'#skF_6')
      | ~ r2_hidden(A_354,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_6303,c_42])).

tff(c_6320,plain,(
    ! [B_356] : ~ r2_hidden(B_356,'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_6316])).

tff(c_6406,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_916,c_6320])).

tff(c_46,plain,(
    ! [A_26] : k2_zfmisc_1(A_26,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_6461,plain,(
    ! [A_26] : k2_zfmisc_1(A_26,'#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6406,c_6406,c_46])).

tff(c_52,plain,(
    k2_zfmisc_1('#skF_5','#skF_6') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_6463,plain,(
    k2_zfmisc_1('#skF_5','#skF_6') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6406,c_52])).

tff(c_7139,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6461,c_6463])).

tff(c_7141,plain,(
    ! [A_371] :
      ( r2_hidden(A_371,'#skF_7')
      | ~ r2_hidden(A_371,'#skF_5') ) ),
    inference(splitRight,[status(thm)],[c_6316])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_7172,plain,(
    ! [A_372] :
      ( r1_tarski(A_372,'#skF_7')
      | ~ r2_hidden('#skF_1'(A_372,'#skF_7'),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_7141,c_4])).

tff(c_7188,plain,(
    r1_tarski('#skF_5','#skF_7') ),
    inference(resolution,[status(thm)],[c_6,c_7172])).

tff(c_7195,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_104,c_104,c_7188])).

tff(c_7206,plain,(
    ! [B_376] : ~ r1_xboole_0(k1_xboole_0,B_376) ),
    inference(splitRight,[status(thm)],[c_198])).

tff(c_7211,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_36,c_7206])).

tff(c_7212,plain,(
    ~ r1_tarski('#skF_6','#skF_8') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_7214,plain,(
    ! [A_377,B_378] : k4_xboole_0(A_377,k4_xboole_0(A_377,B_378)) = k3_xboole_0(A_377,B_378) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_7224,plain,(
    ! [B_378] : k3_xboole_0(k1_xboole_0,B_378) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_7214,c_34])).

tff(c_7831,plain,(
    ! [A_476,B_477,C_478] :
      ( r2_hidden('#skF_2'(A_476,B_477,C_478),A_476)
      | r2_hidden('#skF_3'(A_476,B_477,C_478),C_478)
      | k3_xboole_0(A_476,B_477) = C_478 ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_7285,plain,(
    ! [A_381,B_382,C_383] :
      ( ~ r1_xboole_0(A_381,B_382)
      | ~ r2_hidden(C_383,k3_xboole_0(A_381,B_382)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_7288,plain,(
    ! [B_378,C_383] :
      ( ~ r1_xboole_0(k1_xboole_0,B_378)
      | ~ r2_hidden(C_383,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7224,c_7285])).

tff(c_7289,plain,(
    ! [C_383] : ~ r2_hidden(C_383,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_7288])).

tff(c_7853,plain,(
    ! [B_477,C_478] :
      ( r2_hidden('#skF_3'(k1_xboole_0,B_477,C_478),C_478)
      | k3_xboole_0(k1_xboole_0,B_477) = C_478 ) ),
    inference(resolution,[status(thm)],[c_7831,c_7289])).

tff(c_7885,plain,(
    ! [B_477,C_478] :
      ( r2_hidden('#skF_3'(k1_xboole_0,B_477,C_478),C_478)
      | k1_xboole_0 = C_478 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7224,c_7853])).

tff(c_7667,plain,(
    ! [A_446,B_447,C_448,D_449] :
      ( r2_hidden(k4_tarski(A_446,B_447),k2_zfmisc_1(C_448,D_449))
      | ~ r2_hidden(B_447,D_449)
      | ~ r2_hidden(A_446,C_448) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_11670,plain,(
    ! [B_642,A_639,D_641,B_640,C_643] :
      ( r2_hidden(k4_tarski(A_639,B_640),B_642)
      | ~ r1_tarski(k2_zfmisc_1(C_643,D_641),B_642)
      | ~ r2_hidden(B_640,D_641)
      | ~ r2_hidden(A_639,C_643) ) ),
    inference(resolution,[status(thm)],[c_7667,c_2])).

tff(c_11686,plain,(
    ! [A_644,B_645] :
      ( r2_hidden(k4_tarski(A_644,B_645),k2_zfmisc_1('#skF_7','#skF_8'))
      | ~ r2_hidden(B_645,'#skF_6')
      | ~ r2_hidden(A_644,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_54,c_11670])).

tff(c_40,plain,(
    ! [B_23,D_25,A_22,C_24] :
      ( r2_hidden(B_23,D_25)
      | ~ r2_hidden(k4_tarski(A_22,B_23),k2_zfmisc_1(C_24,D_25)) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_11700,plain,(
    ! [B_645,A_644] :
      ( r2_hidden(B_645,'#skF_8')
      | ~ r2_hidden(B_645,'#skF_6')
      | ~ r2_hidden(A_644,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_11686,c_40])).

tff(c_12004,plain,(
    ! [A_652] : ~ r2_hidden(A_652,'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_11700])).

tff(c_12076,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_7885,c_12004])).

tff(c_48,plain,(
    ! [B_27] : k2_zfmisc_1(k1_xboole_0,B_27) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_12128,plain,(
    ! [B_27] : k2_zfmisc_1('#skF_5',B_27) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12076,c_12076,c_48])).

tff(c_12129,plain,(
    k2_zfmisc_1('#skF_5','#skF_6') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12076,c_52])).

tff(c_12654,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12128,c_12129])).

tff(c_12656,plain,(
    ! [B_665] :
      ( r2_hidden(B_665,'#skF_8')
      | ~ r2_hidden(B_665,'#skF_6') ) ),
    inference(splitRight,[status(thm)],[c_11700])).

tff(c_13848,plain,(
    ! [B_696] :
      ( r2_hidden('#skF_1'('#skF_6',B_696),'#skF_8')
      | r1_tarski('#skF_6',B_696) ) ),
    inference(resolution,[status(thm)],[c_6,c_12656])).

tff(c_13857,plain,(
    r1_tarski('#skF_6','#skF_8') ),
    inference(resolution,[status(thm)],[c_13848,c_4])).

tff(c_13863,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_7212,c_7212,c_13857])).

tff(c_13871,plain,(
    ! [B_699] : ~ r1_xboole_0(k1_xboole_0,B_699) ),
    inference(splitRight,[status(thm)],[c_7288])).

tff(c_13876,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_36,c_13871])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:56:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.95/2.75  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.95/2.76  
% 7.95/2.76  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.95/2.76  %$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_8 > #skF_3 > #skF_1 > #skF_4
% 7.95/2.76  
% 7.95/2.76  %Foreground sorts:
% 7.95/2.76  
% 7.95/2.76  
% 7.95/2.76  %Background operators:
% 7.95/2.76  
% 7.95/2.76  
% 7.95/2.76  %Foreground operators:
% 7.95/2.76  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.95/2.76  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.95/2.76  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.95/2.76  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 7.95/2.76  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.95/2.76  tff('#skF_7', type, '#skF_7': $i).
% 7.95/2.76  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.95/2.76  tff('#skF_5', type, '#skF_5': $i).
% 7.95/2.76  tff('#skF_6', type, '#skF_6': $i).
% 7.95/2.76  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 7.95/2.76  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 7.95/2.76  tff('#skF_8', type, '#skF_8': $i).
% 7.95/2.76  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.95/2.76  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.95/2.76  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 7.95/2.76  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.95/2.76  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.95/2.76  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 7.95/2.76  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 7.95/2.76  
% 7.95/2.77  tff(f_63, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 7.95/2.77  tff(f_84, negated_conjecture, ~(![A, B, C, D]: (r1_tarski(k2_zfmisc_1(A, B), k2_zfmisc_1(C, D)) => ((k2_zfmisc_1(A, B) = k1_xboole_0) | (r1_tarski(A, C) & r1_tarski(B, D))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t138_zfmisc_1)).
% 7.95/2.77  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 7.95/2.77  tff(f_59, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 7.95/2.77  tff(f_61, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 7.95/2.77  tff(f_41, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 7.95/2.77  tff(f_55, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 7.95/2.77  tff(f_69, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 7.95/2.77  tff(f_75, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 7.95/2.77  tff(c_36, plain, (![A_21]: (r1_xboole_0(A_21, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_63])).
% 7.95/2.77  tff(c_50, plain, (~r1_tarski('#skF_6', '#skF_8') | ~r1_tarski('#skF_5', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_84])).
% 7.95/2.77  tff(c_104, plain, (~r1_tarski('#skF_5', '#skF_7')), inference(splitLeft, [status(thm)], [c_50])).
% 7.95/2.77  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.95/2.77  tff(c_106, plain, (![A_36, B_37]: (k4_xboole_0(A_36, k4_xboole_0(A_36, B_37))=k3_xboole_0(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_59])).
% 7.95/2.77  tff(c_34, plain, (![A_20]: (k4_xboole_0(k1_xboole_0, A_20)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_61])).
% 7.95/2.77  tff(c_116, plain, (![B_37]: (k3_xboole_0(k1_xboole_0, B_37)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_106, c_34])).
% 7.95/2.77  tff(c_869, plain, (![A_126, B_127, C_128]: (r2_hidden('#skF_2'(A_126, B_127, C_128), A_126) | r2_hidden('#skF_3'(A_126, B_127, C_128), C_128) | k3_xboole_0(A_126, B_127)=C_128)), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.95/2.77  tff(c_191, plain, (![A_44, B_45, C_46]: (~r1_xboole_0(A_44, B_45) | ~r2_hidden(C_46, k3_xboole_0(A_44, B_45)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 7.95/2.77  tff(c_198, plain, (![B_37, C_46]: (~r1_xboole_0(k1_xboole_0, B_37) | ~r2_hidden(C_46, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_116, c_191])).
% 7.95/2.77  tff(c_200, plain, (![C_46]: (~r2_hidden(C_46, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_198])).
% 7.95/2.77  tff(c_879, plain, (![B_127, C_128]: (r2_hidden('#skF_3'(k1_xboole_0, B_127, C_128), C_128) | k3_xboole_0(k1_xboole_0, B_127)=C_128)), inference(resolution, [status(thm)], [c_869, c_200])).
% 7.95/2.77  tff(c_916, plain, (![B_127, C_128]: (r2_hidden('#skF_3'(k1_xboole_0, B_127, C_128), C_128) | k1_xboole_0=C_128)), inference(demodulation, [status(thm), theory('equality')], [c_116, c_879])).
% 7.95/2.77  tff(c_54, plain, (r1_tarski(k2_zfmisc_1('#skF_5', '#skF_6'), k2_zfmisc_1('#skF_7', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_84])).
% 7.95/2.77  tff(c_559, plain, (![A_102, B_103, C_104, D_105]: (r2_hidden(k4_tarski(A_102, B_103), k2_zfmisc_1(C_104, D_105)) | ~r2_hidden(B_103, D_105) | ~r2_hidden(A_102, C_104))), inference(cnfTransformation, [status(thm)], [f_69])).
% 7.95/2.77  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.95/2.77  tff(c_6205, plain, (![A_350, B_349, C_346, D_347, B_348]: (r2_hidden(k4_tarski(A_350, B_348), B_349) | ~r1_tarski(k2_zfmisc_1(C_346, D_347), B_349) | ~r2_hidden(B_348, D_347) | ~r2_hidden(A_350, C_346))), inference(resolution, [status(thm)], [c_559, c_2])).
% 7.95/2.77  tff(c_6303, plain, (![A_354, B_355]: (r2_hidden(k4_tarski(A_354, B_355), k2_zfmisc_1('#skF_7', '#skF_8')) | ~r2_hidden(B_355, '#skF_6') | ~r2_hidden(A_354, '#skF_5'))), inference(resolution, [status(thm)], [c_54, c_6205])).
% 7.95/2.77  tff(c_42, plain, (![A_22, C_24, B_23, D_25]: (r2_hidden(A_22, C_24) | ~r2_hidden(k4_tarski(A_22, B_23), k2_zfmisc_1(C_24, D_25)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 7.95/2.77  tff(c_6316, plain, (![A_354, B_355]: (r2_hidden(A_354, '#skF_7') | ~r2_hidden(B_355, '#skF_6') | ~r2_hidden(A_354, '#skF_5'))), inference(resolution, [status(thm)], [c_6303, c_42])).
% 7.95/2.77  tff(c_6320, plain, (![B_356]: (~r2_hidden(B_356, '#skF_6'))), inference(splitLeft, [status(thm)], [c_6316])).
% 7.95/2.77  tff(c_6406, plain, (k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_916, c_6320])).
% 7.95/2.77  tff(c_46, plain, (![A_26]: (k2_zfmisc_1(A_26, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_75])).
% 7.95/2.77  tff(c_6461, plain, (![A_26]: (k2_zfmisc_1(A_26, '#skF_6')='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_6406, c_6406, c_46])).
% 7.95/2.77  tff(c_52, plain, (k2_zfmisc_1('#skF_5', '#skF_6')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_84])).
% 7.95/2.77  tff(c_6463, plain, (k2_zfmisc_1('#skF_5', '#skF_6')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_6406, c_52])).
% 7.95/2.77  tff(c_7139, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6461, c_6463])).
% 7.95/2.77  tff(c_7141, plain, (![A_371]: (r2_hidden(A_371, '#skF_7') | ~r2_hidden(A_371, '#skF_5'))), inference(splitRight, [status(thm)], [c_6316])).
% 7.95/2.77  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.95/2.77  tff(c_7172, plain, (![A_372]: (r1_tarski(A_372, '#skF_7') | ~r2_hidden('#skF_1'(A_372, '#skF_7'), '#skF_5'))), inference(resolution, [status(thm)], [c_7141, c_4])).
% 7.95/2.77  tff(c_7188, plain, (r1_tarski('#skF_5', '#skF_7')), inference(resolution, [status(thm)], [c_6, c_7172])).
% 7.95/2.77  tff(c_7195, plain, $false, inference(negUnitSimplification, [status(thm)], [c_104, c_104, c_7188])).
% 7.95/2.77  tff(c_7206, plain, (![B_376]: (~r1_xboole_0(k1_xboole_0, B_376))), inference(splitRight, [status(thm)], [c_198])).
% 7.95/2.77  tff(c_7211, plain, $false, inference(resolution, [status(thm)], [c_36, c_7206])).
% 7.95/2.77  tff(c_7212, plain, (~r1_tarski('#skF_6', '#skF_8')), inference(splitRight, [status(thm)], [c_50])).
% 7.95/2.77  tff(c_7214, plain, (![A_377, B_378]: (k4_xboole_0(A_377, k4_xboole_0(A_377, B_378))=k3_xboole_0(A_377, B_378))), inference(cnfTransformation, [status(thm)], [f_59])).
% 7.95/2.77  tff(c_7224, plain, (![B_378]: (k3_xboole_0(k1_xboole_0, B_378)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_7214, c_34])).
% 7.95/2.77  tff(c_7831, plain, (![A_476, B_477, C_478]: (r2_hidden('#skF_2'(A_476, B_477, C_478), A_476) | r2_hidden('#skF_3'(A_476, B_477, C_478), C_478) | k3_xboole_0(A_476, B_477)=C_478)), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.95/2.77  tff(c_7285, plain, (![A_381, B_382, C_383]: (~r1_xboole_0(A_381, B_382) | ~r2_hidden(C_383, k3_xboole_0(A_381, B_382)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 7.95/2.77  tff(c_7288, plain, (![B_378, C_383]: (~r1_xboole_0(k1_xboole_0, B_378) | ~r2_hidden(C_383, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_7224, c_7285])).
% 7.95/2.77  tff(c_7289, plain, (![C_383]: (~r2_hidden(C_383, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_7288])).
% 7.95/2.77  tff(c_7853, plain, (![B_477, C_478]: (r2_hidden('#skF_3'(k1_xboole_0, B_477, C_478), C_478) | k3_xboole_0(k1_xboole_0, B_477)=C_478)), inference(resolution, [status(thm)], [c_7831, c_7289])).
% 7.95/2.77  tff(c_7885, plain, (![B_477, C_478]: (r2_hidden('#skF_3'(k1_xboole_0, B_477, C_478), C_478) | k1_xboole_0=C_478)), inference(demodulation, [status(thm), theory('equality')], [c_7224, c_7853])).
% 7.95/2.77  tff(c_7667, plain, (![A_446, B_447, C_448, D_449]: (r2_hidden(k4_tarski(A_446, B_447), k2_zfmisc_1(C_448, D_449)) | ~r2_hidden(B_447, D_449) | ~r2_hidden(A_446, C_448))), inference(cnfTransformation, [status(thm)], [f_69])).
% 7.95/2.77  tff(c_11670, plain, (![B_642, A_639, D_641, B_640, C_643]: (r2_hidden(k4_tarski(A_639, B_640), B_642) | ~r1_tarski(k2_zfmisc_1(C_643, D_641), B_642) | ~r2_hidden(B_640, D_641) | ~r2_hidden(A_639, C_643))), inference(resolution, [status(thm)], [c_7667, c_2])).
% 7.95/2.77  tff(c_11686, plain, (![A_644, B_645]: (r2_hidden(k4_tarski(A_644, B_645), k2_zfmisc_1('#skF_7', '#skF_8')) | ~r2_hidden(B_645, '#skF_6') | ~r2_hidden(A_644, '#skF_5'))), inference(resolution, [status(thm)], [c_54, c_11670])).
% 7.95/2.77  tff(c_40, plain, (![B_23, D_25, A_22, C_24]: (r2_hidden(B_23, D_25) | ~r2_hidden(k4_tarski(A_22, B_23), k2_zfmisc_1(C_24, D_25)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 7.95/2.77  tff(c_11700, plain, (![B_645, A_644]: (r2_hidden(B_645, '#skF_8') | ~r2_hidden(B_645, '#skF_6') | ~r2_hidden(A_644, '#skF_5'))), inference(resolution, [status(thm)], [c_11686, c_40])).
% 7.95/2.77  tff(c_12004, plain, (![A_652]: (~r2_hidden(A_652, '#skF_5'))), inference(splitLeft, [status(thm)], [c_11700])).
% 7.95/2.77  tff(c_12076, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_7885, c_12004])).
% 7.95/2.77  tff(c_48, plain, (![B_27]: (k2_zfmisc_1(k1_xboole_0, B_27)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_75])).
% 7.95/2.77  tff(c_12128, plain, (![B_27]: (k2_zfmisc_1('#skF_5', B_27)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_12076, c_12076, c_48])).
% 7.95/2.77  tff(c_12129, plain, (k2_zfmisc_1('#skF_5', '#skF_6')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_12076, c_52])).
% 7.95/2.77  tff(c_12654, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12128, c_12129])).
% 7.95/2.77  tff(c_12656, plain, (![B_665]: (r2_hidden(B_665, '#skF_8') | ~r2_hidden(B_665, '#skF_6'))), inference(splitRight, [status(thm)], [c_11700])).
% 7.95/2.77  tff(c_13848, plain, (![B_696]: (r2_hidden('#skF_1'('#skF_6', B_696), '#skF_8') | r1_tarski('#skF_6', B_696))), inference(resolution, [status(thm)], [c_6, c_12656])).
% 7.95/2.77  tff(c_13857, plain, (r1_tarski('#skF_6', '#skF_8')), inference(resolution, [status(thm)], [c_13848, c_4])).
% 7.95/2.77  tff(c_13863, plain, $false, inference(negUnitSimplification, [status(thm)], [c_7212, c_7212, c_13857])).
% 7.95/2.77  tff(c_13871, plain, (![B_699]: (~r1_xboole_0(k1_xboole_0, B_699))), inference(splitRight, [status(thm)], [c_7288])).
% 7.95/2.77  tff(c_13876, plain, $false, inference(resolution, [status(thm)], [c_36, c_13871])).
% 7.95/2.77  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.95/2.77  
% 7.95/2.77  Inference rules
% 7.95/2.77  ----------------------
% 7.95/2.77  #Ref     : 0
% 7.95/2.77  #Sup     : 3272
% 7.95/2.77  #Fact    : 0
% 7.95/2.77  #Define  : 0
% 7.95/2.77  #Split   : 11
% 7.95/2.77  #Chain   : 0
% 7.95/2.77  #Close   : 0
% 7.95/2.77  
% 7.95/2.77  Ordering : KBO
% 7.95/2.77  
% 7.95/2.77  Simplification rules
% 7.95/2.77  ----------------------
% 7.95/2.77  #Subsume      : 1133
% 7.95/2.77  #Demod        : 1667
% 7.95/2.77  #Tautology    : 1074
% 7.95/2.77  #SimpNegUnit  : 81
% 7.95/2.77  #BackRed      : 258
% 7.95/2.77  
% 7.95/2.77  #Partial instantiations: 0
% 7.95/2.77  #Strategies tried      : 1
% 7.95/2.77  
% 7.95/2.77  Timing (in seconds)
% 7.95/2.77  ----------------------
% 7.95/2.78  Preprocessing        : 0.31
% 7.95/2.78  Parsing              : 0.17
% 7.95/2.78  CNF conversion       : 0.02
% 7.95/2.78  Main loop            : 1.70
% 7.95/2.78  Inferencing          : 0.54
% 7.95/2.78  Reduction            : 0.47
% 7.95/2.78  Demodulation         : 0.33
% 7.95/2.78  BG Simplification    : 0.06
% 7.95/2.78  Subsumption          : 0.49
% 7.95/2.78  Abstraction          : 0.07
% 7.95/2.78  MUC search           : 0.00
% 7.95/2.78  Cooper               : 0.00
% 7.95/2.78  Total                : 2.04
% 7.95/2.78  Index Insertion      : 0.00
% 7.95/2.78  Index Deletion       : 0.00
% 7.95/2.78  Index Matching       : 0.00
% 7.95/2.78  BG Taut test         : 0.00
%------------------------------------------------------------------------------
