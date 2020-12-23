%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:26 EST 2020

% Result     : Theorem 5.56s
% Output     : CNFRefutation 5.65s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 214 expanded)
%              Number of leaves         :   33 (  86 expanded)
%              Depth                    :    9
%              Number of atoms          :  119 ( 439 expanded)
%              Number of equality atoms :   22 (  60 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_11 > #skF_6 > #skF_9 > #skF_4 > #skF_10 > #skF_8 > #skF_13 > #skF_5 > #skF_7 > #skF_3 > #skF_2 > #skF_1 > #skF_12

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

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i * $i * $i ) > $i )).

tff('#skF_13',type,(
    '#skF_13': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff(f_87,negated_conjecture,(
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

tff(f_54,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_78,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( C = k2_zfmisc_1(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ? [E,F] :
              ( r2_hidden(E,A)
              & r2_hidden(F,B)
              & D = k4_tarski(E,F) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_zfmisc_1)).

tff(f_60,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_56,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_58,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(c_50,plain,
    ( ~ r1_tarski('#skF_11','#skF_13')
    | ~ r1_tarski('#skF_10','#skF_12') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_66,plain,(
    ~ r1_tarski('#skF_10','#skF_12') ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_12,plain,(
    ! [A_11] :
      ( r2_hidden('#skF_3'(A_11),A_11)
      | k1_xboole_0 = A_11 ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_54,plain,(
    r1_tarski(k2_zfmisc_1('#skF_10','#skF_11'),k2_zfmisc_1('#skF_12','#skF_13')) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_290,plain,(
    ! [A_101,B_102,C_103,D_104] :
      ( r2_hidden(k4_tarski(A_101,B_102),k2_zfmisc_1(C_103,D_104))
      | ~ r2_hidden(B_102,D_104)
      | ~ r2_hidden(A_101,C_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1952,plain,(
    ! [A_252,D_254,C_256,B_255,B_253] :
      ( r2_hidden(k4_tarski(A_252,B_253),B_255)
      | ~ r1_tarski(k2_zfmisc_1(C_256,D_254),B_255)
      | ~ r2_hidden(B_253,D_254)
      | ~ r2_hidden(A_252,C_256) ) ),
    inference(resolution,[status(thm)],[c_290,c_2])).

tff(c_2299,plain,(
    ! [A_266,B_267] :
      ( r2_hidden(k4_tarski(A_266,B_267),k2_zfmisc_1('#skF_12','#skF_13'))
      | ~ r2_hidden(B_267,'#skF_11')
      | ~ r2_hidden(A_266,'#skF_10') ) ),
    inference(resolution,[status(thm)],[c_54,c_1952])).

tff(c_48,plain,(
    ! [A_51,C_53,B_52,D_54] :
      ( r2_hidden(A_51,C_53)
      | ~ r2_hidden(k4_tarski(A_51,B_52),k2_zfmisc_1(C_53,D_54)) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_2326,plain,(
    ! [A_266,B_267] :
      ( r2_hidden(A_266,'#skF_12')
      | ~ r2_hidden(B_267,'#skF_11')
      | ~ r2_hidden(A_266,'#skF_10') ) ),
    inference(resolution,[status(thm)],[c_2299,c_48])).

tff(c_2330,plain,(
    ! [B_268] : ~ r2_hidden(B_268,'#skF_11') ),
    inference(splitLeft,[status(thm)],[c_2326])).

tff(c_2399,plain,(
    k1_xboole_0 = '#skF_11' ),
    inference(resolution,[status(thm)],[c_12,c_2330])).

tff(c_385,plain,(
    ! [A_115,B_116,D_117] :
      ( r2_hidden('#skF_9'(A_115,B_116,k2_zfmisc_1(A_115,B_116),D_117),B_116)
      | ~ r2_hidden(D_117,k2_zfmisc_1(A_115,B_116)) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_18,plain,(
    ! [A_16] : r1_xboole_0(A_16,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_68,plain,(
    ! [A_60,B_61,C_62] :
      ( ~ r1_xboole_0(A_60,B_61)
      | ~ r2_hidden(C_62,k3_xboole_0(A_60,B_61)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_86,plain,(
    ! [A_66,B_67] :
      ( ~ r1_xboole_0(A_66,B_67)
      | k3_xboole_0(A_66,B_67) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_12,c_68])).

tff(c_91,plain,(
    ! [A_68] : k3_xboole_0(A_68,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_18,c_86])).

tff(c_10,plain,(
    ! [A_6,B_7,C_10] :
      ( ~ r1_xboole_0(A_6,B_7)
      | ~ r2_hidden(C_10,k3_xboole_0(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_96,plain,(
    ! [A_68,C_10] :
      ( ~ r1_xboole_0(A_68,k1_xboole_0)
      | ~ r2_hidden(C_10,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_91,c_10])).

tff(c_101,plain,(
    ! [C_10] : ~ r2_hidden(C_10,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_96])).

tff(c_399,plain,(
    ! [D_118,A_119] : ~ r2_hidden(D_118,k2_zfmisc_1(A_119,k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_385,c_101])).

tff(c_434,plain,(
    ! [A_119] : k2_zfmisc_1(A_119,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12,c_399])).

tff(c_2426,plain,(
    ! [A_119] : k2_zfmisc_1(A_119,'#skF_11') = '#skF_11' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2399,c_2399,c_434])).

tff(c_52,plain,(
    k2_zfmisc_1('#skF_10','#skF_11') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_2438,plain,(
    k2_zfmisc_1('#skF_10','#skF_11') != '#skF_11' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2399,c_52])).

tff(c_2703,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2426,c_2438])).

tff(c_2705,plain,(
    ! [A_283] :
      ( r2_hidden(A_283,'#skF_12')
      | ~ r2_hidden(A_283,'#skF_10') ) ),
    inference(splitRight,[status(thm)],[c_2326])).

tff(c_3709,plain,(
    ! [B_316] :
      ( r2_hidden('#skF_1'('#skF_10',B_316),'#skF_12')
      | r1_tarski('#skF_10',B_316) ) ),
    inference(resolution,[status(thm)],[c_6,c_2705])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_3718,plain,(
    r1_tarski('#skF_10','#skF_12') ),
    inference(resolution,[status(thm)],[c_3709,c_4])).

tff(c_3724,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_66,c_3718])).

tff(c_3725,plain,(
    ~ r1_tarski('#skF_11','#skF_13') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_3983,plain,(
    ! [A_361,B_362,C_363,D_364] :
      ( r2_hidden(k4_tarski(A_361,B_362),k2_zfmisc_1(C_363,D_364))
      | ~ r2_hidden(B_362,D_364)
      | ~ r2_hidden(A_361,C_363) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_5408,plain,(
    ! [A_507,B_504,D_503,C_505,B_506] :
      ( r2_hidden(k4_tarski(A_507,B_504),B_506)
      | ~ r1_tarski(k2_zfmisc_1(C_505,D_503),B_506)
      | ~ r2_hidden(B_504,D_503)
      | ~ r2_hidden(A_507,C_505) ) ),
    inference(resolution,[status(thm)],[c_3983,c_2])).

tff(c_5502,plain,(
    ! [A_514,B_515] :
      ( r2_hidden(k4_tarski(A_514,B_515),k2_zfmisc_1('#skF_12','#skF_13'))
      | ~ r2_hidden(B_515,'#skF_11')
      | ~ r2_hidden(A_514,'#skF_10') ) ),
    inference(resolution,[status(thm)],[c_54,c_5408])).

tff(c_46,plain,(
    ! [B_52,D_54,A_51,C_53] :
      ( r2_hidden(B_52,D_54)
      | ~ r2_hidden(k4_tarski(A_51,B_52),k2_zfmisc_1(C_53,D_54)) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_5529,plain,(
    ! [B_515,A_514] :
      ( r2_hidden(B_515,'#skF_13')
      | ~ r2_hidden(B_515,'#skF_11')
      | ~ r2_hidden(A_514,'#skF_10') ) ),
    inference(resolution,[status(thm)],[c_5502,c_46])).

tff(c_5533,plain,(
    ! [A_516] : ~ r2_hidden(A_516,'#skF_10') ),
    inference(splitLeft,[status(thm)],[c_5529])).

tff(c_5602,plain,(
    k1_xboole_0 = '#skF_10' ),
    inference(resolution,[status(thm)],[c_12,c_5533])).

tff(c_4130,plain,(
    ! [A_378,B_379,D_380] :
      ( r2_hidden('#skF_8'(A_378,B_379,k2_zfmisc_1(A_378,B_379),D_380),A_378)
      | ~ r2_hidden(D_380,k2_zfmisc_1(A_378,B_379)) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_14,plain,(
    ! [A_13] : k4_xboole_0(A_13,k1_xboole_0) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_3727,plain,(
    ! [A_317,B_318] : k4_xboole_0(A_317,k4_xboole_0(A_317,B_318)) = k3_xboole_0(A_317,B_318) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_3746,plain,(
    ! [A_321] : k4_xboole_0(A_321,A_321) = k3_xboole_0(A_321,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_3727])).

tff(c_3756,plain,(
    k3_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_3746,c_14])).

tff(c_3778,plain,(
    ! [A_325,B_326,C_327] :
      ( ~ r1_xboole_0(A_325,B_326)
      | ~ r2_hidden(C_327,k3_xboole_0(A_325,B_326)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_3785,plain,(
    ! [C_327] :
      ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
      | ~ r2_hidden(C_327,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3756,c_3778])).

tff(c_3792,plain,(
    ! [C_327] : ~ r2_hidden(C_327,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_3785])).

tff(c_4148,plain,(
    ! [D_381,B_382] : ~ r2_hidden(D_381,k2_zfmisc_1(k1_xboole_0,B_382)) ),
    inference(resolution,[status(thm)],[c_4130,c_3792])).

tff(c_4186,plain,(
    ! [B_382] : k2_zfmisc_1(k1_xboole_0,B_382) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12,c_4148])).

tff(c_5624,plain,(
    ! [B_382] : k2_zfmisc_1('#skF_10',B_382) = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5602,c_5602,c_4186])).

tff(c_5637,plain,(
    k2_zfmisc_1('#skF_10','#skF_11') != '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5602,c_52])).

tff(c_5848,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5624,c_5637])).

tff(c_6015,plain,(
    ! [B_535] :
      ( r2_hidden(B_535,'#skF_13')
      | ~ r2_hidden(B_535,'#skF_11') ) ),
    inference(splitRight,[status(thm)],[c_5529])).

tff(c_6944,plain,(
    ! [B_566] :
      ( r2_hidden('#skF_1'('#skF_11',B_566),'#skF_13')
      | r1_tarski('#skF_11',B_566) ) ),
    inference(resolution,[status(thm)],[c_6,c_6015])).

tff(c_6953,plain,(
    r1_tarski('#skF_11','#skF_13') ),
    inference(resolution,[status(thm)],[c_6944,c_4])).

tff(c_6959,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3725,c_3725,c_6953])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 19:02:57 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.56/2.09  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.56/2.10  
% 5.56/2.10  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.56/2.10  %$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_11 > #skF_6 > #skF_9 > #skF_4 > #skF_10 > #skF_8 > #skF_13 > #skF_5 > #skF_7 > #skF_3 > #skF_2 > #skF_1 > #skF_12
% 5.56/2.10  
% 5.56/2.10  %Foreground sorts:
% 5.56/2.10  
% 5.56/2.10  
% 5.56/2.10  %Background operators:
% 5.56/2.10  
% 5.56/2.10  
% 5.56/2.10  %Foreground operators:
% 5.56/2.10  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.56/2.10  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.56/2.10  tff('#skF_11', type, '#skF_11': $i).
% 5.56/2.10  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 5.56/2.10  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.56/2.10  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 5.56/2.10  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.56/2.10  tff('#skF_9', type, '#skF_9': ($i * $i * $i * $i) > $i).
% 5.56/2.10  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 5.56/2.10  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.56/2.10  tff('#skF_10', type, '#skF_10': $i).
% 5.56/2.10  tff('#skF_8', type, '#skF_8': ($i * $i * $i * $i) > $i).
% 5.56/2.10  tff('#skF_13', type, '#skF_13': $i).
% 5.56/2.10  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 5.56/2.10  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 5.56/2.10  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 5.56/2.10  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.56/2.10  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.56/2.10  tff('#skF_3', type, '#skF_3': $i > $i).
% 5.56/2.10  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.56/2.10  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 5.56/2.10  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.56/2.10  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.56/2.10  tff('#skF_12', type, '#skF_12': $i).
% 5.56/2.10  
% 5.65/2.11  tff(f_87, negated_conjecture, ~(![A, B, C, D]: (r1_tarski(k2_zfmisc_1(A, B), k2_zfmisc_1(C, D)) => ((k2_zfmisc_1(A, B) = k1_xboole_0) | (r1_tarski(A, C) & r1_tarski(B, D))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t138_zfmisc_1)).
% 5.65/2.11  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 5.65/2.11  tff(f_54, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 5.65/2.11  tff(f_78, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 5.65/2.11  tff(f_72, axiom, (![A, B, C]: ((C = k2_zfmisc_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E, F]: ((r2_hidden(E, A) & r2_hidden(F, B)) & (D = k4_tarski(E, F)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_zfmisc_1)).
% 5.65/2.11  tff(f_60, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 5.65/2.11  tff(f_46, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 5.65/2.11  tff(f_56, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 5.65/2.11  tff(f_58, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 5.65/2.11  tff(c_50, plain, (~r1_tarski('#skF_11', '#skF_13') | ~r1_tarski('#skF_10', '#skF_12')), inference(cnfTransformation, [status(thm)], [f_87])).
% 5.65/2.11  tff(c_66, plain, (~r1_tarski('#skF_10', '#skF_12')), inference(splitLeft, [status(thm)], [c_50])).
% 5.65/2.11  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.65/2.11  tff(c_12, plain, (![A_11]: (r2_hidden('#skF_3'(A_11), A_11) | k1_xboole_0=A_11)), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.65/2.11  tff(c_54, plain, (r1_tarski(k2_zfmisc_1('#skF_10', '#skF_11'), k2_zfmisc_1('#skF_12', '#skF_13'))), inference(cnfTransformation, [status(thm)], [f_87])).
% 5.65/2.11  tff(c_290, plain, (![A_101, B_102, C_103, D_104]: (r2_hidden(k4_tarski(A_101, B_102), k2_zfmisc_1(C_103, D_104)) | ~r2_hidden(B_102, D_104) | ~r2_hidden(A_101, C_103))), inference(cnfTransformation, [status(thm)], [f_78])).
% 5.65/2.11  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.65/2.11  tff(c_1952, plain, (![A_252, D_254, C_256, B_255, B_253]: (r2_hidden(k4_tarski(A_252, B_253), B_255) | ~r1_tarski(k2_zfmisc_1(C_256, D_254), B_255) | ~r2_hidden(B_253, D_254) | ~r2_hidden(A_252, C_256))), inference(resolution, [status(thm)], [c_290, c_2])).
% 5.65/2.11  tff(c_2299, plain, (![A_266, B_267]: (r2_hidden(k4_tarski(A_266, B_267), k2_zfmisc_1('#skF_12', '#skF_13')) | ~r2_hidden(B_267, '#skF_11') | ~r2_hidden(A_266, '#skF_10'))), inference(resolution, [status(thm)], [c_54, c_1952])).
% 5.65/2.11  tff(c_48, plain, (![A_51, C_53, B_52, D_54]: (r2_hidden(A_51, C_53) | ~r2_hidden(k4_tarski(A_51, B_52), k2_zfmisc_1(C_53, D_54)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 5.65/2.11  tff(c_2326, plain, (![A_266, B_267]: (r2_hidden(A_266, '#skF_12') | ~r2_hidden(B_267, '#skF_11') | ~r2_hidden(A_266, '#skF_10'))), inference(resolution, [status(thm)], [c_2299, c_48])).
% 5.65/2.11  tff(c_2330, plain, (![B_268]: (~r2_hidden(B_268, '#skF_11'))), inference(splitLeft, [status(thm)], [c_2326])).
% 5.65/2.11  tff(c_2399, plain, (k1_xboole_0='#skF_11'), inference(resolution, [status(thm)], [c_12, c_2330])).
% 5.65/2.11  tff(c_385, plain, (![A_115, B_116, D_117]: (r2_hidden('#skF_9'(A_115, B_116, k2_zfmisc_1(A_115, B_116), D_117), B_116) | ~r2_hidden(D_117, k2_zfmisc_1(A_115, B_116)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.65/2.11  tff(c_18, plain, (![A_16]: (r1_xboole_0(A_16, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.65/2.11  tff(c_68, plain, (![A_60, B_61, C_62]: (~r1_xboole_0(A_60, B_61) | ~r2_hidden(C_62, k3_xboole_0(A_60, B_61)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 5.65/2.11  tff(c_86, plain, (![A_66, B_67]: (~r1_xboole_0(A_66, B_67) | k3_xboole_0(A_66, B_67)=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_68])).
% 5.65/2.11  tff(c_91, plain, (![A_68]: (k3_xboole_0(A_68, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_86])).
% 5.65/2.11  tff(c_10, plain, (![A_6, B_7, C_10]: (~r1_xboole_0(A_6, B_7) | ~r2_hidden(C_10, k3_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 5.65/2.11  tff(c_96, plain, (![A_68, C_10]: (~r1_xboole_0(A_68, k1_xboole_0) | ~r2_hidden(C_10, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_91, c_10])).
% 5.65/2.11  tff(c_101, plain, (![C_10]: (~r2_hidden(C_10, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_96])).
% 5.65/2.11  tff(c_399, plain, (![D_118, A_119]: (~r2_hidden(D_118, k2_zfmisc_1(A_119, k1_xboole_0)))), inference(resolution, [status(thm)], [c_385, c_101])).
% 5.65/2.11  tff(c_434, plain, (![A_119]: (k2_zfmisc_1(A_119, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_399])).
% 5.65/2.11  tff(c_2426, plain, (![A_119]: (k2_zfmisc_1(A_119, '#skF_11')='#skF_11')), inference(demodulation, [status(thm), theory('equality')], [c_2399, c_2399, c_434])).
% 5.65/2.11  tff(c_52, plain, (k2_zfmisc_1('#skF_10', '#skF_11')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_87])).
% 5.65/2.11  tff(c_2438, plain, (k2_zfmisc_1('#skF_10', '#skF_11')!='#skF_11'), inference(demodulation, [status(thm), theory('equality')], [c_2399, c_52])).
% 5.65/2.11  tff(c_2703, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2426, c_2438])).
% 5.65/2.11  tff(c_2705, plain, (![A_283]: (r2_hidden(A_283, '#skF_12') | ~r2_hidden(A_283, '#skF_10'))), inference(splitRight, [status(thm)], [c_2326])).
% 5.65/2.11  tff(c_3709, plain, (![B_316]: (r2_hidden('#skF_1'('#skF_10', B_316), '#skF_12') | r1_tarski('#skF_10', B_316))), inference(resolution, [status(thm)], [c_6, c_2705])).
% 5.65/2.11  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.65/2.11  tff(c_3718, plain, (r1_tarski('#skF_10', '#skF_12')), inference(resolution, [status(thm)], [c_3709, c_4])).
% 5.65/2.11  tff(c_3724, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_66, c_3718])).
% 5.65/2.11  tff(c_3725, plain, (~r1_tarski('#skF_11', '#skF_13')), inference(splitRight, [status(thm)], [c_50])).
% 5.65/2.11  tff(c_3983, plain, (![A_361, B_362, C_363, D_364]: (r2_hidden(k4_tarski(A_361, B_362), k2_zfmisc_1(C_363, D_364)) | ~r2_hidden(B_362, D_364) | ~r2_hidden(A_361, C_363))), inference(cnfTransformation, [status(thm)], [f_78])).
% 5.65/2.11  tff(c_5408, plain, (![A_507, B_504, D_503, C_505, B_506]: (r2_hidden(k4_tarski(A_507, B_504), B_506) | ~r1_tarski(k2_zfmisc_1(C_505, D_503), B_506) | ~r2_hidden(B_504, D_503) | ~r2_hidden(A_507, C_505))), inference(resolution, [status(thm)], [c_3983, c_2])).
% 5.65/2.11  tff(c_5502, plain, (![A_514, B_515]: (r2_hidden(k4_tarski(A_514, B_515), k2_zfmisc_1('#skF_12', '#skF_13')) | ~r2_hidden(B_515, '#skF_11') | ~r2_hidden(A_514, '#skF_10'))), inference(resolution, [status(thm)], [c_54, c_5408])).
% 5.65/2.11  tff(c_46, plain, (![B_52, D_54, A_51, C_53]: (r2_hidden(B_52, D_54) | ~r2_hidden(k4_tarski(A_51, B_52), k2_zfmisc_1(C_53, D_54)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 5.65/2.11  tff(c_5529, plain, (![B_515, A_514]: (r2_hidden(B_515, '#skF_13') | ~r2_hidden(B_515, '#skF_11') | ~r2_hidden(A_514, '#skF_10'))), inference(resolution, [status(thm)], [c_5502, c_46])).
% 5.65/2.11  tff(c_5533, plain, (![A_516]: (~r2_hidden(A_516, '#skF_10'))), inference(splitLeft, [status(thm)], [c_5529])).
% 5.65/2.11  tff(c_5602, plain, (k1_xboole_0='#skF_10'), inference(resolution, [status(thm)], [c_12, c_5533])).
% 5.65/2.11  tff(c_4130, plain, (![A_378, B_379, D_380]: (r2_hidden('#skF_8'(A_378, B_379, k2_zfmisc_1(A_378, B_379), D_380), A_378) | ~r2_hidden(D_380, k2_zfmisc_1(A_378, B_379)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.65/2.11  tff(c_14, plain, (![A_13]: (k4_xboole_0(A_13, k1_xboole_0)=A_13)), inference(cnfTransformation, [status(thm)], [f_56])).
% 5.65/2.11  tff(c_3727, plain, (![A_317, B_318]: (k4_xboole_0(A_317, k4_xboole_0(A_317, B_318))=k3_xboole_0(A_317, B_318))), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.65/2.11  tff(c_3746, plain, (![A_321]: (k4_xboole_0(A_321, A_321)=k3_xboole_0(A_321, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_14, c_3727])).
% 5.65/2.11  tff(c_3756, plain, (k3_xboole_0(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_3746, c_14])).
% 5.65/2.11  tff(c_3778, plain, (![A_325, B_326, C_327]: (~r1_xboole_0(A_325, B_326) | ~r2_hidden(C_327, k3_xboole_0(A_325, B_326)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 5.65/2.11  tff(c_3785, plain, (![C_327]: (~r1_xboole_0(k1_xboole_0, k1_xboole_0) | ~r2_hidden(C_327, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_3756, c_3778])).
% 5.65/2.11  tff(c_3792, plain, (![C_327]: (~r2_hidden(C_327, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_3785])).
% 5.65/2.11  tff(c_4148, plain, (![D_381, B_382]: (~r2_hidden(D_381, k2_zfmisc_1(k1_xboole_0, B_382)))), inference(resolution, [status(thm)], [c_4130, c_3792])).
% 5.65/2.11  tff(c_4186, plain, (![B_382]: (k2_zfmisc_1(k1_xboole_0, B_382)=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_4148])).
% 5.65/2.11  tff(c_5624, plain, (![B_382]: (k2_zfmisc_1('#skF_10', B_382)='#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_5602, c_5602, c_4186])).
% 5.65/2.11  tff(c_5637, plain, (k2_zfmisc_1('#skF_10', '#skF_11')!='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_5602, c_52])).
% 5.65/2.11  tff(c_5848, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5624, c_5637])).
% 5.65/2.11  tff(c_6015, plain, (![B_535]: (r2_hidden(B_535, '#skF_13') | ~r2_hidden(B_535, '#skF_11'))), inference(splitRight, [status(thm)], [c_5529])).
% 5.65/2.11  tff(c_6944, plain, (![B_566]: (r2_hidden('#skF_1'('#skF_11', B_566), '#skF_13') | r1_tarski('#skF_11', B_566))), inference(resolution, [status(thm)], [c_6, c_6015])).
% 5.65/2.11  tff(c_6953, plain, (r1_tarski('#skF_11', '#skF_13')), inference(resolution, [status(thm)], [c_6944, c_4])).
% 5.65/2.11  tff(c_6959, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3725, c_3725, c_6953])).
% 5.65/2.11  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.65/2.11  
% 5.65/2.11  Inference rules
% 5.65/2.11  ----------------------
% 5.65/2.11  #Ref     : 0
% 5.65/2.11  #Sup     : 1492
% 5.65/2.11  #Fact    : 0
% 5.65/2.11  #Define  : 0
% 5.65/2.11  #Split   : 14
% 5.65/2.11  #Chain   : 0
% 5.65/2.11  #Close   : 0
% 5.65/2.11  
% 5.65/2.11  Ordering : KBO
% 5.65/2.11  
% 5.65/2.11  Simplification rules
% 5.65/2.11  ----------------------
% 5.65/2.11  #Subsume      : 425
% 5.65/2.11  #Demod        : 803
% 5.65/2.11  #Tautology    : 390
% 5.65/2.11  #SimpNegUnit  : 37
% 5.65/2.11  #BackRed      : 282
% 5.65/2.11  
% 5.65/2.11  #Partial instantiations: 0
% 5.65/2.11  #Strategies tried      : 1
% 5.65/2.11  
% 5.65/2.11  Timing (in seconds)
% 5.65/2.11  ----------------------
% 5.65/2.12  Preprocessing        : 0.31
% 5.65/2.12  Parsing              : 0.17
% 5.65/2.12  CNF conversion       : 0.03
% 5.65/2.12  Main loop            : 1.00
% 5.65/2.12  Inferencing          : 0.36
% 5.65/2.12  Reduction            : 0.29
% 5.65/2.12  Demodulation         : 0.19
% 5.65/2.12  BG Simplification    : 0.04
% 5.65/2.12  Subsumption          : 0.22
% 5.65/2.12  Abstraction          : 0.05
% 5.65/2.12  MUC search           : 0.00
% 5.65/2.12  Cooper               : 0.00
% 5.65/2.12  Total                : 1.34
% 5.65/2.12  Index Insertion      : 0.00
% 5.65/2.12  Index Deletion       : 0.00
% 5.65/2.12  Index Matching       : 0.00
% 5.65/2.12  BG Taut test         : 0.00
%------------------------------------------------------------------------------
