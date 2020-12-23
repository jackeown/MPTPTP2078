%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:17 EST 2020

% Result     : Theorem 6.43s
% Output     : CNFRefutation 6.43s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 208 expanded)
%              Number of leaves         :   34 (  82 expanded)
%              Depth                    :   11
%              Number of atoms          :  136 ( 467 expanded)
%              Number of equality atoms :   59 ( 311 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_130,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k1_tarski(A) = k2_xboole_0(B,C)
          & ~ ( B = k1_tarski(A)
              & C = k1_tarski(A) )
          & ~ ( B = k1_xboole_0
              & C = k1_tarski(A) )
          & ~ ( B = k1_tarski(A)
              & C = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_zfmisc_1)).

tff(f_73,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_86,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_47,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_71,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k5_xboole_0(B,C))
    <=> ~ ( r2_hidden(A,B)
        <=> r2_hidden(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).

tff(f_63,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

tff(c_84,plain,
    ( k1_tarski('#skF_5') != '#skF_7'
    | k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_139,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_84])).

tff(c_82,plain,
    ( k1_xboole_0 != '#skF_7'
    | k1_tarski('#skF_5') != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_126,plain,(
    k1_tarski('#skF_5') != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_82])).

tff(c_88,plain,(
    k2_xboole_0('#skF_6','#skF_7') = k1_tarski('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_42,plain,(
    ! [A_26,B_27] : r1_tarski(A_26,k2_xboole_0(A_26,B_27)) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_145,plain,(
    r1_tarski('#skF_6',k1_tarski('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_42])).

tff(c_337,plain,(
    ! [B_88,A_89] :
      ( B_88 = A_89
      | ~ r1_tarski(B_88,A_89)
      | ~ r1_tarski(A_89,B_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_343,plain,
    ( k1_tarski('#skF_5') = '#skF_6'
    | ~ r1_tarski(k1_tarski('#skF_5'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_145,c_337])).

tff(c_356,plain,(
    ~ r1_tarski(k1_tarski('#skF_5'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_126,c_343])).

tff(c_535,plain,(
    ! [A_106,B_107] :
      ( r2_hidden('#skF_1'(A_106,B_107),A_106)
      | r1_tarski(A_106,B_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_50,plain,(
    ! [C_35,A_31] :
      ( C_35 = A_31
      | ~ r2_hidden(C_35,k1_tarski(A_31)) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_1651,plain,(
    ! [A_195,B_196] :
      ( '#skF_1'(k1_tarski(A_195),B_196) = A_195
      | r1_tarski(k1_tarski(A_195),B_196) ) ),
    inference(resolution,[status(thm)],[c_535,c_50])).

tff(c_1679,plain,(
    '#skF_1'(k1_tarski('#skF_5'),'#skF_6') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_1651,c_356])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1688,plain,
    ( ~ r2_hidden('#skF_5','#skF_6')
    | r1_tarski(k1_tarski('#skF_5'),'#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_1679,c_4])).

tff(c_1693,plain,(
    ~ r2_hidden('#skF_5','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_356,c_1688])).

tff(c_20,plain,(
    ! [A_9] :
      ( r2_hidden('#skF_2'(A_9),A_9)
      | k1_xboole_0 = A_9 ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_646,plain,(
    ! [C_116,B_117,A_118] :
      ( r2_hidden(C_116,B_117)
      | ~ r2_hidden(C_116,A_118)
      | ~ r1_tarski(A_118,B_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1098,plain,(
    ! [A_158,B_159] :
      ( r2_hidden('#skF_2'(A_158),B_159)
      | ~ r1_tarski(A_158,B_159)
      | k1_xboole_0 = A_158 ) ),
    inference(resolution,[status(thm)],[c_20,c_646])).

tff(c_3462,plain,(
    ! [A_2979,A_2980] :
      ( A_2979 = '#skF_2'(A_2980)
      | ~ r1_tarski(A_2980,k1_tarski(A_2979))
      | k1_xboole_0 = A_2980 ) ),
    inference(resolution,[status(thm)],[c_1098,c_50])).

tff(c_3480,plain,
    ( '#skF_2'('#skF_6') = '#skF_5'
    | k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_145,c_3462])).

tff(c_3491,plain,(
    '#skF_2'('#skF_6') = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_139,c_3480])).

tff(c_3533,plain,
    ( r2_hidden('#skF_5','#skF_6')
    | k1_xboole_0 = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_3491,c_20])).

tff(c_3538,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_139,c_1693,c_3533])).

tff(c_3539,plain,(
    k1_tarski('#skF_5') != '#skF_7' ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_3540,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_40,plain,(
    ! [A_25] : k5_xboole_0(A_25,k1_xboole_0) = A_25 ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_3543,plain,(
    ! [A_25] : k5_xboole_0(A_25,'#skF_6') = A_25 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3540,c_40])).

tff(c_6674,plain,(
    ! [A_5884,B_5885,C_5886] :
      ( r2_hidden(A_5884,B_5885)
      | ~ r2_hidden(A_5884,C_5886)
      | r2_hidden(A_5884,k5_xboole_0(B_5885,C_5886)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_6832,plain,(
    ! [A_6204,A_6205] :
      ( r2_hidden(A_6204,A_6205)
      | ~ r2_hidden(A_6204,'#skF_6')
      | r2_hidden(A_6204,A_6205) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3543,c_6674])).

tff(c_6917,plain,(
    ! [B_6269,A_6270] :
      ( r2_hidden('#skF_1'('#skF_6',B_6269),A_6270)
      | r1_tarski('#skF_6',B_6269) ) ),
    inference(resolution,[status(thm)],[c_6,c_6832])).

tff(c_6944,plain,(
    ! [A_6302] : r1_tarski('#skF_6',A_6302) ),
    inference(resolution,[status(thm)],[c_6917,c_4])).

tff(c_32,plain,(
    ! [A_18,B_19] :
      ( k2_xboole_0(A_18,B_19) = B_19
      | ~ r1_tarski(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_6963,plain,(
    ! [A_6302] : k2_xboole_0('#skF_6',A_6302) = A_6302 ),
    inference(resolution,[status(thm)],[c_6944,c_32])).

tff(c_6966,plain,(
    k1_tarski('#skF_5') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6963,c_88])).

tff(c_6968,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3539,c_6966])).

tff(c_6969,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(splitRight,[status(thm)],[c_82])).

tff(c_6970,plain,(
    k1_tarski('#skF_5') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_82])).

tff(c_86,plain,
    ( k1_tarski('#skF_5') != '#skF_7'
    | k1_tarski('#skF_5') != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_7035,plain,(
    '#skF_7' != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6970,c_6970,c_86])).

tff(c_26,plain,(
    ! [B_12] : r1_tarski(B_12,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_6988,plain,(
    k2_xboole_0('#skF_6','#skF_7') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6970,c_88])).

tff(c_7288,plain,(
    ! [A_6370,C_6371,B_6372] :
      ( r1_tarski(A_6370,k2_xboole_0(C_6371,B_6372))
      | ~ r1_tarski(A_6370,B_6372) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_7308,plain,(
    ! [A_6373] :
      ( r1_tarski(A_6373,'#skF_6')
      | ~ r1_tarski(A_6373,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6988,c_7288])).

tff(c_7313,plain,(
    r1_tarski('#skF_7','#skF_6') ),
    inference(resolution,[status(thm)],[c_26,c_7308])).

tff(c_7479,plain,(
    ! [B_6385,A_6386] :
      ( B_6385 = A_6386
      | ~ r1_tarski(B_6385,A_6386)
      | ~ r1_tarski(A_6386,B_6385) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_7483,plain,
    ( '#skF_7' = '#skF_6'
    | ~ r1_tarski('#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_7313,c_7479])).

tff(c_7507,plain,(
    ~ r1_tarski('#skF_6','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_7035,c_7483])).

tff(c_7368,plain,(
    ! [A_6377,B_6378] :
      ( r2_hidden('#skF_1'(A_6377,B_6378),A_6377)
      | r1_tarski(A_6377,B_6378) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_7013,plain,(
    ! [C_6342,A_6343] :
      ( C_6342 = A_6343
      | ~ r2_hidden(C_6342,k1_tarski(A_6343)) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_7016,plain,(
    ! [C_6342] :
      ( C_6342 = '#skF_5'
      | ~ r2_hidden(C_6342,'#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6970,c_7013])).

tff(c_7377,plain,(
    ! [B_6378] :
      ( '#skF_1'('#skF_6',B_6378) = '#skF_5'
      | r1_tarski('#skF_6',B_6378) ) ),
    inference(resolution,[status(thm)],[c_7368,c_7016])).

tff(c_7526,plain,(
    '#skF_1'('#skF_6','#skF_7') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_7377,c_7507])).

tff(c_7534,plain,
    ( ~ r2_hidden('#skF_5','#skF_7')
    | r1_tarski('#skF_6','#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_7526,c_4])).

tff(c_7540,plain,(
    ~ r2_hidden('#skF_5','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_7507,c_7534])).

tff(c_7623,plain,(
    ! [C_6391,B_6392,A_6393] :
      ( r2_hidden(C_6391,B_6392)
      | ~ r2_hidden(C_6391,A_6393)
      | ~ r1_tarski(A_6393,B_6392) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_9588,plain,(
    ! [A_9940,B_9941] :
      ( r2_hidden('#skF_2'(A_9940),B_9941)
      | ~ r1_tarski(A_9940,B_9941)
      | k1_xboole_0 = A_9940 ) ),
    inference(resolution,[status(thm)],[c_20,c_7623])).

tff(c_9614,plain,(
    ! [A_9973] :
      ( '#skF_2'(A_9973) = '#skF_5'
      | ~ r1_tarski(A_9973,'#skF_6')
      | k1_xboole_0 = A_9973 ) ),
    inference(resolution,[status(thm)],[c_9588,c_7016])).

tff(c_9625,plain,
    ( '#skF_2'('#skF_7') = '#skF_5'
    | k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_7313,c_9614])).

tff(c_9637,plain,(
    '#skF_2'('#skF_7') = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_6969,c_9625])).

tff(c_9691,plain,
    ( r2_hidden('#skF_5','#skF_7')
    | k1_xboole_0 = '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_9637,c_20])).

tff(c_9696,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6969,c_7540,c_9691])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n011.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 16:14:27 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.18/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.43/2.31  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.43/2.31  
% 6.43/2.31  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.43/2.32  %$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_1 > #skF_4
% 6.43/2.32  
% 6.43/2.32  %Foreground sorts:
% 6.43/2.32  
% 6.43/2.32  
% 6.43/2.32  %Background operators:
% 6.43/2.32  
% 6.43/2.32  
% 6.43/2.32  %Foreground operators:
% 6.43/2.32  tff('#skF_2', type, '#skF_2': $i > $i).
% 6.43/2.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.43/2.32  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.43/2.32  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.43/2.32  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.43/2.32  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.43/2.32  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 6.43/2.32  tff('#skF_7', type, '#skF_7': $i).
% 6.43/2.32  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 6.43/2.32  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 6.43/2.32  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.43/2.32  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 6.43/2.32  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.43/2.32  tff('#skF_5', type, '#skF_5': $i).
% 6.43/2.32  tff('#skF_6', type, '#skF_6': $i).
% 6.43/2.32  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.43/2.32  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 6.43/2.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.43/2.32  tff(k3_tarski, type, k3_tarski: $i > $i).
% 6.43/2.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.43/2.32  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.43/2.32  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.43/2.32  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 6.43/2.32  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 6.43/2.32  
% 6.43/2.33  tff(f_130, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~((B = k1_tarski(A)) & (C = k1_tarski(A)))) & ~((B = k1_xboole_0) & (C = k1_tarski(A)))) & ~((B = k1_tarski(A)) & (C = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_zfmisc_1)).
% 6.43/2.33  tff(f_73, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 6.43/2.33  tff(f_53, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 6.43/2.33  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 6.43/2.33  tff(f_86, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 6.43/2.33  tff(f_47, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 6.43/2.33  tff(f_71, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 6.43/2.33  tff(f_39, axiom, (![A, B, C]: (r2_hidden(A, k5_xboole_0(B, C)) <=> ~(r2_hidden(A, B) <=> r2_hidden(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_0)).
% 6.43/2.33  tff(f_63, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 6.43/2.33  tff(f_59, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_xboole_1)).
% 6.43/2.33  tff(c_84, plain, (k1_tarski('#skF_5')!='#skF_7' | k1_xboole_0!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_130])).
% 6.43/2.33  tff(c_139, plain, (k1_xboole_0!='#skF_6'), inference(splitLeft, [status(thm)], [c_84])).
% 6.43/2.33  tff(c_82, plain, (k1_xboole_0!='#skF_7' | k1_tarski('#skF_5')!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_130])).
% 6.43/2.33  tff(c_126, plain, (k1_tarski('#skF_5')!='#skF_6'), inference(splitLeft, [status(thm)], [c_82])).
% 6.43/2.33  tff(c_88, plain, (k2_xboole_0('#skF_6', '#skF_7')=k1_tarski('#skF_5')), inference(cnfTransformation, [status(thm)], [f_130])).
% 6.43/2.33  tff(c_42, plain, (![A_26, B_27]: (r1_tarski(A_26, k2_xboole_0(A_26, B_27)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 6.43/2.33  tff(c_145, plain, (r1_tarski('#skF_6', k1_tarski('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_88, c_42])).
% 6.43/2.33  tff(c_337, plain, (![B_88, A_89]: (B_88=A_89 | ~r1_tarski(B_88, A_89) | ~r1_tarski(A_89, B_88))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.43/2.33  tff(c_343, plain, (k1_tarski('#skF_5')='#skF_6' | ~r1_tarski(k1_tarski('#skF_5'), '#skF_6')), inference(resolution, [status(thm)], [c_145, c_337])).
% 6.43/2.33  tff(c_356, plain, (~r1_tarski(k1_tarski('#skF_5'), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_126, c_343])).
% 6.43/2.33  tff(c_535, plain, (![A_106, B_107]: (r2_hidden('#skF_1'(A_106, B_107), A_106) | r1_tarski(A_106, B_107))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.43/2.33  tff(c_50, plain, (![C_35, A_31]: (C_35=A_31 | ~r2_hidden(C_35, k1_tarski(A_31)))), inference(cnfTransformation, [status(thm)], [f_86])).
% 6.43/2.33  tff(c_1651, plain, (![A_195, B_196]: ('#skF_1'(k1_tarski(A_195), B_196)=A_195 | r1_tarski(k1_tarski(A_195), B_196))), inference(resolution, [status(thm)], [c_535, c_50])).
% 6.43/2.33  tff(c_1679, plain, ('#skF_1'(k1_tarski('#skF_5'), '#skF_6')='#skF_5'), inference(resolution, [status(thm)], [c_1651, c_356])).
% 6.43/2.33  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.43/2.33  tff(c_1688, plain, (~r2_hidden('#skF_5', '#skF_6') | r1_tarski(k1_tarski('#skF_5'), '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_1679, c_4])).
% 6.43/2.33  tff(c_1693, plain, (~r2_hidden('#skF_5', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_356, c_1688])).
% 6.43/2.33  tff(c_20, plain, (![A_9]: (r2_hidden('#skF_2'(A_9), A_9) | k1_xboole_0=A_9)), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.43/2.33  tff(c_646, plain, (![C_116, B_117, A_118]: (r2_hidden(C_116, B_117) | ~r2_hidden(C_116, A_118) | ~r1_tarski(A_118, B_117))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.43/2.33  tff(c_1098, plain, (![A_158, B_159]: (r2_hidden('#skF_2'(A_158), B_159) | ~r1_tarski(A_158, B_159) | k1_xboole_0=A_158)), inference(resolution, [status(thm)], [c_20, c_646])).
% 6.43/2.33  tff(c_3462, plain, (![A_2979, A_2980]: (A_2979='#skF_2'(A_2980) | ~r1_tarski(A_2980, k1_tarski(A_2979)) | k1_xboole_0=A_2980)), inference(resolution, [status(thm)], [c_1098, c_50])).
% 6.43/2.33  tff(c_3480, plain, ('#skF_2'('#skF_6')='#skF_5' | k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_145, c_3462])).
% 6.43/2.33  tff(c_3491, plain, ('#skF_2'('#skF_6')='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_139, c_3480])).
% 6.43/2.33  tff(c_3533, plain, (r2_hidden('#skF_5', '#skF_6') | k1_xboole_0='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_3491, c_20])).
% 6.43/2.33  tff(c_3538, plain, $false, inference(negUnitSimplification, [status(thm)], [c_139, c_1693, c_3533])).
% 6.43/2.33  tff(c_3539, plain, (k1_tarski('#skF_5')!='#skF_7'), inference(splitRight, [status(thm)], [c_84])).
% 6.43/2.33  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.43/2.33  tff(c_3540, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_84])).
% 6.43/2.33  tff(c_40, plain, (![A_25]: (k5_xboole_0(A_25, k1_xboole_0)=A_25)), inference(cnfTransformation, [status(thm)], [f_71])).
% 6.43/2.33  tff(c_3543, plain, (![A_25]: (k5_xboole_0(A_25, '#skF_6')=A_25)), inference(demodulation, [status(thm), theory('equality')], [c_3540, c_40])).
% 6.43/2.33  tff(c_6674, plain, (![A_5884, B_5885, C_5886]: (r2_hidden(A_5884, B_5885) | ~r2_hidden(A_5884, C_5886) | r2_hidden(A_5884, k5_xboole_0(B_5885, C_5886)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.43/2.33  tff(c_6832, plain, (![A_6204, A_6205]: (r2_hidden(A_6204, A_6205) | ~r2_hidden(A_6204, '#skF_6') | r2_hidden(A_6204, A_6205))), inference(superposition, [status(thm), theory('equality')], [c_3543, c_6674])).
% 6.43/2.33  tff(c_6917, plain, (![B_6269, A_6270]: (r2_hidden('#skF_1'('#skF_6', B_6269), A_6270) | r1_tarski('#skF_6', B_6269))), inference(resolution, [status(thm)], [c_6, c_6832])).
% 6.43/2.33  tff(c_6944, plain, (![A_6302]: (r1_tarski('#skF_6', A_6302))), inference(resolution, [status(thm)], [c_6917, c_4])).
% 6.43/2.33  tff(c_32, plain, (![A_18, B_19]: (k2_xboole_0(A_18, B_19)=B_19 | ~r1_tarski(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_63])).
% 6.43/2.33  tff(c_6963, plain, (![A_6302]: (k2_xboole_0('#skF_6', A_6302)=A_6302)), inference(resolution, [status(thm)], [c_6944, c_32])).
% 6.43/2.33  tff(c_6966, plain, (k1_tarski('#skF_5')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_6963, c_88])).
% 6.43/2.33  tff(c_6968, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3539, c_6966])).
% 6.43/2.33  tff(c_6969, plain, (k1_xboole_0!='#skF_7'), inference(splitRight, [status(thm)], [c_82])).
% 6.43/2.33  tff(c_6970, plain, (k1_tarski('#skF_5')='#skF_6'), inference(splitRight, [status(thm)], [c_82])).
% 6.43/2.33  tff(c_86, plain, (k1_tarski('#skF_5')!='#skF_7' | k1_tarski('#skF_5')!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_130])).
% 6.43/2.33  tff(c_7035, plain, ('#skF_7'!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_6970, c_6970, c_86])).
% 6.43/2.33  tff(c_26, plain, (![B_12]: (r1_tarski(B_12, B_12))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.43/2.33  tff(c_6988, plain, (k2_xboole_0('#skF_6', '#skF_7')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_6970, c_88])).
% 6.43/2.33  tff(c_7288, plain, (![A_6370, C_6371, B_6372]: (r1_tarski(A_6370, k2_xboole_0(C_6371, B_6372)) | ~r1_tarski(A_6370, B_6372))), inference(cnfTransformation, [status(thm)], [f_59])).
% 6.43/2.33  tff(c_7308, plain, (![A_6373]: (r1_tarski(A_6373, '#skF_6') | ~r1_tarski(A_6373, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_6988, c_7288])).
% 6.43/2.33  tff(c_7313, plain, (r1_tarski('#skF_7', '#skF_6')), inference(resolution, [status(thm)], [c_26, c_7308])).
% 6.43/2.33  tff(c_7479, plain, (![B_6385, A_6386]: (B_6385=A_6386 | ~r1_tarski(B_6385, A_6386) | ~r1_tarski(A_6386, B_6385))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.43/2.33  tff(c_7483, plain, ('#skF_7'='#skF_6' | ~r1_tarski('#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_7313, c_7479])).
% 6.43/2.33  tff(c_7507, plain, (~r1_tarski('#skF_6', '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_7035, c_7483])).
% 6.43/2.33  tff(c_7368, plain, (![A_6377, B_6378]: (r2_hidden('#skF_1'(A_6377, B_6378), A_6377) | r1_tarski(A_6377, B_6378))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.43/2.33  tff(c_7013, plain, (![C_6342, A_6343]: (C_6342=A_6343 | ~r2_hidden(C_6342, k1_tarski(A_6343)))), inference(cnfTransformation, [status(thm)], [f_86])).
% 6.43/2.33  tff(c_7016, plain, (![C_6342]: (C_6342='#skF_5' | ~r2_hidden(C_6342, '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_6970, c_7013])).
% 6.43/2.33  tff(c_7377, plain, (![B_6378]: ('#skF_1'('#skF_6', B_6378)='#skF_5' | r1_tarski('#skF_6', B_6378))), inference(resolution, [status(thm)], [c_7368, c_7016])).
% 6.43/2.33  tff(c_7526, plain, ('#skF_1'('#skF_6', '#skF_7')='#skF_5'), inference(resolution, [status(thm)], [c_7377, c_7507])).
% 6.43/2.33  tff(c_7534, plain, (~r2_hidden('#skF_5', '#skF_7') | r1_tarski('#skF_6', '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_7526, c_4])).
% 6.43/2.33  tff(c_7540, plain, (~r2_hidden('#skF_5', '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_7507, c_7534])).
% 6.43/2.33  tff(c_7623, plain, (![C_6391, B_6392, A_6393]: (r2_hidden(C_6391, B_6392) | ~r2_hidden(C_6391, A_6393) | ~r1_tarski(A_6393, B_6392))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.43/2.33  tff(c_9588, plain, (![A_9940, B_9941]: (r2_hidden('#skF_2'(A_9940), B_9941) | ~r1_tarski(A_9940, B_9941) | k1_xboole_0=A_9940)), inference(resolution, [status(thm)], [c_20, c_7623])).
% 6.43/2.33  tff(c_9614, plain, (![A_9973]: ('#skF_2'(A_9973)='#skF_5' | ~r1_tarski(A_9973, '#skF_6') | k1_xboole_0=A_9973)), inference(resolution, [status(thm)], [c_9588, c_7016])).
% 6.43/2.33  tff(c_9625, plain, ('#skF_2'('#skF_7')='#skF_5' | k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_7313, c_9614])).
% 6.43/2.33  tff(c_9637, plain, ('#skF_2'('#skF_7')='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_6969, c_9625])).
% 6.43/2.33  tff(c_9691, plain, (r2_hidden('#skF_5', '#skF_7') | k1_xboole_0='#skF_7'), inference(superposition, [status(thm), theory('equality')], [c_9637, c_20])).
% 6.43/2.33  tff(c_9696, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6969, c_7540, c_9691])).
% 6.43/2.33  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.43/2.33  
% 6.43/2.33  Inference rules
% 6.43/2.33  ----------------------
% 6.43/2.33  #Ref     : 0
% 6.43/2.33  #Sup     : 1546
% 6.43/2.33  #Fact    : 0
% 6.43/2.33  #Define  : 0
% 6.43/2.33  #Split   : 9
% 6.43/2.33  #Chain   : 0
% 6.43/2.33  #Close   : 0
% 6.43/2.33  
% 6.43/2.33  Ordering : KBO
% 6.43/2.33  
% 6.43/2.33  Simplification rules
% 6.43/2.33  ----------------------
% 6.43/2.33  #Subsume      : 97
% 6.43/2.33  #Demod        : 686
% 6.43/2.33  #Tautology    : 890
% 6.43/2.33  #SimpNegUnit  : 49
% 6.43/2.33  #BackRed      : 27
% 6.43/2.33  
% 6.43/2.33  #Partial instantiations: 5526
% 6.43/2.33  #Strategies tried      : 1
% 6.43/2.33  
% 6.43/2.33  Timing (in seconds)
% 6.43/2.33  ----------------------
% 6.43/2.33  Preprocessing        : 0.36
% 6.43/2.33  Parsing              : 0.18
% 6.43/2.33  CNF conversion       : 0.03
% 6.43/2.33  Main loop            : 1.20
% 6.43/2.33  Inferencing          : 0.55
% 6.43/2.33  Reduction            : 0.36
% 6.43/2.33  Demodulation         : 0.26
% 6.43/2.33  BG Simplification    : 0.04
% 6.43/2.33  Subsumption          : 0.17
% 6.43/2.33  Abstraction          : 0.04
% 6.43/2.34  MUC search           : 0.00
% 6.43/2.34  Cooper               : 0.00
% 6.43/2.34  Total                : 1.59
% 6.43/2.34  Index Insertion      : 0.00
% 6.43/2.34  Index Deletion       : 0.00
% 6.43/2.34  Index Matching       : 0.00
% 6.43/2.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
