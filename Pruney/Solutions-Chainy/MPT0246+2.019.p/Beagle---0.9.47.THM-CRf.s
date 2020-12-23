%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:02 EST 2020

% Result     : Theorem 15.50s
% Output     : CNFRefutation 15.50s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 232 expanded)
%              Number of leaves         :   25 (  89 expanded)
%              Depth                    :   13
%              Number of atoms          :  129 ( 504 expanded)
%              Number of equality atoms :   74 ( 279 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_74,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( A != k1_tarski(B)
          & A != k1_xboole_0
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & C != B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_zfmisc_1)).

tff(f_47,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_36,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k4_xboole_0(B,A))
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_xboole_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(c_44,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_46,plain,(
    k1_tarski('#skF_5') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_28,plain,(
    ! [A_14] : k2_tarski(A_14,A_14) = k1_tarski(A_14) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_77,plain,(
    ! [A_55,B_56] :
      ( r2_hidden('#skF_1'(A_55,B_56),A_55)
      | r1_tarski(A_55,B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_42,plain,(
    ! [C_43] :
      ( C_43 = '#skF_5'
      | ~ r2_hidden(C_43,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_83,plain,(
    ! [B_57] :
      ( '#skF_1'('#skF_4',B_57) = '#skF_5'
      | r1_tarski('#skF_4',B_57) ) ),
    inference(resolution,[status(thm)],[c_77,c_42])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( k1_xboole_0 = A_6
      | ~ r1_tarski(A_6,k4_xboole_0(B_7,A_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_87,plain,(
    ! [B_7] :
      ( k1_xboole_0 = '#skF_4'
      | '#skF_1'('#skF_4',k4_xboole_0(B_7,'#skF_4')) = '#skF_5' ) ),
    inference(resolution,[status(thm)],[c_83,c_8])).

tff(c_91,plain,(
    ! [B_58] : '#skF_1'('#skF_4',k4_xboole_0(B_58,'#skF_4')) = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_87])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_96,plain,(
    ! [B_58] :
      ( r2_hidden('#skF_5','#skF_4')
      | r1_tarski('#skF_4',k4_xboole_0(B_58,'#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_91,c_6])).

tff(c_141,plain,(
    r2_hidden('#skF_5','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_96])).

tff(c_111,plain,(
    ! [D_62,B_63,A_64] :
      ( D_62 = B_63
      | D_62 = A_64
      | ~ r2_hidden(D_62,k2_tarski(A_64,B_63)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_130,plain,(
    ! [D_65,A_66] :
      ( D_65 = A_66
      | D_65 = A_66
      | ~ r2_hidden(D_65,k1_tarski(A_66)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_111])).

tff(c_138,plain,(
    ! [A_66,B_2] :
      ( '#skF_1'(k1_tarski(A_66),B_2) = A_66
      | r1_tarski(k1_tarski(A_66),B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_130])).

tff(c_157,plain,(
    ! [C_71,B_72,A_73] :
      ( r2_hidden(C_71,B_72)
      | ~ r2_hidden(C_71,A_73)
      | ~ r1_tarski(A_73,B_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_408,plain,(
    ! [A_110,B_111,B_112] :
      ( r2_hidden('#skF_1'(A_110,B_111),B_112)
      | ~ r1_tarski(A_110,B_112)
      | r1_tarski(A_110,B_111) ) ),
    inference(resolution,[status(thm)],[c_6,c_157])).

tff(c_447,plain,(
    ! [A_113,B_114] :
      ( '#skF_1'(A_113,B_114) = '#skF_5'
      | ~ r1_tarski(A_113,'#skF_4')
      | r1_tarski(A_113,B_114) ) ),
    inference(resolution,[status(thm)],[c_408,c_42])).

tff(c_4339,plain,(
    ! [A_6679,B_6680] :
      ( '#skF_1'(k1_tarski(A_6679),B_6680) = '#skF_5'
      | r1_tarski(k1_tarski(A_6679),B_6680)
      | '#skF_1'(k1_tarski(A_6679),'#skF_4') = A_6679 ) ),
    inference(resolution,[status(thm)],[c_138,c_447])).

tff(c_49,plain,(
    ! [A_48] : k2_tarski(A_48,A_48) = k1_tarski(A_48) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_12,plain,(
    ! [D_13,A_8] : r2_hidden(D_13,k2_tarski(A_8,D_13)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_55,plain,(
    ! [A_48] : r2_hidden(A_48,k1_tarski(A_48)) ),
    inference(superposition,[status(thm),theory(equality)],[c_49,c_12])).

tff(c_170,plain,(
    ! [A_48,B_72] :
      ( r2_hidden(A_48,B_72)
      | ~ r1_tarski(k1_tarski(A_48),B_72) ) ),
    inference(resolution,[status(thm)],[c_55,c_157])).

tff(c_4460,plain,(
    ! [A_6679,B_6680] :
      ( r2_hidden(A_6679,B_6680)
      | '#skF_1'(k1_tarski(A_6679),B_6680) = '#skF_5'
      | '#skF_1'(k1_tarski(A_6679),'#skF_4') = A_6679 ) ),
    inference(resolution,[status(thm)],[c_4339,c_170])).

tff(c_4874,plain,(
    ! [A_7235] :
      ( r2_hidden(A_7235,'#skF_4')
      | '#skF_1'(k1_tarski(A_7235),'#skF_4') = '#skF_5'
      | A_7235 != '#skF_5' ) ),
    inference(factorization,[status(thm),theory(equality)],[c_4460])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4895,plain,(
    ! [A_7235] :
      ( ~ r2_hidden('#skF_5','#skF_4')
      | r1_tarski(k1_tarski(A_7235),'#skF_4')
      | r2_hidden(A_7235,'#skF_4')
      | A_7235 != '#skF_5' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4874,c_4])).

tff(c_4997,plain,(
    ! [A_7515] :
      ( r1_tarski(k1_tarski(A_7515),'#skF_4')
      | r2_hidden(A_7515,'#skF_4')
      | A_7515 != '#skF_5' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_4895])).

tff(c_5022,plain,(
    r2_hidden('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_4997,c_170])).

tff(c_28004,plain,(
    ! [A_37281,B_37282,C_37283] :
      ( '#skF_2'(A_37281,B_37282,C_37283) = B_37282
      | '#skF_2'(A_37281,B_37282,C_37283) = A_37281
      | r2_hidden('#skF_3'(A_37281,B_37282,C_37283),C_37283)
      | k2_tarski(A_37281,B_37282) = C_37283 ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_28821,plain,(
    ! [A_38390,B_38391] :
      ( '#skF_3'(A_38390,B_38391,'#skF_4') = '#skF_5'
      | '#skF_2'(A_38390,B_38391,'#skF_4') = B_38391
      | '#skF_2'(A_38390,B_38391,'#skF_4') = A_38390
      | k2_tarski(A_38390,B_38391) = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_28004,c_42])).

tff(c_67429,plain,(
    ! [B_67637] :
      ( k1_tarski(B_67637) = '#skF_4'
      | '#skF_3'(B_67637,B_67637,'#skF_4') = '#skF_5'
      | '#skF_2'(B_67637,B_67637,'#skF_4') = B_67637
      | '#skF_2'(B_67637,B_67637,'#skF_4') = B_67637 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28821,c_28])).

tff(c_68978,plain,
    ( '#skF_3'('#skF_5','#skF_5','#skF_4') = '#skF_5'
    | '#skF_2'('#skF_5','#skF_5','#skF_4') = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_67429,c_46])).

tff(c_68982,plain,(
    '#skF_2'('#skF_5','#skF_5','#skF_4') = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_68978])).

tff(c_16,plain,(
    ! [A_8,B_9,C_10] :
      ( ~ r2_hidden('#skF_2'(A_8,B_9,C_10),C_10)
      | '#skF_3'(A_8,B_9,C_10) != B_9
      | k2_tarski(A_8,B_9) = C_10 ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_69011,plain,
    ( ~ r2_hidden('#skF_5','#skF_4')
    | '#skF_3'('#skF_5','#skF_5','#skF_4') != '#skF_5'
    | k2_tarski('#skF_5','#skF_5') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_68982,c_16])).

tff(c_69380,plain,
    ( '#skF_3'('#skF_5','#skF_5','#skF_4') != '#skF_5'
    | k1_tarski('#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_5022,c_69011])).

tff(c_69381,plain,(
    '#skF_3'('#skF_5','#skF_5','#skF_4') != '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_69380])).

tff(c_24,plain,(
    ! [A_8,B_9,C_10] :
      ( ~ r2_hidden('#skF_2'(A_8,B_9,C_10),C_10)
      | r2_hidden('#skF_3'(A_8,B_9,C_10),C_10)
      | k2_tarski(A_8,B_9) = C_10 ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_69008,plain,
    ( ~ r2_hidden('#skF_5','#skF_4')
    | r2_hidden('#skF_3'('#skF_5','#skF_5','#skF_4'),'#skF_4')
    | k2_tarski('#skF_5','#skF_5') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_68982,c_24])).

tff(c_69377,plain,
    ( r2_hidden('#skF_3'('#skF_5','#skF_5','#skF_4'),'#skF_4')
    | k1_tarski('#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_5022,c_69008])).

tff(c_69378,plain,(
    r2_hidden('#skF_3'('#skF_5','#skF_5','#skF_4'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_69377])).

tff(c_69411,plain,(
    '#skF_3'('#skF_5','#skF_5','#skF_4') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_69378,c_42])).

tff(c_69746,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_69381,c_69411])).

tff(c_69747,plain,(
    '#skF_3'('#skF_5','#skF_5','#skF_4') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_68978])).

tff(c_18,plain,(
    ! [A_8,B_9,C_10] :
      ( '#skF_2'(A_8,B_9,C_10) = B_9
      | '#skF_2'(A_8,B_9,C_10) = A_8
      | '#skF_3'(A_8,B_9,C_10) != B_9
      | k2_tarski(A_8,B_9) = C_10 ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_7174,plain,(
    ! [B_9,C_10] :
      ( '#skF_3'(B_9,B_9,C_10) != B_9
      | k2_tarski(B_9,B_9) = C_10
      | '#skF_2'(B_9,B_9,C_10) = B_9 ) ),
    inference(factorization,[status(thm),theory(equality)],[c_18])).

tff(c_25204,plain,(
    ! [B_31434,C_31435] :
      ( '#skF_3'(B_31434,B_31434,C_31435) != B_31434
      | k1_tarski(B_31434) = C_31435
      | '#skF_2'(B_31434,B_31434,C_31435) = B_31434 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_7174])).

tff(c_26806,plain,(
    ! [C_31435] :
      ( C_31435 != '#skF_4'
      | '#skF_3'('#skF_5','#skF_5',C_31435) != '#skF_5'
      | '#skF_2'('#skF_5','#skF_5',C_31435) = '#skF_5' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_25204,c_46])).

tff(c_69748,plain,(
    '#skF_2'('#skF_5','#skF_5','#skF_4') != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_68978])).

tff(c_71062,plain,(
    '#skF_3'('#skF_5','#skF_5','#skF_4') != '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_26806,c_69748])).

tff(c_71085,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_69747,c_71062])).

tff(c_71090,plain,(
    ! [B_70861] : r1_tarski('#skF_4',k4_xboole_0(B_70861,'#skF_4')) ),
    inference(splitRight,[status(thm)],[c_96])).

tff(c_71093,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_71090,c_8])).

tff(c_71097,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_71093])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:45:05 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 15.50/6.70  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.50/6.71  
% 15.50/6.71  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.50/6.71  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 15.50/6.71  
% 15.50/6.71  %Foreground sorts:
% 15.50/6.71  
% 15.50/6.71  
% 15.50/6.71  %Background operators:
% 15.50/6.71  
% 15.50/6.71  
% 15.50/6.71  %Foreground operators:
% 15.50/6.71  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 15.50/6.71  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 15.50/6.71  tff(k1_tarski, type, k1_tarski: $i > $i).
% 15.50/6.71  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 15.50/6.71  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 15.50/6.71  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 15.50/6.71  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 15.50/6.71  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 15.50/6.71  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 15.50/6.71  tff('#skF_5', type, '#skF_5': $i).
% 15.50/6.71  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 15.50/6.71  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 15.50/6.71  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 15.50/6.71  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 15.50/6.71  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 15.50/6.71  tff('#skF_4', type, '#skF_4': $i).
% 15.50/6.71  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 15.50/6.71  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 15.50/6.71  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 15.50/6.71  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 15.50/6.71  
% 15.50/6.72  tff(f_74, negated_conjecture, ~(![A, B]: ~((~(A = k1_tarski(B)) & ~(A = k1_xboole_0)) & (![C]: ~(r2_hidden(C, A) & ~(C = B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_zfmisc_1)).
% 15.50/6.72  tff(f_47, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 15.50/6.72  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 15.50/6.72  tff(f_36, axiom, (![A, B]: (r1_tarski(A, k4_xboole_0(B, A)) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_xboole_1)).
% 15.50/6.72  tff(f_45, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 15.50/6.72  tff(c_44, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_74])).
% 15.50/6.72  tff(c_46, plain, (k1_tarski('#skF_5')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_74])).
% 15.50/6.72  tff(c_28, plain, (![A_14]: (k2_tarski(A_14, A_14)=k1_tarski(A_14))), inference(cnfTransformation, [status(thm)], [f_47])).
% 15.50/6.72  tff(c_77, plain, (![A_55, B_56]: (r2_hidden('#skF_1'(A_55, B_56), A_55) | r1_tarski(A_55, B_56))), inference(cnfTransformation, [status(thm)], [f_32])).
% 15.50/6.72  tff(c_42, plain, (![C_43]: (C_43='#skF_5' | ~r2_hidden(C_43, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_74])).
% 15.50/6.72  tff(c_83, plain, (![B_57]: ('#skF_1'('#skF_4', B_57)='#skF_5' | r1_tarski('#skF_4', B_57))), inference(resolution, [status(thm)], [c_77, c_42])).
% 15.50/6.72  tff(c_8, plain, (![A_6, B_7]: (k1_xboole_0=A_6 | ~r1_tarski(A_6, k4_xboole_0(B_7, A_6)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 15.50/6.72  tff(c_87, plain, (![B_7]: (k1_xboole_0='#skF_4' | '#skF_1'('#skF_4', k4_xboole_0(B_7, '#skF_4'))='#skF_5')), inference(resolution, [status(thm)], [c_83, c_8])).
% 15.50/6.72  tff(c_91, plain, (![B_58]: ('#skF_1'('#skF_4', k4_xboole_0(B_58, '#skF_4'))='#skF_5')), inference(negUnitSimplification, [status(thm)], [c_44, c_87])).
% 15.50/6.72  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 15.50/6.72  tff(c_96, plain, (![B_58]: (r2_hidden('#skF_5', '#skF_4') | r1_tarski('#skF_4', k4_xboole_0(B_58, '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_91, c_6])).
% 15.50/6.72  tff(c_141, plain, (r2_hidden('#skF_5', '#skF_4')), inference(splitLeft, [status(thm)], [c_96])).
% 15.50/6.72  tff(c_111, plain, (![D_62, B_63, A_64]: (D_62=B_63 | D_62=A_64 | ~r2_hidden(D_62, k2_tarski(A_64, B_63)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 15.50/6.72  tff(c_130, plain, (![D_65, A_66]: (D_65=A_66 | D_65=A_66 | ~r2_hidden(D_65, k1_tarski(A_66)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_111])).
% 15.50/6.72  tff(c_138, plain, (![A_66, B_2]: ('#skF_1'(k1_tarski(A_66), B_2)=A_66 | r1_tarski(k1_tarski(A_66), B_2))), inference(resolution, [status(thm)], [c_6, c_130])).
% 15.50/6.72  tff(c_157, plain, (![C_71, B_72, A_73]: (r2_hidden(C_71, B_72) | ~r2_hidden(C_71, A_73) | ~r1_tarski(A_73, B_72))), inference(cnfTransformation, [status(thm)], [f_32])).
% 15.50/6.72  tff(c_408, plain, (![A_110, B_111, B_112]: (r2_hidden('#skF_1'(A_110, B_111), B_112) | ~r1_tarski(A_110, B_112) | r1_tarski(A_110, B_111))), inference(resolution, [status(thm)], [c_6, c_157])).
% 15.50/6.72  tff(c_447, plain, (![A_113, B_114]: ('#skF_1'(A_113, B_114)='#skF_5' | ~r1_tarski(A_113, '#skF_4') | r1_tarski(A_113, B_114))), inference(resolution, [status(thm)], [c_408, c_42])).
% 15.50/6.72  tff(c_4339, plain, (![A_6679, B_6680]: ('#skF_1'(k1_tarski(A_6679), B_6680)='#skF_5' | r1_tarski(k1_tarski(A_6679), B_6680) | '#skF_1'(k1_tarski(A_6679), '#skF_4')=A_6679)), inference(resolution, [status(thm)], [c_138, c_447])).
% 15.50/6.72  tff(c_49, plain, (![A_48]: (k2_tarski(A_48, A_48)=k1_tarski(A_48))), inference(cnfTransformation, [status(thm)], [f_47])).
% 15.50/6.72  tff(c_12, plain, (![D_13, A_8]: (r2_hidden(D_13, k2_tarski(A_8, D_13)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 15.50/6.72  tff(c_55, plain, (![A_48]: (r2_hidden(A_48, k1_tarski(A_48)))), inference(superposition, [status(thm), theory('equality')], [c_49, c_12])).
% 15.50/6.72  tff(c_170, plain, (![A_48, B_72]: (r2_hidden(A_48, B_72) | ~r1_tarski(k1_tarski(A_48), B_72))), inference(resolution, [status(thm)], [c_55, c_157])).
% 15.50/6.72  tff(c_4460, plain, (![A_6679, B_6680]: (r2_hidden(A_6679, B_6680) | '#skF_1'(k1_tarski(A_6679), B_6680)='#skF_5' | '#skF_1'(k1_tarski(A_6679), '#skF_4')=A_6679)), inference(resolution, [status(thm)], [c_4339, c_170])).
% 15.50/6.72  tff(c_4874, plain, (![A_7235]: (r2_hidden(A_7235, '#skF_4') | '#skF_1'(k1_tarski(A_7235), '#skF_4')='#skF_5' | A_7235!='#skF_5')), inference(factorization, [status(thm), theory('equality')], [c_4460])).
% 15.50/6.72  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 15.50/6.72  tff(c_4895, plain, (![A_7235]: (~r2_hidden('#skF_5', '#skF_4') | r1_tarski(k1_tarski(A_7235), '#skF_4') | r2_hidden(A_7235, '#skF_4') | A_7235!='#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_4874, c_4])).
% 15.50/6.72  tff(c_4997, plain, (![A_7515]: (r1_tarski(k1_tarski(A_7515), '#skF_4') | r2_hidden(A_7515, '#skF_4') | A_7515!='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_141, c_4895])).
% 15.50/6.72  tff(c_5022, plain, (r2_hidden('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_4997, c_170])).
% 15.50/6.72  tff(c_28004, plain, (![A_37281, B_37282, C_37283]: ('#skF_2'(A_37281, B_37282, C_37283)=B_37282 | '#skF_2'(A_37281, B_37282, C_37283)=A_37281 | r2_hidden('#skF_3'(A_37281, B_37282, C_37283), C_37283) | k2_tarski(A_37281, B_37282)=C_37283)), inference(cnfTransformation, [status(thm)], [f_45])).
% 15.50/6.72  tff(c_28821, plain, (![A_38390, B_38391]: ('#skF_3'(A_38390, B_38391, '#skF_4')='#skF_5' | '#skF_2'(A_38390, B_38391, '#skF_4')=B_38391 | '#skF_2'(A_38390, B_38391, '#skF_4')=A_38390 | k2_tarski(A_38390, B_38391)='#skF_4')), inference(resolution, [status(thm)], [c_28004, c_42])).
% 15.50/6.72  tff(c_67429, plain, (![B_67637]: (k1_tarski(B_67637)='#skF_4' | '#skF_3'(B_67637, B_67637, '#skF_4')='#skF_5' | '#skF_2'(B_67637, B_67637, '#skF_4')=B_67637 | '#skF_2'(B_67637, B_67637, '#skF_4')=B_67637)), inference(superposition, [status(thm), theory('equality')], [c_28821, c_28])).
% 15.50/6.72  tff(c_68978, plain, ('#skF_3'('#skF_5', '#skF_5', '#skF_4')='#skF_5' | '#skF_2'('#skF_5', '#skF_5', '#skF_4')='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_67429, c_46])).
% 15.50/6.72  tff(c_68982, plain, ('#skF_2'('#skF_5', '#skF_5', '#skF_4')='#skF_5'), inference(splitLeft, [status(thm)], [c_68978])).
% 15.50/6.72  tff(c_16, plain, (![A_8, B_9, C_10]: (~r2_hidden('#skF_2'(A_8, B_9, C_10), C_10) | '#skF_3'(A_8, B_9, C_10)!=B_9 | k2_tarski(A_8, B_9)=C_10)), inference(cnfTransformation, [status(thm)], [f_45])).
% 15.50/6.72  tff(c_69011, plain, (~r2_hidden('#skF_5', '#skF_4') | '#skF_3'('#skF_5', '#skF_5', '#skF_4')!='#skF_5' | k2_tarski('#skF_5', '#skF_5')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_68982, c_16])).
% 15.50/6.72  tff(c_69380, plain, ('#skF_3'('#skF_5', '#skF_5', '#skF_4')!='#skF_5' | k1_tarski('#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_28, c_5022, c_69011])).
% 15.50/6.72  tff(c_69381, plain, ('#skF_3'('#skF_5', '#skF_5', '#skF_4')!='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_46, c_69380])).
% 15.50/6.72  tff(c_24, plain, (![A_8, B_9, C_10]: (~r2_hidden('#skF_2'(A_8, B_9, C_10), C_10) | r2_hidden('#skF_3'(A_8, B_9, C_10), C_10) | k2_tarski(A_8, B_9)=C_10)), inference(cnfTransformation, [status(thm)], [f_45])).
% 15.50/6.72  tff(c_69008, plain, (~r2_hidden('#skF_5', '#skF_4') | r2_hidden('#skF_3'('#skF_5', '#skF_5', '#skF_4'), '#skF_4') | k2_tarski('#skF_5', '#skF_5')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_68982, c_24])).
% 15.50/6.72  tff(c_69377, plain, (r2_hidden('#skF_3'('#skF_5', '#skF_5', '#skF_4'), '#skF_4') | k1_tarski('#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_28, c_5022, c_69008])).
% 15.50/6.72  tff(c_69378, plain, (r2_hidden('#skF_3'('#skF_5', '#skF_5', '#skF_4'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_46, c_69377])).
% 15.50/6.72  tff(c_69411, plain, ('#skF_3'('#skF_5', '#skF_5', '#skF_4')='#skF_5'), inference(resolution, [status(thm)], [c_69378, c_42])).
% 15.50/6.72  tff(c_69746, plain, $false, inference(negUnitSimplification, [status(thm)], [c_69381, c_69411])).
% 15.50/6.72  tff(c_69747, plain, ('#skF_3'('#skF_5', '#skF_5', '#skF_4')='#skF_5'), inference(splitRight, [status(thm)], [c_68978])).
% 15.50/6.72  tff(c_18, plain, (![A_8, B_9, C_10]: ('#skF_2'(A_8, B_9, C_10)=B_9 | '#skF_2'(A_8, B_9, C_10)=A_8 | '#skF_3'(A_8, B_9, C_10)!=B_9 | k2_tarski(A_8, B_9)=C_10)), inference(cnfTransformation, [status(thm)], [f_45])).
% 15.50/6.72  tff(c_7174, plain, (![B_9, C_10]: ('#skF_3'(B_9, B_9, C_10)!=B_9 | k2_tarski(B_9, B_9)=C_10 | '#skF_2'(B_9, B_9, C_10)=B_9)), inference(factorization, [status(thm), theory('equality')], [c_18])).
% 15.50/6.72  tff(c_25204, plain, (![B_31434, C_31435]: ('#skF_3'(B_31434, B_31434, C_31435)!=B_31434 | k1_tarski(B_31434)=C_31435 | '#skF_2'(B_31434, B_31434, C_31435)=B_31434)), inference(demodulation, [status(thm), theory('equality')], [c_28, c_7174])).
% 15.50/6.72  tff(c_26806, plain, (![C_31435]: (C_31435!='#skF_4' | '#skF_3'('#skF_5', '#skF_5', C_31435)!='#skF_5' | '#skF_2'('#skF_5', '#skF_5', C_31435)='#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_25204, c_46])).
% 15.50/6.72  tff(c_69748, plain, ('#skF_2'('#skF_5', '#skF_5', '#skF_4')!='#skF_5'), inference(splitRight, [status(thm)], [c_68978])).
% 15.50/6.72  tff(c_71062, plain, ('#skF_3'('#skF_5', '#skF_5', '#skF_4')!='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_26806, c_69748])).
% 15.50/6.72  tff(c_71085, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_69747, c_71062])).
% 15.50/6.72  tff(c_71090, plain, (![B_70861]: (r1_tarski('#skF_4', k4_xboole_0(B_70861, '#skF_4')))), inference(splitRight, [status(thm)], [c_96])).
% 15.50/6.72  tff(c_71093, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_71090, c_8])).
% 15.50/6.72  tff(c_71097, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_71093])).
% 15.50/6.72  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.50/6.72  
% 15.50/6.72  Inference rules
% 15.50/6.72  ----------------------
% 15.50/6.72  #Ref     : 5
% 15.50/6.72  #Sup     : 8560
% 15.50/6.72  #Fact    : 28
% 15.50/6.72  #Define  : 0
% 15.50/6.72  #Split   : 6
% 15.50/6.72  #Chain   : 0
% 15.50/6.72  #Close   : 0
% 15.50/6.72  
% 15.50/6.72  Ordering : KBO
% 15.50/6.72  
% 15.50/6.72  Simplification rules
% 15.50/6.72  ----------------------
% 15.50/6.72  #Subsume      : 2468
% 15.50/6.72  #Demod        : 1076
% 15.50/6.72  #Tautology    : 542
% 15.50/6.72  #SimpNegUnit  : 43
% 15.50/6.72  #BackRed      : 0
% 15.50/6.72  
% 15.50/6.72  #Partial instantiations: 22980
% 15.50/6.72  #Strategies tried      : 1
% 15.50/6.72  
% 15.50/6.72  Timing (in seconds)
% 15.50/6.72  ----------------------
% 15.50/6.73  Preprocessing        : 0.32
% 15.50/6.73  Parsing              : 0.16
% 15.50/6.73  CNF conversion       : 0.02
% 15.50/6.73  Main loop            : 5.66
% 15.50/6.73  Inferencing          : 1.74
% 15.50/6.73  Reduction            : 1.09
% 15.50/6.73  Demodulation         : 0.74
% 15.50/6.73  BG Simplification    : 0.21
% 15.50/6.73  Subsumption          : 2.35
% 15.50/6.73  Abstraction          : 0.27
% 15.50/6.73  MUC search           : 0.00
% 15.50/6.73  Cooper               : 0.00
% 15.50/6.73  Total                : 6.01
% 15.50/6.73  Index Insertion      : 0.00
% 15.50/6.73  Index Deletion       : 0.00
% 15.50/6.73  Index Matching       : 0.00
% 15.50/6.73  BG Taut test         : 0.00
%------------------------------------------------------------------------------
