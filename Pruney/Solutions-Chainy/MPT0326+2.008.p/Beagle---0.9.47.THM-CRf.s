%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:29 EST 2020

% Result     : Theorem 2.57s
% Output     : CNFRefutation 2.57s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 142 expanded)
%              Number of leaves         :   29 (  58 expanded)
%              Depth                    :    8
%              Number of atoms          :  112 ( 235 expanded)
%              Number of equality atoms :   43 (  75 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_96,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B,C,D] :
            ( ( r1_tarski(k2_zfmisc_1(A,B),k2_zfmisc_1(C,D))
              | r1_tarski(k2_zfmisc_1(B,A),k2_zfmisc_1(D,C)) )
           => r1_tarski(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_zfmisc_1)).

tff(f_59,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_57,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_51,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k3_xboole_0(B,C))
     => r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_xboole_1)).

tff(f_85,axiom,(
    ! [A,B,C,D] :
      ( r1_tarski(k2_zfmisc_1(A,B),k2_zfmisc_1(C,D))
     => ( k2_zfmisc_1(A,B) = k1_xboole_0
        | ( r1_tarski(A,C)
          & r1_tarski(B,D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_zfmisc_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_71,axiom,(
    ! [A] :
      ( ~ ( ~ r1_xboole_0(A,A)
          & A = k1_xboole_0 )
      & ~ ( A != k1_xboole_0
          & r1_xboole_0(A,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).

tff(c_40,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_20,plain,(
    ! [A_18] : k5_xboole_0(A_18,k1_xboole_0) = A_18 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_18,plain,(
    ! [A_17] : k3_xboole_0(A_17,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_392,plain,(
    ! [A_80,B_81] : k5_xboole_0(A_80,k3_xboole_0(A_80,B_81)) = k4_xboole_0(A_80,B_81) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_401,plain,(
    ! [A_17] : k5_xboole_0(A_17,k1_xboole_0) = k4_xboole_0(A_17,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_392])).

tff(c_404,plain,(
    ! [A_17] : k4_xboole_0(A_17,k1_xboole_0) = A_17 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_401])).

tff(c_10,plain,(
    ! [A_10,B_11] :
      ( r1_tarski(A_10,B_11)
      | k4_xboole_0(A_10,B_11) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_414,plain,(
    ! [A_83,B_84,C_85] :
      ( r1_tarski(A_83,B_84)
      | ~ r1_tarski(A_83,k3_xboole_0(B_84,C_85)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_427,plain,(
    ! [A_86,A_87] :
      ( r1_tarski(A_86,A_87)
      | ~ r1_tarski(A_86,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_414])).

tff(c_430,plain,(
    ! [A_10,A_87] :
      ( r1_tarski(A_10,A_87)
      | k4_xboole_0(A_10,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_10,c_427])).

tff(c_434,plain,(
    ! [A_88,A_89] :
      ( r1_tarski(A_88,A_89)
      | k1_xboole_0 != A_88 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_404,c_430])).

tff(c_36,plain,(
    ~ r1_tarski('#skF_4','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_455,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(resolution,[status(thm)],[c_434,c_36])).

tff(c_170,plain,(
    ! [A_56,B_57] : k5_xboole_0(A_56,k3_xboole_0(A_56,B_57)) = k4_xboole_0(A_56,B_57) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_179,plain,(
    ! [A_17] : k5_xboole_0(A_17,k1_xboole_0) = k4_xboole_0(A_17,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_170])).

tff(c_182,plain,(
    ! [A_17] : k4_xboole_0(A_17,k1_xboole_0) = A_17 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_179])).

tff(c_117,plain,(
    ! [A_43,B_44,C_45] :
      ( r1_tarski(A_43,B_44)
      | ~ r1_tarski(A_43,k3_xboole_0(B_44,C_45)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_126,plain,(
    ! [A_46,A_47] :
      ( r1_tarski(A_46,A_47)
      | ~ r1_tarski(A_46,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_117])).

tff(c_131,plain,(
    ! [A_48,A_49] :
      ( r1_tarski(A_48,A_49)
      | k4_xboole_0(A_48,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_10,c_126])).

tff(c_148,plain,(
    k4_xboole_0('#skF_4',k1_xboole_0) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_131,c_36])).

tff(c_183,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_182,c_148])).

tff(c_38,plain,
    ( r1_tarski(k2_zfmisc_1('#skF_4','#skF_3'),k2_zfmisc_1('#skF_6','#skF_5'))
    | r1_tarski(k2_zfmisc_1('#skF_3','#skF_4'),k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_86,plain,(
    r1_tarski(k2_zfmisc_1('#skF_3','#skF_4'),k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_278,plain,(
    ! [B_69,D_70,A_71,C_72] :
      ( r1_tarski(B_69,D_70)
      | k2_zfmisc_1(A_71,B_69) = k1_xboole_0
      | ~ r1_tarski(k2_zfmisc_1(A_71,B_69),k2_zfmisc_1(C_72,D_70)) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_284,plain,
    ( r1_tarski('#skF_4','#skF_6')
    | k2_zfmisc_1('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_86,c_278])).

tff(c_303,plain,(
    k2_zfmisc_1('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_284])).

tff(c_26,plain,(
    ! [B_21,A_20] :
      ( k1_xboole_0 = B_21
      | k1_xboole_0 = A_20
      | k2_zfmisc_1(A_20,B_21) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_322,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_303,c_26])).

tff(c_329,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_183,c_322])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_149,plain,(
    ! [A_50,B_51,C_52] :
      ( ~ r1_xboole_0(A_50,B_51)
      | ~ r2_hidden(C_52,k3_xboole_0(A_50,B_51)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_156,plain,(
    ! [A_17,C_52] :
      ( ~ r1_xboole_0(A_17,k1_xboole_0)
      | ~ r2_hidden(C_52,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_149])).

tff(c_159,plain,(
    ! [C_53] : ~ r2_hidden(C_53,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_156])).

tff(c_164,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_4,c_159])).

tff(c_339,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_329,c_164])).

tff(c_352,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_339])).

tff(c_353,plain,(
    ! [A_17] : ~ r1_xboole_0(A_17,k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_156])).

tff(c_22,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_355,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_353,c_22])).

tff(c_356,plain,(
    r1_tarski(k2_zfmisc_1('#skF_4','#skF_3'),k2_zfmisc_1('#skF_6','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_551,plain,(
    ! [B_106,D_107,A_108,C_109] :
      ( r1_tarski(B_106,D_107)
      | k2_zfmisc_1(A_108,B_106) = k1_xboole_0
      | ~ r1_tarski(k2_zfmisc_1(A_108,B_106),k2_zfmisc_1(C_109,D_107)) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_575,plain,
    ( r1_tarski('#skF_3','#skF_5')
    | k2_zfmisc_1('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_356,c_551])).

tff(c_580,plain,(
    k2_zfmisc_1('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_575])).

tff(c_594,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_580,c_26])).

tff(c_601,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_455,c_594])).

tff(c_485,plain,(
    ! [A_92,B_93,C_94] :
      ( ~ r1_xboole_0(A_92,B_93)
      | ~ r2_hidden(C_94,k3_xboole_0(A_92,B_93)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_492,plain,(
    ! [A_17,C_94] :
      ( ~ r1_xboole_0(A_17,k1_xboole_0)
      | ~ r2_hidden(C_94,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_485])).

tff(c_495,plain,(
    ! [C_95] : ~ r2_hidden(C_95,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_492])).

tff(c_500,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_4,c_495])).

tff(c_608,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_601,c_500])).

tff(c_626,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_608])).

tff(c_628,plain,(
    k2_zfmisc_1('#skF_4','#skF_3') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_575])).

tff(c_683,plain,(
    ! [A_115,C_116,B_117,D_118] :
      ( r1_tarski(A_115,C_116)
      | k2_zfmisc_1(A_115,B_117) = k1_xboole_0
      | ~ r1_tarski(k2_zfmisc_1(A_115,B_117),k2_zfmisc_1(C_116,D_118)) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_692,plain,
    ( r1_tarski('#skF_4','#skF_6')
    | k2_zfmisc_1('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_356,c_683])).

tff(c_710,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_628,c_36,c_692])).

tff(c_711,plain,(
    ! [A_17] : ~ r1_xboole_0(A_17,k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_492])).

tff(c_725,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_711,c_22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:52:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.57/1.34  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.57/1.35  
% 2.57/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.57/1.35  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2
% 2.57/1.35  
% 2.57/1.35  %Foreground sorts:
% 2.57/1.35  
% 2.57/1.35  
% 2.57/1.35  %Background operators:
% 2.57/1.35  
% 2.57/1.35  
% 2.57/1.35  %Foreground operators:
% 2.57/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.57/1.35  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.57/1.35  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.57/1.35  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.57/1.35  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.57/1.35  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.57/1.35  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.57/1.35  tff('#skF_5', type, '#skF_5': $i).
% 2.57/1.35  tff('#skF_6', type, '#skF_6': $i).
% 2.57/1.35  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.57/1.35  tff('#skF_3', type, '#skF_3': $i).
% 2.57/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.57/1.35  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.57/1.35  tff('#skF_4', type, '#skF_4': $i).
% 2.57/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.57/1.35  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.57/1.35  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.57/1.35  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.57/1.35  
% 2.57/1.36  tff(f_96, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B, C, D]: ((r1_tarski(k2_zfmisc_1(A, B), k2_zfmisc_1(C, D)) | r1_tarski(k2_zfmisc_1(B, A), k2_zfmisc_1(D, C))) => r1_tarski(B, D))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t139_zfmisc_1)).
% 2.57/1.36  tff(f_59, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 2.57/1.36  tff(f_57, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 2.57/1.36  tff(f_51, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.57/1.36  tff(f_49, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.57/1.36  tff(f_55, axiom, (![A, B, C]: (r1_tarski(A, k3_xboole_0(B, C)) => r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_xboole_1)).
% 2.57/1.36  tff(f_85, axiom, (![A, B, C, D]: (r1_tarski(k2_zfmisc_1(A, B), k2_zfmisc_1(C, D)) => ((k2_zfmisc_1(A, B) = k1_xboole_0) | (r1_tarski(A, C) & r1_tarski(B, D))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t138_zfmisc_1)).
% 2.57/1.36  tff(f_77, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.57/1.36  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.57/1.36  tff(f_45, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.57/1.36  tff(f_71, axiom, (![A]: (~(~r1_xboole_0(A, A) & (A = k1_xboole_0)) & ~(~(A = k1_xboole_0) & r1_xboole_0(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_xboole_1)).
% 2.57/1.36  tff(c_40, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.57/1.36  tff(c_20, plain, (![A_18]: (k5_xboole_0(A_18, k1_xboole_0)=A_18)), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.57/1.36  tff(c_18, plain, (![A_17]: (k3_xboole_0(A_17, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.57/1.36  tff(c_392, plain, (![A_80, B_81]: (k5_xboole_0(A_80, k3_xboole_0(A_80, B_81))=k4_xboole_0(A_80, B_81))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.57/1.36  tff(c_401, plain, (![A_17]: (k5_xboole_0(A_17, k1_xboole_0)=k4_xboole_0(A_17, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_18, c_392])).
% 2.57/1.36  tff(c_404, plain, (![A_17]: (k4_xboole_0(A_17, k1_xboole_0)=A_17)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_401])).
% 2.57/1.36  tff(c_10, plain, (![A_10, B_11]: (r1_tarski(A_10, B_11) | k4_xboole_0(A_10, B_11)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.57/1.36  tff(c_414, plain, (![A_83, B_84, C_85]: (r1_tarski(A_83, B_84) | ~r1_tarski(A_83, k3_xboole_0(B_84, C_85)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.57/1.36  tff(c_427, plain, (![A_86, A_87]: (r1_tarski(A_86, A_87) | ~r1_tarski(A_86, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_18, c_414])).
% 2.57/1.36  tff(c_430, plain, (![A_10, A_87]: (r1_tarski(A_10, A_87) | k4_xboole_0(A_10, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_427])).
% 2.57/1.36  tff(c_434, plain, (![A_88, A_89]: (r1_tarski(A_88, A_89) | k1_xboole_0!=A_88)), inference(demodulation, [status(thm), theory('equality')], [c_404, c_430])).
% 2.57/1.36  tff(c_36, plain, (~r1_tarski('#skF_4', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.57/1.36  tff(c_455, plain, (k1_xboole_0!='#skF_4'), inference(resolution, [status(thm)], [c_434, c_36])).
% 2.57/1.36  tff(c_170, plain, (![A_56, B_57]: (k5_xboole_0(A_56, k3_xboole_0(A_56, B_57))=k4_xboole_0(A_56, B_57))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.57/1.36  tff(c_179, plain, (![A_17]: (k5_xboole_0(A_17, k1_xboole_0)=k4_xboole_0(A_17, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_18, c_170])).
% 2.57/1.36  tff(c_182, plain, (![A_17]: (k4_xboole_0(A_17, k1_xboole_0)=A_17)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_179])).
% 2.57/1.36  tff(c_117, plain, (![A_43, B_44, C_45]: (r1_tarski(A_43, B_44) | ~r1_tarski(A_43, k3_xboole_0(B_44, C_45)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.57/1.36  tff(c_126, plain, (![A_46, A_47]: (r1_tarski(A_46, A_47) | ~r1_tarski(A_46, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_18, c_117])).
% 2.57/1.36  tff(c_131, plain, (![A_48, A_49]: (r1_tarski(A_48, A_49) | k4_xboole_0(A_48, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_126])).
% 2.57/1.36  tff(c_148, plain, (k4_xboole_0('#skF_4', k1_xboole_0)!=k1_xboole_0), inference(resolution, [status(thm)], [c_131, c_36])).
% 2.57/1.36  tff(c_183, plain, (k1_xboole_0!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_182, c_148])).
% 2.57/1.36  tff(c_38, plain, (r1_tarski(k2_zfmisc_1('#skF_4', '#skF_3'), k2_zfmisc_1('#skF_6', '#skF_5')) | r1_tarski(k2_zfmisc_1('#skF_3', '#skF_4'), k2_zfmisc_1('#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.57/1.36  tff(c_86, plain, (r1_tarski(k2_zfmisc_1('#skF_3', '#skF_4'), k2_zfmisc_1('#skF_5', '#skF_6'))), inference(splitLeft, [status(thm)], [c_38])).
% 2.57/1.36  tff(c_278, plain, (![B_69, D_70, A_71, C_72]: (r1_tarski(B_69, D_70) | k2_zfmisc_1(A_71, B_69)=k1_xboole_0 | ~r1_tarski(k2_zfmisc_1(A_71, B_69), k2_zfmisc_1(C_72, D_70)))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.57/1.36  tff(c_284, plain, (r1_tarski('#skF_4', '#skF_6') | k2_zfmisc_1('#skF_3', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_86, c_278])).
% 2.57/1.36  tff(c_303, plain, (k2_zfmisc_1('#skF_3', '#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_36, c_284])).
% 2.57/1.36  tff(c_26, plain, (![B_21, A_20]: (k1_xboole_0=B_21 | k1_xboole_0=A_20 | k2_zfmisc_1(A_20, B_21)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.57/1.36  tff(c_322, plain, (k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_303, c_26])).
% 2.57/1.36  tff(c_329, plain, (k1_xboole_0='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_183, c_322])).
% 2.57/1.36  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.57/1.36  tff(c_149, plain, (![A_50, B_51, C_52]: (~r1_xboole_0(A_50, B_51) | ~r2_hidden(C_52, k3_xboole_0(A_50, B_51)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.57/1.36  tff(c_156, plain, (![A_17, C_52]: (~r1_xboole_0(A_17, k1_xboole_0) | ~r2_hidden(C_52, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_18, c_149])).
% 2.57/1.36  tff(c_159, plain, (![C_53]: (~r2_hidden(C_53, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_156])).
% 2.57/1.36  tff(c_164, plain, (v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_159])).
% 2.57/1.36  tff(c_339, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_329, c_164])).
% 2.57/1.36  tff(c_352, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_339])).
% 2.57/1.36  tff(c_353, plain, (![A_17]: (~r1_xboole_0(A_17, k1_xboole_0))), inference(splitRight, [status(thm)], [c_156])).
% 2.57/1.36  tff(c_22, plain, (r1_xboole_0(k1_xboole_0, k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.57/1.36  tff(c_355, plain, $false, inference(negUnitSimplification, [status(thm)], [c_353, c_22])).
% 2.57/1.36  tff(c_356, plain, (r1_tarski(k2_zfmisc_1('#skF_4', '#skF_3'), k2_zfmisc_1('#skF_6', '#skF_5'))), inference(splitRight, [status(thm)], [c_38])).
% 2.57/1.36  tff(c_551, plain, (![B_106, D_107, A_108, C_109]: (r1_tarski(B_106, D_107) | k2_zfmisc_1(A_108, B_106)=k1_xboole_0 | ~r1_tarski(k2_zfmisc_1(A_108, B_106), k2_zfmisc_1(C_109, D_107)))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.57/1.36  tff(c_575, plain, (r1_tarski('#skF_3', '#skF_5') | k2_zfmisc_1('#skF_4', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_356, c_551])).
% 2.57/1.36  tff(c_580, plain, (k2_zfmisc_1('#skF_4', '#skF_3')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_575])).
% 2.57/1.36  tff(c_594, plain, (k1_xboole_0='#skF_3' | k1_xboole_0='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_580, c_26])).
% 2.57/1.36  tff(c_601, plain, (k1_xboole_0='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_455, c_594])).
% 2.57/1.36  tff(c_485, plain, (![A_92, B_93, C_94]: (~r1_xboole_0(A_92, B_93) | ~r2_hidden(C_94, k3_xboole_0(A_92, B_93)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.57/1.36  tff(c_492, plain, (![A_17, C_94]: (~r1_xboole_0(A_17, k1_xboole_0) | ~r2_hidden(C_94, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_18, c_485])).
% 2.57/1.36  tff(c_495, plain, (![C_95]: (~r2_hidden(C_95, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_492])).
% 2.57/1.36  tff(c_500, plain, (v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_495])).
% 2.57/1.36  tff(c_608, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_601, c_500])).
% 2.57/1.36  tff(c_626, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_608])).
% 2.57/1.36  tff(c_628, plain, (k2_zfmisc_1('#skF_4', '#skF_3')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_575])).
% 2.57/1.36  tff(c_683, plain, (![A_115, C_116, B_117, D_118]: (r1_tarski(A_115, C_116) | k2_zfmisc_1(A_115, B_117)=k1_xboole_0 | ~r1_tarski(k2_zfmisc_1(A_115, B_117), k2_zfmisc_1(C_116, D_118)))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.57/1.36  tff(c_692, plain, (r1_tarski('#skF_4', '#skF_6') | k2_zfmisc_1('#skF_4', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_356, c_683])).
% 2.57/1.36  tff(c_710, plain, $false, inference(negUnitSimplification, [status(thm)], [c_628, c_36, c_692])).
% 2.57/1.36  tff(c_711, plain, (![A_17]: (~r1_xboole_0(A_17, k1_xboole_0))), inference(splitRight, [status(thm)], [c_492])).
% 2.57/1.36  tff(c_725, plain, $false, inference(negUnitSimplification, [status(thm)], [c_711, c_22])).
% 2.57/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.57/1.36  
% 2.57/1.36  Inference rules
% 2.57/1.36  ----------------------
% 2.57/1.36  #Ref     : 0
% 2.57/1.36  #Sup     : 141
% 2.57/1.36  #Fact    : 0
% 2.57/1.36  #Define  : 0
% 2.57/1.36  #Split   : 4
% 2.57/1.36  #Chain   : 0
% 2.57/1.36  #Close   : 0
% 2.57/1.36  
% 2.57/1.36  Ordering : KBO
% 2.57/1.36  
% 2.57/1.36  Simplification rules
% 2.57/1.36  ----------------------
% 2.57/1.36  #Subsume      : 16
% 2.57/1.36  #Demod        : 102
% 2.57/1.36  #Tautology    : 83
% 2.57/1.36  #SimpNegUnit  : 10
% 2.57/1.36  #BackRed      : 50
% 2.57/1.36  
% 2.57/1.36  #Partial instantiations: 0
% 2.57/1.36  #Strategies tried      : 1
% 2.57/1.36  
% 2.57/1.36  Timing (in seconds)
% 2.57/1.36  ----------------------
% 2.57/1.37  Preprocessing        : 0.29
% 2.57/1.37  Parsing              : 0.16
% 2.57/1.37  CNF conversion       : 0.02
% 2.57/1.37  Main loop            : 0.30
% 2.57/1.37  Inferencing          : 0.11
% 2.57/1.37  Reduction            : 0.09
% 2.57/1.37  Demodulation         : 0.06
% 2.57/1.37  BG Simplification    : 0.02
% 2.57/1.37  Subsumption          : 0.06
% 2.57/1.37  Abstraction          : 0.01
% 2.57/1.37  MUC search           : 0.00
% 2.57/1.37  Cooper               : 0.00
% 2.57/1.37  Total                : 0.62
% 2.57/1.37  Index Insertion      : 0.00
% 2.57/1.37  Index Deletion       : 0.00
% 2.57/1.37  Index Matching       : 0.00
% 2.57/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
