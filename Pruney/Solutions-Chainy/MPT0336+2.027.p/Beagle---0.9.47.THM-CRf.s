%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:04 EST 2020

% Result     : Theorem 11.19s
% Output     : CNFRefutation 11.39s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 117 expanded)
%              Number of leaves         :   31 (  52 expanded)
%              Depth                    :   10
%              Number of atoms          :  118 ( 190 expanded)
%              Number of equality atoms :   39 (  55 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_69,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_67,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_109,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_tarski(k3_xboole_0(A,B),k1_tarski(D))
          & r2_hidden(D,C)
          & r1_xboole_0(C,B) )
       => r1_xboole_0(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_89,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k4_xboole_0(B,C))
     => ( r1_tarski(A,B)
        & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_100,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_85,axiom,(
    ! [A,B,C] :
      ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,B)
          & r1_xboole_0(A,C) )
      & ~ ( ~ ( r1_xboole_0(A,B)
              & r1_xboole_0(A,C) )
          & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_53,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_1760,plain,(
    ! [A_148,B_149] : k4_xboole_0(A_148,k4_xboole_0(A_148,B_149)) = k3_xboole_0(A_148,B_149) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_26,plain,(
    ! [A_17,B_18] : r1_tarski(k4_xboole_0(A_17,B_18),A_17) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_3010,plain,(
    ! [A_169,B_170] : r1_tarski(k3_xboole_0(A_169,B_170),A_169) ),
    inference(superposition,[status(thm),theory(equality)],[c_1760,c_26])).

tff(c_52,plain,(
    r1_xboole_0('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_103,plain,(
    ! [B_40,A_41] :
      ( r1_xboole_0(B_40,A_41)
      | ~ r1_xboole_0(A_41,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_106,plain,(
    r1_xboole_0('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_103])).

tff(c_120,plain,(
    ! [A_44,B_45] :
      ( k4_xboole_0(A_44,B_45) = A_44
      | ~ r1_xboole_0(A_44,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_131,plain,(
    k4_xboole_0('#skF_3','#skF_4') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_106,c_120])).

tff(c_243,plain,(
    ! [A_56,C_57,B_58] :
      ( r1_xboole_0(A_56,C_57)
      | ~ r1_tarski(A_56,k4_xboole_0(B_58,C_57)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_419,plain,(
    ! [A_73] :
      ( r1_xboole_0(A_73,'#skF_4')
      | ~ r1_tarski(A_73,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_131,c_243])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( k3_xboole_0(A_3,B_4) = k1_xboole_0
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_428,plain,(
    ! [A_73] :
      ( k3_xboole_0(A_73,'#skF_4') = k1_xboole_0
      | ~ r1_tarski(A_73,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_419,c_4])).

tff(c_6810,plain,(
    ! [B_270] : k3_xboole_0(k3_xboole_0('#skF_3',B_270),'#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_3010,c_428])).

tff(c_6879,plain,(
    ! [B_270] : k3_xboole_0('#skF_4',k3_xboole_0('#skF_3',B_270)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_6810])).

tff(c_48,plain,(
    ! [A_32,B_33] :
      ( k4_xboole_0(A_32,k1_tarski(B_33)) = A_32
      | r2_hidden(B_33,A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_149,plain,(
    ! [A_46,B_47] :
      ( r1_xboole_0(A_46,B_47)
      | k4_xboole_0(A_46,B_47) != A_46 ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_8,plain,(
    ! [B_6,A_5] :
      ( r1_xboole_0(B_6,A_5)
      | ~ r1_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_227,plain,(
    ! [B_54,A_55] :
      ( r1_xboole_0(B_54,A_55)
      | k4_xboole_0(A_55,B_54) != A_55 ) ),
    inference(resolution,[status(thm)],[c_149,c_8])).

tff(c_14335,plain,(
    ! [B_377,A_378] :
      ( k3_xboole_0(B_377,A_378) = k1_xboole_0
      | k4_xboole_0(A_378,B_377) != A_378 ) ),
    inference(resolution,[status(thm)],[c_227,c_4])).

tff(c_14425,plain,(
    ! [B_33,A_32] :
      ( k3_xboole_0(k1_tarski(B_33),A_32) = k1_xboole_0
      | r2_hidden(B_33,A_32) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_14335])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( r1_xboole_0(A_3,B_4)
      | k3_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2878,plain,(
    ! [A_163,C_164,B_165] :
      ( ~ r1_xboole_0(A_163,C_164)
      | ~ r1_xboole_0(A_163,B_165)
      | r1_xboole_0(A_163,k2_xboole_0(B_165,C_164)) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_5661,plain,(
    ! [B_245,C_246,A_247] :
      ( r1_xboole_0(k2_xboole_0(B_245,C_246),A_247)
      | ~ r1_xboole_0(A_247,C_246)
      | ~ r1_xboole_0(A_247,B_245) ) ),
    inference(resolution,[status(thm)],[c_2878,c_8])).

tff(c_50,plain,(
    ~ r1_xboole_0(k2_xboole_0('#skF_2','#skF_4'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_5682,plain,
    ( ~ r1_xboole_0('#skF_3','#skF_4')
    | ~ r1_xboole_0('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_5661,c_50])).

tff(c_5691,plain,(
    ~ r1_xboole_0('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_5682])).

tff(c_5716,plain,(
    k3_xboole_0('#skF_3','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_5691])).

tff(c_56,plain,(
    r1_tarski(k3_xboole_0('#skF_2','#skF_3'),k1_tarski('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_58,plain,(
    r1_tarski(k3_xboole_0('#skF_3','#skF_2'),k1_tarski('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_56])).

tff(c_3643,plain,(
    ! [A_183,B_184] :
      ( k4_xboole_0(A_183,B_184) = A_183
      | k3_xboole_0(A_183,B_184) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_6,c_120])).

tff(c_22,plain,(
    ! [A_14,C_16,B_15] :
      ( r1_xboole_0(A_14,C_16)
      | ~ r1_tarski(A_14,k4_xboole_0(B_15,C_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_28298,plain,(
    ! [A_592,B_593,A_594] :
      ( r1_xboole_0(A_592,B_593)
      | ~ r1_tarski(A_592,A_594)
      | k3_xboole_0(A_594,B_593) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3643,c_22])).

tff(c_28354,plain,(
    ! [B_595] :
      ( r1_xboole_0(k3_xboole_0('#skF_3','#skF_2'),B_595)
      | k3_xboole_0(k1_tarski('#skF_5'),B_595) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_58,c_28298])).

tff(c_31856,plain,(
    ! [B_621] :
      ( k3_xboole_0(k3_xboole_0('#skF_3','#skF_2'),B_621) = k1_xboole_0
      | k3_xboole_0(k1_tarski('#skF_5'),B_621) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_28354,c_4])).

tff(c_20,plain,(
    ! [B_13] : r1_tarski(B_13,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_261,plain,(
    ! [B_61,C_62] : r1_xboole_0(k4_xboole_0(B_61,C_62),C_62) ),
    inference(resolution,[status(thm)],[c_20,c_243])).

tff(c_281,plain,(
    ! [C_63,B_64] : r1_xboole_0(C_63,k4_xboole_0(B_64,C_63)) ),
    inference(resolution,[status(thm)],[c_261,c_8])).

tff(c_36,plain,(
    ! [A_24,B_25] :
      ( k4_xboole_0(A_24,B_25) = A_24
      | ~ r1_xboole_0(A_24,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_297,plain,(
    ! [C_63,B_64] : k4_xboole_0(C_63,k4_xboole_0(B_64,C_63)) = C_63 ),
    inference(resolution,[status(thm)],[c_281,c_36])).

tff(c_1888,plain,(
    ! [B_149] : k3_xboole_0(B_149,B_149) = B_149 ),
    inference(superposition,[status(thm),theory(equality)],[c_1760,c_297])).

tff(c_32232,plain,
    ( k3_xboole_0('#skF_3','#skF_2') = k1_xboole_0
    | k3_xboole_0(k1_tarski('#skF_5'),k3_xboole_0('#skF_3','#skF_2')) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_31856,c_1888])).

tff(c_32401,plain,(
    k3_xboole_0(k1_tarski('#skF_5'),k3_xboole_0('#skF_3','#skF_2')) != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_5716,c_32232])).

tff(c_32421,plain,(
    r2_hidden('#skF_5',k3_xboole_0('#skF_3','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_14425,c_32401])).

tff(c_54,plain,(
    r2_hidden('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_111,plain,(
    ! [A_42,B_43] :
      ( r1_xboole_0(A_42,B_43)
      | k3_xboole_0(A_42,B_43) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_117,plain,(
    ! [B_43,A_42] :
      ( r1_xboole_0(B_43,A_42)
      | k3_xboole_0(A_42,B_43) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_111,c_8])).

tff(c_2333,plain,(
    ! [A_153,B_154,C_155] :
      ( ~ r1_xboole_0(A_153,B_154)
      | ~ r2_hidden(C_155,B_154)
      | ~ r2_hidden(C_155,A_153) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_25737,plain,(
    ! [C_575,A_576,B_577] :
      ( ~ r2_hidden(C_575,A_576)
      | ~ r2_hidden(C_575,B_577)
      | k3_xboole_0(A_576,B_577) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_117,c_2333])).

tff(c_25749,plain,(
    ! [B_577] :
      ( ~ r2_hidden('#skF_5',B_577)
      | k3_xboole_0('#skF_4',B_577) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_54,c_25737])).

tff(c_32424,plain,(
    k3_xboole_0('#skF_4',k3_xboole_0('#skF_3','#skF_2')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_32421,c_25749])).

tff(c_32454,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6879,c_32424])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:20:09 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.19/4.65  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.19/4.65  
% 11.19/4.65  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.19/4.66  %$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 11.19/4.66  
% 11.19/4.66  %Foreground sorts:
% 11.19/4.66  
% 11.19/4.66  
% 11.19/4.66  %Background operators:
% 11.19/4.66  
% 11.19/4.66  
% 11.19/4.66  %Foreground operators:
% 11.19/4.66  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.19/4.66  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 11.19/4.66  tff(k1_tarski, type, k1_tarski: $i > $i).
% 11.19/4.66  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 11.19/4.66  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 11.19/4.66  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.19/4.66  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 11.19/4.66  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 11.19/4.66  tff('#skF_5', type, '#skF_5': $i).
% 11.19/4.66  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 11.19/4.66  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 11.19/4.66  tff('#skF_2', type, '#skF_2': $i).
% 11.19/4.66  tff('#skF_3', type, '#skF_3': $i).
% 11.19/4.66  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.19/4.66  tff('#skF_4', type, '#skF_4': $i).
% 11.19/4.66  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.19/4.66  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 11.19/4.66  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 11.19/4.66  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 11.19/4.66  
% 11.39/4.67  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 11.39/4.67  tff(f_69, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 11.39/4.67  tff(f_67, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 11.39/4.67  tff(f_109, negated_conjecture, ~(![A, B, C, D]: (((r1_tarski(k3_xboole_0(A, B), k1_tarski(D)) & r2_hidden(D, C)) & r1_xboole_0(C, B)) => r1_xboole_0(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t149_zfmisc_1)).
% 11.39/4.67  tff(f_35, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 11.39/4.67  tff(f_89, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 11.39/4.67  tff(f_65, axiom, (![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_xboole_1)).
% 11.39/4.67  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 11.39/4.67  tff(f_100, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 11.39/4.67  tff(f_85, axiom, (![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_xboole_1)).
% 11.39/4.67  tff(f_59, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 11.39/4.67  tff(f_53, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 11.39/4.67  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 11.39/4.67  tff(c_1760, plain, (![A_148, B_149]: (k4_xboole_0(A_148, k4_xboole_0(A_148, B_149))=k3_xboole_0(A_148, B_149))), inference(cnfTransformation, [status(thm)], [f_69])).
% 11.39/4.67  tff(c_26, plain, (![A_17, B_18]: (r1_tarski(k4_xboole_0(A_17, B_18), A_17))), inference(cnfTransformation, [status(thm)], [f_67])).
% 11.39/4.67  tff(c_3010, plain, (![A_169, B_170]: (r1_tarski(k3_xboole_0(A_169, B_170), A_169))), inference(superposition, [status(thm), theory('equality')], [c_1760, c_26])).
% 11.39/4.67  tff(c_52, plain, (r1_xboole_0('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_109])).
% 11.39/4.67  tff(c_103, plain, (![B_40, A_41]: (r1_xboole_0(B_40, A_41) | ~r1_xboole_0(A_41, B_40))), inference(cnfTransformation, [status(thm)], [f_35])).
% 11.39/4.67  tff(c_106, plain, (r1_xboole_0('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_52, c_103])).
% 11.39/4.67  tff(c_120, plain, (![A_44, B_45]: (k4_xboole_0(A_44, B_45)=A_44 | ~r1_xboole_0(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_89])).
% 11.39/4.67  tff(c_131, plain, (k4_xboole_0('#skF_3', '#skF_4')='#skF_3'), inference(resolution, [status(thm)], [c_106, c_120])).
% 11.39/4.67  tff(c_243, plain, (![A_56, C_57, B_58]: (r1_xboole_0(A_56, C_57) | ~r1_tarski(A_56, k4_xboole_0(B_58, C_57)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 11.39/4.67  tff(c_419, plain, (![A_73]: (r1_xboole_0(A_73, '#skF_4') | ~r1_tarski(A_73, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_131, c_243])).
% 11.39/4.67  tff(c_4, plain, (![A_3, B_4]: (k3_xboole_0(A_3, B_4)=k1_xboole_0 | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 11.39/4.67  tff(c_428, plain, (![A_73]: (k3_xboole_0(A_73, '#skF_4')=k1_xboole_0 | ~r1_tarski(A_73, '#skF_3'))), inference(resolution, [status(thm)], [c_419, c_4])).
% 11.39/4.67  tff(c_6810, plain, (![B_270]: (k3_xboole_0(k3_xboole_0('#skF_3', B_270), '#skF_4')=k1_xboole_0)), inference(resolution, [status(thm)], [c_3010, c_428])).
% 11.39/4.67  tff(c_6879, plain, (![B_270]: (k3_xboole_0('#skF_4', k3_xboole_0('#skF_3', B_270))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_6810])).
% 11.39/4.67  tff(c_48, plain, (![A_32, B_33]: (k4_xboole_0(A_32, k1_tarski(B_33))=A_32 | r2_hidden(B_33, A_32))), inference(cnfTransformation, [status(thm)], [f_100])).
% 11.39/4.67  tff(c_149, plain, (![A_46, B_47]: (r1_xboole_0(A_46, B_47) | k4_xboole_0(A_46, B_47)!=A_46)), inference(cnfTransformation, [status(thm)], [f_89])).
% 11.39/4.67  tff(c_8, plain, (![B_6, A_5]: (r1_xboole_0(B_6, A_5) | ~r1_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 11.39/4.67  tff(c_227, plain, (![B_54, A_55]: (r1_xboole_0(B_54, A_55) | k4_xboole_0(A_55, B_54)!=A_55)), inference(resolution, [status(thm)], [c_149, c_8])).
% 11.39/4.67  tff(c_14335, plain, (![B_377, A_378]: (k3_xboole_0(B_377, A_378)=k1_xboole_0 | k4_xboole_0(A_378, B_377)!=A_378)), inference(resolution, [status(thm)], [c_227, c_4])).
% 11.39/4.67  tff(c_14425, plain, (![B_33, A_32]: (k3_xboole_0(k1_tarski(B_33), A_32)=k1_xboole_0 | r2_hidden(B_33, A_32))), inference(superposition, [status(thm), theory('equality')], [c_48, c_14335])).
% 11.39/4.67  tff(c_6, plain, (![A_3, B_4]: (r1_xboole_0(A_3, B_4) | k3_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 11.39/4.67  tff(c_2878, plain, (![A_163, C_164, B_165]: (~r1_xboole_0(A_163, C_164) | ~r1_xboole_0(A_163, B_165) | r1_xboole_0(A_163, k2_xboole_0(B_165, C_164)))), inference(cnfTransformation, [status(thm)], [f_85])).
% 11.39/4.67  tff(c_5661, plain, (![B_245, C_246, A_247]: (r1_xboole_0(k2_xboole_0(B_245, C_246), A_247) | ~r1_xboole_0(A_247, C_246) | ~r1_xboole_0(A_247, B_245))), inference(resolution, [status(thm)], [c_2878, c_8])).
% 11.39/4.67  tff(c_50, plain, (~r1_xboole_0(k2_xboole_0('#skF_2', '#skF_4'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_109])).
% 11.39/4.67  tff(c_5682, plain, (~r1_xboole_0('#skF_3', '#skF_4') | ~r1_xboole_0('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_5661, c_50])).
% 11.39/4.67  tff(c_5691, plain, (~r1_xboole_0('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_106, c_5682])).
% 11.39/4.67  tff(c_5716, plain, (k3_xboole_0('#skF_3', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_6, c_5691])).
% 11.39/4.67  tff(c_56, plain, (r1_tarski(k3_xboole_0('#skF_2', '#skF_3'), k1_tarski('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_109])).
% 11.39/4.67  tff(c_58, plain, (r1_tarski(k3_xboole_0('#skF_3', '#skF_2'), k1_tarski('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_56])).
% 11.39/4.67  tff(c_3643, plain, (![A_183, B_184]: (k4_xboole_0(A_183, B_184)=A_183 | k3_xboole_0(A_183, B_184)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_120])).
% 11.39/4.67  tff(c_22, plain, (![A_14, C_16, B_15]: (r1_xboole_0(A_14, C_16) | ~r1_tarski(A_14, k4_xboole_0(B_15, C_16)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 11.39/4.67  tff(c_28298, plain, (![A_592, B_593, A_594]: (r1_xboole_0(A_592, B_593) | ~r1_tarski(A_592, A_594) | k3_xboole_0(A_594, B_593)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_3643, c_22])).
% 11.39/4.67  tff(c_28354, plain, (![B_595]: (r1_xboole_0(k3_xboole_0('#skF_3', '#skF_2'), B_595) | k3_xboole_0(k1_tarski('#skF_5'), B_595)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_58, c_28298])).
% 11.39/4.67  tff(c_31856, plain, (![B_621]: (k3_xboole_0(k3_xboole_0('#skF_3', '#skF_2'), B_621)=k1_xboole_0 | k3_xboole_0(k1_tarski('#skF_5'), B_621)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_28354, c_4])).
% 11.39/4.67  tff(c_20, plain, (![B_13]: (r1_tarski(B_13, B_13))), inference(cnfTransformation, [status(thm)], [f_59])).
% 11.39/4.67  tff(c_261, plain, (![B_61, C_62]: (r1_xboole_0(k4_xboole_0(B_61, C_62), C_62))), inference(resolution, [status(thm)], [c_20, c_243])).
% 11.39/4.67  tff(c_281, plain, (![C_63, B_64]: (r1_xboole_0(C_63, k4_xboole_0(B_64, C_63)))), inference(resolution, [status(thm)], [c_261, c_8])).
% 11.39/4.67  tff(c_36, plain, (![A_24, B_25]: (k4_xboole_0(A_24, B_25)=A_24 | ~r1_xboole_0(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_89])).
% 11.39/4.67  tff(c_297, plain, (![C_63, B_64]: (k4_xboole_0(C_63, k4_xboole_0(B_64, C_63))=C_63)), inference(resolution, [status(thm)], [c_281, c_36])).
% 11.39/4.67  tff(c_1888, plain, (![B_149]: (k3_xboole_0(B_149, B_149)=B_149)), inference(superposition, [status(thm), theory('equality')], [c_1760, c_297])).
% 11.39/4.67  tff(c_32232, plain, (k3_xboole_0('#skF_3', '#skF_2')=k1_xboole_0 | k3_xboole_0(k1_tarski('#skF_5'), k3_xboole_0('#skF_3', '#skF_2'))!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_31856, c_1888])).
% 11.39/4.67  tff(c_32401, plain, (k3_xboole_0(k1_tarski('#skF_5'), k3_xboole_0('#skF_3', '#skF_2'))!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_5716, c_32232])).
% 11.39/4.67  tff(c_32421, plain, (r2_hidden('#skF_5', k3_xboole_0('#skF_3', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_14425, c_32401])).
% 11.39/4.67  tff(c_54, plain, (r2_hidden('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_109])).
% 11.39/4.67  tff(c_111, plain, (![A_42, B_43]: (r1_xboole_0(A_42, B_43) | k3_xboole_0(A_42, B_43)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 11.39/4.67  tff(c_117, plain, (![B_43, A_42]: (r1_xboole_0(B_43, A_42) | k3_xboole_0(A_42, B_43)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_111, c_8])).
% 11.39/4.67  tff(c_2333, plain, (![A_153, B_154, C_155]: (~r1_xboole_0(A_153, B_154) | ~r2_hidden(C_155, B_154) | ~r2_hidden(C_155, A_153))), inference(cnfTransformation, [status(thm)], [f_53])).
% 11.39/4.67  tff(c_25737, plain, (![C_575, A_576, B_577]: (~r2_hidden(C_575, A_576) | ~r2_hidden(C_575, B_577) | k3_xboole_0(A_576, B_577)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_117, c_2333])).
% 11.39/4.67  tff(c_25749, plain, (![B_577]: (~r2_hidden('#skF_5', B_577) | k3_xboole_0('#skF_4', B_577)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_54, c_25737])).
% 11.39/4.67  tff(c_32424, plain, (k3_xboole_0('#skF_4', k3_xboole_0('#skF_3', '#skF_2'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_32421, c_25749])).
% 11.39/4.67  tff(c_32454, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6879, c_32424])).
% 11.39/4.67  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.39/4.67  
% 11.39/4.67  Inference rules
% 11.39/4.67  ----------------------
% 11.39/4.67  #Ref     : 0
% 11.39/4.67  #Sup     : 7883
% 11.39/4.67  #Fact    : 0
% 11.39/4.67  #Define  : 0
% 11.39/4.67  #Split   : 6
% 11.39/4.67  #Chain   : 0
% 11.39/4.67  #Close   : 0
% 11.39/4.67  
% 11.39/4.67  Ordering : KBO
% 11.39/4.67  
% 11.39/4.67  Simplification rules
% 11.39/4.67  ----------------------
% 11.39/4.67  #Subsume      : 515
% 11.39/4.67  #Demod        : 7609
% 11.39/4.67  #Tautology    : 5762
% 11.39/4.67  #SimpNegUnit  : 28
% 11.39/4.67  #BackRed      : 1
% 11.39/4.67  
% 11.39/4.67  #Partial instantiations: 0
% 11.39/4.67  #Strategies tried      : 1
% 11.39/4.67  
% 11.39/4.67  Timing (in seconds)
% 11.39/4.67  ----------------------
% 11.39/4.67  Preprocessing        : 0.31
% 11.39/4.67  Parsing              : 0.17
% 11.39/4.67  CNF conversion       : 0.02
% 11.39/4.67  Main loop            : 3.59
% 11.39/4.67  Inferencing          : 0.65
% 11.39/4.67  Reduction            : 1.93
% 11.39/4.67  Demodulation         : 1.63
% 11.39/4.67  BG Simplification    : 0.07
% 11.39/4.67  Subsumption          : 0.74
% 11.39/4.67  Abstraction          : 0.09
% 11.39/4.67  MUC search           : 0.00
% 11.39/4.67  Cooper               : 0.00
% 11.39/4.67  Total                : 3.93
% 11.39/4.67  Index Insertion      : 0.00
% 11.39/4.67  Index Deletion       : 0.00
% 11.39/4.67  Index Matching       : 0.00
% 11.39/4.67  BG Taut test         : 0.00
%------------------------------------------------------------------------------
