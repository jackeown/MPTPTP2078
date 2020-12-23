%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:38 EST 2020

% Result     : Theorem 3.44s
% Output     : CNFRefutation 3.44s
% Verified   : 
% Statistics : Number of formulae       :   52 (  68 expanded)
%              Number of leaves         :   22 (  33 expanded)
%              Depth                    :    9
%              Number of atoms          :   79 ( 124 expanded)
%              Number of equality atoms :   26 (  39 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k1_enumset1 > k4_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_77,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r2_hidden(A,k2_relat_1(B))
        <=> k10_relat_1(B,k1_tarski(A)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t142_funct_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_69,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k10_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t173_relat_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k4_xboole_0(B,k1_tarski(C)))
    <=> ( r2_hidden(A,B)
        & A != C ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).

tff(c_28,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_36,plain,
    ( r2_hidden('#skF_2',k2_relat_1('#skF_3'))
    | k10_relat_1('#skF_3',k1_tarski('#skF_2')) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_69,plain,(
    k10_relat_1('#skF_3',k1_tarski('#skF_2')) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_16,plain,(
    ! [A_11,B_12] :
      ( r1_xboole_0(k1_tarski(A_11),B_12)
      | r2_hidden(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_58,plain,(
    ! [A_27,B_28] :
      ( k4_xboole_0(A_27,B_28) = A_27
      | ~ r1_xboole_0(A_27,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_66,plain,(
    ! [A_11,B_12] :
      ( k4_xboole_0(k1_tarski(A_11),B_12) = k1_tarski(A_11)
      | r2_hidden(A_11,B_12) ) ),
    inference(resolution,[status(thm)],[c_16,c_58])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( r1_xboole_0(A_6,B_7)
      | k4_xboole_0(A_6,B_7) != A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_70,plain,(
    ! [A_33,B_34,C_35] :
      ( ~ r1_xboole_0(A_33,B_34)
      | ~ r2_hidden(C_35,B_34)
      | ~ r2_hidden(C_35,A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_158,plain,(
    ! [C_53,B_54,A_55] :
      ( ~ r2_hidden(C_53,B_54)
      | ~ r2_hidden(C_53,A_55)
      | k4_xboole_0(A_55,B_54) != A_55 ) ),
    inference(resolution,[status(thm)],[c_10,c_70])).

tff(c_564,plain,(
    ! [A_92,B_93,A_94] :
      ( ~ r2_hidden('#skF_1'(A_92,B_93),A_94)
      | k4_xboole_0(A_94,A_92) != A_94
      | r1_xboole_0(A_92,B_93) ) ),
    inference(resolution,[status(thm)],[c_6,c_158])).

tff(c_617,plain,(
    ! [B_95,A_96] :
      ( k4_xboole_0(B_95,A_96) != B_95
      | r1_xboole_0(A_96,B_95) ) ),
    inference(resolution,[status(thm)],[c_4,c_564])).

tff(c_24,plain,(
    ! [B_17,A_16] :
      ( k10_relat_1(B_17,A_16) = k1_xboole_0
      | ~ r1_xboole_0(k2_relat_1(B_17),A_16)
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_930,plain,(
    ! [B_115,B_116] :
      ( k10_relat_1(B_115,B_116) = k1_xboole_0
      | ~ v1_relat_1(B_115)
      | k4_xboole_0(B_116,k2_relat_1(B_115)) != B_116 ) ),
    inference(resolution,[status(thm)],[c_617,c_24])).

tff(c_947,plain,(
    ! [B_119,A_120] :
      ( k10_relat_1(B_119,k1_tarski(A_120)) = k1_xboole_0
      | ~ v1_relat_1(B_119)
      | r2_hidden(A_120,k2_relat_1(B_119)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_930])).

tff(c_30,plain,
    ( k10_relat_1('#skF_3',k1_tarski('#skF_2')) = k1_xboole_0
    | ~ r2_hidden('#skF_2',k2_relat_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_88,plain,(
    ~ r2_hidden('#skF_2',k2_relat_1('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_69,c_30])).

tff(c_971,plain,
    ( k10_relat_1('#skF_3',k1_tarski('#skF_2')) = k1_xboole_0
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_947,c_88])).

tff(c_982,plain,(
    k10_relat_1('#skF_3',k1_tarski('#skF_2')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_971])).

tff(c_984,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_69,c_982])).

tff(c_986,plain,(
    k10_relat_1('#skF_3',k1_tarski('#skF_2')) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_985,plain,(
    r2_hidden('#skF_2',k2_relat_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_1011,plain,(
    ! [B_127,A_128] :
      ( r1_xboole_0(k2_relat_1(B_127),A_128)
      | k10_relat_1(B_127,A_128) != k1_xboole_0
      | ~ v1_relat_1(B_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( k4_xboole_0(A_6,B_7) = A_6
      | ~ r1_xboole_0(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1145,plain,(
    ! [B_152,A_153] :
      ( k4_xboole_0(k2_relat_1(B_152),A_153) = k2_relat_1(B_152)
      | k10_relat_1(B_152,A_153) != k1_xboole_0
      | ~ v1_relat_1(B_152) ) ),
    inference(resolution,[status(thm)],[c_1011,c_8])).

tff(c_20,plain,(
    ! [C_15,B_14] : ~ r2_hidden(C_15,k4_xboole_0(B_14,k1_tarski(C_15))) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1171,plain,(
    ! [C_154,B_155] :
      ( ~ r2_hidden(C_154,k2_relat_1(B_155))
      | k10_relat_1(B_155,k1_tarski(C_154)) != k1_xboole_0
      | ~ v1_relat_1(B_155) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1145,c_20])).

tff(c_1180,plain,
    ( k10_relat_1('#skF_3',k1_tarski('#skF_2')) != k1_xboole_0
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_985,c_1171])).

tff(c_1198,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_986,c_1180])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.11  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.31  % Computer   : n009.cluster.edu
% 0.11/0.31  % Model      : x86_64 x86_64
% 0.11/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.31  % Memory     : 8042.1875MB
% 0.11/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.31  % CPULimit   : 60
% 0.11/0.31  % DateTime   : Tue Dec  1 17:42:26 EST 2020
% 0.11/0.31  % CPUTime    : 
% 0.16/0.32  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.44/1.57  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.44/1.57  
% 3.44/1.57  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.44/1.58  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k1_enumset1 > k4_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.44/1.58  
% 3.44/1.58  %Foreground sorts:
% 3.44/1.58  
% 3.44/1.58  
% 3.44/1.58  %Background operators:
% 3.44/1.58  
% 3.44/1.58  
% 3.44/1.58  %Foreground operators:
% 3.44/1.58  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.44/1.58  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.44/1.58  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.44/1.58  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.44/1.58  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.44/1.58  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.44/1.58  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.44/1.58  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.44/1.58  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.44/1.58  tff('#skF_2', type, '#skF_2': $i).
% 3.44/1.58  tff('#skF_3', type, '#skF_3': $i).
% 3.44/1.58  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.44/1.58  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.44/1.58  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.44/1.58  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.44/1.58  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.44/1.58  
% 3.44/1.59  tff(f_77, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r2_hidden(A, k2_relat_1(B)) <=> ~(k10_relat_1(B, k1_tarski(A)) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t142_funct_1)).
% 3.44/1.59  tff(f_56, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 3.44/1.59  tff(f_47, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 3.44/1.59  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 3.44/1.59  tff(f_69, axiom, (![A, B]: (v1_relat_1(B) => ((k10_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t173_relat_1)).
% 3.44/1.59  tff(f_63, axiom, (![A, B, C]: (r2_hidden(A, k4_xboole_0(B, k1_tarski(C))) <=> (r2_hidden(A, B) & ~(A = C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 3.44/1.59  tff(c_28, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.44/1.59  tff(c_36, plain, (r2_hidden('#skF_2', k2_relat_1('#skF_3')) | k10_relat_1('#skF_3', k1_tarski('#skF_2'))!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.44/1.59  tff(c_69, plain, (k10_relat_1('#skF_3', k1_tarski('#skF_2'))!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_36])).
% 3.44/1.59  tff(c_16, plain, (![A_11, B_12]: (r1_xboole_0(k1_tarski(A_11), B_12) | r2_hidden(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.44/1.59  tff(c_58, plain, (![A_27, B_28]: (k4_xboole_0(A_27, B_28)=A_27 | ~r1_xboole_0(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.44/1.59  tff(c_66, plain, (![A_11, B_12]: (k4_xboole_0(k1_tarski(A_11), B_12)=k1_tarski(A_11) | r2_hidden(A_11, B_12))), inference(resolution, [status(thm)], [c_16, c_58])).
% 3.44/1.59  tff(c_4, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.44/1.59  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.44/1.59  tff(c_10, plain, (![A_6, B_7]: (r1_xboole_0(A_6, B_7) | k4_xboole_0(A_6, B_7)!=A_6)), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.44/1.59  tff(c_70, plain, (![A_33, B_34, C_35]: (~r1_xboole_0(A_33, B_34) | ~r2_hidden(C_35, B_34) | ~r2_hidden(C_35, A_33))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.44/1.59  tff(c_158, plain, (![C_53, B_54, A_55]: (~r2_hidden(C_53, B_54) | ~r2_hidden(C_53, A_55) | k4_xboole_0(A_55, B_54)!=A_55)), inference(resolution, [status(thm)], [c_10, c_70])).
% 3.44/1.59  tff(c_564, plain, (![A_92, B_93, A_94]: (~r2_hidden('#skF_1'(A_92, B_93), A_94) | k4_xboole_0(A_94, A_92)!=A_94 | r1_xboole_0(A_92, B_93))), inference(resolution, [status(thm)], [c_6, c_158])).
% 3.44/1.59  tff(c_617, plain, (![B_95, A_96]: (k4_xboole_0(B_95, A_96)!=B_95 | r1_xboole_0(A_96, B_95))), inference(resolution, [status(thm)], [c_4, c_564])).
% 3.44/1.59  tff(c_24, plain, (![B_17, A_16]: (k10_relat_1(B_17, A_16)=k1_xboole_0 | ~r1_xboole_0(k2_relat_1(B_17), A_16) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.44/1.59  tff(c_930, plain, (![B_115, B_116]: (k10_relat_1(B_115, B_116)=k1_xboole_0 | ~v1_relat_1(B_115) | k4_xboole_0(B_116, k2_relat_1(B_115))!=B_116)), inference(resolution, [status(thm)], [c_617, c_24])).
% 3.44/1.59  tff(c_947, plain, (![B_119, A_120]: (k10_relat_1(B_119, k1_tarski(A_120))=k1_xboole_0 | ~v1_relat_1(B_119) | r2_hidden(A_120, k2_relat_1(B_119)))), inference(superposition, [status(thm), theory('equality')], [c_66, c_930])).
% 3.44/1.59  tff(c_30, plain, (k10_relat_1('#skF_3', k1_tarski('#skF_2'))=k1_xboole_0 | ~r2_hidden('#skF_2', k2_relat_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.44/1.59  tff(c_88, plain, (~r2_hidden('#skF_2', k2_relat_1('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_69, c_30])).
% 3.44/1.59  tff(c_971, plain, (k10_relat_1('#skF_3', k1_tarski('#skF_2'))=k1_xboole_0 | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_947, c_88])).
% 3.44/1.59  tff(c_982, plain, (k10_relat_1('#skF_3', k1_tarski('#skF_2'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_28, c_971])).
% 3.44/1.59  tff(c_984, plain, $false, inference(negUnitSimplification, [status(thm)], [c_69, c_982])).
% 3.44/1.59  tff(c_986, plain, (k10_relat_1('#skF_3', k1_tarski('#skF_2'))=k1_xboole_0), inference(splitRight, [status(thm)], [c_36])).
% 3.44/1.59  tff(c_985, plain, (r2_hidden('#skF_2', k2_relat_1('#skF_3'))), inference(splitRight, [status(thm)], [c_36])).
% 3.44/1.59  tff(c_1011, plain, (![B_127, A_128]: (r1_xboole_0(k2_relat_1(B_127), A_128) | k10_relat_1(B_127, A_128)!=k1_xboole_0 | ~v1_relat_1(B_127))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.44/1.59  tff(c_8, plain, (![A_6, B_7]: (k4_xboole_0(A_6, B_7)=A_6 | ~r1_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.44/1.59  tff(c_1145, plain, (![B_152, A_153]: (k4_xboole_0(k2_relat_1(B_152), A_153)=k2_relat_1(B_152) | k10_relat_1(B_152, A_153)!=k1_xboole_0 | ~v1_relat_1(B_152))), inference(resolution, [status(thm)], [c_1011, c_8])).
% 3.44/1.59  tff(c_20, plain, (![C_15, B_14]: (~r2_hidden(C_15, k4_xboole_0(B_14, k1_tarski(C_15))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.44/1.59  tff(c_1171, plain, (![C_154, B_155]: (~r2_hidden(C_154, k2_relat_1(B_155)) | k10_relat_1(B_155, k1_tarski(C_154))!=k1_xboole_0 | ~v1_relat_1(B_155))), inference(superposition, [status(thm), theory('equality')], [c_1145, c_20])).
% 3.44/1.59  tff(c_1180, plain, (k10_relat_1('#skF_3', k1_tarski('#skF_2'))!=k1_xboole_0 | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_985, c_1171])).
% 3.44/1.59  tff(c_1198, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_986, c_1180])).
% 3.44/1.59  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.44/1.59  
% 3.44/1.59  Inference rules
% 3.44/1.59  ----------------------
% 3.44/1.59  #Ref     : 0
% 3.44/1.59  #Sup     : 288
% 3.44/1.59  #Fact    : 0
% 3.44/1.59  #Define  : 0
% 3.44/1.59  #Split   : 1
% 3.44/1.59  #Chain   : 0
% 3.44/1.59  #Close   : 0
% 3.44/1.59  
% 3.44/1.59  Ordering : KBO
% 3.44/1.59  
% 3.44/1.59  Simplification rules
% 3.44/1.59  ----------------------
% 3.44/1.59  #Subsume      : 67
% 3.44/1.59  #Demod        : 7
% 3.44/1.59  #Tautology    : 73
% 3.44/1.59  #SimpNegUnit  : 2
% 3.44/1.59  #BackRed      : 0
% 3.44/1.59  
% 3.44/1.59  #Partial instantiations: 0
% 3.44/1.59  #Strategies tried      : 1
% 3.44/1.59  
% 3.44/1.59  Timing (in seconds)
% 3.44/1.59  ----------------------
% 3.44/1.59  Preprocessing        : 0.33
% 3.44/1.59  Parsing              : 0.18
% 3.44/1.59  CNF conversion       : 0.02
% 3.44/1.59  Main loop            : 0.48
% 3.44/1.59  Inferencing          : 0.19
% 3.44/1.59  Reduction            : 0.11
% 3.44/1.59  Demodulation         : 0.06
% 3.44/1.59  BG Simplification    : 0.03
% 3.44/1.59  Subsumption          : 0.11
% 3.44/1.60  Abstraction          : 0.03
% 3.44/1.60  MUC search           : 0.00
% 3.44/1.60  Cooper               : 0.00
% 3.44/1.60  Total                : 0.85
% 3.44/1.60  Index Insertion      : 0.00
% 3.44/1.60  Index Deletion       : 0.00
% 3.44/1.60  Index Matching       : 0.00
% 3.44/1.60  BG Taut test         : 0.00
%------------------------------------------------------------------------------
