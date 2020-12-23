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
% DateTime   : Thu Dec  3 10:04:35 EST 2020

% Result     : Theorem 14.13s
% Output     : CNFRefutation 14.54s
% Verified   : 
% Statistics : Number of formulae       :   53 (  66 expanded)
%              Number of leaves         :   27 (  35 expanded)
%              Depth                    :    8
%              Number of atoms          :   70 ( 105 expanded)
%              Number of equality atoms :   21 (  32 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_91,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r2_hidden(A,k2_relat_1(B))
        <=> k10_relat_1(B,k1_tarski(A)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t142_funct_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),B) = k1_tarski(A)
    <=> ~ r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l33_zfmisc_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_83,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k10_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t173_relat_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k4_xboole_0(B,k1_tarski(C)))
    <=> ( r2_hidden(A,B)
        & A != C ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).

tff(c_52,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_60,plain,
    ( r2_hidden('#skF_4',k2_relat_1('#skF_5'))
    | k10_relat_1('#skF_5',k1_tarski('#skF_4')) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_99,plain,(
    k10_relat_1('#skF_5',k1_tarski('#skF_4')) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_40,plain,(
    ! [A_24,B_25] :
      ( k4_xboole_0(k1_tarski(A_24),B_25) = k1_tarski(A_24)
      | r2_hidden(A_24,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_24,plain,(
    ! [A_7,B_8] :
      ( r2_hidden('#skF_3'(A_7,B_8),A_7)
      | r1_xboole_0(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_88,plain,(
    ! [A_46,B_47] :
      ( r2_hidden('#skF_3'(A_46,B_47),B_47)
      | r1_xboole_0(A_46,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( ~ r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,k4_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_858,plain,(
    ! [A_123,A_124,B_125] :
      ( ~ r2_hidden('#skF_3'(A_123,k4_xboole_0(A_124,B_125)),B_125)
      | r1_xboole_0(A_123,k4_xboole_0(A_124,B_125)) ) ),
    inference(resolution,[status(thm)],[c_88,c_4])).

tff(c_886,plain,(
    ! [A_126,A_127] : r1_xboole_0(A_126,k4_xboole_0(A_127,A_126)) ),
    inference(resolution,[status(thm)],[c_24,c_858])).

tff(c_1018,plain,(
    ! [B_135,A_136] :
      ( r1_xboole_0(B_135,k1_tarski(A_136))
      | r2_hidden(A_136,B_135) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_886])).

tff(c_48,plain,(
    ! [B_30,A_29] :
      ( k10_relat_1(B_30,A_29) = k1_xboole_0
      | ~ r1_xboole_0(k2_relat_1(B_30),A_29)
      | ~ v1_relat_1(B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_36250,plain,(
    ! [B_650,A_651] :
      ( k10_relat_1(B_650,k1_tarski(A_651)) = k1_xboole_0
      | ~ v1_relat_1(B_650)
      | r2_hidden(A_651,k2_relat_1(B_650)) ) ),
    inference(resolution,[status(thm)],[c_1018,c_48])).

tff(c_54,plain,
    ( k10_relat_1('#skF_5',k1_tarski('#skF_4')) = k1_xboole_0
    | ~ r2_hidden('#skF_4',k2_relat_1('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_112,plain,(
    ~ r2_hidden('#skF_4',k2_relat_1('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_99,c_54])).

tff(c_36341,plain,
    ( k10_relat_1('#skF_5',k1_tarski('#skF_4')) = k1_xboole_0
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_36250,c_112])).

tff(c_36372,plain,(
    k10_relat_1('#skF_5',k1_tarski('#skF_4')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_36341])).

tff(c_36374,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_99,c_36372])).

tff(c_36376,plain,(
    k10_relat_1('#skF_5',k1_tarski('#skF_4')) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_36375,plain,(
    r2_hidden('#skF_4',k2_relat_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_36440,plain,(
    ! [B_666,A_667] :
      ( r1_xboole_0(k2_relat_1(B_666),A_667)
      | k10_relat_1(B_666,A_667) != k1_xboole_0
      | ~ v1_relat_1(B_666) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_26,plain,(
    ! [A_12,B_13] :
      ( k4_xboole_0(A_12,B_13) = A_12
      | ~ r1_xboole_0(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_38208,plain,(
    ! [B_756,A_757] :
      ( k4_xboole_0(k2_relat_1(B_756),A_757) = k2_relat_1(B_756)
      | k10_relat_1(B_756,A_757) != k1_xboole_0
      | ~ v1_relat_1(B_756) ) ),
    inference(resolution,[status(thm)],[c_36440,c_26])).

tff(c_44,plain,(
    ! [C_28,B_27] : ~ r2_hidden(C_28,k4_xboole_0(B_27,k1_tarski(C_28))) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_38283,plain,(
    ! [C_758,B_759] :
      ( ~ r2_hidden(C_758,k2_relat_1(B_759))
      | k10_relat_1(B_759,k1_tarski(C_758)) != k1_xboole_0
      | ~ v1_relat_1(B_759) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38208,c_44])).

tff(c_38324,plain,
    ( k10_relat_1('#skF_5',k1_tarski('#skF_4')) != k1_xboole_0
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_36375,c_38283])).

tff(c_38346,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_36376,c_38324])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n001.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 19:21:45 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 14.13/5.65  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 14.54/5.66  
% 14.54/5.66  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 14.54/5.66  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_2 > #skF_4
% 14.54/5.66  
% 14.54/5.66  %Foreground sorts:
% 14.54/5.66  
% 14.54/5.66  
% 14.54/5.66  %Background operators:
% 14.54/5.66  
% 14.54/5.66  
% 14.54/5.66  %Foreground operators:
% 14.54/5.66  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 14.54/5.66  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 14.54/5.66  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 14.54/5.66  tff(k1_tarski, type, k1_tarski: $i > $i).
% 14.54/5.66  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 14.54/5.66  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 14.54/5.66  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 14.54/5.66  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 14.54/5.66  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 14.54/5.66  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 14.54/5.66  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 14.54/5.66  tff('#skF_5', type, '#skF_5': $i).
% 14.54/5.66  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 14.54/5.66  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 14.54/5.66  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 14.54/5.66  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 14.54/5.66  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 14.54/5.66  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 14.54/5.66  tff('#skF_4', type, '#skF_4': $i).
% 14.54/5.66  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 14.54/5.66  
% 14.54/5.67  tff(f_91, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r2_hidden(A, k2_relat_1(B)) <=> ~(k10_relat_1(B, k1_tarski(A)) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t142_funct_1)).
% 14.54/5.67  tff(f_70, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_tarski(A)) <=> ~r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l33_zfmisc_1)).
% 14.54/5.67  tff(f_53, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 14.54/5.67  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 14.54/5.67  tff(f_83, axiom, (![A, B]: (v1_relat_1(B) => ((k10_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t173_relat_1)).
% 14.54/5.67  tff(f_57, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 14.54/5.67  tff(f_77, axiom, (![A, B, C]: (r2_hidden(A, k4_xboole_0(B, k1_tarski(C))) <=> (r2_hidden(A, B) & ~(A = C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 14.54/5.67  tff(c_52, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_91])).
% 14.54/5.67  tff(c_60, plain, (r2_hidden('#skF_4', k2_relat_1('#skF_5')) | k10_relat_1('#skF_5', k1_tarski('#skF_4'))!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_91])).
% 14.54/5.67  tff(c_99, plain, (k10_relat_1('#skF_5', k1_tarski('#skF_4'))!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_60])).
% 14.54/5.67  tff(c_40, plain, (![A_24, B_25]: (k4_xboole_0(k1_tarski(A_24), B_25)=k1_tarski(A_24) | r2_hidden(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_70])).
% 14.54/5.67  tff(c_24, plain, (![A_7, B_8]: (r2_hidden('#skF_3'(A_7, B_8), A_7) | r1_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_53])).
% 14.54/5.67  tff(c_88, plain, (![A_46, B_47]: (r2_hidden('#skF_3'(A_46, B_47), B_47) | r1_xboole_0(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_53])).
% 14.54/5.67  tff(c_4, plain, (![D_6, B_2, A_1]: (~r2_hidden(D_6, B_2) | ~r2_hidden(D_6, k4_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 14.54/5.67  tff(c_858, plain, (![A_123, A_124, B_125]: (~r2_hidden('#skF_3'(A_123, k4_xboole_0(A_124, B_125)), B_125) | r1_xboole_0(A_123, k4_xboole_0(A_124, B_125)))), inference(resolution, [status(thm)], [c_88, c_4])).
% 14.54/5.67  tff(c_886, plain, (![A_126, A_127]: (r1_xboole_0(A_126, k4_xboole_0(A_127, A_126)))), inference(resolution, [status(thm)], [c_24, c_858])).
% 14.54/5.67  tff(c_1018, plain, (![B_135, A_136]: (r1_xboole_0(B_135, k1_tarski(A_136)) | r2_hidden(A_136, B_135))), inference(superposition, [status(thm), theory('equality')], [c_40, c_886])).
% 14.54/5.67  tff(c_48, plain, (![B_30, A_29]: (k10_relat_1(B_30, A_29)=k1_xboole_0 | ~r1_xboole_0(k2_relat_1(B_30), A_29) | ~v1_relat_1(B_30))), inference(cnfTransformation, [status(thm)], [f_83])).
% 14.54/5.67  tff(c_36250, plain, (![B_650, A_651]: (k10_relat_1(B_650, k1_tarski(A_651))=k1_xboole_0 | ~v1_relat_1(B_650) | r2_hidden(A_651, k2_relat_1(B_650)))), inference(resolution, [status(thm)], [c_1018, c_48])).
% 14.54/5.67  tff(c_54, plain, (k10_relat_1('#skF_5', k1_tarski('#skF_4'))=k1_xboole_0 | ~r2_hidden('#skF_4', k2_relat_1('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_91])).
% 14.54/5.67  tff(c_112, plain, (~r2_hidden('#skF_4', k2_relat_1('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_99, c_54])).
% 14.54/5.67  tff(c_36341, plain, (k10_relat_1('#skF_5', k1_tarski('#skF_4'))=k1_xboole_0 | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_36250, c_112])).
% 14.54/5.67  tff(c_36372, plain, (k10_relat_1('#skF_5', k1_tarski('#skF_4'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_52, c_36341])).
% 14.54/5.67  tff(c_36374, plain, $false, inference(negUnitSimplification, [status(thm)], [c_99, c_36372])).
% 14.54/5.67  tff(c_36376, plain, (k10_relat_1('#skF_5', k1_tarski('#skF_4'))=k1_xboole_0), inference(splitRight, [status(thm)], [c_60])).
% 14.54/5.67  tff(c_36375, plain, (r2_hidden('#skF_4', k2_relat_1('#skF_5'))), inference(splitRight, [status(thm)], [c_60])).
% 14.54/5.67  tff(c_36440, plain, (![B_666, A_667]: (r1_xboole_0(k2_relat_1(B_666), A_667) | k10_relat_1(B_666, A_667)!=k1_xboole_0 | ~v1_relat_1(B_666))), inference(cnfTransformation, [status(thm)], [f_83])).
% 14.54/5.67  tff(c_26, plain, (![A_12, B_13]: (k4_xboole_0(A_12, B_13)=A_12 | ~r1_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_57])).
% 14.54/5.67  tff(c_38208, plain, (![B_756, A_757]: (k4_xboole_0(k2_relat_1(B_756), A_757)=k2_relat_1(B_756) | k10_relat_1(B_756, A_757)!=k1_xboole_0 | ~v1_relat_1(B_756))), inference(resolution, [status(thm)], [c_36440, c_26])).
% 14.54/5.67  tff(c_44, plain, (![C_28, B_27]: (~r2_hidden(C_28, k4_xboole_0(B_27, k1_tarski(C_28))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 14.54/5.67  tff(c_38283, plain, (![C_758, B_759]: (~r2_hidden(C_758, k2_relat_1(B_759)) | k10_relat_1(B_759, k1_tarski(C_758))!=k1_xboole_0 | ~v1_relat_1(B_759))), inference(superposition, [status(thm), theory('equality')], [c_38208, c_44])).
% 14.54/5.67  tff(c_38324, plain, (k10_relat_1('#skF_5', k1_tarski('#skF_4'))!=k1_xboole_0 | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_36375, c_38283])).
% 14.54/5.67  tff(c_38346, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_36376, c_38324])).
% 14.54/5.67  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 14.54/5.67  
% 14.54/5.67  Inference rules
% 14.54/5.67  ----------------------
% 14.54/5.67  #Ref     : 14
% 14.54/5.67  #Sup     : 10210
% 14.54/5.67  #Fact    : 0
% 14.54/5.67  #Define  : 0
% 14.54/5.67  #Split   : 2
% 14.54/5.67  #Chain   : 0
% 14.54/5.67  #Close   : 0
% 14.54/5.67  
% 14.54/5.67  Ordering : KBO
% 14.54/5.67  
% 14.54/5.67  Simplification rules
% 14.54/5.67  ----------------------
% 14.54/5.67  #Subsume      : 3828
% 14.54/5.67  #Demod        : 4471
% 14.54/5.67  #Tautology    : 2898
% 14.54/5.67  #SimpNegUnit  : 449
% 14.54/5.67  #BackRed      : 18
% 14.54/5.67  
% 14.54/5.67  #Partial instantiations: 0
% 14.54/5.67  #Strategies tried      : 1
% 14.54/5.67  
% 14.54/5.67  Timing (in seconds)
% 14.54/5.67  ----------------------
% 14.54/5.67  Preprocessing        : 0.32
% 14.54/5.67  Parsing              : 0.17
% 14.54/5.67  CNF conversion       : 0.02
% 14.54/5.67  Main loop            : 4.57
% 14.54/5.67  Inferencing          : 1.05
% 14.54/5.67  Reduction            : 1.89
% 14.54/5.67  Demodulation         : 1.52
% 14.54/5.67  BG Simplification    : 0.13
% 14.54/5.67  Subsumption          : 1.23
% 14.54/5.67  Abstraction          : 0.23
% 14.54/5.67  MUC search           : 0.00
% 14.54/5.67  Cooper               : 0.00
% 14.54/5.67  Total                : 4.92
% 14.54/5.67  Index Insertion      : 0.00
% 14.54/5.67  Index Deletion       : 0.00
% 14.54/5.67  Index Matching       : 0.00
% 14.54/5.67  BG Taut test         : 0.00
%------------------------------------------------------------------------------
