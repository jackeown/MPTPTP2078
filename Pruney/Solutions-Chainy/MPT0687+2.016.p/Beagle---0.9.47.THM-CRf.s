%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:35 EST 2020

% Result     : Theorem 2.65s
% Output     : CNFRefutation 2.65s
% Verified   : 
% Statistics : Number of formulae       :   54 (  69 expanded)
%              Number of leaves         :   27 (  36 expanded)
%              Depth                    :    9
%              Number of atoms          :   71 ( 110 expanded)
%              Number of equality atoms :   17 (  27 expanded)
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

tff(f_89,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r2_hidden(A,k2_relat_1(B))
        <=> k10_relat_1(B,k1_tarski(A)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t142_funct_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),B) = k1_tarski(A)
    <=> ~ r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l33_zfmisc_1)).

tff(f_57,axiom,(
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

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_81,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k10_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t173_relat_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),B)
        & r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l24_zfmisc_1)).

tff(c_46,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_48,plain,
    ( k10_relat_1('#skF_5',k1_tarski('#skF_4')) = k1_xboole_0
    | ~ r2_hidden('#skF_4',k2_relat_1('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_99,plain,(
    ~ r2_hidden('#skF_4',k2_relat_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_54,plain,
    ( r2_hidden('#skF_4',k2_relat_1('#skF_5'))
    | k10_relat_1('#skF_5',k1_tarski('#skF_4')) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_124,plain,(
    k10_relat_1('#skF_5',k1_tarski('#skF_4')) != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_99,c_54])).

tff(c_40,plain,(
    ! [A_26,B_27] :
      ( k4_xboole_0(k1_tarski(A_26),B_27) = k1_tarski(A_26)
      | r2_hidden(A_26,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_24,plain,(
    ! [A_9,B_10] :
      ( r2_hidden('#skF_3'(A_9,B_10),B_10)
      | r1_xboole_0(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_88,plain,(
    ! [A_45,B_46] :
      ( r2_hidden('#skF_3'(A_45,B_46),A_45)
      | r1_xboole_0(A_45,B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( ~ r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,k4_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_202,plain,(
    ! [A_75,B_76,B_77] :
      ( ~ r2_hidden('#skF_3'(k4_xboole_0(A_75,B_76),B_77),B_76)
      | r1_xboole_0(k4_xboole_0(A_75,B_76),B_77) ) ),
    inference(resolution,[status(thm)],[c_88,c_4])).

tff(c_216,plain,(
    ! [A_78,B_79] : r1_xboole_0(k4_xboole_0(A_78,B_79),B_79) ),
    inference(resolution,[status(thm)],[c_24,c_202])).

tff(c_20,plain,(
    ! [B_8,A_7] :
      ( r1_xboole_0(B_8,A_7)
      | ~ r1_xboole_0(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_231,plain,(
    ! [B_83,A_84] : r1_xboole_0(B_83,k4_xboole_0(A_84,B_83)) ),
    inference(resolution,[status(thm)],[c_216,c_20])).

tff(c_279,plain,(
    ! [B_92,A_93] :
      ( r1_xboole_0(B_92,k1_tarski(A_93))
      | r2_hidden(A_93,B_92) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_231])).

tff(c_42,plain,(
    ! [B_29,A_28] :
      ( k10_relat_1(B_29,A_28) = k1_xboole_0
      | ~ r1_xboole_0(k2_relat_1(B_29),A_28)
      | ~ v1_relat_1(B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_551,plain,(
    ! [B_116,A_117] :
      ( k10_relat_1(B_116,k1_tarski(A_117)) = k1_xboole_0
      | ~ v1_relat_1(B_116)
      | r2_hidden(A_117,k2_relat_1(B_116)) ) ),
    inference(resolution,[status(thm)],[c_279,c_42])).

tff(c_570,plain,
    ( k10_relat_1('#skF_5',k1_tarski('#skF_4')) = k1_xboole_0
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_551,c_99])).

tff(c_578,plain,(
    k10_relat_1('#skF_5',k1_tarski('#skF_4')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_570])).

tff(c_580,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_124,c_578])).

tff(c_581,plain,(
    k10_relat_1('#skF_5',k1_tarski('#skF_4')) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_582,plain,(
    r2_hidden('#skF_4',k2_relat_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_619,plain,(
    ! [B_128,A_129] :
      ( r1_xboole_0(k2_relat_1(B_128),A_129)
      | k10_relat_1(B_128,A_129) != k1_xboole_0
      | ~ v1_relat_1(B_128) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_631,plain,(
    ! [A_132,B_133] :
      ( r1_xboole_0(A_132,k2_relat_1(B_133))
      | k10_relat_1(B_133,A_132) != k1_xboole_0
      | ~ v1_relat_1(B_133) ) ),
    inference(resolution,[status(thm)],[c_619,c_20])).

tff(c_36,plain,(
    ! [A_24,B_25] :
      ( ~ r2_hidden(A_24,B_25)
      | ~ r1_xboole_0(k1_tarski(A_24),B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_683,plain,(
    ! [A_145,B_146] :
      ( ~ r2_hidden(A_145,k2_relat_1(B_146))
      | k10_relat_1(B_146,k1_tarski(A_145)) != k1_xboole_0
      | ~ v1_relat_1(B_146) ) ),
    inference(resolution,[status(thm)],[c_631,c_36])).

tff(c_686,plain,
    ( k10_relat_1('#skF_5',k1_tarski('#skF_4')) != k1_xboole_0
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_582,c_683])).

tff(c_698,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_581,c_686])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.32  % Computer   : n018.cluster.edu
% 0.13/0.32  % Model      : x86_64 x86_64
% 0.13/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.32  % Memory     : 8042.1875MB
% 0.13/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.32  % CPULimit   : 60
% 0.13/0.32  % DateTime   : Tue Dec  1 20:38:27 EST 2020
% 0.13/0.32  % CPUTime    : 
% 0.13/0.32  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.65/1.33  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.65/1.33  
% 2.65/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.65/1.33  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_2 > #skF_4
% 2.65/1.33  
% 2.65/1.33  %Foreground sorts:
% 2.65/1.33  
% 2.65/1.33  
% 2.65/1.33  %Background operators:
% 2.65/1.33  
% 2.65/1.33  
% 2.65/1.33  %Foreground operators:
% 2.65/1.33  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.65/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.65/1.33  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.65/1.33  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.65/1.33  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.65/1.33  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.65/1.33  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.65/1.33  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.65/1.33  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.65/1.33  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.65/1.33  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.65/1.33  tff('#skF_5', type, '#skF_5': $i).
% 2.65/1.33  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.65/1.33  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.65/1.33  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.65/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.65/1.33  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.65/1.33  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.65/1.33  tff('#skF_4', type, '#skF_4': $i).
% 2.65/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.65/1.33  
% 2.65/1.34  tff(f_89, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r2_hidden(A, k2_relat_1(B)) <=> ~(k10_relat_1(B, k1_tarski(A)) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t142_funct_1)).
% 2.65/1.34  tff(f_75, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_tarski(A)) <=> ~r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l33_zfmisc_1)).
% 2.65/1.34  tff(f_57, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.65/1.34  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 2.65/1.34  tff(f_39, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 2.65/1.34  tff(f_81, axiom, (![A, B]: (v1_relat_1(B) => ((k10_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t173_relat_1)).
% 2.65/1.34  tff(f_70, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), B) & r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 2.65/1.34  tff(c_46, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.65/1.34  tff(c_48, plain, (k10_relat_1('#skF_5', k1_tarski('#skF_4'))=k1_xboole_0 | ~r2_hidden('#skF_4', k2_relat_1('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.65/1.34  tff(c_99, plain, (~r2_hidden('#skF_4', k2_relat_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_48])).
% 2.65/1.34  tff(c_54, plain, (r2_hidden('#skF_4', k2_relat_1('#skF_5')) | k10_relat_1('#skF_5', k1_tarski('#skF_4'))!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.65/1.34  tff(c_124, plain, (k10_relat_1('#skF_5', k1_tarski('#skF_4'))!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_99, c_54])).
% 2.65/1.34  tff(c_40, plain, (![A_26, B_27]: (k4_xboole_0(k1_tarski(A_26), B_27)=k1_tarski(A_26) | r2_hidden(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.65/1.34  tff(c_24, plain, (![A_9, B_10]: (r2_hidden('#skF_3'(A_9, B_10), B_10) | r1_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.65/1.34  tff(c_88, plain, (![A_45, B_46]: (r2_hidden('#skF_3'(A_45, B_46), A_45) | r1_xboole_0(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.65/1.34  tff(c_4, plain, (![D_6, B_2, A_1]: (~r2_hidden(D_6, B_2) | ~r2_hidden(D_6, k4_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.65/1.34  tff(c_202, plain, (![A_75, B_76, B_77]: (~r2_hidden('#skF_3'(k4_xboole_0(A_75, B_76), B_77), B_76) | r1_xboole_0(k4_xboole_0(A_75, B_76), B_77))), inference(resolution, [status(thm)], [c_88, c_4])).
% 2.65/1.34  tff(c_216, plain, (![A_78, B_79]: (r1_xboole_0(k4_xboole_0(A_78, B_79), B_79))), inference(resolution, [status(thm)], [c_24, c_202])).
% 2.65/1.34  tff(c_20, plain, (![B_8, A_7]: (r1_xboole_0(B_8, A_7) | ~r1_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.65/1.34  tff(c_231, plain, (![B_83, A_84]: (r1_xboole_0(B_83, k4_xboole_0(A_84, B_83)))), inference(resolution, [status(thm)], [c_216, c_20])).
% 2.65/1.34  tff(c_279, plain, (![B_92, A_93]: (r1_xboole_0(B_92, k1_tarski(A_93)) | r2_hidden(A_93, B_92))), inference(superposition, [status(thm), theory('equality')], [c_40, c_231])).
% 2.65/1.34  tff(c_42, plain, (![B_29, A_28]: (k10_relat_1(B_29, A_28)=k1_xboole_0 | ~r1_xboole_0(k2_relat_1(B_29), A_28) | ~v1_relat_1(B_29))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.65/1.34  tff(c_551, plain, (![B_116, A_117]: (k10_relat_1(B_116, k1_tarski(A_117))=k1_xboole_0 | ~v1_relat_1(B_116) | r2_hidden(A_117, k2_relat_1(B_116)))), inference(resolution, [status(thm)], [c_279, c_42])).
% 2.65/1.34  tff(c_570, plain, (k10_relat_1('#skF_5', k1_tarski('#skF_4'))=k1_xboole_0 | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_551, c_99])).
% 2.65/1.34  tff(c_578, plain, (k10_relat_1('#skF_5', k1_tarski('#skF_4'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_46, c_570])).
% 2.65/1.34  tff(c_580, plain, $false, inference(negUnitSimplification, [status(thm)], [c_124, c_578])).
% 2.65/1.34  tff(c_581, plain, (k10_relat_1('#skF_5', k1_tarski('#skF_4'))=k1_xboole_0), inference(splitRight, [status(thm)], [c_48])).
% 2.65/1.34  tff(c_582, plain, (r2_hidden('#skF_4', k2_relat_1('#skF_5'))), inference(splitRight, [status(thm)], [c_48])).
% 2.65/1.34  tff(c_619, plain, (![B_128, A_129]: (r1_xboole_0(k2_relat_1(B_128), A_129) | k10_relat_1(B_128, A_129)!=k1_xboole_0 | ~v1_relat_1(B_128))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.65/1.34  tff(c_631, plain, (![A_132, B_133]: (r1_xboole_0(A_132, k2_relat_1(B_133)) | k10_relat_1(B_133, A_132)!=k1_xboole_0 | ~v1_relat_1(B_133))), inference(resolution, [status(thm)], [c_619, c_20])).
% 2.65/1.34  tff(c_36, plain, (![A_24, B_25]: (~r2_hidden(A_24, B_25) | ~r1_xboole_0(k1_tarski(A_24), B_25))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.65/1.34  tff(c_683, plain, (![A_145, B_146]: (~r2_hidden(A_145, k2_relat_1(B_146)) | k10_relat_1(B_146, k1_tarski(A_145))!=k1_xboole_0 | ~v1_relat_1(B_146))), inference(resolution, [status(thm)], [c_631, c_36])).
% 2.65/1.34  tff(c_686, plain, (k10_relat_1('#skF_5', k1_tarski('#skF_4'))!=k1_xboole_0 | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_582, c_683])).
% 2.65/1.34  tff(c_698, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_581, c_686])).
% 2.65/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.65/1.34  
% 2.65/1.34  Inference rules
% 2.65/1.34  ----------------------
% 2.65/1.34  #Ref     : 0
% 2.65/1.34  #Sup     : 148
% 2.65/1.34  #Fact    : 0
% 2.65/1.34  #Define  : 0
% 2.65/1.34  #Split   : 1
% 2.65/1.34  #Chain   : 0
% 2.65/1.34  #Close   : 0
% 2.65/1.34  
% 2.65/1.34  Ordering : KBO
% 2.65/1.34  
% 2.65/1.34  Simplification rules
% 2.65/1.34  ----------------------
% 2.65/1.35  #Subsume      : 14
% 2.65/1.35  #Demod        : 6
% 2.65/1.35  #Tautology    : 40
% 2.65/1.35  #SimpNegUnit  : 2
% 2.65/1.35  #BackRed      : 0
% 2.65/1.35  
% 2.65/1.35  #Partial instantiations: 0
% 2.65/1.35  #Strategies tried      : 1
% 2.65/1.35  
% 2.65/1.35  Timing (in seconds)
% 2.65/1.35  ----------------------
% 2.65/1.35  Preprocessing        : 0.31
% 2.65/1.35  Parsing              : 0.16
% 2.65/1.35  CNF conversion       : 0.02
% 2.65/1.35  Main loop            : 0.31
% 2.65/1.35  Inferencing          : 0.12
% 2.65/1.35  Reduction            : 0.07
% 2.65/1.35  Demodulation         : 0.04
% 2.65/1.35  BG Simplification    : 0.02
% 2.65/1.35  Subsumption          : 0.07
% 2.65/1.35  Abstraction          : 0.02
% 2.65/1.35  MUC search           : 0.00
% 2.65/1.35  Cooper               : 0.00
% 2.65/1.35  Total                : 0.64
% 2.65/1.35  Index Insertion      : 0.00
% 2.65/1.35  Index Deletion       : 0.00
% 2.65/1.35  Index Matching       : 0.00
% 2.65/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
