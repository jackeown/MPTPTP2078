%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:35 EST 2020

% Result     : Theorem 5.92s
% Output     : CNFRefutation 6.11s
% Verified   : 
% Statistics : Number of formulae       :   65 (  88 expanded)
%              Number of leaves         :   28 (  42 expanded)
%              Depth                    :    9
%              Number of atoms          :   92 ( 163 expanded)
%              Number of equality atoms :   21 (  35 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t142_funct_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

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

tff(f_81,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k10_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t173_relat_1)).

tff(f_59,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ~ ( r1_xboole_0(k2_tarski(A,B),C)
        & r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_zfmisc_1)).

tff(c_46,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_48,plain,
    ( k10_relat_1('#skF_5',k1_tarski('#skF_4')) = k1_xboole_0
    | ~ r2_hidden('#skF_4',k2_relat_1('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_95,plain,(
    ~ r2_hidden('#skF_4',k2_relat_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_54,plain,
    ( r2_hidden('#skF_4',k2_relat_1('#skF_5'))
    | k10_relat_1('#skF_5',k1_tarski('#skF_4')) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_137,plain,(
    k10_relat_1('#skF_5',k1_tarski('#skF_4')) != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_95,c_54])).

tff(c_38,plain,(
    ! [A_24,B_25] :
      ( r1_xboole_0(k1_tarski(A_24),B_25)
      | r2_hidden(A_24,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_75,plain,(
    ! [A_38,B_39] :
      ( k4_xboole_0(A_38,B_39) = A_38
      | ~ r1_xboole_0(A_38,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_83,plain,(
    ! [A_24,B_25] :
      ( k4_xboole_0(k1_tarski(A_24),B_25) = k1_tarski(A_24)
      | r2_hidden(A_24,B_25) ) ),
    inference(resolution,[status(thm)],[c_38,c_75])).

tff(c_24,plain,(
    ! [A_7,B_8] :
      ( r2_hidden('#skF_3'(A_7,B_8),A_7)
      | r1_xboole_0(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_22,plain,(
    ! [A_7,B_8] :
      ( r2_hidden('#skF_3'(A_7,B_8),B_8)
      | r1_xboole_0(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_106,plain,(
    ! [D_49,B_50,A_51] :
      ( ~ r2_hidden(D_49,B_50)
      | ~ r2_hidden(D_49,k4_xboole_0(A_51,B_50)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_229,plain,(
    ! [A_85,A_86,B_87] :
      ( ~ r2_hidden('#skF_3'(A_85,k4_xboole_0(A_86,B_87)),B_87)
      | r1_xboole_0(A_85,k4_xboole_0(A_86,B_87)) ) ),
    inference(resolution,[status(thm)],[c_22,c_106])).

tff(c_243,plain,(
    ! [A_88,A_89] : r1_xboole_0(A_88,k4_xboole_0(A_89,A_88)) ),
    inference(resolution,[status(thm)],[c_24,c_229])).

tff(c_42,plain,(
    ! [B_30,A_29] :
      ( k10_relat_1(B_30,A_29) = k1_xboole_0
      | ~ r1_xboole_0(k2_relat_1(B_30),A_29)
      | ~ v1_relat_1(B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_721,plain,(
    ! [B_130,A_131] :
      ( k10_relat_1(B_130,k4_xboole_0(A_131,k2_relat_1(B_130))) = k1_xboole_0
      | ~ v1_relat_1(B_130) ) ),
    inference(resolution,[status(thm)],[c_243,c_42])).

tff(c_895,plain,(
    ! [B_148,A_149] :
      ( k10_relat_1(B_148,k1_tarski(A_149)) = k1_xboole_0
      | ~ v1_relat_1(B_148)
      | r2_hidden(A_149,k2_relat_1(B_148)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_83,c_721])).

tff(c_921,plain,
    ( k10_relat_1('#skF_5',k1_tarski('#skF_4')) = k1_xboole_0
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_895,c_95])).

tff(c_932,plain,(
    k10_relat_1('#skF_5',k1_tarski('#skF_4')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_921])).

tff(c_934,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_137,c_932])).

tff(c_935,plain,(
    k10_relat_1('#skF_5',k1_tarski('#skF_4')) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_936,plain,(
    r2_hidden('#skF_4',k2_relat_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_2,plain,(
    ! [D_6,A_1,B_2] :
      ( r2_hidden(D_6,k4_xboole_0(A_1,B_2))
      | r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_962,plain,(
    ! [D_155,B_156,A_157] :
      ( ~ r2_hidden(D_155,B_156)
      | ~ r2_hidden(D_155,k4_xboole_0(A_157,B_156)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2006,plain,(
    ! [A_268,A_269,B_270] :
      ( ~ r2_hidden('#skF_3'(A_268,k4_xboole_0(A_269,B_270)),B_270)
      | r1_xboole_0(A_268,k4_xboole_0(A_269,B_270)) ) ),
    inference(resolution,[status(thm)],[c_22,c_962])).

tff(c_2080,plain,(
    ! [A_273,A_274] : r1_xboole_0(A_273,k4_xboole_0(A_274,A_273)) ),
    inference(resolution,[status(thm)],[c_24,c_2006])).

tff(c_30,plain,(
    ! [A_14] : k2_tarski(A_14,A_14) = k1_tarski(A_14) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_86,plain,(
    ! [A_44,C_45,B_46] :
      ( ~ r2_hidden(A_44,C_45)
      | ~ r1_xboole_0(k2_tarski(A_44,B_46),C_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_93,plain,(
    ! [A_14,C_45] :
      ( ~ r2_hidden(A_14,C_45)
      | ~ r1_xboole_0(k1_tarski(A_14),C_45) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_86])).

tff(c_2604,plain,(
    ! [A_281,A_282] : ~ r2_hidden(A_281,k4_xboole_0(A_282,k1_tarski(A_281))) ),
    inference(resolution,[status(thm)],[c_2080,c_93])).

tff(c_3479,plain,(
    ! [D_313,A_314] :
      ( r2_hidden(D_313,k1_tarski(D_313))
      | ~ r2_hidden(D_313,A_314) ) ),
    inference(resolution,[status(thm)],[c_2,c_2604])).

tff(c_3516,plain,(
    r2_hidden('#skF_4',k1_tarski('#skF_4')) ),
    inference(resolution,[status(thm)],[c_936,c_3479])).

tff(c_1011,plain,(
    ! [B_168,A_169] :
      ( r1_xboole_0(k2_relat_1(B_168),A_169)
      | k10_relat_1(B_168,A_169) != k1_xboole_0
      | ~ v1_relat_1(B_168) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_20,plain,(
    ! [A_7,B_8,C_11] :
      ( ~ r1_xboole_0(A_7,B_8)
      | ~ r2_hidden(C_11,B_8)
      | ~ r2_hidden(C_11,A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1017,plain,(
    ! [C_11,A_169,B_168] :
      ( ~ r2_hidden(C_11,A_169)
      | ~ r2_hidden(C_11,k2_relat_1(B_168))
      | k10_relat_1(B_168,A_169) != k1_xboole_0
      | ~ v1_relat_1(B_168) ) ),
    inference(resolution,[status(thm)],[c_1011,c_20])).

tff(c_6316,plain,(
    ! [B_380] :
      ( ~ r2_hidden('#skF_4',k2_relat_1(B_380))
      | k10_relat_1(B_380,k1_tarski('#skF_4')) != k1_xboole_0
      | ~ v1_relat_1(B_380) ) ),
    inference(resolution,[status(thm)],[c_3516,c_1017])).

tff(c_6319,plain,
    ( k10_relat_1('#skF_5',k1_tarski('#skF_4')) != k1_xboole_0
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_936,c_6316])).

tff(c_6323,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_935,c_6319])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:50:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.92/2.15  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.92/2.16  
% 5.92/2.16  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.92/2.16  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_2 > #skF_4
% 5.92/2.16  
% 5.92/2.16  %Foreground sorts:
% 5.92/2.16  
% 5.92/2.16  
% 5.92/2.16  %Background operators:
% 5.92/2.16  
% 5.92/2.16  
% 5.92/2.16  %Foreground operators:
% 5.92/2.16  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 5.92/2.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.92/2.16  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.92/2.16  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.92/2.16  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.92/2.16  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.92/2.16  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 5.92/2.16  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 5.92/2.16  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.92/2.16  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.92/2.16  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.92/2.16  tff('#skF_5', type, '#skF_5': $i).
% 5.92/2.16  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.92/2.16  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 5.92/2.16  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 5.92/2.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.92/2.16  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 5.92/2.16  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.92/2.16  tff('#skF_4', type, '#skF_4': $i).
% 5.92/2.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.92/2.16  
% 6.11/2.17  tff(f_89, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r2_hidden(A, k2_relat_1(B)) <=> ~(k10_relat_1(B, k1_tarski(A)) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t142_funct_1)).
% 6.11/2.17  tff(f_70, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 6.11/2.17  tff(f_57, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 6.11/2.17  tff(f_53, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 6.11/2.17  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 6.11/2.17  tff(f_81, axiom, (![A, B]: (v1_relat_1(B) => ((k10_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t173_relat_1)).
% 6.11/2.17  tff(f_59, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 6.11/2.17  tff(f_75, axiom, (![A, B, C]: ~(r1_xboole_0(k2_tarski(A, B), C) & r2_hidden(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_zfmisc_1)).
% 6.11/2.17  tff(c_46, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_89])).
% 6.11/2.17  tff(c_48, plain, (k10_relat_1('#skF_5', k1_tarski('#skF_4'))=k1_xboole_0 | ~r2_hidden('#skF_4', k2_relat_1('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_89])).
% 6.11/2.17  tff(c_95, plain, (~r2_hidden('#skF_4', k2_relat_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_48])).
% 6.11/2.17  tff(c_54, plain, (r2_hidden('#skF_4', k2_relat_1('#skF_5')) | k10_relat_1('#skF_5', k1_tarski('#skF_4'))!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_89])).
% 6.11/2.17  tff(c_137, plain, (k10_relat_1('#skF_5', k1_tarski('#skF_4'))!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_95, c_54])).
% 6.11/2.17  tff(c_38, plain, (![A_24, B_25]: (r1_xboole_0(k1_tarski(A_24), B_25) | r2_hidden(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_70])).
% 6.11/2.17  tff(c_75, plain, (![A_38, B_39]: (k4_xboole_0(A_38, B_39)=A_38 | ~r1_xboole_0(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.11/2.17  tff(c_83, plain, (![A_24, B_25]: (k4_xboole_0(k1_tarski(A_24), B_25)=k1_tarski(A_24) | r2_hidden(A_24, B_25))), inference(resolution, [status(thm)], [c_38, c_75])).
% 6.11/2.17  tff(c_24, plain, (![A_7, B_8]: (r2_hidden('#skF_3'(A_7, B_8), A_7) | r1_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.11/2.17  tff(c_22, plain, (![A_7, B_8]: (r2_hidden('#skF_3'(A_7, B_8), B_8) | r1_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.11/2.17  tff(c_106, plain, (![D_49, B_50, A_51]: (~r2_hidden(D_49, B_50) | ~r2_hidden(D_49, k4_xboole_0(A_51, B_50)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.11/2.17  tff(c_229, plain, (![A_85, A_86, B_87]: (~r2_hidden('#skF_3'(A_85, k4_xboole_0(A_86, B_87)), B_87) | r1_xboole_0(A_85, k4_xboole_0(A_86, B_87)))), inference(resolution, [status(thm)], [c_22, c_106])).
% 6.11/2.17  tff(c_243, plain, (![A_88, A_89]: (r1_xboole_0(A_88, k4_xboole_0(A_89, A_88)))), inference(resolution, [status(thm)], [c_24, c_229])).
% 6.11/2.17  tff(c_42, plain, (![B_30, A_29]: (k10_relat_1(B_30, A_29)=k1_xboole_0 | ~r1_xboole_0(k2_relat_1(B_30), A_29) | ~v1_relat_1(B_30))), inference(cnfTransformation, [status(thm)], [f_81])).
% 6.11/2.17  tff(c_721, plain, (![B_130, A_131]: (k10_relat_1(B_130, k4_xboole_0(A_131, k2_relat_1(B_130)))=k1_xboole_0 | ~v1_relat_1(B_130))), inference(resolution, [status(thm)], [c_243, c_42])).
% 6.11/2.17  tff(c_895, plain, (![B_148, A_149]: (k10_relat_1(B_148, k1_tarski(A_149))=k1_xboole_0 | ~v1_relat_1(B_148) | r2_hidden(A_149, k2_relat_1(B_148)))), inference(superposition, [status(thm), theory('equality')], [c_83, c_721])).
% 6.11/2.17  tff(c_921, plain, (k10_relat_1('#skF_5', k1_tarski('#skF_4'))=k1_xboole_0 | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_895, c_95])).
% 6.11/2.17  tff(c_932, plain, (k10_relat_1('#skF_5', k1_tarski('#skF_4'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_46, c_921])).
% 6.11/2.17  tff(c_934, plain, $false, inference(negUnitSimplification, [status(thm)], [c_137, c_932])).
% 6.11/2.17  tff(c_935, plain, (k10_relat_1('#skF_5', k1_tarski('#skF_4'))=k1_xboole_0), inference(splitRight, [status(thm)], [c_48])).
% 6.11/2.17  tff(c_936, plain, (r2_hidden('#skF_4', k2_relat_1('#skF_5'))), inference(splitRight, [status(thm)], [c_48])).
% 6.11/2.17  tff(c_2, plain, (![D_6, A_1, B_2]: (r2_hidden(D_6, k4_xboole_0(A_1, B_2)) | r2_hidden(D_6, B_2) | ~r2_hidden(D_6, A_1))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.11/2.17  tff(c_962, plain, (![D_155, B_156, A_157]: (~r2_hidden(D_155, B_156) | ~r2_hidden(D_155, k4_xboole_0(A_157, B_156)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.11/2.17  tff(c_2006, plain, (![A_268, A_269, B_270]: (~r2_hidden('#skF_3'(A_268, k4_xboole_0(A_269, B_270)), B_270) | r1_xboole_0(A_268, k4_xboole_0(A_269, B_270)))), inference(resolution, [status(thm)], [c_22, c_962])).
% 6.11/2.17  tff(c_2080, plain, (![A_273, A_274]: (r1_xboole_0(A_273, k4_xboole_0(A_274, A_273)))), inference(resolution, [status(thm)], [c_24, c_2006])).
% 6.11/2.17  tff(c_30, plain, (![A_14]: (k2_tarski(A_14, A_14)=k1_tarski(A_14))), inference(cnfTransformation, [status(thm)], [f_59])).
% 6.11/2.17  tff(c_86, plain, (![A_44, C_45, B_46]: (~r2_hidden(A_44, C_45) | ~r1_xboole_0(k2_tarski(A_44, B_46), C_45))), inference(cnfTransformation, [status(thm)], [f_75])).
% 6.11/2.17  tff(c_93, plain, (![A_14, C_45]: (~r2_hidden(A_14, C_45) | ~r1_xboole_0(k1_tarski(A_14), C_45))), inference(superposition, [status(thm), theory('equality')], [c_30, c_86])).
% 6.11/2.17  tff(c_2604, plain, (![A_281, A_282]: (~r2_hidden(A_281, k4_xboole_0(A_282, k1_tarski(A_281))))), inference(resolution, [status(thm)], [c_2080, c_93])).
% 6.11/2.17  tff(c_3479, plain, (![D_313, A_314]: (r2_hidden(D_313, k1_tarski(D_313)) | ~r2_hidden(D_313, A_314))), inference(resolution, [status(thm)], [c_2, c_2604])).
% 6.11/2.17  tff(c_3516, plain, (r2_hidden('#skF_4', k1_tarski('#skF_4'))), inference(resolution, [status(thm)], [c_936, c_3479])).
% 6.11/2.17  tff(c_1011, plain, (![B_168, A_169]: (r1_xboole_0(k2_relat_1(B_168), A_169) | k10_relat_1(B_168, A_169)!=k1_xboole_0 | ~v1_relat_1(B_168))), inference(cnfTransformation, [status(thm)], [f_81])).
% 6.11/2.17  tff(c_20, plain, (![A_7, B_8, C_11]: (~r1_xboole_0(A_7, B_8) | ~r2_hidden(C_11, B_8) | ~r2_hidden(C_11, A_7))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.11/2.17  tff(c_1017, plain, (![C_11, A_169, B_168]: (~r2_hidden(C_11, A_169) | ~r2_hidden(C_11, k2_relat_1(B_168)) | k10_relat_1(B_168, A_169)!=k1_xboole_0 | ~v1_relat_1(B_168))), inference(resolution, [status(thm)], [c_1011, c_20])).
% 6.11/2.17  tff(c_6316, plain, (![B_380]: (~r2_hidden('#skF_4', k2_relat_1(B_380)) | k10_relat_1(B_380, k1_tarski('#skF_4'))!=k1_xboole_0 | ~v1_relat_1(B_380))), inference(resolution, [status(thm)], [c_3516, c_1017])).
% 6.11/2.17  tff(c_6319, plain, (k10_relat_1('#skF_5', k1_tarski('#skF_4'))!=k1_xboole_0 | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_936, c_6316])).
% 6.11/2.17  tff(c_6323, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_935, c_6319])).
% 6.11/2.17  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.11/2.17  
% 6.11/2.17  Inference rules
% 6.11/2.17  ----------------------
% 6.11/2.17  #Ref     : 0
% 6.11/2.17  #Sup     : 1612
% 6.11/2.17  #Fact    : 0
% 6.11/2.17  #Define  : 0
% 6.11/2.17  #Split   : 1
% 6.11/2.17  #Chain   : 0
% 6.11/2.17  #Close   : 0
% 6.11/2.17  
% 6.11/2.17  Ordering : KBO
% 6.11/2.17  
% 6.11/2.17  Simplification rules
% 6.11/2.17  ----------------------
% 6.11/2.17  #Subsume      : 392
% 6.11/2.17  #Demod        : 506
% 6.11/2.17  #Tautology    : 486
% 6.11/2.17  #SimpNegUnit  : 42
% 6.11/2.17  #BackRed      : 3
% 6.11/2.17  
% 6.11/2.17  #Partial instantiations: 0
% 6.11/2.17  #Strategies tried      : 1
% 6.11/2.17  
% 6.11/2.17  Timing (in seconds)
% 6.11/2.17  ----------------------
% 6.11/2.18  Preprocessing        : 0.32
% 6.11/2.18  Parsing              : 0.16
% 6.11/2.18  CNF conversion       : 0.02
% 6.11/2.18  Main loop            : 1.10
% 6.11/2.18  Inferencing          : 0.37
% 6.11/2.18  Reduction            : 0.33
% 6.11/2.18  Demodulation         : 0.23
% 6.11/2.18  BG Simplification    : 0.05
% 6.11/2.18  Subsumption          : 0.26
% 6.11/2.18  Abstraction          : 0.06
% 6.11/2.18  MUC search           : 0.00
% 6.11/2.18  Cooper               : 0.00
% 6.11/2.18  Total                : 1.45
% 6.11/2.18  Index Insertion      : 0.00
% 6.11/2.18  Index Deletion       : 0.00
% 6.11/2.18  Index Matching       : 0.00
% 6.11/2.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
