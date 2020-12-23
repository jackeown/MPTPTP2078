%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:59 EST 2020

% Result     : Theorem 2.02s
% Output     : CNFRefutation 2.14s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 145 expanded)
%              Number of leaves         :   23 (  57 expanded)
%              Depth                    :    9
%              Number of atoms          :   91 ( 322 expanded)
%              Number of equality atoms :    6 (  22 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k2_enumset1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_74,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,A)
       => ! [C] :
            ( m1_subset_1(C,A)
           => ( A != k1_xboole_0
             => m1_subset_1(k2_tarski(B,C),k1_zfmisc_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_subset_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(c_38,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_42,plain,(
    m1_subset_1('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_56,plain,(
    ! [B_27,A_28] :
      ( v1_xboole_0(B_27)
      | ~ m1_subset_1(B_27,A_28)
      | ~ v1_xboole_0(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_63,plain,
    ( v1_xboole_0('#skF_5')
    | ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_56])).

tff(c_65,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_63])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_278,plain,(
    ! [A_68,B_69,C_70] :
      ( r1_tarski(k2_tarski(A_68,B_69),C_70)
      | ~ r2_hidden(B_69,C_70)
      | ~ r2_hidden(A_68,C_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_40,plain,(
    m1_subset_1('#skF_6','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_30,plain,(
    ! [B_17,A_16] :
      ( r2_hidden(B_17,A_16)
      | ~ m1_subset_1(B_17,A_16)
      | v1_xboole_0(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_22,plain,(
    ! [A_13,B_14,C_15] :
      ( r1_tarski(k2_tarski(A_13,B_14),C_15)
      | ~ r2_hidden(B_14,C_15)
      | ~ r2_hidden(A_13,C_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_76,plain,(
    ! [B_31,A_32] :
      ( m1_subset_1(B_31,A_32)
      | ~ v1_xboole_0(B_31)
      | ~ v1_xboole_0(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_36,plain,(
    ~ m1_subset_1(k2_tarski('#skF_5','#skF_6'),k1_zfmisc_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_84,plain,
    ( ~ v1_xboole_0(k2_tarski('#skF_5','#skF_6'))
    | ~ v1_xboole_0(k1_zfmisc_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_76,c_36])).

tff(c_95,plain,(
    ~ v1_xboole_0(k1_zfmisc_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_84])).

tff(c_12,plain,(
    ! [C_12,A_8] :
      ( r2_hidden(C_12,k1_zfmisc_1(A_8))
      | ~ r1_tarski(C_12,A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_96,plain,(
    ! [B_35,A_36] :
      ( m1_subset_1(B_35,A_36)
      | ~ r2_hidden(B_35,A_36)
      | v1_xboole_0(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_126,plain,(
    ! [C_47,A_48] :
      ( m1_subset_1(C_47,k1_zfmisc_1(A_48))
      | v1_xboole_0(k1_zfmisc_1(A_48))
      | ~ r1_tarski(C_47,A_48) ) ),
    inference(resolution,[status(thm)],[c_12,c_96])).

tff(c_132,plain,
    ( v1_xboole_0(k1_zfmisc_1('#skF_4'))
    | ~ r1_tarski(k2_tarski('#skF_5','#skF_6'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_126,c_36])).

tff(c_136,plain,(
    ~ r1_tarski(k2_tarski('#skF_5','#skF_6'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_95,c_132])).

tff(c_149,plain,
    ( ~ r2_hidden('#skF_6','#skF_4')
    | ~ r2_hidden('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_22,c_136])).

tff(c_150,plain,(
    ~ r2_hidden('#skF_5','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_149])).

tff(c_153,plain,
    ( ~ m1_subset_1('#skF_5','#skF_4')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_150])).

tff(c_156,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_153])).

tff(c_158,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_65,c_156])).

tff(c_159,plain,(
    ~ r2_hidden('#skF_6','#skF_4') ),
    inference(splitRight,[status(thm)],[c_149])).

tff(c_173,plain,
    ( ~ m1_subset_1('#skF_6','#skF_4')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_159])).

tff(c_176,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_173])).

tff(c_178,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_65,c_176])).

tff(c_180,plain,(
    v1_xboole_0(k1_zfmisc_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_50,plain,(
    ! [C_23,A_24] :
      ( r2_hidden(C_23,k1_zfmisc_1(A_24))
      | ~ r1_tarski(C_23,A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_54,plain,(
    ! [A_24,C_23] :
      ( ~ v1_xboole_0(k1_zfmisc_1(A_24))
      | ~ r1_tarski(C_23,A_24) ) ),
    inference(resolution,[status(thm)],[c_50,c_2])).

tff(c_186,plain,(
    ! [C_23] : ~ r1_tarski(C_23,'#skF_4') ),
    inference(resolution,[status(thm)],[c_180,c_54])).

tff(c_291,plain,(
    ! [B_69,A_68] :
      ( ~ r2_hidden(B_69,'#skF_4')
      | ~ r2_hidden(A_68,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_278,c_186])).

tff(c_293,plain,(
    ! [A_71] : ~ r2_hidden(A_71,'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_291])).

tff(c_301,plain,(
    v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_4,c_293])).

tff(c_308,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_65,c_301])).

tff(c_310,plain,(
    ! [B_72] : ~ r2_hidden(B_72,'#skF_4') ),
    inference(splitRight,[status(thm)],[c_291])).

tff(c_318,plain,(
    v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_4,c_310])).

tff(c_325,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_65,c_318])).

tff(c_327,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_63])).

tff(c_6,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_335,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_327,c_6])).

tff(c_339,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_335])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n004.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 15:46:53 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.02/1.23  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.14/1.23  
% 2.14/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.14/1.24  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k2_enumset1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2
% 2.14/1.24  
% 2.14/1.24  %Foreground sorts:
% 2.14/1.24  
% 2.14/1.24  
% 2.14/1.24  %Background operators:
% 2.14/1.24  
% 2.14/1.24  
% 2.14/1.24  %Foreground operators:
% 2.14/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.14/1.24  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.14/1.24  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.14/1.24  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.14/1.24  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.14/1.24  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.14/1.24  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.14/1.24  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.14/1.24  tff('#skF_5', type, '#skF_5': $i).
% 2.14/1.24  tff('#skF_6', type, '#skF_6': $i).
% 2.14/1.24  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.14/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.14/1.24  tff('#skF_4', type, '#skF_4': $i).
% 2.14/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.14/1.24  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.14/1.24  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.14/1.24  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.14/1.24  
% 2.14/1.25  tff(f_74, negated_conjecture, ~(![A, B]: (m1_subset_1(B, A) => (![C]: (m1_subset_1(C, A) => (~(A = k1_xboole_0) => m1_subset_1(k2_tarski(B, C), k1_zfmisc_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_subset_1)).
% 2.14/1.25  tff(f_63, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 2.14/1.25  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.14/1.25  tff(f_50, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 2.14/1.25  tff(f_44, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 2.14/1.25  tff(f_35, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.14/1.25  tff(c_38, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.14/1.25  tff(c_42, plain, (m1_subset_1('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.14/1.25  tff(c_56, plain, (![B_27, A_28]: (v1_xboole_0(B_27) | ~m1_subset_1(B_27, A_28) | ~v1_xboole_0(A_28))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.14/1.25  tff(c_63, plain, (v1_xboole_0('#skF_5') | ~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_42, c_56])).
% 2.14/1.25  tff(c_65, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_63])).
% 2.14/1.25  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.14/1.25  tff(c_278, plain, (![A_68, B_69, C_70]: (r1_tarski(k2_tarski(A_68, B_69), C_70) | ~r2_hidden(B_69, C_70) | ~r2_hidden(A_68, C_70))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.14/1.25  tff(c_40, plain, (m1_subset_1('#skF_6', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.14/1.25  tff(c_30, plain, (![B_17, A_16]: (r2_hidden(B_17, A_16) | ~m1_subset_1(B_17, A_16) | v1_xboole_0(A_16))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.14/1.25  tff(c_22, plain, (![A_13, B_14, C_15]: (r1_tarski(k2_tarski(A_13, B_14), C_15) | ~r2_hidden(B_14, C_15) | ~r2_hidden(A_13, C_15))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.14/1.25  tff(c_76, plain, (![B_31, A_32]: (m1_subset_1(B_31, A_32) | ~v1_xboole_0(B_31) | ~v1_xboole_0(A_32))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.14/1.25  tff(c_36, plain, (~m1_subset_1(k2_tarski('#skF_5', '#skF_6'), k1_zfmisc_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.14/1.25  tff(c_84, plain, (~v1_xboole_0(k2_tarski('#skF_5', '#skF_6')) | ~v1_xboole_0(k1_zfmisc_1('#skF_4'))), inference(resolution, [status(thm)], [c_76, c_36])).
% 2.14/1.25  tff(c_95, plain, (~v1_xboole_0(k1_zfmisc_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_84])).
% 2.14/1.25  tff(c_12, plain, (![C_12, A_8]: (r2_hidden(C_12, k1_zfmisc_1(A_8)) | ~r1_tarski(C_12, A_8))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.14/1.25  tff(c_96, plain, (![B_35, A_36]: (m1_subset_1(B_35, A_36) | ~r2_hidden(B_35, A_36) | v1_xboole_0(A_36))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.14/1.25  tff(c_126, plain, (![C_47, A_48]: (m1_subset_1(C_47, k1_zfmisc_1(A_48)) | v1_xboole_0(k1_zfmisc_1(A_48)) | ~r1_tarski(C_47, A_48))), inference(resolution, [status(thm)], [c_12, c_96])).
% 2.14/1.25  tff(c_132, plain, (v1_xboole_0(k1_zfmisc_1('#skF_4')) | ~r1_tarski(k2_tarski('#skF_5', '#skF_6'), '#skF_4')), inference(resolution, [status(thm)], [c_126, c_36])).
% 2.14/1.25  tff(c_136, plain, (~r1_tarski(k2_tarski('#skF_5', '#skF_6'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_95, c_132])).
% 2.14/1.25  tff(c_149, plain, (~r2_hidden('#skF_6', '#skF_4') | ~r2_hidden('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_22, c_136])).
% 2.14/1.25  tff(c_150, plain, (~r2_hidden('#skF_5', '#skF_4')), inference(splitLeft, [status(thm)], [c_149])).
% 2.14/1.25  tff(c_153, plain, (~m1_subset_1('#skF_5', '#skF_4') | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_30, c_150])).
% 2.14/1.25  tff(c_156, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_153])).
% 2.14/1.25  tff(c_158, plain, $false, inference(negUnitSimplification, [status(thm)], [c_65, c_156])).
% 2.14/1.25  tff(c_159, plain, (~r2_hidden('#skF_6', '#skF_4')), inference(splitRight, [status(thm)], [c_149])).
% 2.14/1.25  tff(c_173, plain, (~m1_subset_1('#skF_6', '#skF_4') | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_30, c_159])).
% 2.14/1.25  tff(c_176, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_173])).
% 2.14/1.25  tff(c_178, plain, $false, inference(negUnitSimplification, [status(thm)], [c_65, c_176])).
% 2.14/1.25  tff(c_180, plain, (v1_xboole_0(k1_zfmisc_1('#skF_4'))), inference(splitRight, [status(thm)], [c_84])).
% 2.14/1.25  tff(c_50, plain, (![C_23, A_24]: (r2_hidden(C_23, k1_zfmisc_1(A_24)) | ~r1_tarski(C_23, A_24))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.14/1.25  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.14/1.25  tff(c_54, plain, (![A_24, C_23]: (~v1_xboole_0(k1_zfmisc_1(A_24)) | ~r1_tarski(C_23, A_24))), inference(resolution, [status(thm)], [c_50, c_2])).
% 2.14/1.25  tff(c_186, plain, (![C_23]: (~r1_tarski(C_23, '#skF_4'))), inference(resolution, [status(thm)], [c_180, c_54])).
% 2.14/1.25  tff(c_291, plain, (![B_69, A_68]: (~r2_hidden(B_69, '#skF_4') | ~r2_hidden(A_68, '#skF_4'))), inference(resolution, [status(thm)], [c_278, c_186])).
% 2.14/1.25  tff(c_293, plain, (![A_71]: (~r2_hidden(A_71, '#skF_4'))), inference(splitLeft, [status(thm)], [c_291])).
% 2.14/1.25  tff(c_301, plain, (v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_4, c_293])).
% 2.14/1.25  tff(c_308, plain, $false, inference(negUnitSimplification, [status(thm)], [c_65, c_301])).
% 2.14/1.25  tff(c_310, plain, (![B_72]: (~r2_hidden(B_72, '#skF_4'))), inference(splitRight, [status(thm)], [c_291])).
% 2.14/1.25  tff(c_318, plain, (v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_4, c_310])).
% 2.14/1.25  tff(c_325, plain, $false, inference(negUnitSimplification, [status(thm)], [c_65, c_318])).
% 2.14/1.25  tff(c_327, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_63])).
% 2.14/1.25  tff(c_6, plain, (![A_5]: (k1_xboole_0=A_5 | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.14/1.25  tff(c_335, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_327, c_6])).
% 2.14/1.25  tff(c_339, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_335])).
% 2.14/1.25  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.14/1.25  
% 2.14/1.25  Inference rules
% 2.14/1.25  ----------------------
% 2.14/1.25  #Ref     : 0
% 2.14/1.25  #Sup     : 55
% 2.14/1.25  #Fact    : 0
% 2.14/1.25  #Define  : 0
% 2.14/1.25  #Split   : 5
% 2.14/1.25  #Chain   : 0
% 2.14/1.25  #Close   : 0
% 2.14/1.25  
% 2.14/1.25  Ordering : KBO
% 2.14/1.25  
% 2.14/1.25  Simplification rules
% 2.14/1.25  ----------------------
% 2.14/1.25  #Subsume      : 8
% 2.14/1.25  #Demod        : 14
% 2.14/1.25  #Tautology    : 24
% 2.14/1.25  #SimpNegUnit  : 11
% 2.14/1.25  #BackRed      : 2
% 2.14/1.25  
% 2.14/1.25  #Partial instantiations: 0
% 2.14/1.25  #Strategies tried      : 1
% 2.14/1.25  
% 2.14/1.25  Timing (in seconds)
% 2.14/1.25  ----------------------
% 2.14/1.25  Preprocessing        : 0.30
% 2.14/1.25  Parsing              : 0.16
% 2.14/1.25  CNF conversion       : 0.02
% 2.14/1.25  Main loop            : 0.19
% 2.14/1.25  Inferencing          : 0.08
% 2.14/1.25  Reduction            : 0.05
% 2.14/1.25  Demodulation         : 0.03
% 2.14/1.25  BG Simplification    : 0.02
% 2.14/1.25  Subsumption          : 0.03
% 2.14/1.25  Abstraction          : 0.01
% 2.14/1.25  MUC search           : 0.00
% 2.14/1.25  Cooper               : 0.00
% 2.14/1.25  Total                : 0.53
% 2.14/1.25  Index Insertion      : 0.00
% 2.14/1.25  Index Deletion       : 0.00
% 2.14/1.25  Index Matching       : 0.00
% 2.14/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
