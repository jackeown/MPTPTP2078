%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:58 EST 2020

% Result     : Theorem 2.00s
% Output     : CNFRefutation 2.08s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 131 expanded)
%              Number of leaves         :   23 (  52 expanded)
%              Depth                    :   10
%              Number of atoms          :   87 ( 263 expanded)
%              Number of equality atoms :   13 (  38 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k4_xboole_0 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_5 > #skF_4 > #skF_3 > #skF_2 > #skF_1

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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_74,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,A)
       => ( A != k1_xboole_0
         => m1_subset_1(k1_tarski(B),k1_zfmisc_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_subset_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),B) = k1_xboole_0
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l35_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_xboole_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_66,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ? [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
          & ~ v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_subset_1)).

tff(c_38,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_40,plain,(
    m1_subset_1('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_51,plain,(
    ! [B_22,A_23] :
      ( v1_xboole_0(B_22)
      | ~ m1_subset_1(B_22,A_23)
      | ~ v1_xboole_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_63,plain,
    ( v1_xboole_0('#skF_5')
    | ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_51])).

tff(c_64,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_63])).

tff(c_26,plain,(
    ! [B_12,A_11] :
      ( r2_hidden(B_12,A_11)
      | ~ m1_subset_1(B_12,A_11)
      | v1_xboole_0(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_22,plain,(
    ! [A_9,B_10] :
      ( k4_xboole_0(k1_tarski(A_9),B_10) = k1_xboole_0
      | ~ r2_hidden(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_4,plain,(
    ! [A_2,B_3] :
      ( r1_tarski(A_2,B_3)
      | k4_xboole_0(A_2,B_3) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_44,plain,(
    ! [B_18,A_19] :
      ( m1_subset_1(B_18,A_19)
      | ~ v1_xboole_0(B_18)
      | ~ v1_xboole_0(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_36,plain,(
    ~ m1_subset_1(k1_tarski('#skF_5'),k1_zfmisc_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_48,plain,
    ( ~ v1_xboole_0(k1_tarski('#skF_5'))
    | ~ v1_xboole_0(k1_zfmisc_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_44,c_36])).

tff(c_49,plain,(
    ~ v1_xboole_0(k1_zfmisc_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_10,plain,(
    ! [C_8,A_4] :
      ( r2_hidden(C_8,k1_zfmisc_1(A_4))
      | ~ r1_tarski(C_8,A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_96,plain,(
    ! [B_36,A_37] :
      ( m1_subset_1(B_36,A_37)
      | ~ r2_hidden(B_36,A_37)
      | v1_xboole_0(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_106,plain,(
    ! [C_39,A_40] :
      ( m1_subset_1(C_39,k1_zfmisc_1(A_40))
      | v1_xboole_0(k1_zfmisc_1(A_40))
      | ~ r1_tarski(C_39,A_40) ) ),
    inference(resolution,[status(thm)],[c_10,c_96])).

tff(c_112,plain,
    ( v1_xboole_0(k1_zfmisc_1('#skF_4'))
    | ~ r1_tarski(k1_tarski('#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_106,c_36])).

tff(c_116,plain,(
    ~ r1_tarski(k1_tarski('#skF_5'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_49,c_112])).

tff(c_120,plain,(
    k4_xboole_0(k1_tarski('#skF_5'),'#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4,c_116])).

tff(c_124,plain,(
    ~ r2_hidden('#skF_5','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_120])).

tff(c_127,plain,
    ( ~ m1_subset_1('#skF_5','#skF_4')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_26,c_124])).

tff(c_130,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_127])).

tff(c_132,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_130])).

tff(c_134,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_63])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_142,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_134,c_2])).

tff(c_146,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_142])).

tff(c_148,plain,(
    v1_xboole_0(k1_zfmisc_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_152,plain,(
    k1_zfmisc_1('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_148,c_2])).

tff(c_34,plain,(
    ! [A_13] :
      ( m1_subset_1('#skF_3'(A_13),k1_zfmisc_1(A_13))
      | v1_xboole_0(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_158,plain,
    ( m1_subset_1('#skF_3'('#skF_4'),k1_xboole_0)
    | v1_xboole_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_152,c_34])).

tff(c_173,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_158])).

tff(c_176,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_173,c_2])).

tff(c_180,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_176])).

tff(c_182,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_158])).

tff(c_153,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_148])).

tff(c_181,plain,(
    m1_subset_1('#skF_3'('#skF_4'),k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_158])).

tff(c_207,plain,(
    ! [B_53,A_54] :
      ( v1_xboole_0(B_53)
      | ~ m1_subset_1(B_53,A_54)
      | ~ v1_xboole_0(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_210,plain,
    ( v1_xboole_0('#skF_3'('#skF_4'))
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_181,c_207])).

tff(c_222,plain,(
    v1_xboole_0('#skF_3'('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_153,c_210])).

tff(c_32,plain,(
    ! [A_13] :
      ( ~ v1_xboole_0('#skF_3'(A_13))
      | v1_xboole_0(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_228,plain,(
    v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_222,c_32])).

tff(c_235,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_182,c_228])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 19:56:08 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.00/1.22  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.00/1.23  
% 2.00/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.00/1.23  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k4_xboole_0 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_5 > #skF_4 > #skF_3 > #skF_2 > #skF_1
% 2.00/1.23  
% 2.00/1.23  %Foreground sorts:
% 2.00/1.23  
% 2.00/1.23  
% 2.00/1.23  %Background operators:
% 2.00/1.23  
% 2.00/1.23  
% 2.00/1.23  %Foreground operators:
% 2.00/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.00/1.23  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.00/1.23  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.00/1.23  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.00/1.23  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.00/1.23  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.00/1.23  tff('#skF_5', type, '#skF_5': $i).
% 2.00/1.23  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.00/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.00/1.23  tff('#skF_4', type, '#skF_4': $i).
% 2.00/1.23  tff('#skF_3', type, '#skF_3': $i > $i).
% 2.00/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.00/1.23  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.00/1.23  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.00/1.23  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.00/1.23  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.00/1.23  
% 2.08/1.24  tff(f_74, negated_conjecture, ~(![A, B]: (m1_subset_1(B, A) => (~(A = k1_xboole_0) => m1_subset_1(k1_tarski(B), k1_zfmisc_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_subset_1)).
% 2.08/1.24  tff(f_57, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 2.08/1.24  tff(f_44, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_xboole_0) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l35_zfmisc_1)).
% 2.08/1.24  tff(f_33, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_xboole_1)).
% 2.08/1.24  tff(f_40, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 2.08/1.24  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.08/1.24  tff(f_66, axiom, (![A]: (~v1_xboole_0(A) => (?[B]: (m1_subset_1(B, k1_zfmisc_1(A)) & ~v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc1_subset_1)).
% 2.08/1.24  tff(c_38, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.08/1.24  tff(c_40, plain, (m1_subset_1('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.08/1.24  tff(c_51, plain, (![B_22, A_23]: (v1_xboole_0(B_22) | ~m1_subset_1(B_22, A_23) | ~v1_xboole_0(A_23))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.08/1.24  tff(c_63, plain, (v1_xboole_0('#skF_5') | ~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_40, c_51])).
% 2.08/1.24  tff(c_64, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_63])).
% 2.08/1.24  tff(c_26, plain, (![B_12, A_11]: (r2_hidden(B_12, A_11) | ~m1_subset_1(B_12, A_11) | v1_xboole_0(A_11))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.08/1.24  tff(c_22, plain, (![A_9, B_10]: (k4_xboole_0(k1_tarski(A_9), B_10)=k1_xboole_0 | ~r2_hidden(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.08/1.25  tff(c_4, plain, (![A_2, B_3]: (r1_tarski(A_2, B_3) | k4_xboole_0(A_2, B_3)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.08/1.25  tff(c_44, plain, (![B_18, A_19]: (m1_subset_1(B_18, A_19) | ~v1_xboole_0(B_18) | ~v1_xboole_0(A_19))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.08/1.25  tff(c_36, plain, (~m1_subset_1(k1_tarski('#skF_5'), k1_zfmisc_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.08/1.25  tff(c_48, plain, (~v1_xboole_0(k1_tarski('#skF_5')) | ~v1_xboole_0(k1_zfmisc_1('#skF_4'))), inference(resolution, [status(thm)], [c_44, c_36])).
% 2.08/1.25  tff(c_49, plain, (~v1_xboole_0(k1_zfmisc_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_48])).
% 2.08/1.25  tff(c_10, plain, (![C_8, A_4]: (r2_hidden(C_8, k1_zfmisc_1(A_4)) | ~r1_tarski(C_8, A_4))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.08/1.25  tff(c_96, plain, (![B_36, A_37]: (m1_subset_1(B_36, A_37) | ~r2_hidden(B_36, A_37) | v1_xboole_0(A_37))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.08/1.25  tff(c_106, plain, (![C_39, A_40]: (m1_subset_1(C_39, k1_zfmisc_1(A_40)) | v1_xboole_0(k1_zfmisc_1(A_40)) | ~r1_tarski(C_39, A_40))), inference(resolution, [status(thm)], [c_10, c_96])).
% 2.08/1.25  tff(c_112, plain, (v1_xboole_0(k1_zfmisc_1('#skF_4')) | ~r1_tarski(k1_tarski('#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_106, c_36])).
% 2.08/1.25  tff(c_116, plain, (~r1_tarski(k1_tarski('#skF_5'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_49, c_112])).
% 2.08/1.25  tff(c_120, plain, (k4_xboole_0(k1_tarski('#skF_5'), '#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_4, c_116])).
% 2.08/1.25  tff(c_124, plain, (~r2_hidden('#skF_5', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_22, c_120])).
% 2.08/1.25  tff(c_127, plain, (~m1_subset_1('#skF_5', '#skF_4') | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_26, c_124])).
% 2.08/1.25  tff(c_130, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_127])).
% 2.08/1.25  tff(c_132, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_130])).
% 2.08/1.25  tff(c_134, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_63])).
% 2.08/1.25  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.08/1.25  tff(c_142, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_134, c_2])).
% 2.08/1.25  tff(c_146, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_142])).
% 2.08/1.25  tff(c_148, plain, (v1_xboole_0(k1_zfmisc_1('#skF_4'))), inference(splitRight, [status(thm)], [c_48])).
% 2.08/1.25  tff(c_152, plain, (k1_zfmisc_1('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_148, c_2])).
% 2.08/1.25  tff(c_34, plain, (![A_13]: (m1_subset_1('#skF_3'(A_13), k1_zfmisc_1(A_13)) | v1_xboole_0(A_13))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.08/1.25  tff(c_158, plain, (m1_subset_1('#skF_3'('#skF_4'), k1_xboole_0) | v1_xboole_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_152, c_34])).
% 2.08/1.25  tff(c_173, plain, (v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_158])).
% 2.08/1.25  tff(c_176, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_173, c_2])).
% 2.08/1.25  tff(c_180, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_176])).
% 2.08/1.25  tff(c_182, plain, (~v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_158])).
% 2.08/1.25  tff(c_153, plain, (v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_152, c_148])).
% 2.08/1.25  tff(c_181, plain, (m1_subset_1('#skF_3'('#skF_4'), k1_xboole_0)), inference(splitRight, [status(thm)], [c_158])).
% 2.08/1.25  tff(c_207, plain, (![B_53, A_54]: (v1_xboole_0(B_53) | ~m1_subset_1(B_53, A_54) | ~v1_xboole_0(A_54))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.08/1.25  tff(c_210, plain, (v1_xboole_0('#skF_3'('#skF_4')) | ~v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_181, c_207])).
% 2.08/1.25  tff(c_222, plain, (v1_xboole_0('#skF_3'('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_153, c_210])).
% 2.08/1.25  tff(c_32, plain, (![A_13]: (~v1_xboole_0('#skF_3'(A_13)) | v1_xboole_0(A_13))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.08/1.25  tff(c_228, plain, (v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_222, c_32])).
% 2.08/1.25  tff(c_235, plain, $false, inference(negUnitSimplification, [status(thm)], [c_182, c_228])).
% 2.08/1.25  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.08/1.25  
% 2.08/1.25  Inference rules
% 2.08/1.25  ----------------------
% 2.08/1.25  #Ref     : 0
% 2.08/1.25  #Sup     : 37
% 2.08/1.25  #Fact    : 0
% 2.08/1.25  #Define  : 0
% 2.08/1.25  #Split   : 3
% 2.08/1.25  #Chain   : 0
% 2.08/1.25  #Close   : 0
% 2.08/1.25  
% 2.08/1.25  Ordering : KBO
% 2.08/1.25  
% 2.08/1.25  Simplification rules
% 2.08/1.25  ----------------------
% 2.08/1.25  #Subsume      : 2
% 2.08/1.25  #Demod        : 5
% 2.08/1.25  #Tautology    : 15
% 2.08/1.25  #SimpNegUnit  : 5
% 2.08/1.25  #BackRed      : 2
% 2.08/1.25  
% 2.08/1.25  #Partial instantiations: 0
% 2.08/1.25  #Strategies tried      : 1
% 2.08/1.25  
% 2.08/1.25  Timing (in seconds)
% 2.08/1.25  ----------------------
% 2.08/1.25  Preprocessing        : 0.30
% 2.08/1.25  Parsing              : 0.16
% 2.08/1.25  CNF conversion       : 0.02
% 2.08/1.25  Main loop            : 0.17
% 2.08/1.25  Inferencing          : 0.06
% 2.08/1.25  Reduction            : 0.05
% 2.08/1.25  Demodulation         : 0.03
% 2.08/1.25  BG Simplification    : 0.01
% 2.08/1.25  Subsumption          : 0.03
% 2.08/1.25  Abstraction          : 0.01
% 2.08/1.25  MUC search           : 0.00
% 2.08/1.25  Cooper               : 0.00
% 2.08/1.25  Total                : 0.50
% 2.08/1.25  Index Insertion      : 0.00
% 2.08/1.25  Index Deletion       : 0.00
% 2.08/1.25  Index Matching       : 0.00
% 2.08/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
