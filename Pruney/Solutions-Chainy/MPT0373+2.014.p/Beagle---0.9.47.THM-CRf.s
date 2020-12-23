%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:58 EST 2020

% Result     : Theorem 1.95s
% Output     : CNFRefutation 1.95s
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

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
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 14:45:40 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.95/1.21  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.95/1.22  
% 1.95/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.95/1.22  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k4_xboole_0 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_5 > #skF_4 > #skF_3 > #skF_2 > #skF_1
% 1.95/1.22  
% 1.95/1.22  %Foreground sorts:
% 1.95/1.22  
% 1.95/1.22  
% 1.95/1.22  %Background operators:
% 1.95/1.22  
% 1.95/1.22  
% 1.95/1.22  %Foreground operators:
% 1.95/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.95/1.22  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.95/1.22  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.95/1.22  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.95/1.22  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.95/1.22  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.95/1.22  tff('#skF_5', type, '#skF_5': $i).
% 1.95/1.22  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.95/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.95/1.22  tff('#skF_4', type, '#skF_4': $i).
% 1.95/1.22  tff('#skF_3', type, '#skF_3': $i > $i).
% 1.95/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.95/1.22  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.95/1.22  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.95/1.22  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.95/1.22  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.95/1.22  
% 1.95/1.24  tff(f_74, negated_conjecture, ~(![A, B]: (m1_subset_1(B, A) => (~(A = k1_xboole_0) => m1_subset_1(k1_tarski(B), k1_zfmisc_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_subset_1)).
% 1.95/1.24  tff(f_57, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 1.95/1.24  tff(f_44, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_xboole_0) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t68_zfmisc_1)).
% 1.95/1.24  tff(f_33, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 1.95/1.24  tff(f_40, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 1.95/1.24  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 1.95/1.24  tff(f_66, axiom, (![A]: (~v1_xboole_0(A) => (?[B]: (m1_subset_1(B, k1_zfmisc_1(A)) & ~v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc1_subset_1)).
% 1.95/1.24  tff(c_38, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_74])).
% 1.95/1.24  tff(c_40, plain, (m1_subset_1('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_74])).
% 1.95/1.24  tff(c_51, plain, (![B_22, A_23]: (v1_xboole_0(B_22) | ~m1_subset_1(B_22, A_23) | ~v1_xboole_0(A_23))), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.95/1.24  tff(c_63, plain, (v1_xboole_0('#skF_5') | ~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_40, c_51])).
% 1.95/1.24  tff(c_64, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_63])).
% 1.95/1.24  tff(c_26, plain, (![B_12, A_11]: (r2_hidden(B_12, A_11) | ~m1_subset_1(B_12, A_11) | v1_xboole_0(A_11))), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.95/1.24  tff(c_22, plain, (![A_9, B_10]: (k4_xboole_0(k1_tarski(A_9), B_10)=k1_xboole_0 | ~r2_hidden(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.95/1.24  tff(c_4, plain, (![A_2, B_3]: (r1_tarski(A_2, B_3) | k4_xboole_0(A_2, B_3)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.95/1.24  tff(c_44, plain, (![B_18, A_19]: (m1_subset_1(B_18, A_19) | ~v1_xboole_0(B_18) | ~v1_xboole_0(A_19))), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.95/1.24  tff(c_36, plain, (~m1_subset_1(k1_tarski('#skF_5'), k1_zfmisc_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_74])).
% 1.95/1.24  tff(c_48, plain, (~v1_xboole_0(k1_tarski('#skF_5')) | ~v1_xboole_0(k1_zfmisc_1('#skF_4'))), inference(resolution, [status(thm)], [c_44, c_36])).
% 1.95/1.24  tff(c_49, plain, (~v1_xboole_0(k1_zfmisc_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_48])).
% 1.95/1.24  tff(c_10, plain, (![C_8, A_4]: (r2_hidden(C_8, k1_zfmisc_1(A_4)) | ~r1_tarski(C_8, A_4))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.95/1.24  tff(c_96, plain, (![B_36, A_37]: (m1_subset_1(B_36, A_37) | ~r2_hidden(B_36, A_37) | v1_xboole_0(A_37))), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.95/1.24  tff(c_106, plain, (![C_39, A_40]: (m1_subset_1(C_39, k1_zfmisc_1(A_40)) | v1_xboole_0(k1_zfmisc_1(A_40)) | ~r1_tarski(C_39, A_40))), inference(resolution, [status(thm)], [c_10, c_96])).
% 1.95/1.24  tff(c_112, plain, (v1_xboole_0(k1_zfmisc_1('#skF_4')) | ~r1_tarski(k1_tarski('#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_106, c_36])).
% 1.95/1.24  tff(c_116, plain, (~r1_tarski(k1_tarski('#skF_5'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_49, c_112])).
% 1.95/1.24  tff(c_120, plain, (k4_xboole_0(k1_tarski('#skF_5'), '#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_4, c_116])).
% 1.95/1.24  tff(c_124, plain, (~r2_hidden('#skF_5', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_22, c_120])).
% 1.95/1.24  tff(c_127, plain, (~m1_subset_1('#skF_5', '#skF_4') | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_26, c_124])).
% 1.95/1.24  tff(c_130, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_127])).
% 1.95/1.24  tff(c_132, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_130])).
% 1.95/1.24  tff(c_134, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_63])).
% 1.95/1.24  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.95/1.24  tff(c_142, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_134, c_2])).
% 1.95/1.24  tff(c_146, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_142])).
% 1.95/1.24  tff(c_148, plain, (v1_xboole_0(k1_zfmisc_1('#skF_4'))), inference(splitRight, [status(thm)], [c_48])).
% 1.95/1.24  tff(c_152, plain, (k1_zfmisc_1('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_148, c_2])).
% 1.95/1.24  tff(c_34, plain, (![A_13]: (m1_subset_1('#skF_3'(A_13), k1_zfmisc_1(A_13)) | v1_xboole_0(A_13))), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.95/1.24  tff(c_158, plain, (m1_subset_1('#skF_3'('#skF_4'), k1_xboole_0) | v1_xboole_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_152, c_34])).
% 1.95/1.24  tff(c_173, plain, (v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_158])).
% 1.95/1.24  tff(c_176, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_173, c_2])).
% 1.95/1.24  tff(c_180, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_176])).
% 1.95/1.24  tff(c_182, plain, (~v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_158])).
% 1.95/1.24  tff(c_153, plain, (v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_152, c_148])).
% 1.95/1.24  tff(c_181, plain, (m1_subset_1('#skF_3'('#skF_4'), k1_xboole_0)), inference(splitRight, [status(thm)], [c_158])).
% 1.95/1.24  tff(c_207, plain, (![B_53, A_54]: (v1_xboole_0(B_53) | ~m1_subset_1(B_53, A_54) | ~v1_xboole_0(A_54))), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.95/1.24  tff(c_210, plain, (v1_xboole_0('#skF_3'('#skF_4')) | ~v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_181, c_207])).
% 1.95/1.24  tff(c_222, plain, (v1_xboole_0('#skF_3'('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_153, c_210])).
% 1.95/1.24  tff(c_32, plain, (![A_13]: (~v1_xboole_0('#skF_3'(A_13)) | v1_xboole_0(A_13))), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.95/1.24  tff(c_228, plain, (v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_222, c_32])).
% 1.95/1.24  tff(c_235, plain, $false, inference(negUnitSimplification, [status(thm)], [c_182, c_228])).
% 1.95/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.95/1.24  
% 1.95/1.24  Inference rules
% 1.95/1.24  ----------------------
% 1.95/1.24  #Ref     : 0
% 1.95/1.24  #Sup     : 37
% 1.95/1.24  #Fact    : 0
% 1.95/1.24  #Define  : 0
% 1.95/1.24  #Split   : 3
% 1.95/1.24  #Chain   : 0
% 1.95/1.24  #Close   : 0
% 1.95/1.24  
% 1.95/1.24  Ordering : KBO
% 1.95/1.24  
% 1.95/1.24  Simplification rules
% 1.95/1.24  ----------------------
% 1.95/1.24  #Subsume      : 2
% 1.95/1.24  #Demod        : 5
% 1.95/1.24  #Tautology    : 15
% 1.95/1.24  #SimpNegUnit  : 5
% 1.95/1.24  #BackRed      : 2
% 1.95/1.24  
% 1.95/1.24  #Partial instantiations: 0
% 1.95/1.24  #Strategies tried      : 1
% 1.95/1.24  
% 1.95/1.24  Timing (in seconds)
% 1.95/1.24  ----------------------
% 1.95/1.24  Preprocessing        : 0.29
% 1.95/1.24  Parsing              : 0.15
% 1.95/1.24  CNF conversion       : 0.02
% 1.95/1.24  Main loop            : 0.17
% 1.95/1.24  Inferencing          : 0.07
% 1.95/1.24  Reduction            : 0.05
% 1.95/1.24  Demodulation         : 0.03
% 1.95/1.24  BG Simplification    : 0.01
% 1.95/1.24  Subsumption          : 0.03
% 1.95/1.24  Abstraction          : 0.01
% 1.95/1.24  MUC search           : 0.00
% 1.95/1.24  Cooper               : 0.00
% 1.95/1.24  Total                : 0.50
% 1.95/1.24  Index Insertion      : 0.00
% 1.95/1.24  Index Deletion       : 0.00
% 1.95/1.24  Index Matching       : 0.00
% 1.95/1.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
