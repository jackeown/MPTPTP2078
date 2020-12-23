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
% DateTime   : Thu Dec  3 09:56:57 EST 2020

% Result     : Theorem 1.93s
% Output     : CNFRefutation 2.19s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 104 expanded)
%              Number of leaves         :   23 (  45 expanded)
%              Depth                    :   11
%              Number of atoms          :   77 ( 197 expanded)
%              Number of equality atoms :    8 (  26 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k1_enumset1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff(f_71,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,A)
       => ( A != k1_xboole_0
         => m1_subset_1(k1_tarski(B),k1_zfmisc_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_subset_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_50,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_46,axiom,(
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
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_26,plain,(
    ! [A_14,B_15] :
      ( r1_tarski(k1_tarski(A_14),B_15)
      | ~ r2_hidden(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_40,plain,(
    m1_subset_1('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_78,plain,(
    ! [B_31,A_32] :
      ( v1_xboole_0(B_31)
      | ~ m1_subset_1(B_31,A_32)
      | ~ v1_xboole_0(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_86,plain,
    ( v1_xboole_0('#skF_5')
    | ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_78])).

tff(c_87,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_86])).

tff(c_30,plain,(
    ! [B_17,A_16] :
      ( r2_hidden(B_17,A_16)
      | ~ m1_subset_1(B_17,A_16)
      | v1_xboole_0(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_66,plain,(
    ! [B_25,A_26] :
      ( m1_subset_1(B_25,A_26)
      | ~ v1_xboole_0(B_25)
      | ~ v1_xboole_0(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_36,plain,(
    ~ m1_subset_1(k1_tarski('#skF_5'),k1_zfmisc_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_70,plain,
    ( ~ v1_xboole_0(k1_tarski('#skF_5'))
    | ~ v1_xboole_0(k1_zfmisc_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_66,c_36])).

tff(c_71,plain,(
    ~ v1_xboole_0(k1_zfmisc_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_70])).

tff(c_14,plain,(
    ! [C_13,A_9] :
      ( r2_hidden(C_13,k1_zfmisc_1(A_9))
      | ~ r1_tarski(C_13,A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_114,plain,(
    ! [B_41,A_42] :
      ( m1_subset_1(B_41,A_42)
      | ~ r2_hidden(B_41,A_42)
      | v1_xboole_0(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_133,plain,(
    ! [C_45,A_46] :
      ( m1_subset_1(C_45,k1_zfmisc_1(A_46))
      | v1_xboole_0(k1_zfmisc_1(A_46))
      | ~ r1_tarski(C_45,A_46) ) ),
    inference(resolution,[status(thm)],[c_14,c_114])).

tff(c_139,plain,
    ( v1_xboole_0(k1_zfmisc_1('#skF_4'))
    | ~ r1_tarski(k1_tarski('#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_133,c_36])).

tff(c_143,plain,(
    ~ r1_tarski(k1_tarski('#skF_5'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_71,c_139])).

tff(c_147,plain,(
    ~ r2_hidden('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_26,c_143])).

tff(c_164,plain,
    ( ~ m1_subset_1('#skF_5','#skF_4')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_147])).

tff(c_167,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_164])).

tff(c_169,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_87,c_167])).

tff(c_171,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_86])).

tff(c_6,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_178,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_171,c_6])).

tff(c_182,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_178])).

tff(c_184,plain,(
    v1_xboole_0(k1_zfmisc_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_188,plain,(
    k1_zfmisc_1('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_184,c_6])).

tff(c_189,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_188,c_184])).

tff(c_228,plain,(
    ! [C_56,A_57] :
      ( r2_hidden(C_56,k1_zfmisc_1(A_57))
      | ~ r1_tarski(C_56,A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_240,plain,(
    ! [C_58] :
      ( r2_hidden(C_58,k1_xboole_0)
      | ~ r1_tarski(C_58,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_188,c_228])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_246,plain,(
    ! [C_58] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r1_tarski(C_58,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_240,c_2])).

tff(c_252,plain,(
    ! [C_59] : ~ r1_tarski(C_59,'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_189,c_246])).

tff(c_265,plain,(
    ! [A_61] : ~ r2_hidden(A_61,'#skF_4') ),
    inference(resolution,[status(thm)],[c_26,c_252])).

tff(c_270,plain,(
    v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_4,c_265])).

tff(c_273,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_270,c_6])).

tff(c_277,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_273])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:34:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.93/1.30  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.93/1.30  
% 1.93/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.93/1.30  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k1_enumset1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2
% 1.93/1.30  
% 1.93/1.30  %Foreground sorts:
% 1.93/1.30  
% 1.93/1.30  
% 1.93/1.30  %Background operators:
% 1.93/1.30  
% 1.93/1.30  
% 1.93/1.30  %Foreground operators:
% 1.93/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.93/1.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.93/1.30  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.93/1.30  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.93/1.30  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.93/1.30  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 1.93/1.30  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.93/1.30  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.93/1.30  tff('#skF_5', type, '#skF_5': $i).
% 1.93/1.30  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.93/1.30  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.93/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.93/1.30  tff('#skF_4', type, '#skF_4': $i).
% 1.93/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.93/1.30  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.93/1.30  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.93/1.30  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.93/1.30  
% 2.19/1.32  tff(f_71, negated_conjecture, ~(![A, B]: (m1_subset_1(B, A) => (~(A = k1_xboole_0) => m1_subset_1(k1_tarski(B), k1_zfmisc_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_subset_1)).
% 2.19/1.32  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.19/1.32  tff(f_50, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 2.19/1.32  tff(f_63, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 2.19/1.32  tff(f_46, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 2.19/1.32  tff(f_35, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.19/1.32  tff(c_38, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.19/1.32  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.19/1.32  tff(c_26, plain, (![A_14, B_15]: (r1_tarski(k1_tarski(A_14), B_15) | ~r2_hidden(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.19/1.32  tff(c_40, plain, (m1_subset_1('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.19/1.32  tff(c_78, plain, (![B_31, A_32]: (v1_xboole_0(B_31) | ~m1_subset_1(B_31, A_32) | ~v1_xboole_0(A_32))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.19/1.32  tff(c_86, plain, (v1_xboole_0('#skF_5') | ~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_40, c_78])).
% 2.19/1.32  tff(c_87, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_86])).
% 2.19/1.32  tff(c_30, plain, (![B_17, A_16]: (r2_hidden(B_17, A_16) | ~m1_subset_1(B_17, A_16) | v1_xboole_0(A_16))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.19/1.32  tff(c_66, plain, (![B_25, A_26]: (m1_subset_1(B_25, A_26) | ~v1_xboole_0(B_25) | ~v1_xboole_0(A_26))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.19/1.32  tff(c_36, plain, (~m1_subset_1(k1_tarski('#skF_5'), k1_zfmisc_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.19/1.32  tff(c_70, plain, (~v1_xboole_0(k1_tarski('#skF_5')) | ~v1_xboole_0(k1_zfmisc_1('#skF_4'))), inference(resolution, [status(thm)], [c_66, c_36])).
% 2.19/1.32  tff(c_71, plain, (~v1_xboole_0(k1_zfmisc_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_70])).
% 2.19/1.32  tff(c_14, plain, (![C_13, A_9]: (r2_hidden(C_13, k1_zfmisc_1(A_9)) | ~r1_tarski(C_13, A_9))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.19/1.32  tff(c_114, plain, (![B_41, A_42]: (m1_subset_1(B_41, A_42) | ~r2_hidden(B_41, A_42) | v1_xboole_0(A_42))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.19/1.32  tff(c_133, plain, (![C_45, A_46]: (m1_subset_1(C_45, k1_zfmisc_1(A_46)) | v1_xboole_0(k1_zfmisc_1(A_46)) | ~r1_tarski(C_45, A_46))), inference(resolution, [status(thm)], [c_14, c_114])).
% 2.19/1.32  tff(c_139, plain, (v1_xboole_0(k1_zfmisc_1('#skF_4')) | ~r1_tarski(k1_tarski('#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_133, c_36])).
% 2.19/1.32  tff(c_143, plain, (~r1_tarski(k1_tarski('#skF_5'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_71, c_139])).
% 2.19/1.32  tff(c_147, plain, (~r2_hidden('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_26, c_143])).
% 2.19/1.32  tff(c_164, plain, (~m1_subset_1('#skF_5', '#skF_4') | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_30, c_147])).
% 2.19/1.32  tff(c_167, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_164])).
% 2.19/1.32  tff(c_169, plain, $false, inference(negUnitSimplification, [status(thm)], [c_87, c_167])).
% 2.19/1.32  tff(c_171, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_86])).
% 2.19/1.32  tff(c_6, plain, (![A_5]: (k1_xboole_0=A_5 | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.19/1.32  tff(c_178, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_171, c_6])).
% 2.19/1.32  tff(c_182, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_178])).
% 2.19/1.32  tff(c_184, plain, (v1_xboole_0(k1_zfmisc_1('#skF_4'))), inference(splitRight, [status(thm)], [c_70])).
% 2.19/1.32  tff(c_188, plain, (k1_zfmisc_1('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_184, c_6])).
% 2.19/1.32  tff(c_189, plain, (v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_188, c_184])).
% 2.19/1.32  tff(c_228, plain, (![C_56, A_57]: (r2_hidden(C_56, k1_zfmisc_1(A_57)) | ~r1_tarski(C_56, A_57))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.19/1.32  tff(c_240, plain, (![C_58]: (r2_hidden(C_58, k1_xboole_0) | ~r1_tarski(C_58, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_188, c_228])).
% 2.19/1.32  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.19/1.32  tff(c_246, plain, (![C_58]: (~v1_xboole_0(k1_xboole_0) | ~r1_tarski(C_58, '#skF_4'))), inference(resolution, [status(thm)], [c_240, c_2])).
% 2.19/1.32  tff(c_252, plain, (![C_59]: (~r1_tarski(C_59, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_189, c_246])).
% 2.19/1.32  tff(c_265, plain, (![A_61]: (~r2_hidden(A_61, '#skF_4'))), inference(resolution, [status(thm)], [c_26, c_252])).
% 2.19/1.32  tff(c_270, plain, (v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_4, c_265])).
% 2.19/1.32  tff(c_273, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_270, c_6])).
% 2.19/1.32  tff(c_277, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_273])).
% 2.19/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.19/1.32  
% 2.19/1.32  Inference rules
% 2.19/1.32  ----------------------
% 2.19/1.32  #Ref     : 0
% 2.19/1.32  #Sup     : 45
% 2.19/1.32  #Fact    : 0
% 2.19/1.32  #Define  : 0
% 2.19/1.32  #Split   : 2
% 2.19/1.32  #Chain   : 0
% 2.19/1.32  #Close   : 0
% 2.19/1.32  
% 2.19/1.32  Ordering : KBO
% 2.19/1.32  
% 2.19/1.32  Simplification rules
% 2.19/1.32  ----------------------
% 2.19/1.32  #Subsume      : 4
% 2.19/1.32  #Demod        : 7
% 2.19/1.32  #Tautology    : 19
% 2.19/1.32  #SimpNegUnit  : 5
% 2.19/1.32  #BackRed      : 3
% 2.19/1.32  
% 2.19/1.32  #Partial instantiations: 0
% 2.19/1.32  #Strategies tried      : 1
% 2.19/1.32  
% 2.19/1.32  Timing (in seconds)
% 2.19/1.32  ----------------------
% 2.19/1.32  Preprocessing        : 0.32
% 2.19/1.32  Parsing              : 0.16
% 2.19/1.32  CNF conversion       : 0.02
% 2.19/1.32  Main loop            : 0.18
% 2.19/1.32  Inferencing          : 0.07
% 2.19/1.32  Reduction            : 0.05
% 2.19/1.32  Demodulation         : 0.03
% 2.19/1.32  BG Simplification    : 0.02
% 2.19/1.32  Subsumption          : 0.03
% 2.19/1.32  Abstraction          : 0.01
% 2.19/1.32  MUC search           : 0.00
% 2.19/1.32  Cooper               : 0.00
% 2.19/1.32  Total                : 0.53
% 2.19/1.32  Index Insertion      : 0.00
% 2.19/1.32  Index Deletion       : 0.00
% 2.19/1.32  Index Matching       : 0.00
% 2.19/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
