%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:05 EST 2020

% Result     : Theorem 1.93s
% Output     : CNFRefutation 2.09s
% Verified   : 
% Statistics : Number of formulae       :   56 (  89 expanded)
%              Number of leaves         :   20 (  37 expanded)
%              Depth                    :   11
%              Number of atoms          :   80 ( 152 expanded)
%              Number of equality atoms :   21 (  45 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > m1_setfam_1 > k5_setfam_1 > #nlpp > k3_tarski > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(m1_setfam_1,type,(
    m1_setfam_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k5_setfam_1,type,(
    k5_setfam_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_63,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
       => ( m1_setfam_1(B,A)
        <=> k5_setfam_1(A,B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_setfam_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k5_setfam_1(A,B) = k3_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k5_setfam_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_42,axiom,(
    ! [A,B] :
      ( m1_setfam_1(B,A)
    <=> r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_setfam_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
         => r1_tarski(C,B) )
     => r1_tarski(k3_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_zfmisc_1)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_50,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(c_24,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_153,plain,(
    ! [A_48,B_49] :
      ( k5_setfam_1(A_48,B_49) = k3_tarski(B_49)
      | ~ m1_subset_1(B_49,k1_zfmisc_1(k1_zfmisc_1(A_48))) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_162,plain,(
    k5_setfam_1('#skF_2','#skF_3') = k3_tarski('#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_153])).

tff(c_26,plain,
    ( k5_setfam_1('#skF_2','#skF_3') != '#skF_2'
    | ~ m1_setfam_1('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_35,plain,(
    ~ m1_setfam_1('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_26])).

tff(c_32,plain,
    ( m1_setfam_1('#skF_3','#skF_2')
    | k5_setfam_1('#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_53,plain,(
    k5_setfam_1('#skF_2','#skF_3') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_35,c_32])).

tff(c_83,plain,(
    ! [A_31,B_32] :
      ( k5_setfam_1(A_31,B_32) = k3_tarski(B_32)
      | ~ m1_subset_1(B_32,k1_zfmisc_1(k1_zfmisc_1(A_31))) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_90,plain,(
    k5_setfam_1('#skF_2','#skF_3') = k3_tarski('#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_83])).

tff(c_93,plain,(
    k3_tarski('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_90])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_37,plain,(
    ! [B_18,A_19] :
      ( m1_setfam_1(B_18,A_19)
      | ~ r1_tarski(A_19,k3_tarski(B_18)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_42,plain,(
    ! [B_18] : m1_setfam_1(B_18,k3_tarski(B_18)) ),
    inference(resolution,[status(thm)],[c_6,c_37])).

tff(c_100,plain,(
    m1_setfam_1('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_93,c_42])).

tff(c_107,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_35,c_100])).

tff(c_108,plain,(
    k5_setfam_1('#skF_2','#skF_3') != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_163,plain,(
    k3_tarski('#skF_3') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_162,c_108])).

tff(c_109,plain,(
    m1_setfam_1('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_10,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),A_3)
      | r1_tarski(k3_tarski(A_3),B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_168,plain,(
    ! [A_50,C_51,B_52] :
      ( m1_subset_1(A_50,C_51)
      | ~ m1_subset_1(B_52,k1_zfmisc_1(C_51))
      | ~ r2_hidden(A_50,B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_175,plain,(
    ! [A_53] :
      ( m1_subset_1(A_53,k1_zfmisc_1('#skF_2'))
      | ~ r2_hidden(A_53,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_24,c_168])).

tff(c_18,plain,(
    ! [A_10,B_11] :
      ( r1_tarski(A_10,B_11)
      | ~ m1_subset_1(A_10,k1_zfmisc_1(B_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_183,plain,(
    ! [A_54] :
      ( r1_tarski(A_54,'#skF_2')
      | ~ r2_hidden(A_54,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_175,c_18])).

tff(c_188,plain,(
    ! [B_4] :
      ( r1_tarski('#skF_1'('#skF_3',B_4),'#skF_2')
      | r1_tarski(k3_tarski('#skF_3'),B_4) ) ),
    inference(resolution,[status(thm)],[c_10,c_183])).

tff(c_12,plain,(
    ! [A_6,B_7] :
      ( r1_tarski(A_6,k3_tarski(B_7))
      | ~ m1_setfam_1(B_7,A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_133,plain,(
    ! [B_42,A_43] :
      ( B_42 = A_43
      | ~ r1_tarski(B_42,A_43)
      | ~ r1_tarski(A_43,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_229,plain,(
    ! [B_64,A_65] :
      ( k3_tarski(B_64) = A_65
      | ~ r1_tarski(k3_tarski(B_64),A_65)
      | ~ m1_setfam_1(B_64,A_65) ) ),
    inference(resolution,[status(thm)],[c_12,c_133])).

tff(c_280,plain,(
    ! [B_71] :
      ( k3_tarski('#skF_3') = B_71
      | ~ m1_setfam_1('#skF_3',B_71)
      | r1_tarski('#skF_1'('#skF_3',B_71),'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_188,c_229])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( ~ r1_tarski('#skF_1'(A_3,B_4),B_4)
      | r1_tarski(k3_tarski(A_3),B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_283,plain,
    ( r1_tarski(k3_tarski('#skF_3'),'#skF_2')
    | k3_tarski('#skF_3') = '#skF_2'
    | ~ m1_setfam_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_280,c_8])).

tff(c_288,plain,
    ( r1_tarski(k3_tarski('#skF_3'),'#skF_2')
    | k3_tarski('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_283])).

tff(c_289,plain,(
    r1_tarski(k3_tarski('#skF_3'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_163,c_288])).

tff(c_141,plain,(
    ! [B_7,A_6] :
      ( k3_tarski(B_7) = A_6
      | ~ r1_tarski(k3_tarski(B_7),A_6)
      | ~ m1_setfam_1(B_7,A_6) ) ),
    inference(resolution,[status(thm)],[c_12,c_133])).

tff(c_293,plain,
    ( k3_tarski('#skF_3') = '#skF_2'
    | ~ m1_setfam_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_289,c_141])).

tff(c_298,plain,(
    k3_tarski('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_293])).

tff(c_300,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_163,c_298])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:36:42 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.93/1.22  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.93/1.22  
% 1.93/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.93/1.23  %$ r2_hidden > r1_tarski > m1_subset_1 > m1_setfam_1 > k5_setfam_1 > #nlpp > k3_tarski > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 1.93/1.23  
% 1.93/1.23  %Foreground sorts:
% 1.93/1.23  
% 1.93/1.23  
% 1.93/1.23  %Background operators:
% 1.93/1.23  
% 1.93/1.23  
% 1.93/1.23  %Foreground operators:
% 1.93/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.93/1.23  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.93/1.23  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.93/1.23  tff('#skF_2', type, '#skF_2': $i).
% 1.93/1.23  tff('#skF_3', type, '#skF_3': $i).
% 1.93/1.23  tff(m1_setfam_1, type, m1_setfam_1: ($i * $i) > $o).
% 1.93/1.23  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.93/1.23  tff(k5_setfam_1, type, k5_setfam_1: ($i * $i) > $i).
% 1.93/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.93/1.23  tff(k3_tarski, type, k3_tarski: $i > $i).
% 1.93/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.93/1.23  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.93/1.23  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.93/1.23  
% 2.09/1.24  tff(f_63, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (m1_setfam_1(B, A) <=> (k5_setfam_1(A, B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_setfam_1)).
% 2.09/1.24  tff(f_46, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k5_setfam_1(A, B) = k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k5_setfam_1)).
% 2.09/1.24  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.09/1.24  tff(f_42, axiom, (![A, B]: (m1_setfam_1(B, A) <=> r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_setfam_1)).
% 2.09/1.24  tff(f_38, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) => r1_tarski(C, B))) => r1_tarski(k3_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_zfmisc_1)).
% 2.09/1.24  tff(f_56, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 2.09/1.24  tff(f_50, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.09/1.24  tff(c_24, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.09/1.24  tff(c_153, plain, (![A_48, B_49]: (k5_setfam_1(A_48, B_49)=k3_tarski(B_49) | ~m1_subset_1(B_49, k1_zfmisc_1(k1_zfmisc_1(A_48))))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.09/1.24  tff(c_162, plain, (k5_setfam_1('#skF_2', '#skF_3')=k3_tarski('#skF_3')), inference(resolution, [status(thm)], [c_24, c_153])).
% 2.09/1.24  tff(c_26, plain, (k5_setfam_1('#skF_2', '#skF_3')!='#skF_2' | ~m1_setfam_1('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.09/1.24  tff(c_35, plain, (~m1_setfam_1('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_26])).
% 2.09/1.24  tff(c_32, plain, (m1_setfam_1('#skF_3', '#skF_2') | k5_setfam_1('#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.09/1.24  tff(c_53, plain, (k5_setfam_1('#skF_2', '#skF_3')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_35, c_32])).
% 2.09/1.24  tff(c_83, plain, (![A_31, B_32]: (k5_setfam_1(A_31, B_32)=k3_tarski(B_32) | ~m1_subset_1(B_32, k1_zfmisc_1(k1_zfmisc_1(A_31))))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.09/1.24  tff(c_90, plain, (k5_setfam_1('#skF_2', '#skF_3')=k3_tarski('#skF_3')), inference(resolution, [status(thm)], [c_24, c_83])).
% 2.09/1.24  tff(c_93, plain, (k3_tarski('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_53, c_90])).
% 2.09/1.24  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.09/1.24  tff(c_37, plain, (![B_18, A_19]: (m1_setfam_1(B_18, A_19) | ~r1_tarski(A_19, k3_tarski(B_18)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.09/1.24  tff(c_42, plain, (![B_18]: (m1_setfam_1(B_18, k3_tarski(B_18)))), inference(resolution, [status(thm)], [c_6, c_37])).
% 2.09/1.24  tff(c_100, plain, (m1_setfam_1('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_93, c_42])).
% 2.09/1.24  tff(c_107, plain, $false, inference(negUnitSimplification, [status(thm)], [c_35, c_100])).
% 2.09/1.24  tff(c_108, plain, (k5_setfam_1('#skF_2', '#skF_3')!='#skF_2'), inference(splitRight, [status(thm)], [c_26])).
% 2.09/1.24  tff(c_163, plain, (k3_tarski('#skF_3')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_162, c_108])).
% 2.09/1.24  tff(c_109, plain, (m1_setfam_1('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_26])).
% 2.09/1.24  tff(c_10, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), A_3) | r1_tarski(k3_tarski(A_3), B_4))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.09/1.24  tff(c_168, plain, (![A_50, C_51, B_52]: (m1_subset_1(A_50, C_51) | ~m1_subset_1(B_52, k1_zfmisc_1(C_51)) | ~r2_hidden(A_50, B_52))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.09/1.24  tff(c_175, plain, (![A_53]: (m1_subset_1(A_53, k1_zfmisc_1('#skF_2')) | ~r2_hidden(A_53, '#skF_3'))), inference(resolution, [status(thm)], [c_24, c_168])).
% 2.09/1.24  tff(c_18, plain, (![A_10, B_11]: (r1_tarski(A_10, B_11) | ~m1_subset_1(A_10, k1_zfmisc_1(B_11)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.09/1.24  tff(c_183, plain, (![A_54]: (r1_tarski(A_54, '#skF_2') | ~r2_hidden(A_54, '#skF_3'))), inference(resolution, [status(thm)], [c_175, c_18])).
% 2.09/1.24  tff(c_188, plain, (![B_4]: (r1_tarski('#skF_1'('#skF_3', B_4), '#skF_2') | r1_tarski(k3_tarski('#skF_3'), B_4))), inference(resolution, [status(thm)], [c_10, c_183])).
% 2.09/1.24  tff(c_12, plain, (![A_6, B_7]: (r1_tarski(A_6, k3_tarski(B_7)) | ~m1_setfam_1(B_7, A_6))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.09/1.24  tff(c_133, plain, (![B_42, A_43]: (B_42=A_43 | ~r1_tarski(B_42, A_43) | ~r1_tarski(A_43, B_42))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.09/1.24  tff(c_229, plain, (![B_64, A_65]: (k3_tarski(B_64)=A_65 | ~r1_tarski(k3_tarski(B_64), A_65) | ~m1_setfam_1(B_64, A_65))), inference(resolution, [status(thm)], [c_12, c_133])).
% 2.09/1.24  tff(c_280, plain, (![B_71]: (k3_tarski('#skF_3')=B_71 | ~m1_setfam_1('#skF_3', B_71) | r1_tarski('#skF_1'('#skF_3', B_71), '#skF_2'))), inference(resolution, [status(thm)], [c_188, c_229])).
% 2.09/1.24  tff(c_8, plain, (![A_3, B_4]: (~r1_tarski('#skF_1'(A_3, B_4), B_4) | r1_tarski(k3_tarski(A_3), B_4))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.09/1.24  tff(c_283, plain, (r1_tarski(k3_tarski('#skF_3'), '#skF_2') | k3_tarski('#skF_3')='#skF_2' | ~m1_setfam_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_280, c_8])).
% 2.09/1.24  tff(c_288, plain, (r1_tarski(k3_tarski('#skF_3'), '#skF_2') | k3_tarski('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_109, c_283])).
% 2.09/1.24  tff(c_289, plain, (r1_tarski(k3_tarski('#skF_3'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_163, c_288])).
% 2.09/1.24  tff(c_141, plain, (![B_7, A_6]: (k3_tarski(B_7)=A_6 | ~r1_tarski(k3_tarski(B_7), A_6) | ~m1_setfam_1(B_7, A_6))), inference(resolution, [status(thm)], [c_12, c_133])).
% 2.09/1.24  tff(c_293, plain, (k3_tarski('#skF_3')='#skF_2' | ~m1_setfam_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_289, c_141])).
% 2.09/1.24  tff(c_298, plain, (k3_tarski('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_109, c_293])).
% 2.09/1.24  tff(c_300, plain, $false, inference(negUnitSimplification, [status(thm)], [c_163, c_298])).
% 2.09/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.09/1.24  
% 2.09/1.24  Inference rules
% 2.09/1.24  ----------------------
% 2.09/1.24  #Ref     : 0
% 2.09/1.24  #Sup     : 56
% 2.09/1.24  #Fact    : 0
% 2.09/1.24  #Define  : 0
% 2.09/1.24  #Split   : 3
% 2.09/1.24  #Chain   : 0
% 2.09/1.24  #Close   : 0
% 2.09/1.24  
% 2.09/1.24  Ordering : KBO
% 2.09/1.24  
% 2.09/1.24  Simplification rules
% 2.09/1.24  ----------------------
% 2.09/1.24  #Subsume      : 0
% 2.09/1.24  #Demod        : 10
% 2.09/1.24  #Tautology    : 19
% 2.09/1.24  #SimpNegUnit  : 4
% 2.09/1.24  #BackRed      : 1
% 2.09/1.24  
% 2.09/1.24  #Partial instantiations: 0
% 2.09/1.24  #Strategies tried      : 1
% 2.09/1.24  
% 2.09/1.24  Timing (in seconds)
% 2.09/1.24  ----------------------
% 2.09/1.24  Preprocessing        : 0.28
% 2.09/1.24  Parsing              : 0.15
% 2.09/1.24  CNF conversion       : 0.02
% 2.09/1.24  Main loop            : 0.21
% 2.09/1.24  Inferencing          : 0.08
% 2.09/1.24  Reduction            : 0.05
% 2.09/1.24  Demodulation         : 0.04
% 2.09/1.24  BG Simplification    : 0.01
% 2.09/1.24  Subsumption          : 0.04
% 2.09/1.24  Abstraction          : 0.01
% 2.09/1.24  MUC search           : 0.00
% 2.09/1.24  Cooper               : 0.00
% 2.09/1.24  Total                : 0.52
% 2.09/1.24  Index Insertion      : 0.00
% 2.09/1.24  Index Deletion       : 0.00
% 2.09/1.24  Index Matching       : 0.00
% 2.09/1.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
