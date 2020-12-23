%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:49 EST 2020

% Result     : Theorem 2.61s
% Output     : CNFRefutation 2.61s
% Verified   : 
% Statistics : Number of formulae       :   55 (  93 expanded)
%              Number of leaves         :   26 (  43 expanded)
%              Depth                    :   11
%              Number of atoms          :   80 ( 176 expanded)
%              Number of equality atoms :   17 (  29 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_subset_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k6_domain_1 > #nlpp > k1_zfmisc_1 > k1_tarski > #skF_4 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_4',type,(
    '#skF_4': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_zfmisc_1,type,(
    v1_zfmisc_1: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_92,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v1_xboole_0(A)
          & ~ v1_zfmisc_1(A) )
       => ! [B] :
            ( m1_subset_1(B,A)
           => v1_subset_1(k6_domain_1(A,B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tex_2)).

tff(f_52,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_80,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( v1_subset_1(B,A)
      <=> B != A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_39,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_73,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ( v1_zfmisc_1(A)
      <=> ? [B] :
            ( m1_subset_1(B,A)
            & A = k6_domain_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tex_2)).

tff(c_50,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_48,plain,(
    ~ v1_zfmisc_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_46,plain,(
    m1_subset_1('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_22,plain,(
    ! [B_12,A_11] :
      ( r2_hidden(B_12,A_11)
      | ~ m1_subset_1(B_12,A_11)
      | v1_xboole_0(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_244,plain,(
    ! [A_69,B_70] :
      ( k6_domain_1(A_69,B_70) = k1_tarski(B_70)
      | ~ m1_subset_1(B_70,A_69)
      | v1_xboole_0(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_259,plain,
    ( k6_domain_1('#skF_5','#skF_6') = k1_tarski('#skF_6')
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_46,c_244])).

tff(c_266,plain,(
    k6_domain_1('#skF_5','#skF_6') = k1_tarski('#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_259])).

tff(c_30,plain,(
    ! [A_13,B_14] :
      ( m1_subset_1(A_13,k1_zfmisc_1(B_14))
      | ~ r1_tarski(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_169,plain,(
    ! [B_58,A_59] :
      ( v1_subset_1(B_58,A_59)
      | B_58 = A_59
      | ~ m1_subset_1(B_58,k1_zfmisc_1(A_59)) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_184,plain,(
    ! [A_60,B_61] :
      ( v1_subset_1(A_60,B_61)
      | B_61 = A_60
      | ~ r1_tarski(A_60,B_61) ) ),
    inference(resolution,[status(thm)],[c_30,c_169])).

tff(c_44,plain,(
    ~ v1_subset_1(k6_domain_1('#skF_5','#skF_6'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_196,plain,
    ( k6_domain_1('#skF_5','#skF_6') = '#skF_5'
    | ~ r1_tarski(k6_domain_1('#skF_5','#skF_6'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_184,c_44])).

tff(c_211,plain,(
    ~ r1_tarski(k6_domain_1('#skF_5','#skF_6'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_196])).

tff(c_267,plain,(
    ~ r1_tarski(k1_tarski('#skF_6'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_266,c_211])).

tff(c_105,plain,(
    ! [A_40,B_41] :
      ( r2_hidden('#skF_1'(A_40,B_41),A_40)
      | r1_tarski(A_40,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_8,plain,(
    ! [C_10,A_6] :
      ( C_10 = A_6
      | ~ r2_hidden(C_10,k1_tarski(A_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_114,plain,(
    ! [A_6,B_41] :
      ( '#skF_1'(k1_tarski(A_6),B_41) = A_6
      | r1_tarski(k1_tarski(A_6),B_41) ) ),
    inference(resolution,[status(thm)],[c_105,c_8])).

tff(c_281,plain,(
    '#skF_1'(k1_tarski('#skF_6'),'#skF_5') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_114,c_267])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_288,plain,
    ( ~ r2_hidden('#skF_6','#skF_5')
    | r1_tarski(k1_tarski('#skF_6'),'#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_281,c_4])).

tff(c_298,plain,(
    ~ r2_hidden('#skF_6','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_267,c_288])).

tff(c_305,plain,
    ( ~ m1_subset_1('#skF_6','#skF_5')
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_22,c_298])).

tff(c_308,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_305])).

tff(c_310,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_308])).

tff(c_311,plain,(
    k6_domain_1('#skF_5','#skF_6') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_196])).

tff(c_610,plain,(
    ! [A_95,B_96] :
      ( v1_zfmisc_1(A_95)
      | k6_domain_1(A_95,B_96) != A_95
      | ~ m1_subset_1(B_96,A_95)
      | v1_xboole_0(A_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_628,plain,
    ( v1_zfmisc_1('#skF_5')
    | k6_domain_1('#skF_5','#skF_6') != '#skF_5'
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_46,c_610])).

tff(c_636,plain,
    ( v1_zfmisc_1('#skF_5')
    | v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_311,c_628])).

tff(c_638,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_48,c_636])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:34:38 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.61/1.43  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.61/1.43  
% 2.61/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.61/1.44  %$ v1_subset_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k6_domain_1 > #nlpp > k1_zfmisc_1 > k1_tarski > #skF_4 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_1
% 2.61/1.44  
% 2.61/1.44  %Foreground sorts:
% 2.61/1.44  
% 2.61/1.44  
% 2.61/1.44  %Background operators:
% 2.61/1.44  
% 2.61/1.44  
% 2.61/1.44  %Foreground operators:
% 2.61/1.44  tff('#skF_4', type, '#skF_4': $i > $i).
% 2.61/1.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.61/1.44  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.61/1.44  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 2.61/1.44  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.61/1.44  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.61/1.44  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.61/1.44  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.61/1.44  tff('#skF_5', type, '#skF_5': $i).
% 2.61/1.44  tff('#skF_6', type, '#skF_6': $i).
% 2.61/1.44  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.61/1.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.61/1.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.61/1.44  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.61/1.44  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 2.61/1.44  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.61/1.44  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.61/1.44  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.61/1.44  
% 2.61/1.45  tff(f_92, negated_conjecture, ~(![A]: ((~v1_xboole_0(A) & ~v1_zfmisc_1(A)) => (![B]: (m1_subset_1(B, A) => v1_subset_1(k6_domain_1(A, B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_tex_2)).
% 2.61/1.45  tff(f_52, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 2.61/1.45  tff(f_63, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 2.61/1.45  tff(f_56, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.61/1.45  tff(f_80, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (v1_subset_1(B, A) <=> ~(B = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_subset_1)).
% 2.61/1.45  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.61/1.45  tff(f_39, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 2.61/1.45  tff(f_73, axiom, (![A]: (~v1_xboole_0(A) => (v1_zfmisc_1(A) <=> (?[B]: (m1_subset_1(B, A) & (A = k6_domain_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tex_2)).
% 2.61/1.45  tff(c_50, plain, (~v1_xboole_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.61/1.45  tff(c_48, plain, (~v1_zfmisc_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.61/1.45  tff(c_46, plain, (m1_subset_1('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.61/1.45  tff(c_22, plain, (![B_12, A_11]: (r2_hidden(B_12, A_11) | ~m1_subset_1(B_12, A_11) | v1_xboole_0(A_11))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.61/1.45  tff(c_244, plain, (![A_69, B_70]: (k6_domain_1(A_69, B_70)=k1_tarski(B_70) | ~m1_subset_1(B_70, A_69) | v1_xboole_0(A_69))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.61/1.45  tff(c_259, plain, (k6_domain_1('#skF_5', '#skF_6')=k1_tarski('#skF_6') | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_46, c_244])).
% 2.61/1.45  tff(c_266, plain, (k6_domain_1('#skF_5', '#skF_6')=k1_tarski('#skF_6')), inference(negUnitSimplification, [status(thm)], [c_50, c_259])).
% 2.61/1.45  tff(c_30, plain, (![A_13, B_14]: (m1_subset_1(A_13, k1_zfmisc_1(B_14)) | ~r1_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.61/1.45  tff(c_169, plain, (![B_58, A_59]: (v1_subset_1(B_58, A_59) | B_58=A_59 | ~m1_subset_1(B_58, k1_zfmisc_1(A_59)))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.61/1.45  tff(c_184, plain, (![A_60, B_61]: (v1_subset_1(A_60, B_61) | B_61=A_60 | ~r1_tarski(A_60, B_61))), inference(resolution, [status(thm)], [c_30, c_169])).
% 2.61/1.45  tff(c_44, plain, (~v1_subset_1(k6_domain_1('#skF_5', '#skF_6'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.61/1.45  tff(c_196, plain, (k6_domain_1('#skF_5', '#skF_6')='#skF_5' | ~r1_tarski(k6_domain_1('#skF_5', '#skF_6'), '#skF_5')), inference(resolution, [status(thm)], [c_184, c_44])).
% 2.61/1.45  tff(c_211, plain, (~r1_tarski(k6_domain_1('#skF_5', '#skF_6'), '#skF_5')), inference(splitLeft, [status(thm)], [c_196])).
% 2.61/1.45  tff(c_267, plain, (~r1_tarski(k1_tarski('#skF_6'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_266, c_211])).
% 2.61/1.45  tff(c_105, plain, (![A_40, B_41]: (r2_hidden('#skF_1'(A_40, B_41), A_40) | r1_tarski(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.61/1.45  tff(c_8, plain, (![C_10, A_6]: (C_10=A_6 | ~r2_hidden(C_10, k1_tarski(A_6)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.61/1.45  tff(c_114, plain, (![A_6, B_41]: ('#skF_1'(k1_tarski(A_6), B_41)=A_6 | r1_tarski(k1_tarski(A_6), B_41))), inference(resolution, [status(thm)], [c_105, c_8])).
% 2.61/1.45  tff(c_281, plain, ('#skF_1'(k1_tarski('#skF_6'), '#skF_5')='#skF_6'), inference(resolution, [status(thm)], [c_114, c_267])).
% 2.61/1.45  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.61/1.45  tff(c_288, plain, (~r2_hidden('#skF_6', '#skF_5') | r1_tarski(k1_tarski('#skF_6'), '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_281, c_4])).
% 2.61/1.45  tff(c_298, plain, (~r2_hidden('#skF_6', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_267, c_288])).
% 2.61/1.45  tff(c_305, plain, (~m1_subset_1('#skF_6', '#skF_5') | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_22, c_298])).
% 2.61/1.45  tff(c_308, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_305])).
% 2.61/1.45  tff(c_310, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_308])).
% 2.61/1.45  tff(c_311, plain, (k6_domain_1('#skF_5', '#skF_6')='#skF_5'), inference(splitRight, [status(thm)], [c_196])).
% 2.61/1.45  tff(c_610, plain, (![A_95, B_96]: (v1_zfmisc_1(A_95) | k6_domain_1(A_95, B_96)!=A_95 | ~m1_subset_1(B_96, A_95) | v1_xboole_0(A_95))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.61/1.45  tff(c_628, plain, (v1_zfmisc_1('#skF_5') | k6_domain_1('#skF_5', '#skF_6')!='#skF_5' | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_46, c_610])).
% 2.61/1.45  tff(c_636, plain, (v1_zfmisc_1('#skF_5') | v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_311, c_628])).
% 2.61/1.45  tff(c_638, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_48, c_636])).
% 2.61/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.61/1.45  
% 2.61/1.45  Inference rules
% 2.61/1.45  ----------------------
% 2.61/1.45  #Ref     : 0
% 2.61/1.45  #Sup     : 123
% 2.61/1.45  #Fact    : 0
% 2.61/1.45  #Define  : 0
% 2.61/1.45  #Split   : 1
% 2.61/1.45  #Chain   : 0
% 2.61/1.45  #Close   : 0
% 2.61/1.45  
% 2.61/1.45  Ordering : KBO
% 2.61/1.45  
% 2.61/1.45  Simplification rules
% 2.61/1.45  ----------------------
% 2.61/1.45  #Subsume      : 18
% 2.61/1.45  #Demod        : 28
% 2.61/1.45  #Tautology    : 56
% 2.61/1.45  #SimpNegUnit  : 14
% 2.61/1.45  #BackRed      : 4
% 2.61/1.45  
% 2.61/1.45  #Partial instantiations: 0
% 2.61/1.45  #Strategies tried      : 1
% 2.61/1.45  
% 2.61/1.45  Timing (in seconds)
% 2.61/1.45  ----------------------
% 2.61/1.45  Preprocessing        : 0.34
% 2.61/1.45  Parsing              : 0.18
% 2.61/1.45  CNF conversion       : 0.03
% 2.61/1.45  Main loop            : 0.32
% 2.61/1.45  Inferencing          : 0.13
% 2.61/1.45  Reduction            : 0.08
% 2.61/1.45  Demodulation         : 0.06
% 2.61/1.45  BG Simplification    : 0.02
% 2.61/1.45  Subsumption          : 0.07
% 2.61/1.45  Abstraction          : 0.02
% 2.61/1.45  MUC search           : 0.00
% 2.61/1.45  Cooper               : 0.00
% 2.61/1.45  Total                : 0.70
% 2.61/1.45  Index Insertion      : 0.00
% 2.61/1.46  Index Deletion       : 0.00
% 2.61/1.46  Index Matching       : 0.00
% 2.61/1.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
