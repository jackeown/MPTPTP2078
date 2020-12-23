%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:19 EST 2020

% Result     : Theorem 1.95s
% Output     : CNFRefutation 1.95s
% Verified   : 
% Statistics : Number of formulae       :   50 (  88 expanded)
%              Number of leaves         :   22 (  40 expanded)
%              Depth                    :   11
%              Number of atoms          :   86 ( 219 expanded)
%              Number of equality atoms :   25 (  61 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k6_domain_1 > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

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

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_zfmisc_1,type,(
    v1_zfmisc_1: $i > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_75,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ( ~ v1_xboole_0(B)
              & v1_zfmisc_1(B) )
           => ( r1_tarski(A,B)
             => A = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).

tff(f_61,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ( v1_zfmisc_1(A)
      <=> ? [B] :
            ( m1_subset_1(B,A)
            & A = k6_domain_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tex_2)).

tff(f_51,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_44,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_30,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_24,plain,(
    '#skF_3' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_28,plain,(
    v1_zfmisc_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_32,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_26,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_22,plain,(
    ! [A_12] :
      ( m1_subset_1('#skF_2'(A_12),A_12)
      | ~ v1_zfmisc_1(A_12)
      | v1_xboole_0(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_75,plain,(
    ! [A_29,B_30] :
      ( k6_domain_1(A_29,B_30) = k1_tarski(B_30)
      | ~ m1_subset_1(B_30,A_29)
      | v1_xboole_0(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_85,plain,(
    ! [A_33] :
      ( k6_domain_1(A_33,'#skF_2'(A_33)) = k1_tarski('#skF_2'(A_33))
      | ~ v1_zfmisc_1(A_33)
      | v1_xboole_0(A_33) ) ),
    inference(resolution,[status(thm)],[c_22,c_75])).

tff(c_20,plain,(
    ! [A_12] :
      ( k6_domain_1(A_12,'#skF_2'(A_12)) = A_12
      | ~ v1_zfmisc_1(A_12)
      | v1_xboole_0(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_100,plain,(
    ! [A_34] :
      ( k1_tarski('#skF_2'(A_34)) = A_34
      | ~ v1_zfmisc_1(A_34)
      | v1_xboole_0(A_34)
      | ~ v1_zfmisc_1(A_34)
      | v1_xboole_0(A_34) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_85,c_20])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( k1_tarski(B_7) = A_6
      | k1_xboole_0 = A_6
      | ~ r1_tarski(A_6,k1_tarski(B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_135,plain,(
    ! [A_37,A_38] :
      ( k1_tarski('#skF_2'(A_37)) = A_38
      | k1_xboole_0 = A_38
      | ~ r1_tarski(A_38,A_37)
      | ~ v1_zfmisc_1(A_37)
      | v1_xboole_0(A_37)
      | ~ v1_zfmisc_1(A_37)
      | v1_xboole_0(A_37) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_100,c_8])).

tff(c_145,plain,
    ( k1_tarski('#skF_2'('#skF_4')) = '#skF_3'
    | k1_xboole_0 = '#skF_3'
    | ~ v1_zfmisc_1('#skF_4')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_26,c_135])).

tff(c_154,plain,
    ( k1_tarski('#skF_2'('#skF_4')) = '#skF_3'
    | k1_xboole_0 = '#skF_3'
    | v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_145])).

tff(c_155,plain,
    ( k1_tarski('#skF_2'('#skF_4')) = '#skF_3'
    | k1_xboole_0 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_154])).

tff(c_156,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_155])).

tff(c_6,plain,(
    ! [A_5] : r1_tarski(k1_xboole_0,A_5) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_38,plain,(
    ! [A_23] :
      ( v1_xboole_0(A_23)
      | r2_hidden('#skF_1'(A_23),A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_14,plain,(
    ! [B_9,A_8] :
      ( ~ r1_tarski(B_9,A_8)
      | ~ r2_hidden(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_47,plain,(
    ! [A_24] :
      ( ~ r1_tarski(A_24,'#skF_1'(A_24))
      | v1_xboole_0(A_24) ) ),
    inference(resolution,[status(thm)],[c_38,c_14])).

tff(c_52,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_6,c_47])).

tff(c_159,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_156,c_52])).

tff(c_162,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_159])).

tff(c_163,plain,(
    k1_tarski('#skF_2'('#skF_4')) = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_155])).

tff(c_91,plain,(
    ! [A_33] :
      ( k1_tarski('#skF_2'(A_33)) = A_33
      | ~ v1_zfmisc_1(A_33)
      | v1_xboole_0(A_33)
      | ~ v1_zfmisc_1(A_33)
      | v1_xboole_0(A_33) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_85,c_20])).

tff(c_174,plain,
    ( '#skF_3' = '#skF_4'
    | ~ v1_zfmisc_1('#skF_4')
    | v1_xboole_0('#skF_4')
    | ~ v1_zfmisc_1('#skF_4')
    | v1_xboole_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_163,c_91])).

tff(c_196,plain,
    ( '#skF_3' = '#skF_4'
    | v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_28,c_174])).

tff(c_198,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_24,c_196])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:11:35 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.95/1.25  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.95/1.25  
% 1.95/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.95/1.26  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k6_domain_1 > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1 > #skF_3 > #skF_4
% 1.95/1.26  
% 1.95/1.26  %Foreground sorts:
% 1.95/1.26  
% 1.95/1.26  
% 1.95/1.26  %Background operators:
% 1.95/1.26  
% 1.95/1.26  
% 1.95/1.26  %Foreground operators:
% 1.95/1.26  tff('#skF_2', type, '#skF_2': $i > $i).
% 1.95/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.95/1.26  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.95/1.26  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.95/1.26  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.95/1.26  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.95/1.26  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 1.95/1.26  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.95/1.26  tff('#skF_3', type, '#skF_3': $i).
% 1.95/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.95/1.26  tff('#skF_4', type, '#skF_4': $i).
% 1.95/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.95/1.26  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 1.95/1.26  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.95/1.26  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.95/1.26  
% 1.95/1.27  tff(f_75, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tex_2)).
% 1.95/1.27  tff(f_61, axiom, (![A]: (~v1_xboole_0(A) => (v1_zfmisc_1(A) <=> (?[B]: (m1_subset_1(B, A) & (A = k6_domain_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tex_2)).
% 1.95/1.27  tff(f_51, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 1.95/1.27  tff(f_39, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 1.95/1.27  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 1.95/1.27  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 1.95/1.27  tff(f_44, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 1.95/1.27  tff(c_30, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_75])).
% 1.95/1.27  tff(c_24, plain, ('#skF_3'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_75])).
% 1.95/1.27  tff(c_28, plain, (v1_zfmisc_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_75])).
% 1.95/1.27  tff(c_32, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_75])).
% 1.95/1.27  tff(c_26, plain, (r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_75])).
% 1.95/1.27  tff(c_22, plain, (![A_12]: (m1_subset_1('#skF_2'(A_12), A_12) | ~v1_zfmisc_1(A_12) | v1_xboole_0(A_12))), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.95/1.27  tff(c_75, plain, (![A_29, B_30]: (k6_domain_1(A_29, B_30)=k1_tarski(B_30) | ~m1_subset_1(B_30, A_29) | v1_xboole_0(A_29))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.95/1.27  tff(c_85, plain, (![A_33]: (k6_domain_1(A_33, '#skF_2'(A_33))=k1_tarski('#skF_2'(A_33)) | ~v1_zfmisc_1(A_33) | v1_xboole_0(A_33))), inference(resolution, [status(thm)], [c_22, c_75])).
% 1.95/1.27  tff(c_20, plain, (![A_12]: (k6_domain_1(A_12, '#skF_2'(A_12))=A_12 | ~v1_zfmisc_1(A_12) | v1_xboole_0(A_12))), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.95/1.27  tff(c_100, plain, (![A_34]: (k1_tarski('#skF_2'(A_34))=A_34 | ~v1_zfmisc_1(A_34) | v1_xboole_0(A_34) | ~v1_zfmisc_1(A_34) | v1_xboole_0(A_34))), inference(superposition, [status(thm), theory('equality')], [c_85, c_20])).
% 1.95/1.27  tff(c_8, plain, (![B_7, A_6]: (k1_tarski(B_7)=A_6 | k1_xboole_0=A_6 | ~r1_tarski(A_6, k1_tarski(B_7)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.95/1.27  tff(c_135, plain, (![A_37, A_38]: (k1_tarski('#skF_2'(A_37))=A_38 | k1_xboole_0=A_38 | ~r1_tarski(A_38, A_37) | ~v1_zfmisc_1(A_37) | v1_xboole_0(A_37) | ~v1_zfmisc_1(A_37) | v1_xboole_0(A_37))), inference(superposition, [status(thm), theory('equality')], [c_100, c_8])).
% 1.95/1.27  tff(c_145, plain, (k1_tarski('#skF_2'('#skF_4'))='#skF_3' | k1_xboole_0='#skF_3' | ~v1_zfmisc_1('#skF_4') | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_26, c_135])).
% 1.95/1.27  tff(c_154, plain, (k1_tarski('#skF_2'('#skF_4'))='#skF_3' | k1_xboole_0='#skF_3' | v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_145])).
% 1.95/1.27  tff(c_155, plain, (k1_tarski('#skF_2'('#skF_4'))='#skF_3' | k1_xboole_0='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_30, c_154])).
% 1.95/1.27  tff(c_156, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_155])).
% 1.95/1.27  tff(c_6, plain, (![A_5]: (r1_tarski(k1_xboole_0, A_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.95/1.27  tff(c_38, plain, (![A_23]: (v1_xboole_0(A_23) | r2_hidden('#skF_1'(A_23), A_23))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.95/1.27  tff(c_14, plain, (![B_9, A_8]: (~r1_tarski(B_9, A_8) | ~r2_hidden(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.95/1.27  tff(c_47, plain, (![A_24]: (~r1_tarski(A_24, '#skF_1'(A_24)) | v1_xboole_0(A_24))), inference(resolution, [status(thm)], [c_38, c_14])).
% 1.95/1.27  tff(c_52, plain, (v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_47])).
% 1.95/1.27  tff(c_159, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_156, c_52])).
% 1.95/1.27  tff(c_162, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_159])).
% 1.95/1.27  tff(c_163, plain, (k1_tarski('#skF_2'('#skF_4'))='#skF_3'), inference(splitRight, [status(thm)], [c_155])).
% 1.95/1.27  tff(c_91, plain, (![A_33]: (k1_tarski('#skF_2'(A_33))=A_33 | ~v1_zfmisc_1(A_33) | v1_xboole_0(A_33) | ~v1_zfmisc_1(A_33) | v1_xboole_0(A_33))), inference(superposition, [status(thm), theory('equality')], [c_85, c_20])).
% 1.95/1.27  tff(c_174, plain, ('#skF_3'='#skF_4' | ~v1_zfmisc_1('#skF_4') | v1_xboole_0('#skF_4') | ~v1_zfmisc_1('#skF_4') | v1_xboole_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_163, c_91])).
% 1.95/1.27  tff(c_196, plain, ('#skF_3'='#skF_4' | v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_28, c_174])).
% 1.95/1.27  tff(c_198, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_24, c_196])).
% 1.95/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.95/1.27  
% 1.95/1.27  Inference rules
% 1.95/1.27  ----------------------
% 1.95/1.27  #Ref     : 0
% 1.95/1.27  #Sup     : 36
% 1.95/1.27  #Fact    : 0
% 1.95/1.27  #Define  : 0
% 1.95/1.27  #Split   : 1
% 1.95/1.27  #Chain   : 0
% 1.95/1.27  #Close   : 0
% 1.95/1.27  
% 1.95/1.27  Ordering : KBO
% 1.95/1.27  
% 1.95/1.27  Simplification rules
% 1.95/1.27  ----------------------
% 1.95/1.27  #Subsume      : 4
% 1.95/1.27  #Demod        : 13
% 1.95/1.27  #Tautology    : 15
% 1.95/1.27  #SimpNegUnit  : 5
% 1.95/1.27  #BackRed      : 4
% 1.95/1.27  
% 1.95/1.27  #Partial instantiations: 0
% 1.95/1.27  #Strategies tried      : 1
% 1.95/1.27  
% 1.95/1.27  Timing (in seconds)
% 1.95/1.27  ----------------------
% 1.95/1.27  Preprocessing        : 0.30
% 1.95/1.27  Parsing              : 0.16
% 1.95/1.27  CNF conversion       : 0.02
% 1.95/1.27  Main loop            : 0.16
% 1.95/1.27  Inferencing          : 0.06
% 1.95/1.27  Reduction            : 0.05
% 1.95/1.27  Demodulation         : 0.04
% 1.95/1.27  BG Simplification    : 0.01
% 1.95/1.27  Subsumption          : 0.02
% 1.95/1.27  Abstraction          : 0.01
% 1.95/1.27  MUC search           : 0.00
% 1.95/1.27  Cooper               : 0.00
% 1.95/1.27  Total                : 0.49
% 1.95/1.27  Index Insertion      : 0.00
% 1.95/1.27  Index Deletion       : 0.00
% 1.95/1.27  Index Matching       : 0.00
% 1.95/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
