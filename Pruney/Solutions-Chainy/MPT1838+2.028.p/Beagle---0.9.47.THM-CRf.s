%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:17 EST 2020

% Result     : Theorem 2.03s
% Output     : CNFRefutation 2.03s
% Verified   : 
% Statistics : Number of formulae       :   49 (  87 expanded)
%              Number of leaves         :   21 (  39 expanded)
%              Depth                    :   11
%              Number of atoms          :   93 ( 226 expanded)
%              Number of equality atoms :   28 (  64 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k6_domain_1 > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_zfmisc_1,type,(
    v1_zfmisc_1: $i > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_90,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ( ~ v1_xboole_0(B)
              & v1_zfmisc_1(B) )
           => ( r1_tarski(A,B)
             => A = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).

tff(f_76,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ( v1_zfmisc_1(A)
      <=> ? [B] :
            ( m1_subset_1(B,A)
            & A = k6_domain_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tex_2)).

tff(f_66,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_43,axiom,(
    ! [A] :
      ( ~ ( ~ r1_xboole_0(A,A)
          & A = k1_xboole_0 )
      & ~ ( A != k1_xboole_0
          & r1_xboole_0(A,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( ~ v1_xboole_0(C)
     => ~ ( r1_tarski(C,A)
          & r1_tarski(C,B)
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_xboole_1)).

tff(c_34,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_28,plain,(
    '#skF_2' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_32,plain,(
    v1_zfmisc_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_36,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_30,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_26,plain,(
    ! [A_11] :
      ( m1_subset_1('#skF_1'(A_11),A_11)
      | ~ v1_zfmisc_1(A_11)
      | v1_xboole_0(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_85,plain,(
    ! [A_26,B_27] :
      ( k6_domain_1(A_26,B_27) = k1_tarski(B_27)
      | ~ m1_subset_1(B_27,A_26)
      | v1_xboole_0(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_105,plain,(
    ! [A_34] :
      ( k6_domain_1(A_34,'#skF_1'(A_34)) = k1_tarski('#skF_1'(A_34))
      | ~ v1_zfmisc_1(A_34)
      | v1_xboole_0(A_34) ) ),
    inference(resolution,[status(thm)],[c_26,c_85])).

tff(c_24,plain,(
    ! [A_11] :
      ( k6_domain_1(A_11,'#skF_1'(A_11)) = A_11
      | ~ v1_zfmisc_1(A_11)
      | v1_xboole_0(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_120,plain,(
    ! [A_35] :
      ( k1_tarski('#skF_1'(A_35)) = A_35
      | ~ v1_zfmisc_1(A_35)
      | v1_xboole_0(A_35)
      | ~ v1_zfmisc_1(A_35)
      | v1_xboole_0(A_35) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_105,c_24])).

tff(c_14,plain,(
    ! [B_8,A_7] :
      ( k1_tarski(B_8) = A_7
      | k1_xboole_0 = A_7
      | ~ r1_tarski(A_7,k1_tarski(B_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_153,plain,(
    ! [A_37,A_38] :
      ( k1_tarski('#skF_1'(A_37)) = A_38
      | k1_xboole_0 = A_38
      | ~ r1_tarski(A_38,A_37)
      | ~ v1_zfmisc_1(A_37)
      | v1_xboole_0(A_37)
      | ~ v1_zfmisc_1(A_37)
      | v1_xboole_0(A_37) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_120,c_14])).

tff(c_159,plain,
    ( k1_tarski('#skF_1'('#skF_3')) = '#skF_2'
    | k1_xboole_0 = '#skF_2'
    | ~ v1_zfmisc_1('#skF_3')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_153])).

tff(c_168,plain,
    ( k1_tarski('#skF_1'('#skF_3')) = '#skF_2'
    | k1_xboole_0 = '#skF_2'
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_159])).

tff(c_169,plain,
    ( k1_tarski('#skF_1'('#skF_3')) = '#skF_2'
    | k1_xboole_0 = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_168])).

tff(c_171,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_169])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_90,plain,(
    ! [A_28,B_29,C_30] :
      ( ~ r1_xboole_0(A_28,B_29)
      | ~ r1_tarski(C_30,B_29)
      | ~ r1_tarski(C_30,A_28)
      | v1_xboole_0(C_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_94,plain,(
    ! [C_31] :
      ( ~ r1_tarski(C_31,k1_xboole_0)
      | v1_xboole_0(C_31) ) ),
    inference(resolution,[status(thm)],[c_8,c_90])).

tff(c_99,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_6,c_94])).

tff(c_174,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_171,c_99])).

tff(c_182,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_174])).

tff(c_183,plain,(
    k1_tarski('#skF_1'('#skF_3')) = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_169])).

tff(c_111,plain,(
    ! [A_34] :
      ( k1_tarski('#skF_1'(A_34)) = A_34
      | ~ v1_zfmisc_1(A_34)
      | v1_xboole_0(A_34)
      | ~ v1_zfmisc_1(A_34)
      | v1_xboole_0(A_34) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_105,c_24])).

tff(c_188,plain,
    ( '#skF_2' = '#skF_3'
    | ~ v1_zfmisc_1('#skF_3')
    | v1_xboole_0('#skF_3')
    | ~ v1_zfmisc_1('#skF_3')
    | v1_xboole_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_183,c_111])).

tff(c_203,plain,
    ( '#skF_2' = '#skF_3'
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_32,c_188])).

tff(c_205,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_28,c_203])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n017.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 20:29:31 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.03/1.28  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.03/1.29  
% 2.03/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.03/1.29  %$ r1_xboole_0 > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k6_domain_1 > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3
% 2.03/1.29  
% 2.03/1.29  %Foreground sorts:
% 2.03/1.29  
% 2.03/1.29  
% 2.03/1.29  %Background operators:
% 2.03/1.29  
% 2.03/1.29  
% 2.03/1.29  %Foreground operators:
% 2.03/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.03/1.29  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.03/1.29  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.03/1.29  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.03/1.29  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.03/1.29  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.03/1.29  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.03/1.29  tff('#skF_2', type, '#skF_2': $i).
% 2.03/1.29  tff('#skF_3', type, '#skF_3': $i).
% 2.03/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.03/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.03/1.29  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 2.03/1.29  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.03/1.29  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.03/1.29  
% 2.03/1.30  tff(f_90, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tex_2)).
% 2.03/1.30  tff(f_76, axiom, (![A]: (~v1_xboole_0(A) => (v1_zfmisc_1(A) <=> (?[B]: (m1_subset_1(B, A) & (A = k6_domain_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tex_2)).
% 2.03/1.30  tff(f_66, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 2.03/1.30  tff(f_59, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 2.03/1.30  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.03/1.30  tff(f_43, axiom, (![A]: (~(~r1_xboole_0(A, A) & (A = k1_xboole_0)) & ~(~(A = k1_xboole_0) & r1_xboole_0(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_xboole_1)).
% 2.03/1.30  tff(f_53, axiom, (![A, B, C]: (~v1_xboole_0(C) => ~((r1_tarski(C, A) & r1_tarski(C, B)) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t68_xboole_1)).
% 2.03/1.30  tff(c_34, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.03/1.30  tff(c_28, plain, ('#skF_2'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.03/1.30  tff(c_32, plain, (v1_zfmisc_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.03/1.30  tff(c_36, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.03/1.30  tff(c_30, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.03/1.30  tff(c_26, plain, (![A_11]: (m1_subset_1('#skF_1'(A_11), A_11) | ~v1_zfmisc_1(A_11) | v1_xboole_0(A_11))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.03/1.30  tff(c_85, plain, (![A_26, B_27]: (k6_domain_1(A_26, B_27)=k1_tarski(B_27) | ~m1_subset_1(B_27, A_26) | v1_xboole_0(A_26))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.03/1.30  tff(c_105, plain, (![A_34]: (k6_domain_1(A_34, '#skF_1'(A_34))=k1_tarski('#skF_1'(A_34)) | ~v1_zfmisc_1(A_34) | v1_xboole_0(A_34))), inference(resolution, [status(thm)], [c_26, c_85])).
% 2.03/1.30  tff(c_24, plain, (![A_11]: (k6_domain_1(A_11, '#skF_1'(A_11))=A_11 | ~v1_zfmisc_1(A_11) | v1_xboole_0(A_11))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.03/1.30  tff(c_120, plain, (![A_35]: (k1_tarski('#skF_1'(A_35))=A_35 | ~v1_zfmisc_1(A_35) | v1_xboole_0(A_35) | ~v1_zfmisc_1(A_35) | v1_xboole_0(A_35))), inference(superposition, [status(thm), theory('equality')], [c_105, c_24])).
% 2.03/1.30  tff(c_14, plain, (![B_8, A_7]: (k1_tarski(B_8)=A_7 | k1_xboole_0=A_7 | ~r1_tarski(A_7, k1_tarski(B_8)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.03/1.30  tff(c_153, plain, (![A_37, A_38]: (k1_tarski('#skF_1'(A_37))=A_38 | k1_xboole_0=A_38 | ~r1_tarski(A_38, A_37) | ~v1_zfmisc_1(A_37) | v1_xboole_0(A_37) | ~v1_zfmisc_1(A_37) | v1_xboole_0(A_37))), inference(superposition, [status(thm), theory('equality')], [c_120, c_14])).
% 2.03/1.30  tff(c_159, plain, (k1_tarski('#skF_1'('#skF_3'))='#skF_2' | k1_xboole_0='#skF_2' | ~v1_zfmisc_1('#skF_3') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_30, c_153])).
% 2.03/1.30  tff(c_168, plain, (k1_tarski('#skF_1'('#skF_3'))='#skF_2' | k1_xboole_0='#skF_2' | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_159])).
% 2.03/1.30  tff(c_169, plain, (k1_tarski('#skF_1'('#skF_3'))='#skF_2' | k1_xboole_0='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_34, c_168])).
% 2.03/1.30  tff(c_171, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_169])).
% 2.03/1.30  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.03/1.30  tff(c_8, plain, (r1_xboole_0(k1_xboole_0, k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.03/1.30  tff(c_90, plain, (![A_28, B_29, C_30]: (~r1_xboole_0(A_28, B_29) | ~r1_tarski(C_30, B_29) | ~r1_tarski(C_30, A_28) | v1_xboole_0(C_30))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.03/1.30  tff(c_94, plain, (![C_31]: (~r1_tarski(C_31, k1_xboole_0) | v1_xboole_0(C_31))), inference(resolution, [status(thm)], [c_8, c_90])).
% 2.03/1.30  tff(c_99, plain, (v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_94])).
% 2.03/1.30  tff(c_174, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_171, c_99])).
% 2.03/1.30  tff(c_182, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_174])).
% 2.03/1.30  tff(c_183, plain, (k1_tarski('#skF_1'('#skF_3'))='#skF_2'), inference(splitRight, [status(thm)], [c_169])).
% 2.03/1.30  tff(c_111, plain, (![A_34]: (k1_tarski('#skF_1'(A_34))=A_34 | ~v1_zfmisc_1(A_34) | v1_xboole_0(A_34) | ~v1_zfmisc_1(A_34) | v1_xboole_0(A_34))), inference(superposition, [status(thm), theory('equality')], [c_105, c_24])).
% 2.03/1.30  tff(c_188, plain, ('#skF_2'='#skF_3' | ~v1_zfmisc_1('#skF_3') | v1_xboole_0('#skF_3') | ~v1_zfmisc_1('#skF_3') | v1_xboole_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_183, c_111])).
% 2.03/1.30  tff(c_203, plain, ('#skF_2'='#skF_3' | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_32, c_188])).
% 2.03/1.30  tff(c_205, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_28, c_203])).
% 2.03/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.03/1.30  
% 2.03/1.30  Inference rules
% 2.03/1.30  ----------------------
% 2.03/1.30  #Ref     : 0
% 2.03/1.30  #Sup     : 35
% 2.03/1.30  #Fact    : 0
% 2.03/1.30  #Define  : 0
% 2.03/1.30  #Split   : 1
% 2.03/1.30  #Chain   : 0
% 2.03/1.30  #Close   : 0
% 2.03/1.30  
% 2.03/1.30  Ordering : KBO
% 2.03/1.30  
% 2.03/1.30  Simplification rules
% 2.03/1.30  ----------------------
% 2.03/1.30  #Subsume      : 4
% 2.03/1.30  #Demod        : 18
% 2.03/1.30  #Tautology    : 18
% 2.03/1.30  #SimpNegUnit  : 4
% 2.03/1.30  #BackRed      : 9
% 2.03/1.30  
% 2.03/1.30  #Partial instantiations: 0
% 2.03/1.30  #Strategies tried      : 1
% 2.03/1.30  
% 2.03/1.30  Timing (in seconds)
% 2.03/1.30  ----------------------
% 2.03/1.31  Preprocessing        : 0.31
% 2.03/1.31  Parsing              : 0.16
% 2.03/1.31  CNF conversion       : 0.02
% 2.03/1.31  Main loop            : 0.19
% 2.03/1.31  Inferencing          : 0.07
% 2.03/1.31  Reduction            : 0.06
% 2.03/1.31  Demodulation         : 0.04
% 2.03/1.31  BG Simplification    : 0.02
% 2.03/1.31  Subsumption          : 0.04
% 2.03/1.31  Abstraction          : 0.01
% 2.03/1.31  MUC search           : 0.00
% 2.03/1.31  Cooper               : 0.00
% 2.03/1.31  Total                : 0.53
% 2.03/1.31  Index Insertion      : 0.00
% 2.03/1.31  Index Deletion       : 0.00
% 2.03/1.31  Index Matching       : 0.00
% 2.03/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
