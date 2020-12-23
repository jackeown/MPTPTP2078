%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:46 EST 2020

% Result     : Theorem 1.92s
% Output     : CNFRefutation 2.16s
% Verified   : 
% Statistics : Number of formulae       :   52 (  75 expanded)
%              Number of leaves         :   24 (  37 expanded)
%              Depth                    :   13
%              Number of atoms          :   83 ( 153 expanded)
%              Number of equality atoms :   22 (  31 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_subset_1 > r2_hidden > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k6_domain_1 > k2_tarski > #nlpp > k2_subset_1 > k1_tarski > #skF_5 > #skF_4 > #skF_3 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

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

tff(v1_zfmisc_1,type,(
    v1_zfmisc_1: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_36,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_39,axiom,(
    ! [A] : ~ v1_subset_1(k2_subset_1(A),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc14_subset_1)).

tff(f_74,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( m1_subset_1(B,A)
           => ~ ( v1_subset_1(k6_domain_1(A,B),A)
                & v1_zfmisc_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_tex_2)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_62,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ( v1_zfmisc_1(A)
      <=> ? [B] :
            ( m1_subset_1(B,A)
            & A = k6_domain_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tex_2)).

tff(f_52,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(c_16,plain,(
    ! [A_7] : k2_subset_1(A_7) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_18,plain,(
    ! [A_8] : ~ v1_subset_1(k2_subset_1(A_8),A_8) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_37,plain,(
    ! [A_8] : ~ v1_subset_1(A_8,A_8) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_18])).

tff(c_36,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_30,plain,(
    v1_zfmisc_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_34,plain,(
    m1_subset_1('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_20,plain,(
    ! [A_9,B_10] :
      ( r2_hidden(A_9,B_10)
      | v1_xboole_0(B_10)
      | ~ m1_subset_1(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_26,plain,(
    ! [A_13] :
      ( k6_domain_1(A_13,'#skF_3'(A_13)) = A_13
      | ~ v1_zfmisc_1(A_13)
      | v1_xboole_0(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_28,plain,(
    ! [A_13] :
      ( m1_subset_1('#skF_3'(A_13),A_13)
      | ~ v1_zfmisc_1(A_13)
      | v1_xboole_0(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_86,plain,(
    ! [A_30,B_31] :
      ( k6_domain_1(A_30,B_31) = k1_tarski(B_31)
      | ~ m1_subset_1(B_31,A_30)
      | v1_xboole_0(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_121,plain,(
    ! [A_39] :
      ( k6_domain_1(A_39,'#skF_3'(A_39)) = k1_tarski('#skF_3'(A_39))
      | ~ v1_zfmisc_1(A_39)
      | v1_xboole_0(A_39) ) ),
    inference(resolution,[status(thm)],[c_28,c_86])).

tff(c_142,plain,(
    ! [A_42] :
      ( k1_tarski('#skF_3'(A_42)) = A_42
      | ~ v1_zfmisc_1(A_42)
      | v1_xboole_0(A_42)
      | ~ v1_zfmisc_1(A_42)
      | v1_xboole_0(A_42) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_121])).

tff(c_2,plain,(
    ! [C_5,A_1] :
      ( C_5 = A_1
      | ~ r2_hidden(C_5,k1_tarski(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_202,plain,(
    ! [C_50,A_51] :
      ( C_50 = '#skF_3'(A_51)
      | ~ r2_hidden(C_50,A_51)
      | ~ v1_zfmisc_1(A_51)
      | v1_xboole_0(A_51)
      | ~ v1_zfmisc_1(A_51)
      | v1_xboole_0(A_51) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_142,c_2])).

tff(c_224,plain,(
    ! [A_52,B_53] :
      ( A_52 = '#skF_3'(B_53)
      | ~ v1_zfmisc_1(B_53)
      | v1_xboole_0(B_53)
      | ~ m1_subset_1(A_52,B_53) ) ),
    inference(resolution,[status(thm)],[c_20,c_202])).

tff(c_230,plain,
    ( '#skF_3'('#skF_4') = '#skF_5'
    | ~ v1_zfmisc_1('#skF_4')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_34,c_224])).

tff(c_235,plain,
    ( '#skF_3'('#skF_4') = '#skF_5'
    | v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_230])).

tff(c_236,plain,(
    '#skF_3'('#skF_4') = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_235])).

tff(c_133,plain,(
    ! [A_13] :
      ( k1_tarski('#skF_3'(A_13)) = A_13
      | ~ v1_zfmisc_1(A_13)
      | v1_xboole_0(A_13)
      | ~ v1_zfmisc_1(A_13)
      | v1_xboole_0(A_13) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_121])).

tff(c_243,plain,
    ( k1_tarski('#skF_5') = '#skF_4'
    | ~ v1_zfmisc_1('#skF_4')
    | v1_xboole_0('#skF_4')
    | ~ v1_zfmisc_1('#skF_4')
    | v1_xboole_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_236,c_133])).

tff(c_259,plain,
    ( k1_tarski('#skF_5') = '#skF_4'
    | v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_30,c_243])).

tff(c_260,plain,(
    k1_tarski('#skF_5') = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_259])).

tff(c_92,plain,
    ( k6_domain_1('#skF_4','#skF_5') = k1_tarski('#skF_5')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_34,c_86])).

tff(c_96,plain,(
    k6_domain_1('#skF_4','#skF_5') = k1_tarski('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_92])).

tff(c_32,plain,(
    v1_subset_1(k6_domain_1('#skF_4','#skF_5'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_97,plain,(
    v1_subset_1(k1_tarski('#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_32])).

tff(c_278,plain,(
    v1_subset_1('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_260,c_97])).

tff(c_281,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_37,c_278])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.32  % Computer   : n011.cluster.edu
% 0.14/0.32  % Model      : x86_64 x86_64
% 0.14/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.32  % Memory     : 8042.1875MB
% 0.14/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.32  % CPULimit   : 60
% 0.14/0.32  % DateTime   : Tue Dec  1 13:32:12 EST 2020
% 0.14/0.32  % CPUTime    : 
% 0.14/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.92/1.22  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.92/1.23  
% 1.92/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.16/1.23  %$ v1_subset_1 > r2_hidden > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k6_domain_1 > k2_tarski > #nlpp > k2_subset_1 > k1_tarski > #skF_5 > #skF_4 > #skF_3 > #skF_2 > #skF_1
% 2.16/1.23  
% 2.16/1.23  %Foreground sorts:
% 2.16/1.23  
% 2.16/1.23  
% 2.16/1.23  %Background operators:
% 2.16/1.23  
% 2.16/1.23  
% 2.16/1.23  %Foreground operators:
% 2.16/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.16/1.23  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.16/1.23  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 2.16/1.23  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.16/1.23  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.16/1.23  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.16/1.23  tff('#skF_5', type, '#skF_5': $i).
% 2.16/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.16/1.23  tff('#skF_4', type, '#skF_4': $i).
% 2.16/1.23  tff('#skF_3', type, '#skF_3': $i > $i).
% 2.16/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.16/1.23  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.16/1.23  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 2.16/1.23  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.16/1.23  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.16/1.23  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.16/1.23  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.16/1.23  
% 2.16/1.24  tff(f_36, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 2.16/1.24  tff(f_39, axiom, (![A]: ~v1_subset_1(k2_subset_1(A), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc14_subset_1)).
% 2.16/1.24  tff(f_74, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, A) => ~(v1_subset_1(k6_domain_1(A, B), A) & v1_zfmisc_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_tex_2)).
% 2.16/1.24  tff(f_45, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 2.16/1.24  tff(f_62, axiom, (![A]: (~v1_xboole_0(A) => (v1_zfmisc_1(A) <=> (?[B]: (m1_subset_1(B, A) & (A = k6_domain_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tex_2)).
% 2.16/1.24  tff(f_52, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 2.16/1.24  tff(f_32, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 2.16/1.24  tff(c_16, plain, (![A_7]: (k2_subset_1(A_7)=A_7)), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.16/1.24  tff(c_18, plain, (![A_8]: (~v1_subset_1(k2_subset_1(A_8), A_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.16/1.24  tff(c_37, plain, (![A_8]: (~v1_subset_1(A_8, A_8))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_18])).
% 2.16/1.24  tff(c_36, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.16/1.24  tff(c_30, plain, (v1_zfmisc_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.16/1.24  tff(c_34, plain, (m1_subset_1('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.16/1.24  tff(c_20, plain, (![A_9, B_10]: (r2_hidden(A_9, B_10) | v1_xboole_0(B_10) | ~m1_subset_1(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.16/1.24  tff(c_26, plain, (![A_13]: (k6_domain_1(A_13, '#skF_3'(A_13))=A_13 | ~v1_zfmisc_1(A_13) | v1_xboole_0(A_13))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.16/1.24  tff(c_28, plain, (![A_13]: (m1_subset_1('#skF_3'(A_13), A_13) | ~v1_zfmisc_1(A_13) | v1_xboole_0(A_13))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.16/1.24  tff(c_86, plain, (![A_30, B_31]: (k6_domain_1(A_30, B_31)=k1_tarski(B_31) | ~m1_subset_1(B_31, A_30) | v1_xboole_0(A_30))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.16/1.24  tff(c_121, plain, (![A_39]: (k6_domain_1(A_39, '#skF_3'(A_39))=k1_tarski('#skF_3'(A_39)) | ~v1_zfmisc_1(A_39) | v1_xboole_0(A_39))), inference(resolution, [status(thm)], [c_28, c_86])).
% 2.16/1.24  tff(c_142, plain, (![A_42]: (k1_tarski('#skF_3'(A_42))=A_42 | ~v1_zfmisc_1(A_42) | v1_xboole_0(A_42) | ~v1_zfmisc_1(A_42) | v1_xboole_0(A_42))), inference(superposition, [status(thm), theory('equality')], [c_26, c_121])).
% 2.16/1.24  tff(c_2, plain, (![C_5, A_1]: (C_5=A_1 | ~r2_hidden(C_5, k1_tarski(A_1)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.16/1.24  tff(c_202, plain, (![C_50, A_51]: (C_50='#skF_3'(A_51) | ~r2_hidden(C_50, A_51) | ~v1_zfmisc_1(A_51) | v1_xboole_0(A_51) | ~v1_zfmisc_1(A_51) | v1_xboole_0(A_51))), inference(superposition, [status(thm), theory('equality')], [c_142, c_2])).
% 2.16/1.24  tff(c_224, plain, (![A_52, B_53]: (A_52='#skF_3'(B_53) | ~v1_zfmisc_1(B_53) | v1_xboole_0(B_53) | ~m1_subset_1(A_52, B_53))), inference(resolution, [status(thm)], [c_20, c_202])).
% 2.16/1.24  tff(c_230, plain, ('#skF_3'('#skF_4')='#skF_5' | ~v1_zfmisc_1('#skF_4') | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_34, c_224])).
% 2.16/1.24  tff(c_235, plain, ('#skF_3'('#skF_4')='#skF_5' | v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_230])).
% 2.16/1.24  tff(c_236, plain, ('#skF_3'('#skF_4')='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_36, c_235])).
% 2.16/1.24  tff(c_133, plain, (![A_13]: (k1_tarski('#skF_3'(A_13))=A_13 | ~v1_zfmisc_1(A_13) | v1_xboole_0(A_13) | ~v1_zfmisc_1(A_13) | v1_xboole_0(A_13))), inference(superposition, [status(thm), theory('equality')], [c_26, c_121])).
% 2.16/1.24  tff(c_243, plain, (k1_tarski('#skF_5')='#skF_4' | ~v1_zfmisc_1('#skF_4') | v1_xboole_0('#skF_4') | ~v1_zfmisc_1('#skF_4') | v1_xboole_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_236, c_133])).
% 2.16/1.24  tff(c_259, plain, (k1_tarski('#skF_5')='#skF_4' | v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_30, c_243])).
% 2.16/1.24  tff(c_260, plain, (k1_tarski('#skF_5')='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_36, c_259])).
% 2.16/1.24  tff(c_92, plain, (k6_domain_1('#skF_4', '#skF_5')=k1_tarski('#skF_5') | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_34, c_86])).
% 2.16/1.24  tff(c_96, plain, (k6_domain_1('#skF_4', '#skF_5')=k1_tarski('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_36, c_92])).
% 2.16/1.24  tff(c_32, plain, (v1_subset_1(k6_domain_1('#skF_4', '#skF_5'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.16/1.24  tff(c_97, plain, (v1_subset_1(k1_tarski('#skF_5'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_96, c_32])).
% 2.16/1.24  tff(c_278, plain, (v1_subset_1('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_260, c_97])).
% 2.16/1.24  tff(c_281, plain, $false, inference(negUnitSimplification, [status(thm)], [c_37, c_278])).
% 2.16/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.16/1.24  
% 2.16/1.24  Inference rules
% 2.16/1.24  ----------------------
% 2.16/1.24  #Ref     : 0
% 2.16/1.24  #Sup     : 50
% 2.16/1.24  #Fact    : 0
% 2.16/1.24  #Define  : 0
% 2.16/1.24  #Split   : 0
% 2.16/1.24  #Chain   : 0
% 2.16/1.24  #Close   : 0
% 2.16/1.24  
% 2.16/1.24  Ordering : KBO
% 2.16/1.24  
% 2.16/1.24  Simplification rules
% 2.16/1.24  ----------------------
% 2.16/1.24  #Subsume      : 3
% 2.16/1.24  #Demod        : 22
% 2.16/1.24  #Tautology    : 27
% 2.16/1.24  #SimpNegUnit  : 10
% 2.16/1.24  #BackRed      : 3
% 2.16/1.24  
% 2.16/1.24  #Partial instantiations: 0
% 2.16/1.24  #Strategies tried      : 1
% 2.16/1.24  
% 2.16/1.24  Timing (in seconds)
% 2.16/1.24  ----------------------
% 2.16/1.25  Preprocessing        : 0.31
% 2.16/1.25  Parsing              : 0.16
% 2.16/1.25  CNF conversion       : 0.02
% 2.16/1.25  Main loop            : 0.21
% 2.16/1.25  Inferencing          : 0.08
% 2.16/1.25  Reduction            : 0.06
% 2.16/1.25  Demodulation         : 0.04
% 2.16/1.25  BG Simplification    : 0.02
% 2.16/1.25  Subsumption          : 0.03
% 2.16/1.25  Abstraction          : 0.02
% 2.16/1.25  MUC search           : 0.00
% 2.16/1.25  Cooper               : 0.00
% 2.16/1.25  Total                : 0.54
% 2.16/1.25  Index Insertion      : 0.00
% 2.16/1.25  Index Deletion       : 0.00
% 2.16/1.25  Index Matching       : 0.00
% 2.16/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
