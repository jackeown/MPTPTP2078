%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:19 EST 2020

% Result     : Theorem 2.43s
% Output     : CNFRefutation 2.48s
% Verified   : 
% Statistics : Number of formulae       :   52 ( 102 expanded)
%              Number of leaves         :   20 (  43 expanded)
%              Depth                    :   11
%              Number of atoms          :  116 ( 287 expanded)
%              Number of equality atoms :   46 ( 115 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k6_domain_1 > k2_xboole_0 > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_79,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ( ~ v1_xboole_0(B)
              & v1_zfmisc_1(B) )
           => ( r1_tarski(A,B)
             => A = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).

tff(f_65,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ( v1_zfmisc_1(A)
      <=> ? [B] :
            ( m1_subset_1(B,A)
            & A = k6_domain_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tex_2)).

tff(f_55,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_30,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ~ ( k1_tarski(A) = k2_xboole_0(B,C)
        & ~ ( B = k1_tarski(A)
            & C = k1_tarski(A) )
        & ~ ( B = k1_xboole_0
            & C = k1_tarski(A) )
        & ~ ( B = k1_tarski(A)
            & C = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_zfmisc_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(c_36,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_34,plain,(
    v1_zfmisc_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_30,plain,(
    '#skF_2' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_28,plain,(
    ! [A_8] :
      ( m1_subset_1('#skF_1'(A_8),A_8)
      | ~ v1_zfmisc_1(A_8)
      | v1_xboole_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_58,plain,(
    ! [A_17,B_18] :
      ( k6_domain_1(A_17,B_18) = k1_tarski(B_18)
      | ~ m1_subset_1(B_18,A_17)
      | v1_xboole_0(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_88,plain,(
    ! [A_31] :
      ( k6_domain_1(A_31,'#skF_1'(A_31)) = k1_tarski('#skF_1'(A_31))
      | ~ v1_zfmisc_1(A_31)
      | v1_xboole_0(A_31) ) ),
    inference(resolution,[status(thm)],[c_28,c_58])).

tff(c_26,plain,(
    ! [A_8] :
      ( k6_domain_1(A_8,'#skF_1'(A_8)) = A_8
      | ~ v1_zfmisc_1(A_8)
      | v1_xboole_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_103,plain,(
    ! [A_32] :
      ( k1_tarski('#skF_1'(A_32)) = A_32
      | ~ v1_zfmisc_1(A_32)
      | v1_xboole_0(A_32)
      | ~ v1_zfmisc_1(A_32)
      | v1_xboole_0(A_32) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_26])).

tff(c_38,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_32,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_39,plain,(
    ! [A_13,B_14] :
      ( k2_xboole_0(A_13,B_14) = B_14
      | ~ r1_tarski(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_43,plain,(
    k2_xboole_0('#skF_2','#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_32,c_39])).

tff(c_63,plain,(
    ! [B_19,A_20,C_21] :
      ( k1_xboole_0 = B_19
      | k1_tarski(A_20) = B_19
      | k2_xboole_0(B_19,C_21) != k1_tarski(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_66,plain,(
    ! [A_20] :
      ( k1_xboole_0 = '#skF_2'
      | k1_tarski(A_20) = '#skF_2'
      | k1_tarski(A_20) != '#skF_3' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_43,c_63])).

tff(c_67,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_69,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_2])).

tff(c_71,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_69])).

tff(c_72,plain,(
    ! [A_20] :
      ( k1_tarski(A_20) = '#skF_2'
      | k1_tarski(A_20) != '#skF_3' ) ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_112,plain,(
    ! [A_32] :
      ( k1_tarski('#skF_1'(A_32)) = '#skF_2'
      | A_32 != '#skF_3'
      | ~ v1_zfmisc_1(A_32)
      | v1_xboole_0(A_32)
      | ~ v1_zfmisc_1(A_32)
      | v1_xboole_0(A_32) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_103,c_72])).

tff(c_6,plain,(
    ! [A_3,C_5,B_4] :
      ( k1_tarski(A_3) = C_5
      | k1_xboole_0 = C_5
      | k2_xboole_0(B_4,C_5) != k1_tarski(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_156,plain,(
    ! [A_34,C_35,B_36] :
      ( k1_tarski('#skF_1'(A_34)) = C_35
      | k1_xboole_0 = C_35
      | k2_xboole_0(B_36,C_35) != A_34
      | ~ v1_zfmisc_1(A_34)
      | v1_xboole_0(A_34)
      | ~ v1_zfmisc_1(A_34)
      | v1_xboole_0(A_34) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_103,c_6])).

tff(c_158,plain,(
    ! [A_34] :
      ( k1_tarski('#skF_1'(A_34)) = '#skF_3'
      | k1_xboole_0 = '#skF_3'
      | A_34 != '#skF_3'
      | ~ v1_zfmisc_1(A_34)
      | v1_xboole_0(A_34)
      | ~ v1_zfmisc_1(A_34)
      | v1_xboole_0(A_34) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_43,c_156])).

tff(c_159,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_158])).

tff(c_173,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_159,c_2])).

tff(c_175,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_173])).

tff(c_179,plain,(
    ! [A_40] :
      ( k1_tarski('#skF_1'(A_40)) = '#skF_3'
      | A_40 != '#skF_3'
      | ~ v1_zfmisc_1(A_40)
      | v1_xboole_0(A_40)
      | ~ v1_zfmisc_1(A_40)
      | v1_xboole_0(A_40) ) ),
    inference(splitRight,[status(thm)],[c_158])).

tff(c_206,plain,(
    ! [A_32] :
      ( '#skF_2' = '#skF_3'
      | A_32 != '#skF_3'
      | ~ v1_zfmisc_1(A_32)
      | v1_xboole_0(A_32)
      | ~ v1_zfmisc_1(A_32)
      | v1_xboole_0(A_32)
      | A_32 != '#skF_3'
      | ~ v1_zfmisc_1(A_32)
      | v1_xboole_0(A_32)
      | ~ v1_zfmisc_1(A_32)
      | v1_xboole_0(A_32) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_112,c_179])).

tff(c_216,plain,(
    ! [A_41] :
      ( A_41 != '#skF_3'
      | ~ v1_zfmisc_1(A_41)
      | v1_xboole_0(A_41)
      | ~ v1_zfmisc_1(A_41)
      | v1_xboole_0(A_41)
      | A_41 != '#skF_3'
      | ~ v1_zfmisc_1(A_41)
      | v1_xboole_0(A_41)
      | ~ v1_zfmisc_1(A_41)
      | v1_xboole_0(A_41) ) ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_206])).

tff(c_218,plain,
    ( ~ v1_zfmisc_1('#skF_3')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_216])).

tff(c_221,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_218])).

tff(c_223,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_221])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n006.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:27:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.43/1.24  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.43/1.24  
% 2.43/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.43/1.24  %$ r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k6_domain_1 > k2_xboole_0 > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3
% 2.43/1.24  
% 2.43/1.24  %Foreground sorts:
% 2.43/1.24  
% 2.43/1.24  
% 2.43/1.24  %Background operators:
% 2.43/1.24  
% 2.43/1.24  
% 2.43/1.24  %Foreground operators:
% 2.43/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.43/1.24  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.43/1.24  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.43/1.24  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.43/1.24  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.43/1.24  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.43/1.24  tff('#skF_2', type, '#skF_2': $i).
% 2.43/1.24  tff('#skF_3', type, '#skF_3': $i).
% 2.43/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.43/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.43/1.24  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 2.43/1.24  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.43/1.24  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.43/1.24  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.43/1.24  
% 2.48/1.26  tff(f_79, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tex_2)).
% 2.48/1.26  tff(f_65, axiom, (![A]: (~v1_xboole_0(A) => (v1_zfmisc_1(A) <=> (?[B]: (m1_subset_1(B, A) & (A = k6_domain_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tex_2)).
% 2.48/1.26  tff(f_55, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 2.48/1.26  tff(f_30, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.48/1.26  tff(f_48, axiom, (![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~((B = k1_tarski(A)) & (C = k1_tarski(A)))) & ~((B = k1_xboole_0) & (C = k1_tarski(A)))) & ~((B = k1_tarski(A)) & (C = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_zfmisc_1)).
% 2.48/1.26  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.48/1.26  tff(c_36, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.48/1.26  tff(c_34, plain, (v1_zfmisc_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.48/1.26  tff(c_30, plain, ('#skF_2'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.48/1.26  tff(c_28, plain, (![A_8]: (m1_subset_1('#skF_1'(A_8), A_8) | ~v1_zfmisc_1(A_8) | v1_xboole_0(A_8))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.48/1.26  tff(c_58, plain, (![A_17, B_18]: (k6_domain_1(A_17, B_18)=k1_tarski(B_18) | ~m1_subset_1(B_18, A_17) | v1_xboole_0(A_17))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.48/1.26  tff(c_88, plain, (![A_31]: (k6_domain_1(A_31, '#skF_1'(A_31))=k1_tarski('#skF_1'(A_31)) | ~v1_zfmisc_1(A_31) | v1_xboole_0(A_31))), inference(resolution, [status(thm)], [c_28, c_58])).
% 2.48/1.26  tff(c_26, plain, (![A_8]: (k6_domain_1(A_8, '#skF_1'(A_8))=A_8 | ~v1_zfmisc_1(A_8) | v1_xboole_0(A_8))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.48/1.26  tff(c_103, plain, (![A_32]: (k1_tarski('#skF_1'(A_32))=A_32 | ~v1_zfmisc_1(A_32) | v1_xboole_0(A_32) | ~v1_zfmisc_1(A_32) | v1_xboole_0(A_32))), inference(superposition, [status(thm), theory('equality')], [c_88, c_26])).
% 2.48/1.26  tff(c_38, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.48/1.26  tff(c_32, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.48/1.26  tff(c_39, plain, (![A_13, B_14]: (k2_xboole_0(A_13, B_14)=B_14 | ~r1_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.48/1.26  tff(c_43, plain, (k2_xboole_0('#skF_2', '#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_32, c_39])).
% 2.48/1.26  tff(c_63, plain, (![B_19, A_20, C_21]: (k1_xboole_0=B_19 | k1_tarski(A_20)=B_19 | k2_xboole_0(B_19, C_21)!=k1_tarski(A_20))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.48/1.26  tff(c_66, plain, (![A_20]: (k1_xboole_0='#skF_2' | k1_tarski(A_20)='#skF_2' | k1_tarski(A_20)!='#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_43, c_63])).
% 2.48/1.26  tff(c_67, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_66])).
% 2.48/1.26  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.48/1.26  tff(c_69, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_67, c_2])).
% 2.48/1.26  tff(c_71, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_69])).
% 2.48/1.26  tff(c_72, plain, (![A_20]: (k1_tarski(A_20)='#skF_2' | k1_tarski(A_20)!='#skF_3')), inference(splitRight, [status(thm)], [c_66])).
% 2.48/1.26  tff(c_112, plain, (![A_32]: (k1_tarski('#skF_1'(A_32))='#skF_2' | A_32!='#skF_3' | ~v1_zfmisc_1(A_32) | v1_xboole_0(A_32) | ~v1_zfmisc_1(A_32) | v1_xboole_0(A_32))), inference(superposition, [status(thm), theory('equality')], [c_103, c_72])).
% 2.48/1.26  tff(c_6, plain, (![A_3, C_5, B_4]: (k1_tarski(A_3)=C_5 | k1_xboole_0=C_5 | k2_xboole_0(B_4, C_5)!=k1_tarski(A_3))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.48/1.26  tff(c_156, plain, (![A_34, C_35, B_36]: (k1_tarski('#skF_1'(A_34))=C_35 | k1_xboole_0=C_35 | k2_xboole_0(B_36, C_35)!=A_34 | ~v1_zfmisc_1(A_34) | v1_xboole_0(A_34) | ~v1_zfmisc_1(A_34) | v1_xboole_0(A_34))), inference(superposition, [status(thm), theory('equality')], [c_103, c_6])).
% 2.48/1.26  tff(c_158, plain, (![A_34]: (k1_tarski('#skF_1'(A_34))='#skF_3' | k1_xboole_0='#skF_3' | A_34!='#skF_3' | ~v1_zfmisc_1(A_34) | v1_xboole_0(A_34) | ~v1_zfmisc_1(A_34) | v1_xboole_0(A_34))), inference(superposition, [status(thm), theory('equality')], [c_43, c_156])).
% 2.48/1.26  tff(c_159, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_158])).
% 2.48/1.26  tff(c_173, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_159, c_2])).
% 2.48/1.26  tff(c_175, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_173])).
% 2.48/1.26  tff(c_179, plain, (![A_40]: (k1_tarski('#skF_1'(A_40))='#skF_3' | A_40!='#skF_3' | ~v1_zfmisc_1(A_40) | v1_xboole_0(A_40) | ~v1_zfmisc_1(A_40) | v1_xboole_0(A_40))), inference(splitRight, [status(thm)], [c_158])).
% 2.48/1.26  tff(c_206, plain, (![A_32]: ('#skF_2'='#skF_3' | A_32!='#skF_3' | ~v1_zfmisc_1(A_32) | v1_xboole_0(A_32) | ~v1_zfmisc_1(A_32) | v1_xboole_0(A_32) | A_32!='#skF_3' | ~v1_zfmisc_1(A_32) | v1_xboole_0(A_32) | ~v1_zfmisc_1(A_32) | v1_xboole_0(A_32))), inference(superposition, [status(thm), theory('equality')], [c_112, c_179])).
% 2.48/1.26  tff(c_216, plain, (![A_41]: (A_41!='#skF_3' | ~v1_zfmisc_1(A_41) | v1_xboole_0(A_41) | ~v1_zfmisc_1(A_41) | v1_xboole_0(A_41) | A_41!='#skF_3' | ~v1_zfmisc_1(A_41) | v1_xboole_0(A_41) | ~v1_zfmisc_1(A_41) | v1_xboole_0(A_41))), inference(negUnitSimplification, [status(thm)], [c_30, c_206])).
% 2.48/1.26  tff(c_218, plain, (~v1_zfmisc_1('#skF_3') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_34, c_216])).
% 2.48/1.26  tff(c_221, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_218])).
% 2.48/1.26  tff(c_223, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_221])).
% 2.48/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.48/1.26  
% 2.48/1.26  Inference rules
% 2.48/1.26  ----------------------
% 2.48/1.26  #Ref     : 2
% 2.48/1.26  #Sup     : 41
% 2.48/1.26  #Fact    : 0
% 2.48/1.26  #Define  : 0
% 2.48/1.26  #Split   : 2
% 2.48/1.26  #Chain   : 0
% 2.48/1.26  #Close   : 0
% 2.48/1.26  
% 2.48/1.26  Ordering : KBO
% 2.48/1.26  
% 2.48/1.26  Simplification rules
% 2.48/1.26  ----------------------
% 2.48/1.26  #Subsume      : 11
% 2.48/1.26  #Demod        : 9
% 2.48/1.26  #Tautology    : 16
% 2.48/1.26  #SimpNegUnit  : 6
% 2.48/1.26  #BackRed      : 8
% 2.48/1.26  
% 2.48/1.26  #Partial instantiations: 0
% 2.48/1.26  #Strategies tried      : 1
% 2.48/1.26  
% 2.48/1.26  Timing (in seconds)
% 2.48/1.26  ----------------------
% 2.48/1.26  Preprocessing        : 0.29
% 2.48/1.26  Parsing              : 0.15
% 2.48/1.26  CNF conversion       : 0.02
% 2.48/1.26  Main loop            : 0.20
% 2.48/1.26  Inferencing          : 0.07
% 2.48/1.26  Reduction            : 0.05
% 2.48/1.26  Demodulation         : 0.03
% 2.48/1.26  BG Simplification    : 0.02
% 2.48/1.26  Subsumption          : 0.05
% 2.48/1.26  Abstraction          : 0.01
% 2.48/1.26  MUC search           : 0.00
% 2.48/1.26  Cooper               : 0.00
% 2.48/1.26  Total                : 0.52
% 2.48/1.26  Index Insertion      : 0.00
% 2.48/1.26  Index Deletion       : 0.00
% 2.48/1.26  Index Matching       : 0.00
% 2.48/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
