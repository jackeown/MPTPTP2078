%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:17 EST 2020

% Result     : Theorem 2.66s
% Output     : CNFRefutation 3.00s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 115 expanded)
%              Number of leaves         :   29 (  52 expanded)
%              Depth                    :   12
%              Number of atoms          :  104 ( 239 expanded)
%              Number of equality atoms :   51 ( 123 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k2_enumset1 > k1_enumset1 > k6_domain_1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

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

tff(f_95,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ( ~ v1_xboole_0(B)
              & v1_zfmisc_1(B) )
           => ( r1_tarski(A,B)
             => A = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).

tff(f_28,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_81,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ( v1_zfmisc_1(A)
      <=> ? [B] :
            ( m1_subset_1(B,A)
            & A = k6_domain_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tex_2)).

tff(f_71,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ~ ( k1_tarski(A) = k2_xboole_0(B,C)
        & ~ ( B = k1_tarski(A)
            & C = k1_tarski(A) )
        & ~ ( B = k1_xboole_0
            & C = k1_tarski(A) )
        & ~ ( B = k1_tarski(A)
            & C = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_38,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_40,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(c_54,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_48,plain,(
    '#skF_2' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_52,plain,(
    v1_zfmisc_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_4,plain,(
    ! [A_1] : k2_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_46,plain,(
    ! [A_21] :
      ( m1_subset_1('#skF_1'(A_21),A_21)
      | ~ v1_zfmisc_1(A_21)
      | v1_xboole_0(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_203,plain,(
    ! [A_52,B_53] :
      ( k6_domain_1(A_52,B_53) = k1_tarski(B_53)
      | ~ m1_subset_1(B_53,A_52)
      | v1_xboole_0(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_254,plain,(
    ! [A_65] :
      ( k6_domain_1(A_65,'#skF_1'(A_65)) = k1_tarski('#skF_1'(A_65))
      | ~ v1_zfmisc_1(A_65)
      | v1_xboole_0(A_65) ) ),
    inference(resolution,[status(thm)],[c_46,c_203])).

tff(c_44,plain,(
    ! [A_21] :
      ( k6_domain_1(A_21,'#skF_1'(A_21)) = A_21
      | ~ v1_zfmisc_1(A_21)
      | v1_xboole_0(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_269,plain,(
    ! [A_66] :
      ( k1_tarski('#skF_1'(A_66)) = A_66
      | ~ v1_zfmisc_1(A_66)
      | v1_xboole_0(A_66)
      | ~ v1_zfmisc_1(A_66)
      | v1_xboole_0(A_66) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_254,c_44])).

tff(c_34,plain,(
    ! [A_16,C_18,B_17] :
      ( k1_tarski(A_16) = C_18
      | k1_tarski(A_16) = B_17
      | k2_xboole_0(B_17,C_18) != k1_tarski(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_529,plain,(
    ! [A_86,C_87,B_88] :
      ( k1_tarski('#skF_1'(A_86)) = C_87
      | k1_tarski('#skF_1'(A_86)) = B_88
      | k2_xboole_0(B_88,C_87) != A_86
      | ~ v1_zfmisc_1(A_86)
      | v1_xboole_0(A_86)
      | ~ v1_zfmisc_1(A_86)
      | v1_xboole_0(A_86) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_269,c_34])).

tff(c_535,plain,(
    ! [A_89] :
      ( k1_tarski('#skF_1'(A_89)) = A_89
      | ~ v1_zfmisc_1(A_89)
      | v1_xboole_0(A_89) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_529])).

tff(c_56,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_10,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_68,plain,(
    ! [A_28,B_29] :
      ( k4_xboole_0(A_28,B_29) = k1_xboole_0
      | ~ r1_tarski(A_28,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_75,plain,(
    ! [B_4] : k4_xboole_0(B_4,B_4) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_68])).

tff(c_111,plain,(
    ! [A_37,B_38] : k5_xboole_0(A_37,k4_xboole_0(B_38,A_37)) = k2_xboole_0(A_37,B_38) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_120,plain,(
    ! [B_4] : k5_xboole_0(B_4,k1_xboole_0) = k2_xboole_0(B_4,B_4) ),
    inference(superposition,[status(thm),theory(equality)],[c_75,c_111])).

tff(c_126,plain,(
    ! [B_4] : k5_xboole_0(B_4,k1_xboole_0) = B_4 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_120])).

tff(c_50,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_76,plain,(
    k4_xboole_0('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_50,c_68])).

tff(c_123,plain,(
    k5_xboole_0('#skF_3',k1_xboole_0) = k2_xboole_0('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_111])).

tff(c_137,plain,(
    k2_xboole_0('#skF_3','#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_123])).

tff(c_208,plain,(
    ! [A_54,C_55,B_56] :
      ( k1_tarski(A_54) = C_55
      | k1_xboole_0 = C_55
      | k2_xboole_0(B_56,C_55) != k1_tarski(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_211,plain,(
    ! [A_54] :
      ( k1_tarski(A_54) = '#skF_2'
      | k1_xboole_0 = '#skF_2'
      | k1_tarski(A_54) != '#skF_3' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_137,c_208])).

tff(c_215,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_211])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_225,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_215,c_2])).

tff(c_227,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_225])).

tff(c_228,plain,(
    ! [A_54] :
      ( k1_tarski(A_54) = '#skF_2'
      | k1_tarski(A_54) != '#skF_3' ) ),
    inference(splitRight,[status(thm)],[c_211])).

tff(c_575,plain,(
    ! [A_90] :
      ( k1_tarski('#skF_1'(A_90)) = '#skF_2'
      | A_90 != '#skF_3'
      | ~ v1_zfmisc_1(A_90)
      | v1_xboole_0(A_90) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_535,c_228])).

tff(c_534,plain,(
    ! [A_86] :
      ( k1_tarski('#skF_1'(A_86)) = A_86
      | ~ v1_zfmisc_1(A_86)
      | v1_xboole_0(A_86) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_529])).

tff(c_611,plain,(
    ! [A_91] :
      ( A_91 = '#skF_2'
      | ~ v1_zfmisc_1(A_91)
      | v1_xboole_0(A_91)
      | A_91 != '#skF_3'
      | ~ v1_zfmisc_1(A_91)
      | v1_xboole_0(A_91) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_575,c_534])).

tff(c_613,plain,
    ( '#skF_2' = '#skF_3'
    | ~ v1_zfmisc_1('#skF_3')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_611])).

tff(c_616,plain,
    ( '#skF_2' = '#skF_3'
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_613])).

tff(c_618,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_48,c_616])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:40:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.66/1.42  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.66/1.43  
% 2.66/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.66/1.43  %$ r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k2_enumset1 > k1_enumset1 > k6_domain_1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3
% 2.66/1.43  
% 2.66/1.43  %Foreground sorts:
% 2.66/1.43  
% 2.66/1.43  
% 2.66/1.43  %Background operators:
% 2.66/1.43  
% 2.66/1.43  
% 2.66/1.43  %Foreground operators:
% 2.66/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.66/1.43  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.66/1.43  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.66/1.43  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.66/1.43  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.66/1.43  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.66/1.43  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.66/1.43  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.66/1.43  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.66/1.43  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.66/1.43  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.66/1.43  tff('#skF_2', type, '#skF_2': $i).
% 2.66/1.43  tff('#skF_3', type, '#skF_3': $i).
% 2.66/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.66/1.43  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.66/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.66/1.43  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 2.66/1.43  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.66/1.43  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.66/1.43  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.66/1.43  
% 3.00/1.44  tff(f_95, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tex_2)).
% 3.00/1.44  tff(f_28, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 3.00/1.44  tff(f_81, axiom, (![A]: (~v1_xboole_0(A) => (v1_zfmisc_1(A) <=> (?[B]: (m1_subset_1(B, A) & (A = k6_domain_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tex_2)).
% 3.00/1.44  tff(f_71, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 3.00/1.44  tff(f_64, axiom, (![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~((B = k1_tarski(A)) & (C = k1_tarski(A)))) & ~((B = k1_xboole_0) & (C = k1_tarski(A)))) & ~((B = k1_tarski(A)) & (C = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_zfmisc_1)).
% 3.00/1.44  tff(f_34, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.00/1.44  tff(f_38, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 3.00/1.44  tff(f_40, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 3.00/1.44  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.00/1.44  tff(c_54, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.00/1.44  tff(c_48, plain, ('#skF_2'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.00/1.44  tff(c_52, plain, (v1_zfmisc_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.00/1.44  tff(c_4, plain, (![A_1]: (k2_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_28])).
% 3.00/1.44  tff(c_46, plain, (![A_21]: (m1_subset_1('#skF_1'(A_21), A_21) | ~v1_zfmisc_1(A_21) | v1_xboole_0(A_21))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.00/1.44  tff(c_203, plain, (![A_52, B_53]: (k6_domain_1(A_52, B_53)=k1_tarski(B_53) | ~m1_subset_1(B_53, A_52) | v1_xboole_0(A_52))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.00/1.44  tff(c_254, plain, (![A_65]: (k6_domain_1(A_65, '#skF_1'(A_65))=k1_tarski('#skF_1'(A_65)) | ~v1_zfmisc_1(A_65) | v1_xboole_0(A_65))), inference(resolution, [status(thm)], [c_46, c_203])).
% 3.00/1.44  tff(c_44, plain, (![A_21]: (k6_domain_1(A_21, '#skF_1'(A_21))=A_21 | ~v1_zfmisc_1(A_21) | v1_xboole_0(A_21))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.00/1.44  tff(c_269, plain, (![A_66]: (k1_tarski('#skF_1'(A_66))=A_66 | ~v1_zfmisc_1(A_66) | v1_xboole_0(A_66) | ~v1_zfmisc_1(A_66) | v1_xboole_0(A_66))), inference(superposition, [status(thm), theory('equality')], [c_254, c_44])).
% 3.00/1.44  tff(c_34, plain, (![A_16, C_18, B_17]: (k1_tarski(A_16)=C_18 | k1_tarski(A_16)=B_17 | k2_xboole_0(B_17, C_18)!=k1_tarski(A_16))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.00/1.44  tff(c_529, plain, (![A_86, C_87, B_88]: (k1_tarski('#skF_1'(A_86))=C_87 | k1_tarski('#skF_1'(A_86))=B_88 | k2_xboole_0(B_88, C_87)!=A_86 | ~v1_zfmisc_1(A_86) | v1_xboole_0(A_86) | ~v1_zfmisc_1(A_86) | v1_xboole_0(A_86))), inference(superposition, [status(thm), theory('equality')], [c_269, c_34])).
% 3.00/1.44  tff(c_535, plain, (![A_89]: (k1_tarski('#skF_1'(A_89))=A_89 | ~v1_zfmisc_1(A_89) | v1_xboole_0(A_89))), inference(superposition, [status(thm), theory('equality')], [c_4, c_529])).
% 3.00/1.44  tff(c_56, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.00/1.44  tff(c_10, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.00/1.44  tff(c_68, plain, (![A_28, B_29]: (k4_xboole_0(A_28, B_29)=k1_xboole_0 | ~r1_tarski(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.00/1.44  tff(c_75, plain, (![B_4]: (k4_xboole_0(B_4, B_4)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_68])).
% 3.00/1.44  tff(c_111, plain, (![A_37, B_38]: (k5_xboole_0(A_37, k4_xboole_0(B_38, A_37))=k2_xboole_0(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.00/1.44  tff(c_120, plain, (![B_4]: (k5_xboole_0(B_4, k1_xboole_0)=k2_xboole_0(B_4, B_4))), inference(superposition, [status(thm), theory('equality')], [c_75, c_111])).
% 3.00/1.44  tff(c_126, plain, (![B_4]: (k5_xboole_0(B_4, k1_xboole_0)=B_4)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_120])).
% 3.00/1.44  tff(c_50, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.00/1.44  tff(c_76, plain, (k4_xboole_0('#skF_2', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_50, c_68])).
% 3.00/1.44  tff(c_123, plain, (k5_xboole_0('#skF_3', k1_xboole_0)=k2_xboole_0('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_76, c_111])).
% 3.00/1.44  tff(c_137, plain, (k2_xboole_0('#skF_3', '#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_126, c_123])).
% 3.00/1.44  tff(c_208, plain, (![A_54, C_55, B_56]: (k1_tarski(A_54)=C_55 | k1_xboole_0=C_55 | k2_xboole_0(B_56, C_55)!=k1_tarski(A_54))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.00/1.44  tff(c_211, plain, (![A_54]: (k1_tarski(A_54)='#skF_2' | k1_xboole_0='#skF_2' | k1_tarski(A_54)!='#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_137, c_208])).
% 3.00/1.44  tff(c_215, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_211])).
% 3.00/1.44  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 3.00/1.44  tff(c_225, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_215, c_2])).
% 3.00/1.44  tff(c_227, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_225])).
% 3.00/1.44  tff(c_228, plain, (![A_54]: (k1_tarski(A_54)='#skF_2' | k1_tarski(A_54)!='#skF_3')), inference(splitRight, [status(thm)], [c_211])).
% 3.00/1.44  tff(c_575, plain, (![A_90]: (k1_tarski('#skF_1'(A_90))='#skF_2' | A_90!='#skF_3' | ~v1_zfmisc_1(A_90) | v1_xboole_0(A_90))), inference(superposition, [status(thm), theory('equality')], [c_535, c_228])).
% 3.00/1.44  tff(c_534, plain, (![A_86]: (k1_tarski('#skF_1'(A_86))=A_86 | ~v1_zfmisc_1(A_86) | v1_xboole_0(A_86))), inference(superposition, [status(thm), theory('equality')], [c_4, c_529])).
% 3.00/1.44  tff(c_611, plain, (![A_91]: (A_91='#skF_2' | ~v1_zfmisc_1(A_91) | v1_xboole_0(A_91) | A_91!='#skF_3' | ~v1_zfmisc_1(A_91) | v1_xboole_0(A_91))), inference(superposition, [status(thm), theory('equality')], [c_575, c_534])).
% 3.00/1.44  tff(c_613, plain, ('#skF_2'='#skF_3' | ~v1_zfmisc_1('#skF_3') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_52, c_611])).
% 3.00/1.44  tff(c_616, plain, ('#skF_2'='#skF_3' | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_613])).
% 3.00/1.44  tff(c_618, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_48, c_616])).
% 3.00/1.44  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.00/1.44  
% 3.00/1.44  Inference rules
% 3.00/1.44  ----------------------
% 3.00/1.44  #Ref     : 5
% 3.00/1.44  #Sup     : 131
% 3.00/1.44  #Fact    : 0
% 3.00/1.44  #Define  : 0
% 3.00/1.44  #Split   : 3
% 3.00/1.44  #Chain   : 0
% 3.00/1.44  #Close   : 0
% 3.00/1.44  
% 3.00/1.44  Ordering : KBO
% 3.00/1.44  
% 3.00/1.44  Simplification rules
% 3.00/1.44  ----------------------
% 3.00/1.44  #Subsume      : 25
% 3.00/1.44  #Demod        : 39
% 3.00/1.44  #Tautology    : 57
% 3.00/1.44  #SimpNegUnit  : 15
% 3.00/1.44  #BackRed      : 28
% 3.00/1.44  
% 3.00/1.44  #Partial instantiations: 0
% 3.00/1.44  #Strategies tried      : 1
% 3.00/1.44  
% 3.00/1.44  Timing (in seconds)
% 3.00/1.44  ----------------------
% 3.00/1.45  Preprocessing        : 0.32
% 3.00/1.45  Parsing              : 0.17
% 3.00/1.45  CNF conversion       : 0.02
% 3.00/1.45  Main loop            : 0.35
% 3.00/1.45  Inferencing          : 0.11
% 3.00/1.45  Reduction            : 0.10
% 3.00/1.45  Demodulation         : 0.06
% 3.00/1.45  BG Simplification    : 0.02
% 3.00/1.45  Subsumption          : 0.09
% 3.00/1.45  Abstraction          : 0.02
% 3.00/1.45  MUC search           : 0.00
% 3.00/1.45  Cooper               : 0.00
% 3.00/1.45  Total                : 0.70
% 3.00/1.45  Index Insertion      : 0.00
% 3.00/1.45  Index Deletion       : 0.00
% 3.00/1.45  Index Matching       : 0.00
% 3.00/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
