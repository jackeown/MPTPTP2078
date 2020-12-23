%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:20 EST 2020

% Result     : Theorem 1.98s
% Output     : CNFRefutation 2.13s
% Verified   : 
% Statistics : Number of formulae       :   57 (  79 expanded)
%              Number of leaves         :   25 (  38 expanded)
%              Depth                    :   10
%              Number of atoms          :   92 ( 159 expanded)
%              Number of equality atoms :   38 (  52 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k6_domain_1 > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

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

tff(f_29,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ ( r1_tarski(B,A)
          & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ~ ( k1_tarski(A) = k2_xboole_0(B,C)
        & B != C
        & B != k1_xboole_0
        & C != k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_zfmisc_1)).

tff(c_32,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_30,plain,(
    v1_zfmisc_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_24,plain,(
    ! [A_16] :
      ( m1_subset_1('#skF_1'(A_16),A_16)
      | ~ v1_zfmisc_1(A_16)
      | v1_xboole_0(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_147,plain,(
    ! [A_43,B_44] :
      ( k6_domain_1(A_43,B_44) = k1_tarski(B_44)
      | ~ m1_subset_1(B_44,A_43)
      | v1_xboole_0(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_202,plain,(
    ! [A_56] :
      ( k6_domain_1(A_56,'#skF_1'(A_56)) = k1_tarski('#skF_1'(A_56))
      | ~ v1_zfmisc_1(A_56)
      | v1_xboole_0(A_56) ) ),
    inference(resolution,[status(thm)],[c_24,c_147])).

tff(c_22,plain,(
    ! [A_16] :
      ( k6_domain_1(A_16,'#skF_1'(A_16)) = A_16
      | ~ v1_zfmisc_1(A_16)
      | v1_xboole_0(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_217,plain,(
    ! [A_57] :
      ( k1_tarski('#skF_1'(A_57)) = A_57
      | ~ v1_zfmisc_1(A_57)
      | v1_xboole_0(A_57)
      | ~ v1_zfmisc_1(A_57)
      | v1_xboole_0(A_57) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_202,c_22])).

tff(c_26,plain,(
    '#skF_2' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_34,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_28,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_59,plain,(
    ! [A_29,B_30] :
      ( k4_xboole_0(A_29,B_30) = k1_xboole_0
      | ~ r1_tarski(A_29,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_67,plain,(
    k4_xboole_0('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_28,c_59])).

tff(c_14,plain,(
    ! [A_9,B_10] :
      ( r1_xboole_0(A_9,B_10)
      | k4_xboole_0(A_9,B_10) != A_9 ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_93,plain,(
    ! [B_36,A_37] :
      ( ~ r1_xboole_0(B_36,A_37)
      | ~ r1_tarski(B_36,A_37)
      | v1_xboole_0(B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_152,plain,(
    ! [A_45,B_46] :
      ( ~ r1_tarski(A_45,B_46)
      | v1_xboole_0(A_45)
      | k4_xboole_0(A_45,B_46) != A_45 ) ),
    inference(resolution,[status(thm)],[c_14,c_93])).

tff(c_161,plain,
    ( v1_xboole_0('#skF_2')
    | k4_xboole_0('#skF_2','#skF_3') != '#skF_2' ),
    inference(resolution,[status(thm)],[c_28,c_152])).

tff(c_166,plain,
    ( v1_xboole_0('#skF_2')
    | k1_xboole_0 != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_161])).

tff(c_167,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_166])).

tff(c_10,plain,(
    ! [A_7,B_8] : r1_tarski(A_7,k2_xboole_0(A_7,B_8)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_66,plain,(
    ! [A_7,B_8] : k4_xboole_0(A_7,k2_xboole_0(A_7,B_8)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_59])).

tff(c_158,plain,(
    ! [A_7,B_8] :
      ( v1_xboole_0(A_7)
      | k4_xboole_0(A_7,k2_xboole_0(A_7,B_8)) != A_7 ) ),
    inference(resolution,[status(thm)],[c_10,c_152])).

tff(c_169,plain,(
    ! [A_47] :
      ( v1_xboole_0(A_47)
      | k1_xboole_0 != A_47 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_158])).

tff(c_176,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(resolution,[status(thm)],[c_169,c_32])).

tff(c_36,plain,(
    ! [A_23,B_24] :
      ( k2_xboole_0(A_23,B_24) = B_24
      | ~ r1_tarski(A_23,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_44,plain,(
    k2_xboole_0('#skF_2','#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_28,c_36])).

tff(c_193,plain,(
    ! [C_52,B_53,A_54] :
      ( k1_xboole_0 = C_52
      | k1_xboole_0 = B_53
      | C_52 = B_53
      | k2_xboole_0(B_53,C_52) != k1_tarski(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_199,plain,(
    ! [A_54] :
      ( k1_xboole_0 = '#skF_3'
      | k1_xboole_0 = '#skF_2'
      | '#skF_2' = '#skF_3'
      | k1_tarski(A_54) != '#skF_3' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_193])).

tff(c_200,plain,(
    ! [A_54] : k1_tarski(A_54) != '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_167,c_176,c_199])).

tff(c_231,plain,(
    ! [A_58] :
      ( A_58 != '#skF_3'
      | ~ v1_zfmisc_1(A_58)
      | v1_xboole_0(A_58)
      | ~ v1_zfmisc_1(A_58)
      | v1_xboole_0(A_58) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_217,c_200])).

tff(c_233,plain,
    ( ~ v1_zfmisc_1('#skF_3')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_231])).

tff(c_236,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_233])).

tff(c_238,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_236])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:38:20 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.98/1.26  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.98/1.27  
% 1.98/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.98/1.27  %$ r1_xboole_0 > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k6_domain_1 > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3
% 1.98/1.27  
% 1.98/1.27  %Foreground sorts:
% 1.98/1.27  
% 1.98/1.27  
% 1.98/1.27  %Background operators:
% 1.98/1.27  
% 1.98/1.27  
% 1.98/1.27  %Foreground operators:
% 1.98/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.98/1.27  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.98/1.27  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.98/1.27  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.98/1.27  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.98/1.27  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 1.98/1.27  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.98/1.27  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.98/1.27  tff('#skF_2', type, '#skF_2': $i).
% 1.98/1.27  tff('#skF_3', type, '#skF_3': $i).
% 1.98/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.98/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.98/1.27  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 1.98/1.27  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.98/1.27  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.98/1.27  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.98/1.27  
% 2.13/1.28  tff(f_90, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tex_2)).
% 2.13/1.28  tff(f_76, axiom, (![A]: (~v1_xboole_0(A) => (v1_zfmisc_1(A) <=> (?[B]: (m1_subset_1(B, A) & (A = k6_domain_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tex_2)).
% 2.13/1.28  tff(f_66, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 2.13/1.28  tff(f_29, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.13/1.28  tff(f_47, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.13/1.28  tff(f_41, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_xboole_1)).
% 2.13/1.28  tff(f_43, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.13/1.28  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.13/1.28  tff(f_59, axiom, (![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~(B = C)) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_zfmisc_1)).
% 2.13/1.28  tff(c_32, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.13/1.28  tff(c_30, plain, (v1_zfmisc_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.13/1.28  tff(c_24, plain, (![A_16]: (m1_subset_1('#skF_1'(A_16), A_16) | ~v1_zfmisc_1(A_16) | v1_xboole_0(A_16))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.13/1.28  tff(c_147, plain, (![A_43, B_44]: (k6_domain_1(A_43, B_44)=k1_tarski(B_44) | ~m1_subset_1(B_44, A_43) | v1_xboole_0(A_43))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.13/1.28  tff(c_202, plain, (![A_56]: (k6_domain_1(A_56, '#skF_1'(A_56))=k1_tarski('#skF_1'(A_56)) | ~v1_zfmisc_1(A_56) | v1_xboole_0(A_56))), inference(resolution, [status(thm)], [c_24, c_147])).
% 2.13/1.28  tff(c_22, plain, (![A_16]: (k6_domain_1(A_16, '#skF_1'(A_16))=A_16 | ~v1_zfmisc_1(A_16) | v1_xboole_0(A_16))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.13/1.28  tff(c_217, plain, (![A_57]: (k1_tarski('#skF_1'(A_57))=A_57 | ~v1_zfmisc_1(A_57) | v1_xboole_0(A_57) | ~v1_zfmisc_1(A_57) | v1_xboole_0(A_57))), inference(superposition, [status(thm), theory('equality')], [c_202, c_22])).
% 2.13/1.28  tff(c_26, plain, ('#skF_2'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.13/1.28  tff(c_34, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.13/1.28  tff(c_28, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.13/1.28  tff(c_59, plain, (![A_29, B_30]: (k4_xboole_0(A_29, B_30)=k1_xboole_0 | ~r1_tarski(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.13/1.28  tff(c_67, plain, (k4_xboole_0('#skF_2', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_28, c_59])).
% 2.13/1.28  tff(c_14, plain, (![A_9, B_10]: (r1_xboole_0(A_9, B_10) | k4_xboole_0(A_9, B_10)!=A_9)), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.13/1.28  tff(c_93, plain, (![B_36, A_37]: (~r1_xboole_0(B_36, A_37) | ~r1_tarski(B_36, A_37) | v1_xboole_0(B_36))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.13/1.28  tff(c_152, plain, (![A_45, B_46]: (~r1_tarski(A_45, B_46) | v1_xboole_0(A_45) | k4_xboole_0(A_45, B_46)!=A_45)), inference(resolution, [status(thm)], [c_14, c_93])).
% 2.13/1.28  tff(c_161, plain, (v1_xboole_0('#skF_2') | k4_xboole_0('#skF_2', '#skF_3')!='#skF_2'), inference(resolution, [status(thm)], [c_28, c_152])).
% 2.13/1.28  tff(c_166, plain, (v1_xboole_0('#skF_2') | k1_xboole_0!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_67, c_161])).
% 2.13/1.28  tff(c_167, plain, (k1_xboole_0!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_34, c_166])).
% 2.13/1.28  tff(c_10, plain, (![A_7, B_8]: (r1_tarski(A_7, k2_xboole_0(A_7, B_8)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.13/1.28  tff(c_66, plain, (![A_7, B_8]: (k4_xboole_0(A_7, k2_xboole_0(A_7, B_8))=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_59])).
% 2.13/1.28  tff(c_158, plain, (![A_7, B_8]: (v1_xboole_0(A_7) | k4_xboole_0(A_7, k2_xboole_0(A_7, B_8))!=A_7)), inference(resolution, [status(thm)], [c_10, c_152])).
% 2.13/1.28  tff(c_169, plain, (![A_47]: (v1_xboole_0(A_47) | k1_xboole_0!=A_47)), inference(demodulation, [status(thm), theory('equality')], [c_66, c_158])).
% 2.13/1.28  tff(c_176, plain, (k1_xboole_0!='#skF_3'), inference(resolution, [status(thm)], [c_169, c_32])).
% 2.13/1.28  tff(c_36, plain, (![A_23, B_24]: (k2_xboole_0(A_23, B_24)=B_24 | ~r1_tarski(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.13/1.28  tff(c_44, plain, (k2_xboole_0('#skF_2', '#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_28, c_36])).
% 2.13/1.28  tff(c_193, plain, (![C_52, B_53, A_54]: (k1_xboole_0=C_52 | k1_xboole_0=B_53 | C_52=B_53 | k2_xboole_0(B_53, C_52)!=k1_tarski(A_54))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.13/1.28  tff(c_199, plain, (![A_54]: (k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | '#skF_2'='#skF_3' | k1_tarski(A_54)!='#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_44, c_193])).
% 2.13/1.28  tff(c_200, plain, (![A_54]: (k1_tarski(A_54)!='#skF_3')), inference(negUnitSimplification, [status(thm)], [c_26, c_167, c_176, c_199])).
% 2.13/1.28  tff(c_231, plain, (![A_58]: (A_58!='#skF_3' | ~v1_zfmisc_1(A_58) | v1_xboole_0(A_58) | ~v1_zfmisc_1(A_58) | v1_xboole_0(A_58))), inference(superposition, [status(thm), theory('equality')], [c_217, c_200])).
% 2.13/1.28  tff(c_233, plain, (~v1_zfmisc_1('#skF_3') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_30, c_231])).
% 2.13/1.28  tff(c_236, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_233])).
% 2.13/1.28  tff(c_238, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_236])).
% 2.13/1.28  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.13/1.28  
% 2.13/1.28  Inference rules
% 2.13/1.28  ----------------------
% 2.13/1.28  #Ref     : 0
% 2.13/1.28  #Sup     : 47
% 2.13/1.28  #Fact    : 0
% 2.13/1.28  #Define  : 0
% 2.13/1.28  #Split   : 0
% 2.13/1.28  #Chain   : 0
% 2.13/1.28  #Close   : 0
% 2.13/1.28  
% 2.13/1.28  Ordering : KBO
% 2.13/1.28  
% 2.13/1.28  Simplification rules
% 2.13/1.28  ----------------------
% 2.13/1.28  #Subsume      : 3
% 2.13/1.28  #Demod        : 17
% 2.13/1.28  #Tautology    : 26
% 2.13/1.28  #SimpNegUnit  : 4
% 2.13/1.28  #BackRed      : 0
% 2.13/1.28  
% 2.13/1.28  #Partial instantiations: 0
% 2.13/1.28  #Strategies tried      : 1
% 2.13/1.28  
% 2.13/1.28  Timing (in seconds)
% 2.13/1.28  ----------------------
% 2.13/1.29  Preprocessing        : 0.30
% 2.13/1.29  Parsing              : 0.17
% 2.13/1.29  CNF conversion       : 0.02
% 2.13/1.29  Main loop            : 0.17
% 2.13/1.29  Inferencing          : 0.07
% 2.13/1.29  Reduction            : 0.05
% 2.13/1.29  Demodulation         : 0.03
% 2.13/1.29  BG Simplification    : 0.02
% 2.13/1.29  Subsumption          : 0.02
% 2.13/1.29  Abstraction          : 0.01
% 2.13/1.29  MUC search           : 0.00
% 2.13/1.29  Cooper               : 0.00
% 2.13/1.29  Total                : 0.50
% 2.13/1.29  Index Insertion      : 0.00
% 2.13/1.29  Index Deletion       : 0.00
% 2.13/1.29  Index Matching       : 0.00
% 2.13/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
