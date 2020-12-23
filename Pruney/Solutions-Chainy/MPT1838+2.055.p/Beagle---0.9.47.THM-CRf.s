%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:21 EST 2020

% Result     : Theorem 2.13s
% Output     : CNFRefutation 2.13s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 103 expanded)
%              Number of leaves         :   25 (  46 expanded)
%              Depth                    :   12
%              Number of atoms          :   99 ( 210 expanded)
%              Number of equality atoms :   45 (  78 expanded)
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

tff(f_33,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ ( r1_tarski(B,A)
          & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

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

tff(c_121,plain,(
    ! [A_39,B_40] :
      ( k6_domain_1(A_39,B_40) = k1_tarski(B_40)
      | ~ m1_subset_1(B_40,A_39)
      | v1_xboole_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_213,plain,(
    ! [A_55] :
      ( k6_domain_1(A_55,'#skF_1'(A_55)) = k1_tarski('#skF_1'(A_55))
      | ~ v1_zfmisc_1(A_55)
      | v1_xboole_0(A_55) ) ),
    inference(resolution,[status(thm)],[c_24,c_121])).

tff(c_22,plain,(
    ! [A_16] :
      ( k6_domain_1(A_16,'#skF_1'(A_16)) = A_16
      | ~ v1_zfmisc_1(A_16)
      | v1_xboole_0(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_228,plain,(
    ! [A_56] :
      ( k1_tarski('#skF_1'(A_56)) = A_56
      | ~ v1_zfmisc_1(A_56)
      | v1_xboole_0(A_56)
      | ~ v1_zfmisc_1(A_56)
      | v1_xboole_0(A_56) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_213,c_22])).

tff(c_26,plain,(
    '#skF_2' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_34,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_28,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_36,plain,(
    ! [A_23,B_24] :
      ( k4_xboole_0(A_23,B_24) = k1_xboole_0
      | ~ r1_tarski(A_23,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_44,plain,(
    k4_xboole_0('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_28,c_36])).

tff(c_14,plain,(
    ! [A_9,B_10] :
      ( r1_xboole_0(A_9,B_10)
      | k4_xboole_0(A_9,B_10) != A_9 ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_69,plain,(
    ! [B_32,A_33] :
      ( ~ r1_xboole_0(B_32,A_33)
      | ~ r1_tarski(B_32,A_33)
      | v1_xboole_0(B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_126,plain,(
    ! [A_41,B_42] :
      ( ~ r1_tarski(A_41,B_42)
      | v1_xboole_0(A_41)
      | k4_xboole_0(A_41,B_42) != A_41 ) ),
    inference(resolution,[status(thm)],[c_14,c_69])).

tff(c_132,plain,
    ( v1_xboole_0('#skF_2')
    | k4_xboole_0('#skF_2','#skF_3') != '#skF_2' ),
    inference(resolution,[status(thm)],[c_28,c_126])).

tff(c_135,plain,
    ( v1_xboole_0('#skF_2')
    | k1_xboole_0 != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_132])).

tff(c_136,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_135])).

tff(c_50,plain,(
    ! [A_27,B_28] :
      ( k2_xboole_0(A_27,B_28) = B_28
      | ~ r1_tarski(A_27,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_58,plain,(
    k2_xboole_0('#skF_2','#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_28,c_50])).

tff(c_74,plain,(
    ! [A_34,B_35] : k4_xboole_0(k2_xboole_0(A_34,B_35),B_35) = k4_xboole_0(A_34,B_35) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_83,plain,(
    k4_xboole_0('#skF_2','#skF_3') = k4_xboole_0('#skF_3','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_74])).

tff(c_86,plain,(
    k4_xboole_0('#skF_3','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_83])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | k4_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_137,plain,(
    ! [A_43,B_44] :
      ( v1_xboole_0(A_43)
      | k4_xboole_0(A_43,B_44) != A_43
      | k4_xboole_0(A_43,B_44) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_126])).

tff(c_139,plain,
    ( v1_xboole_0('#skF_3')
    | k1_xboole_0 != '#skF_3'
    | k4_xboole_0('#skF_3','#skF_3') != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_86,c_137])).

tff(c_145,plain,
    ( v1_xboole_0('#skF_3')
    | k1_xboole_0 != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_139])).

tff(c_146,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_145])).

tff(c_199,plain,(
    ! [C_51,B_52,A_53] :
      ( k1_xboole_0 = C_51
      | k1_xboole_0 = B_52
      | C_51 = B_52
      | k2_xboole_0(B_52,C_51) != k1_tarski(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_208,plain,(
    ! [A_53] :
      ( k1_xboole_0 = '#skF_3'
      | k1_xboole_0 = '#skF_2'
      | '#skF_2' = '#skF_3'
      | k1_tarski(A_53) != '#skF_3' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_199])).

tff(c_211,plain,(
    ! [A_53] : k1_tarski(A_53) != '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_136,c_146,c_208])).

tff(c_242,plain,(
    ! [A_57] :
      ( A_57 != '#skF_3'
      | ~ v1_zfmisc_1(A_57)
      | v1_xboole_0(A_57)
      | ~ v1_zfmisc_1(A_57)
      | v1_xboole_0(A_57) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_228,c_211])).

tff(c_244,plain,
    ( ~ v1_zfmisc_1('#skF_3')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_242])).

tff(c_247,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_244])).

tff(c_249,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_247])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n019.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 20:13:07 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.13/1.40  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.13/1.41  
% 2.13/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.13/1.41  %$ r1_xboole_0 > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k6_domain_1 > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3
% 2.13/1.41  
% 2.13/1.41  %Foreground sorts:
% 2.13/1.41  
% 2.13/1.41  
% 2.13/1.41  %Background operators:
% 2.13/1.41  
% 2.13/1.41  
% 2.13/1.41  %Foreground operators:
% 2.13/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.13/1.41  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.13/1.41  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.13/1.41  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.13/1.41  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.13/1.41  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.13/1.41  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.13/1.41  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.13/1.41  tff('#skF_2', type, '#skF_2': $i).
% 2.13/1.41  tff('#skF_3', type, '#skF_3': $i).
% 2.13/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.13/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.13/1.41  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 2.13/1.41  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.13/1.41  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.13/1.41  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.13/1.41  
% 2.13/1.42  tff(f_90, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tex_2)).
% 2.13/1.42  tff(f_76, axiom, (![A]: (~v1_xboole_0(A) => (v1_zfmisc_1(A) <=> (?[B]: (m1_subset_1(B, A) & (A = k6_domain_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tex_2)).
% 2.13/1.42  tff(f_66, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 2.13/1.42  tff(f_33, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_xboole_1)).
% 2.13/1.42  tff(f_47, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.13/1.42  tff(f_43, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_xboole_1)).
% 2.13/1.42  tff(f_29, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.13/1.42  tff(f_35, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_xboole_1)).
% 2.13/1.42  tff(f_59, axiom, (![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~(B = C)) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_zfmisc_1)).
% 2.13/1.42  tff(c_32, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.13/1.42  tff(c_30, plain, (v1_zfmisc_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.13/1.42  tff(c_24, plain, (![A_16]: (m1_subset_1('#skF_1'(A_16), A_16) | ~v1_zfmisc_1(A_16) | v1_xboole_0(A_16))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.13/1.42  tff(c_121, plain, (![A_39, B_40]: (k6_domain_1(A_39, B_40)=k1_tarski(B_40) | ~m1_subset_1(B_40, A_39) | v1_xboole_0(A_39))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.13/1.42  tff(c_213, plain, (![A_55]: (k6_domain_1(A_55, '#skF_1'(A_55))=k1_tarski('#skF_1'(A_55)) | ~v1_zfmisc_1(A_55) | v1_xboole_0(A_55))), inference(resolution, [status(thm)], [c_24, c_121])).
% 2.13/1.42  tff(c_22, plain, (![A_16]: (k6_domain_1(A_16, '#skF_1'(A_16))=A_16 | ~v1_zfmisc_1(A_16) | v1_xboole_0(A_16))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.13/1.42  tff(c_228, plain, (![A_56]: (k1_tarski('#skF_1'(A_56))=A_56 | ~v1_zfmisc_1(A_56) | v1_xboole_0(A_56) | ~v1_zfmisc_1(A_56) | v1_xboole_0(A_56))), inference(superposition, [status(thm), theory('equality')], [c_213, c_22])).
% 2.13/1.42  tff(c_26, plain, ('#skF_2'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.13/1.42  tff(c_34, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.13/1.42  tff(c_28, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.13/1.42  tff(c_36, plain, (![A_23, B_24]: (k4_xboole_0(A_23, B_24)=k1_xboole_0 | ~r1_tarski(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.13/1.42  tff(c_44, plain, (k4_xboole_0('#skF_2', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_28, c_36])).
% 2.13/1.42  tff(c_14, plain, (![A_9, B_10]: (r1_xboole_0(A_9, B_10) | k4_xboole_0(A_9, B_10)!=A_9)), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.13/1.42  tff(c_69, plain, (![B_32, A_33]: (~r1_xboole_0(B_32, A_33) | ~r1_tarski(B_32, A_33) | v1_xboole_0(B_32))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.13/1.42  tff(c_126, plain, (![A_41, B_42]: (~r1_tarski(A_41, B_42) | v1_xboole_0(A_41) | k4_xboole_0(A_41, B_42)!=A_41)), inference(resolution, [status(thm)], [c_14, c_69])).
% 2.13/1.42  tff(c_132, plain, (v1_xboole_0('#skF_2') | k4_xboole_0('#skF_2', '#skF_3')!='#skF_2'), inference(resolution, [status(thm)], [c_28, c_126])).
% 2.13/1.42  tff(c_135, plain, (v1_xboole_0('#skF_2') | k1_xboole_0!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_44, c_132])).
% 2.13/1.42  tff(c_136, plain, (k1_xboole_0!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_34, c_135])).
% 2.13/1.42  tff(c_50, plain, (![A_27, B_28]: (k2_xboole_0(A_27, B_28)=B_28 | ~r1_tarski(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.13/1.42  tff(c_58, plain, (k2_xboole_0('#skF_2', '#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_28, c_50])).
% 2.13/1.42  tff(c_74, plain, (![A_34, B_35]: (k4_xboole_0(k2_xboole_0(A_34, B_35), B_35)=k4_xboole_0(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.13/1.42  tff(c_83, plain, (k4_xboole_0('#skF_2', '#skF_3')=k4_xboole_0('#skF_3', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_58, c_74])).
% 2.13/1.42  tff(c_86, plain, (k4_xboole_0('#skF_3', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_44, c_83])).
% 2.13/1.42  tff(c_4, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | k4_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.13/1.42  tff(c_137, plain, (![A_43, B_44]: (v1_xboole_0(A_43) | k4_xboole_0(A_43, B_44)!=A_43 | k4_xboole_0(A_43, B_44)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_126])).
% 2.13/1.42  tff(c_139, plain, (v1_xboole_0('#skF_3') | k1_xboole_0!='#skF_3' | k4_xboole_0('#skF_3', '#skF_3')!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_86, c_137])).
% 2.13/1.42  tff(c_145, plain, (v1_xboole_0('#skF_3') | k1_xboole_0!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_86, c_139])).
% 2.13/1.42  tff(c_146, plain, (k1_xboole_0!='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_32, c_145])).
% 2.13/1.42  tff(c_199, plain, (![C_51, B_52, A_53]: (k1_xboole_0=C_51 | k1_xboole_0=B_52 | C_51=B_52 | k2_xboole_0(B_52, C_51)!=k1_tarski(A_53))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.13/1.42  tff(c_208, plain, (![A_53]: (k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | '#skF_2'='#skF_3' | k1_tarski(A_53)!='#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_58, c_199])).
% 2.13/1.42  tff(c_211, plain, (![A_53]: (k1_tarski(A_53)!='#skF_3')), inference(negUnitSimplification, [status(thm)], [c_26, c_136, c_146, c_208])).
% 2.13/1.42  tff(c_242, plain, (![A_57]: (A_57!='#skF_3' | ~v1_zfmisc_1(A_57) | v1_xboole_0(A_57) | ~v1_zfmisc_1(A_57) | v1_xboole_0(A_57))), inference(superposition, [status(thm), theory('equality')], [c_228, c_211])).
% 2.13/1.42  tff(c_244, plain, (~v1_zfmisc_1('#skF_3') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_30, c_242])).
% 2.13/1.42  tff(c_247, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_244])).
% 2.13/1.42  tff(c_249, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_247])).
% 2.13/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.13/1.42  
% 2.13/1.42  Inference rules
% 2.13/1.42  ----------------------
% 2.13/1.42  #Ref     : 0
% 2.13/1.42  #Sup     : 52
% 2.13/1.42  #Fact    : 0
% 2.13/1.42  #Define  : 0
% 2.13/1.42  #Split   : 0
% 2.13/1.42  #Chain   : 0
% 2.13/1.42  #Close   : 0
% 2.13/1.42  
% 2.13/1.42  Ordering : KBO
% 2.13/1.42  
% 2.13/1.42  Simplification rules
% 2.13/1.42  ----------------------
% 2.13/1.42  #Subsume      : 3
% 2.13/1.42  #Demod        : 21
% 2.13/1.42  #Tautology    : 28
% 2.13/1.42  #SimpNegUnit  : 6
% 2.13/1.42  #BackRed      : 0
% 2.13/1.42  
% 2.13/1.42  #Partial instantiations: 0
% 2.13/1.42  #Strategies tried      : 1
% 2.13/1.42  
% 2.13/1.42  Timing (in seconds)
% 2.13/1.42  ----------------------
% 2.13/1.43  Preprocessing        : 0.38
% 2.13/1.43  Parsing              : 0.21
% 2.13/1.43  CNF conversion       : 0.02
% 2.13/1.43  Main loop            : 0.19
% 2.13/1.43  Inferencing          : 0.08
% 2.13/1.43  Reduction            : 0.06
% 2.13/1.43  Demodulation         : 0.04
% 2.13/1.43  BG Simplification    : 0.01
% 2.13/1.43  Subsumption          : 0.02
% 2.13/1.43  Abstraction          : 0.01
% 2.13/1.43  MUC search           : 0.00
% 2.13/1.43  Cooper               : 0.00
% 2.13/1.43  Total                : 0.60
% 2.13/1.43  Index Insertion      : 0.00
% 2.13/1.43  Index Deletion       : 0.00
% 2.13/1.43  Index Matching       : 0.00
% 2.13/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
