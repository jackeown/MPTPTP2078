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
% DateTime   : Thu Dec  3 10:28:20 EST 2020

% Result     : Theorem 2.26s
% Output     : CNFRefutation 2.26s
% Verified   : 
% Statistics : Number of formulae       :   53 (  71 expanded)
%              Number of leaves         :   24 (  35 expanded)
%              Depth                    :   11
%              Number of atoms          :  104 ( 169 expanded)
%              Number of equality atoms :   42 (  56 expanded)
%              Maximal formula depth    :   12 (   4 average)
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

tff(f_94,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ( ~ v1_xboole_0(B)
              & v1_zfmisc_1(B) )
           => ( r1_tarski(A,B)
             => A = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).

tff(f_80,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ( v1_zfmisc_1(A)
      <=> ? [B] :
            ( m1_subset_1(B,A)
            & A = k6_domain_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tex_2)).

tff(f_70,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ ( r1_tarski(B,A)
          & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ~ ( k1_tarski(A) = k2_xboole_0(B,C)
        & ~ ( B = k1_tarski(A)
            & C = k1_tarski(A) )
        & ~ ( B = k1_xboole_0
            & C = k1_tarski(A) )
        & ~ ( B = k1_tarski(A)
            & C = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_zfmisc_1)).

tff(c_44,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_38,plain,(
    '#skF_2' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_42,plain,(
    v1_zfmisc_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_36,plain,(
    ! [A_14] :
      ( m1_subset_1('#skF_1'(A_14),A_14)
      | ~ v1_zfmisc_1(A_14)
      | v1_xboole_0(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_118,plain,(
    ! [A_41,B_42] :
      ( k6_domain_1(A_41,B_42) = k1_tarski(B_42)
      | ~ m1_subset_1(B_42,A_41)
      | v1_xboole_0(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_142,plain,(
    ! [A_53] :
      ( k6_domain_1(A_53,'#skF_1'(A_53)) = k1_tarski('#skF_1'(A_53))
      | ~ v1_zfmisc_1(A_53)
      | v1_xboole_0(A_53) ) ),
    inference(resolution,[status(thm)],[c_36,c_118])).

tff(c_34,plain,(
    ! [A_14] :
      ( k6_domain_1(A_14,'#skF_1'(A_14)) = A_14
      | ~ v1_zfmisc_1(A_14)
      | v1_xboole_0(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_148,plain,(
    ! [A_53] :
      ( k1_tarski('#skF_1'(A_53)) = A_53
      | ~ v1_zfmisc_1(A_53)
      | v1_xboole_0(A_53)
      | ~ v1_zfmisc_1(A_53)
      | v1_xboole_0(A_53) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_142,c_34])).

tff(c_157,plain,(
    ! [A_54] :
      ( k1_tarski('#skF_1'(A_54)) = A_54
      | ~ v1_zfmisc_1(A_54)
      | v1_xboole_0(A_54)
      | ~ v1_zfmisc_1(A_54)
      | v1_xboole_0(A_54) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_142,c_34])).

tff(c_46,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_40,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_47,plain,(
    ! [A_19,B_20] :
      ( k4_xboole_0(A_19,B_20) = k1_xboole_0
      | ~ r1_tarski(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_51,plain,(
    k4_xboole_0('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_40,c_47])).

tff(c_12,plain,(
    ! [A_7,B_8] :
      ( r1_xboole_0(A_7,B_8)
      | k4_xboole_0(A_7,B_8) != A_7 ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_81,plain,(
    ! [B_30,A_31] :
      ( ~ r1_xboole_0(B_30,A_31)
      | ~ r1_tarski(B_30,A_31)
      | v1_xboole_0(B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_101,plain,(
    ! [A_35,B_36] :
      ( ~ r1_tarski(A_35,B_36)
      | v1_xboole_0(A_35)
      | k4_xboole_0(A_35,B_36) != A_35 ) ),
    inference(resolution,[status(thm)],[c_12,c_81])).

tff(c_107,plain,
    ( v1_xboole_0('#skF_2')
    | k4_xboole_0('#skF_2','#skF_3') != '#skF_2' ),
    inference(resolution,[status(thm)],[c_40,c_101])).

tff(c_110,plain,
    ( v1_xboole_0('#skF_2')
    | k1_xboole_0 != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_51,c_107])).

tff(c_111,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_110])).

tff(c_67,plain,(
    ! [A_27,B_28] :
      ( k2_xboole_0(A_27,B_28) = B_28
      | ~ r1_tarski(A_27,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_75,plain,(
    k2_xboole_0('#skF_2','#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_40,c_67])).

tff(c_112,plain,(
    ! [B_37,A_38,C_39] :
      ( k1_xboole_0 = B_37
      | k1_tarski(A_38) = B_37
      | k2_xboole_0(B_37,C_39) != k1_tarski(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_115,plain,(
    ! [A_38] :
      ( k1_xboole_0 = '#skF_2'
      | k1_tarski(A_38) = '#skF_2'
      | k1_tarski(A_38) != '#skF_3' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_75,c_112])).

tff(c_116,plain,(
    ! [A_38] :
      ( k1_tarski(A_38) = '#skF_2'
      | k1_tarski(A_38) != '#skF_3' ) ),
    inference(negUnitSimplification,[status(thm)],[c_111,c_115])).

tff(c_179,plain,(
    ! [A_55] :
      ( k1_tarski('#skF_1'(A_55)) = '#skF_2'
      | A_55 != '#skF_3'
      | ~ v1_zfmisc_1(A_55)
      | v1_xboole_0(A_55)
      | ~ v1_zfmisc_1(A_55)
      | v1_xboole_0(A_55) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_157,c_116])).

tff(c_328,plain,(
    ! [A_91] :
      ( A_91 = '#skF_2'
      | A_91 != '#skF_3'
      | ~ v1_zfmisc_1(A_91)
      | v1_xboole_0(A_91)
      | ~ v1_zfmisc_1(A_91)
      | v1_xboole_0(A_91)
      | ~ v1_zfmisc_1(A_91)
      | v1_xboole_0(A_91)
      | ~ v1_zfmisc_1(A_91)
      | v1_xboole_0(A_91) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_148,c_179])).

tff(c_330,plain,
    ( '#skF_2' = '#skF_3'
    | ~ v1_zfmisc_1('#skF_3')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_328])).

tff(c_333,plain,
    ( '#skF_2' = '#skF_3'
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_330])).

tff(c_335,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_38,c_333])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 13:45:07 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.26/1.28  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.26/1.28  
% 2.26/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.26/1.28  %$ r1_xboole_0 > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k6_domain_1 > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3
% 2.26/1.28  
% 2.26/1.28  %Foreground sorts:
% 2.26/1.28  
% 2.26/1.28  
% 2.26/1.28  %Background operators:
% 2.26/1.28  
% 2.26/1.28  
% 2.26/1.28  %Foreground operators:
% 2.26/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.26/1.28  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.26/1.28  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.26/1.28  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.26/1.28  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.26/1.28  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.26/1.28  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.26/1.28  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.26/1.28  tff('#skF_2', type, '#skF_2': $i).
% 2.26/1.28  tff('#skF_3', type, '#skF_3': $i).
% 2.26/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.26/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.26/1.28  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 2.26/1.28  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.26/1.28  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.26/1.28  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.26/1.28  
% 2.26/1.30  tff(f_94, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tex_2)).
% 2.26/1.30  tff(f_80, axiom, (![A]: (~v1_xboole_0(A) => (v1_zfmisc_1(A) <=> (?[B]: (m1_subset_1(B, A) & (A = k6_domain_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tex_2)).
% 2.26/1.30  tff(f_70, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 2.26/1.30  tff(f_29, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.26/1.30  tff(f_45, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.26/1.30  tff(f_41, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_xboole_1)).
% 2.26/1.30  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.26/1.30  tff(f_63, axiom, (![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~((B = k1_tarski(A)) & (C = k1_tarski(A)))) & ~((B = k1_xboole_0) & (C = k1_tarski(A)))) & ~((B = k1_tarski(A)) & (C = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_zfmisc_1)).
% 2.26/1.30  tff(c_44, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.26/1.30  tff(c_38, plain, ('#skF_2'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.26/1.30  tff(c_42, plain, (v1_zfmisc_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.26/1.30  tff(c_36, plain, (![A_14]: (m1_subset_1('#skF_1'(A_14), A_14) | ~v1_zfmisc_1(A_14) | v1_xboole_0(A_14))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.26/1.30  tff(c_118, plain, (![A_41, B_42]: (k6_domain_1(A_41, B_42)=k1_tarski(B_42) | ~m1_subset_1(B_42, A_41) | v1_xboole_0(A_41))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.26/1.30  tff(c_142, plain, (![A_53]: (k6_domain_1(A_53, '#skF_1'(A_53))=k1_tarski('#skF_1'(A_53)) | ~v1_zfmisc_1(A_53) | v1_xboole_0(A_53))), inference(resolution, [status(thm)], [c_36, c_118])).
% 2.26/1.30  tff(c_34, plain, (![A_14]: (k6_domain_1(A_14, '#skF_1'(A_14))=A_14 | ~v1_zfmisc_1(A_14) | v1_xboole_0(A_14))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.26/1.30  tff(c_148, plain, (![A_53]: (k1_tarski('#skF_1'(A_53))=A_53 | ~v1_zfmisc_1(A_53) | v1_xboole_0(A_53) | ~v1_zfmisc_1(A_53) | v1_xboole_0(A_53))), inference(superposition, [status(thm), theory('equality')], [c_142, c_34])).
% 2.26/1.30  tff(c_157, plain, (![A_54]: (k1_tarski('#skF_1'(A_54))=A_54 | ~v1_zfmisc_1(A_54) | v1_xboole_0(A_54) | ~v1_zfmisc_1(A_54) | v1_xboole_0(A_54))), inference(superposition, [status(thm), theory('equality')], [c_142, c_34])).
% 2.26/1.30  tff(c_46, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.26/1.30  tff(c_40, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.26/1.30  tff(c_47, plain, (![A_19, B_20]: (k4_xboole_0(A_19, B_20)=k1_xboole_0 | ~r1_tarski(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.26/1.30  tff(c_51, plain, (k4_xboole_0('#skF_2', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_40, c_47])).
% 2.26/1.30  tff(c_12, plain, (![A_7, B_8]: (r1_xboole_0(A_7, B_8) | k4_xboole_0(A_7, B_8)!=A_7)), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.26/1.30  tff(c_81, plain, (![B_30, A_31]: (~r1_xboole_0(B_30, A_31) | ~r1_tarski(B_30, A_31) | v1_xboole_0(B_30))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.26/1.30  tff(c_101, plain, (![A_35, B_36]: (~r1_tarski(A_35, B_36) | v1_xboole_0(A_35) | k4_xboole_0(A_35, B_36)!=A_35)), inference(resolution, [status(thm)], [c_12, c_81])).
% 2.26/1.30  tff(c_107, plain, (v1_xboole_0('#skF_2') | k4_xboole_0('#skF_2', '#skF_3')!='#skF_2'), inference(resolution, [status(thm)], [c_40, c_101])).
% 2.26/1.30  tff(c_110, plain, (v1_xboole_0('#skF_2') | k1_xboole_0!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_51, c_107])).
% 2.26/1.30  tff(c_111, plain, (k1_xboole_0!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_46, c_110])).
% 2.26/1.30  tff(c_67, plain, (![A_27, B_28]: (k2_xboole_0(A_27, B_28)=B_28 | ~r1_tarski(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.26/1.30  tff(c_75, plain, (k2_xboole_0('#skF_2', '#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_40, c_67])).
% 2.26/1.30  tff(c_112, plain, (![B_37, A_38, C_39]: (k1_xboole_0=B_37 | k1_tarski(A_38)=B_37 | k2_xboole_0(B_37, C_39)!=k1_tarski(A_38))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.26/1.30  tff(c_115, plain, (![A_38]: (k1_xboole_0='#skF_2' | k1_tarski(A_38)='#skF_2' | k1_tarski(A_38)!='#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_75, c_112])).
% 2.26/1.30  tff(c_116, plain, (![A_38]: (k1_tarski(A_38)='#skF_2' | k1_tarski(A_38)!='#skF_3')), inference(negUnitSimplification, [status(thm)], [c_111, c_115])).
% 2.26/1.30  tff(c_179, plain, (![A_55]: (k1_tarski('#skF_1'(A_55))='#skF_2' | A_55!='#skF_3' | ~v1_zfmisc_1(A_55) | v1_xboole_0(A_55) | ~v1_zfmisc_1(A_55) | v1_xboole_0(A_55))), inference(superposition, [status(thm), theory('equality')], [c_157, c_116])).
% 2.26/1.30  tff(c_328, plain, (![A_91]: (A_91='#skF_2' | A_91!='#skF_3' | ~v1_zfmisc_1(A_91) | v1_xboole_0(A_91) | ~v1_zfmisc_1(A_91) | v1_xboole_0(A_91) | ~v1_zfmisc_1(A_91) | v1_xboole_0(A_91) | ~v1_zfmisc_1(A_91) | v1_xboole_0(A_91))), inference(superposition, [status(thm), theory('equality')], [c_148, c_179])).
% 2.26/1.30  tff(c_330, plain, ('#skF_2'='#skF_3' | ~v1_zfmisc_1('#skF_3') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_42, c_328])).
% 2.26/1.30  tff(c_333, plain, ('#skF_2'='#skF_3' | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_330])).
% 2.26/1.30  tff(c_335, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_38, c_333])).
% 2.26/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.26/1.30  
% 2.26/1.30  Inference rules
% 2.26/1.30  ----------------------
% 2.26/1.30  #Ref     : 5
% 2.26/1.30  #Sup     : 63
% 2.26/1.30  #Fact    : 0
% 2.26/1.30  #Define  : 0
% 2.26/1.30  #Split   : 1
% 2.26/1.30  #Chain   : 0
% 2.26/1.30  #Close   : 0
% 2.26/1.30  
% 2.26/1.30  Ordering : KBO
% 2.26/1.30  
% 2.26/1.30  Simplification rules
% 2.26/1.30  ----------------------
% 2.26/1.30  #Subsume      : 22
% 2.26/1.30  #Demod        : 19
% 2.26/1.30  #Tautology    : 26
% 2.26/1.30  #SimpNegUnit  : 9
% 2.26/1.30  #BackRed      : 11
% 2.26/1.30  
% 2.26/1.30  #Partial instantiations: 0
% 2.26/1.30  #Strategies tried      : 1
% 2.26/1.30  
% 2.26/1.30  Timing (in seconds)
% 2.26/1.30  ----------------------
% 2.26/1.30  Preprocessing        : 0.30
% 2.26/1.30  Parsing              : 0.16
% 2.26/1.30  CNF conversion       : 0.02
% 2.26/1.30  Main loop            : 0.24
% 2.26/1.30  Inferencing          : 0.09
% 2.26/1.30  Reduction            : 0.06
% 2.26/1.30  Demodulation         : 0.04
% 2.26/1.30  BG Simplification    : 0.02
% 2.26/1.30  Subsumption          : 0.06
% 2.26/1.30  Abstraction          : 0.01
% 2.26/1.30  MUC search           : 0.00
% 2.26/1.30  Cooper               : 0.00
% 2.26/1.30  Total                : 0.57
% 2.26/1.30  Index Insertion      : 0.00
% 2.26/1.30  Index Deletion       : 0.00
% 2.26/1.30  Index Matching       : 0.00
% 2.26/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
