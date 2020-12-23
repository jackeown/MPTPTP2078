%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:18 EST 2020

% Result     : Theorem 2.76s
% Output     : CNFRefutation 3.06s
% Verified   : 
% Statistics : Number of formulae       :   60 (  77 expanded)
%              Number of leaves         :   30 (  40 expanded)
%              Depth                    :   10
%              Number of atoms          :   83 ( 133 expanded)
%              Number of equality atoms :   39 (  52 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k6_domain_1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_4 > #skF_3 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_98,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ( ~ v1_xboole_0(B)
              & v1_zfmisc_1(B) )
           => ( r1_tarski(A,B)
             => A = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).

tff(f_84,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ( v1_zfmisc_1(A)
      <=> ? [B] :
            ( m1_subset_1(B,A)
            & A = k6_domain_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tex_2)).

tff(f_74,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_50,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k2_xboole_0(k1_tarski(A),B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l22_zfmisc_1)).

tff(f_67,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_44,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_42,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_46,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ~ ( k1_tarski(A) = k2_xboole_0(B,C)
        & B != C
        & B != k1_xboole_0
        & C != k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_zfmisc_1)).

tff(c_42,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_40,plain,(
    v1_zfmisc_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_34,plain,(
    ! [A_26] :
      ( m1_subset_1('#skF_3'(A_26),A_26)
      | ~ v1_zfmisc_1(A_26)
      | v1_xboole_0(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_428,plain,(
    ! [A_82,B_83] :
      ( k6_domain_1(A_82,B_83) = k1_tarski(B_83)
      | ~ m1_subset_1(B_83,A_82)
      | v1_xboole_0(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_569,plain,(
    ! [A_107] :
      ( k6_domain_1(A_107,'#skF_3'(A_107)) = k1_tarski('#skF_3'(A_107))
      | ~ v1_zfmisc_1(A_107)
      | v1_xboole_0(A_107) ) ),
    inference(resolution,[status(thm)],[c_34,c_428])).

tff(c_32,plain,(
    ! [A_26] :
      ( k6_domain_1(A_26,'#skF_3'(A_26)) = A_26
      | ~ v1_zfmisc_1(A_26)
      | v1_xboole_0(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_872,plain,(
    ! [A_142] :
      ( k1_tarski('#skF_3'(A_142)) = A_142
      | ~ v1_zfmisc_1(A_142)
      | v1_xboole_0(A_142)
      | ~ v1_zfmisc_1(A_142)
      | v1_xboole_0(A_142) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_569,c_32])).

tff(c_36,plain,(
    '#skF_5' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_89,plain,(
    ! [A_44,B_45] :
      ( k2_xboole_0(k1_tarski(A_44),B_45) = B_45
      | ~ r2_hidden(A_44,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_26,plain,(
    ! [A_22,B_23] : k2_xboole_0(k1_tarski(A_22),B_23) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_177,plain,(
    ! [B_55,A_56] :
      ( k1_xboole_0 != B_55
      | ~ r2_hidden(A_56,B_55) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_89,c_26])).

tff(c_189,plain,(
    ! [A_58] :
      ( k1_xboole_0 != A_58
      | v1_xboole_0(A_58) ) ),
    inference(resolution,[status(thm)],[c_4,c_177])).

tff(c_196,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(resolution,[status(thm)],[c_189,c_42])).

tff(c_44,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_197,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(resolution,[status(thm)],[c_189,c_44])).

tff(c_16,plain,(
    ! [A_12] : k2_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_38,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_67,plain,(
    ! [A_40,B_41] :
      ( k4_xboole_0(A_40,B_41) = k1_xboole_0
      | ~ r1_tarski(A_40,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_75,plain,(
    k4_xboole_0('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_38,c_67])).

tff(c_126,plain,(
    ! [A_49,B_50] : k2_xboole_0(A_49,k4_xboole_0(B_50,A_49)) = k2_xboole_0(A_49,B_50) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_147,plain,(
    k2_xboole_0('#skF_5',k1_xboole_0) = k2_xboole_0('#skF_5','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_75,c_126])).

tff(c_150,plain,(
    k2_xboole_0('#skF_5','#skF_4') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_147])).

tff(c_464,plain,(
    ! [C_86,B_87,A_88] :
      ( k1_xboole_0 = C_86
      | k1_xboole_0 = B_87
      | C_86 = B_87
      | k2_xboole_0(B_87,C_86) != k1_tarski(A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_473,plain,(
    ! [A_88] :
      ( k1_xboole_0 = '#skF_4'
      | k1_xboole_0 = '#skF_5'
      | '#skF_5' = '#skF_4'
      | k1_tarski(A_88) != '#skF_5' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_150,c_464])).

tff(c_481,plain,(
    ! [A_88] : k1_tarski(A_88) != '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_196,c_197,c_473])).

tff(c_910,plain,(
    ! [A_143] :
      ( A_143 != '#skF_5'
      | ~ v1_zfmisc_1(A_143)
      | v1_xboole_0(A_143)
      | ~ v1_zfmisc_1(A_143)
      | v1_xboole_0(A_143) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_872,c_481])).

tff(c_912,plain,
    ( ~ v1_zfmisc_1('#skF_5')
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_40,c_910])).

tff(c_915,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_912])).

tff(c_917,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_915])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:21:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.76/1.51  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.76/1.52  
% 2.76/1.52  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.76/1.52  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k6_domain_1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_4 > #skF_3 > #skF_2
% 2.76/1.52  
% 2.76/1.52  %Foreground sorts:
% 2.76/1.52  
% 2.76/1.52  
% 2.76/1.52  %Background operators:
% 2.76/1.52  
% 2.76/1.52  
% 2.76/1.52  %Foreground operators:
% 2.76/1.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.76/1.52  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.76/1.52  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.76/1.52  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.76/1.52  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.76/1.52  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.76/1.52  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.76/1.52  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.76/1.52  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.76/1.52  tff('#skF_5', type, '#skF_5': $i).
% 2.76/1.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.76/1.52  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.76/1.52  tff('#skF_4', type, '#skF_4': $i).
% 2.76/1.52  tff('#skF_3', type, '#skF_3': $i > $i).
% 2.76/1.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.76/1.52  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.76/1.52  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 2.76/1.52  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.76/1.52  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.76/1.52  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.76/1.52  
% 3.06/1.53  tff(f_98, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tex_2)).
% 3.06/1.53  tff(f_84, axiom, (![A]: (~v1_xboole_0(A) => (v1_zfmisc_1(A) <=> (?[B]: (m1_subset_1(B, A) & (A = k6_domain_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tex_2)).
% 3.06/1.53  tff(f_74, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 3.06/1.53  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.06/1.53  tff(f_50, axiom, (![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l22_zfmisc_1)).
% 3.06/1.53  tff(f_67, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 3.06/1.53  tff(f_44, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 3.06/1.53  tff(f_42, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 3.06/1.53  tff(f_46, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 3.06/1.53  tff(f_64, axiom, (![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~(B = C)) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_zfmisc_1)).
% 3.06/1.53  tff(c_42, plain, (~v1_xboole_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.06/1.53  tff(c_40, plain, (v1_zfmisc_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.06/1.53  tff(c_34, plain, (![A_26]: (m1_subset_1('#skF_3'(A_26), A_26) | ~v1_zfmisc_1(A_26) | v1_xboole_0(A_26))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.06/1.53  tff(c_428, plain, (![A_82, B_83]: (k6_domain_1(A_82, B_83)=k1_tarski(B_83) | ~m1_subset_1(B_83, A_82) | v1_xboole_0(A_82))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.06/1.53  tff(c_569, plain, (![A_107]: (k6_domain_1(A_107, '#skF_3'(A_107))=k1_tarski('#skF_3'(A_107)) | ~v1_zfmisc_1(A_107) | v1_xboole_0(A_107))), inference(resolution, [status(thm)], [c_34, c_428])).
% 3.06/1.53  tff(c_32, plain, (![A_26]: (k6_domain_1(A_26, '#skF_3'(A_26))=A_26 | ~v1_zfmisc_1(A_26) | v1_xboole_0(A_26))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.06/1.53  tff(c_872, plain, (![A_142]: (k1_tarski('#skF_3'(A_142))=A_142 | ~v1_zfmisc_1(A_142) | v1_xboole_0(A_142) | ~v1_zfmisc_1(A_142) | v1_xboole_0(A_142))), inference(superposition, [status(thm), theory('equality')], [c_569, c_32])).
% 3.06/1.53  tff(c_36, plain, ('#skF_5'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.06/1.53  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.06/1.53  tff(c_89, plain, (![A_44, B_45]: (k2_xboole_0(k1_tarski(A_44), B_45)=B_45 | ~r2_hidden(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.06/1.53  tff(c_26, plain, (![A_22, B_23]: (k2_xboole_0(k1_tarski(A_22), B_23)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.06/1.53  tff(c_177, plain, (![B_55, A_56]: (k1_xboole_0!=B_55 | ~r2_hidden(A_56, B_55))), inference(superposition, [status(thm), theory('equality')], [c_89, c_26])).
% 3.06/1.53  tff(c_189, plain, (![A_58]: (k1_xboole_0!=A_58 | v1_xboole_0(A_58))), inference(resolution, [status(thm)], [c_4, c_177])).
% 3.06/1.53  tff(c_196, plain, (k1_xboole_0!='#skF_5'), inference(resolution, [status(thm)], [c_189, c_42])).
% 3.06/1.53  tff(c_44, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.06/1.53  tff(c_197, plain, (k1_xboole_0!='#skF_4'), inference(resolution, [status(thm)], [c_189, c_44])).
% 3.06/1.53  tff(c_16, plain, (![A_12]: (k2_xboole_0(A_12, k1_xboole_0)=A_12)), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.06/1.53  tff(c_38, plain, (r1_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.06/1.53  tff(c_67, plain, (![A_40, B_41]: (k4_xboole_0(A_40, B_41)=k1_xboole_0 | ~r1_tarski(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.06/1.53  tff(c_75, plain, (k4_xboole_0('#skF_4', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_38, c_67])).
% 3.06/1.53  tff(c_126, plain, (![A_49, B_50]: (k2_xboole_0(A_49, k4_xboole_0(B_50, A_49))=k2_xboole_0(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.06/1.53  tff(c_147, plain, (k2_xboole_0('#skF_5', k1_xboole_0)=k2_xboole_0('#skF_5', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_75, c_126])).
% 3.06/1.53  tff(c_150, plain, (k2_xboole_0('#skF_5', '#skF_4')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_16, c_147])).
% 3.06/1.53  tff(c_464, plain, (![C_86, B_87, A_88]: (k1_xboole_0=C_86 | k1_xboole_0=B_87 | C_86=B_87 | k2_xboole_0(B_87, C_86)!=k1_tarski(A_88))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.06/1.53  tff(c_473, plain, (![A_88]: (k1_xboole_0='#skF_4' | k1_xboole_0='#skF_5' | '#skF_5'='#skF_4' | k1_tarski(A_88)!='#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_150, c_464])).
% 3.06/1.53  tff(c_481, plain, (![A_88]: (k1_tarski(A_88)!='#skF_5')), inference(negUnitSimplification, [status(thm)], [c_36, c_196, c_197, c_473])).
% 3.06/1.53  tff(c_910, plain, (![A_143]: (A_143!='#skF_5' | ~v1_zfmisc_1(A_143) | v1_xboole_0(A_143) | ~v1_zfmisc_1(A_143) | v1_xboole_0(A_143))), inference(superposition, [status(thm), theory('equality')], [c_872, c_481])).
% 3.06/1.53  tff(c_912, plain, (~v1_zfmisc_1('#skF_5') | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_40, c_910])).
% 3.06/1.53  tff(c_915, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_912])).
% 3.06/1.53  tff(c_917, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_915])).
% 3.06/1.53  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.06/1.53  
% 3.06/1.53  Inference rules
% 3.06/1.53  ----------------------
% 3.06/1.53  #Ref     : 1
% 3.06/1.53  #Sup     : 215
% 3.06/1.53  #Fact    : 0
% 3.06/1.53  #Define  : 0
% 3.06/1.53  #Split   : 0
% 3.06/1.53  #Chain   : 0
% 3.06/1.53  #Close   : 0
% 3.06/1.53  
% 3.06/1.53  Ordering : KBO
% 3.06/1.53  
% 3.06/1.53  Simplification rules
% 3.06/1.53  ----------------------
% 3.06/1.53  #Subsume      : 76
% 3.06/1.53  #Demod        : 17
% 3.06/1.53  #Tautology    : 65
% 3.06/1.53  #SimpNegUnit  : 12
% 3.06/1.53  #BackRed      : 0
% 3.06/1.53  
% 3.06/1.53  #Partial instantiations: 0
% 3.06/1.53  #Strategies tried      : 1
% 3.06/1.53  
% 3.06/1.53  Timing (in seconds)
% 3.06/1.53  ----------------------
% 3.06/1.54  Preprocessing        : 0.35
% 3.06/1.54  Parsing              : 0.18
% 3.06/1.54  CNF conversion       : 0.03
% 3.06/1.54  Main loop            : 0.37
% 3.06/1.54  Inferencing          : 0.15
% 3.06/1.54  Reduction            : 0.10
% 3.06/1.54  Demodulation         : 0.06
% 3.06/1.54  BG Simplification    : 0.02
% 3.06/1.54  Subsumption          : 0.07
% 3.06/1.54  Abstraction          : 0.02
% 3.06/1.54  MUC search           : 0.00
% 3.06/1.54  Cooper               : 0.00
% 3.06/1.54  Total                : 0.75
% 3.06/1.54  Index Insertion      : 0.00
% 3.06/1.54  Index Deletion       : 0.00
% 3.06/1.54  Index Matching       : 0.00
% 3.06/1.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------
