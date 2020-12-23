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
% DateTime   : Thu Dec  3 10:16:49 EST 2020

% Result     : Theorem 2.01s
% Output     : CNFRefutation 2.12s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 119 expanded)
%              Number of leaves         :   22 (  48 expanded)
%              Depth                    :    9
%              Number of atoms          :   87 ( 298 expanded)
%              Number of equality atoms :   22 (  94 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v1_partfun1 > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k2_zfmisc_1 > #nlpp > k6_partfun1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_partfun1,type,(
    k6_partfun1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_79,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ( v1_funct_1(C)
            & v1_funct_2(C,A,B)
            & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
         => ( ( B = k1_xboole_0
              & A != k1_xboole_0 )
            | v1_partfun1(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_funct_2)).

tff(f_43,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_61,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(c_24,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_37,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_24])).

tff(c_32,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_88,plain,(
    ! [C_20,B_21,A_22] :
      ( v1_xboole_0(C_20)
      | ~ m1_subset_1(C_20,k1_zfmisc_1(k2_zfmisc_1(B_21,A_22)))
      | ~ v1_xboole_0(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_102,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_88])).

tff(c_105,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_102])).

tff(c_22,plain,(
    ~ v1_partfun1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_34,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_28,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_111,plain,(
    ! [C_24,A_25,B_26] :
      ( v1_partfun1(C_24,A_25)
      | ~ v1_funct_2(C_24,A_25,B_26)
      | ~ v1_funct_1(C_24)
      | ~ m1_subset_1(C_24,k1_zfmisc_1(k2_zfmisc_1(A_25,B_26)))
      | v1_xboole_0(B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_117,plain,
    ( v1_partfun1('#skF_3','#skF_1')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_111])).

tff(c_128,plain,
    ( v1_partfun1('#skF_3','#skF_1')
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_28,c_117])).

tff(c_130,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_105,c_22,c_128])).

tff(c_132,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_102])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_139,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_132,c_4])).

tff(c_143,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_37,c_139])).

tff(c_144,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_146,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_144,c_2])).

tff(c_20,plain,(
    ! [A_12] : m1_subset_1(k6_partfun1(A_12),k1_zfmisc_1(k2_zfmisc_1(A_12,A_12))) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_212,plain,(
    ! [C_34,B_35,A_36] :
      ( v1_xboole_0(C_34)
      | ~ m1_subset_1(C_34,k1_zfmisc_1(k2_zfmisc_1(B_35,A_36)))
      | ~ v1_xboole_0(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_225,plain,(
    ! [A_37] :
      ( v1_xboole_0(k6_partfun1(A_37))
      | ~ v1_xboole_0(A_37) ) ),
    inference(resolution,[status(thm)],[c_20,c_212])).

tff(c_183,plain,(
    ! [A_1] :
      ( A_1 = '#skF_1'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_144,c_4])).

tff(c_230,plain,(
    ! [A_38] :
      ( k6_partfun1(A_38) = '#skF_1'
      | ~ v1_xboole_0(A_38) ) ),
    inference(resolution,[status(thm)],[c_225,c_183])).

tff(c_238,plain,(
    k6_partfun1('#skF_1') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_146,c_230])).

tff(c_18,plain,(
    ! [A_12] : v1_partfun1(k6_partfun1(A_12),A_12) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_249,plain,(
    v1_partfun1('#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_238,c_18])).

tff(c_10,plain,(
    ! [B_3] : k2_zfmisc_1(k1_xboole_0,B_3) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_156,plain,(
    ! [B_3] : k2_zfmisc_1('#skF_1',B_3) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_144,c_144,c_10])).

tff(c_145,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_151,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_144,c_145])).

tff(c_182,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_156,c_151,c_32])).

tff(c_8,plain,(
    ! [A_2] : k2_zfmisc_1(A_2,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_166,plain,(
    ! [A_2] : k2_zfmisc_1(A_2,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_144,c_144,c_8])).

tff(c_218,plain,(
    ! [C_34] :
      ( v1_xboole_0(C_34)
      | ~ m1_subset_1(C_34,k1_zfmisc_1('#skF_1'))
      | ~ v1_xboole_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_166,c_212])).

tff(c_270,plain,(
    ! [C_42] :
      ( v1_xboole_0(C_42)
      | ~ m1_subset_1(C_42,k1_zfmisc_1('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_218])).

tff(c_279,plain,(
    v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_182,c_270])).

tff(c_287,plain,(
    '#skF_3' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_279,c_183])).

tff(c_291,plain,(
    ~ v1_partfun1('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_287,c_22])).

tff(c_297,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_249,c_291])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:57:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.01/1.21  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.01/1.22  
% 2.01/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.01/1.22  %$ v1_funct_2 > v1_partfun1 > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k2_zfmisc_1 > #nlpp > k6_partfun1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.01/1.22  
% 2.01/1.22  %Foreground sorts:
% 2.01/1.22  
% 2.01/1.22  
% 2.01/1.22  %Background operators:
% 2.01/1.22  
% 2.01/1.22  
% 2.01/1.22  %Foreground operators:
% 2.01/1.22  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.01/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.01/1.22  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.01/1.22  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.01/1.22  tff('#skF_2', type, '#skF_2': $i).
% 2.01/1.22  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 2.01/1.22  tff('#skF_3', type, '#skF_3': $i).
% 2.01/1.22  tff('#skF_1', type, '#skF_1': $i).
% 2.01/1.22  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.01/1.22  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 2.01/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.01/1.22  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.01/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.01/1.22  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.01/1.22  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.01/1.22  
% 2.12/1.24  tff(f_79, negated_conjecture, ~(![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | v1_partfun1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t132_funct_2)).
% 2.12/1.24  tff(f_43, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => v1_xboole_0(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc4_relset_1)).
% 2.12/1.24  tff(f_57, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc5_funct_2)).
% 2.12/1.24  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.12/1.24  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.12/1.24  tff(f_61, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 2.12/1.24  tff(f_36, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.12/1.24  tff(c_24, plain, (k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.12/1.24  tff(c_37, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_24])).
% 2.12/1.24  tff(c_32, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.12/1.24  tff(c_88, plain, (![C_20, B_21, A_22]: (v1_xboole_0(C_20) | ~m1_subset_1(C_20, k1_zfmisc_1(k2_zfmisc_1(B_21, A_22))) | ~v1_xboole_0(A_22))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.12/1.24  tff(c_102, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_32, c_88])).
% 2.12/1.24  tff(c_105, plain, (~v1_xboole_0('#skF_2')), inference(splitLeft, [status(thm)], [c_102])).
% 2.12/1.24  tff(c_22, plain, (~v1_partfun1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.12/1.24  tff(c_34, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.12/1.24  tff(c_28, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.12/1.24  tff(c_111, plain, (![C_24, A_25, B_26]: (v1_partfun1(C_24, A_25) | ~v1_funct_2(C_24, A_25, B_26) | ~v1_funct_1(C_24) | ~m1_subset_1(C_24, k1_zfmisc_1(k2_zfmisc_1(A_25, B_26))) | v1_xboole_0(B_26))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.12/1.24  tff(c_117, plain, (v1_partfun1('#skF_3', '#skF_1') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_32, c_111])).
% 2.12/1.24  tff(c_128, plain, (v1_partfun1('#skF_3', '#skF_1') | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_28, c_117])).
% 2.12/1.24  tff(c_130, plain, $false, inference(negUnitSimplification, [status(thm)], [c_105, c_22, c_128])).
% 2.12/1.24  tff(c_132, plain, (v1_xboole_0('#skF_2')), inference(splitRight, [status(thm)], [c_102])).
% 2.12/1.24  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.12/1.24  tff(c_139, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_132, c_4])).
% 2.12/1.24  tff(c_143, plain, $false, inference(negUnitSimplification, [status(thm)], [c_37, c_139])).
% 2.12/1.24  tff(c_144, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_24])).
% 2.12/1.24  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.12/1.24  tff(c_146, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_144, c_2])).
% 2.12/1.24  tff(c_20, plain, (![A_12]: (m1_subset_1(k6_partfun1(A_12), k1_zfmisc_1(k2_zfmisc_1(A_12, A_12))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.12/1.24  tff(c_212, plain, (![C_34, B_35, A_36]: (v1_xboole_0(C_34) | ~m1_subset_1(C_34, k1_zfmisc_1(k2_zfmisc_1(B_35, A_36))) | ~v1_xboole_0(A_36))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.12/1.24  tff(c_225, plain, (![A_37]: (v1_xboole_0(k6_partfun1(A_37)) | ~v1_xboole_0(A_37))), inference(resolution, [status(thm)], [c_20, c_212])).
% 2.12/1.24  tff(c_183, plain, (![A_1]: (A_1='#skF_1' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_144, c_4])).
% 2.12/1.24  tff(c_230, plain, (![A_38]: (k6_partfun1(A_38)='#skF_1' | ~v1_xboole_0(A_38))), inference(resolution, [status(thm)], [c_225, c_183])).
% 2.12/1.24  tff(c_238, plain, (k6_partfun1('#skF_1')='#skF_1'), inference(resolution, [status(thm)], [c_146, c_230])).
% 2.12/1.24  tff(c_18, plain, (![A_12]: (v1_partfun1(k6_partfun1(A_12), A_12))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.12/1.24  tff(c_249, plain, (v1_partfun1('#skF_1', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_238, c_18])).
% 2.12/1.24  tff(c_10, plain, (![B_3]: (k2_zfmisc_1(k1_xboole_0, B_3)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.12/1.24  tff(c_156, plain, (![B_3]: (k2_zfmisc_1('#skF_1', B_3)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_144, c_144, c_10])).
% 2.12/1.24  tff(c_145, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_24])).
% 2.12/1.24  tff(c_151, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_144, c_145])).
% 2.12/1.24  tff(c_182, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_156, c_151, c_32])).
% 2.12/1.24  tff(c_8, plain, (![A_2]: (k2_zfmisc_1(A_2, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.12/1.24  tff(c_166, plain, (![A_2]: (k2_zfmisc_1(A_2, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_144, c_144, c_8])).
% 2.12/1.24  tff(c_218, plain, (![C_34]: (v1_xboole_0(C_34) | ~m1_subset_1(C_34, k1_zfmisc_1('#skF_1')) | ~v1_xboole_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_166, c_212])).
% 2.12/1.24  tff(c_270, plain, (![C_42]: (v1_xboole_0(C_42) | ~m1_subset_1(C_42, k1_zfmisc_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_146, c_218])).
% 2.12/1.24  tff(c_279, plain, (v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_182, c_270])).
% 2.12/1.24  tff(c_287, plain, ('#skF_3'='#skF_1'), inference(resolution, [status(thm)], [c_279, c_183])).
% 2.12/1.24  tff(c_291, plain, (~v1_partfun1('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_287, c_22])).
% 2.12/1.24  tff(c_297, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_249, c_291])).
% 2.12/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.12/1.24  
% 2.12/1.24  Inference rules
% 2.12/1.24  ----------------------
% 2.12/1.24  #Ref     : 0
% 2.12/1.24  #Sup     : 55
% 2.12/1.24  #Fact    : 0
% 2.12/1.24  #Define  : 0
% 2.12/1.24  #Split   : 2
% 2.12/1.24  #Chain   : 0
% 2.12/1.24  #Close   : 0
% 2.12/1.24  
% 2.12/1.24  Ordering : KBO
% 2.12/1.24  
% 2.12/1.24  Simplification rules
% 2.12/1.24  ----------------------
% 2.12/1.24  #Subsume      : 1
% 2.12/1.24  #Demod        : 38
% 2.12/1.24  #Tautology    : 37
% 2.12/1.24  #SimpNegUnit  : 2
% 2.12/1.24  #BackRed      : 7
% 2.12/1.24  
% 2.12/1.24  #Partial instantiations: 0
% 2.12/1.24  #Strategies tried      : 1
% 2.12/1.24  
% 2.12/1.24  Timing (in seconds)
% 2.12/1.24  ----------------------
% 2.12/1.24  Preprocessing        : 0.30
% 2.12/1.24  Parsing              : 0.16
% 2.12/1.24  CNF conversion       : 0.02
% 2.12/1.24  Main loop            : 0.18
% 2.12/1.24  Inferencing          : 0.06
% 2.12/1.24  Reduction            : 0.06
% 2.12/1.24  Demodulation         : 0.04
% 2.12/1.24  BG Simplification    : 0.01
% 2.12/1.24  Subsumption          : 0.03
% 2.12/1.24  Abstraction          : 0.01
% 2.12/1.24  MUC search           : 0.00
% 2.12/1.24  Cooper               : 0.00
% 2.12/1.24  Total                : 0.51
% 2.12/1.24  Index Insertion      : 0.00
% 2.12/1.24  Index Deletion       : 0.00
% 2.12/1.24  Index Matching       : 0.00
% 2.12/1.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
