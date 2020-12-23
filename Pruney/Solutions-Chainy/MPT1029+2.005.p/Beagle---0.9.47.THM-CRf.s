%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:48 EST 2020

% Result     : Theorem 2.00s
% Output     : CNFRefutation 2.00s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 107 expanded)
%              Number of leaves         :   22 (  44 expanded)
%              Depth                    :    9
%              Number of atoms          :   77 ( 259 expanded)
%              Number of equality atoms :   21 (  89 expanded)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t132_funct_2)).

tff(f_57,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_36,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_43,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_61,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(c_24,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_37,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_24])).

tff(c_22,plain,(
    ~ v1_partfun1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_34,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_28,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_32,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_142,plain,(
    ! [C_22,A_23,B_24] :
      ( v1_partfun1(C_22,A_23)
      | ~ v1_funct_2(C_22,A_23,B_24)
      | ~ v1_funct_1(C_22)
      | ~ m1_subset_1(C_22,k1_zfmisc_1(k2_zfmisc_1(A_23,B_24)))
      | v1_xboole_0(B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_148,plain,
    ( v1_partfun1('#skF_3','#skF_1')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_142])).

tff(c_159,plain,
    ( v1_partfun1('#skF_3','#skF_1')
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_28,c_148])).

tff(c_160,plain,(
    v1_xboole_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_159])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_164,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_160,c_4])).

tff(c_168,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_37,c_164])).

tff(c_169,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_171,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_169,c_2])).

tff(c_10,plain,(
    ! [B_3] : k2_zfmisc_1(k1_xboole_0,B_3) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_182,plain,(
    ! [B_3] : k2_zfmisc_1('#skF_1',B_3) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_169,c_169,c_10])).

tff(c_170,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_176,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_169,c_170])).

tff(c_214,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_182,c_176,c_32])).

tff(c_237,plain,(
    ! [B_32,A_33] :
      ( v1_xboole_0(B_32)
      | ~ m1_subset_1(B_32,k1_zfmisc_1(A_33))
      | ~ v1_xboole_0(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_246,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_214,c_237])).

tff(c_253,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_171,c_246])).

tff(c_207,plain,(
    ! [A_1] :
      ( A_1 = '#skF_1'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_169,c_4])).

tff(c_257,plain,(
    '#skF_3' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_253,c_207])).

tff(c_261,plain,(
    ~ v1_partfun1('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_257,c_22])).

tff(c_8,plain,(
    ! [A_2] : k2_zfmisc_1(A_2,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_191,plain,(
    ! [A_2] : k2_zfmisc_1(A_2,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_169,c_169,c_8])).

tff(c_215,plain,(
    ! [A_29] : m1_subset_1(k6_partfun1(A_29),k1_zfmisc_1(k2_zfmisc_1(A_29,A_29))) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_219,plain,(
    m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_191,c_215])).

tff(c_240,plain,
    ( v1_xboole_0(k6_partfun1('#skF_1'))
    | ~ v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_219,c_237])).

tff(c_249,plain,(
    v1_xboole_0(k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_171,c_240])).

tff(c_271,plain,(
    k6_partfun1('#skF_1') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_249,c_207])).

tff(c_18,plain,(
    ! [A_11] : v1_partfun1(k6_partfun1(A_11),A_11) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_294,plain,(
    v1_partfun1('#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_271,c_18])).

tff(c_299,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_261,c_294])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:41:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.00/1.28  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.00/1.28  
% 2.00/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.00/1.28  %$ v1_funct_2 > v1_partfun1 > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k2_zfmisc_1 > #nlpp > k6_partfun1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.00/1.28  
% 2.00/1.28  %Foreground sorts:
% 2.00/1.28  
% 2.00/1.28  
% 2.00/1.28  %Background operators:
% 2.00/1.28  
% 2.00/1.28  
% 2.00/1.28  %Foreground operators:
% 2.00/1.28  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.00/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.00/1.28  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.00/1.28  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.00/1.28  tff('#skF_2', type, '#skF_2': $i).
% 2.00/1.28  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 2.00/1.28  tff('#skF_3', type, '#skF_3': $i).
% 2.00/1.28  tff('#skF_1', type, '#skF_1': $i).
% 2.00/1.28  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.00/1.28  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 2.00/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.00/1.28  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.00/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.00/1.28  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.00/1.28  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.00/1.28  
% 2.00/1.30  tff(f_79, negated_conjecture, ~(![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | v1_partfun1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t132_funct_2)).
% 2.00/1.30  tff(f_57, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc5_funct_2)).
% 2.00/1.30  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.00/1.30  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.00/1.30  tff(f_36, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.00/1.30  tff(f_43, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_subset_1)).
% 2.00/1.30  tff(f_61, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 2.00/1.30  tff(c_24, plain, (k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.00/1.30  tff(c_37, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_24])).
% 2.00/1.30  tff(c_22, plain, (~v1_partfun1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.00/1.30  tff(c_34, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.00/1.30  tff(c_28, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.00/1.30  tff(c_32, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.00/1.30  tff(c_142, plain, (![C_22, A_23, B_24]: (v1_partfun1(C_22, A_23) | ~v1_funct_2(C_22, A_23, B_24) | ~v1_funct_1(C_22) | ~m1_subset_1(C_22, k1_zfmisc_1(k2_zfmisc_1(A_23, B_24))) | v1_xboole_0(B_24))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.00/1.30  tff(c_148, plain, (v1_partfun1('#skF_3', '#skF_1') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_32, c_142])).
% 2.00/1.30  tff(c_159, plain, (v1_partfun1('#skF_3', '#skF_1') | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_28, c_148])).
% 2.00/1.30  tff(c_160, plain, (v1_xboole_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_22, c_159])).
% 2.00/1.30  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.00/1.30  tff(c_164, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_160, c_4])).
% 2.00/1.30  tff(c_168, plain, $false, inference(negUnitSimplification, [status(thm)], [c_37, c_164])).
% 2.00/1.30  tff(c_169, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_24])).
% 2.00/1.30  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.00/1.30  tff(c_171, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_169, c_2])).
% 2.00/1.30  tff(c_10, plain, (![B_3]: (k2_zfmisc_1(k1_xboole_0, B_3)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.00/1.30  tff(c_182, plain, (![B_3]: (k2_zfmisc_1('#skF_1', B_3)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_169, c_169, c_10])).
% 2.00/1.30  tff(c_170, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_24])).
% 2.00/1.30  tff(c_176, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_169, c_170])).
% 2.00/1.30  tff(c_214, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_182, c_176, c_32])).
% 2.00/1.30  tff(c_237, plain, (![B_32, A_33]: (v1_xboole_0(B_32) | ~m1_subset_1(B_32, k1_zfmisc_1(A_33)) | ~v1_xboole_0(A_33))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.00/1.30  tff(c_246, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_214, c_237])).
% 2.00/1.30  tff(c_253, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_171, c_246])).
% 2.00/1.30  tff(c_207, plain, (![A_1]: (A_1='#skF_1' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_169, c_4])).
% 2.00/1.30  tff(c_257, plain, ('#skF_3'='#skF_1'), inference(resolution, [status(thm)], [c_253, c_207])).
% 2.00/1.30  tff(c_261, plain, (~v1_partfun1('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_257, c_22])).
% 2.00/1.30  tff(c_8, plain, (![A_2]: (k2_zfmisc_1(A_2, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.00/1.30  tff(c_191, plain, (![A_2]: (k2_zfmisc_1(A_2, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_169, c_169, c_8])).
% 2.00/1.30  tff(c_215, plain, (![A_29]: (m1_subset_1(k6_partfun1(A_29), k1_zfmisc_1(k2_zfmisc_1(A_29, A_29))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.00/1.30  tff(c_219, plain, (m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_191, c_215])).
% 2.00/1.30  tff(c_240, plain, (v1_xboole_0(k6_partfun1('#skF_1')) | ~v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_219, c_237])).
% 2.00/1.30  tff(c_249, plain, (v1_xboole_0(k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_171, c_240])).
% 2.00/1.30  tff(c_271, plain, (k6_partfun1('#skF_1')='#skF_1'), inference(resolution, [status(thm)], [c_249, c_207])).
% 2.00/1.30  tff(c_18, plain, (![A_11]: (v1_partfun1(k6_partfun1(A_11), A_11))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.00/1.30  tff(c_294, plain, (v1_partfun1('#skF_1', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_271, c_18])).
% 2.00/1.30  tff(c_299, plain, $false, inference(negUnitSimplification, [status(thm)], [c_261, c_294])).
% 2.00/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.00/1.30  
% 2.00/1.30  Inference rules
% 2.00/1.30  ----------------------
% 2.00/1.30  #Ref     : 0
% 2.00/1.30  #Sup     : 56
% 2.00/1.30  #Fact    : 0
% 2.00/1.30  #Define  : 0
% 2.00/1.30  #Split   : 2
% 2.00/1.30  #Chain   : 0
% 2.00/1.30  #Close   : 0
% 2.00/1.30  
% 2.00/1.30  Ordering : KBO
% 2.00/1.30  
% 2.00/1.30  Simplification rules
% 2.00/1.30  ----------------------
% 2.00/1.30  #Subsume      : 0
% 2.00/1.30  #Demod        : 49
% 2.00/1.30  #Tautology    : 43
% 2.00/1.30  #SimpNegUnit  : 3
% 2.00/1.30  #BackRed      : 10
% 2.00/1.30  
% 2.00/1.30  #Partial instantiations: 0
% 2.00/1.30  #Strategies tried      : 1
% 2.00/1.30  
% 2.00/1.30  Timing (in seconds)
% 2.00/1.30  ----------------------
% 2.00/1.30  Preprocessing        : 0.31
% 2.00/1.30  Parsing              : 0.17
% 2.00/1.30  CNF conversion       : 0.02
% 2.00/1.30  Main loop            : 0.18
% 2.00/1.30  Inferencing          : 0.06
% 2.00/1.30  Reduction            : 0.06
% 2.00/1.30  Demodulation         : 0.05
% 2.00/1.30  BG Simplification    : 0.01
% 2.00/1.30  Subsumption          : 0.02
% 2.00/1.30  Abstraction          : 0.01
% 2.00/1.30  MUC search           : 0.00
% 2.00/1.30  Cooper               : 0.00
% 2.00/1.30  Total                : 0.52
% 2.00/1.30  Index Insertion      : 0.00
% 2.00/1.30  Index Deletion       : 0.00
% 2.00/1.30  Index Matching       : 0.00
% 2.00/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
