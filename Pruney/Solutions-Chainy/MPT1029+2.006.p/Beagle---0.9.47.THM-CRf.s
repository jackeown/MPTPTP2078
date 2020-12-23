%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:48 EST 2020

% Result     : Theorem 1.98s
% Output     : CNFRefutation 1.98s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 116 expanded)
%              Number of leaves         :   22 (  47 expanded)
%              Depth                    :    9
%              Number of atoms          :   84 ( 275 expanded)
%              Number of equality atoms :   23 (  90 expanded)
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

tff(f_83,negated_conjecture,(
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

tff(f_61,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_34,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

tff(f_40,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_47,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_65,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(c_24,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_37,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_24])).

tff(c_22,plain,(
    ~ v1_partfun1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_34,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_28,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_32,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_137,plain,(
    ! [C_24,A_25,B_26] :
      ( v1_partfun1(C_24,A_25)
      | ~ v1_funct_2(C_24,A_25,B_26)
      | ~ v1_funct_1(C_24)
      | ~ m1_subset_1(C_24,k1_zfmisc_1(k2_zfmisc_1(A_25,B_26)))
      | v1_xboole_0(B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_143,plain,
    ( v1_partfun1('#skF_3','#skF_1')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_137])).

tff(c_154,plain,
    ( v1_partfun1('#skF_3','#skF_1')
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_28,c_143])).

tff(c_155,plain,(
    v1_xboole_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_154])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_61,plain,(
    ! [B_16,A_17] :
      ( ~ v1_xboole_0(B_16)
      | B_16 = A_17
      | ~ v1_xboole_0(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_64,plain,(
    ! [A_17] :
      ( k1_xboole_0 = A_17
      | ~ v1_xboole_0(A_17) ) ),
    inference(resolution,[status(thm)],[c_2,c_61])).

tff(c_159,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_155,c_64])).

tff(c_165,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_37,c_159])).

tff(c_166,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_168,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_166,c_2])).

tff(c_10,plain,(
    ! [B_4] : k2_zfmisc_1(k1_xboole_0,B_4) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_179,plain,(
    ! [B_4] : k2_zfmisc_1('#skF_1',B_4) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_166,c_166,c_10])).

tff(c_167,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_173,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_166,c_167])).

tff(c_204,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_179,c_173,c_32])).

tff(c_237,plain,(
    ! [B_36,A_37] :
      ( v1_xboole_0(B_36)
      | ~ m1_subset_1(B_36,k1_zfmisc_1(A_37))
      | ~ v1_xboole_0(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_246,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_204,c_237])).

tff(c_253,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_168,c_246])).

tff(c_205,plain,(
    ! [B_30,A_31] :
      ( ~ v1_xboole_0(B_30)
      | B_30 = A_31
      | ~ v1_xboole_0(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_208,plain,(
    ! [A_31] :
      ( A_31 = '#skF_1'
      | ~ v1_xboole_0(A_31) ) ),
    inference(resolution,[status(thm)],[c_168,c_205])).

tff(c_259,plain,(
    '#skF_3' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_253,c_208])).

tff(c_264,plain,(
    ~ v1_partfun1('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_259,c_22])).

tff(c_8,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_187,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_166,c_166,c_8])).

tff(c_215,plain,(
    ! [A_33] : m1_subset_1(k6_partfun1(A_33),k1_zfmisc_1(k2_zfmisc_1(A_33,A_33))) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_219,plain,(
    m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_187,c_215])).

tff(c_240,plain,
    ( v1_xboole_0(k6_partfun1('#skF_1'))
    | ~ v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_219,c_237])).

tff(c_249,plain,(
    v1_xboole_0(k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_168,c_240])).

tff(c_289,plain,(
    k6_partfun1('#skF_1') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_249,c_208])).

tff(c_18,plain,(
    ! [A_12] : v1_partfun1(k6_partfun1(A_12),A_12) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_300,plain,(
    v1_partfun1('#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_289,c_18])).

tff(c_305,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_264,c_300])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:09:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.98/1.27  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.98/1.27  
% 1.98/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.98/1.27  %$ v1_funct_2 > v1_partfun1 > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k2_zfmisc_1 > #nlpp > k6_partfun1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 1.98/1.27  
% 1.98/1.27  %Foreground sorts:
% 1.98/1.27  
% 1.98/1.27  
% 1.98/1.27  %Background operators:
% 1.98/1.27  
% 1.98/1.27  
% 1.98/1.27  %Foreground operators:
% 1.98/1.27  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.98/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.98/1.27  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.98/1.27  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 1.98/1.27  tff('#skF_2', type, '#skF_2': $i).
% 1.98/1.27  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 1.98/1.27  tff('#skF_3', type, '#skF_3': $i).
% 1.98/1.27  tff('#skF_1', type, '#skF_1': $i).
% 1.98/1.27  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.98/1.27  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 1.98/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.98/1.27  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.98/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.98/1.27  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.98/1.27  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.98/1.27  
% 1.98/1.29  tff(f_83, negated_conjecture, ~(![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | v1_partfun1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t132_funct_2)).
% 1.98/1.29  tff(f_61, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc5_funct_2)).
% 1.98/1.29  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.98/1.29  tff(f_34, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_boole)).
% 1.98/1.29  tff(f_40, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 1.98/1.29  tff(f_47, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_subset_1)).
% 1.98/1.29  tff(f_65, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 1.98/1.29  tff(c_24, plain, (k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_83])).
% 1.98/1.29  tff(c_37, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_24])).
% 1.98/1.29  tff(c_22, plain, (~v1_partfun1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_83])).
% 1.98/1.29  tff(c_34, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_83])).
% 1.98/1.29  tff(c_28, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_83])).
% 1.98/1.29  tff(c_32, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_83])).
% 1.98/1.29  tff(c_137, plain, (![C_24, A_25, B_26]: (v1_partfun1(C_24, A_25) | ~v1_funct_2(C_24, A_25, B_26) | ~v1_funct_1(C_24) | ~m1_subset_1(C_24, k1_zfmisc_1(k2_zfmisc_1(A_25, B_26))) | v1_xboole_0(B_26))), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.98/1.29  tff(c_143, plain, (v1_partfun1('#skF_3', '#skF_1') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_32, c_137])).
% 1.98/1.29  tff(c_154, plain, (v1_partfun1('#skF_3', '#skF_1') | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_28, c_143])).
% 1.98/1.29  tff(c_155, plain, (v1_xboole_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_22, c_154])).
% 1.98/1.29  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 1.98/1.29  tff(c_61, plain, (![B_16, A_17]: (~v1_xboole_0(B_16) | B_16=A_17 | ~v1_xboole_0(A_17))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.98/1.29  tff(c_64, plain, (![A_17]: (k1_xboole_0=A_17 | ~v1_xboole_0(A_17))), inference(resolution, [status(thm)], [c_2, c_61])).
% 1.98/1.29  tff(c_159, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_155, c_64])).
% 1.98/1.29  tff(c_165, plain, $false, inference(negUnitSimplification, [status(thm)], [c_37, c_159])).
% 1.98/1.29  tff(c_166, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_24])).
% 1.98/1.29  tff(c_168, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_166, c_2])).
% 1.98/1.29  tff(c_10, plain, (![B_4]: (k2_zfmisc_1(k1_xboole_0, B_4)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.98/1.29  tff(c_179, plain, (![B_4]: (k2_zfmisc_1('#skF_1', B_4)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_166, c_166, c_10])).
% 1.98/1.29  tff(c_167, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_24])).
% 1.98/1.29  tff(c_173, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_166, c_167])).
% 1.98/1.29  tff(c_204, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_179, c_173, c_32])).
% 1.98/1.29  tff(c_237, plain, (![B_36, A_37]: (v1_xboole_0(B_36) | ~m1_subset_1(B_36, k1_zfmisc_1(A_37)) | ~v1_xboole_0(A_37))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.98/1.29  tff(c_246, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_204, c_237])).
% 1.98/1.29  tff(c_253, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_168, c_246])).
% 1.98/1.29  tff(c_205, plain, (![B_30, A_31]: (~v1_xboole_0(B_30) | B_30=A_31 | ~v1_xboole_0(A_31))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.98/1.29  tff(c_208, plain, (![A_31]: (A_31='#skF_1' | ~v1_xboole_0(A_31))), inference(resolution, [status(thm)], [c_168, c_205])).
% 1.98/1.29  tff(c_259, plain, ('#skF_3'='#skF_1'), inference(resolution, [status(thm)], [c_253, c_208])).
% 1.98/1.29  tff(c_264, plain, (~v1_partfun1('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_259, c_22])).
% 1.98/1.29  tff(c_8, plain, (![A_3]: (k2_zfmisc_1(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.98/1.29  tff(c_187, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_166, c_166, c_8])).
% 1.98/1.29  tff(c_215, plain, (![A_33]: (m1_subset_1(k6_partfun1(A_33), k1_zfmisc_1(k2_zfmisc_1(A_33, A_33))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 1.98/1.29  tff(c_219, plain, (m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_187, c_215])).
% 1.98/1.29  tff(c_240, plain, (v1_xboole_0(k6_partfun1('#skF_1')) | ~v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_219, c_237])).
% 1.98/1.29  tff(c_249, plain, (v1_xboole_0(k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_168, c_240])).
% 1.98/1.29  tff(c_289, plain, (k6_partfun1('#skF_1')='#skF_1'), inference(resolution, [status(thm)], [c_249, c_208])).
% 1.98/1.29  tff(c_18, plain, (![A_12]: (v1_partfun1(k6_partfun1(A_12), A_12))), inference(cnfTransformation, [status(thm)], [f_65])).
% 1.98/1.29  tff(c_300, plain, (v1_partfun1('#skF_1', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_289, c_18])).
% 1.98/1.29  tff(c_305, plain, $false, inference(negUnitSimplification, [status(thm)], [c_264, c_300])).
% 1.98/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.98/1.29  
% 1.98/1.29  Inference rules
% 1.98/1.29  ----------------------
% 1.98/1.29  #Ref     : 0
% 1.98/1.29  #Sup     : 60
% 1.98/1.29  #Fact    : 0
% 1.98/1.29  #Define  : 0
% 1.98/1.29  #Split   : 2
% 1.98/1.29  #Chain   : 0
% 1.98/1.29  #Close   : 0
% 1.98/1.29  
% 1.98/1.29  Ordering : KBO
% 1.98/1.29  
% 1.98/1.29  Simplification rules
% 1.98/1.29  ----------------------
% 1.98/1.29  #Subsume      : 1
% 1.98/1.29  #Demod        : 43
% 1.98/1.29  #Tautology    : 41
% 1.98/1.29  #SimpNegUnit  : 3
% 1.98/1.29  #BackRed      : 10
% 1.98/1.29  
% 1.98/1.29  #Partial instantiations: 0
% 1.98/1.29  #Strategies tried      : 1
% 1.98/1.29  
% 1.98/1.29  Timing (in seconds)
% 1.98/1.29  ----------------------
% 1.98/1.29  Preprocessing        : 0.31
% 1.98/1.29  Parsing              : 0.17
% 1.98/1.29  CNF conversion       : 0.02
% 1.98/1.29  Main loop            : 0.18
% 1.98/1.29  Inferencing          : 0.06
% 1.98/1.29  Reduction            : 0.06
% 1.98/1.29  Demodulation         : 0.04
% 1.98/1.29  BG Simplification    : 0.01
% 1.98/1.29  Subsumption          : 0.03
% 1.98/1.29  Abstraction          : 0.01
% 1.98/1.29  MUC search           : 0.00
% 1.98/1.29  Cooper               : 0.00
% 1.98/1.29  Total                : 0.52
% 1.98/1.29  Index Insertion      : 0.00
% 1.98/1.29  Index Deletion       : 0.00
% 1.98/1.29  Index Matching       : 0.00
% 1.98/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
