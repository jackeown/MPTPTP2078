%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:49 EST 2020

% Result     : Theorem 2.03s
% Output     : CNFRefutation 2.03s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 128 expanded)
%              Number of leaves         :   22 (  51 expanded)
%              Depth                    :    9
%              Number of atoms          :   94 ( 314 expanded)
%              Number of equality atoms :   24 (  95 expanded)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t132_funct_2)).

tff(f_47,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_34,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

tff(f_65,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(c_24,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_37,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_24])).

tff(c_32,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_92,plain,(
    ! [C_23,B_24,A_25] :
      ( v1_xboole_0(C_23)
      | ~ m1_subset_1(C_23,k1_zfmisc_1(k2_zfmisc_1(B_24,A_25)))
      | ~ v1_xboole_0(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_106,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_92])).

tff(c_109,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_106])).

tff(c_22,plain,(
    ~ v1_partfun1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_34,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_28,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_110,plain,(
    ! [C_26,A_27,B_28] :
      ( v1_partfun1(C_26,A_27)
      | ~ v1_funct_2(C_26,A_27,B_28)
      | ~ v1_funct_1(C_26)
      | ~ m1_subset_1(C_26,k1_zfmisc_1(k2_zfmisc_1(A_27,B_28)))
      | v1_xboole_0(B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_116,plain,
    ( v1_partfun1('#skF_3','#skF_1')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_110])).

tff(c_127,plain,
    ( v1_partfun1('#skF_3','#skF_1')
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_28,c_116])).

tff(c_129,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_109,c_22,c_127])).

tff(c_131,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_106])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_61,plain,(
    ! [B_17,A_18] :
      ( ~ v1_xboole_0(B_17)
      | B_17 = A_18
      | ~ v1_xboole_0(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_64,plain,(
    ! [A_18] :
      ( k1_xboole_0 = A_18
      | ~ v1_xboole_0(A_18) ) ),
    inference(resolution,[status(thm)],[c_2,c_61])).

tff(c_141,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_131,c_64])).

tff(c_147,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_37,c_141])).

tff(c_148,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_150,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_2])).

tff(c_20,plain,(
    ! [A_13] : m1_subset_1(k6_partfun1(A_13),k1_zfmisc_1(k2_zfmisc_1(A_13,A_13))) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_219,plain,(
    ! [C_38,B_39,A_40] :
      ( v1_xboole_0(C_38)
      | ~ m1_subset_1(C_38,k1_zfmisc_1(k2_zfmisc_1(B_39,A_40)))
      | ~ v1_xboole_0(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_232,plain,(
    ! [A_41] :
      ( v1_xboole_0(k6_partfun1(A_41))
      | ~ v1_xboole_0(A_41) ) ),
    inference(resolution,[status(thm)],[c_20,c_219])).

tff(c_187,plain,(
    ! [B_32,A_33] :
      ( ~ v1_xboole_0(B_32)
      | B_32 = A_33
      | ~ v1_xboole_0(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_190,plain,(
    ! [A_33] :
      ( A_33 = '#skF_1'
      | ~ v1_xboole_0(A_33) ) ),
    inference(resolution,[status(thm)],[c_150,c_187])).

tff(c_240,plain,(
    ! [A_42] :
      ( k6_partfun1(A_42) = '#skF_1'
      | ~ v1_xboole_0(A_42) ) ),
    inference(resolution,[status(thm)],[c_232,c_190])).

tff(c_248,plain,(
    k6_partfun1('#skF_1') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_150,c_240])).

tff(c_18,plain,(
    ! [A_13] : v1_partfun1(k6_partfun1(A_13),A_13) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_272,plain,(
    v1_partfun1('#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_248,c_18])).

tff(c_10,plain,(
    ! [B_4] : k2_zfmisc_1(k1_xboole_0,B_4) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_160,plain,(
    ! [B_4] : k2_zfmisc_1('#skF_1',B_4) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_148,c_10])).

tff(c_149,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_155,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_149])).

tff(c_186,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_160,c_155,c_32])).

tff(c_8,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_170,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_148,c_8])).

tff(c_225,plain,(
    ! [C_38] :
      ( v1_xboole_0(C_38)
      | ~ m1_subset_1(C_38,k1_zfmisc_1('#skF_1'))
      | ~ v1_xboole_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_170,c_219])).

tff(c_280,plain,(
    ! [C_46] :
      ( v1_xboole_0(C_46)
      | ~ m1_subset_1(C_46,k1_zfmisc_1('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_150,c_225])).

tff(c_289,plain,(
    v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_186,c_280])).

tff(c_299,plain,(
    '#skF_3' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_289,c_190])).

tff(c_304,plain,(
    ~ v1_partfun1('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_299,c_22])).

tff(c_310,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_272,c_304])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n024.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 10:59:21 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.03/1.20  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.03/1.21  
% 2.03/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.03/1.21  %$ v1_funct_2 > v1_partfun1 > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k2_zfmisc_1 > #nlpp > k6_partfun1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.03/1.21  
% 2.03/1.21  %Foreground sorts:
% 2.03/1.21  
% 2.03/1.21  
% 2.03/1.21  %Background operators:
% 2.03/1.21  
% 2.03/1.21  
% 2.03/1.21  %Foreground operators:
% 2.03/1.21  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.03/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.03/1.21  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.03/1.21  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.03/1.21  tff('#skF_2', type, '#skF_2': $i).
% 2.03/1.21  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 2.03/1.21  tff('#skF_3', type, '#skF_3': $i).
% 2.03/1.21  tff('#skF_1', type, '#skF_1': $i).
% 2.03/1.21  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.03/1.21  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 2.03/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.03/1.21  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.03/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.03/1.21  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.03/1.21  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.03/1.21  
% 2.03/1.22  tff(f_83, negated_conjecture, ~(![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | v1_partfun1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t132_funct_2)).
% 2.03/1.22  tff(f_47, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => v1_xboole_0(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc4_relset_1)).
% 2.03/1.22  tff(f_61, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc5_funct_2)).
% 2.03/1.22  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.03/1.22  tff(f_34, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_boole)).
% 2.03/1.22  tff(f_65, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 2.03/1.22  tff(f_40, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.03/1.22  tff(c_24, plain, (k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.03/1.22  tff(c_37, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_24])).
% 2.03/1.22  tff(c_32, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.03/1.22  tff(c_92, plain, (![C_23, B_24, A_25]: (v1_xboole_0(C_23) | ~m1_subset_1(C_23, k1_zfmisc_1(k2_zfmisc_1(B_24, A_25))) | ~v1_xboole_0(A_25))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.03/1.22  tff(c_106, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_32, c_92])).
% 2.03/1.22  tff(c_109, plain, (~v1_xboole_0('#skF_2')), inference(splitLeft, [status(thm)], [c_106])).
% 2.03/1.22  tff(c_22, plain, (~v1_partfun1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.03/1.22  tff(c_34, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.03/1.22  tff(c_28, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.03/1.22  tff(c_110, plain, (![C_26, A_27, B_28]: (v1_partfun1(C_26, A_27) | ~v1_funct_2(C_26, A_27, B_28) | ~v1_funct_1(C_26) | ~m1_subset_1(C_26, k1_zfmisc_1(k2_zfmisc_1(A_27, B_28))) | v1_xboole_0(B_28))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.03/1.22  tff(c_116, plain, (v1_partfun1('#skF_3', '#skF_1') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_32, c_110])).
% 2.03/1.22  tff(c_127, plain, (v1_partfun1('#skF_3', '#skF_1') | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_28, c_116])).
% 2.03/1.22  tff(c_129, plain, $false, inference(negUnitSimplification, [status(thm)], [c_109, c_22, c_127])).
% 2.03/1.22  tff(c_131, plain, (v1_xboole_0('#skF_2')), inference(splitRight, [status(thm)], [c_106])).
% 2.03/1.22  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.03/1.22  tff(c_61, plain, (![B_17, A_18]: (~v1_xboole_0(B_17) | B_17=A_18 | ~v1_xboole_0(A_18))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.03/1.22  tff(c_64, plain, (![A_18]: (k1_xboole_0=A_18 | ~v1_xboole_0(A_18))), inference(resolution, [status(thm)], [c_2, c_61])).
% 2.03/1.22  tff(c_141, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_131, c_64])).
% 2.03/1.22  tff(c_147, plain, $false, inference(negUnitSimplification, [status(thm)], [c_37, c_141])).
% 2.03/1.22  tff(c_148, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_24])).
% 2.03/1.22  tff(c_150, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_148, c_2])).
% 2.03/1.22  tff(c_20, plain, (![A_13]: (m1_subset_1(k6_partfun1(A_13), k1_zfmisc_1(k2_zfmisc_1(A_13, A_13))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.03/1.22  tff(c_219, plain, (![C_38, B_39, A_40]: (v1_xboole_0(C_38) | ~m1_subset_1(C_38, k1_zfmisc_1(k2_zfmisc_1(B_39, A_40))) | ~v1_xboole_0(A_40))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.03/1.22  tff(c_232, plain, (![A_41]: (v1_xboole_0(k6_partfun1(A_41)) | ~v1_xboole_0(A_41))), inference(resolution, [status(thm)], [c_20, c_219])).
% 2.03/1.22  tff(c_187, plain, (![B_32, A_33]: (~v1_xboole_0(B_32) | B_32=A_33 | ~v1_xboole_0(A_33))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.03/1.22  tff(c_190, plain, (![A_33]: (A_33='#skF_1' | ~v1_xboole_0(A_33))), inference(resolution, [status(thm)], [c_150, c_187])).
% 2.03/1.22  tff(c_240, plain, (![A_42]: (k6_partfun1(A_42)='#skF_1' | ~v1_xboole_0(A_42))), inference(resolution, [status(thm)], [c_232, c_190])).
% 2.03/1.22  tff(c_248, plain, (k6_partfun1('#skF_1')='#skF_1'), inference(resolution, [status(thm)], [c_150, c_240])).
% 2.03/1.22  tff(c_18, plain, (![A_13]: (v1_partfun1(k6_partfun1(A_13), A_13))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.03/1.22  tff(c_272, plain, (v1_partfun1('#skF_1', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_248, c_18])).
% 2.03/1.22  tff(c_10, plain, (![B_4]: (k2_zfmisc_1(k1_xboole_0, B_4)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.03/1.22  tff(c_160, plain, (![B_4]: (k2_zfmisc_1('#skF_1', B_4)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_148, c_148, c_10])).
% 2.03/1.22  tff(c_149, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_24])).
% 2.03/1.22  tff(c_155, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_148, c_149])).
% 2.03/1.22  tff(c_186, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_160, c_155, c_32])).
% 2.03/1.22  tff(c_8, plain, (![A_3]: (k2_zfmisc_1(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.03/1.22  tff(c_170, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_148, c_148, c_8])).
% 2.03/1.22  tff(c_225, plain, (![C_38]: (v1_xboole_0(C_38) | ~m1_subset_1(C_38, k1_zfmisc_1('#skF_1')) | ~v1_xboole_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_170, c_219])).
% 2.03/1.22  tff(c_280, plain, (![C_46]: (v1_xboole_0(C_46) | ~m1_subset_1(C_46, k1_zfmisc_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_150, c_225])).
% 2.03/1.22  tff(c_289, plain, (v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_186, c_280])).
% 2.03/1.22  tff(c_299, plain, ('#skF_3'='#skF_1'), inference(resolution, [status(thm)], [c_289, c_190])).
% 2.03/1.22  tff(c_304, plain, (~v1_partfun1('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_299, c_22])).
% 2.03/1.22  tff(c_310, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_272, c_304])).
% 2.03/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.03/1.22  
% 2.03/1.22  Inference rules
% 2.03/1.22  ----------------------
% 2.03/1.22  #Ref     : 0
% 2.03/1.22  #Sup     : 60
% 2.03/1.22  #Fact    : 0
% 2.03/1.22  #Define  : 0
% 2.03/1.22  #Split   : 2
% 2.03/1.22  #Chain   : 0
% 2.03/1.22  #Close   : 0
% 2.03/1.22  
% 2.03/1.22  Ordering : KBO
% 2.03/1.22  
% 2.03/1.22  Simplification rules
% 2.03/1.22  ----------------------
% 2.03/1.22  #Subsume      : 1
% 2.03/1.22  #Demod        : 37
% 2.03/1.22  #Tautology    : 37
% 2.03/1.22  #SimpNegUnit  : 2
% 2.03/1.22  #BackRed      : 7
% 2.03/1.22  
% 2.03/1.22  #Partial instantiations: 0
% 2.03/1.22  #Strategies tried      : 1
% 2.03/1.22  
% 2.03/1.22  Timing (in seconds)
% 2.03/1.22  ----------------------
% 2.03/1.23  Preprocessing        : 0.29
% 2.03/1.23  Parsing              : 0.16
% 2.03/1.23  CNF conversion       : 0.02
% 2.03/1.23  Main loop            : 0.18
% 2.03/1.23  Inferencing          : 0.06
% 2.03/1.23  Reduction            : 0.05
% 2.03/1.23  Demodulation         : 0.04
% 2.03/1.23  BG Simplification    : 0.01
% 2.03/1.23  Subsumption          : 0.03
% 2.03/1.23  Abstraction          : 0.01
% 2.03/1.23  MUC search           : 0.00
% 2.03/1.23  Cooper               : 0.00
% 2.03/1.23  Total                : 0.50
% 2.03/1.23  Index Insertion      : 0.00
% 2.03/1.23  Index Deletion       : 0.00
% 2.03/1.23  Index Matching       : 0.00
% 2.03/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
