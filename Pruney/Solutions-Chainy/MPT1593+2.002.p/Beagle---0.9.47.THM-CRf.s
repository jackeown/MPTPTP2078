%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:25:20 EST 2020

% Result     : Theorem 1.90s
% Output     : CNFRefutation 2.08s
% Verified   : 
% Statistics : Number of formulae       :   47 (  61 expanded)
%              Number of leaves         :   25 (  33 expanded)
%              Depth                    :    7
%              Number of atoms          :   62 (  92 expanded)
%              Number of equality atoms :   33 (  44 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_partfun1 > m1_subset_1 > v8_relat_2 > v4_relat_2 > v1_relat_2 > v1_orders_2 > l1_orders_2 > k2_zfmisc_1 > g1_orders_2 > #nlpp > u1_struct_0 > u1_orders_2 > k2_yellow_1 > k1_zfmisc_1 > k1_yellow_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_orders_2,type,(
    v1_orders_2: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k2_yellow_1,type,(
    k2_yellow_1: $i > $i )).

tff(v1_relat_2,type,(
    v1_relat_2: $i > $o )).

tff(v8_relat_2,type,(
    v8_relat_2: $i > $o )).

tff(g1_orders_2,type,(
    g1_orders_2: ( $i * $i ) > $i )).

tff(v4_relat_2,type,(
    v4_relat_2: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff(k1_yellow_1,type,(
    k1_yellow_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_orders_2,type,(
    u1_orders_2: $i > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_56,axiom,(
    ! [A] :
      ( v1_orders_2(k2_yellow_1(A))
      & l1_orders_2(k2_yellow_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_yellow_1)).

tff(f_31,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v1_orders_2(A)
       => A = g1_orders_2(u1_struct_0(A),u1_orders_2(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',abstractness_v1_orders_2)).

tff(f_52,axiom,(
    ! [A] :
      ( v1_relat_2(k1_yellow_1(A))
      & v4_relat_2(k1_yellow_1(A))
      & v8_relat_2(k1_yellow_1(A))
      & v1_partfun1(k1_yellow_1(A),A)
      & m1_subset_1(k1_yellow_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_yellow_1)).

tff(f_42,axiom,(
    ! [A] : k2_yellow_1(A) = g1_orders_2(A,k1_yellow_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_yellow_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A)))
     => ! [C,D] :
          ( g1_orders_2(A,B) = g1_orders_2(C,D)
         => ( A = C
            & B = D ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',free_g1_orders_2)).

tff(f_61,negated_conjecture,(
    ~ ! [A] :
        ( u1_struct_0(k2_yellow_1(A)) = A
        & u1_orders_2(k2_yellow_1(A)) = k1_yellow_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_yellow_1)).

tff(c_22,plain,(
    ! [A_10] : l1_orders_2(k2_yellow_1(A_10)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_20,plain,(
    ! [A_10] : v1_orders_2(k2_yellow_1(A_10)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_2,plain,(
    ! [A_1] :
      ( g1_orders_2(u1_struct_0(A_1),u1_orders_2(A_1)) = A_1
      | ~ v1_orders_2(A_1)
      | ~ l1_orders_2(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_18,plain,(
    ! [A_9] : m1_subset_1(k1_yellow_1(A_9),k1_zfmisc_1(k2_zfmisc_1(A_9,A_9))) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_8,plain,(
    ! [A_8] : g1_orders_2(A_8,k1_yellow_1(A_8)) = k2_yellow_1(A_8) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_170,plain,(
    ! [C_46,A_47,D_48,B_49] :
      ( C_46 = A_47
      | g1_orders_2(C_46,D_48) != g1_orders_2(A_47,B_49)
      | ~ m1_subset_1(B_49,k1_zfmisc_1(k2_zfmisc_1(A_47,A_47))) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_182,plain,(
    ! [C_46,A_8,D_48] :
      ( C_46 = A_8
      | k2_yellow_1(A_8) != g1_orders_2(C_46,D_48)
      | ~ m1_subset_1(k1_yellow_1(A_8),k1_zfmisc_1(k2_zfmisc_1(A_8,A_8))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_170])).

tff(c_185,plain,(
    ! [C_50,A_51,D_52] :
      ( C_50 = A_51
      | k2_yellow_1(A_51) != g1_orders_2(C_50,D_52) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_182])).

tff(c_191,plain,(
    ! [A_1,A_51] :
      ( u1_struct_0(A_1) = A_51
      | k2_yellow_1(A_51) != A_1
      | ~ v1_orders_2(A_1)
      | ~ l1_orders_2(A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_185])).

tff(c_219,plain,(
    ! [A_51] :
      ( u1_struct_0(k2_yellow_1(A_51)) = A_51
      | ~ v1_orders_2(k2_yellow_1(A_51))
      | ~ l1_orders_2(k2_yellow_1(A_51)) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_191])).

tff(c_221,plain,(
    ! [A_51] : u1_struct_0(k2_yellow_1(A_51)) = A_51 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_219])).

tff(c_55,plain,(
    ! [D_20,B_21,C_22,A_23] :
      ( D_20 = B_21
      | g1_orders_2(C_22,D_20) != g1_orders_2(A_23,B_21)
      | ~ m1_subset_1(B_21,k1_zfmisc_1(k2_zfmisc_1(A_23,A_23))) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_63,plain,(
    ! [A_8,D_20,C_22] :
      ( k1_yellow_1(A_8) = D_20
      | k2_yellow_1(A_8) != g1_orders_2(C_22,D_20)
      | ~ m1_subset_1(k1_yellow_1(A_8),k1_zfmisc_1(k2_zfmisc_1(A_8,A_8))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_55])).

tff(c_66,plain,(
    ! [A_24,D_25,C_26] :
      ( k1_yellow_1(A_24) = D_25
      | k2_yellow_1(A_24) != g1_orders_2(C_26,D_25) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_63])).

tff(c_69,plain,(
    ! [A_1,A_24] :
      ( u1_orders_2(A_1) = k1_yellow_1(A_24)
      | k2_yellow_1(A_24) != A_1
      | ~ v1_orders_2(A_1)
      | ~ l1_orders_2(A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_66])).

tff(c_81,plain,(
    ! [A_24] :
      ( u1_orders_2(k2_yellow_1(A_24)) = k1_yellow_1(A_24)
      | ~ v1_orders_2(k2_yellow_1(A_24))
      | ~ l1_orders_2(k2_yellow_1(A_24)) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_69])).

tff(c_83,plain,(
    ! [A_24] : u1_orders_2(k2_yellow_1(A_24)) = k1_yellow_1(A_24) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_81])).

tff(c_24,plain,
    ( u1_struct_0(k2_yellow_1('#skF_2')) != '#skF_2'
    | u1_orders_2(k2_yellow_1('#skF_1')) != k1_yellow_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_41,plain,(
    u1_orders_2(k2_yellow_1('#skF_1')) != k1_yellow_1('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_24])).

tff(c_102,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_41])).

tff(c_103,plain,(
    u1_struct_0(k2_yellow_1('#skF_2')) != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_226,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_221,c_103])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:12:38 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.90/1.22  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.90/1.22  
% 1.90/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.90/1.23  %$ v1_partfun1 > m1_subset_1 > v8_relat_2 > v4_relat_2 > v1_relat_2 > v1_orders_2 > l1_orders_2 > k2_zfmisc_1 > g1_orders_2 > #nlpp > u1_struct_0 > u1_orders_2 > k2_yellow_1 > k1_zfmisc_1 > k1_yellow_1 > #skF_2 > #skF_1
% 1.90/1.23  
% 1.90/1.23  %Foreground sorts:
% 1.90/1.23  
% 1.90/1.23  
% 1.90/1.23  %Background operators:
% 1.90/1.23  
% 1.90/1.23  
% 1.90/1.23  %Foreground operators:
% 1.90/1.23  tff(v1_orders_2, type, v1_orders_2: $i > $o).
% 1.90/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.90/1.23  tff(k2_yellow_1, type, k2_yellow_1: $i > $i).
% 1.90/1.23  tff(v1_relat_2, type, v1_relat_2: $i > $o).
% 1.90/1.23  tff(v8_relat_2, type, v8_relat_2: $i > $o).
% 1.90/1.23  tff(g1_orders_2, type, g1_orders_2: ($i * $i) > $i).
% 1.90/1.23  tff(v4_relat_2, type, v4_relat_2: $i > $o).
% 1.90/1.23  tff('#skF_2', type, '#skF_2': $i).
% 1.90/1.23  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 1.90/1.23  tff('#skF_1', type, '#skF_1': $i).
% 1.90/1.23  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.90/1.23  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 1.90/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.90/1.23  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.90/1.23  tff(k1_yellow_1, type, k1_yellow_1: $i > $i).
% 1.90/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.90/1.23  tff(u1_orders_2, type, u1_orders_2: $i > $i).
% 1.90/1.23  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 1.90/1.23  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.90/1.23  
% 2.08/1.24  tff(f_56, axiom, (![A]: (v1_orders_2(k2_yellow_1(A)) & l1_orders_2(k2_yellow_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_yellow_1)).
% 2.08/1.24  tff(f_31, axiom, (![A]: (l1_orders_2(A) => (v1_orders_2(A) => (A = g1_orders_2(u1_struct_0(A), u1_orders_2(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', abstractness_v1_orders_2)).
% 2.08/1.24  tff(f_52, axiom, (![A]: ((((v1_relat_2(k1_yellow_1(A)) & v4_relat_2(k1_yellow_1(A))) & v8_relat_2(k1_yellow_1(A))) & v1_partfun1(k1_yellow_1(A), A)) & m1_subset_1(k1_yellow_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_yellow_1)).
% 2.08/1.24  tff(f_42, axiom, (![A]: (k2_yellow_1(A) = g1_orders_2(A, k1_yellow_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_yellow_1)).
% 2.08/1.24  tff(f_40, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A))) => (![C, D]: ((g1_orders_2(A, B) = g1_orders_2(C, D)) => ((A = C) & (B = D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', free_g1_orders_2)).
% 2.08/1.24  tff(f_61, negated_conjecture, ~(![A]: ((u1_struct_0(k2_yellow_1(A)) = A) & (u1_orders_2(k2_yellow_1(A)) = k1_yellow_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_yellow_1)).
% 2.08/1.24  tff(c_22, plain, (![A_10]: (l1_orders_2(k2_yellow_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.08/1.24  tff(c_20, plain, (![A_10]: (v1_orders_2(k2_yellow_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.08/1.24  tff(c_2, plain, (![A_1]: (g1_orders_2(u1_struct_0(A_1), u1_orders_2(A_1))=A_1 | ~v1_orders_2(A_1) | ~l1_orders_2(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.08/1.24  tff(c_18, plain, (![A_9]: (m1_subset_1(k1_yellow_1(A_9), k1_zfmisc_1(k2_zfmisc_1(A_9, A_9))))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.08/1.24  tff(c_8, plain, (![A_8]: (g1_orders_2(A_8, k1_yellow_1(A_8))=k2_yellow_1(A_8))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.08/1.24  tff(c_170, plain, (![C_46, A_47, D_48, B_49]: (C_46=A_47 | g1_orders_2(C_46, D_48)!=g1_orders_2(A_47, B_49) | ~m1_subset_1(B_49, k1_zfmisc_1(k2_zfmisc_1(A_47, A_47))))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.08/1.24  tff(c_182, plain, (![C_46, A_8, D_48]: (C_46=A_8 | k2_yellow_1(A_8)!=g1_orders_2(C_46, D_48) | ~m1_subset_1(k1_yellow_1(A_8), k1_zfmisc_1(k2_zfmisc_1(A_8, A_8))))), inference(superposition, [status(thm), theory('equality')], [c_8, c_170])).
% 2.08/1.24  tff(c_185, plain, (![C_50, A_51, D_52]: (C_50=A_51 | k2_yellow_1(A_51)!=g1_orders_2(C_50, D_52))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_182])).
% 2.08/1.24  tff(c_191, plain, (![A_1, A_51]: (u1_struct_0(A_1)=A_51 | k2_yellow_1(A_51)!=A_1 | ~v1_orders_2(A_1) | ~l1_orders_2(A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_185])).
% 2.08/1.24  tff(c_219, plain, (![A_51]: (u1_struct_0(k2_yellow_1(A_51))=A_51 | ~v1_orders_2(k2_yellow_1(A_51)) | ~l1_orders_2(k2_yellow_1(A_51)))), inference(reflexivity, [status(thm), theory('equality')], [c_191])).
% 2.08/1.24  tff(c_221, plain, (![A_51]: (u1_struct_0(k2_yellow_1(A_51))=A_51)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_20, c_219])).
% 2.08/1.24  tff(c_55, plain, (![D_20, B_21, C_22, A_23]: (D_20=B_21 | g1_orders_2(C_22, D_20)!=g1_orders_2(A_23, B_21) | ~m1_subset_1(B_21, k1_zfmisc_1(k2_zfmisc_1(A_23, A_23))))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.08/1.24  tff(c_63, plain, (![A_8, D_20, C_22]: (k1_yellow_1(A_8)=D_20 | k2_yellow_1(A_8)!=g1_orders_2(C_22, D_20) | ~m1_subset_1(k1_yellow_1(A_8), k1_zfmisc_1(k2_zfmisc_1(A_8, A_8))))), inference(superposition, [status(thm), theory('equality')], [c_8, c_55])).
% 2.08/1.24  tff(c_66, plain, (![A_24, D_25, C_26]: (k1_yellow_1(A_24)=D_25 | k2_yellow_1(A_24)!=g1_orders_2(C_26, D_25))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_63])).
% 2.08/1.24  tff(c_69, plain, (![A_1, A_24]: (u1_orders_2(A_1)=k1_yellow_1(A_24) | k2_yellow_1(A_24)!=A_1 | ~v1_orders_2(A_1) | ~l1_orders_2(A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_66])).
% 2.08/1.24  tff(c_81, plain, (![A_24]: (u1_orders_2(k2_yellow_1(A_24))=k1_yellow_1(A_24) | ~v1_orders_2(k2_yellow_1(A_24)) | ~l1_orders_2(k2_yellow_1(A_24)))), inference(reflexivity, [status(thm), theory('equality')], [c_69])).
% 2.08/1.24  tff(c_83, plain, (![A_24]: (u1_orders_2(k2_yellow_1(A_24))=k1_yellow_1(A_24))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_20, c_81])).
% 2.08/1.24  tff(c_24, plain, (u1_struct_0(k2_yellow_1('#skF_2'))!='#skF_2' | u1_orders_2(k2_yellow_1('#skF_1'))!=k1_yellow_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.08/1.24  tff(c_41, plain, (u1_orders_2(k2_yellow_1('#skF_1'))!=k1_yellow_1('#skF_1')), inference(splitLeft, [status(thm)], [c_24])).
% 2.08/1.24  tff(c_102, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_83, c_41])).
% 2.08/1.24  tff(c_103, plain, (u1_struct_0(k2_yellow_1('#skF_2'))!='#skF_2'), inference(splitRight, [status(thm)], [c_24])).
% 2.08/1.24  tff(c_226, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_221, c_103])).
% 2.08/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.08/1.24  
% 2.08/1.24  Inference rules
% 2.08/1.24  ----------------------
% 2.08/1.24  #Ref     : 11
% 2.08/1.24  #Sup     : 42
% 2.08/1.24  #Fact    : 0
% 2.08/1.24  #Define  : 0
% 2.08/1.24  #Split   : 1
% 2.08/1.24  #Chain   : 0
% 2.08/1.24  #Close   : 0
% 2.08/1.24  
% 2.08/1.24  Ordering : KBO
% 2.08/1.24  
% 2.08/1.24  Simplification rules
% 2.08/1.24  ----------------------
% 2.08/1.24  #Subsume      : 3
% 2.08/1.24  #Demod        : 20
% 2.08/1.24  #Tautology    : 23
% 2.08/1.24  #SimpNegUnit  : 0
% 2.08/1.24  #BackRed      : 4
% 2.08/1.24  
% 2.08/1.24  #Partial instantiations: 0
% 2.08/1.24  #Strategies tried      : 1
% 2.08/1.24  
% 2.08/1.24  Timing (in seconds)
% 2.08/1.24  ----------------------
% 2.08/1.24  Preprocessing        : 0.27
% 2.08/1.24  Parsing              : 0.15
% 2.08/1.24  CNF conversion       : 0.02
% 2.08/1.24  Main loop            : 0.20
% 2.08/1.24  Inferencing          : 0.08
% 2.08/1.24  Reduction            : 0.06
% 2.08/1.24  Demodulation         : 0.04
% 2.08/1.24  BG Simplification    : 0.01
% 2.08/1.24  Subsumption          : 0.04
% 2.08/1.24  Abstraction          : 0.01
% 2.08/1.24  MUC search           : 0.00
% 2.08/1.24  Cooper               : 0.00
% 2.08/1.24  Total                : 0.50
% 2.08/1.24  Index Insertion      : 0.00
% 2.08/1.24  Index Deletion       : 0.00
% 2.08/1.24  Index Matching       : 0.00
% 2.08/1.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
