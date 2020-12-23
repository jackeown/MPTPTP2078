%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:25:20 EST 2020

% Result     : Theorem 2.79s
% Output     : CNFRefutation 3.23s
% Verified   : 
% Statistics : Number of formulae       :   53 ( 143 expanded)
%              Number of leaves         :   21 (  59 expanded)
%              Depth                    :   11
%              Number of atoms          :   90 ( 283 expanded)
%              Number of equality atoms :   42 ( 110 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_subset_1 > v1_orders_2 > l1_orders_2 > k2_zfmisc_1 > g1_orders_2 > #nlpp > u1_struct_0 > u1_orders_2 > k2_yellow_1 > k1_zfmisc_1 > k1_yellow_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_orders_2,type,(
    v1_orders_2: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k2_yellow_1,type,(
    k2_yellow_1: $i > $i )).

tff(g1_orders_2,type,(
    g1_orders_2: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff(f_50,axiom,(
    ! [A] :
      ( v1_orders_2(k2_yellow_1(A))
      & l1_orders_2(k2_yellow_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_yellow_1)).

tff(f_35,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => m1_subset_1(u1_orders_2(A),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_orders_2)).

tff(f_46,axiom,(
    ! [A] : k2_yellow_1(A) = g1_orders_2(A,k1_yellow_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_yellow_1)).

tff(f_31,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v1_orders_2(A)
       => A = g1_orders_2(u1_struct_0(A),u1_orders_2(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',abstractness_v1_orders_2)).

tff(f_44,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A)))
     => ! [C,D] :
          ( g1_orders_2(A,B) = g1_orders_2(C,D)
         => ( A = C
            & B = D ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_orders_2)).

tff(f_55,negated_conjecture,(
    ~ ! [A] :
        ( u1_struct_0(k2_yellow_1(A)) = A
        & u1_orders_2(k2_yellow_1(A)) = k1_yellow_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_yellow_1)).

tff(c_14,plain,(
    ! [A_10] : l1_orders_2(k2_yellow_1(A_10)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_4,plain,(
    ! [A_2] :
      ( m1_subset_1(u1_orders_2(A_2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2),u1_struct_0(A_2))))
      | ~ l1_orders_2(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_12,plain,(
    ! [A_10] : v1_orders_2(k2_yellow_1(A_10)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_10,plain,(
    ! [A_9] : g1_orders_2(A_9,k1_yellow_1(A_9)) = k2_yellow_1(A_9) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_2,plain,(
    ! [A_1] :
      ( g1_orders_2(u1_struct_0(A_1),u1_orders_2(A_1)) = A_1
      | ~ v1_orders_2(A_1)
      | ~ l1_orders_2(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_530,plain,(
    ! [C_100,A_101,D_102,B_103] :
      ( C_100 = A_101
      | g1_orders_2(C_100,D_102) != g1_orders_2(A_101,B_103)
      | ~ m1_subset_1(B_103,k1_zfmisc_1(k2_zfmisc_1(A_101,A_101))) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_974,plain,(
    ! [A_162,C_163,D_164] :
      ( u1_struct_0(A_162) = C_163
      | g1_orders_2(C_163,D_164) != A_162
      | ~ m1_subset_1(u1_orders_2(A_162),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_162),u1_struct_0(A_162))))
      | ~ v1_orders_2(A_162)
      | ~ l1_orders_2(A_162) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_530])).

tff(c_982,plain,(
    ! [A_162,A_9] :
      ( u1_struct_0(A_162) = A_9
      | k2_yellow_1(A_9) != A_162
      | ~ m1_subset_1(u1_orders_2(A_162),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_162),u1_struct_0(A_162))))
      | ~ v1_orders_2(A_162)
      | ~ l1_orders_2(A_162) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_974])).

tff(c_992,plain,(
    ! [A_9] :
      ( u1_struct_0(k2_yellow_1(A_9)) = A_9
      | ~ m1_subset_1(u1_orders_2(k2_yellow_1(A_9)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k2_yellow_1(A_9)),u1_struct_0(k2_yellow_1(A_9)))))
      | ~ v1_orders_2(k2_yellow_1(A_9))
      | ~ l1_orders_2(k2_yellow_1(A_9)) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_982])).

tff(c_1000,plain,(
    ! [A_171] :
      ( u1_struct_0(k2_yellow_1(A_171)) = A_171
      | ~ m1_subset_1(u1_orders_2(k2_yellow_1(A_171)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k2_yellow_1(A_171)),u1_struct_0(k2_yellow_1(A_171))))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_12,c_992])).

tff(c_1018,plain,(
    ! [A_171] :
      ( u1_struct_0(k2_yellow_1(A_171)) = A_171
      | ~ l1_orders_2(k2_yellow_1(A_171)) ) ),
    inference(resolution,[status(thm)],[c_4,c_1000])).

tff(c_1028,plain,(
    ! [A_171] : u1_struct_0(k2_yellow_1(A_171)) = A_171 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_1018])).

tff(c_56,plain,(
    ! [C_20,A_21,D_22,B_23] :
      ( C_20 = A_21
      | g1_orders_2(C_20,D_22) != g1_orders_2(A_21,B_23)
      | ~ m1_subset_1(B_23,k1_zfmisc_1(k2_zfmisc_1(A_21,A_21))) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_65,plain,(
    ! [A_25,A_24,B_26] :
      ( A_25 = A_24
      | k2_yellow_1(A_24) != g1_orders_2(A_25,B_26)
      | ~ m1_subset_1(B_26,k1_zfmisc_1(k2_zfmisc_1(A_25,A_25))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_56])).

tff(c_67,plain,(
    ! [A_1,A_24] :
      ( u1_struct_0(A_1) = A_24
      | k2_yellow_1(A_24) != A_1
      | ~ m1_subset_1(u1_orders_2(A_1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1),u1_struct_0(A_1))))
      | ~ v1_orders_2(A_1)
      | ~ l1_orders_2(A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_65])).

tff(c_152,plain,(
    ! [A_24] :
      ( u1_struct_0(k2_yellow_1(A_24)) = A_24
      | ~ m1_subset_1(u1_orders_2(k2_yellow_1(A_24)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k2_yellow_1(A_24)),u1_struct_0(k2_yellow_1(A_24)))))
      | ~ v1_orders_2(k2_yellow_1(A_24))
      | ~ l1_orders_2(k2_yellow_1(A_24)) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_67])).

tff(c_156,plain,(
    ! [A_59] :
      ( u1_struct_0(k2_yellow_1(A_59)) = A_59
      | ~ m1_subset_1(u1_orders_2(k2_yellow_1(A_59)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k2_yellow_1(A_59)),u1_struct_0(k2_yellow_1(A_59))))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_12,c_152])).

tff(c_159,plain,(
    ! [A_59] :
      ( u1_struct_0(k2_yellow_1(A_59)) = A_59
      | ~ l1_orders_2(k2_yellow_1(A_59)) ) ),
    inference(resolution,[status(thm)],[c_4,c_156])).

tff(c_162,plain,(
    ! [A_59] : u1_struct_0(k2_yellow_1(A_59)) = A_59 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_159])).

tff(c_165,plain,(
    ! [A_60] : u1_struct_0(k2_yellow_1(A_60)) = A_60 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_159])).

tff(c_171,plain,(
    ! [A_60] :
      ( m1_subset_1(u1_orders_2(k2_yellow_1(A_60)),k1_zfmisc_1(k2_zfmisc_1(A_60,u1_struct_0(k2_yellow_1(A_60)))))
      | ~ l1_orders_2(k2_yellow_1(A_60)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_165,c_4])).

tff(c_183,plain,(
    ! [A_60] : m1_subset_1(u1_orders_2(k2_yellow_1(A_60)),k1_zfmisc_1(k2_zfmisc_1(A_60,A_60))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_162,c_171])).

tff(c_43,plain,(
    ! [D_16,B_17,C_18,A_19] :
      ( D_16 = B_17
      | g1_orders_2(C_18,D_16) != g1_orders_2(A_19,B_17)
      | ~ m1_subset_1(B_17,k1_zfmisc_1(k2_zfmisc_1(A_19,A_19))) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_75,plain,(
    ! [A_29,B_30,A_31] :
      ( k1_yellow_1(A_29) = B_30
      | k2_yellow_1(A_29) != g1_orders_2(A_31,B_30)
      | ~ m1_subset_1(B_30,k1_zfmisc_1(k2_zfmisc_1(A_31,A_31))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_43])).

tff(c_77,plain,(
    ! [A_1,A_29] :
      ( u1_orders_2(A_1) = k1_yellow_1(A_29)
      | k2_yellow_1(A_29) != A_1
      | ~ m1_subset_1(u1_orders_2(A_1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1),u1_struct_0(A_1))))
      | ~ v1_orders_2(A_1)
      | ~ l1_orders_2(A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_75])).

tff(c_447,plain,(
    ! [A_29] :
      ( u1_orders_2(k2_yellow_1(A_29)) = k1_yellow_1(A_29)
      | ~ m1_subset_1(u1_orders_2(k2_yellow_1(A_29)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k2_yellow_1(A_29)),u1_struct_0(k2_yellow_1(A_29)))))
      | ~ v1_orders_2(k2_yellow_1(A_29))
      | ~ l1_orders_2(k2_yellow_1(A_29)) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_77])).

tff(c_449,plain,(
    ! [A_29] : u1_orders_2(k2_yellow_1(A_29)) = k1_yellow_1(A_29) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_12,c_183,c_162,c_162,c_447])).

tff(c_16,plain,
    ( u1_struct_0(k2_yellow_1('#skF_2')) != '#skF_2'
    | u1_orders_2(k2_yellow_1('#skF_1')) != k1_yellow_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_28,plain,(
    u1_orders_2(k2_yellow_1('#skF_1')) != k1_yellow_1('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_16])).

tff(c_464,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_449,c_28])).

tff(c_465,plain,(
    u1_struct_0(k2_yellow_1('#skF_2')) != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_16])).

tff(c_1043,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1028,c_465])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n011.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 09:34:42 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.79/1.45  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.79/1.45  
% 2.79/1.45  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.79/1.45  %$ m1_subset_1 > v1_orders_2 > l1_orders_2 > k2_zfmisc_1 > g1_orders_2 > #nlpp > u1_struct_0 > u1_orders_2 > k2_yellow_1 > k1_zfmisc_1 > k1_yellow_1 > #skF_2 > #skF_1
% 2.79/1.45  
% 2.79/1.45  %Foreground sorts:
% 2.79/1.45  
% 2.79/1.45  
% 2.79/1.45  %Background operators:
% 2.79/1.45  
% 2.79/1.45  
% 2.79/1.45  %Foreground operators:
% 2.79/1.45  tff(v1_orders_2, type, v1_orders_2: $i > $o).
% 2.79/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.79/1.45  tff(k2_yellow_1, type, k2_yellow_1: $i > $i).
% 2.79/1.45  tff(g1_orders_2, type, g1_orders_2: ($i * $i) > $i).
% 2.79/1.45  tff('#skF_2', type, '#skF_2': $i).
% 2.79/1.45  tff('#skF_1', type, '#skF_1': $i).
% 2.79/1.45  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.79/1.45  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.79/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.79/1.45  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.79/1.45  tff(k1_yellow_1, type, k1_yellow_1: $i > $i).
% 2.79/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.79/1.45  tff(u1_orders_2, type, u1_orders_2: $i > $i).
% 2.79/1.45  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.79/1.45  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.79/1.45  
% 3.23/1.47  tff(f_50, axiom, (![A]: (v1_orders_2(k2_yellow_1(A)) & l1_orders_2(k2_yellow_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_yellow_1)).
% 3.23/1.47  tff(f_35, axiom, (![A]: (l1_orders_2(A) => m1_subset_1(u1_orders_2(A), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_u1_orders_2)).
% 3.23/1.47  tff(f_46, axiom, (![A]: (k2_yellow_1(A) = g1_orders_2(A, k1_yellow_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_yellow_1)).
% 3.23/1.47  tff(f_31, axiom, (![A]: (l1_orders_2(A) => (v1_orders_2(A) => (A = g1_orders_2(u1_struct_0(A), u1_orders_2(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', abstractness_v1_orders_2)).
% 3.23/1.47  tff(f_44, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A))) => (![C, D]: ((g1_orders_2(A, B) = g1_orders_2(C, D)) => ((A = C) & (B = D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', free_g1_orders_2)).
% 3.23/1.47  tff(f_55, negated_conjecture, ~(![A]: ((u1_struct_0(k2_yellow_1(A)) = A) & (u1_orders_2(k2_yellow_1(A)) = k1_yellow_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_yellow_1)).
% 3.23/1.47  tff(c_14, plain, (![A_10]: (l1_orders_2(k2_yellow_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.23/1.47  tff(c_4, plain, (![A_2]: (m1_subset_1(u1_orders_2(A_2), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2), u1_struct_0(A_2)))) | ~l1_orders_2(A_2))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.23/1.47  tff(c_12, plain, (![A_10]: (v1_orders_2(k2_yellow_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.23/1.47  tff(c_10, plain, (![A_9]: (g1_orders_2(A_9, k1_yellow_1(A_9))=k2_yellow_1(A_9))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.23/1.47  tff(c_2, plain, (![A_1]: (g1_orders_2(u1_struct_0(A_1), u1_orders_2(A_1))=A_1 | ~v1_orders_2(A_1) | ~l1_orders_2(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.23/1.47  tff(c_530, plain, (![C_100, A_101, D_102, B_103]: (C_100=A_101 | g1_orders_2(C_100, D_102)!=g1_orders_2(A_101, B_103) | ~m1_subset_1(B_103, k1_zfmisc_1(k2_zfmisc_1(A_101, A_101))))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.23/1.47  tff(c_974, plain, (![A_162, C_163, D_164]: (u1_struct_0(A_162)=C_163 | g1_orders_2(C_163, D_164)!=A_162 | ~m1_subset_1(u1_orders_2(A_162), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_162), u1_struct_0(A_162)))) | ~v1_orders_2(A_162) | ~l1_orders_2(A_162))), inference(superposition, [status(thm), theory('equality')], [c_2, c_530])).
% 3.23/1.47  tff(c_982, plain, (![A_162, A_9]: (u1_struct_0(A_162)=A_9 | k2_yellow_1(A_9)!=A_162 | ~m1_subset_1(u1_orders_2(A_162), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_162), u1_struct_0(A_162)))) | ~v1_orders_2(A_162) | ~l1_orders_2(A_162))), inference(superposition, [status(thm), theory('equality')], [c_10, c_974])).
% 3.23/1.47  tff(c_992, plain, (![A_9]: (u1_struct_0(k2_yellow_1(A_9))=A_9 | ~m1_subset_1(u1_orders_2(k2_yellow_1(A_9)), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k2_yellow_1(A_9)), u1_struct_0(k2_yellow_1(A_9))))) | ~v1_orders_2(k2_yellow_1(A_9)) | ~l1_orders_2(k2_yellow_1(A_9)))), inference(reflexivity, [status(thm), theory('equality')], [c_982])).
% 3.23/1.47  tff(c_1000, plain, (![A_171]: (u1_struct_0(k2_yellow_1(A_171))=A_171 | ~m1_subset_1(u1_orders_2(k2_yellow_1(A_171)), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k2_yellow_1(A_171)), u1_struct_0(k2_yellow_1(A_171))))))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_12, c_992])).
% 3.23/1.47  tff(c_1018, plain, (![A_171]: (u1_struct_0(k2_yellow_1(A_171))=A_171 | ~l1_orders_2(k2_yellow_1(A_171)))), inference(resolution, [status(thm)], [c_4, c_1000])).
% 3.23/1.47  tff(c_1028, plain, (![A_171]: (u1_struct_0(k2_yellow_1(A_171))=A_171)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_1018])).
% 3.23/1.47  tff(c_56, plain, (![C_20, A_21, D_22, B_23]: (C_20=A_21 | g1_orders_2(C_20, D_22)!=g1_orders_2(A_21, B_23) | ~m1_subset_1(B_23, k1_zfmisc_1(k2_zfmisc_1(A_21, A_21))))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.23/1.47  tff(c_65, plain, (![A_25, A_24, B_26]: (A_25=A_24 | k2_yellow_1(A_24)!=g1_orders_2(A_25, B_26) | ~m1_subset_1(B_26, k1_zfmisc_1(k2_zfmisc_1(A_25, A_25))))), inference(superposition, [status(thm), theory('equality')], [c_10, c_56])).
% 3.23/1.47  tff(c_67, plain, (![A_1, A_24]: (u1_struct_0(A_1)=A_24 | k2_yellow_1(A_24)!=A_1 | ~m1_subset_1(u1_orders_2(A_1), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1), u1_struct_0(A_1)))) | ~v1_orders_2(A_1) | ~l1_orders_2(A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_65])).
% 3.23/1.47  tff(c_152, plain, (![A_24]: (u1_struct_0(k2_yellow_1(A_24))=A_24 | ~m1_subset_1(u1_orders_2(k2_yellow_1(A_24)), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k2_yellow_1(A_24)), u1_struct_0(k2_yellow_1(A_24))))) | ~v1_orders_2(k2_yellow_1(A_24)) | ~l1_orders_2(k2_yellow_1(A_24)))), inference(reflexivity, [status(thm), theory('equality')], [c_67])).
% 3.23/1.47  tff(c_156, plain, (![A_59]: (u1_struct_0(k2_yellow_1(A_59))=A_59 | ~m1_subset_1(u1_orders_2(k2_yellow_1(A_59)), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k2_yellow_1(A_59)), u1_struct_0(k2_yellow_1(A_59))))))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_12, c_152])).
% 3.23/1.47  tff(c_159, plain, (![A_59]: (u1_struct_0(k2_yellow_1(A_59))=A_59 | ~l1_orders_2(k2_yellow_1(A_59)))), inference(resolution, [status(thm)], [c_4, c_156])).
% 3.23/1.47  tff(c_162, plain, (![A_59]: (u1_struct_0(k2_yellow_1(A_59))=A_59)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_159])).
% 3.23/1.47  tff(c_165, plain, (![A_60]: (u1_struct_0(k2_yellow_1(A_60))=A_60)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_159])).
% 3.23/1.47  tff(c_171, plain, (![A_60]: (m1_subset_1(u1_orders_2(k2_yellow_1(A_60)), k1_zfmisc_1(k2_zfmisc_1(A_60, u1_struct_0(k2_yellow_1(A_60))))) | ~l1_orders_2(k2_yellow_1(A_60)))), inference(superposition, [status(thm), theory('equality')], [c_165, c_4])).
% 3.23/1.47  tff(c_183, plain, (![A_60]: (m1_subset_1(u1_orders_2(k2_yellow_1(A_60)), k1_zfmisc_1(k2_zfmisc_1(A_60, A_60))))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_162, c_171])).
% 3.23/1.47  tff(c_43, plain, (![D_16, B_17, C_18, A_19]: (D_16=B_17 | g1_orders_2(C_18, D_16)!=g1_orders_2(A_19, B_17) | ~m1_subset_1(B_17, k1_zfmisc_1(k2_zfmisc_1(A_19, A_19))))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.23/1.47  tff(c_75, plain, (![A_29, B_30, A_31]: (k1_yellow_1(A_29)=B_30 | k2_yellow_1(A_29)!=g1_orders_2(A_31, B_30) | ~m1_subset_1(B_30, k1_zfmisc_1(k2_zfmisc_1(A_31, A_31))))), inference(superposition, [status(thm), theory('equality')], [c_10, c_43])).
% 3.23/1.47  tff(c_77, plain, (![A_1, A_29]: (u1_orders_2(A_1)=k1_yellow_1(A_29) | k2_yellow_1(A_29)!=A_1 | ~m1_subset_1(u1_orders_2(A_1), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1), u1_struct_0(A_1)))) | ~v1_orders_2(A_1) | ~l1_orders_2(A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_75])).
% 3.23/1.47  tff(c_447, plain, (![A_29]: (u1_orders_2(k2_yellow_1(A_29))=k1_yellow_1(A_29) | ~m1_subset_1(u1_orders_2(k2_yellow_1(A_29)), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k2_yellow_1(A_29)), u1_struct_0(k2_yellow_1(A_29))))) | ~v1_orders_2(k2_yellow_1(A_29)) | ~l1_orders_2(k2_yellow_1(A_29)))), inference(reflexivity, [status(thm), theory('equality')], [c_77])).
% 3.23/1.47  tff(c_449, plain, (![A_29]: (u1_orders_2(k2_yellow_1(A_29))=k1_yellow_1(A_29))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_12, c_183, c_162, c_162, c_447])).
% 3.23/1.47  tff(c_16, plain, (u1_struct_0(k2_yellow_1('#skF_2'))!='#skF_2' | u1_orders_2(k2_yellow_1('#skF_1'))!=k1_yellow_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.23/1.47  tff(c_28, plain, (u1_orders_2(k2_yellow_1('#skF_1'))!=k1_yellow_1('#skF_1')), inference(splitLeft, [status(thm)], [c_16])).
% 3.23/1.47  tff(c_464, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_449, c_28])).
% 3.23/1.47  tff(c_465, plain, (u1_struct_0(k2_yellow_1('#skF_2'))!='#skF_2'), inference(splitRight, [status(thm)], [c_16])).
% 3.23/1.47  tff(c_1043, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1028, c_465])).
% 3.23/1.47  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.23/1.47  
% 3.23/1.47  Inference rules
% 3.23/1.47  ----------------------
% 3.23/1.47  #Ref     : 32
% 3.23/1.47  #Sup     : 240
% 3.23/1.47  #Fact    : 0
% 3.23/1.47  #Define  : 0
% 3.23/1.47  #Split   : 2
% 3.23/1.47  #Chain   : 0
% 3.23/1.47  #Close   : 0
% 3.23/1.47  
% 3.23/1.47  Ordering : KBO
% 3.23/1.47  
% 3.23/1.47  Simplification rules
% 3.23/1.47  ----------------------
% 3.23/1.47  #Subsume      : 56
% 3.23/1.47  #Demod        : 165
% 3.23/1.47  #Tautology    : 91
% 3.23/1.47  #SimpNegUnit  : 0
% 3.23/1.47  #BackRed      : 22
% 3.23/1.47  
% 3.23/1.47  #Partial instantiations: 0
% 3.23/1.47  #Strategies tried      : 1
% 3.23/1.47  
% 3.23/1.47  Timing (in seconds)
% 3.23/1.47  ----------------------
% 3.23/1.47  Preprocessing        : 0.27
% 3.23/1.47  Parsing              : 0.15
% 3.23/1.47  CNF conversion       : 0.02
% 3.23/1.47  Main loop            : 0.44
% 3.23/1.47  Inferencing          : 0.17
% 3.23/1.47  Reduction            : 0.12
% 3.23/1.47  Demodulation         : 0.08
% 3.23/1.47  BG Simplification    : 0.02
% 3.23/1.47  Subsumption          : 0.10
% 3.23/1.47  Abstraction          : 0.02
% 3.23/1.47  MUC search           : 0.00
% 3.23/1.47  Cooper               : 0.00
% 3.23/1.47  Total                : 0.74
% 3.23/1.47  Index Insertion      : 0.00
% 3.23/1.47  Index Deletion       : 0.00
% 3.23/1.47  Index Matching       : 0.00
% 3.23/1.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
