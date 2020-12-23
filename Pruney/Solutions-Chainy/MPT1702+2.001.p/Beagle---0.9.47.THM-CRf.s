%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:22 EST 2020

% Result     : Theorem 2.14s
% Output     : CNFRefutation 2.14s
% Verified   : 
% Statistics : Number of formulae       :   50 ( 104 expanded)
%              Number of leaves         :   19 (  42 expanded)
%              Depth                    :   11
%              Number of atoms          :  100 ( 265 expanded)
%              Number of equality atoms :   15 (  29 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_subset_1 > m1_pre_topc > v1_pre_topc > l1_pre_topc > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(g1_pre_topc,type,(
    g1_pre_topc: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_77,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_pre_topc(B,A)
           => ( v1_pre_topc(g1_pre_topc(u1_struct_0(B),u1_pre_topc(B)))
              & m1_pre_topc(g1_pre_topc(u1_struct_0(B),u1_pre_topc(B)),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_tmap_1)).

tff(f_44,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_48,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_subset_1(u1_pre_topc(A),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( v1_pre_topc(g1_pre_topc(A,B))
        & l1_pre_topc(g1_pre_topc(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_g1_pre_topc)).

tff(f_31,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( v1_pre_topc(A)
       => A = g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).

tff(f_67,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( l1_pre_topc(B)
         => ! [C] :
              ( l1_pre_topc(C)
             => ! [D] :
                  ( l1_pre_topc(D)
                 => ( ( g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)) = g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))
                      & g1_pre_topc(u1_struct_0(C),u1_pre_topc(C)) = g1_pre_topc(u1_struct_0(D),u1_pre_topc(D))
                      & m1_pre_topc(C,A) )
                   => m1_pre_topc(D,B) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_pre_topc)).

tff(c_18,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_16,plain,(
    m1_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_19,plain,(
    ! [B_24,A_25] :
      ( l1_pre_topc(B_24)
      | ~ m1_pre_topc(B_24,A_25)
      | ~ l1_pre_topc(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_22,plain,
    ( l1_pre_topc('#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_16,c_19])).

tff(c_25,plain,(
    l1_pre_topc('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_22])).

tff(c_27,plain,(
    ! [A_28] :
      ( m1_subset_1(u1_pre_topc(A_28),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_28))))
      | ~ l1_pre_topc(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_6,plain,(
    ! [A_2,B_3] :
      ( v1_pre_topc(g1_pre_topc(A_2,B_3))
      | ~ m1_subset_1(B_3,k1_zfmisc_1(k1_zfmisc_1(A_2))) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_31,plain,(
    ! [A_28] :
      ( v1_pre_topc(g1_pre_topc(u1_struct_0(A_28),u1_pre_topc(A_28)))
      | ~ l1_pre_topc(A_28) ) ),
    inference(resolution,[status(thm)],[c_27,c_6])).

tff(c_14,plain,
    ( ~ m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')),'#skF_1')
    | ~ v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_39,plain,(
    ~ v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_14])).

tff(c_42,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_31,c_39])).

tff(c_46,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_25,c_42])).

tff(c_47,plain,(
    ~ m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_14])).

tff(c_10,plain,(
    ! [A_7] :
      ( m1_subset_1(u1_pre_topc(A_7),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_7))))
      | ~ l1_pre_topc(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_33,plain,(
    ! [A_30,B_31] :
      ( l1_pre_topc(g1_pre_topc(A_30,B_31))
      | ~ m1_subset_1(B_31,k1_zfmisc_1(k1_zfmisc_1(A_30))) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_37,plain,(
    ! [A_7] :
      ( l1_pre_topc(g1_pre_topc(u1_struct_0(A_7),u1_pre_topc(A_7)))
      | ~ l1_pre_topc(A_7) ) ),
    inference(resolution,[status(thm)],[c_10,c_33])).

tff(c_48,plain,(
    v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_14])).

tff(c_2,plain,(
    ! [A_1] :
      ( g1_pre_topc(u1_struct_0(A_1),u1_pre_topc(A_1)) = A_1
      | ~ v1_pre_topc(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_74,plain,(
    ! [D_34,B_35,C_36,A_37] :
      ( m1_pre_topc(D_34,B_35)
      | ~ m1_pre_topc(C_36,A_37)
      | g1_pre_topc(u1_struct_0(D_34),u1_pre_topc(D_34)) != g1_pre_topc(u1_struct_0(C_36),u1_pre_topc(C_36))
      | g1_pre_topc(u1_struct_0(B_35),u1_pre_topc(B_35)) != g1_pre_topc(u1_struct_0(A_37),u1_pre_topc(A_37))
      | ~ l1_pre_topc(D_34)
      | ~ l1_pre_topc(C_36)
      | ~ l1_pre_topc(B_35)
      | ~ l1_pre_topc(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_76,plain,(
    ! [D_34,B_35] :
      ( m1_pre_topc(D_34,B_35)
      | g1_pre_topc(u1_struct_0(D_34),u1_pre_topc(D_34)) != g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))
      | g1_pre_topc(u1_struct_0(B_35),u1_pre_topc(B_35)) != g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))
      | ~ l1_pre_topc(D_34)
      | ~ l1_pre_topc('#skF_2')
      | ~ l1_pre_topc(B_35)
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_16,c_74])).

tff(c_85,plain,(
    ! [D_38,B_39] :
      ( m1_pre_topc(D_38,B_39)
      | g1_pre_topc(u1_struct_0(D_38),u1_pre_topc(D_38)) != g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))
      | g1_pre_topc(u1_struct_0(B_39),u1_pre_topc(B_39)) != g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))
      | ~ l1_pre_topc(D_38)
      | ~ l1_pre_topc(B_39) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_25,c_76])).

tff(c_87,plain,(
    ! [A_1,B_39] :
      ( m1_pre_topc(A_1,B_39)
      | g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) != A_1
      | g1_pre_topc(u1_struct_0(B_39),u1_pre_topc(B_39)) != g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))
      | ~ l1_pre_topc(A_1)
      | ~ l1_pre_topc(B_39)
      | ~ v1_pre_topc(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_85])).

tff(c_111,plain,(
    ! [B_39] :
      ( m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')),B_39)
      | g1_pre_topc(u1_struct_0(B_39),u1_pre_topc(B_39)) != g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ l1_pre_topc(B_39)
      | ~ v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_87])).

tff(c_113,plain,(
    ! [B_39] :
      ( m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')),B_39)
      | g1_pre_topc(u1_struct_0(B_39),u1_pre_topc(B_39)) != g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))
      | ~ l1_pre_topc(B_39)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_111])).

tff(c_130,plain,(
    ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_113])).

tff(c_136,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_37,c_130])).

tff(c_142,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_25,c_136])).

tff(c_143,plain,(
    ! [B_39] :
      ( m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')),B_39)
      | g1_pre_topc(u1_struct_0(B_39),u1_pre_topc(B_39)) != g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))
      | ~ l1_pre_topc(B_39) ) ),
    inference(splitRight,[status(thm)],[c_113])).

tff(c_152,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')),'#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_143])).

tff(c_154,plain,(
    m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_152])).

tff(c_156,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_47,c_154])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:38:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.14/1.29  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.14/1.29  
% 2.14/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.14/1.29  %$ m1_subset_1 > m1_pre_topc > v1_pre_topc > l1_pre_topc > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_2 > #skF_1
% 2.14/1.29  
% 2.14/1.29  %Foreground sorts:
% 2.14/1.29  
% 2.14/1.29  
% 2.14/1.29  %Background operators:
% 2.14/1.29  
% 2.14/1.29  
% 2.14/1.29  %Foreground operators:
% 2.14/1.29  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 2.14/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.14/1.29  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 2.14/1.29  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.14/1.29  tff('#skF_2', type, '#skF_2': $i).
% 2.14/1.29  tff('#skF_1', type, '#skF_1': $i).
% 2.14/1.29  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 2.14/1.29  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.14/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.14/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.14/1.29  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.14/1.29  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.14/1.29  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.14/1.29  
% 2.14/1.31  tff(f_77, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (v1_pre_topc(g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))) & m1_pre_topc(g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_tmap_1)).
% 2.14/1.31  tff(f_44, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 2.14/1.31  tff(f_48, axiom, (![A]: (l1_pre_topc(A) => m1_subset_1(u1_pre_topc(A), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 2.14/1.31  tff(f_37, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (v1_pre_topc(g1_pre_topc(A, B)) & l1_pre_topc(g1_pre_topc(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_g1_pre_topc)).
% 2.14/1.31  tff(f_31, axiom, (![A]: (l1_pre_topc(A) => (v1_pre_topc(A) => (A = g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', abstractness_v1_pre_topc)).
% 2.14/1.31  tff(f_67, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (![C]: (l1_pre_topc(C) => (![D]: (l1_pre_topc(D) => ((((g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)) = g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))) & (g1_pre_topc(u1_struct_0(C), u1_pre_topc(C)) = g1_pre_topc(u1_struct_0(D), u1_pre_topc(D)))) & m1_pre_topc(C, A)) => m1_pre_topc(D, B)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_pre_topc)).
% 2.14/1.31  tff(c_18, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.14/1.31  tff(c_16, plain, (m1_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.14/1.31  tff(c_19, plain, (![B_24, A_25]: (l1_pre_topc(B_24) | ~m1_pre_topc(B_24, A_25) | ~l1_pre_topc(A_25))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.14/1.31  tff(c_22, plain, (l1_pre_topc('#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_16, c_19])).
% 2.14/1.31  tff(c_25, plain, (l1_pre_topc('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_22])).
% 2.14/1.31  tff(c_27, plain, (![A_28]: (m1_subset_1(u1_pre_topc(A_28), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_28)))) | ~l1_pre_topc(A_28))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.14/1.31  tff(c_6, plain, (![A_2, B_3]: (v1_pre_topc(g1_pre_topc(A_2, B_3)) | ~m1_subset_1(B_3, k1_zfmisc_1(k1_zfmisc_1(A_2))))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.14/1.31  tff(c_31, plain, (![A_28]: (v1_pre_topc(g1_pre_topc(u1_struct_0(A_28), u1_pre_topc(A_28))) | ~l1_pre_topc(A_28))), inference(resolution, [status(thm)], [c_27, c_6])).
% 2.14/1.31  tff(c_14, plain, (~m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')), '#skF_1') | ~v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.14/1.31  tff(c_39, plain, (~v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(splitLeft, [status(thm)], [c_14])).
% 2.14/1.31  tff(c_42, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_31, c_39])).
% 2.14/1.31  tff(c_46, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_25, c_42])).
% 2.14/1.31  tff(c_47, plain, (~m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')), '#skF_1')), inference(splitRight, [status(thm)], [c_14])).
% 2.14/1.31  tff(c_10, plain, (![A_7]: (m1_subset_1(u1_pre_topc(A_7), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_7)))) | ~l1_pre_topc(A_7))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.14/1.31  tff(c_33, plain, (![A_30, B_31]: (l1_pre_topc(g1_pre_topc(A_30, B_31)) | ~m1_subset_1(B_31, k1_zfmisc_1(k1_zfmisc_1(A_30))))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.14/1.31  tff(c_37, plain, (![A_7]: (l1_pre_topc(g1_pre_topc(u1_struct_0(A_7), u1_pre_topc(A_7))) | ~l1_pre_topc(A_7))), inference(resolution, [status(thm)], [c_10, c_33])).
% 2.14/1.31  tff(c_48, plain, (v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(splitRight, [status(thm)], [c_14])).
% 2.14/1.31  tff(c_2, plain, (![A_1]: (g1_pre_topc(u1_struct_0(A_1), u1_pre_topc(A_1))=A_1 | ~v1_pre_topc(A_1) | ~l1_pre_topc(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.14/1.31  tff(c_74, plain, (![D_34, B_35, C_36, A_37]: (m1_pre_topc(D_34, B_35) | ~m1_pre_topc(C_36, A_37) | g1_pre_topc(u1_struct_0(D_34), u1_pre_topc(D_34))!=g1_pre_topc(u1_struct_0(C_36), u1_pre_topc(C_36)) | g1_pre_topc(u1_struct_0(B_35), u1_pre_topc(B_35))!=g1_pre_topc(u1_struct_0(A_37), u1_pre_topc(A_37)) | ~l1_pre_topc(D_34) | ~l1_pre_topc(C_36) | ~l1_pre_topc(B_35) | ~l1_pre_topc(A_37))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.14/1.31  tff(c_76, plain, (![D_34, B_35]: (m1_pre_topc(D_34, B_35) | g1_pre_topc(u1_struct_0(D_34), u1_pre_topc(D_34))!=g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')) | g1_pre_topc(u1_struct_0(B_35), u1_pre_topc(B_35))!=g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')) | ~l1_pre_topc(D_34) | ~l1_pre_topc('#skF_2') | ~l1_pre_topc(B_35) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_16, c_74])).
% 2.14/1.31  tff(c_85, plain, (![D_38, B_39]: (m1_pre_topc(D_38, B_39) | g1_pre_topc(u1_struct_0(D_38), u1_pre_topc(D_38))!=g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')) | g1_pre_topc(u1_struct_0(B_39), u1_pre_topc(B_39))!=g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')) | ~l1_pre_topc(D_38) | ~l1_pre_topc(B_39))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_25, c_76])).
% 2.14/1.31  tff(c_87, plain, (![A_1, B_39]: (m1_pre_topc(A_1, B_39) | g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))!=A_1 | g1_pre_topc(u1_struct_0(B_39), u1_pre_topc(B_39))!=g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')) | ~l1_pre_topc(A_1) | ~l1_pre_topc(B_39) | ~v1_pre_topc(A_1) | ~l1_pre_topc(A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_85])).
% 2.14/1.31  tff(c_111, plain, (![B_39]: (m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')), B_39) | g1_pre_topc(u1_struct_0(B_39), u1_pre_topc(B_39))!=g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~l1_pre_topc(B_39) | ~v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))), inference(reflexivity, [status(thm), theory('equality')], [c_87])).
% 2.14/1.31  tff(c_113, plain, (![B_39]: (m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')), B_39) | g1_pre_topc(u1_struct_0(B_39), u1_pre_topc(B_39))!=g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')) | ~l1_pre_topc(B_39) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_111])).
% 2.14/1.31  tff(c_130, plain, (~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(splitLeft, [status(thm)], [c_113])).
% 2.14/1.31  tff(c_136, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_37, c_130])).
% 2.14/1.31  tff(c_142, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_25, c_136])).
% 2.14/1.31  tff(c_143, plain, (![B_39]: (m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')), B_39) | g1_pre_topc(u1_struct_0(B_39), u1_pre_topc(B_39))!=g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')) | ~l1_pre_topc(B_39))), inference(splitRight, [status(thm)], [c_113])).
% 2.14/1.31  tff(c_152, plain, (m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')), '#skF_1') | ~l1_pre_topc('#skF_1')), inference(reflexivity, [status(thm), theory('equality')], [c_143])).
% 2.14/1.31  tff(c_154, plain, (m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_152])).
% 2.14/1.31  tff(c_156, plain, $false, inference(negUnitSimplification, [status(thm)], [c_47, c_154])).
% 2.14/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.14/1.31  
% 2.14/1.31  Inference rules
% 2.14/1.31  ----------------------
% 2.14/1.31  #Ref     : 5
% 2.14/1.31  #Sup     : 20
% 2.14/1.31  #Fact    : 0
% 2.14/1.31  #Define  : 0
% 2.14/1.31  #Split   : 3
% 2.14/1.31  #Chain   : 0
% 2.14/1.31  #Close   : 0
% 2.14/1.31  
% 2.14/1.31  Ordering : KBO
% 2.14/1.31  
% 2.14/1.31  Simplification rules
% 2.14/1.31  ----------------------
% 2.14/1.31  #Subsume      : 5
% 2.14/1.31  #Demod        : 21
% 2.14/1.31  #Tautology    : 6
% 2.14/1.31  #SimpNegUnit  : 1
% 2.14/1.31  #BackRed      : 0
% 2.14/1.31  
% 2.14/1.31  #Partial instantiations: 0
% 2.14/1.31  #Strategies tried      : 1
% 2.14/1.31  
% 2.14/1.31  Timing (in seconds)
% 2.14/1.31  ----------------------
% 2.14/1.31  Preprocessing        : 0.33
% 2.14/1.31  Parsing              : 0.20
% 2.14/1.31  CNF conversion       : 0.02
% 2.14/1.31  Main loop            : 0.18
% 2.14/1.31  Inferencing          : 0.08
% 2.14/1.31  Reduction            : 0.05
% 2.14/1.31  Demodulation         : 0.04
% 2.14/1.31  BG Simplification    : 0.01
% 2.14/1.31  Subsumption          : 0.04
% 2.14/1.31  Abstraction          : 0.01
% 2.14/1.31  MUC search           : 0.00
% 2.14/1.31  Cooper               : 0.00
% 2.14/1.31  Total                : 0.55
% 2.14/1.31  Index Insertion      : 0.00
% 2.14/1.31  Index Deletion       : 0.00
% 2.14/1.31  Index Matching       : 0.00
% 2.14/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
