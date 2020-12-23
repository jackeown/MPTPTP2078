%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:10 EST 2020

% Result     : Theorem 1.65s
% Output     : CNFRefutation 1.91s
% Verified   : 
% Statistics : Number of formulae       :   50 ( 118 expanded)
%              Number of leaves         :   19 (  45 expanded)
%              Depth                    :   12
%              Number of atoms          :   96 ( 275 expanded)
%              Number of equality atoms :   15 (  29 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    5 (   2 average)

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

tff(f_75,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_pre_topc(B,g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))
           => m1_pre_topc(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_pre_topc)).

tff(f_48,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_subset_1(u1_pre_topc(A),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( v1_pre_topc(g1_pre_topc(A,B))
        & l1_pre_topc(g1_pre_topc(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_g1_pre_topc)).

tff(f_44,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_31,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( v1_pre_topc(A)
       => A = g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_pre_topc)).

tff(c_14,plain,(
    ~ m1_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_18,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_10,plain,(
    ! [A_7] :
      ( m1_subset_1(u1_pre_topc(A_7),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_7))))
      | ~ l1_pre_topc(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_48,plain,(
    ! [A_34,B_35] :
      ( v1_pre_topc(g1_pre_topc(A_34,B_35))
      | ~ m1_subset_1(B_35,k1_zfmisc_1(k1_zfmisc_1(A_34))) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_52,plain,(
    ! [A_7] :
      ( v1_pre_topc(g1_pre_topc(u1_struct_0(A_7),u1_pre_topc(A_7)))
      | ~ l1_pre_topc(A_7) ) ),
    inference(resolution,[status(thm)],[c_10,c_48])).

tff(c_26,plain,(
    ! [A_28] :
      ( m1_subset_1(u1_pre_topc(A_28),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_28))))
      | ~ l1_pre_topc(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_4,plain,(
    ! [A_2,B_3] :
      ( l1_pre_topc(g1_pre_topc(A_2,B_3))
      | ~ m1_subset_1(B_3,k1_zfmisc_1(k1_zfmisc_1(A_2))) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_31,plain,(
    ! [A_29] :
      ( l1_pre_topc(g1_pre_topc(u1_struct_0(A_29),u1_pre_topc(A_29)))
      | ~ l1_pre_topc(A_29) ) ),
    inference(resolution,[status(thm)],[c_26,c_4])).

tff(c_16,plain,(
    m1_pre_topc('#skF_2',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_19,plain,(
    ! [B_24,A_25] :
      ( l1_pre_topc(B_24)
      | ~ m1_pre_topc(B_24,A_25)
      | ~ l1_pre_topc(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_23,plain,
    ( l1_pre_topc('#skF_2')
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_16,c_19])).

tff(c_24,plain,(
    ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_23])).

tff(c_34,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_31,c_24])).

tff(c_38,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_34])).

tff(c_40,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_23])).

tff(c_2,plain,(
    ! [A_1] :
      ( g1_pre_topc(u1_struct_0(A_1),u1_pre_topc(A_1)) = A_1
      | ~ v1_pre_topc(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_39,plain,(
    l1_pre_topc('#skF_2') ),
    inference(splitRight,[status(thm)],[c_23])).

tff(c_80,plain,(
    ! [D_38,B_39,C_40,A_41] :
      ( m1_pre_topc(D_38,B_39)
      | ~ m1_pre_topc(C_40,A_41)
      | g1_pre_topc(u1_struct_0(D_38),u1_pre_topc(D_38)) != g1_pre_topc(u1_struct_0(C_40),u1_pre_topc(C_40))
      | g1_pre_topc(u1_struct_0(B_39),u1_pre_topc(B_39)) != g1_pre_topc(u1_struct_0(A_41),u1_pre_topc(A_41))
      | ~ l1_pre_topc(D_38)
      | ~ l1_pre_topc(C_40)
      | ~ l1_pre_topc(B_39)
      | ~ l1_pre_topc(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_82,plain,(
    ! [D_38,B_39] :
      ( m1_pre_topc(D_38,B_39)
      | g1_pre_topc(u1_struct_0(D_38),u1_pre_topc(D_38)) != g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))
      | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))) != g1_pre_topc(u1_struct_0(B_39),u1_pre_topc(B_39))
      | ~ l1_pre_topc(D_38)
      | ~ l1_pre_topc('#skF_2')
      | ~ l1_pre_topc(B_39)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_16,c_80])).

tff(c_85,plain,(
    ! [D_38,B_39] :
      ( m1_pre_topc(D_38,B_39)
      | g1_pre_topc(u1_struct_0(D_38),u1_pre_topc(D_38)) != g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))
      | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))) != g1_pre_topc(u1_struct_0(B_39),u1_pre_topc(B_39))
      | ~ l1_pre_topc(D_38)
      | ~ l1_pre_topc(B_39) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_39,c_82])).

tff(c_88,plain,(
    ! [B_39] :
      ( m1_pre_topc('#skF_2',B_39)
      | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))) != g1_pre_topc(u1_struct_0(B_39),u1_pre_topc(B_39))
      | ~ l1_pre_topc('#skF_2')
      | ~ l1_pre_topc(B_39) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_85])).

tff(c_104,plain,(
    ! [B_44] :
      ( m1_pre_topc('#skF_2',B_44)
      | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))) != g1_pre_topc(u1_struct_0(B_44),u1_pre_topc(B_44))
      | ~ l1_pre_topc(B_44) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_39,c_88])).

tff(c_113,plain,(
    ! [B_44] :
      ( m1_pre_topc('#skF_2',B_44)
      | g1_pre_topc(u1_struct_0(B_44),u1_pre_topc(B_44)) != g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))
      | ~ l1_pre_topc(B_44)
      | ~ v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_104])).

tff(c_122,plain,(
    ! [B_44] :
      ( m1_pre_topc('#skF_2',B_44)
      | g1_pre_topc(u1_struct_0(B_44),u1_pre_topc(B_44)) != g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))
      | ~ l1_pre_topc(B_44)
      | ~ v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_113])).

tff(c_123,plain,(
    ~ v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_122])).

tff(c_126,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_52,c_123])).

tff(c_133,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_126])).

tff(c_134,plain,(
    ! [B_44] :
      ( m1_pre_topc('#skF_2',B_44)
      | g1_pre_topc(u1_struct_0(B_44),u1_pre_topc(B_44)) != g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))
      | ~ l1_pre_topc(B_44) ) ),
    inference(splitRight,[status(thm)],[c_122])).

tff(c_144,plain,
    ( m1_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_134])).

tff(c_146,plain,(
    m1_pre_topc('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_144])).

tff(c_148,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14,c_146])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n020.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 16:01:37 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.19/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.65/1.17  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.91/1.18  
% 1.91/1.18  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.91/1.18  %$ m1_subset_1 > m1_pre_topc > v1_pre_topc > l1_pre_topc > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_2 > #skF_1
% 1.91/1.18  
% 1.91/1.18  %Foreground sorts:
% 1.91/1.18  
% 1.91/1.18  
% 1.91/1.18  %Background operators:
% 1.91/1.18  
% 1.91/1.18  
% 1.91/1.18  %Foreground operators:
% 1.91/1.18  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 1.91/1.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.91/1.18  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 1.91/1.18  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 1.91/1.18  tff('#skF_2', type, '#skF_2': $i).
% 1.91/1.18  tff('#skF_1', type, '#skF_1': $i).
% 1.91/1.18  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 1.91/1.18  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.91/1.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.91/1.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.91/1.18  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 1.91/1.18  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 1.91/1.18  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.91/1.18  
% 1.91/1.19  tff(f_75, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))) => m1_pre_topc(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t59_pre_topc)).
% 1.91/1.19  tff(f_48, axiom, (![A]: (l1_pre_topc(A) => m1_subset_1(u1_pre_topc(A), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 1.91/1.19  tff(f_37, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (v1_pre_topc(g1_pre_topc(A, B)) & l1_pre_topc(g1_pre_topc(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_g1_pre_topc)).
% 1.91/1.19  tff(f_44, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 1.91/1.19  tff(f_31, axiom, (![A]: (l1_pre_topc(A) => (v1_pre_topc(A) => (A = g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', abstractness_v1_pre_topc)).
% 1.91/1.19  tff(f_67, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (![C]: (l1_pre_topc(C) => (![D]: (l1_pre_topc(D) => ((((g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)) = g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))) & (g1_pre_topc(u1_struct_0(C), u1_pre_topc(C)) = g1_pre_topc(u1_struct_0(D), u1_pre_topc(D)))) & m1_pre_topc(C, A)) => m1_pre_topc(D, B)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_pre_topc)).
% 1.91/1.19  tff(c_14, plain, (~m1_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_75])).
% 1.91/1.19  tff(c_18, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_75])).
% 1.91/1.19  tff(c_10, plain, (![A_7]: (m1_subset_1(u1_pre_topc(A_7), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_7)))) | ~l1_pre_topc(A_7))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.91/1.19  tff(c_48, plain, (![A_34, B_35]: (v1_pre_topc(g1_pre_topc(A_34, B_35)) | ~m1_subset_1(B_35, k1_zfmisc_1(k1_zfmisc_1(A_34))))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.91/1.19  tff(c_52, plain, (![A_7]: (v1_pre_topc(g1_pre_topc(u1_struct_0(A_7), u1_pre_topc(A_7))) | ~l1_pre_topc(A_7))), inference(resolution, [status(thm)], [c_10, c_48])).
% 1.91/1.19  tff(c_26, plain, (![A_28]: (m1_subset_1(u1_pre_topc(A_28), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_28)))) | ~l1_pre_topc(A_28))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.91/1.19  tff(c_4, plain, (![A_2, B_3]: (l1_pre_topc(g1_pre_topc(A_2, B_3)) | ~m1_subset_1(B_3, k1_zfmisc_1(k1_zfmisc_1(A_2))))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.91/1.19  tff(c_31, plain, (![A_29]: (l1_pre_topc(g1_pre_topc(u1_struct_0(A_29), u1_pre_topc(A_29))) | ~l1_pre_topc(A_29))), inference(resolution, [status(thm)], [c_26, c_4])).
% 1.91/1.19  tff(c_16, plain, (m1_pre_topc('#skF_2', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_75])).
% 1.91/1.19  tff(c_19, plain, (![B_24, A_25]: (l1_pre_topc(B_24) | ~m1_pre_topc(B_24, A_25) | ~l1_pre_topc(A_25))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.91/1.19  tff(c_23, plain, (l1_pre_topc('#skF_2') | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(resolution, [status(thm)], [c_16, c_19])).
% 1.91/1.19  tff(c_24, plain, (~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitLeft, [status(thm)], [c_23])).
% 1.91/1.19  tff(c_34, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_31, c_24])).
% 1.91/1.19  tff(c_38, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_34])).
% 1.91/1.19  tff(c_40, plain, (l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitRight, [status(thm)], [c_23])).
% 1.91/1.19  tff(c_2, plain, (![A_1]: (g1_pre_topc(u1_struct_0(A_1), u1_pre_topc(A_1))=A_1 | ~v1_pre_topc(A_1) | ~l1_pre_topc(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.91/1.19  tff(c_39, plain, (l1_pre_topc('#skF_2')), inference(splitRight, [status(thm)], [c_23])).
% 1.91/1.19  tff(c_80, plain, (![D_38, B_39, C_40, A_41]: (m1_pre_topc(D_38, B_39) | ~m1_pre_topc(C_40, A_41) | g1_pre_topc(u1_struct_0(D_38), u1_pre_topc(D_38))!=g1_pre_topc(u1_struct_0(C_40), u1_pre_topc(C_40)) | g1_pre_topc(u1_struct_0(B_39), u1_pre_topc(B_39))!=g1_pre_topc(u1_struct_0(A_41), u1_pre_topc(A_41)) | ~l1_pre_topc(D_38) | ~l1_pre_topc(C_40) | ~l1_pre_topc(B_39) | ~l1_pre_topc(A_41))), inference(cnfTransformation, [status(thm)], [f_67])).
% 1.91/1.19  tff(c_82, plain, (![D_38, B_39]: (m1_pre_topc(D_38, B_39) | g1_pre_topc(u1_struct_0(D_38), u1_pre_topc(D_38))!=g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')) | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))!=g1_pre_topc(u1_struct_0(B_39), u1_pre_topc(B_39)) | ~l1_pre_topc(D_38) | ~l1_pre_topc('#skF_2') | ~l1_pre_topc(B_39) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))), inference(resolution, [status(thm)], [c_16, c_80])).
% 1.91/1.19  tff(c_85, plain, (![D_38, B_39]: (m1_pre_topc(D_38, B_39) | g1_pre_topc(u1_struct_0(D_38), u1_pre_topc(D_38))!=g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')) | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))!=g1_pre_topc(u1_struct_0(B_39), u1_pre_topc(B_39)) | ~l1_pre_topc(D_38) | ~l1_pre_topc(B_39))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_39, c_82])).
% 1.91/1.19  tff(c_88, plain, (![B_39]: (m1_pre_topc('#skF_2', B_39) | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))!=g1_pre_topc(u1_struct_0(B_39), u1_pre_topc(B_39)) | ~l1_pre_topc('#skF_2') | ~l1_pre_topc(B_39))), inference(reflexivity, [status(thm), theory('equality')], [c_85])).
% 1.91/1.19  tff(c_104, plain, (![B_44]: (m1_pre_topc('#skF_2', B_44) | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))!=g1_pre_topc(u1_struct_0(B_44), u1_pre_topc(B_44)) | ~l1_pre_topc(B_44))), inference(demodulation, [status(thm), theory('equality')], [c_39, c_88])).
% 1.91/1.19  tff(c_113, plain, (![B_44]: (m1_pre_topc('#skF_2', B_44) | g1_pre_topc(u1_struct_0(B_44), u1_pre_topc(B_44))!=g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')) | ~l1_pre_topc(B_44) | ~v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_2, c_104])).
% 1.91/1.19  tff(c_122, plain, (![B_44]: (m1_pre_topc('#skF_2', B_44) | g1_pre_topc(u1_struct_0(B_44), u1_pre_topc(B_44))!=g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')) | ~l1_pre_topc(B_44) | ~v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_113])).
% 1.91/1.19  tff(c_123, plain, (~v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitLeft, [status(thm)], [c_122])).
% 1.91/1.19  tff(c_126, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_52, c_123])).
% 1.91/1.19  tff(c_133, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_126])).
% 1.91/1.19  tff(c_134, plain, (![B_44]: (m1_pre_topc('#skF_2', B_44) | g1_pre_topc(u1_struct_0(B_44), u1_pre_topc(B_44))!=g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')) | ~l1_pre_topc(B_44))), inference(splitRight, [status(thm)], [c_122])).
% 1.91/1.19  tff(c_144, plain, (m1_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(reflexivity, [status(thm), theory('equality')], [c_134])).
% 1.91/1.19  tff(c_146, plain, (m1_pre_topc('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_144])).
% 1.91/1.19  tff(c_148, plain, $false, inference(negUnitSimplification, [status(thm)], [c_14, c_146])).
% 1.91/1.19  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.91/1.19  
% 1.91/1.19  Inference rules
% 1.91/1.19  ----------------------
% 1.91/1.19  #Ref     : 3
% 1.91/1.19  #Sup     : 21
% 1.91/1.19  #Fact    : 0
% 1.91/1.19  #Define  : 0
% 1.91/1.19  #Split   : 2
% 1.91/1.19  #Chain   : 0
% 1.91/1.19  #Close   : 0
% 1.91/1.19  
% 1.91/1.19  Ordering : KBO
% 1.91/1.19  
% 1.91/1.19  Simplification rules
% 1.91/1.19  ----------------------
% 1.91/1.19  #Subsume      : 3
% 1.91/1.19  #Demod        : 16
% 1.91/1.19  #Tautology    : 6
% 1.91/1.19  #SimpNegUnit  : 3
% 1.91/1.19  #BackRed      : 0
% 1.91/1.19  
% 1.91/1.19  #Partial instantiations: 0
% 1.91/1.19  #Strategies tried      : 1
% 1.91/1.19  
% 1.91/1.19  Timing (in seconds)
% 1.91/1.19  ----------------------
% 1.91/1.20  Preprocessing        : 0.28
% 1.91/1.20  Parsing              : 0.16
% 1.91/1.20  CNF conversion       : 0.02
% 1.91/1.20  Main loop            : 0.16
% 1.91/1.20  Inferencing          : 0.06
% 1.91/1.20  Reduction            : 0.04
% 1.91/1.20  Demodulation         : 0.03
% 1.91/1.20  BG Simplification    : 0.01
% 1.91/1.20  Subsumption          : 0.03
% 1.91/1.20  Abstraction          : 0.01
% 1.91/1.20  MUC search           : 0.00
% 1.91/1.20  Cooper               : 0.00
% 1.91/1.20  Total                : 0.46
% 1.91/1.20  Index Insertion      : 0.00
% 1.91/1.20  Index Deletion       : 0.00
% 1.91/1.20  Index Matching       : 0.00
% 1.91/1.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
