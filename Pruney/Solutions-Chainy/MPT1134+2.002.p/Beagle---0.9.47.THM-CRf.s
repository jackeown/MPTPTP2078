%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:17 EST 2020

% Result     : Theorem 1.88s
% Output     : CNFRefutation 2.00s
% Verified   : 
% Statistics : Number of formulae       :   53 ( 120 expanded)
%              Number of leaves         :   19 (  45 expanded)
%              Depth                    :   13
%              Number of atoms          :  101 ( 323 expanded)
%              Number of equality atoms :   13 (  39 expanded)
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
            ( l1_pre_topc(B)
           => ( m1_pre_topc(A,B)
            <=> m1_pre_topc(A,g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_pre_topc)).

tff(f_41,axiom,(
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

tff(f_67,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))
         => m1_pre_topc(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_pre_topc)).

tff(f_31,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( v1_pre_topc(A)
       => A = g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).

tff(f_60,axiom,(
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
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_27,plain,(
    ! [A_28] :
      ( m1_subset_1(u1_pre_topc(A_28),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_28))))
      | ~ l1_pre_topc(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_6,plain,(
    ! [A_2,B_3] :
      ( v1_pre_topc(g1_pre_topc(A_2,B_3))
      | ~ m1_subset_1(B_3,k1_zfmisc_1(k1_zfmisc_1(A_2))) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_35,plain,(
    ! [A_28] :
      ( v1_pre_topc(g1_pre_topc(u1_struct_0(A_28),u1_pre_topc(A_28)))
      | ~ l1_pre_topc(A_28) ) ),
    inference(resolution,[status(thm)],[c_27,c_6])).

tff(c_4,plain,(
    ! [A_2,B_3] :
      ( l1_pre_topc(g1_pre_topc(A_2,B_3))
      | ~ m1_subset_1(B_3,k1_zfmisc_1(k1_zfmisc_1(A_2))) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_34,plain,(
    ! [A_28] :
      ( l1_pre_topc(g1_pre_topc(u1_struct_0(A_28),u1_pre_topc(A_28)))
      | ~ l1_pre_topc(A_28) ) ),
    inference(resolution,[status(thm)],[c_27,c_4])).

tff(c_24,plain,
    ( m1_pre_topc('#skF_1','#skF_2')
    | m1_pre_topc('#skF_1',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_36,plain,(
    m1_pre_topc('#skF_1',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_24])).

tff(c_18,plain,
    ( ~ m1_pre_topc('#skF_1',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ m1_pre_topc('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_40,plain,(
    ~ m1_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_18])).

tff(c_62,plain,(
    ! [B_32,A_33] :
      ( m1_pre_topc(B_32,A_33)
      | ~ m1_pre_topc(B_32,g1_pre_topc(u1_struct_0(A_33),u1_pre_topc(A_33)))
      | ~ l1_pre_topc(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_68,plain,
    ( m1_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_36,c_62])).

tff(c_71,plain,(
    m1_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_68])).

tff(c_73,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_71])).

tff(c_75,plain,(
    ~ m1_pre_topc('#skF_1',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_2,plain,(
    ! [A_1] :
      ( g1_pre_topc(u1_struct_0(A_1),u1_pre_topc(A_1)) = A_1
      | ~ v1_pre_topc(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_16,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_74,plain,(
    m1_pre_topc('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_104,plain,(
    ! [D_39,B_40,C_41,A_42] :
      ( m1_pre_topc(D_39,B_40)
      | ~ m1_pre_topc(C_41,A_42)
      | g1_pre_topc(u1_struct_0(D_39),u1_pre_topc(D_39)) != g1_pre_topc(u1_struct_0(C_41),u1_pre_topc(C_41))
      | g1_pre_topc(u1_struct_0(B_40),u1_pre_topc(B_40)) != g1_pre_topc(u1_struct_0(A_42),u1_pre_topc(A_42))
      | ~ l1_pre_topc(D_39)
      | ~ l1_pre_topc(C_41)
      | ~ l1_pre_topc(B_40)
      | ~ l1_pre_topc(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_106,plain,(
    ! [D_39,B_40] :
      ( m1_pre_topc(D_39,B_40)
      | g1_pre_topc(u1_struct_0(D_39),u1_pre_topc(D_39)) != g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))
      | g1_pre_topc(u1_struct_0(B_40),u1_pre_topc(B_40)) != g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))
      | ~ l1_pre_topc(D_39)
      | ~ l1_pre_topc('#skF_1')
      | ~ l1_pre_topc(B_40)
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_74,c_104])).

tff(c_109,plain,(
    ! [D_39,B_40] :
      ( m1_pre_topc(D_39,B_40)
      | g1_pre_topc(u1_struct_0(D_39),u1_pre_topc(D_39)) != g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))
      | g1_pre_topc(u1_struct_0(B_40),u1_pre_topc(B_40)) != g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))
      | ~ l1_pre_topc(D_39)
      | ~ l1_pre_topc(B_40) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_16,c_106])).

tff(c_112,plain,(
    ! [B_40] :
      ( m1_pre_topc('#skF_1',B_40)
      | g1_pre_topc(u1_struct_0(B_40),u1_pre_topc(B_40)) != g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))
      | ~ l1_pre_topc('#skF_1')
      | ~ l1_pre_topc(B_40) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_109])).

tff(c_128,plain,(
    ! [B_45] :
      ( m1_pre_topc('#skF_1',B_45)
      | g1_pre_topc(u1_struct_0(B_45),u1_pre_topc(B_45)) != g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))
      | ~ l1_pre_topc(B_45) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_112])).

tff(c_131,plain,(
    ! [A_1] :
      ( m1_pre_topc('#skF_1',A_1)
      | g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) != A_1
      | ~ l1_pre_topc(A_1)
      | ~ v1_pre_topc(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_128])).

tff(c_140,plain,
    ( m1_pre_topc('#skF_1',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_131])).

tff(c_141,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_140])).

tff(c_149,plain,(
    ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_141])).

tff(c_152,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_149])).

tff(c_159,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_152])).

tff(c_161,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_141])).

tff(c_160,plain,
    ( ~ v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_141])).

tff(c_168,plain,(
    ~ v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_161,c_160])).

tff(c_171,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_35,c_168])).

tff(c_178,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_171])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n022.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 17:19:10 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.88/1.11  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.88/1.11  
% 1.88/1.11  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.88/1.11  %$ m1_subset_1 > m1_pre_topc > v1_pre_topc > l1_pre_topc > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_2 > #skF_1
% 1.88/1.11  
% 1.88/1.11  %Foreground sorts:
% 1.88/1.11  
% 1.88/1.11  
% 1.88/1.11  %Background operators:
% 1.88/1.11  
% 1.88/1.11  
% 1.88/1.11  %Foreground operators:
% 1.88/1.11  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 1.88/1.11  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.88/1.11  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 1.88/1.11  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 1.88/1.11  tff('#skF_2', type, '#skF_2': $i).
% 1.88/1.11  tff('#skF_1', type, '#skF_1': $i).
% 1.88/1.11  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 1.88/1.11  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.88/1.11  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.88/1.11  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.88/1.11  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 1.88/1.11  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 1.88/1.11  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.88/1.11  
% 2.00/1.13  tff(f_77, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (m1_pre_topc(A, B) <=> m1_pre_topc(A, g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_pre_topc)).
% 2.00/1.13  tff(f_41, axiom, (![A]: (l1_pre_topc(A) => m1_subset_1(u1_pre_topc(A), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 2.00/1.13  tff(f_37, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (v1_pre_topc(g1_pre_topc(A, B)) & l1_pre_topc(g1_pre_topc(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_g1_pre_topc)).
% 2.00/1.13  tff(f_67, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))) => m1_pre_topc(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t59_pre_topc)).
% 2.00/1.13  tff(f_31, axiom, (![A]: (l1_pre_topc(A) => (v1_pre_topc(A) => (A = g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', abstractness_v1_pre_topc)).
% 2.00/1.13  tff(f_60, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (![C]: (l1_pre_topc(C) => (![D]: (l1_pre_topc(D) => ((((g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)) = g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))) & (g1_pre_topc(u1_struct_0(C), u1_pre_topc(C)) = g1_pre_topc(u1_struct_0(D), u1_pre_topc(D)))) & m1_pre_topc(C, A)) => m1_pre_topc(D, B)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_pre_topc)).
% 2.00/1.13  tff(c_14, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.00/1.13  tff(c_27, plain, (![A_28]: (m1_subset_1(u1_pre_topc(A_28), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_28)))) | ~l1_pre_topc(A_28))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.00/1.13  tff(c_6, plain, (![A_2, B_3]: (v1_pre_topc(g1_pre_topc(A_2, B_3)) | ~m1_subset_1(B_3, k1_zfmisc_1(k1_zfmisc_1(A_2))))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.00/1.13  tff(c_35, plain, (![A_28]: (v1_pre_topc(g1_pre_topc(u1_struct_0(A_28), u1_pre_topc(A_28))) | ~l1_pre_topc(A_28))), inference(resolution, [status(thm)], [c_27, c_6])).
% 2.00/1.13  tff(c_4, plain, (![A_2, B_3]: (l1_pre_topc(g1_pre_topc(A_2, B_3)) | ~m1_subset_1(B_3, k1_zfmisc_1(k1_zfmisc_1(A_2))))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.00/1.13  tff(c_34, plain, (![A_28]: (l1_pre_topc(g1_pre_topc(u1_struct_0(A_28), u1_pre_topc(A_28))) | ~l1_pre_topc(A_28))), inference(resolution, [status(thm)], [c_27, c_4])).
% 2.00/1.13  tff(c_24, plain, (m1_pre_topc('#skF_1', '#skF_2') | m1_pre_topc('#skF_1', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.00/1.13  tff(c_36, plain, (m1_pre_topc('#skF_1', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(splitLeft, [status(thm)], [c_24])).
% 2.00/1.13  tff(c_18, plain, (~m1_pre_topc('#skF_1', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~m1_pre_topc('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.00/1.13  tff(c_40, plain, (~m1_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_18])).
% 2.00/1.13  tff(c_62, plain, (![B_32, A_33]: (m1_pre_topc(B_32, A_33) | ~m1_pre_topc(B_32, g1_pre_topc(u1_struct_0(A_33), u1_pre_topc(A_33))) | ~l1_pre_topc(A_33))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.00/1.13  tff(c_68, plain, (m1_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_36, c_62])).
% 2.00/1.13  tff(c_71, plain, (m1_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_68])).
% 2.00/1.13  tff(c_73, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_71])).
% 2.00/1.13  tff(c_75, plain, (~m1_pre_topc('#skF_1', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(splitRight, [status(thm)], [c_24])).
% 2.00/1.13  tff(c_2, plain, (![A_1]: (g1_pre_topc(u1_struct_0(A_1), u1_pre_topc(A_1))=A_1 | ~v1_pre_topc(A_1) | ~l1_pre_topc(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.00/1.13  tff(c_16, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.00/1.13  tff(c_74, plain, (m1_pre_topc('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_24])).
% 2.00/1.13  tff(c_104, plain, (![D_39, B_40, C_41, A_42]: (m1_pre_topc(D_39, B_40) | ~m1_pre_topc(C_41, A_42) | g1_pre_topc(u1_struct_0(D_39), u1_pre_topc(D_39))!=g1_pre_topc(u1_struct_0(C_41), u1_pre_topc(C_41)) | g1_pre_topc(u1_struct_0(B_40), u1_pre_topc(B_40))!=g1_pre_topc(u1_struct_0(A_42), u1_pre_topc(A_42)) | ~l1_pre_topc(D_39) | ~l1_pre_topc(C_41) | ~l1_pre_topc(B_40) | ~l1_pre_topc(A_42))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.00/1.13  tff(c_106, plain, (![D_39, B_40]: (m1_pre_topc(D_39, B_40) | g1_pre_topc(u1_struct_0(D_39), u1_pre_topc(D_39))!=g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')) | g1_pre_topc(u1_struct_0(B_40), u1_pre_topc(B_40))!=g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')) | ~l1_pre_topc(D_39) | ~l1_pre_topc('#skF_1') | ~l1_pre_topc(B_40) | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_74, c_104])).
% 2.00/1.13  tff(c_109, plain, (![D_39, B_40]: (m1_pre_topc(D_39, B_40) | g1_pre_topc(u1_struct_0(D_39), u1_pre_topc(D_39))!=g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')) | g1_pre_topc(u1_struct_0(B_40), u1_pre_topc(B_40))!=g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')) | ~l1_pre_topc(D_39) | ~l1_pre_topc(B_40))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_16, c_106])).
% 2.00/1.13  tff(c_112, plain, (![B_40]: (m1_pre_topc('#skF_1', B_40) | g1_pre_topc(u1_struct_0(B_40), u1_pre_topc(B_40))!=g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')) | ~l1_pre_topc('#skF_1') | ~l1_pre_topc(B_40))), inference(reflexivity, [status(thm), theory('equality')], [c_109])).
% 2.00/1.13  tff(c_128, plain, (![B_45]: (m1_pre_topc('#skF_1', B_45) | g1_pre_topc(u1_struct_0(B_45), u1_pre_topc(B_45))!=g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')) | ~l1_pre_topc(B_45))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_112])).
% 2.00/1.13  tff(c_131, plain, (![A_1]: (m1_pre_topc('#skF_1', A_1) | g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))!=A_1 | ~l1_pre_topc(A_1) | ~v1_pre_topc(A_1) | ~l1_pre_topc(A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_128])).
% 2.00/1.13  tff(c_140, plain, (m1_pre_topc('#skF_1', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(reflexivity, [status(thm), theory('equality')], [c_131])).
% 2.00/1.13  tff(c_141, plain, (~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_75, c_140])).
% 2.00/1.13  tff(c_149, plain, (~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(splitLeft, [status(thm)], [c_141])).
% 2.00/1.13  tff(c_152, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_34, c_149])).
% 2.00/1.13  tff(c_159, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_152])).
% 2.00/1.13  tff(c_161, plain, (l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(splitRight, [status(thm)], [c_141])).
% 2.00/1.13  tff(c_160, plain, (~v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(splitRight, [status(thm)], [c_141])).
% 2.00/1.13  tff(c_168, plain, (~v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_161, c_160])).
% 2.00/1.13  tff(c_171, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_35, c_168])).
% 2.00/1.13  tff(c_178, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_171])).
% 2.00/1.13  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.00/1.13  
% 2.00/1.13  Inference rules
% 2.00/1.13  ----------------------
% 2.00/1.13  #Ref     : 3
% 2.00/1.13  #Sup     : 26
% 2.00/1.13  #Fact    : 0
% 2.00/1.13  #Define  : 0
% 2.00/1.13  #Split   : 3
% 2.00/1.13  #Chain   : 0
% 2.00/1.13  #Close   : 0
% 2.00/1.13  
% 2.00/1.13  Ordering : KBO
% 2.00/1.13  
% 2.00/1.13  Simplification rules
% 2.00/1.13  ----------------------
% 2.00/1.13  #Subsume      : 4
% 2.00/1.13  #Demod        : 19
% 2.00/1.13  #Tautology    : 13
% 2.00/1.13  #SimpNegUnit  : 3
% 2.00/1.13  #BackRed      : 0
% 2.00/1.13  
% 2.00/1.13  #Partial instantiations: 0
% 2.00/1.13  #Strategies tried      : 1
% 2.00/1.13  
% 2.00/1.13  Timing (in seconds)
% 2.00/1.13  ----------------------
% 2.00/1.13  Preprocessing        : 0.28
% 2.00/1.13  Parsing              : 0.16
% 2.00/1.13  CNF conversion       : 0.02
% 2.00/1.13  Main loop            : 0.17
% 2.00/1.13  Inferencing          : 0.07
% 2.00/1.13  Reduction            : 0.04
% 2.00/1.13  Demodulation         : 0.03
% 2.00/1.13  BG Simplification    : 0.01
% 2.00/1.13  Subsumption          : 0.03
% 2.00/1.13  Abstraction          : 0.01
% 2.00/1.13  MUC search           : 0.00
% 2.00/1.13  Cooper               : 0.00
% 2.00/1.13  Total                : 0.47
% 2.00/1.13  Index Insertion      : 0.00
% 2.00/1.13  Index Deletion       : 0.00
% 2.00/1.13  Index Matching       : 0.00
% 2.00/1.13  BG Taut test         : 0.00
%------------------------------------------------------------------------------
