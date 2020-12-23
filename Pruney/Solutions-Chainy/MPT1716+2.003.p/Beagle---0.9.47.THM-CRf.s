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
% DateTime   : Thu Dec  3 10:26:40 EST 2020

% Result     : Theorem 1.98s
% Output     : CNFRefutation 1.98s
% Verified   : 
% Statistics : Number of formulae       :   44 (  57 expanded)
%              Number of leaves         :   23 (  32 expanded)
%              Depth                    :   11
%              Number of atoms          :   78 ( 136 expanded)
%              Number of equality atoms :   10 (  19 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > l1_pre_topc > k1_tsep_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k2_subset_1 > k1_zfmisc_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k1_tsep_1,type,(
    k1_tsep_1: ( $i * $i * $i ) > $i )).

tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(g1_pre_topc,type,(
    g1_pre_topc: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_86,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & m1_pre_topc(B,A) )
           => k1_tsep_1(A,B,B) = g1_pre_topc(u1_struct_0(B),u1_pre_topc(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_tmap_1)).

tff(f_27,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_29,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_70,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_pre_topc(C,A)
             => ( r1_tarski(u1_struct_0(B),u1_struct_0(C))
              <=> m1_pre_topc(B,C) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_tsep_1)).

tff(f_56,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & m1_pre_topc(B,A) )
         => ! [C] :
              ( ( ~ v2_struct_0(C)
                & m1_pre_topc(C,A) )
             => ( m1_pre_topc(B,C)
              <=> k1_tsep_1(A,B,C) = g1_pre_topc(u1_struct_0(C),u1_pre_topc(C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_tsep_1)).

tff(c_28,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_18,plain,(
    g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) != k1_tsep_1('#skF_1','#skF_2','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_26,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_24,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_20,plain,(
    m1_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_22,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_2,plain,(
    ! [A_1] : k2_subset_1(A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_2] : m1_subset_1(k2_subset_1(A_2),k1_zfmisc_1(A_2)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_29,plain,(
    ! [A_2] : m1_subset_1(A_2,k1_zfmisc_1(A_2)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_4])).

tff(c_41,plain,(
    ! [A_24,B_25] :
      ( r1_tarski(A_24,B_25)
      | ~ m1_subset_1(A_24,k1_zfmisc_1(B_25)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_49,plain,(
    ! [A_2] : r1_tarski(A_2,A_2) ),
    inference(resolution,[status(thm)],[c_29,c_41])).

tff(c_58,plain,(
    ! [B_31,C_32,A_33] :
      ( m1_pre_topc(B_31,C_32)
      | ~ r1_tarski(u1_struct_0(B_31),u1_struct_0(C_32))
      | ~ m1_pre_topc(C_32,A_33)
      | ~ m1_pre_topc(B_31,A_33)
      | ~ l1_pre_topc(A_33)
      | ~ v2_pre_topc(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_66,plain,(
    ! [B_34,A_35] :
      ( m1_pre_topc(B_34,B_34)
      | ~ m1_pre_topc(B_34,A_35)
      | ~ l1_pre_topc(A_35)
      | ~ v2_pre_topc(A_35) ) ),
    inference(resolution,[status(thm)],[c_49,c_58])).

tff(c_68,plain,
    ( m1_pre_topc('#skF_2','#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_66])).

tff(c_71,plain,(
    m1_pre_topc('#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_68])).

tff(c_81,plain,(
    ! [A_39,B_40,C_41] :
      ( k1_tsep_1(A_39,B_40,C_41) = g1_pre_topc(u1_struct_0(C_41),u1_pre_topc(C_41))
      | ~ m1_pre_topc(B_40,C_41)
      | ~ m1_pre_topc(C_41,A_39)
      | v2_struct_0(C_41)
      | ~ m1_pre_topc(B_40,A_39)
      | v2_struct_0(B_40)
      | ~ l1_pre_topc(A_39)
      | ~ v2_pre_topc(A_39)
      | v2_struct_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_83,plain,(
    ! [A_39] :
      ( k1_tsep_1(A_39,'#skF_2','#skF_2') = g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))
      | ~ m1_pre_topc('#skF_2',A_39)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_39)
      | ~ v2_pre_topc(A_39)
      | v2_struct_0(A_39) ) ),
    inference(resolution,[status(thm)],[c_71,c_81])).

tff(c_92,plain,(
    ! [A_42] :
      ( k1_tsep_1(A_42,'#skF_2','#skF_2') = g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))
      | ~ m1_pre_topc('#skF_2',A_42)
      | ~ l1_pre_topc(A_42)
      | ~ v2_pre_topc(A_42)
      | v2_struct_0(A_42) ) ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_22,c_83])).

tff(c_96,plain,
    ( g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) = k1_tsep_1('#skF_1','#skF_2','#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_92])).

tff(c_101,plain,
    ( g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) = k1_tsep_1('#skF_1','#skF_2','#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_96])).

tff(c_103,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_18,c_101])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:01:23 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.98/1.25  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.98/1.25  
% 1.98/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.98/1.25  %$ r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > l1_pre_topc > k1_tsep_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k2_subset_1 > k1_zfmisc_1 > #skF_2 > #skF_1
% 1.98/1.25  
% 1.98/1.25  %Foreground sorts:
% 1.98/1.25  
% 1.98/1.25  
% 1.98/1.25  %Background operators:
% 1.98/1.25  
% 1.98/1.25  
% 1.98/1.25  %Foreground operators:
% 1.98/1.25  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 1.98/1.25  tff(k1_tsep_1, type, k1_tsep_1: ($i * $i * $i) > $i).
% 1.98/1.25  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 1.98/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.98/1.25  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 1.98/1.25  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 1.98/1.25  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.98/1.25  tff('#skF_2', type, '#skF_2': $i).
% 1.98/1.25  tff('#skF_1', type, '#skF_1': $i).
% 1.98/1.25  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.98/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.98/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.98/1.25  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 1.98/1.25  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 1.98/1.25  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 1.98/1.25  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 1.98/1.25  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.98/1.25  
% 1.98/1.26  tff(f_86, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (k1_tsep_1(A, B, B) = g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_tmap_1)).
% 1.98/1.26  tff(f_27, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 1.98/1.26  tff(f_29, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 1.98/1.26  tff(f_33, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 1.98/1.26  tff(f_70, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_pre_topc(C, A) => (r1_tarski(u1_struct_0(B), u1_struct_0(C)) <=> m1_pre_topc(B, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_tsep_1)).
% 1.98/1.26  tff(f_56, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (m1_pre_topc(B, C) <=> (k1_tsep_1(A, B, C) = g1_pre_topc(u1_struct_0(C), u1_pre_topc(C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_tsep_1)).
% 1.98/1.26  tff(c_28, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_86])).
% 1.98/1.26  tff(c_18, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))!=k1_tsep_1('#skF_1', '#skF_2', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_86])).
% 1.98/1.26  tff(c_26, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_86])).
% 1.98/1.26  tff(c_24, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_86])).
% 1.98/1.26  tff(c_20, plain, (m1_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_86])).
% 1.98/1.26  tff(c_22, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_86])).
% 1.98/1.26  tff(c_2, plain, (![A_1]: (k2_subset_1(A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.98/1.26  tff(c_4, plain, (![A_2]: (m1_subset_1(k2_subset_1(A_2), k1_zfmisc_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.98/1.26  tff(c_29, plain, (![A_2]: (m1_subset_1(A_2, k1_zfmisc_1(A_2)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_4])).
% 1.98/1.26  tff(c_41, plain, (![A_24, B_25]: (r1_tarski(A_24, B_25) | ~m1_subset_1(A_24, k1_zfmisc_1(B_25)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.98/1.26  tff(c_49, plain, (![A_2]: (r1_tarski(A_2, A_2))), inference(resolution, [status(thm)], [c_29, c_41])).
% 1.98/1.26  tff(c_58, plain, (![B_31, C_32, A_33]: (m1_pre_topc(B_31, C_32) | ~r1_tarski(u1_struct_0(B_31), u1_struct_0(C_32)) | ~m1_pre_topc(C_32, A_33) | ~m1_pre_topc(B_31, A_33) | ~l1_pre_topc(A_33) | ~v2_pre_topc(A_33))), inference(cnfTransformation, [status(thm)], [f_70])).
% 1.98/1.26  tff(c_66, plain, (![B_34, A_35]: (m1_pre_topc(B_34, B_34) | ~m1_pre_topc(B_34, A_35) | ~l1_pre_topc(A_35) | ~v2_pre_topc(A_35))), inference(resolution, [status(thm)], [c_49, c_58])).
% 1.98/1.26  tff(c_68, plain, (m1_pre_topc('#skF_2', '#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_20, c_66])).
% 1.98/1.26  tff(c_71, plain, (m1_pre_topc('#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_68])).
% 1.98/1.26  tff(c_81, plain, (![A_39, B_40, C_41]: (k1_tsep_1(A_39, B_40, C_41)=g1_pre_topc(u1_struct_0(C_41), u1_pre_topc(C_41)) | ~m1_pre_topc(B_40, C_41) | ~m1_pre_topc(C_41, A_39) | v2_struct_0(C_41) | ~m1_pre_topc(B_40, A_39) | v2_struct_0(B_40) | ~l1_pre_topc(A_39) | ~v2_pre_topc(A_39) | v2_struct_0(A_39))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.98/1.26  tff(c_83, plain, (![A_39]: (k1_tsep_1(A_39, '#skF_2', '#skF_2')=g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')) | ~m1_pre_topc('#skF_2', A_39) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_39) | ~v2_pre_topc(A_39) | v2_struct_0(A_39))), inference(resolution, [status(thm)], [c_71, c_81])).
% 1.98/1.26  tff(c_92, plain, (![A_42]: (k1_tsep_1(A_42, '#skF_2', '#skF_2')=g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')) | ~m1_pre_topc('#skF_2', A_42) | ~l1_pre_topc(A_42) | ~v2_pre_topc(A_42) | v2_struct_0(A_42))), inference(negUnitSimplification, [status(thm)], [c_22, c_22, c_83])).
% 1.98/1.26  tff(c_96, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))=k1_tsep_1('#skF_1', '#skF_2', '#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_20, c_92])).
% 1.98/1.26  tff(c_101, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))=k1_tsep_1('#skF_1', '#skF_2', '#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_96])).
% 1.98/1.26  tff(c_103, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_18, c_101])).
% 1.98/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.98/1.26  
% 1.98/1.26  Inference rules
% 1.98/1.26  ----------------------
% 1.98/1.26  #Ref     : 0
% 1.98/1.26  #Sup     : 14
% 1.98/1.26  #Fact    : 0
% 1.98/1.26  #Define  : 0
% 1.98/1.26  #Split   : 1
% 1.98/1.26  #Chain   : 0
% 1.98/1.26  #Close   : 0
% 1.98/1.26  
% 1.98/1.26  Ordering : KBO
% 1.98/1.26  
% 1.98/1.26  Simplification rules
% 1.98/1.26  ----------------------
% 1.98/1.26  #Subsume      : 1
% 1.98/1.26  #Demod        : 8
% 1.98/1.26  #Tautology    : 5
% 1.98/1.26  #SimpNegUnit  : 4
% 1.98/1.26  #BackRed      : 0
% 1.98/1.26  
% 1.98/1.26  #Partial instantiations: 0
% 1.98/1.26  #Strategies tried      : 1
% 1.98/1.26  
% 1.98/1.26  Timing (in seconds)
% 1.98/1.26  ----------------------
% 1.98/1.27  Preprocessing        : 0.31
% 1.98/1.27  Parsing              : 0.17
% 1.98/1.27  CNF conversion       : 0.02
% 1.98/1.27  Main loop            : 0.17
% 1.98/1.27  Inferencing          : 0.07
% 1.98/1.27  Reduction            : 0.05
% 1.98/1.27  Demodulation         : 0.03
% 1.98/1.27  BG Simplification    : 0.01
% 1.98/1.27  Subsumption          : 0.04
% 1.98/1.27  Abstraction          : 0.01
% 1.98/1.27  MUC search           : 0.00
% 1.98/1.27  Cooper               : 0.00
% 1.98/1.27  Total                : 0.51
% 1.98/1.27  Index Insertion      : 0.00
% 1.98/1.27  Index Deletion       : 0.00
% 1.98/1.27  Index Matching       : 0.00
% 1.98/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
