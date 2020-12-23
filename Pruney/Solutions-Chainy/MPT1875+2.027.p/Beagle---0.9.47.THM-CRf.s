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
% DateTime   : Thu Dec  3 10:29:50 EST 2020

% Result     : Theorem 1.98s
% Output     : CNFRefutation 2.08s
% Verified   : 
% Statistics : Number of formulae       :   46 (  98 expanded)
%              Number of leaves         :   21 (  43 expanded)
%              Depth                    :   11
%              Number of atoms          :   84 ( 275 expanded)
%              Number of equality atoms :    1 (   1 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_tex_2 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_tdlat_3 > l1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(v1_tdlat_3,type,(
    v1_tdlat_3: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_83,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & v1_tdlat_3(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => v2_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_tex_2)).

tff(f_33,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

tff(f_40,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l17_tex_2)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_68,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( ( r1_tarski(C,B)
                  & v2_tex_2(B,A) )
               => v2_tex_2(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_tex_2)).

tff(f_54,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( B = u1_struct_0(A)
           => ( v2_tex_2(B,A)
            <=> v1_tdlat_3(A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_tex_2)).

tff(c_26,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_20,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_6,plain,(
    ! [A_3] :
      ( m1_pre_topc(A_3,A_3)
      | ~ l1_pre_topc(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_16,plain,(
    ~ v2_tex_2('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_18,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_8,plain,(
    ! [B_6,A_4] :
      ( m1_subset_1(u1_struct_0(B_6),k1_zfmisc_1(u1_struct_0(A_4)))
      | ~ m1_pre_topc(B_6,A_4)
      | ~ l1_pre_topc(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_28,plain,(
    ! [A_19,B_20] :
      ( r1_tarski(A_19,B_20)
      | ~ m1_subset_1(A_19,k1_zfmisc_1(B_20)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_32,plain,(
    r1_tarski('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_18,c_28])).

tff(c_82,plain,(
    ! [C_33,A_34,B_35] :
      ( v2_tex_2(C_33,A_34)
      | ~ v2_tex_2(B_35,A_34)
      | ~ r1_tarski(C_33,B_35)
      | ~ m1_subset_1(C_33,k1_zfmisc_1(u1_struct_0(A_34)))
      | ~ m1_subset_1(B_35,k1_zfmisc_1(u1_struct_0(A_34)))
      | ~ l1_pre_topc(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_89,plain,(
    ! [A_36] :
      ( v2_tex_2('#skF_2',A_36)
      | ~ v2_tex_2(u1_struct_0('#skF_1'),A_36)
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(A_36)))
      | ~ m1_subset_1(u1_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_36)))
      | ~ l1_pre_topc(A_36) ) ),
    inference(resolution,[status(thm)],[c_32,c_82])).

tff(c_99,plain,(
    ! [A_37] :
      ( v2_tex_2('#skF_2',A_37)
      | ~ v2_tex_2(u1_struct_0('#skF_1'),A_37)
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(A_37)))
      | ~ m1_pre_topc('#skF_1',A_37)
      | ~ l1_pre_topc(A_37) ) ),
    inference(resolution,[status(thm)],[c_8,c_89])).

tff(c_105,plain,
    ( v2_tex_2('#skF_2','#skF_1')
    | ~ v2_tex_2(u1_struct_0('#skF_1'),'#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_99])).

tff(c_109,plain,
    ( v2_tex_2('#skF_2','#skF_1')
    | ~ v2_tex_2(u1_struct_0('#skF_1'),'#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_105])).

tff(c_110,plain,
    ( ~ v2_tex_2(u1_struct_0('#skF_1'),'#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_16,c_109])).

tff(c_111,plain,(
    ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_110])).

tff(c_114,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_6,c_111])).

tff(c_118,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_114])).

tff(c_120,plain,(
    m1_pre_topc('#skF_1','#skF_1') ),
    inference(splitRight,[status(thm)],[c_110])).

tff(c_22,plain,(
    v1_tdlat_3('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_61,plain,(
    ! [A_30] :
      ( v2_tex_2(u1_struct_0(A_30),A_30)
      | ~ v1_tdlat_3(A_30)
      | ~ m1_subset_1(u1_struct_0(A_30),k1_zfmisc_1(u1_struct_0(A_30)))
      | ~ l1_pre_topc(A_30)
      | v2_struct_0(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_69,plain,(
    ! [A_4] :
      ( v2_tex_2(u1_struct_0(A_4),A_4)
      | ~ v1_tdlat_3(A_4)
      | v2_struct_0(A_4)
      | ~ m1_pre_topc(A_4,A_4)
      | ~ l1_pre_topc(A_4) ) ),
    inference(resolution,[status(thm)],[c_8,c_61])).

tff(c_119,plain,(
    ~ v2_tex_2(u1_struct_0('#skF_1'),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_110])).

tff(c_123,plain,
    ( ~ v1_tdlat_3('#skF_1')
    | v2_struct_0('#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_69,c_119])).

tff(c_126,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_120,c_22,c_123])).

tff(c_128,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_126])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.34  % Computer   : n020.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % DateTime   : Tue Dec  1 11:55:07 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.98/1.27  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.08/1.27  
% 2.08/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.08/1.27  %$ v2_tex_2 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_tdlat_3 > l1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1
% 2.08/1.27  
% 2.08/1.27  %Foreground sorts:
% 2.08/1.27  
% 2.08/1.27  
% 2.08/1.27  %Background operators:
% 2.08/1.27  
% 2.08/1.27  
% 2.08/1.27  %Foreground operators:
% 2.08/1.27  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.08/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.08/1.27  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.08/1.27  tff(v1_tdlat_3, type, v1_tdlat_3: $i > $o).
% 2.08/1.27  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.08/1.27  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 2.08/1.27  tff('#skF_2', type, '#skF_2': $i).
% 2.08/1.27  tff('#skF_1', type, '#skF_1': $i).
% 2.08/1.27  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.08/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.08/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.08/1.27  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.08/1.27  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.08/1.27  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.08/1.27  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.08/1.27  
% 2.08/1.29  tff(f_83, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v1_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => v2_tex_2(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_tex_2)).
% 2.08/1.29  tff(f_33, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tsep_1)).
% 2.08/1.29  tff(f_40, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l17_tex_2)).
% 2.08/1.29  tff(f_29, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.08/1.29  tff(f_68, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((r1_tarski(C, B) & v2_tex_2(B, A)) => v2_tex_2(C, A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_tex_2)).
% 2.08/1.29  tff(f_54, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((B = u1_struct_0(A)) => (v2_tex_2(B, A) <=> v1_tdlat_3(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t27_tex_2)).
% 2.08/1.29  tff(c_26, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.08/1.29  tff(c_20, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.08/1.29  tff(c_6, plain, (![A_3]: (m1_pre_topc(A_3, A_3) | ~l1_pre_topc(A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.08/1.29  tff(c_16, plain, (~v2_tex_2('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.08/1.29  tff(c_18, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.08/1.29  tff(c_8, plain, (![B_6, A_4]: (m1_subset_1(u1_struct_0(B_6), k1_zfmisc_1(u1_struct_0(A_4))) | ~m1_pre_topc(B_6, A_4) | ~l1_pre_topc(A_4))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.08/1.29  tff(c_28, plain, (![A_19, B_20]: (r1_tarski(A_19, B_20) | ~m1_subset_1(A_19, k1_zfmisc_1(B_20)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.08/1.29  tff(c_32, plain, (r1_tarski('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_18, c_28])).
% 2.08/1.29  tff(c_82, plain, (![C_33, A_34, B_35]: (v2_tex_2(C_33, A_34) | ~v2_tex_2(B_35, A_34) | ~r1_tarski(C_33, B_35) | ~m1_subset_1(C_33, k1_zfmisc_1(u1_struct_0(A_34))) | ~m1_subset_1(B_35, k1_zfmisc_1(u1_struct_0(A_34))) | ~l1_pre_topc(A_34))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.08/1.29  tff(c_89, plain, (![A_36]: (v2_tex_2('#skF_2', A_36) | ~v2_tex_2(u1_struct_0('#skF_1'), A_36) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(A_36))) | ~m1_subset_1(u1_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_36))) | ~l1_pre_topc(A_36))), inference(resolution, [status(thm)], [c_32, c_82])).
% 2.08/1.29  tff(c_99, plain, (![A_37]: (v2_tex_2('#skF_2', A_37) | ~v2_tex_2(u1_struct_0('#skF_1'), A_37) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(A_37))) | ~m1_pre_topc('#skF_1', A_37) | ~l1_pre_topc(A_37))), inference(resolution, [status(thm)], [c_8, c_89])).
% 2.08/1.29  tff(c_105, plain, (v2_tex_2('#skF_2', '#skF_1') | ~v2_tex_2(u1_struct_0('#skF_1'), '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_18, c_99])).
% 2.08/1.29  tff(c_109, plain, (v2_tex_2('#skF_2', '#skF_1') | ~v2_tex_2(u1_struct_0('#skF_1'), '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_105])).
% 2.08/1.29  tff(c_110, plain, (~v2_tex_2(u1_struct_0('#skF_1'), '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_16, c_109])).
% 2.08/1.29  tff(c_111, plain, (~m1_pre_topc('#skF_1', '#skF_1')), inference(splitLeft, [status(thm)], [c_110])).
% 2.08/1.29  tff(c_114, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_6, c_111])).
% 2.08/1.29  tff(c_118, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_114])).
% 2.08/1.29  tff(c_120, plain, (m1_pre_topc('#skF_1', '#skF_1')), inference(splitRight, [status(thm)], [c_110])).
% 2.08/1.29  tff(c_22, plain, (v1_tdlat_3('#skF_1')), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.08/1.29  tff(c_61, plain, (![A_30]: (v2_tex_2(u1_struct_0(A_30), A_30) | ~v1_tdlat_3(A_30) | ~m1_subset_1(u1_struct_0(A_30), k1_zfmisc_1(u1_struct_0(A_30))) | ~l1_pre_topc(A_30) | v2_struct_0(A_30))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.08/1.29  tff(c_69, plain, (![A_4]: (v2_tex_2(u1_struct_0(A_4), A_4) | ~v1_tdlat_3(A_4) | v2_struct_0(A_4) | ~m1_pre_topc(A_4, A_4) | ~l1_pre_topc(A_4))), inference(resolution, [status(thm)], [c_8, c_61])).
% 2.08/1.29  tff(c_119, plain, (~v2_tex_2(u1_struct_0('#skF_1'), '#skF_1')), inference(splitRight, [status(thm)], [c_110])).
% 2.08/1.29  tff(c_123, plain, (~v1_tdlat_3('#skF_1') | v2_struct_0('#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_69, c_119])).
% 2.08/1.29  tff(c_126, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_120, c_22, c_123])).
% 2.08/1.29  tff(c_128, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_126])).
% 2.08/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.08/1.29  
% 2.08/1.29  Inference rules
% 2.08/1.29  ----------------------
% 2.08/1.29  #Ref     : 0
% 2.08/1.29  #Sup     : 18
% 2.08/1.29  #Fact    : 0
% 2.08/1.29  #Define  : 0
% 2.08/1.29  #Split   : 1
% 2.08/1.29  #Chain   : 0
% 2.08/1.29  #Close   : 0
% 2.08/1.29  
% 2.08/1.29  Ordering : KBO
% 2.08/1.29  
% 2.08/1.29  Simplification rules
% 2.08/1.29  ----------------------
% 2.08/1.29  #Subsume      : 2
% 2.08/1.29  #Demod        : 5
% 2.08/1.29  #Tautology    : 2
% 2.08/1.29  #SimpNegUnit  : 2
% 2.08/1.29  #BackRed      : 0
% 2.08/1.29  
% 2.08/1.29  #Partial instantiations: 0
% 2.08/1.29  #Strategies tried      : 1
% 2.08/1.29  
% 2.08/1.29  Timing (in seconds)
% 2.08/1.29  ----------------------
% 2.08/1.29  Preprocessing        : 0.30
% 2.08/1.29  Parsing              : 0.17
% 2.08/1.29  CNF conversion       : 0.02
% 2.08/1.29  Main loop            : 0.17
% 2.08/1.29  Inferencing          : 0.07
% 2.08/1.29  Reduction            : 0.04
% 2.08/1.29  Demodulation         : 0.03
% 2.08/1.29  BG Simplification    : 0.01
% 2.08/1.29  Subsumption          : 0.03
% 2.08/1.29  Abstraction          : 0.01
% 2.08/1.29  MUC search           : 0.00
% 2.08/1.29  Cooper               : 0.00
% 2.08/1.29  Total                : 0.50
% 2.08/1.29  Index Insertion      : 0.00
% 2.08/1.29  Index Deletion       : 0.00
% 2.08/1.29  Index Matching       : 0.00
% 2.08/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
