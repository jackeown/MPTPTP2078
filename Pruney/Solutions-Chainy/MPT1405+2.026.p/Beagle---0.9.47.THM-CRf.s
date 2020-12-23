%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:33 EST 2020

% Result     : Theorem 2.46s
% Output     : CNFRefutation 2.46s
% Verified   : 
% Statistics : Number of formulae       :   52 ( 125 expanded)
%              Number of leaves         :   23 (  54 expanded)
%              Depth                    :   10
%              Number of atoms          :   84 ( 254 expanded)
%              Number of equality atoms :    6 (  30 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m2_connsp_2 > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > l1_struct_0 > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(m2_connsp_2,type,(
    m2_connsp_2: ( $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_74,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => m2_connsp_2(k2_struct_0(A),A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_connsp_2)).

tff(f_41,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_33,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_37,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => m1_subset_1(k2_struct_0(A),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_struct_0)).

tff(f_47,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => k1_tops_1(A,k2_struct_0(A)) = k2_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_tops_1)).

tff(f_61,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( m2_connsp_2(C,A,B)
              <=> r1_tarski(B,k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_connsp_2)).

tff(c_18,plain,(
    ~ m2_connsp_2(k2_struct_0('#skF_1'),'#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_22,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_10,plain,(
    ! [A_5] :
      ( l1_struct_0(A_5)
      | ~ l1_pre_topc(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_28,plain,(
    ! [A_16] :
      ( u1_struct_0(A_16) = k2_struct_0(A_16)
      | ~ l1_struct_0(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_33,plain,(
    ! [A_17] :
      ( u1_struct_0(A_17) = k2_struct_0(A_17)
      | ~ l1_pre_topc(A_17) ) ),
    inference(resolution,[status(thm)],[c_10,c_28])).

tff(c_37,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_33])).

tff(c_20,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_38,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_37,c_20])).

tff(c_43,plain,(
    ! [A_18,B_19] :
      ( r1_tarski(A_18,B_19)
      | ~ m1_subset_1(A_18,k1_zfmisc_1(B_19)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_47,plain,(
    r1_tarski('#skF_2',k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_38,c_43])).

tff(c_24,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_53,plain,(
    ! [A_22] :
      ( m1_subset_1(k2_struct_0(A_22),k1_zfmisc_1(u1_struct_0(A_22)))
      | ~ l1_struct_0(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(A_1,B_2)
      | ~ m1_subset_1(A_1,k1_zfmisc_1(B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_61,plain,(
    ! [A_23] :
      ( r1_tarski(k2_struct_0(A_23),u1_struct_0(A_23))
      | ~ l1_struct_0(A_23) ) ),
    inference(resolution,[status(thm)],[c_53,c_2])).

tff(c_64,plain,
    ( r1_tarski(k2_struct_0('#skF_1'),k2_struct_0('#skF_1'))
    | ~ l1_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_37,c_61])).

tff(c_74,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_77,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_10,c_74])).

tff(c_81,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_77])).

tff(c_83,plain,(
    l1_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_59,plain,
    ( m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1')))
    | ~ l1_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_37,c_53])).

tff(c_90,plain,(
    m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_59])).

tff(c_12,plain,(
    ! [A_6] :
      ( k1_tops_1(A_6,k2_struct_0(A_6)) = k2_struct_0(A_6)
      | ~ l1_pre_topc(A_6)
      | ~ v2_pre_topc(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_133,plain,(
    ! [C_31,A_32,B_33] :
      ( m2_connsp_2(C_31,A_32,B_33)
      | ~ r1_tarski(B_33,k1_tops_1(A_32,C_31))
      | ~ m1_subset_1(C_31,k1_zfmisc_1(u1_struct_0(A_32)))
      | ~ m1_subset_1(B_33,k1_zfmisc_1(u1_struct_0(A_32)))
      | ~ l1_pre_topc(A_32)
      | ~ v2_pre_topc(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_246,plain,(
    ! [A_59,B_60] :
      ( m2_connsp_2(k2_struct_0(A_59),A_59,B_60)
      | ~ r1_tarski(B_60,k2_struct_0(A_59))
      | ~ m1_subset_1(k2_struct_0(A_59),k1_zfmisc_1(u1_struct_0(A_59)))
      | ~ m1_subset_1(B_60,k1_zfmisc_1(u1_struct_0(A_59)))
      | ~ l1_pre_topc(A_59)
      | ~ v2_pre_topc(A_59)
      | ~ l1_pre_topc(A_59)
      | ~ v2_pre_topc(A_59) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_133])).

tff(c_253,plain,(
    ! [B_60] :
      ( m2_connsp_2(k2_struct_0('#skF_1'),'#skF_1',B_60)
      | ~ r1_tarski(B_60,k2_struct_0('#skF_1'))
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ m1_subset_1(B_60,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_37,c_246])).

tff(c_258,plain,(
    ! [B_61] :
      ( m2_connsp_2(k2_struct_0('#skF_1'),'#skF_1',B_61)
      | ~ r1_tarski(B_61,k2_struct_0('#skF_1'))
      | ~ m1_subset_1(B_61,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_24,c_22,c_37,c_90,c_253])).

tff(c_268,plain,
    ( m2_connsp_2(k2_struct_0('#skF_1'),'#skF_1','#skF_2')
    | ~ r1_tarski('#skF_2',k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_38,c_258])).

tff(c_275,plain,(
    m2_connsp_2(k2_struct_0('#skF_1'),'#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_47,c_268])).

tff(c_277,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_275])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n016.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:55:34 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.46/1.29  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.46/1.29  
% 2.46/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.46/1.29  %$ m2_connsp_2 > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > l1_struct_0 > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1
% 2.46/1.29  
% 2.46/1.29  %Foreground sorts:
% 2.46/1.29  
% 2.46/1.29  
% 2.46/1.29  %Background operators:
% 2.46/1.29  
% 2.46/1.29  
% 2.46/1.29  %Foreground operators:
% 2.46/1.29  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.46/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.46/1.29  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.46/1.29  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.46/1.29  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 2.46/1.29  tff('#skF_2', type, '#skF_2': $i).
% 2.46/1.29  tff('#skF_1', type, '#skF_1': $i).
% 2.46/1.29  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.46/1.29  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.46/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.46/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.46/1.29  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.46/1.29  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.46/1.29  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.46/1.29  tff(m2_connsp_2, type, m2_connsp_2: ($i * $i * $i) > $o).
% 2.46/1.29  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.46/1.29  
% 2.46/1.31  tff(f_74, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => m2_connsp_2(k2_struct_0(A), A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_connsp_2)).
% 2.46/1.31  tff(f_41, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.46/1.31  tff(f_33, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 2.46/1.31  tff(f_29, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.46/1.31  tff(f_37, axiom, (![A]: (l1_struct_0(A) => m1_subset_1(k2_struct_0(A), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_struct_0)).
% 2.46/1.31  tff(f_47, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (k1_tops_1(A, k2_struct_0(A)) = k2_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_tops_1)).
% 2.46/1.31  tff(f_61, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m2_connsp_2(C, A, B) <=> r1_tarski(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_connsp_2)).
% 2.46/1.31  tff(c_18, plain, (~m2_connsp_2(k2_struct_0('#skF_1'), '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.46/1.31  tff(c_22, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.46/1.31  tff(c_10, plain, (![A_5]: (l1_struct_0(A_5) | ~l1_pre_topc(A_5))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.46/1.31  tff(c_28, plain, (![A_16]: (u1_struct_0(A_16)=k2_struct_0(A_16) | ~l1_struct_0(A_16))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.46/1.31  tff(c_33, plain, (![A_17]: (u1_struct_0(A_17)=k2_struct_0(A_17) | ~l1_pre_topc(A_17))), inference(resolution, [status(thm)], [c_10, c_28])).
% 2.46/1.31  tff(c_37, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_22, c_33])).
% 2.46/1.31  tff(c_20, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.46/1.31  tff(c_38, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_37, c_20])).
% 2.46/1.31  tff(c_43, plain, (![A_18, B_19]: (r1_tarski(A_18, B_19) | ~m1_subset_1(A_18, k1_zfmisc_1(B_19)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.46/1.31  tff(c_47, plain, (r1_tarski('#skF_2', k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_38, c_43])).
% 2.46/1.31  tff(c_24, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.46/1.31  tff(c_53, plain, (![A_22]: (m1_subset_1(k2_struct_0(A_22), k1_zfmisc_1(u1_struct_0(A_22))) | ~l1_struct_0(A_22))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.46/1.31  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(A_1, B_2) | ~m1_subset_1(A_1, k1_zfmisc_1(B_2)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.46/1.31  tff(c_61, plain, (![A_23]: (r1_tarski(k2_struct_0(A_23), u1_struct_0(A_23)) | ~l1_struct_0(A_23))), inference(resolution, [status(thm)], [c_53, c_2])).
% 2.46/1.31  tff(c_64, plain, (r1_tarski(k2_struct_0('#skF_1'), k2_struct_0('#skF_1')) | ~l1_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_37, c_61])).
% 2.46/1.31  tff(c_74, plain, (~l1_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_64])).
% 2.46/1.31  tff(c_77, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_10, c_74])).
% 2.46/1.31  tff(c_81, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_77])).
% 2.46/1.31  tff(c_83, plain, (l1_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_64])).
% 2.46/1.31  tff(c_59, plain, (m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_37, c_53])).
% 2.46/1.31  tff(c_90, plain, (m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_83, c_59])).
% 2.46/1.31  tff(c_12, plain, (![A_6]: (k1_tops_1(A_6, k2_struct_0(A_6))=k2_struct_0(A_6) | ~l1_pre_topc(A_6) | ~v2_pre_topc(A_6))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.46/1.31  tff(c_133, plain, (![C_31, A_32, B_33]: (m2_connsp_2(C_31, A_32, B_33) | ~r1_tarski(B_33, k1_tops_1(A_32, C_31)) | ~m1_subset_1(C_31, k1_zfmisc_1(u1_struct_0(A_32))) | ~m1_subset_1(B_33, k1_zfmisc_1(u1_struct_0(A_32))) | ~l1_pre_topc(A_32) | ~v2_pre_topc(A_32))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.46/1.31  tff(c_246, plain, (![A_59, B_60]: (m2_connsp_2(k2_struct_0(A_59), A_59, B_60) | ~r1_tarski(B_60, k2_struct_0(A_59)) | ~m1_subset_1(k2_struct_0(A_59), k1_zfmisc_1(u1_struct_0(A_59))) | ~m1_subset_1(B_60, k1_zfmisc_1(u1_struct_0(A_59))) | ~l1_pre_topc(A_59) | ~v2_pre_topc(A_59) | ~l1_pre_topc(A_59) | ~v2_pre_topc(A_59))), inference(superposition, [status(thm), theory('equality')], [c_12, c_133])).
% 2.46/1.31  tff(c_253, plain, (![B_60]: (m2_connsp_2(k2_struct_0('#skF_1'), '#skF_1', B_60) | ~r1_tarski(B_60, k2_struct_0('#skF_1')) | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~m1_subset_1(B_60, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_37, c_246])).
% 2.46/1.31  tff(c_258, plain, (![B_61]: (m2_connsp_2(k2_struct_0('#skF_1'), '#skF_1', B_61) | ~r1_tarski(B_61, k2_struct_0('#skF_1')) | ~m1_subset_1(B_61, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_24, c_22, c_37, c_90, c_253])).
% 2.46/1.31  tff(c_268, plain, (m2_connsp_2(k2_struct_0('#skF_1'), '#skF_1', '#skF_2') | ~r1_tarski('#skF_2', k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_38, c_258])).
% 2.46/1.31  tff(c_275, plain, (m2_connsp_2(k2_struct_0('#skF_1'), '#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_47, c_268])).
% 2.46/1.31  tff(c_277, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18, c_275])).
% 2.46/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.46/1.31  
% 2.46/1.31  Inference rules
% 2.46/1.31  ----------------------
% 2.46/1.31  #Ref     : 0
% 2.46/1.31  #Sup     : 55
% 2.46/1.31  #Fact    : 0
% 2.46/1.31  #Define  : 0
% 2.46/1.31  #Split   : 3
% 2.46/1.31  #Chain   : 0
% 2.46/1.31  #Close   : 0
% 2.46/1.31  
% 2.46/1.31  Ordering : KBO
% 2.46/1.31  
% 2.46/1.31  Simplification rules
% 2.46/1.31  ----------------------
% 2.46/1.31  #Subsume      : 7
% 2.46/1.31  #Demod        : 50
% 2.46/1.31  #Tautology    : 16
% 2.46/1.31  #SimpNegUnit  : 1
% 2.46/1.31  #BackRed      : 1
% 2.46/1.31  
% 2.46/1.31  #Partial instantiations: 0
% 2.46/1.31  #Strategies tried      : 1
% 2.46/1.31  
% 2.46/1.31  Timing (in seconds)
% 2.46/1.31  ----------------------
% 2.46/1.31  Preprocessing        : 0.30
% 2.46/1.31  Parsing              : 0.16
% 2.46/1.31  CNF conversion       : 0.02
% 2.46/1.31  Main loop            : 0.25
% 2.46/1.31  Inferencing          : 0.10
% 2.46/1.31  Reduction            : 0.07
% 2.46/1.31  Demodulation         : 0.05
% 2.46/1.31  BG Simplification    : 0.01
% 2.46/1.31  Subsumption          : 0.05
% 2.46/1.31  Abstraction          : 0.01
% 2.46/1.31  MUC search           : 0.00
% 2.46/1.31  Cooper               : 0.00
% 2.46/1.31  Total                : 0.58
% 2.46/1.31  Index Insertion      : 0.00
% 2.46/1.31  Index Deletion       : 0.00
% 2.46/1.31  Index Matching       : 0.00
% 2.46/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
