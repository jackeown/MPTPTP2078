%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:51 EST 2020

% Result     : Theorem 2.16s
% Output     : CNFRefutation 2.16s
% Verified   : 
% Statistics : Number of formulae       :   50 (  74 expanded)
%              Number of leaves         :   23 (  35 expanded)
%              Depth                    :   11
%              Number of atoms          :   66 ( 141 expanded)
%              Number of equality atoms :    8 (  18 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_subset_1 > m1_subset_1 > v7_struct_0 > v2_struct_0 > v1_zfmisc_1 > v1_xboole_0 > l1_struct_0 > k6_domain_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(v7_struct_0,type,(
    v7_struct_0: $i > $o )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

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

tff(v1_zfmisc_1,type,(
    v1_zfmisc_1: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_78,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & ~ v7_struct_0(A)
          & l1_struct_0(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => v1_subset_1(k6_domain_1(u1_struct_0(A),B),u1_struct_0(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_tex_2)).

tff(f_27,axiom,(
    ! [A] : v1_zfmisc_1(k1_tarski(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_zfmisc_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_35,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_50,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( v1_subset_1(B,A)
      <=> B != A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).

tff(f_43,axiom,(
    ! [A] :
      ( ( ~ v7_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_zfmisc_1(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_struct_0)).

tff(c_22,plain,(
    ~ v7_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_20,plain,(
    l1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_2,plain,(
    ! [A_1] : v1_zfmisc_1(k1_tarski(A_1)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_24,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_18,plain,(
    m1_subset_1('#skF_2',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_30,plain,(
    ! [A_17,B_18] :
      ( k6_domain_1(A_17,B_18) = k1_tarski(B_18)
      | ~ m1_subset_1(B_18,A_17)
      | v1_xboole_0(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_34,plain,
    ( k6_domain_1(u1_struct_0('#skF_1'),'#skF_2') = k1_tarski('#skF_2')
    | v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_18,c_30])).

tff(c_35,plain,(
    v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_4,plain,(
    ! [A_2] :
      ( ~ v1_xboole_0(u1_struct_0(A_2))
      | ~ l1_struct_0(A_2)
      | v2_struct_0(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_38,plain,
    ( ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_35,c_4])).

tff(c_41,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_38])).

tff(c_43,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_41])).

tff(c_44,plain,(
    k6_domain_1(u1_struct_0('#skF_1'),'#skF_2') = k1_tarski('#skF_2') ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_16,plain,(
    ~ v1_subset_1(k6_domain_1(u1_struct_0('#skF_1'),'#skF_2'),u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_46,plain,(
    ~ v1_subset_1(k1_tarski('#skF_2'),u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_16])).

tff(c_45,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_51,plain,(
    ! [A_19,B_20] :
      ( m1_subset_1(k6_domain_1(A_19,B_20),k1_zfmisc_1(A_19))
      | ~ m1_subset_1(B_20,A_19)
      | v1_xboole_0(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_60,plain,
    ( m1_subset_1(k1_tarski('#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1'))
    | v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_51])).

tff(c_64,plain,
    ( m1_subset_1(k1_tarski('#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_60])).

tff(c_65,plain,(
    m1_subset_1(k1_tarski('#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_45,c_64])).

tff(c_12,plain,(
    ! [B_9,A_8] :
      ( v1_subset_1(B_9,A_8)
      | B_9 = A_8
      | ~ m1_subset_1(B_9,k1_zfmisc_1(A_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_71,plain,
    ( v1_subset_1(k1_tarski('#skF_2'),u1_struct_0('#skF_1'))
    | u1_struct_0('#skF_1') = k1_tarski('#skF_2') ),
    inference(resolution,[status(thm)],[c_65,c_12])).

tff(c_75,plain,(
    u1_struct_0('#skF_1') = k1_tarski('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_71])).

tff(c_6,plain,(
    ! [A_3] :
      ( ~ v1_zfmisc_1(u1_struct_0(A_3))
      | ~ l1_struct_0(A_3)
      | v7_struct_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_87,plain,
    ( ~ v1_zfmisc_1(k1_tarski('#skF_2'))
    | ~ l1_struct_0('#skF_1')
    | v7_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_75,c_6])).

tff(c_94,plain,(
    v7_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_2,c_87])).

tff(c_96,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_94])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.34  % Computer   : n011.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % DateTime   : Tue Dec  1 15:44:12 EST 2020
% 0.15/0.34  % CPUTime    : 
% 0.15/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.16/1.23  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.16/1.24  
% 2.16/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.16/1.24  %$ v1_subset_1 > m1_subset_1 > v7_struct_0 > v2_struct_0 > v1_zfmisc_1 > v1_xboole_0 > l1_struct_0 > k6_domain_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_1
% 2.16/1.24  
% 2.16/1.24  %Foreground sorts:
% 2.16/1.24  
% 2.16/1.24  
% 2.16/1.24  %Background operators:
% 2.16/1.24  
% 2.16/1.24  
% 2.16/1.24  %Foreground operators:
% 2.16/1.24  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.16/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.16/1.24  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 2.16/1.24  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.16/1.24  tff(v7_struct_0, type, v7_struct_0: $i > $o).
% 2.16/1.24  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.16/1.24  tff('#skF_2', type, '#skF_2': $i).
% 2.16/1.24  tff('#skF_1', type, '#skF_1': $i).
% 2.16/1.24  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.16/1.24  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.16/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.16/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.16/1.24  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 2.16/1.24  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.16/1.24  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.16/1.24  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.16/1.24  
% 2.16/1.25  tff(f_78, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & ~v7_struct_0(A)) & l1_struct_0(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => v1_subset_1(k6_domain_1(u1_struct_0(A), B), u1_struct_0(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_tex_2)).
% 2.16/1.25  tff(f_27, axiom, (![A]: v1_zfmisc_1(k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_zfmisc_1)).
% 2.16/1.25  tff(f_57, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 2.16/1.25  tff(f_35, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 2.16/1.25  tff(f_50, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 2.16/1.25  tff(f_64, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (v1_subset_1(B, A) <=> ~(B = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_subset_1)).
% 2.16/1.25  tff(f_43, axiom, (![A]: ((~v7_struct_0(A) & l1_struct_0(A)) => ~v1_zfmisc_1(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_struct_0)).
% 2.16/1.25  tff(c_22, plain, (~v7_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.16/1.25  tff(c_20, plain, (l1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.16/1.25  tff(c_2, plain, (![A_1]: (v1_zfmisc_1(k1_tarski(A_1)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.16/1.25  tff(c_24, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.16/1.25  tff(c_18, plain, (m1_subset_1('#skF_2', u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.16/1.25  tff(c_30, plain, (![A_17, B_18]: (k6_domain_1(A_17, B_18)=k1_tarski(B_18) | ~m1_subset_1(B_18, A_17) | v1_xboole_0(A_17))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.16/1.25  tff(c_34, plain, (k6_domain_1(u1_struct_0('#skF_1'), '#skF_2')=k1_tarski('#skF_2') | v1_xboole_0(u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_18, c_30])).
% 2.16/1.25  tff(c_35, plain, (v1_xboole_0(u1_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_34])).
% 2.16/1.25  tff(c_4, plain, (![A_2]: (~v1_xboole_0(u1_struct_0(A_2)) | ~l1_struct_0(A_2) | v2_struct_0(A_2))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.16/1.25  tff(c_38, plain, (~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_35, c_4])).
% 2.16/1.25  tff(c_41, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_38])).
% 2.16/1.25  tff(c_43, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_41])).
% 2.16/1.25  tff(c_44, plain, (k6_domain_1(u1_struct_0('#skF_1'), '#skF_2')=k1_tarski('#skF_2')), inference(splitRight, [status(thm)], [c_34])).
% 2.16/1.25  tff(c_16, plain, (~v1_subset_1(k6_domain_1(u1_struct_0('#skF_1'), '#skF_2'), u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.16/1.25  tff(c_46, plain, (~v1_subset_1(k1_tarski('#skF_2'), u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_16])).
% 2.16/1.25  tff(c_45, plain, (~v1_xboole_0(u1_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_34])).
% 2.16/1.25  tff(c_51, plain, (![A_19, B_20]: (m1_subset_1(k6_domain_1(A_19, B_20), k1_zfmisc_1(A_19)) | ~m1_subset_1(B_20, A_19) | v1_xboole_0(A_19))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.16/1.25  tff(c_60, plain, (m1_subset_1(k1_tarski('#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', u1_struct_0('#skF_1')) | v1_xboole_0(u1_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_44, c_51])).
% 2.16/1.25  tff(c_64, plain, (m1_subset_1(k1_tarski('#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | v1_xboole_0(u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_60])).
% 2.16/1.25  tff(c_65, plain, (m1_subset_1(k1_tarski('#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_45, c_64])).
% 2.16/1.25  tff(c_12, plain, (![B_9, A_8]: (v1_subset_1(B_9, A_8) | B_9=A_8 | ~m1_subset_1(B_9, k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.16/1.25  tff(c_71, plain, (v1_subset_1(k1_tarski('#skF_2'), u1_struct_0('#skF_1')) | u1_struct_0('#skF_1')=k1_tarski('#skF_2')), inference(resolution, [status(thm)], [c_65, c_12])).
% 2.16/1.25  tff(c_75, plain, (u1_struct_0('#skF_1')=k1_tarski('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_46, c_71])).
% 2.16/1.25  tff(c_6, plain, (![A_3]: (~v1_zfmisc_1(u1_struct_0(A_3)) | ~l1_struct_0(A_3) | v7_struct_0(A_3))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.16/1.25  tff(c_87, plain, (~v1_zfmisc_1(k1_tarski('#skF_2')) | ~l1_struct_0('#skF_1') | v7_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_75, c_6])).
% 2.16/1.25  tff(c_94, plain, (v7_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_2, c_87])).
% 2.16/1.25  tff(c_96, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22, c_94])).
% 2.16/1.25  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.16/1.25  
% 2.16/1.25  Inference rules
% 2.16/1.25  ----------------------
% 2.16/1.25  #Ref     : 0
% 2.16/1.25  #Sup     : 13
% 2.16/1.25  #Fact    : 0
% 2.16/1.25  #Define  : 0
% 2.16/1.25  #Split   : 1
% 2.16/1.25  #Chain   : 0
% 2.16/1.25  #Close   : 0
% 2.16/1.25  
% 2.16/1.25  Ordering : KBO
% 2.16/1.25  
% 2.16/1.25  Simplification rules
% 2.16/1.25  ----------------------
% 2.16/1.25  #Subsume      : 0
% 2.16/1.25  #Demod        : 11
% 2.16/1.25  #Tautology    : 3
% 2.16/1.25  #SimpNegUnit  : 5
% 2.16/1.25  #BackRed      : 6
% 2.16/1.25  
% 2.16/1.25  #Partial instantiations: 0
% 2.16/1.25  #Strategies tried      : 1
% 2.16/1.25  
% 2.16/1.25  Timing (in seconds)
% 2.16/1.25  ----------------------
% 2.16/1.25  Preprocessing        : 0.31
% 2.16/1.25  Parsing              : 0.16
% 2.16/1.25  CNF conversion       : 0.02
% 2.16/1.25  Main loop            : 0.12
% 2.16/1.25  Inferencing          : 0.04
% 2.16/1.25  Reduction            : 0.04
% 2.16/1.25  Demodulation         : 0.03
% 2.16/1.25  BG Simplification    : 0.01
% 2.16/1.25  Subsumption          : 0.02
% 2.16/1.25  Abstraction          : 0.01
% 2.16/1.25  MUC search           : 0.00
% 2.16/1.25  Cooper               : 0.00
% 2.16/1.26  Total                : 0.46
% 2.16/1.26  Index Insertion      : 0.00
% 2.16/1.26  Index Deletion       : 0.00
% 2.16/1.26  Index Matching       : 0.00
% 2.16/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
