%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:06 EST 2020

% Result     : Theorem 2.20s
% Output     : CNFRefutation 2.20s
% Verified   : 
% Statistics : Number of formulae       :   50 (  68 expanded)
%              Number of leaves         :   23 (  36 expanded)
%              Depth                    :   10
%              Number of atoms          :   94 ( 188 expanded)
%              Number of equality atoms :    1 (   2 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(m1_connsp_2,type,(
    m1_connsp_2: ( $i * $i * $i ) > $o )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_99,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => ( ( v3_pre_topc(B,A)
                    & r2_hidden(C,B) )
                 => m1_connsp_2(B,A,C) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_connsp_2)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_62,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( ( v3_pre_topc(B,A)
                  & r1_tarski(B,C) )
               => r1_tarski(B,k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_tops_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_38,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_79,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( m1_connsp_2(C,A,B)
              <=> r2_hidden(B,k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_connsp_2)).

tff(c_36,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_22,plain,(
    ~ m1_connsp_2('#skF_2','#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_34,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_32,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_28,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_30,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_26,plain,(
    v3_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_123,plain,(
    ! [B_52,A_53,C_54] :
      ( r1_tarski(B_52,k1_tops_1(A_53,C_54))
      | ~ r1_tarski(B_52,C_54)
      | ~ v3_pre_topc(B_52,A_53)
      | ~ m1_subset_1(C_54,k1_zfmisc_1(u1_struct_0(A_53)))
      | ~ m1_subset_1(B_52,k1_zfmisc_1(u1_struct_0(A_53)))
      | ~ l1_pre_topc(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_128,plain,(
    ! [B_52] :
      ( r1_tarski(B_52,k1_tops_1('#skF_1','#skF_2'))
      | ~ r1_tarski(B_52,'#skF_2')
      | ~ v3_pre_topc(B_52,'#skF_1')
      | ~ m1_subset_1(B_52,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_30,c_123])).

tff(c_149,plain,(
    ! [B_58] :
      ( r1_tarski(B_58,k1_tops_1('#skF_1','#skF_2'))
      | ~ r1_tarski(B_58,'#skF_2')
      | ~ v3_pre_topc(B_58,'#skF_1')
      | ~ m1_subset_1(B_58,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_128])).

tff(c_156,plain,
    ( r1_tarski('#skF_2',k1_tops_1('#skF_1','#skF_2'))
    | ~ r1_tarski('#skF_2','#skF_2')
    | ~ v3_pre_topc('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_149])).

tff(c_160,plain,(
    r1_tarski('#skF_2',k1_tops_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_6,c_156])).

tff(c_12,plain,(
    ! [A_7,B_8] :
      ( m1_subset_1(A_7,k1_zfmisc_1(B_8))
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_24,plain,(
    r2_hidden('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_60,plain,(
    ! [C_37,A_38,B_39] :
      ( r2_hidden(C_37,A_38)
      | ~ r2_hidden(C_37,B_39)
      | ~ m1_subset_1(B_39,k1_zfmisc_1(A_38)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_64,plain,(
    ! [A_40] :
      ( r2_hidden('#skF_3',A_40)
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(A_40)) ) ),
    inference(resolution,[status(thm)],[c_24,c_60])).

tff(c_77,plain,(
    ! [B_41] :
      ( r2_hidden('#skF_3',B_41)
      | ~ r1_tarski('#skF_2',B_41) ) ),
    inference(resolution,[status(thm)],[c_12,c_64])).

tff(c_8,plain,(
    ! [C_6,A_3,B_4] :
      ( r2_hidden(C_6,A_3)
      | ~ r2_hidden(C_6,B_4)
      | ~ m1_subset_1(B_4,k1_zfmisc_1(A_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_186,plain,(
    ! [A_62,B_63] :
      ( r2_hidden('#skF_3',A_62)
      | ~ m1_subset_1(B_63,k1_zfmisc_1(A_62))
      | ~ r1_tarski('#skF_2',B_63) ) ),
    inference(resolution,[status(thm)],[c_77,c_8])).

tff(c_197,plain,(
    ! [B_64,A_65] :
      ( r2_hidden('#skF_3',B_64)
      | ~ r1_tarski('#skF_2',A_65)
      | ~ r1_tarski(A_65,B_64) ) ),
    inference(resolution,[status(thm)],[c_12,c_186])).

tff(c_208,plain,(
    ! [B_66] :
      ( r2_hidden('#skF_3',B_66)
      | ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),B_66) ) ),
    inference(resolution,[status(thm)],[c_160,c_197])).

tff(c_213,plain,(
    r2_hidden('#skF_3',k1_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_6,c_208])).

tff(c_296,plain,(
    ! [C_73,A_74,B_75] :
      ( m1_connsp_2(C_73,A_74,B_75)
      | ~ r2_hidden(B_75,k1_tops_1(A_74,C_73))
      | ~ m1_subset_1(C_73,k1_zfmisc_1(u1_struct_0(A_74)))
      | ~ m1_subset_1(B_75,u1_struct_0(A_74))
      | ~ l1_pre_topc(A_74)
      | ~ v2_pre_topc(A_74)
      | v2_struct_0(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_298,plain,
    ( m1_connsp_2('#skF_2','#skF_1','#skF_3')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_1'))
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_213,c_296])).

tff(c_306,plain,
    ( m1_connsp_2('#skF_2','#skF_1','#skF_3')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_28,c_30,c_298])).

tff(c_308,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_22,c_306])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:12:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.20/1.27  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.20/1.28  
% 2.20/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.20/1.28  %$ m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 2.20/1.28  
% 2.20/1.28  %Foreground sorts:
% 2.20/1.28  
% 2.20/1.28  
% 2.20/1.28  %Background operators:
% 2.20/1.28  
% 2.20/1.28  
% 2.20/1.28  %Foreground operators:
% 2.20/1.28  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.20/1.28  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 2.20/1.28  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 2.20/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.20/1.28  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.20/1.28  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.20/1.28  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.20/1.28  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 2.20/1.28  tff('#skF_2', type, '#skF_2': $i).
% 2.20/1.28  tff('#skF_3', type, '#skF_3': $i).
% 2.20/1.28  tff('#skF_1', type, '#skF_1': $i).
% 2.20/1.28  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.20/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.20/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.20/1.28  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.20/1.28  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.20/1.28  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.20/1.28  
% 2.20/1.29  tff(f_99, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ((v3_pre_topc(B, A) & r2_hidden(C, B)) => m1_connsp_2(B, A, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_connsp_2)).
% 2.20/1.29  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.20/1.29  tff(f_62, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & r1_tarski(B, C)) => r1_tarski(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_tops_1)).
% 2.20/1.29  tff(f_42, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.20/1.29  tff(f_38, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 2.20/1.29  tff(f_79, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m1_connsp_2(C, A, B) <=> r2_hidden(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_connsp_2)).
% 2.20/1.29  tff(c_36, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.20/1.29  tff(c_22, plain, (~m1_connsp_2('#skF_2', '#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.20/1.29  tff(c_34, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.20/1.29  tff(c_32, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.20/1.29  tff(c_28, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.20/1.29  tff(c_30, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.20/1.29  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.20/1.29  tff(c_26, plain, (v3_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.20/1.29  tff(c_123, plain, (![B_52, A_53, C_54]: (r1_tarski(B_52, k1_tops_1(A_53, C_54)) | ~r1_tarski(B_52, C_54) | ~v3_pre_topc(B_52, A_53) | ~m1_subset_1(C_54, k1_zfmisc_1(u1_struct_0(A_53))) | ~m1_subset_1(B_52, k1_zfmisc_1(u1_struct_0(A_53))) | ~l1_pre_topc(A_53))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.20/1.29  tff(c_128, plain, (![B_52]: (r1_tarski(B_52, k1_tops_1('#skF_1', '#skF_2')) | ~r1_tarski(B_52, '#skF_2') | ~v3_pre_topc(B_52, '#skF_1') | ~m1_subset_1(B_52, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_30, c_123])).
% 2.20/1.29  tff(c_149, plain, (![B_58]: (r1_tarski(B_58, k1_tops_1('#skF_1', '#skF_2')) | ~r1_tarski(B_58, '#skF_2') | ~v3_pre_topc(B_58, '#skF_1') | ~m1_subset_1(B_58, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_128])).
% 2.20/1.29  tff(c_156, plain, (r1_tarski('#skF_2', k1_tops_1('#skF_1', '#skF_2')) | ~r1_tarski('#skF_2', '#skF_2') | ~v3_pre_topc('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_30, c_149])).
% 2.20/1.29  tff(c_160, plain, (r1_tarski('#skF_2', k1_tops_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_6, c_156])).
% 2.20/1.29  tff(c_12, plain, (![A_7, B_8]: (m1_subset_1(A_7, k1_zfmisc_1(B_8)) | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.20/1.29  tff(c_24, plain, (r2_hidden('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.20/1.29  tff(c_60, plain, (![C_37, A_38, B_39]: (r2_hidden(C_37, A_38) | ~r2_hidden(C_37, B_39) | ~m1_subset_1(B_39, k1_zfmisc_1(A_38)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.20/1.29  tff(c_64, plain, (![A_40]: (r2_hidden('#skF_3', A_40) | ~m1_subset_1('#skF_2', k1_zfmisc_1(A_40)))), inference(resolution, [status(thm)], [c_24, c_60])).
% 2.20/1.29  tff(c_77, plain, (![B_41]: (r2_hidden('#skF_3', B_41) | ~r1_tarski('#skF_2', B_41))), inference(resolution, [status(thm)], [c_12, c_64])).
% 2.20/1.29  tff(c_8, plain, (![C_6, A_3, B_4]: (r2_hidden(C_6, A_3) | ~r2_hidden(C_6, B_4) | ~m1_subset_1(B_4, k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.20/1.29  tff(c_186, plain, (![A_62, B_63]: (r2_hidden('#skF_3', A_62) | ~m1_subset_1(B_63, k1_zfmisc_1(A_62)) | ~r1_tarski('#skF_2', B_63))), inference(resolution, [status(thm)], [c_77, c_8])).
% 2.20/1.29  tff(c_197, plain, (![B_64, A_65]: (r2_hidden('#skF_3', B_64) | ~r1_tarski('#skF_2', A_65) | ~r1_tarski(A_65, B_64))), inference(resolution, [status(thm)], [c_12, c_186])).
% 2.20/1.29  tff(c_208, plain, (![B_66]: (r2_hidden('#skF_3', B_66) | ~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), B_66))), inference(resolution, [status(thm)], [c_160, c_197])).
% 2.20/1.29  tff(c_213, plain, (r2_hidden('#skF_3', k1_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_6, c_208])).
% 2.20/1.29  tff(c_296, plain, (![C_73, A_74, B_75]: (m1_connsp_2(C_73, A_74, B_75) | ~r2_hidden(B_75, k1_tops_1(A_74, C_73)) | ~m1_subset_1(C_73, k1_zfmisc_1(u1_struct_0(A_74))) | ~m1_subset_1(B_75, u1_struct_0(A_74)) | ~l1_pre_topc(A_74) | ~v2_pre_topc(A_74) | v2_struct_0(A_74))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.20/1.29  tff(c_298, plain, (m1_connsp_2('#skF_2', '#skF_1', '#skF_3') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_1')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_213, c_296])).
% 2.20/1.29  tff(c_306, plain, (m1_connsp_2('#skF_2', '#skF_1', '#skF_3') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_28, c_30, c_298])).
% 2.20/1.29  tff(c_308, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_22, c_306])).
% 2.20/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.20/1.29  
% 2.20/1.29  Inference rules
% 2.20/1.29  ----------------------
% 2.20/1.29  #Ref     : 0
% 2.20/1.29  #Sup     : 55
% 2.20/1.29  #Fact    : 0
% 2.20/1.29  #Define  : 0
% 2.20/1.29  #Split   : 2
% 2.20/1.29  #Chain   : 0
% 2.20/1.29  #Close   : 0
% 2.20/1.29  
% 2.20/1.29  Ordering : KBO
% 2.20/1.29  
% 2.20/1.29  Simplification rules
% 2.20/1.29  ----------------------
% 2.20/1.29  #Subsume      : 10
% 2.20/1.29  #Demod        : 35
% 2.20/1.29  #Tautology    : 12
% 2.20/1.29  #SimpNegUnit  : 2
% 2.20/1.29  #BackRed      : 0
% 2.20/1.29  
% 2.20/1.29  #Partial instantiations: 0
% 2.20/1.29  #Strategies tried      : 1
% 2.20/1.29  
% 2.20/1.29  Timing (in seconds)
% 2.20/1.29  ----------------------
% 2.20/1.29  Preprocessing        : 0.29
% 2.20/1.29  Parsing              : 0.16
% 2.20/1.29  CNF conversion       : 0.02
% 2.20/1.29  Main loop            : 0.24
% 2.20/1.29  Inferencing          : 0.09
% 2.20/1.29  Reduction            : 0.07
% 2.20/1.29  Demodulation         : 0.05
% 2.20/1.29  BG Simplification    : 0.01
% 2.20/1.29  Subsumption          : 0.06
% 2.20/1.29  Abstraction          : 0.01
% 2.20/1.29  MUC search           : 0.00
% 2.20/1.29  Cooper               : 0.00
% 2.20/1.29  Total                : 0.56
% 2.20/1.29  Index Insertion      : 0.00
% 2.20/1.29  Index Deletion       : 0.00
% 2.20/1.29  Index Matching       : 0.00
% 2.20/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
