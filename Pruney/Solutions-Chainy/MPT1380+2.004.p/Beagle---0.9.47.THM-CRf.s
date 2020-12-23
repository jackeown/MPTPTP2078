%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:06 EST 2020

% Result     : Theorem 1.99s
% Output     : CNFRefutation 2.21s
% Verified   : 
% Statistics : Number of formulae       :   48 (  69 expanded)
%              Number of leaves         :   22 (  37 expanded)
%              Depth                    :   10
%              Number of atoms          :   86 ( 189 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_83,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_connsp_2)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_46,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( ( v3_pre_topc(B,A)
                  & r1_tarski(B,C) )
               => r1_tarski(B,k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_tops_1)).

tff(f_63,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_connsp_2)).

tff(c_28,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_14,plain,(
    ~ m1_connsp_2('#skF_3','#skF_2','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_26,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_24,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_20,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_22,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_30,plain,(
    ! [A_26,B_27] :
      ( ~ r2_hidden('#skF_1'(A_26,B_27),B_27)
      | r1_tarski(A_26,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_35,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_30])).

tff(c_18,plain,(
    v3_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_61,plain,(
    ! [B_38,A_39,C_40] :
      ( r1_tarski(B_38,k1_tops_1(A_39,C_40))
      | ~ r1_tarski(B_38,C_40)
      | ~ v3_pre_topc(B_38,A_39)
      | ~ m1_subset_1(C_40,k1_zfmisc_1(u1_struct_0(A_39)))
      | ~ m1_subset_1(B_38,k1_zfmisc_1(u1_struct_0(A_39)))
      | ~ l1_pre_topc(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_63,plain,(
    ! [B_38] :
      ( r1_tarski(B_38,k1_tops_1('#skF_2','#skF_3'))
      | ~ r1_tarski(B_38,'#skF_3')
      | ~ v3_pre_topc(B_38,'#skF_2')
      | ~ m1_subset_1(B_38,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_22,c_61])).

tff(c_71,plain,(
    ! [B_45] :
      ( r1_tarski(B_45,k1_tops_1('#skF_2','#skF_3'))
      | ~ r1_tarski(B_45,'#skF_3')
      | ~ v3_pre_topc(B_45,'#skF_2')
      | ~ m1_subset_1(B_45,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_63])).

tff(c_74,plain,
    ( r1_tarski('#skF_3',k1_tops_1('#skF_2','#skF_3'))
    | ~ r1_tarski('#skF_3','#skF_3')
    | ~ v3_pre_topc('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_22,c_71])).

tff(c_77,plain,(
    r1_tarski('#skF_3',k1_tops_1('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_35,c_74])).

tff(c_16,plain,(
    r2_hidden('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_37,plain,(
    ! [C_29,B_30,A_31] :
      ( r2_hidden(C_29,B_30)
      | ~ r2_hidden(C_29,A_31)
      | ~ r1_tarski(A_31,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_44,plain,(
    ! [B_32] :
      ( r2_hidden('#skF_4',B_32)
      | ~ r1_tarski('#skF_3',B_32) ) ),
    inference(resolution,[status(thm)],[c_16,c_37])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_47,plain,(
    ! [B_2,B_32] :
      ( r2_hidden('#skF_4',B_2)
      | ~ r1_tarski(B_32,B_2)
      | ~ r1_tarski('#skF_3',B_32) ) ),
    inference(resolution,[status(thm)],[c_44,c_2])).

tff(c_81,plain,
    ( r2_hidden('#skF_4',k1_tops_1('#skF_2','#skF_3'))
    | ~ r1_tarski('#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_77,c_47])).

tff(c_85,plain,(
    r2_hidden('#skF_4',k1_tops_1('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_35,c_81])).

tff(c_184,plain,(
    ! [C_69,A_70,B_71] :
      ( m1_connsp_2(C_69,A_70,B_71)
      | ~ r2_hidden(B_71,k1_tops_1(A_70,C_69))
      | ~ m1_subset_1(C_69,k1_zfmisc_1(u1_struct_0(A_70)))
      | ~ m1_subset_1(B_71,u1_struct_0(A_70))
      | ~ l1_pre_topc(A_70)
      | ~ v2_pre_topc(A_70)
      | v2_struct_0(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_191,plain,
    ( m1_connsp_2('#skF_3','#skF_2','#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_85,c_184])).

tff(c_210,plain,
    ( m1_connsp_2('#skF_3','#skF_2','#skF_4')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_20,c_22,c_191])).

tff(c_212,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_14,c_210])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:49:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.99/1.22  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.16/1.23  
% 2.16/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.16/1.23  %$ m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.16/1.23  
% 2.16/1.23  %Foreground sorts:
% 2.16/1.23  
% 2.16/1.23  
% 2.16/1.23  %Background operators:
% 2.16/1.23  
% 2.16/1.23  
% 2.16/1.23  %Foreground operators:
% 2.16/1.23  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.16/1.23  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 2.16/1.23  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 2.16/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.16/1.23  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.16/1.23  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.16/1.23  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.16/1.23  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 2.16/1.23  tff('#skF_2', type, '#skF_2': $i).
% 2.16/1.23  tff('#skF_3', type, '#skF_3': $i).
% 2.16/1.23  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.16/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.16/1.23  tff('#skF_4', type, '#skF_4': $i).
% 2.16/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.16/1.23  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.16/1.23  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.16/1.23  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.16/1.23  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.16/1.23  
% 2.21/1.24  tff(f_83, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ((v3_pre_topc(B, A) & r2_hidden(C, B)) => m1_connsp_2(B, A, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_connsp_2)).
% 2.21/1.24  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.21/1.24  tff(f_46, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & r1_tarski(B, C)) => r1_tarski(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_tops_1)).
% 2.21/1.24  tff(f_63, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m1_connsp_2(C, A, B) <=> r2_hidden(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_connsp_2)).
% 2.21/1.24  tff(c_28, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.21/1.24  tff(c_14, plain, (~m1_connsp_2('#skF_3', '#skF_2', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.21/1.24  tff(c_26, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.21/1.24  tff(c_24, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.21/1.24  tff(c_20, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.21/1.24  tff(c_22, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.21/1.24  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.21/1.24  tff(c_30, plain, (![A_26, B_27]: (~r2_hidden('#skF_1'(A_26, B_27), B_27) | r1_tarski(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.21/1.24  tff(c_35, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_30])).
% 2.21/1.24  tff(c_18, plain, (v3_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.21/1.24  tff(c_61, plain, (![B_38, A_39, C_40]: (r1_tarski(B_38, k1_tops_1(A_39, C_40)) | ~r1_tarski(B_38, C_40) | ~v3_pre_topc(B_38, A_39) | ~m1_subset_1(C_40, k1_zfmisc_1(u1_struct_0(A_39))) | ~m1_subset_1(B_38, k1_zfmisc_1(u1_struct_0(A_39))) | ~l1_pre_topc(A_39))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.21/1.24  tff(c_63, plain, (![B_38]: (r1_tarski(B_38, k1_tops_1('#skF_2', '#skF_3')) | ~r1_tarski(B_38, '#skF_3') | ~v3_pre_topc(B_38, '#skF_2') | ~m1_subset_1(B_38, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_22, c_61])).
% 2.21/1.24  tff(c_71, plain, (![B_45]: (r1_tarski(B_45, k1_tops_1('#skF_2', '#skF_3')) | ~r1_tarski(B_45, '#skF_3') | ~v3_pre_topc(B_45, '#skF_2') | ~m1_subset_1(B_45, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_63])).
% 2.21/1.24  tff(c_74, plain, (r1_tarski('#skF_3', k1_tops_1('#skF_2', '#skF_3')) | ~r1_tarski('#skF_3', '#skF_3') | ~v3_pre_topc('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_22, c_71])).
% 2.21/1.24  tff(c_77, plain, (r1_tarski('#skF_3', k1_tops_1('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_35, c_74])).
% 2.21/1.24  tff(c_16, plain, (r2_hidden('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.21/1.24  tff(c_37, plain, (![C_29, B_30, A_31]: (r2_hidden(C_29, B_30) | ~r2_hidden(C_29, A_31) | ~r1_tarski(A_31, B_30))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.21/1.24  tff(c_44, plain, (![B_32]: (r2_hidden('#skF_4', B_32) | ~r1_tarski('#skF_3', B_32))), inference(resolution, [status(thm)], [c_16, c_37])).
% 2.21/1.24  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.21/1.24  tff(c_47, plain, (![B_2, B_32]: (r2_hidden('#skF_4', B_2) | ~r1_tarski(B_32, B_2) | ~r1_tarski('#skF_3', B_32))), inference(resolution, [status(thm)], [c_44, c_2])).
% 2.21/1.24  tff(c_81, plain, (r2_hidden('#skF_4', k1_tops_1('#skF_2', '#skF_3')) | ~r1_tarski('#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_77, c_47])).
% 2.21/1.24  tff(c_85, plain, (r2_hidden('#skF_4', k1_tops_1('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_35, c_81])).
% 2.21/1.24  tff(c_184, plain, (![C_69, A_70, B_71]: (m1_connsp_2(C_69, A_70, B_71) | ~r2_hidden(B_71, k1_tops_1(A_70, C_69)) | ~m1_subset_1(C_69, k1_zfmisc_1(u1_struct_0(A_70))) | ~m1_subset_1(B_71, u1_struct_0(A_70)) | ~l1_pre_topc(A_70) | ~v2_pre_topc(A_70) | v2_struct_0(A_70))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.21/1.24  tff(c_191, plain, (m1_connsp_2('#skF_3', '#skF_2', '#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_85, c_184])).
% 2.21/1.24  tff(c_210, plain, (m1_connsp_2('#skF_3', '#skF_2', '#skF_4') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_20, c_22, c_191])).
% 2.21/1.24  tff(c_212, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_14, c_210])).
% 2.21/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.21/1.24  
% 2.21/1.24  Inference rules
% 2.21/1.24  ----------------------
% 2.21/1.24  #Ref     : 0
% 2.21/1.24  #Sup     : 41
% 2.21/1.24  #Fact    : 0
% 2.21/1.24  #Define  : 0
% 2.21/1.24  #Split   : 1
% 2.21/1.24  #Chain   : 0
% 2.21/1.24  #Close   : 0
% 2.21/1.24  
% 2.21/1.24  Ordering : KBO
% 2.21/1.24  
% 2.21/1.24  Simplification rules
% 2.21/1.24  ----------------------
% 2.21/1.24  #Subsume      : 12
% 2.21/1.24  #Demod        : 16
% 2.21/1.24  #Tautology    : 5
% 2.21/1.24  #SimpNegUnit  : 3
% 2.21/1.24  #BackRed      : 0
% 2.21/1.24  
% 2.21/1.24  #Partial instantiations: 0
% 2.21/1.24  #Strategies tried      : 1
% 2.21/1.24  
% 2.21/1.24  Timing (in seconds)
% 2.21/1.24  ----------------------
% 2.21/1.25  Preprocessing        : 0.27
% 2.21/1.25  Parsing              : 0.15
% 2.21/1.25  CNF conversion       : 0.02
% 2.21/1.25  Main loop            : 0.22
% 2.21/1.25  Inferencing          : 0.09
% 2.21/1.25  Reduction            : 0.06
% 2.21/1.25  Demodulation         : 0.04
% 2.21/1.25  BG Simplification    : 0.01
% 2.21/1.25  Subsumption          : 0.05
% 2.21/1.25  Abstraction          : 0.01
% 2.21/1.25  MUC search           : 0.00
% 2.21/1.25  Cooper               : 0.00
% 2.21/1.25  Total                : 0.51
% 2.21/1.25  Index Insertion      : 0.00
% 2.21/1.25  Index Deletion       : 0.00
% 2.21/1.25  Index Matching       : 0.00
% 2.21/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
