%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:06 EST 2020

% Result     : Theorem 2.95s
% Output     : CNFRefutation 2.95s
% Verified   : 
% Statistics : Number of formulae       :   46 (  56 expanded)
%              Number of leaves         :   24 (  32 expanded)
%              Depth                    :    9
%              Number of atoms          :   70 ( 128 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_connsp_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > l1_pre_topc > k3_xboole_0 > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(m1_connsp_2,type,(
    m1_connsp_2: ( $i * $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_94,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => ( m1_connsp_2(B,A,C)
                 => r2_hidden(C,B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_connsp_2)).

tff(f_62,axiom,(
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

tff(f_45,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

tff(c_30,plain,(
    ~ r2_hidden('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_32,plain,(
    m1_connsp_2('#skF_4','#skF_3','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_34,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_42,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_40,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_38,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_36,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_622,plain,(
    ! [B_95,A_96,C_97] :
      ( r2_hidden(B_95,k1_tops_1(A_96,C_97))
      | ~ m1_connsp_2(C_97,A_96,B_95)
      | ~ m1_subset_1(C_97,k1_zfmisc_1(u1_struct_0(A_96)))
      | ~ m1_subset_1(B_95,u1_struct_0(A_96))
      | ~ l1_pre_topc(A_96)
      | ~ v2_pre_topc(A_96)
      | v2_struct_0(A_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_624,plain,(
    ! [B_95] :
      ( r2_hidden(B_95,k1_tops_1('#skF_3','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_3',B_95)
      | ~ m1_subset_1(B_95,u1_struct_0('#skF_3'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_36,c_622])).

tff(c_627,plain,(
    ! [B_95] :
      ( r2_hidden(B_95,k1_tops_1('#skF_3','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_3',B_95)
      | ~ m1_subset_1(B_95,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_624])).

tff(c_629,plain,(
    ! [B_98] :
      ( r2_hidden(B_98,k1_tops_1('#skF_3','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_3',B_98)
      | ~ m1_subset_1(B_98,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_627])).

tff(c_55,plain,(
    ! [A_38,B_39] :
      ( r1_tarski(k1_tops_1(A_38,B_39),B_39)
      | ~ m1_subset_1(B_39,k1_zfmisc_1(u1_struct_0(A_38)))
      | ~ l1_pre_topc(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_57,plain,
    ( r1_tarski(k1_tops_1('#skF_3','#skF_4'),'#skF_4')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_55])).

tff(c_60,plain,(
    r1_tarski(k1_tops_1('#skF_3','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_57])).

tff(c_20,plain,(
    ! [A_7,B_8] :
      ( k3_xboole_0(A_7,B_8) = A_7
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_64,plain,(
    k3_xboole_0(k1_tops_1('#skF_3','#skF_4'),'#skF_4') = k1_tops_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_20])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,k3_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_71,plain,(
    ! [D_6] :
      ( r2_hidden(D_6,'#skF_4')
      | ~ r2_hidden(D_6,k1_tops_1('#skF_3','#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_4])).

tff(c_651,plain,(
    ! [B_99] :
      ( r2_hidden(B_99,'#skF_4')
      | ~ m1_connsp_2('#skF_4','#skF_3',B_99)
      | ~ m1_subset_1(B_99,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_629,c_71])).

tff(c_654,plain,
    ( r2_hidden('#skF_5','#skF_4')
    | ~ m1_connsp_2('#skF_4','#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_34,c_651])).

tff(c_657,plain,(
    r2_hidden('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_654])).

tff(c_659,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_657])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n015.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:53:08 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.95/1.45  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.95/1.45  
% 2.95/1.45  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.95/1.45  %$ m1_connsp_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > l1_pre_topc > k3_xboole_0 > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4
% 2.95/1.45  
% 2.95/1.45  %Foreground sorts:
% 2.95/1.45  
% 2.95/1.45  
% 2.95/1.45  %Background operators:
% 2.95/1.45  
% 2.95/1.45  
% 2.95/1.45  %Foreground operators:
% 2.95/1.45  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.95/1.45  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 2.95/1.45  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.95/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.95/1.45  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.95/1.45  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.95/1.45  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.95/1.45  tff('#skF_5', type, '#skF_5': $i).
% 2.95/1.45  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 2.95/1.45  tff('#skF_3', type, '#skF_3': $i).
% 2.95/1.45  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.95/1.45  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.95/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.95/1.45  tff('#skF_4', type, '#skF_4': $i).
% 2.95/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.95/1.45  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.95/1.45  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.95/1.45  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.95/1.45  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.95/1.45  
% 2.95/1.46  tff(f_94, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (m1_connsp_2(B, A, C) => r2_hidden(C, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_connsp_2)).
% 2.95/1.46  tff(f_62, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m1_connsp_2(C, A, B) <=> r2_hidden(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_connsp_2)).
% 2.95/1.46  tff(f_45, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tops_1)).
% 2.95/1.46  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.95/1.46  tff(f_34, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 2.95/1.46  tff(c_30, plain, (~r2_hidden('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.95/1.46  tff(c_32, plain, (m1_connsp_2('#skF_4', '#skF_3', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.95/1.46  tff(c_34, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.95/1.46  tff(c_42, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.95/1.46  tff(c_40, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.95/1.46  tff(c_38, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.95/1.46  tff(c_36, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.95/1.46  tff(c_622, plain, (![B_95, A_96, C_97]: (r2_hidden(B_95, k1_tops_1(A_96, C_97)) | ~m1_connsp_2(C_97, A_96, B_95) | ~m1_subset_1(C_97, k1_zfmisc_1(u1_struct_0(A_96))) | ~m1_subset_1(B_95, u1_struct_0(A_96)) | ~l1_pre_topc(A_96) | ~v2_pre_topc(A_96) | v2_struct_0(A_96))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.95/1.46  tff(c_624, plain, (![B_95]: (r2_hidden(B_95, k1_tops_1('#skF_3', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_3', B_95) | ~m1_subset_1(B_95, u1_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_36, c_622])).
% 2.95/1.46  tff(c_627, plain, (![B_95]: (r2_hidden(B_95, k1_tops_1('#skF_3', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_3', B_95) | ~m1_subset_1(B_95, u1_struct_0('#skF_3')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_624])).
% 2.95/1.46  tff(c_629, plain, (![B_98]: (r2_hidden(B_98, k1_tops_1('#skF_3', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_3', B_98) | ~m1_subset_1(B_98, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_42, c_627])).
% 2.95/1.46  tff(c_55, plain, (![A_38, B_39]: (r1_tarski(k1_tops_1(A_38, B_39), B_39) | ~m1_subset_1(B_39, k1_zfmisc_1(u1_struct_0(A_38))) | ~l1_pre_topc(A_38))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.95/1.46  tff(c_57, plain, (r1_tarski(k1_tops_1('#skF_3', '#skF_4'), '#skF_4') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_36, c_55])).
% 2.95/1.46  tff(c_60, plain, (r1_tarski(k1_tops_1('#skF_3', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_57])).
% 2.95/1.46  tff(c_20, plain, (![A_7, B_8]: (k3_xboole_0(A_7, B_8)=A_7 | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.95/1.46  tff(c_64, plain, (k3_xboole_0(k1_tops_1('#skF_3', '#skF_4'), '#skF_4')=k1_tops_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_60, c_20])).
% 2.95/1.46  tff(c_4, plain, (![D_6, B_2, A_1]: (r2_hidden(D_6, B_2) | ~r2_hidden(D_6, k3_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.95/1.46  tff(c_71, plain, (![D_6]: (r2_hidden(D_6, '#skF_4') | ~r2_hidden(D_6, k1_tops_1('#skF_3', '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_64, c_4])).
% 2.95/1.46  tff(c_651, plain, (![B_99]: (r2_hidden(B_99, '#skF_4') | ~m1_connsp_2('#skF_4', '#skF_3', B_99) | ~m1_subset_1(B_99, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_629, c_71])).
% 2.95/1.46  tff(c_654, plain, (r2_hidden('#skF_5', '#skF_4') | ~m1_connsp_2('#skF_4', '#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_34, c_651])).
% 2.95/1.46  tff(c_657, plain, (r2_hidden('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_654])).
% 2.95/1.46  tff(c_659, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_657])).
% 2.95/1.46  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.95/1.46  
% 2.95/1.46  Inference rules
% 2.95/1.46  ----------------------
% 2.95/1.46  #Ref     : 0
% 2.95/1.46  #Sup     : 129
% 2.95/1.46  #Fact    : 0
% 2.95/1.46  #Define  : 0
% 2.95/1.46  #Split   : 0
% 2.95/1.46  #Chain   : 0
% 2.95/1.46  #Close   : 0
% 2.95/1.46  
% 2.95/1.46  Ordering : KBO
% 2.95/1.46  
% 2.95/1.46  Simplification rules
% 2.95/1.46  ----------------------
% 2.95/1.46  #Subsume      : 36
% 2.95/1.46  #Demod        : 69
% 2.95/1.46  #Tautology    : 16
% 2.95/1.46  #SimpNegUnit  : 3
% 2.95/1.46  #BackRed      : 0
% 2.95/1.46  
% 2.95/1.46  #Partial instantiations: 0
% 2.95/1.46  #Strategies tried      : 1
% 2.95/1.46  
% 2.95/1.46  Timing (in seconds)
% 2.95/1.46  ----------------------
% 2.95/1.47  Preprocessing        : 0.29
% 2.95/1.47  Parsing              : 0.16
% 2.95/1.47  CNF conversion       : 0.02
% 2.95/1.47  Main loop            : 0.40
% 2.95/1.47  Inferencing          : 0.16
% 2.95/1.47  Reduction            : 0.10
% 2.95/1.47  Demodulation         : 0.07
% 2.95/1.47  BG Simplification    : 0.02
% 2.95/1.47  Subsumption          : 0.10
% 2.95/1.47  Abstraction          : 0.02
% 2.95/1.47  MUC search           : 0.00
% 2.95/1.47  Cooper               : 0.00
% 2.95/1.47  Total                : 0.72
% 2.95/1.47  Index Insertion      : 0.00
% 2.95/1.47  Index Deletion       : 0.00
% 2.95/1.47  Index Matching       : 0.00
% 2.95/1.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
