%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:32 EST 2020

% Result     : Theorem 2.53s
% Output     : CNFRefutation 2.53s
% Verified   : 
% Statistics : Number of formulae       :   54 (  91 expanded)
%              Number of leaves         :   28 (  45 expanded)
%              Depth                    :    8
%              Number of atoms          :   86 ( 180 expanded)
%              Number of equality atoms :    8 (  20 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m2_connsp_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > l1_struct_0 > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(m2_connsp_2,type,(
    m2_connsp_2: ( $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_84,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => m2_connsp_2(k2_struct_0(A),A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_connsp_2)).

tff(f_51,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_47,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_34,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_36,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_57,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => k1_tops_1(A,k2_struct_0(A)) = k2_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_tops_1)).

tff(f_71,axiom,(
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

tff(c_24,plain,(
    ~ m2_connsp_2(k2_struct_0('#skF_2'),'#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_28,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_16,plain,(
    ! [A_13] :
      ( l1_struct_0(A_13)
      | ~ l1_pre_topc(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_45,plain,(
    ! [A_26] :
      ( u1_struct_0(A_26) = k2_struct_0(A_26)
      | ~ l1_struct_0(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_51,plain,(
    ! [A_29] :
      ( u1_struct_0(A_29) = k2_struct_0(A_29)
      | ~ l1_pre_topc(A_29) ) ),
    inference(resolution,[status(thm)],[c_16,c_45])).

tff(c_55,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_51])).

tff(c_26,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_56,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_26])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_81,plain,(
    ! [C_37,A_38,B_39] :
      ( r2_hidden(C_37,A_38)
      | ~ r2_hidden(C_37,B_39)
      | ~ m1_subset_1(B_39,k1_zfmisc_1(A_38)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_104,plain,(
    ! [A_46,B_47,A_48] :
      ( r2_hidden('#skF_1'(A_46,B_47),A_48)
      | ~ m1_subset_1(A_46,k1_zfmisc_1(A_48))
      | r1_tarski(A_46,B_47) ) ),
    inference(resolution,[status(thm)],[c_6,c_81])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_116,plain,(
    ! [A_49,A_50] :
      ( ~ m1_subset_1(A_49,k1_zfmisc_1(A_50))
      | r1_tarski(A_49,A_50) ) ),
    inference(resolution,[status(thm)],[c_104,c_4])).

tff(c_123,plain,(
    r1_tarski('#skF_3',k2_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_56,c_116])).

tff(c_30,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_8,plain,(
    ! [A_6] : k2_subset_1(A_6) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_10,plain,(
    ! [A_7] : m1_subset_1(k2_subset_1(A_7),k1_zfmisc_1(A_7)) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_33,plain,(
    ! [A_7] : m1_subset_1(A_7,k1_zfmisc_1(A_7)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_10])).

tff(c_18,plain,(
    ! [A_14] :
      ( k1_tops_1(A_14,k2_struct_0(A_14)) = k2_struct_0(A_14)
      | ~ l1_pre_topc(A_14)
      | ~ v2_pre_topc(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_97,plain,(
    ! [C_43,A_44,B_45] :
      ( m2_connsp_2(C_43,A_44,B_45)
      | ~ r1_tarski(B_45,k1_tops_1(A_44,C_43))
      | ~ m1_subset_1(C_43,k1_zfmisc_1(u1_struct_0(A_44)))
      | ~ m1_subset_1(B_45,k1_zfmisc_1(u1_struct_0(A_44)))
      | ~ l1_pre_topc(A_44)
      | ~ v2_pre_topc(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_310,plain,(
    ! [A_90,B_91] :
      ( m2_connsp_2(k2_struct_0(A_90),A_90,B_91)
      | ~ r1_tarski(B_91,k2_struct_0(A_90))
      | ~ m1_subset_1(k2_struct_0(A_90),k1_zfmisc_1(u1_struct_0(A_90)))
      | ~ m1_subset_1(B_91,k1_zfmisc_1(u1_struct_0(A_90)))
      | ~ l1_pre_topc(A_90)
      | ~ v2_pre_topc(A_90)
      | ~ l1_pre_topc(A_90)
      | ~ v2_pre_topc(A_90) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_97])).

tff(c_312,plain,(
    ! [B_91] :
      ( m2_connsp_2(k2_struct_0('#skF_2'),'#skF_2',B_91)
      | ~ r1_tarski(B_91,k2_struct_0('#skF_2'))
      | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ m1_subset_1(B_91,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_55,c_310])).

tff(c_315,plain,(
    ! [B_92] :
      ( m2_connsp_2(k2_struct_0('#skF_2'),'#skF_2',B_92)
      | ~ r1_tarski(B_92,k2_struct_0('#skF_2'))
      | ~ m1_subset_1(B_92,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_30,c_28,c_55,c_33,c_312])).

tff(c_318,plain,
    ( m2_connsp_2(k2_struct_0('#skF_2'),'#skF_2','#skF_3')
    | ~ r1_tarski('#skF_3',k2_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_56,c_315])).

tff(c_325,plain,(
    m2_connsp_2(k2_struct_0('#skF_2'),'#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_318])).

tff(c_327,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_325])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:48:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.53/1.29  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.53/1.30  
% 2.53/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.53/1.30  %$ m2_connsp_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > l1_struct_0 > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 2.53/1.30  
% 2.53/1.30  %Foreground sorts:
% 2.53/1.30  
% 2.53/1.30  
% 2.53/1.30  %Background operators:
% 2.53/1.30  
% 2.53/1.30  
% 2.53/1.30  %Foreground operators:
% 2.53/1.30  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.53/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.53/1.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.53/1.30  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.53/1.30  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.53/1.30  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 2.53/1.30  tff('#skF_2', type, '#skF_2': $i).
% 2.53/1.30  tff('#skF_3', type, '#skF_3': $i).
% 2.53/1.30  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.53/1.30  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.53/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.53/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.53/1.30  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.53/1.30  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.53/1.30  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.53/1.30  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.53/1.30  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.53/1.30  tff(m2_connsp_2, type, m2_connsp_2: ($i * $i * $i) > $o).
% 2.53/1.30  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.53/1.30  
% 2.53/1.31  tff(f_84, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => m2_connsp_2(k2_struct_0(A), A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_connsp_2)).
% 2.53/1.31  tff(f_51, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.53/1.31  tff(f_47, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 2.53/1.31  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.53/1.31  tff(f_43, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 2.53/1.31  tff(f_34, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 2.53/1.31  tff(f_36, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 2.53/1.31  tff(f_57, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (k1_tops_1(A, k2_struct_0(A)) = k2_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_tops_1)).
% 2.53/1.31  tff(f_71, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m2_connsp_2(C, A, B) <=> r1_tarski(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_connsp_2)).
% 2.53/1.31  tff(c_24, plain, (~m2_connsp_2(k2_struct_0('#skF_2'), '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.53/1.31  tff(c_28, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.53/1.31  tff(c_16, plain, (![A_13]: (l1_struct_0(A_13) | ~l1_pre_topc(A_13))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.53/1.31  tff(c_45, plain, (![A_26]: (u1_struct_0(A_26)=k2_struct_0(A_26) | ~l1_struct_0(A_26))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.53/1.31  tff(c_51, plain, (![A_29]: (u1_struct_0(A_29)=k2_struct_0(A_29) | ~l1_pre_topc(A_29))), inference(resolution, [status(thm)], [c_16, c_45])).
% 2.53/1.31  tff(c_55, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_28, c_51])).
% 2.53/1.31  tff(c_26, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.53/1.31  tff(c_56, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_55, c_26])).
% 2.53/1.31  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.53/1.31  tff(c_81, plain, (![C_37, A_38, B_39]: (r2_hidden(C_37, A_38) | ~r2_hidden(C_37, B_39) | ~m1_subset_1(B_39, k1_zfmisc_1(A_38)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.53/1.31  tff(c_104, plain, (![A_46, B_47, A_48]: (r2_hidden('#skF_1'(A_46, B_47), A_48) | ~m1_subset_1(A_46, k1_zfmisc_1(A_48)) | r1_tarski(A_46, B_47))), inference(resolution, [status(thm)], [c_6, c_81])).
% 2.53/1.31  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.53/1.31  tff(c_116, plain, (![A_49, A_50]: (~m1_subset_1(A_49, k1_zfmisc_1(A_50)) | r1_tarski(A_49, A_50))), inference(resolution, [status(thm)], [c_104, c_4])).
% 2.53/1.31  tff(c_123, plain, (r1_tarski('#skF_3', k2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_56, c_116])).
% 2.53/1.31  tff(c_30, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.53/1.31  tff(c_8, plain, (![A_6]: (k2_subset_1(A_6)=A_6)), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.53/1.31  tff(c_10, plain, (![A_7]: (m1_subset_1(k2_subset_1(A_7), k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.53/1.31  tff(c_33, plain, (![A_7]: (m1_subset_1(A_7, k1_zfmisc_1(A_7)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_10])).
% 2.53/1.31  tff(c_18, plain, (![A_14]: (k1_tops_1(A_14, k2_struct_0(A_14))=k2_struct_0(A_14) | ~l1_pre_topc(A_14) | ~v2_pre_topc(A_14))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.53/1.31  tff(c_97, plain, (![C_43, A_44, B_45]: (m2_connsp_2(C_43, A_44, B_45) | ~r1_tarski(B_45, k1_tops_1(A_44, C_43)) | ~m1_subset_1(C_43, k1_zfmisc_1(u1_struct_0(A_44))) | ~m1_subset_1(B_45, k1_zfmisc_1(u1_struct_0(A_44))) | ~l1_pre_topc(A_44) | ~v2_pre_topc(A_44))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.53/1.31  tff(c_310, plain, (![A_90, B_91]: (m2_connsp_2(k2_struct_0(A_90), A_90, B_91) | ~r1_tarski(B_91, k2_struct_0(A_90)) | ~m1_subset_1(k2_struct_0(A_90), k1_zfmisc_1(u1_struct_0(A_90))) | ~m1_subset_1(B_91, k1_zfmisc_1(u1_struct_0(A_90))) | ~l1_pre_topc(A_90) | ~v2_pre_topc(A_90) | ~l1_pre_topc(A_90) | ~v2_pre_topc(A_90))), inference(superposition, [status(thm), theory('equality')], [c_18, c_97])).
% 2.53/1.31  tff(c_312, plain, (![B_91]: (m2_connsp_2(k2_struct_0('#skF_2'), '#skF_2', B_91) | ~r1_tarski(B_91, k2_struct_0('#skF_2')) | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~m1_subset_1(B_91, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_55, c_310])).
% 2.53/1.31  tff(c_315, plain, (![B_92]: (m2_connsp_2(k2_struct_0('#skF_2'), '#skF_2', B_92) | ~r1_tarski(B_92, k2_struct_0('#skF_2')) | ~m1_subset_1(B_92, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_30, c_28, c_55, c_33, c_312])).
% 2.53/1.31  tff(c_318, plain, (m2_connsp_2(k2_struct_0('#skF_2'), '#skF_2', '#skF_3') | ~r1_tarski('#skF_3', k2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_56, c_315])).
% 2.53/1.31  tff(c_325, plain, (m2_connsp_2(k2_struct_0('#skF_2'), '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_123, c_318])).
% 2.53/1.31  tff(c_327, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_325])).
% 2.53/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.53/1.31  
% 2.53/1.31  Inference rules
% 2.53/1.31  ----------------------
% 2.53/1.31  #Ref     : 0
% 2.53/1.31  #Sup     : 70
% 2.53/1.31  #Fact    : 0
% 2.53/1.31  #Define  : 0
% 2.53/1.31  #Split   : 3
% 2.53/1.31  #Chain   : 0
% 2.53/1.31  #Close   : 0
% 2.53/1.31  
% 2.53/1.31  Ordering : KBO
% 2.53/1.31  
% 2.53/1.31  Simplification rules
% 2.53/1.31  ----------------------
% 2.53/1.31  #Subsume      : 15
% 2.53/1.31  #Demod        : 26
% 2.53/1.31  #Tautology    : 10
% 2.53/1.31  #SimpNegUnit  : 1
% 2.53/1.31  #BackRed      : 1
% 2.53/1.31  
% 2.53/1.31  #Partial instantiations: 0
% 2.53/1.31  #Strategies tried      : 1
% 2.53/1.31  
% 2.53/1.31  Timing (in seconds)
% 2.53/1.31  ----------------------
% 2.53/1.32  Preprocessing        : 0.30
% 2.53/1.32  Parsing              : 0.16
% 2.53/1.32  CNF conversion       : 0.02
% 2.53/1.32  Main loop            : 0.26
% 2.53/1.32  Inferencing          : 0.09
% 2.53/1.32  Reduction            : 0.07
% 2.53/1.32  Demodulation         : 0.05
% 2.53/1.32  BG Simplification    : 0.01
% 2.53/1.32  Subsumption          : 0.07
% 2.53/1.32  Abstraction          : 0.01
% 2.53/1.32  MUC search           : 0.00
% 2.53/1.32  Cooper               : 0.00
% 2.53/1.32  Total                : 0.58
% 2.53/1.32  Index Insertion      : 0.00
% 2.53/1.32  Index Deletion       : 0.00
% 2.53/1.32  Index Matching       : 0.00
% 2.53/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
