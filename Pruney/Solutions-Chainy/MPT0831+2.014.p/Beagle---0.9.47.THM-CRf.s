%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:34 EST 2020

% Result     : Theorem 3.23s
% Output     : CNFRefutation 3.37s
% Verified   : 
% Statistics : Number of formulae       :   52 (  61 expanded)
%              Number of leaves         :   26 (  32 expanded)
%              Depth                    :    9
%              Number of atoms          :   70 (  90 expanded)
%              Number of equality atoms :    9 (   9 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k5_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k5_relset_1,type,(
    k5_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_76,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A)))
       => ( r1_tarski(B,C)
         => r2_relset_1(B,A,k5_relset_1(B,A,D,C),D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_relset_1)).

tff(f_69,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => ( r1_tarski(k2_zfmisc_1(A,C),k2_zfmisc_1(B,C))
        & r1_tarski(k2_zfmisc_1(C,A),k2_zfmisc_1(C,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t118_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_61,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k5_relset_1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_relset_1)).

tff(c_30,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_238,plain,(
    ! [A_82,B_83,D_84] :
      ( r2_relset_1(A_82,B_83,D_84,D_84)
      | ~ m1_subset_1(D_84,k1_zfmisc_1(k2_zfmisc_1(A_82,B_83))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_245,plain,(
    r2_relset_1('#skF_2','#skF_1','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_238])).

tff(c_28,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_41,plain,(
    ! [C_29,A_30,B_31] :
      ( v1_relat_1(C_29)
      | ~ m1_subset_1(C_29,k1_zfmisc_1(k2_zfmisc_1(A_30,B_31))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_50,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_41])).

tff(c_32,plain,(
    ! [A_27,B_28] :
      ( r1_tarski(A_27,B_28)
      | ~ m1_subset_1(A_27,k1_zfmisc_1(B_28)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_40,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_30,c_32])).

tff(c_132,plain,(
    ! [A_58,C_59,B_60] :
      ( r1_tarski(k2_zfmisc_1(A_58,C_59),k2_zfmisc_1(B_60,C_59))
      | ~ r1_tarski(A_58,B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,C_3)
      | ~ r1_tarski(B_2,C_3)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_642,plain,(
    ! [A_189,B_190,C_191,A_192] :
      ( r1_tarski(A_189,k2_zfmisc_1(B_190,C_191))
      | ~ r1_tarski(A_189,k2_zfmisc_1(A_192,C_191))
      | ~ r1_tarski(A_192,B_190) ) ),
    inference(resolution,[status(thm)],[c_132,c_2])).

tff(c_658,plain,(
    ! [B_193] :
      ( r1_tarski('#skF_4',k2_zfmisc_1(B_193,'#skF_1'))
      | ~ r1_tarski('#skF_2',B_193) ) ),
    inference(resolution,[status(thm)],[c_40,c_642])).

tff(c_10,plain,(
    ! [A_7,B_8] :
      ( m1_subset_1(A_7,k1_zfmisc_1(B_8))
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_58,plain,(
    ! [C_37,A_38,B_39] :
      ( v4_relat_1(C_37,A_38)
      | ~ m1_subset_1(C_37,k1_zfmisc_1(k2_zfmisc_1(A_38,B_39))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_66,plain,(
    ! [A_7,A_38,B_39] :
      ( v4_relat_1(A_7,A_38)
      | ~ r1_tarski(A_7,k2_zfmisc_1(A_38,B_39)) ) ),
    inference(resolution,[status(thm)],[c_10,c_58])).

tff(c_743,plain,(
    ! [B_194] :
      ( v4_relat_1('#skF_4',B_194)
      | ~ r1_tarski('#skF_2',B_194) ) ),
    inference(resolution,[status(thm)],[c_658,c_66])).

tff(c_12,plain,(
    ! [B_10,A_9] :
      ( k7_relat_1(B_10,A_9) = B_10
      | ~ v4_relat_1(B_10,A_9)
      | ~ v1_relat_1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_746,plain,(
    ! [B_194] :
      ( k7_relat_1('#skF_4',B_194) = '#skF_4'
      | ~ v1_relat_1('#skF_4')
      | ~ r1_tarski('#skF_2',B_194) ) ),
    inference(resolution,[status(thm)],[c_743,c_12])).

tff(c_750,plain,(
    ! [B_195] :
      ( k7_relat_1('#skF_4',B_195) = '#skF_4'
      | ~ r1_tarski('#skF_2',B_195) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_746])).

tff(c_759,plain,(
    k7_relat_1('#skF_4','#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_28,c_750])).

tff(c_280,plain,(
    ! [A_95,B_96,C_97,D_98] :
      ( k5_relset_1(A_95,B_96,C_97,D_98) = k7_relat_1(C_97,D_98)
      | ~ m1_subset_1(C_97,k1_zfmisc_1(k2_zfmisc_1(A_95,B_96))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_287,plain,(
    ! [D_98] : k5_relset_1('#skF_2','#skF_1','#skF_4',D_98) = k7_relat_1('#skF_4',D_98) ),
    inference(resolution,[status(thm)],[c_30,c_280])).

tff(c_26,plain,(
    ~ r2_relset_1('#skF_2','#skF_1',k5_relset_1('#skF_2','#skF_1','#skF_4','#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_288,plain,(
    ~ r2_relset_1('#skF_2','#skF_1',k7_relat_1('#skF_4','#skF_3'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_287,c_26])).

tff(c_760,plain,(
    ~ r2_relset_1('#skF_2','#skF_1','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_759,c_288])).

tff(c_763,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_245,c_760])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n011.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:54:57 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.23/1.52  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.23/1.52  
% 3.23/1.52  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.23/1.53  %$ r2_relset_1 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k5_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.23/1.53  
% 3.23/1.53  %Foreground sorts:
% 3.23/1.53  
% 3.23/1.53  
% 3.23/1.53  %Background operators:
% 3.23/1.53  
% 3.23/1.53  
% 3.23/1.53  %Foreground operators:
% 3.23/1.53  tff(k5_relset_1, type, k5_relset_1: ($i * $i * $i * $i) > $i).
% 3.23/1.53  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.23/1.53  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 3.23/1.53  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.23/1.53  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.23/1.53  tff('#skF_2', type, '#skF_2': $i).
% 3.23/1.53  tff('#skF_3', type, '#skF_3': $i).
% 3.23/1.53  tff('#skF_1', type, '#skF_1': $i).
% 3.23/1.53  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.23/1.53  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.23/1.53  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.23/1.53  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.23/1.53  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.23/1.53  tff('#skF_4', type, '#skF_4': $i).
% 3.23/1.53  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.23/1.53  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.23/1.53  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.23/1.53  
% 3.37/1.54  tff(f_76, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A))) => (r1_tarski(B, C) => r2_relset_1(B, A, k5_relset_1(B, A, D, C), D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_relset_1)).
% 3.37/1.54  tff(f_69, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 3.37/1.54  tff(f_51, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.37/1.54  tff(f_41, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.37/1.54  tff(f_37, axiom, (![A, B, C]: (r1_tarski(A, B) => (r1_tarski(k2_zfmisc_1(A, C), k2_zfmisc_1(B, C)) & r1_tarski(k2_zfmisc_1(C, A), k2_zfmisc_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t118_zfmisc_1)).
% 3.37/1.54  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 3.37/1.54  tff(f_57, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.37/1.54  tff(f_47, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 3.37/1.54  tff(f_61, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k5_relset_1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k5_relset_1)).
% 3.37/1.54  tff(c_30, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.37/1.54  tff(c_238, plain, (![A_82, B_83, D_84]: (r2_relset_1(A_82, B_83, D_84, D_84) | ~m1_subset_1(D_84, k1_zfmisc_1(k2_zfmisc_1(A_82, B_83))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.37/1.54  tff(c_245, plain, (r2_relset_1('#skF_2', '#skF_1', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_30, c_238])).
% 3.37/1.54  tff(c_28, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.37/1.54  tff(c_41, plain, (![C_29, A_30, B_31]: (v1_relat_1(C_29) | ~m1_subset_1(C_29, k1_zfmisc_1(k2_zfmisc_1(A_30, B_31))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.37/1.54  tff(c_50, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_30, c_41])).
% 3.37/1.54  tff(c_32, plain, (![A_27, B_28]: (r1_tarski(A_27, B_28) | ~m1_subset_1(A_27, k1_zfmisc_1(B_28)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.37/1.54  tff(c_40, plain, (r1_tarski('#skF_4', k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_30, c_32])).
% 3.37/1.54  tff(c_132, plain, (![A_58, C_59, B_60]: (r1_tarski(k2_zfmisc_1(A_58, C_59), k2_zfmisc_1(B_60, C_59)) | ~r1_tarski(A_58, B_60))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.37/1.54  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, C_3) | ~r1_tarski(B_2, C_3) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.37/1.54  tff(c_642, plain, (![A_189, B_190, C_191, A_192]: (r1_tarski(A_189, k2_zfmisc_1(B_190, C_191)) | ~r1_tarski(A_189, k2_zfmisc_1(A_192, C_191)) | ~r1_tarski(A_192, B_190))), inference(resolution, [status(thm)], [c_132, c_2])).
% 3.37/1.54  tff(c_658, plain, (![B_193]: (r1_tarski('#skF_4', k2_zfmisc_1(B_193, '#skF_1')) | ~r1_tarski('#skF_2', B_193))), inference(resolution, [status(thm)], [c_40, c_642])).
% 3.37/1.54  tff(c_10, plain, (![A_7, B_8]: (m1_subset_1(A_7, k1_zfmisc_1(B_8)) | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.37/1.54  tff(c_58, plain, (![C_37, A_38, B_39]: (v4_relat_1(C_37, A_38) | ~m1_subset_1(C_37, k1_zfmisc_1(k2_zfmisc_1(A_38, B_39))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.37/1.54  tff(c_66, plain, (![A_7, A_38, B_39]: (v4_relat_1(A_7, A_38) | ~r1_tarski(A_7, k2_zfmisc_1(A_38, B_39)))), inference(resolution, [status(thm)], [c_10, c_58])).
% 3.37/1.54  tff(c_743, plain, (![B_194]: (v4_relat_1('#skF_4', B_194) | ~r1_tarski('#skF_2', B_194))), inference(resolution, [status(thm)], [c_658, c_66])).
% 3.37/1.54  tff(c_12, plain, (![B_10, A_9]: (k7_relat_1(B_10, A_9)=B_10 | ~v4_relat_1(B_10, A_9) | ~v1_relat_1(B_10))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.37/1.54  tff(c_746, plain, (![B_194]: (k7_relat_1('#skF_4', B_194)='#skF_4' | ~v1_relat_1('#skF_4') | ~r1_tarski('#skF_2', B_194))), inference(resolution, [status(thm)], [c_743, c_12])).
% 3.37/1.54  tff(c_750, plain, (![B_195]: (k7_relat_1('#skF_4', B_195)='#skF_4' | ~r1_tarski('#skF_2', B_195))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_746])).
% 3.37/1.54  tff(c_759, plain, (k7_relat_1('#skF_4', '#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_28, c_750])).
% 3.37/1.54  tff(c_280, plain, (![A_95, B_96, C_97, D_98]: (k5_relset_1(A_95, B_96, C_97, D_98)=k7_relat_1(C_97, D_98) | ~m1_subset_1(C_97, k1_zfmisc_1(k2_zfmisc_1(A_95, B_96))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.37/1.54  tff(c_287, plain, (![D_98]: (k5_relset_1('#skF_2', '#skF_1', '#skF_4', D_98)=k7_relat_1('#skF_4', D_98))), inference(resolution, [status(thm)], [c_30, c_280])).
% 3.37/1.54  tff(c_26, plain, (~r2_relset_1('#skF_2', '#skF_1', k5_relset_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.37/1.54  tff(c_288, plain, (~r2_relset_1('#skF_2', '#skF_1', k7_relat_1('#skF_4', '#skF_3'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_287, c_26])).
% 3.37/1.54  tff(c_760, plain, (~r2_relset_1('#skF_2', '#skF_1', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_759, c_288])).
% 3.37/1.54  tff(c_763, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_245, c_760])).
% 3.37/1.54  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.37/1.54  
% 3.37/1.54  Inference rules
% 3.37/1.54  ----------------------
% 3.37/1.54  #Ref     : 0
% 3.37/1.54  #Sup     : 182
% 3.37/1.54  #Fact    : 0
% 3.37/1.54  #Define  : 0
% 3.37/1.54  #Split   : 1
% 3.37/1.54  #Chain   : 0
% 3.37/1.54  #Close   : 0
% 3.37/1.54  
% 3.37/1.54  Ordering : KBO
% 3.37/1.54  
% 3.37/1.54  Simplification rules
% 3.37/1.54  ----------------------
% 3.37/1.54  #Subsume      : 13
% 3.37/1.54  #Demod        : 48
% 3.37/1.54  #Tautology    : 48
% 3.37/1.54  #SimpNegUnit  : 0
% 3.37/1.54  #BackRed      : 2
% 3.37/1.54  
% 3.37/1.54  #Partial instantiations: 0
% 3.37/1.54  #Strategies tried      : 1
% 3.37/1.54  
% 3.37/1.54  Timing (in seconds)
% 3.37/1.54  ----------------------
% 3.37/1.55  Preprocessing        : 0.31
% 3.37/1.55  Parsing              : 0.16
% 3.37/1.55  CNF conversion       : 0.02
% 3.37/1.55  Main loop            : 0.47
% 3.37/1.55  Inferencing          : 0.17
% 3.37/1.55  Reduction            : 0.14
% 3.37/1.55  Demodulation         : 0.10
% 3.37/1.55  BG Simplification    : 0.02
% 3.37/1.55  Subsumption          : 0.11
% 3.37/1.55  Abstraction          : 0.02
% 3.37/1.55  MUC search           : 0.00
% 3.37/1.55  Cooper               : 0.00
% 3.37/1.55  Total                : 0.82
% 3.37/1.55  Index Insertion      : 0.00
% 3.37/1.55  Index Deletion       : 0.00
% 3.37/1.55  Index Matching       : 0.00
% 3.37/1.55  BG Taut test         : 0.00
%------------------------------------------------------------------------------
