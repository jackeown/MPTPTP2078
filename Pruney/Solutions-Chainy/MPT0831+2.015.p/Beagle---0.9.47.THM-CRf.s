%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:34 EST 2020

% Result     : Theorem 2.19s
% Output     : CNFRefutation 2.19s
% Verified   : 
% Statistics : Number of formulae       :   52 (  70 expanded)
%              Number of leaves         :   27 (  36 expanded)
%              Depth                    :    9
%              Number of atoms          :   66 ( 102 expanded)
%              Number of equality atoms :   12 (  12 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k5_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

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

tff(f_57,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_61,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k5_relset_1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_relset_1)).

tff(c_26,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_165,plain,(
    ! [A_50,B_51,D_52] :
      ( r2_relset_1(A_50,B_51,D_52,D_52)
      | ~ m1_subset_1(D_52,k1_zfmisc_1(k2_zfmisc_1(A_50,B_51))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_168,plain,(
    r2_relset_1('#skF_2','#skF_1','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_26,c_165])).

tff(c_27,plain,(
    ! [C_24,A_25,B_26] :
      ( v1_relat_1(C_24)
      | ~ m1_subset_1(C_24,k1_zfmisc_1(k2_zfmisc_1(A_25,B_26))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_31,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_26,c_27])).

tff(c_56,plain,(
    ! [C_39,A_40,B_41] :
      ( v4_relat_1(C_39,A_40)
      | ~ m1_subset_1(C_39,k1_zfmisc_1(k2_zfmisc_1(A_40,B_41))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_60,plain,(
    v4_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_56])).

tff(c_4,plain,(
    ! [B_5,A_4] :
      ( k7_relat_1(B_5,A_4) = B_5
      | ~ v4_relat_1(B_5,A_4)
      | ~ v1_relat_1(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_63,plain,
    ( k7_relat_1('#skF_4','#skF_2') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_4])).

tff(c_66,plain,(
    k7_relat_1('#skF_4','#skF_2') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_31,c_63])).

tff(c_6,plain,(
    ! [B_7,A_6] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_7,A_6)),A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_24,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_39,plain,(
    ! [A_34,C_35,B_36] :
      ( r1_tarski(A_34,C_35)
      | ~ r1_tarski(B_36,C_35)
      | ~ r1_tarski(A_34,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_46,plain,(
    ! [A_37] :
      ( r1_tarski(A_37,'#skF_3')
      | ~ r1_tarski(A_37,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_24,c_39])).

tff(c_51,plain,(
    ! [B_7] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_7,'#skF_2')),'#skF_3')
      | ~ v1_relat_1(B_7) ) ),
    inference(resolution,[status(thm)],[c_6,c_46])).

tff(c_70,plain,
    ( r1_tarski(k1_relat_1('#skF_4'),'#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_51])).

tff(c_77,plain,(
    r1_tarski(k1_relat_1('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_31,c_70])).

tff(c_8,plain,(
    ! [B_9,A_8] :
      ( k7_relat_1(B_9,A_8) = B_9
      | ~ r1_tarski(k1_relat_1(B_9),A_8)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_92,plain,
    ( k7_relat_1('#skF_4','#skF_3') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_77,c_8])).

tff(c_97,plain,(
    k7_relat_1('#skF_4','#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_31,c_92])).

tff(c_269,plain,(
    ! [A_66,B_67,C_68,D_69] :
      ( k5_relset_1(A_66,B_67,C_68,D_69) = k7_relat_1(C_68,D_69)
      | ~ m1_subset_1(C_68,k1_zfmisc_1(k2_zfmisc_1(A_66,B_67))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_272,plain,(
    ! [D_69] : k5_relset_1('#skF_2','#skF_1','#skF_4',D_69) = k7_relat_1('#skF_4',D_69) ),
    inference(resolution,[status(thm)],[c_26,c_269])).

tff(c_22,plain,(
    ~ r2_relset_1('#skF_2','#skF_1',k5_relset_1('#skF_2','#skF_1','#skF_4','#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_280,plain,(
    ~ r2_relset_1('#skF_2','#skF_1',k7_relat_1('#skF_4','#skF_3'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_272,c_22])).

tff(c_283,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_168,c_97,c_280])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 15:36:34 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.19/1.31  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.19/1.31  
% 2.19/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.19/1.31  %$ r2_relset_1 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k5_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.19/1.31  
% 2.19/1.31  %Foreground sorts:
% 2.19/1.31  
% 2.19/1.31  
% 2.19/1.31  %Background operators:
% 2.19/1.31  
% 2.19/1.31  
% 2.19/1.31  %Foreground operators:
% 2.19/1.31  tff(k5_relset_1, type, k5_relset_1: ($i * $i * $i * $i) > $i).
% 2.19/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.19/1.31  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 2.19/1.31  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.19/1.31  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.19/1.31  tff('#skF_2', type, '#skF_2': $i).
% 2.19/1.31  tff('#skF_3', type, '#skF_3': $i).
% 2.19/1.31  tff('#skF_1', type, '#skF_1': $i).
% 2.19/1.31  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.19/1.31  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.19/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.19/1.31  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.19/1.31  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.19/1.31  tff('#skF_4', type, '#skF_4': $i).
% 2.19/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.19/1.31  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.19/1.31  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.19/1.31  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.19/1.31  
% 2.19/1.33  tff(f_76, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A))) => (r1_tarski(B, C) => r2_relset_1(B, A, k5_relset_1(B, A, D, C), D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_relset_1)).
% 2.19/1.33  tff(f_69, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 2.19/1.33  tff(f_51, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.19/1.33  tff(f_57, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.19/1.33  tff(f_37, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 2.19/1.33  tff(f_41, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_relat_1)).
% 2.19/1.33  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 2.19/1.33  tff(f_47, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_relat_1)).
% 2.19/1.33  tff(f_61, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k5_relset_1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k5_relset_1)).
% 2.19/1.33  tff(c_26, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.19/1.33  tff(c_165, plain, (![A_50, B_51, D_52]: (r2_relset_1(A_50, B_51, D_52, D_52) | ~m1_subset_1(D_52, k1_zfmisc_1(k2_zfmisc_1(A_50, B_51))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.19/1.33  tff(c_168, plain, (r2_relset_1('#skF_2', '#skF_1', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_26, c_165])).
% 2.19/1.33  tff(c_27, plain, (![C_24, A_25, B_26]: (v1_relat_1(C_24) | ~m1_subset_1(C_24, k1_zfmisc_1(k2_zfmisc_1(A_25, B_26))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.19/1.33  tff(c_31, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_26, c_27])).
% 2.19/1.33  tff(c_56, plain, (![C_39, A_40, B_41]: (v4_relat_1(C_39, A_40) | ~m1_subset_1(C_39, k1_zfmisc_1(k2_zfmisc_1(A_40, B_41))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.19/1.33  tff(c_60, plain, (v4_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_26, c_56])).
% 2.19/1.33  tff(c_4, plain, (![B_5, A_4]: (k7_relat_1(B_5, A_4)=B_5 | ~v4_relat_1(B_5, A_4) | ~v1_relat_1(B_5))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.19/1.33  tff(c_63, plain, (k7_relat_1('#skF_4', '#skF_2')='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_60, c_4])).
% 2.19/1.33  tff(c_66, plain, (k7_relat_1('#skF_4', '#skF_2')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_31, c_63])).
% 2.19/1.33  tff(c_6, plain, (![B_7, A_6]: (r1_tarski(k1_relat_1(k7_relat_1(B_7, A_6)), A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.19/1.33  tff(c_24, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.19/1.33  tff(c_39, plain, (![A_34, C_35, B_36]: (r1_tarski(A_34, C_35) | ~r1_tarski(B_36, C_35) | ~r1_tarski(A_34, B_36))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.19/1.33  tff(c_46, plain, (![A_37]: (r1_tarski(A_37, '#skF_3') | ~r1_tarski(A_37, '#skF_2'))), inference(resolution, [status(thm)], [c_24, c_39])).
% 2.19/1.33  tff(c_51, plain, (![B_7]: (r1_tarski(k1_relat_1(k7_relat_1(B_7, '#skF_2')), '#skF_3') | ~v1_relat_1(B_7))), inference(resolution, [status(thm)], [c_6, c_46])).
% 2.19/1.33  tff(c_70, plain, (r1_tarski(k1_relat_1('#skF_4'), '#skF_3') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_66, c_51])).
% 2.19/1.33  tff(c_77, plain, (r1_tarski(k1_relat_1('#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_31, c_70])).
% 2.19/1.33  tff(c_8, plain, (![B_9, A_8]: (k7_relat_1(B_9, A_8)=B_9 | ~r1_tarski(k1_relat_1(B_9), A_8) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.19/1.33  tff(c_92, plain, (k7_relat_1('#skF_4', '#skF_3')='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_77, c_8])).
% 2.19/1.33  tff(c_97, plain, (k7_relat_1('#skF_4', '#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_31, c_92])).
% 2.19/1.33  tff(c_269, plain, (![A_66, B_67, C_68, D_69]: (k5_relset_1(A_66, B_67, C_68, D_69)=k7_relat_1(C_68, D_69) | ~m1_subset_1(C_68, k1_zfmisc_1(k2_zfmisc_1(A_66, B_67))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.19/1.33  tff(c_272, plain, (![D_69]: (k5_relset_1('#skF_2', '#skF_1', '#skF_4', D_69)=k7_relat_1('#skF_4', D_69))), inference(resolution, [status(thm)], [c_26, c_269])).
% 2.19/1.33  tff(c_22, plain, (~r2_relset_1('#skF_2', '#skF_1', k5_relset_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.19/1.33  tff(c_280, plain, (~r2_relset_1('#skF_2', '#skF_1', k7_relat_1('#skF_4', '#skF_3'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_272, c_22])).
% 2.19/1.33  tff(c_283, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_168, c_97, c_280])).
% 2.19/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.19/1.33  
% 2.19/1.33  Inference rules
% 2.19/1.33  ----------------------
% 2.19/1.33  #Ref     : 0
% 2.19/1.33  #Sup     : 54
% 2.19/1.33  #Fact    : 0
% 2.19/1.33  #Define  : 0
% 2.19/1.33  #Split   : 0
% 2.19/1.33  #Chain   : 0
% 2.19/1.33  #Close   : 0
% 2.19/1.33  
% 2.19/1.33  Ordering : KBO
% 2.19/1.33  
% 2.19/1.33  Simplification rules
% 2.19/1.33  ----------------------
% 2.19/1.33  #Subsume      : 8
% 2.19/1.33  #Demod        : 24
% 2.19/1.33  #Tautology    : 9
% 2.19/1.33  #SimpNegUnit  : 0
% 2.19/1.33  #BackRed      : 1
% 2.19/1.33  
% 2.19/1.33  #Partial instantiations: 0
% 2.19/1.33  #Strategies tried      : 1
% 2.19/1.33  
% 2.19/1.33  Timing (in seconds)
% 2.19/1.33  ----------------------
% 2.19/1.33  Preprocessing        : 0.30
% 2.19/1.33  Parsing              : 0.17
% 2.19/1.33  CNF conversion       : 0.02
% 2.19/1.33  Main loop            : 0.20
% 2.19/1.33  Inferencing          : 0.08
% 2.19/1.33  Reduction            : 0.05
% 2.19/1.33  Demodulation         : 0.04
% 2.19/1.33  BG Simplification    : 0.01
% 2.19/1.33  Subsumption          : 0.04
% 2.19/1.33  Abstraction          : 0.01
% 2.19/1.33  MUC search           : 0.00
% 2.19/1.33  Cooper               : 0.00
% 2.19/1.33  Total                : 0.53
% 2.19/1.33  Index Insertion      : 0.00
% 2.19/1.33  Index Deletion       : 0.00
% 2.19/1.33  Index Matching       : 0.00
% 2.19/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
