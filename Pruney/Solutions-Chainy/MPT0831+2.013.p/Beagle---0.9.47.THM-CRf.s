%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:34 EST 2020

% Result     : Theorem 1.73s
% Output     : CNFRefutation 1.73s
% Verified   : 
% Statistics : Number of formulae       :   44 (  71 expanded)
%              Number of leaves         :   24 (  36 expanded)
%              Depth                    :    8
%              Number of atoms          :   52 ( 107 expanded)
%              Number of equality atoms :   13 (  17 expanded)
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

tff(f_66,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A)))
       => ( r1_tarski(B,C)
         => r2_relset_1(B,A,k5_relset_1(B,A,D,C),D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_relset_1)).

tff(f_59,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t102_relat_1)).

tff(f_51,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k5_relset_1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k5_relset_1)).

tff(c_22,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_49,plain,(
    ! [A_31,B_32,D_33] :
      ( r2_relset_1(A_31,B_32,D_33,D_33)
      | ~ m1_subset_1(D_33,k1_zfmisc_1(k2_zfmisc_1(A_31,B_32))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_52,plain,(
    r2_relset_1('#skF_2','#skF_1','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_22,c_49])).

tff(c_20,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_23,plain,(
    ! [C_20,A_21,B_22] :
      ( v1_relat_1(C_20)
      | ~ m1_subset_1(C_20,k1_zfmisc_1(k2_zfmisc_1(A_21,B_22))) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_27,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_22,c_23])).

tff(c_34,plain,(
    ! [C_28,A_29,B_30] :
      ( v4_relat_1(C_28,A_29)
      | ~ m1_subset_1(C_28,k1_zfmisc_1(k2_zfmisc_1(A_29,B_30))) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_38,plain,(
    v4_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_22,c_34])).

tff(c_4,plain,(
    ! [B_5,A_4] :
      ( k7_relat_1(B_5,A_4) = B_5
      | ~ v4_relat_1(B_5,A_4)
      | ~ v1_relat_1(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_41,plain,
    ( k7_relat_1('#skF_4','#skF_2') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_4])).

tff(c_44,plain,(
    k7_relat_1('#skF_4','#skF_2') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_27,c_41])).

tff(c_53,plain,(
    ! [C_34,A_35,B_36] :
      ( k7_relat_1(k7_relat_1(C_34,A_35),B_36) = k7_relat_1(C_34,A_35)
      | ~ r1_tarski(A_35,B_36)
      | ~ v1_relat_1(C_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_68,plain,(
    ! [B_36] :
      ( k7_relat_1('#skF_4',B_36) = k7_relat_1('#skF_4','#skF_2')
      | ~ r1_tarski('#skF_2',B_36)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_53])).

tff(c_73,plain,(
    ! [B_37] :
      ( k7_relat_1('#skF_4',B_37) = '#skF_4'
      | ~ r1_tarski('#skF_2',B_37) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_27,c_44,c_68])).

tff(c_77,plain,(
    k7_relat_1('#skF_4','#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_20,c_73])).

tff(c_78,plain,(
    ! [A_38,B_39,C_40,D_41] :
      ( k5_relset_1(A_38,B_39,C_40,D_41) = k7_relat_1(C_40,D_41)
      | ~ m1_subset_1(C_40,k1_zfmisc_1(k2_zfmisc_1(A_38,B_39))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_81,plain,(
    ! [D_41] : k5_relset_1('#skF_2','#skF_1','#skF_4',D_41) = k7_relat_1('#skF_4',D_41) ),
    inference(resolution,[status(thm)],[c_22,c_78])).

tff(c_18,plain,(
    ~ r2_relset_1('#skF_2','#skF_1',k5_relset_1('#skF_2','#skF_1','#skF_4','#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_92,plain,(
    ~ r2_relset_1('#skF_2','#skF_1',k7_relat_1('#skF_4','#skF_3'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_18])).

tff(c_95,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_77,c_92])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n017.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 19:11:16 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.73/1.16  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.73/1.16  
% 1.73/1.16  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.73/1.16  %$ r2_relset_1 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k5_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.73/1.16  
% 1.73/1.16  %Foreground sorts:
% 1.73/1.16  
% 1.73/1.16  
% 1.73/1.16  %Background operators:
% 1.73/1.16  
% 1.73/1.16  
% 1.73/1.16  %Foreground operators:
% 1.73/1.16  tff(k5_relset_1, type, k5_relset_1: ($i * $i * $i * $i) > $i).
% 1.73/1.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.73/1.16  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 1.73/1.16  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.73/1.16  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.73/1.16  tff('#skF_2', type, '#skF_2': $i).
% 1.73/1.16  tff('#skF_3', type, '#skF_3': $i).
% 1.73/1.16  tff('#skF_1', type, '#skF_1': $i).
% 1.73/1.16  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 1.73/1.16  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.73/1.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.73/1.16  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.73/1.16  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.73/1.16  tff('#skF_4', type, '#skF_4': $i).
% 1.73/1.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.73/1.16  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 1.73/1.16  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.73/1.16  
% 1.73/1.18  tff(f_66, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A))) => (r1_tarski(B, C) => r2_relset_1(B, A, k5_relset_1(B, A, D, C), D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_relset_1)).
% 1.73/1.18  tff(f_59, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 1.73/1.18  tff(f_41, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 1.73/1.18  tff(f_47, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 1.73/1.18  tff(f_37, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 1.73/1.18  tff(f_31, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t102_relat_1)).
% 1.73/1.18  tff(f_51, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k5_relset_1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k5_relset_1)).
% 1.73/1.18  tff(c_22, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.73/1.18  tff(c_49, plain, (![A_31, B_32, D_33]: (r2_relset_1(A_31, B_32, D_33, D_33) | ~m1_subset_1(D_33, k1_zfmisc_1(k2_zfmisc_1(A_31, B_32))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.73/1.18  tff(c_52, plain, (r2_relset_1('#skF_2', '#skF_1', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_22, c_49])).
% 1.73/1.18  tff(c_20, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.73/1.18  tff(c_23, plain, (![C_20, A_21, B_22]: (v1_relat_1(C_20) | ~m1_subset_1(C_20, k1_zfmisc_1(k2_zfmisc_1(A_21, B_22))))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.73/1.18  tff(c_27, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_22, c_23])).
% 1.73/1.18  tff(c_34, plain, (![C_28, A_29, B_30]: (v4_relat_1(C_28, A_29) | ~m1_subset_1(C_28, k1_zfmisc_1(k2_zfmisc_1(A_29, B_30))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.73/1.18  tff(c_38, plain, (v4_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_22, c_34])).
% 1.73/1.18  tff(c_4, plain, (![B_5, A_4]: (k7_relat_1(B_5, A_4)=B_5 | ~v4_relat_1(B_5, A_4) | ~v1_relat_1(B_5))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.73/1.18  tff(c_41, plain, (k7_relat_1('#skF_4', '#skF_2')='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_38, c_4])).
% 1.73/1.18  tff(c_44, plain, (k7_relat_1('#skF_4', '#skF_2')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_27, c_41])).
% 1.73/1.18  tff(c_53, plain, (![C_34, A_35, B_36]: (k7_relat_1(k7_relat_1(C_34, A_35), B_36)=k7_relat_1(C_34, A_35) | ~r1_tarski(A_35, B_36) | ~v1_relat_1(C_34))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.73/1.18  tff(c_68, plain, (![B_36]: (k7_relat_1('#skF_4', B_36)=k7_relat_1('#skF_4', '#skF_2') | ~r1_tarski('#skF_2', B_36) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_44, c_53])).
% 1.73/1.18  tff(c_73, plain, (![B_37]: (k7_relat_1('#skF_4', B_37)='#skF_4' | ~r1_tarski('#skF_2', B_37))), inference(demodulation, [status(thm), theory('equality')], [c_27, c_44, c_68])).
% 1.73/1.18  tff(c_77, plain, (k7_relat_1('#skF_4', '#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_20, c_73])).
% 1.73/1.18  tff(c_78, plain, (![A_38, B_39, C_40, D_41]: (k5_relset_1(A_38, B_39, C_40, D_41)=k7_relat_1(C_40, D_41) | ~m1_subset_1(C_40, k1_zfmisc_1(k2_zfmisc_1(A_38, B_39))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.73/1.18  tff(c_81, plain, (![D_41]: (k5_relset_1('#skF_2', '#skF_1', '#skF_4', D_41)=k7_relat_1('#skF_4', D_41))), inference(resolution, [status(thm)], [c_22, c_78])).
% 1.73/1.18  tff(c_18, plain, (~r2_relset_1('#skF_2', '#skF_1', k5_relset_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.73/1.18  tff(c_92, plain, (~r2_relset_1('#skF_2', '#skF_1', k7_relat_1('#skF_4', '#skF_3'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_81, c_18])).
% 1.73/1.18  tff(c_95, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_77, c_92])).
% 1.73/1.18  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.73/1.18  
% 1.73/1.18  Inference rules
% 1.73/1.18  ----------------------
% 1.73/1.18  #Ref     : 0
% 1.73/1.18  #Sup     : 17
% 1.73/1.18  #Fact    : 0
% 1.73/1.18  #Define  : 0
% 1.73/1.18  #Split   : 0
% 1.73/1.18  #Chain   : 0
% 1.73/1.18  #Close   : 0
% 1.73/1.18  
% 1.73/1.18  Ordering : KBO
% 1.73/1.18  
% 1.73/1.18  Simplification rules
% 1.73/1.18  ----------------------
% 1.73/1.18  #Subsume      : 0
% 1.73/1.18  #Demod        : 8
% 1.73/1.18  #Tautology    : 6
% 1.73/1.18  #SimpNegUnit  : 0
% 1.73/1.18  #BackRed      : 1
% 1.73/1.18  
% 1.73/1.18  #Partial instantiations: 0
% 1.73/1.18  #Strategies tried      : 1
% 1.73/1.18  
% 1.73/1.18  Timing (in seconds)
% 1.73/1.18  ----------------------
% 1.97/1.18  Preprocessing        : 0.30
% 1.97/1.18  Parsing              : 0.17
% 1.97/1.18  CNF conversion       : 0.02
% 1.97/1.18  Main loop            : 0.11
% 1.97/1.18  Inferencing          : 0.04
% 1.97/1.18  Reduction            : 0.03
% 1.97/1.18  Demodulation         : 0.03
% 1.97/1.18  BG Simplification    : 0.01
% 1.97/1.18  Subsumption          : 0.01
% 1.97/1.18  Abstraction          : 0.01
% 1.97/1.18  MUC search           : 0.00
% 1.97/1.18  Cooper               : 0.00
% 1.97/1.18  Total                : 0.44
% 1.97/1.18  Index Insertion      : 0.00
% 1.97/1.18  Index Deletion       : 0.00
% 1.97/1.18  Index Matching       : 0.00
% 1.97/1.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
