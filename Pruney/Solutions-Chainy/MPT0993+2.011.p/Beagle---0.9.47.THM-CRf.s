%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:44 EST 2020

% Result     : Theorem 1.81s
% Output     : CNFRefutation 2.08s
% Verified   : 
% Statistics : Number of formulae       :   52 (  83 expanded)
%              Number of leaves         :   28 (  42 expanded)
%              Depth                    :    8
%              Number of atoms          :   68 ( 153 expanded)
%              Number of equality atoms :   15 (  20 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_partfun1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

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

tff(k2_partfun1,type,(
    k2_partfun1: ( $i * $i * $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_78,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( r1_tarski(A,C)
         => r2_relset_1(A,B,k2_partfun1(A,B,D,C),D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_funct_2)).

tff(f_61,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t102_relat_1)).

tff(f_67,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(c_26,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_64,plain,(
    ! [A_39,B_40,D_41] :
      ( r2_relset_1(A_39,B_40,D_41,D_41)
      | ~ m1_subset_1(D_41,k1_zfmisc_1(k2_zfmisc_1(A_39,B_40))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_67,plain,(
    r2_relset_1('#skF_1','#skF_2','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_26,c_64])).

tff(c_24,plain,(
    r1_tarski('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_31,plain,(
    ! [C_22,A_23,B_24] :
      ( v1_relat_1(C_22)
      | ~ m1_subset_1(C_22,k1_zfmisc_1(k2_zfmisc_1(A_23,B_24))) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_35,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_26,c_31])).

tff(c_41,plain,(
    ! [C_28,A_29,B_30] :
      ( v4_relat_1(C_28,A_29)
      | ~ m1_subset_1(C_28,k1_zfmisc_1(k2_zfmisc_1(A_29,B_30))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_45,plain,(
    v4_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_41])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( r1_tarski(k1_relat_1(B_2),A_1)
      | ~ v4_relat_1(B_2,A_1)
      | ~ v1_relat_1(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_52,plain,(
    ! [B_35,A_36] :
      ( k7_relat_1(B_35,A_36) = B_35
      | ~ r1_tarski(k1_relat_1(B_35),A_36)
      | ~ v1_relat_1(B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_57,plain,(
    ! [B_37,A_38] :
      ( k7_relat_1(B_37,A_38) = B_37
      | ~ v4_relat_1(B_37,A_38)
      | ~ v1_relat_1(B_37) ) ),
    inference(resolution,[status(thm)],[c_4,c_52])).

tff(c_60,plain,
    ( k7_relat_1('#skF_4','#skF_1') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_45,c_57])).

tff(c_63,plain,(
    k7_relat_1('#skF_4','#skF_1') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_35,c_60])).

tff(c_72,plain,(
    ! [C_42,A_43,B_44] :
      ( k7_relat_1(k7_relat_1(C_42,A_43),B_44) = k7_relat_1(C_42,A_43)
      | ~ r1_tarski(A_43,B_44)
      | ~ v1_relat_1(C_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_87,plain,(
    ! [B_44] :
      ( k7_relat_1('#skF_4',B_44) = k7_relat_1('#skF_4','#skF_1')
      | ~ r1_tarski('#skF_1',B_44)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_63,c_72])).

tff(c_92,plain,(
    ! [B_45] :
      ( k7_relat_1('#skF_4',B_45) = '#skF_4'
      | ~ r1_tarski('#skF_1',B_45) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_35,c_63,c_87])).

tff(c_96,plain,(
    k7_relat_1('#skF_4','#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_24,c_92])).

tff(c_30,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_107,plain,(
    ! [A_47,B_48,C_49,D_50] :
      ( k2_partfun1(A_47,B_48,C_49,D_50) = k7_relat_1(C_49,D_50)
      | ~ m1_subset_1(C_49,k1_zfmisc_1(k2_zfmisc_1(A_47,B_48)))
      | ~ v1_funct_1(C_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_109,plain,(
    ! [D_50] :
      ( k2_partfun1('#skF_1','#skF_2','#skF_4',D_50) = k7_relat_1('#skF_4',D_50)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_26,c_107])).

tff(c_112,plain,(
    ! [D_50] : k2_partfun1('#skF_1','#skF_2','#skF_4',D_50) = k7_relat_1('#skF_4',D_50) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_109])).

tff(c_22,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_113,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k7_relat_1('#skF_4','#skF_3'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_22])).

tff(c_116,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_96,c_113])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:56:20 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.81/1.16  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.81/1.17  
% 1.81/1.17  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.81/1.17  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_partfun1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.81/1.17  
% 1.81/1.17  %Foreground sorts:
% 1.81/1.17  
% 1.81/1.17  
% 1.81/1.17  %Background operators:
% 1.81/1.17  
% 1.81/1.17  
% 1.81/1.17  %Foreground operators:
% 1.81/1.17  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.81/1.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.81/1.17  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 1.81/1.17  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.81/1.17  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.81/1.17  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 1.81/1.17  tff('#skF_2', type, '#skF_2': $i).
% 1.81/1.17  tff('#skF_3', type, '#skF_3': $i).
% 1.81/1.17  tff('#skF_1', type, '#skF_1': $i).
% 1.81/1.17  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 1.81/1.17  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.81/1.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.81/1.17  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.81/1.17  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.81/1.17  tff('#skF_4', type, '#skF_4': $i).
% 1.81/1.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.81/1.17  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 1.81/1.17  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 1.81/1.17  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.81/1.17  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.81/1.17  
% 2.08/1.18  tff(f_78, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(A, C) => r2_relset_1(A, B, k2_partfun1(A, B, D, C), D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_funct_2)).
% 2.08/1.18  tff(f_61, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 2.08/1.18  tff(f_47, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.08/1.18  tff(f_53, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.08/1.18  tff(f_31, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 2.08/1.18  tff(f_43, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_relat_1)).
% 2.08/1.18  tff(f_37, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t102_relat_1)).
% 2.08/1.18  tff(f_67, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 2.08/1.18  tff(c_26, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.08/1.18  tff(c_64, plain, (![A_39, B_40, D_41]: (r2_relset_1(A_39, B_40, D_41, D_41) | ~m1_subset_1(D_41, k1_zfmisc_1(k2_zfmisc_1(A_39, B_40))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.08/1.18  tff(c_67, plain, (r2_relset_1('#skF_1', '#skF_2', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_26, c_64])).
% 2.08/1.18  tff(c_24, plain, (r1_tarski('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.08/1.18  tff(c_31, plain, (![C_22, A_23, B_24]: (v1_relat_1(C_22) | ~m1_subset_1(C_22, k1_zfmisc_1(k2_zfmisc_1(A_23, B_24))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.08/1.18  tff(c_35, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_26, c_31])).
% 2.08/1.18  tff(c_41, plain, (![C_28, A_29, B_30]: (v4_relat_1(C_28, A_29) | ~m1_subset_1(C_28, k1_zfmisc_1(k2_zfmisc_1(A_29, B_30))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.08/1.18  tff(c_45, plain, (v4_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_26, c_41])).
% 2.08/1.18  tff(c_4, plain, (![B_2, A_1]: (r1_tarski(k1_relat_1(B_2), A_1) | ~v4_relat_1(B_2, A_1) | ~v1_relat_1(B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.08/1.18  tff(c_52, plain, (![B_35, A_36]: (k7_relat_1(B_35, A_36)=B_35 | ~r1_tarski(k1_relat_1(B_35), A_36) | ~v1_relat_1(B_35))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.08/1.18  tff(c_57, plain, (![B_37, A_38]: (k7_relat_1(B_37, A_38)=B_37 | ~v4_relat_1(B_37, A_38) | ~v1_relat_1(B_37))), inference(resolution, [status(thm)], [c_4, c_52])).
% 2.08/1.18  tff(c_60, plain, (k7_relat_1('#skF_4', '#skF_1')='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_45, c_57])).
% 2.08/1.18  tff(c_63, plain, (k7_relat_1('#skF_4', '#skF_1')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_35, c_60])).
% 2.08/1.18  tff(c_72, plain, (![C_42, A_43, B_44]: (k7_relat_1(k7_relat_1(C_42, A_43), B_44)=k7_relat_1(C_42, A_43) | ~r1_tarski(A_43, B_44) | ~v1_relat_1(C_42))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.08/1.18  tff(c_87, plain, (![B_44]: (k7_relat_1('#skF_4', B_44)=k7_relat_1('#skF_4', '#skF_1') | ~r1_tarski('#skF_1', B_44) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_63, c_72])).
% 2.08/1.18  tff(c_92, plain, (![B_45]: (k7_relat_1('#skF_4', B_45)='#skF_4' | ~r1_tarski('#skF_1', B_45))), inference(demodulation, [status(thm), theory('equality')], [c_35, c_63, c_87])).
% 2.08/1.18  tff(c_96, plain, (k7_relat_1('#skF_4', '#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_24, c_92])).
% 2.08/1.18  tff(c_30, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.08/1.18  tff(c_107, plain, (![A_47, B_48, C_49, D_50]: (k2_partfun1(A_47, B_48, C_49, D_50)=k7_relat_1(C_49, D_50) | ~m1_subset_1(C_49, k1_zfmisc_1(k2_zfmisc_1(A_47, B_48))) | ~v1_funct_1(C_49))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.08/1.18  tff(c_109, plain, (![D_50]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_50)=k7_relat_1('#skF_4', D_50) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_26, c_107])).
% 2.08/1.18  tff(c_112, plain, (![D_50]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_50)=k7_relat_1('#skF_4', D_50))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_109])).
% 2.08/1.18  tff(c_22, plain, (~r2_relset_1('#skF_1', '#skF_2', k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.08/1.18  tff(c_113, plain, (~r2_relset_1('#skF_1', '#skF_2', k7_relat_1('#skF_4', '#skF_3'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_112, c_22])).
% 2.08/1.18  tff(c_116, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_67, c_96, c_113])).
% 2.08/1.18  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.08/1.18  
% 2.08/1.18  Inference rules
% 2.08/1.18  ----------------------
% 2.08/1.18  #Ref     : 0
% 2.08/1.18  #Sup     : 19
% 2.08/1.18  #Fact    : 0
% 2.08/1.18  #Define  : 0
% 2.08/1.18  #Split   : 0
% 2.08/1.18  #Chain   : 0
% 2.08/1.18  #Close   : 0
% 2.08/1.18  
% 2.08/1.18  Ordering : KBO
% 2.08/1.18  
% 2.08/1.18  Simplification rules
% 2.08/1.18  ----------------------
% 2.08/1.18  #Subsume      : 0
% 2.08/1.18  #Demod        : 9
% 2.08/1.18  #Tautology    : 7
% 2.08/1.18  #SimpNegUnit  : 0
% 2.08/1.18  #BackRed      : 1
% 2.08/1.18  
% 2.08/1.18  #Partial instantiations: 0
% 2.08/1.18  #Strategies tried      : 1
% 2.08/1.18  
% 2.08/1.18  Timing (in seconds)
% 2.08/1.18  ----------------------
% 2.08/1.19  Preprocessing        : 0.29
% 2.08/1.19  Parsing              : 0.16
% 2.08/1.19  CNF conversion       : 0.02
% 2.08/1.19  Main loop            : 0.12
% 2.08/1.19  Inferencing          : 0.05
% 2.08/1.19  Reduction            : 0.04
% 2.08/1.19  Demodulation         : 0.03
% 2.08/1.19  BG Simplification    : 0.01
% 2.08/1.19  Subsumption          : 0.01
% 2.08/1.19  Abstraction          : 0.01
% 2.08/1.19  MUC search           : 0.00
% 2.08/1.19  Cooper               : 0.00
% 2.08/1.19  Total                : 0.44
% 2.08/1.19  Index Insertion      : 0.00
% 2.08/1.19  Index Deletion       : 0.00
% 2.08/1.19  Index Matching       : 0.00
% 2.08/1.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
