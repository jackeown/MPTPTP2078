%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:44 EST 2020

% Result     : Theorem 2.13s
% Output     : CNFRefutation 2.20s
% Verified   : 
% Statistics : Number of formulae       :   56 (  65 expanded)
%              Number of leaves         :   30 (  36 expanded)
%              Depth                    :    9
%              Number of atoms          :   75 ( 108 expanded)
%              Number of equality atoms :   13 (  13 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_partfun1 > k7_relat_1 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_80,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( r1_tarski(A,C)
         => r2_relset_1(A,B,k2_partfun1(A,B,D,C),D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_funct_2)).

tff(f_63,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_69,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(c_28,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_100,plain,(
    ! [A_49,B_50,D_51] :
      ( r2_relset_1(A_49,B_50,D_51,D_51)
      | ~ m1_subset_1(D_51,k1_zfmisc_1(k2_zfmisc_1(A_49,B_50))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_103,plain,(
    r2_relset_1('#skF_1','#skF_2','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_100])).

tff(c_38,plain,(
    ! [C_26,A_27,B_28] :
      ( v1_relat_1(C_26)
      | ~ m1_subset_1(C_26,k1_zfmisc_1(k2_zfmisc_1(A_27,B_28))) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_42,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_38])).

tff(c_52,plain,(
    ! [C_33,A_34,B_35] :
      ( v4_relat_1(C_33,A_34)
      | ~ m1_subset_1(C_33,k1_zfmisc_1(k2_zfmisc_1(A_34,B_35))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_56,plain,(
    v4_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_52])).

tff(c_26,plain,(
    r1_tarski('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_57,plain,(
    ! [B_36,A_37] :
      ( r1_tarski(k1_relat_1(B_36),A_37)
      | ~ v4_relat_1(B_36,A_37)
      | ~ v1_relat_1(B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_4,plain,(
    ! [A_4,B_5] :
      ( k2_xboole_0(A_4,B_5) = B_5
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_88,plain,(
    ! [B_47,A_48] :
      ( k2_xboole_0(k1_relat_1(B_47),A_48) = A_48
      | ~ v4_relat_1(B_47,A_48)
      | ~ v1_relat_1(B_47) ) ),
    inference(resolution,[status(thm)],[c_57,c_4])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,C_3)
      | ~ r1_tarski(k2_xboole_0(A_1,B_2),C_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_104,plain,(
    ! [B_52,C_53,A_54] :
      ( r1_tarski(k1_relat_1(B_52),C_53)
      | ~ r1_tarski(A_54,C_53)
      | ~ v4_relat_1(B_52,A_54)
      | ~ v1_relat_1(B_52) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_2])).

tff(c_111,plain,(
    ! [B_55] :
      ( r1_tarski(k1_relat_1(B_55),'#skF_3')
      | ~ v4_relat_1(B_55,'#skF_1')
      | ~ v1_relat_1(B_55) ) ),
    inference(resolution,[status(thm)],[c_26,c_104])).

tff(c_10,plain,(
    ! [B_9,A_8] :
      ( k7_relat_1(B_9,A_8) = B_9
      | ~ r1_tarski(k1_relat_1(B_9),A_8)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_148,plain,(
    ! [B_62] :
      ( k7_relat_1(B_62,'#skF_3') = B_62
      | ~ v4_relat_1(B_62,'#skF_1')
      | ~ v1_relat_1(B_62) ) ),
    inference(resolution,[status(thm)],[c_111,c_10])).

tff(c_151,plain,
    ( k7_relat_1('#skF_4','#skF_3') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_148])).

tff(c_154,plain,(
    k7_relat_1('#skF_4','#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_151])).

tff(c_32,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_127,plain,(
    ! [A_56,B_57,C_58,D_59] :
      ( k2_partfun1(A_56,B_57,C_58,D_59) = k7_relat_1(C_58,D_59)
      | ~ m1_subset_1(C_58,k1_zfmisc_1(k2_zfmisc_1(A_56,B_57)))
      | ~ v1_funct_1(C_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_129,plain,(
    ! [D_59] :
      ( k2_partfun1('#skF_1','#skF_2','#skF_4',D_59) = k7_relat_1('#skF_4',D_59)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_28,c_127])).

tff(c_132,plain,(
    ! [D_59] : k2_partfun1('#skF_1','#skF_2','#skF_4',D_59) = k7_relat_1('#skF_4',D_59) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_129])).

tff(c_24,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_133,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k7_relat_1('#skF_4','#skF_3'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_24])).

tff(c_155,plain,(
    ~ r2_relset_1('#skF_1','#skF_2','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_133])).

tff(c_158,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_155])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n019.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 13:56:07 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.13/1.23  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.20/1.23  
% 2.20/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.20/1.24  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_partfun1 > k7_relat_1 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.20/1.24  
% 2.20/1.24  %Foreground sorts:
% 2.20/1.24  
% 2.20/1.24  
% 2.20/1.24  %Background operators:
% 2.20/1.24  
% 2.20/1.24  
% 2.20/1.24  %Foreground operators:
% 2.20/1.24  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.20/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.20/1.24  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 2.20/1.24  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.20/1.24  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.20/1.24  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.20/1.24  tff('#skF_2', type, '#skF_2': $i).
% 2.20/1.24  tff('#skF_3', type, '#skF_3': $i).
% 2.20/1.24  tff('#skF_1', type, '#skF_1': $i).
% 2.20/1.24  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.20/1.24  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.20/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.20/1.24  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.20/1.24  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.20/1.24  tff('#skF_4', type, '#skF_4': $i).
% 2.20/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.20/1.24  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 2.20/1.24  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.20/1.24  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.20/1.24  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.20/1.24  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.20/1.24  
% 2.20/1.25  tff(f_80, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(A, C) => r2_relset_1(A, B, k2_partfun1(A, B, D, C), D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_funct_2)).
% 2.20/1.25  tff(f_63, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 2.20/1.25  tff(f_49, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.20/1.25  tff(f_55, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.20/1.25  tff(f_39, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 2.20/1.25  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.20/1.25  tff(f_29, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_xboole_1)).
% 2.20/1.25  tff(f_45, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t97_relat_1)).
% 2.20/1.25  tff(f_69, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 2.20/1.25  tff(c_28, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.20/1.25  tff(c_100, plain, (![A_49, B_50, D_51]: (r2_relset_1(A_49, B_50, D_51, D_51) | ~m1_subset_1(D_51, k1_zfmisc_1(k2_zfmisc_1(A_49, B_50))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.20/1.25  tff(c_103, plain, (r2_relset_1('#skF_1', '#skF_2', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_28, c_100])).
% 2.20/1.25  tff(c_38, plain, (![C_26, A_27, B_28]: (v1_relat_1(C_26) | ~m1_subset_1(C_26, k1_zfmisc_1(k2_zfmisc_1(A_27, B_28))))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.20/1.25  tff(c_42, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_28, c_38])).
% 2.20/1.25  tff(c_52, plain, (![C_33, A_34, B_35]: (v4_relat_1(C_33, A_34) | ~m1_subset_1(C_33, k1_zfmisc_1(k2_zfmisc_1(A_34, B_35))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.20/1.25  tff(c_56, plain, (v4_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_28, c_52])).
% 2.20/1.25  tff(c_26, plain, (r1_tarski('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.20/1.25  tff(c_57, plain, (![B_36, A_37]: (r1_tarski(k1_relat_1(B_36), A_37) | ~v4_relat_1(B_36, A_37) | ~v1_relat_1(B_36))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.20/1.25  tff(c_4, plain, (![A_4, B_5]: (k2_xboole_0(A_4, B_5)=B_5 | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.20/1.25  tff(c_88, plain, (![B_47, A_48]: (k2_xboole_0(k1_relat_1(B_47), A_48)=A_48 | ~v4_relat_1(B_47, A_48) | ~v1_relat_1(B_47))), inference(resolution, [status(thm)], [c_57, c_4])).
% 2.20/1.25  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, C_3) | ~r1_tarski(k2_xboole_0(A_1, B_2), C_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.20/1.25  tff(c_104, plain, (![B_52, C_53, A_54]: (r1_tarski(k1_relat_1(B_52), C_53) | ~r1_tarski(A_54, C_53) | ~v4_relat_1(B_52, A_54) | ~v1_relat_1(B_52))), inference(superposition, [status(thm), theory('equality')], [c_88, c_2])).
% 2.20/1.25  tff(c_111, plain, (![B_55]: (r1_tarski(k1_relat_1(B_55), '#skF_3') | ~v4_relat_1(B_55, '#skF_1') | ~v1_relat_1(B_55))), inference(resolution, [status(thm)], [c_26, c_104])).
% 2.20/1.25  tff(c_10, plain, (![B_9, A_8]: (k7_relat_1(B_9, A_8)=B_9 | ~r1_tarski(k1_relat_1(B_9), A_8) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.20/1.25  tff(c_148, plain, (![B_62]: (k7_relat_1(B_62, '#skF_3')=B_62 | ~v4_relat_1(B_62, '#skF_1') | ~v1_relat_1(B_62))), inference(resolution, [status(thm)], [c_111, c_10])).
% 2.20/1.25  tff(c_151, plain, (k7_relat_1('#skF_4', '#skF_3')='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_56, c_148])).
% 2.20/1.25  tff(c_154, plain, (k7_relat_1('#skF_4', '#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_151])).
% 2.20/1.25  tff(c_32, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.20/1.25  tff(c_127, plain, (![A_56, B_57, C_58, D_59]: (k2_partfun1(A_56, B_57, C_58, D_59)=k7_relat_1(C_58, D_59) | ~m1_subset_1(C_58, k1_zfmisc_1(k2_zfmisc_1(A_56, B_57))) | ~v1_funct_1(C_58))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.20/1.25  tff(c_129, plain, (![D_59]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_59)=k7_relat_1('#skF_4', D_59) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_28, c_127])).
% 2.20/1.25  tff(c_132, plain, (![D_59]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_59)=k7_relat_1('#skF_4', D_59))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_129])).
% 2.20/1.25  tff(c_24, plain, (~r2_relset_1('#skF_1', '#skF_2', k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.20/1.25  tff(c_133, plain, (~r2_relset_1('#skF_1', '#skF_2', k7_relat_1('#skF_4', '#skF_3'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_132, c_24])).
% 2.20/1.25  tff(c_155, plain, (~r2_relset_1('#skF_1', '#skF_2', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_154, c_133])).
% 2.20/1.25  tff(c_158, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_103, c_155])).
% 2.20/1.25  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.20/1.25  
% 2.20/1.25  Inference rules
% 2.20/1.25  ----------------------
% 2.20/1.25  #Ref     : 0
% 2.20/1.25  #Sup     : 28
% 2.20/1.25  #Fact    : 0
% 2.20/1.25  #Define  : 0
% 2.20/1.25  #Split   : 0
% 2.20/1.25  #Chain   : 0
% 2.20/1.25  #Close   : 0
% 2.20/1.25  
% 2.20/1.25  Ordering : KBO
% 2.20/1.25  
% 2.20/1.25  Simplification rules
% 2.20/1.25  ----------------------
% 2.20/1.25  #Subsume      : 0
% 2.20/1.25  #Demod        : 6
% 2.20/1.25  #Tautology    : 9
% 2.20/1.25  #SimpNegUnit  : 0
% 2.20/1.25  #BackRed      : 2
% 2.20/1.25  
% 2.20/1.25  #Partial instantiations: 0
% 2.20/1.25  #Strategies tried      : 1
% 2.20/1.25  
% 2.20/1.25  Timing (in seconds)
% 2.20/1.25  ----------------------
% 2.20/1.25  Preprocessing        : 0.31
% 2.20/1.25  Parsing              : 0.16
% 2.20/1.25  CNF conversion       : 0.02
% 2.20/1.25  Main loop            : 0.16
% 2.20/1.25  Inferencing          : 0.07
% 2.20/1.25  Reduction            : 0.05
% 2.20/1.25  Demodulation         : 0.04
% 2.20/1.25  BG Simplification    : 0.01
% 2.20/1.25  Subsumption          : 0.03
% 2.20/1.25  Abstraction          : 0.01
% 2.20/1.25  MUC search           : 0.00
% 2.20/1.25  Cooper               : 0.00
% 2.20/1.25  Total                : 0.51
% 2.20/1.25  Index Insertion      : 0.00
% 2.20/1.25  Index Deletion       : 0.00
% 2.20/1.25  Index Matching       : 0.00
% 2.20/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
