%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:44 EST 2020

% Result     : Theorem 1.88s
% Output     : CNFRefutation 2.13s
% Verified   : 
% Statistics : Number of formulae       :   58 (  68 expanded)
%              Number of leaves         :   30 (  37 expanded)
%              Depth                    :   10
%              Number of atoms          :   81 ( 117 expanded)
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
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_69,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(c_28,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_83,plain,(
    ! [A_45,B_46,D_47] :
      ( r2_relset_1(A_45,B_46,D_47,D_47)
      | ~ m1_subset_1(D_47,k1_zfmisc_1(k2_zfmisc_1(A_45,B_46))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_86,plain,(
    r2_relset_1('#skF_1','#skF_2','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_83])).

tff(c_38,plain,(
    ! [C_26,A_27,B_28] :
      ( v1_relat_1(C_26)
      | ~ m1_subset_1(C_26,k1_zfmisc_1(k2_zfmisc_1(A_27,B_28))) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_42,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_38])).

tff(c_68,plain,(
    ! [C_42,A_43,B_44] :
      ( v4_relat_1(C_42,A_43)
      | ~ m1_subset_1(C_42,k1_zfmisc_1(k2_zfmisc_1(A_43,B_44))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_72,plain,(
    v4_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_68])).

tff(c_26,plain,(
    r1_tarski('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_52,plain,(
    ! [B_33,A_34] :
      ( r1_tarski(k1_relat_1(B_33),A_34)
      | ~ v4_relat_1(B_33,A_34)
      | ~ v1_relat_1(B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_4,plain,(
    ! [A_4,B_5] :
      ( k2_xboole_0(A_4,B_5) = B_5
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_87,plain,(
    ! [B_48,A_49] :
      ( k2_xboole_0(k1_relat_1(B_48),A_49) = A_49
      | ~ v4_relat_1(B_48,A_49)
      | ~ v1_relat_1(B_48) ) ),
    inference(resolution,[status(thm)],[c_52,c_4])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,C_3)
      | ~ r1_tarski(k2_xboole_0(A_1,B_2),C_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_99,plain,(
    ! [B_50,C_51,A_52] :
      ( r1_tarski(k1_relat_1(B_50),C_51)
      | ~ r1_tarski(A_52,C_51)
      | ~ v4_relat_1(B_50,A_52)
      | ~ v1_relat_1(B_50) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_87,c_2])).

tff(c_106,plain,(
    ! [B_53] :
      ( r1_tarski(k1_relat_1(B_53),'#skF_3')
      | ~ v4_relat_1(B_53,'#skF_1')
      | ~ v1_relat_1(B_53) ) ),
    inference(resolution,[status(thm)],[c_26,c_99])).

tff(c_6,plain,(
    ! [B_7,A_6] :
      ( v4_relat_1(B_7,A_6)
      | ~ r1_tarski(k1_relat_1(B_7),A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_118,plain,(
    ! [B_54] :
      ( v4_relat_1(B_54,'#skF_3')
      | ~ v4_relat_1(B_54,'#skF_1')
      | ~ v1_relat_1(B_54) ) ),
    inference(resolution,[status(thm)],[c_106,c_6])).

tff(c_10,plain,(
    ! [B_9,A_8] :
      ( k7_relat_1(B_9,A_8) = B_9
      | ~ v4_relat_1(B_9,A_8)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_139,plain,(
    ! [B_60] :
      ( k7_relat_1(B_60,'#skF_3') = B_60
      | ~ v4_relat_1(B_60,'#skF_1')
      | ~ v1_relat_1(B_60) ) ),
    inference(resolution,[status(thm)],[c_118,c_10])).

tff(c_142,plain,
    ( k7_relat_1('#skF_4','#skF_3') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_72,c_139])).

tff(c_145,plain,(
    k7_relat_1('#skF_4','#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_142])).

tff(c_32,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_123,plain,(
    ! [A_55,B_56,C_57,D_58] :
      ( k2_partfun1(A_55,B_56,C_57,D_58) = k7_relat_1(C_57,D_58)
      | ~ m1_subset_1(C_57,k1_zfmisc_1(k2_zfmisc_1(A_55,B_56)))
      | ~ v1_funct_1(C_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_125,plain,(
    ! [D_58] :
      ( k2_partfun1('#skF_1','#skF_2','#skF_4',D_58) = k7_relat_1('#skF_4',D_58)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_28,c_123])).

tff(c_128,plain,(
    ! [D_58] : k2_partfun1('#skF_1','#skF_2','#skF_4',D_58) = k7_relat_1('#skF_4',D_58) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_125])).

tff(c_24,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_129,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k7_relat_1('#skF_4','#skF_3'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_24])).

tff(c_167,plain,(
    ~ r2_relset_1('#skF_1','#skF_2','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_145,c_129])).

tff(c_170,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_167])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 18:40:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.88/1.23  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.13/1.24  
% 2.13/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.13/1.24  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_partfun1 > k7_relat_1 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.13/1.24  
% 2.13/1.24  %Foreground sorts:
% 2.13/1.24  
% 2.13/1.24  
% 2.13/1.24  %Background operators:
% 2.13/1.24  
% 2.13/1.24  
% 2.13/1.24  %Foreground operators:
% 2.13/1.24  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.13/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.13/1.24  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 2.13/1.24  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.13/1.24  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.13/1.24  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.13/1.24  tff('#skF_2', type, '#skF_2': $i).
% 2.13/1.24  tff('#skF_3', type, '#skF_3': $i).
% 2.13/1.24  tff('#skF_1', type, '#skF_1': $i).
% 2.13/1.24  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.13/1.24  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.13/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.13/1.24  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.13/1.24  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.13/1.24  tff('#skF_4', type, '#skF_4': $i).
% 2.13/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.13/1.24  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 2.13/1.24  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.13/1.24  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.13/1.24  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.13/1.24  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.13/1.24  
% 2.13/1.26  tff(f_80, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(A, C) => r2_relset_1(A, B, k2_partfun1(A, B, D, C), D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_funct_2)).
% 2.13/1.26  tff(f_63, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 2.13/1.26  tff(f_49, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.13/1.26  tff(f_55, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.13/1.26  tff(f_39, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 2.13/1.26  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.13/1.26  tff(f_29, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_xboole_1)).
% 2.13/1.26  tff(f_45, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 2.13/1.26  tff(f_69, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 2.13/1.26  tff(c_28, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.13/1.26  tff(c_83, plain, (![A_45, B_46, D_47]: (r2_relset_1(A_45, B_46, D_47, D_47) | ~m1_subset_1(D_47, k1_zfmisc_1(k2_zfmisc_1(A_45, B_46))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.13/1.26  tff(c_86, plain, (r2_relset_1('#skF_1', '#skF_2', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_28, c_83])).
% 2.13/1.26  tff(c_38, plain, (![C_26, A_27, B_28]: (v1_relat_1(C_26) | ~m1_subset_1(C_26, k1_zfmisc_1(k2_zfmisc_1(A_27, B_28))))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.13/1.26  tff(c_42, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_28, c_38])).
% 2.13/1.26  tff(c_68, plain, (![C_42, A_43, B_44]: (v4_relat_1(C_42, A_43) | ~m1_subset_1(C_42, k1_zfmisc_1(k2_zfmisc_1(A_43, B_44))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.13/1.26  tff(c_72, plain, (v4_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_28, c_68])).
% 2.13/1.26  tff(c_26, plain, (r1_tarski('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.13/1.26  tff(c_52, plain, (![B_33, A_34]: (r1_tarski(k1_relat_1(B_33), A_34) | ~v4_relat_1(B_33, A_34) | ~v1_relat_1(B_33))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.13/1.26  tff(c_4, plain, (![A_4, B_5]: (k2_xboole_0(A_4, B_5)=B_5 | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.13/1.26  tff(c_87, plain, (![B_48, A_49]: (k2_xboole_0(k1_relat_1(B_48), A_49)=A_49 | ~v4_relat_1(B_48, A_49) | ~v1_relat_1(B_48))), inference(resolution, [status(thm)], [c_52, c_4])).
% 2.13/1.26  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, C_3) | ~r1_tarski(k2_xboole_0(A_1, B_2), C_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.13/1.26  tff(c_99, plain, (![B_50, C_51, A_52]: (r1_tarski(k1_relat_1(B_50), C_51) | ~r1_tarski(A_52, C_51) | ~v4_relat_1(B_50, A_52) | ~v1_relat_1(B_50))), inference(superposition, [status(thm), theory('equality')], [c_87, c_2])).
% 2.13/1.26  tff(c_106, plain, (![B_53]: (r1_tarski(k1_relat_1(B_53), '#skF_3') | ~v4_relat_1(B_53, '#skF_1') | ~v1_relat_1(B_53))), inference(resolution, [status(thm)], [c_26, c_99])).
% 2.13/1.26  tff(c_6, plain, (![B_7, A_6]: (v4_relat_1(B_7, A_6) | ~r1_tarski(k1_relat_1(B_7), A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.13/1.26  tff(c_118, plain, (![B_54]: (v4_relat_1(B_54, '#skF_3') | ~v4_relat_1(B_54, '#skF_1') | ~v1_relat_1(B_54))), inference(resolution, [status(thm)], [c_106, c_6])).
% 2.13/1.26  tff(c_10, plain, (![B_9, A_8]: (k7_relat_1(B_9, A_8)=B_9 | ~v4_relat_1(B_9, A_8) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.13/1.26  tff(c_139, plain, (![B_60]: (k7_relat_1(B_60, '#skF_3')=B_60 | ~v4_relat_1(B_60, '#skF_1') | ~v1_relat_1(B_60))), inference(resolution, [status(thm)], [c_118, c_10])).
% 2.13/1.26  tff(c_142, plain, (k7_relat_1('#skF_4', '#skF_3')='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_72, c_139])).
% 2.13/1.26  tff(c_145, plain, (k7_relat_1('#skF_4', '#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_142])).
% 2.13/1.26  tff(c_32, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.13/1.26  tff(c_123, plain, (![A_55, B_56, C_57, D_58]: (k2_partfun1(A_55, B_56, C_57, D_58)=k7_relat_1(C_57, D_58) | ~m1_subset_1(C_57, k1_zfmisc_1(k2_zfmisc_1(A_55, B_56))) | ~v1_funct_1(C_57))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.13/1.26  tff(c_125, plain, (![D_58]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_58)=k7_relat_1('#skF_4', D_58) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_28, c_123])).
% 2.13/1.26  tff(c_128, plain, (![D_58]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_58)=k7_relat_1('#skF_4', D_58))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_125])).
% 2.13/1.26  tff(c_24, plain, (~r2_relset_1('#skF_1', '#skF_2', k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.13/1.26  tff(c_129, plain, (~r2_relset_1('#skF_1', '#skF_2', k7_relat_1('#skF_4', '#skF_3'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_128, c_24])).
% 2.13/1.26  tff(c_167, plain, (~r2_relset_1('#skF_1', '#skF_2', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_145, c_129])).
% 2.13/1.26  tff(c_170, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_86, c_167])).
% 2.13/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.13/1.26  
% 2.13/1.26  Inference rules
% 2.13/1.26  ----------------------
% 2.13/1.26  #Ref     : 0
% 2.13/1.26  #Sup     : 31
% 2.13/1.26  #Fact    : 0
% 2.13/1.26  #Define  : 0
% 2.13/1.26  #Split   : 0
% 2.13/1.26  #Chain   : 0
% 2.13/1.26  #Close   : 0
% 2.13/1.26  
% 2.13/1.26  Ordering : KBO
% 2.13/1.26  
% 2.13/1.26  Simplification rules
% 2.13/1.26  ----------------------
% 2.13/1.26  #Subsume      : 0
% 2.13/1.26  #Demod        : 6
% 2.13/1.26  #Tautology    : 13
% 2.13/1.26  #SimpNegUnit  : 0
% 2.13/1.26  #BackRed      : 2
% 2.13/1.26  
% 2.13/1.26  #Partial instantiations: 0
% 2.13/1.26  #Strategies tried      : 1
% 2.13/1.26  
% 2.13/1.26  Timing (in seconds)
% 2.13/1.26  ----------------------
% 2.13/1.26  Preprocessing        : 0.28
% 2.13/1.26  Parsing              : 0.15
% 2.13/1.26  CNF conversion       : 0.02
% 2.13/1.26  Main loop            : 0.15
% 2.13/1.26  Inferencing          : 0.06
% 2.13/1.26  Reduction            : 0.04
% 2.13/1.26  Demodulation         : 0.03
% 2.13/1.26  BG Simplification    : 0.01
% 2.13/1.26  Subsumption          : 0.02
% 2.13/1.26  Abstraction          : 0.01
% 2.13/1.26  MUC search           : 0.00
% 2.13/1.26  Cooper               : 0.00
% 2.13/1.26  Total                : 0.46
% 2.13/1.26  Index Insertion      : 0.00
% 2.13/1.26  Index Deletion       : 0.00
% 2.13/1.26  Index Matching       : 0.00
% 2.13/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
