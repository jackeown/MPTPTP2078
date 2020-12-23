%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:43 EST 2020

% Result     : Theorem 2.51s
% Output     : CNFRefutation 2.51s
% Verified   : 
% Statistics : Number of formulae       :   61 (  81 expanded)
%              Number of leaves         :   30 (  41 expanded)
%              Depth                    :   11
%              Number of atoms          :   84 ( 142 expanded)
%              Number of equality atoms :   14 (  14 expanded)
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

tff(f_88,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( r1_tarski(A,C)
         => r2_relset_1(A,B,k2_partfun1(A,B,D,C),D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_funct_2)).

tff(f_71,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_77,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(c_32,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_248,plain,(
    ! [A_57,B_58,D_59] :
      ( r2_relset_1(A_57,B_58,D_59,D_59)
      | ~ m1_subset_1(D_59,k1_zfmisc_1(k2_zfmisc_1(A_57,B_58))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_251,plain,(
    r2_relset_1('#skF_1','#skF_2','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_248])).

tff(c_50,plain,(
    ! [C_29,A_30,B_31] :
      ( v1_relat_1(C_29)
      | ~ m1_subset_1(C_29,k1_zfmisc_1(k2_zfmisc_1(A_30,B_31))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_54,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_50])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_86,plain,(
    ! [C_41,A_42,B_43] :
      ( v4_relat_1(C_41,A_42)
      | ~ m1_subset_1(C_41,k1_zfmisc_1(k2_zfmisc_1(A_42,B_43))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_90,plain,(
    v4_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_86])).

tff(c_10,plain,(
    ! [B_7,A_6] :
      ( k7_relat_1(B_7,A_6) = B_7
      | ~ v4_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_93,plain,
    ( k7_relat_1('#skF_4','#skF_1') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_90,c_10])).

tff(c_96,plain,(
    k7_relat_1('#skF_4','#skF_1') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_93])).

tff(c_12,plain,(
    ! [B_9,A_8] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_9,A_8)),A_8)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_100,plain,
    ( r1_tarski(k1_relat_1('#skF_4'),'#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_12])).

tff(c_104,plain,(
    r1_tarski(k1_relat_1('#skF_4'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_100])).

tff(c_30,plain,(
    r1_tarski('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_59,plain,(
    ! [A_34,C_35,B_36] :
      ( r1_tarski(A_34,C_35)
      | ~ r1_tarski(B_36,C_35)
      | ~ r1_tarski(A_34,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_69,plain,(
    ! [A_37] :
      ( r1_tarski(A_37,'#skF_3')
      | ~ r1_tarski(A_37,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_30,c_59])).

tff(c_8,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(A_3,C_5)
      | ~ r1_tarski(B_4,C_5)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_74,plain,(
    ! [A_3,A_37] :
      ( r1_tarski(A_3,'#skF_3')
      | ~ r1_tarski(A_3,A_37)
      | ~ r1_tarski(A_37,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_69,c_8])).

tff(c_121,plain,
    ( r1_tarski(k1_relat_1('#skF_4'),'#skF_3')
    | ~ r1_tarski('#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_104,c_74])).

tff(c_128,plain,(
    r1_tarski(k1_relat_1('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_121])).

tff(c_209,plain,(
    ! [B_55,A_56] :
      ( k7_relat_1(B_55,A_56) = B_55
      | ~ r1_tarski(k1_relat_1(B_55),A_56)
      | ~ v1_relat_1(B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_221,plain,
    ( k7_relat_1('#skF_4','#skF_3') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_128,c_209])).

tff(c_241,plain,(
    k7_relat_1('#skF_4','#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_221])).

tff(c_36,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_451,plain,(
    ! [A_72,B_73,C_74,D_75] :
      ( k2_partfun1(A_72,B_73,C_74,D_75) = k7_relat_1(C_74,D_75)
      | ~ m1_subset_1(C_74,k1_zfmisc_1(k2_zfmisc_1(A_72,B_73)))
      | ~ v1_funct_1(C_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_453,plain,(
    ! [D_75] :
      ( k2_partfun1('#skF_1','#skF_2','#skF_4',D_75) = k7_relat_1('#skF_4',D_75)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_32,c_451])).

tff(c_456,plain,(
    ! [D_75] : k2_partfun1('#skF_1','#skF_2','#skF_4',D_75) = k7_relat_1('#skF_4',D_75) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_453])).

tff(c_28,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_457,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k7_relat_1('#skF_4','#skF_3'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_456,c_28])).

tff(c_460,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_251,c_241,c_457])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:44:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.51/1.37  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.51/1.38  
% 2.51/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.51/1.38  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_partfun1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.51/1.38  
% 2.51/1.38  %Foreground sorts:
% 2.51/1.38  
% 2.51/1.38  
% 2.51/1.38  %Background operators:
% 2.51/1.38  
% 2.51/1.38  
% 2.51/1.38  %Foreground operators:
% 2.51/1.38  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.51/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.51/1.38  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 2.51/1.38  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.51/1.38  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.51/1.38  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.51/1.38  tff('#skF_2', type, '#skF_2': $i).
% 2.51/1.38  tff('#skF_3', type, '#skF_3': $i).
% 2.51/1.38  tff('#skF_1', type, '#skF_1': $i).
% 2.51/1.38  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.51/1.38  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.51/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.51/1.38  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.51/1.38  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.51/1.38  tff('#skF_4', type, '#skF_4': $i).
% 2.51/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.51/1.38  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 2.51/1.38  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.51/1.38  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.51/1.38  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.51/1.38  
% 2.51/1.39  tff(f_88, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(A, C) => r2_relset_1(A, B, k2_partfun1(A, B, D, C), D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_funct_2)).
% 2.51/1.39  tff(f_71, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 2.51/1.39  tff(f_57, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.51/1.39  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.51/1.39  tff(f_63, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.51/1.39  tff(f_43, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 2.51/1.39  tff(f_47, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_relat_1)).
% 2.51/1.39  tff(f_37, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 2.51/1.39  tff(f_53, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t97_relat_1)).
% 2.51/1.39  tff(f_77, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 2.51/1.39  tff(c_32, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.51/1.39  tff(c_248, plain, (![A_57, B_58, D_59]: (r2_relset_1(A_57, B_58, D_59, D_59) | ~m1_subset_1(D_59, k1_zfmisc_1(k2_zfmisc_1(A_57, B_58))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.51/1.39  tff(c_251, plain, (r2_relset_1('#skF_1', '#skF_2', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_32, c_248])).
% 2.51/1.39  tff(c_50, plain, (![C_29, A_30, B_31]: (v1_relat_1(C_29) | ~m1_subset_1(C_29, k1_zfmisc_1(k2_zfmisc_1(A_30, B_31))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.51/1.39  tff(c_54, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_32, c_50])).
% 2.51/1.39  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.51/1.39  tff(c_86, plain, (![C_41, A_42, B_43]: (v4_relat_1(C_41, A_42) | ~m1_subset_1(C_41, k1_zfmisc_1(k2_zfmisc_1(A_42, B_43))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.51/1.39  tff(c_90, plain, (v4_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_32, c_86])).
% 2.51/1.39  tff(c_10, plain, (![B_7, A_6]: (k7_relat_1(B_7, A_6)=B_7 | ~v4_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.51/1.39  tff(c_93, plain, (k7_relat_1('#skF_4', '#skF_1')='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_90, c_10])).
% 2.51/1.39  tff(c_96, plain, (k7_relat_1('#skF_4', '#skF_1')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_54, c_93])).
% 2.51/1.39  tff(c_12, plain, (![B_9, A_8]: (r1_tarski(k1_relat_1(k7_relat_1(B_9, A_8)), A_8) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.51/1.39  tff(c_100, plain, (r1_tarski(k1_relat_1('#skF_4'), '#skF_1') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_96, c_12])).
% 2.51/1.39  tff(c_104, plain, (r1_tarski(k1_relat_1('#skF_4'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_100])).
% 2.51/1.39  tff(c_30, plain, (r1_tarski('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.51/1.39  tff(c_59, plain, (![A_34, C_35, B_36]: (r1_tarski(A_34, C_35) | ~r1_tarski(B_36, C_35) | ~r1_tarski(A_34, B_36))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.51/1.39  tff(c_69, plain, (![A_37]: (r1_tarski(A_37, '#skF_3') | ~r1_tarski(A_37, '#skF_1'))), inference(resolution, [status(thm)], [c_30, c_59])).
% 2.51/1.39  tff(c_8, plain, (![A_3, C_5, B_4]: (r1_tarski(A_3, C_5) | ~r1_tarski(B_4, C_5) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.51/1.39  tff(c_74, plain, (![A_3, A_37]: (r1_tarski(A_3, '#skF_3') | ~r1_tarski(A_3, A_37) | ~r1_tarski(A_37, '#skF_1'))), inference(resolution, [status(thm)], [c_69, c_8])).
% 2.51/1.39  tff(c_121, plain, (r1_tarski(k1_relat_1('#skF_4'), '#skF_3') | ~r1_tarski('#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_104, c_74])).
% 2.51/1.39  tff(c_128, plain, (r1_tarski(k1_relat_1('#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_121])).
% 2.51/1.39  tff(c_209, plain, (![B_55, A_56]: (k7_relat_1(B_55, A_56)=B_55 | ~r1_tarski(k1_relat_1(B_55), A_56) | ~v1_relat_1(B_55))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.51/1.39  tff(c_221, plain, (k7_relat_1('#skF_4', '#skF_3')='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_128, c_209])).
% 2.51/1.39  tff(c_241, plain, (k7_relat_1('#skF_4', '#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_54, c_221])).
% 2.51/1.39  tff(c_36, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.51/1.39  tff(c_451, plain, (![A_72, B_73, C_74, D_75]: (k2_partfun1(A_72, B_73, C_74, D_75)=k7_relat_1(C_74, D_75) | ~m1_subset_1(C_74, k1_zfmisc_1(k2_zfmisc_1(A_72, B_73))) | ~v1_funct_1(C_74))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.51/1.39  tff(c_453, plain, (![D_75]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_75)=k7_relat_1('#skF_4', D_75) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_32, c_451])).
% 2.51/1.39  tff(c_456, plain, (![D_75]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_75)=k7_relat_1('#skF_4', D_75))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_453])).
% 2.51/1.39  tff(c_28, plain, (~r2_relset_1('#skF_1', '#skF_2', k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.51/1.39  tff(c_457, plain, (~r2_relset_1('#skF_1', '#skF_2', k7_relat_1('#skF_4', '#skF_3'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_456, c_28])).
% 2.51/1.39  tff(c_460, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_251, c_241, c_457])).
% 2.51/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.51/1.39  
% 2.51/1.39  Inference rules
% 2.51/1.39  ----------------------
% 2.51/1.39  #Ref     : 0
% 2.51/1.39  #Sup     : 94
% 2.51/1.39  #Fact    : 0
% 2.51/1.39  #Define  : 0
% 2.51/1.39  #Split   : 3
% 2.51/1.39  #Chain   : 0
% 2.51/1.39  #Close   : 0
% 2.51/1.39  
% 2.51/1.39  Ordering : KBO
% 2.51/1.39  
% 2.51/1.39  Simplification rules
% 2.51/1.39  ----------------------
% 2.51/1.39  #Subsume      : 24
% 2.51/1.39  #Demod        : 56
% 2.51/1.39  #Tautology    : 26
% 2.51/1.39  #SimpNegUnit  : 0
% 2.51/1.39  #BackRed      : 1
% 2.51/1.39  
% 2.51/1.39  #Partial instantiations: 0
% 2.51/1.39  #Strategies tried      : 1
% 2.51/1.39  
% 2.51/1.39  Timing (in seconds)
% 2.51/1.39  ----------------------
% 2.51/1.39  Preprocessing        : 0.29
% 2.51/1.39  Parsing              : 0.15
% 2.51/1.39  CNF conversion       : 0.02
% 2.51/1.39  Main loop            : 0.27
% 2.51/1.39  Inferencing          : 0.10
% 2.51/1.40  Reduction            : 0.08
% 2.51/1.40  Demodulation         : 0.06
% 2.51/1.40  BG Simplification    : 0.01
% 2.51/1.40  Subsumption          : 0.06
% 2.51/1.40  Abstraction          : 0.02
% 2.51/1.40  MUC search           : 0.00
% 2.51/1.40  Cooper               : 0.00
% 2.51/1.40  Total                : 0.59
% 2.51/1.40  Index Insertion      : 0.00
% 2.71/1.40  Index Deletion       : 0.00
% 2.71/1.40  Index Matching       : 0.00
% 2.71/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
