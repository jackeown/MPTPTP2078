%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:27 EST 2020

% Result     : Theorem 2.53s
% Output     : CNFRefutation 2.89s
% Verified   : 
% Statistics : Number of formulae       :   49 (  72 expanded)
%              Number of leaves         :   25 (  36 expanded)
%              Depth                    :    8
%              Number of atoms          :   63 ( 104 expanded)
%              Number of equality atoms :    3 (   6 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k5_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k5_relset_1,type,(
    k5_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff(f_70,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C)))
       => m1_subset_1(k5_relset_1(A,C,D,B),k1_zfmisc_1(k2_zfmisc_1(B,C))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_relset_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v4_relat_1(C,B) )
     => ( v1_relat_1(k7_relat_1(C,A))
        & v4_relat_1(k7_relat_1(C,A),A)
        & v4_relat_1(k7_relat_1(C,A),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc23_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_59,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k5_relset_1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k5_relset_1)).

tff(f_55,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k5_relset_1(A,B,C,D),k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relset_1)).

tff(f_65,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C)))
     => ( r1_tarski(k1_relat_1(D),B)
       => m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_relset_1)).

tff(c_26,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_27,plain,(
    ! [C_24,A_25,B_26] :
      ( v1_relat_1(C_24)
      | ~ m1_subset_1(C_24,k1_zfmisc_1(k2_zfmisc_1(A_25,B_26))) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_31,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_26,c_27])).

tff(c_44,plain,(
    ! [C_37,A_38,B_39] :
      ( v4_relat_1(C_37,A_38)
      | ~ m1_subset_1(C_37,k1_zfmisc_1(k2_zfmisc_1(A_38,B_39))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_48,plain,(
    v4_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_44])).

tff(c_10,plain,(
    ! [C_5,A_3,B_4] :
      ( v1_relat_1(k7_relat_1(C_5,A_3))
      | ~ v4_relat_1(C_5,B_4)
      | ~ v1_relat_1(C_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_50,plain,(
    ! [A_3] :
      ( v1_relat_1(k7_relat_1('#skF_4',A_3))
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_48,c_10])).

tff(c_53,plain,(
    ! [A_3] : v1_relat_1(k7_relat_1('#skF_4',A_3)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_31,c_50])).

tff(c_55,plain,(
    ! [C_41,A_42,B_43] :
      ( v4_relat_1(k7_relat_1(C_41,A_42),A_42)
      | ~ v4_relat_1(C_41,B_43)
      | ~ v1_relat_1(C_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_57,plain,(
    ! [A_42] :
      ( v4_relat_1(k7_relat_1('#skF_4',A_42),A_42)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_48,c_55])).

tff(c_60,plain,(
    ! [A_42] : v4_relat_1(k7_relat_1('#skF_4',A_42),A_42) ),
    inference(demodulation,[status(thm),theory(equality)],[c_31,c_57])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( r1_tarski(k1_relat_1(B_2),A_1)
      | ~ v4_relat_1(B_2,A_1)
      | ~ v1_relat_1(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_127,plain,(
    ! [A_76,B_77,C_78,D_79] :
      ( k5_relset_1(A_76,B_77,C_78,D_79) = k7_relat_1(C_78,D_79)
      | ~ m1_subset_1(C_78,k1_zfmisc_1(k2_zfmisc_1(A_76,B_77))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_130,plain,(
    ! [D_79] : k5_relset_1('#skF_1','#skF_3','#skF_4',D_79) = k7_relat_1('#skF_4',D_79) ),
    inference(resolution,[status(thm)],[c_26,c_127])).

tff(c_237,plain,(
    ! [A_107,B_108,C_109,D_110] :
      ( m1_subset_1(k5_relset_1(A_107,B_108,C_109,D_110),k1_zfmisc_1(k2_zfmisc_1(A_107,B_108)))
      | ~ m1_subset_1(C_109,k1_zfmisc_1(k2_zfmisc_1(A_107,B_108))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_253,plain,(
    ! [D_79] :
      ( m1_subset_1(k7_relat_1('#skF_4',D_79),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3')))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_130,c_237])).

tff(c_272,plain,(
    ! [D_115] : m1_subset_1(k7_relat_1('#skF_4',D_115),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_253])).

tff(c_22,plain,(
    ! [D_23,B_21,C_22,A_20] :
      ( m1_subset_1(D_23,k1_zfmisc_1(k2_zfmisc_1(B_21,C_22)))
      | ~ r1_tarski(k1_relat_1(D_23),B_21)
      | ~ m1_subset_1(D_23,k1_zfmisc_1(k2_zfmisc_1(A_20,C_22))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_535,plain,(
    ! [D_165,B_166] :
      ( m1_subset_1(k7_relat_1('#skF_4',D_165),k1_zfmisc_1(k2_zfmisc_1(B_166,'#skF_3')))
      | ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_4',D_165)),B_166) ) ),
    inference(resolution,[status(thm)],[c_272,c_22])).

tff(c_24,plain,(
    ~ m1_subset_1(k5_relset_1('#skF_1','#skF_3','#skF_4','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_131,plain,(
    ~ m1_subset_1(k7_relat_1('#skF_4','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_24])).

tff(c_561,plain,(
    ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_4','#skF_2')),'#skF_2') ),
    inference(resolution,[status(thm)],[c_535,c_131])).

tff(c_571,plain,
    ( ~ v4_relat_1(k7_relat_1('#skF_4','#skF_2'),'#skF_2')
    | ~ v1_relat_1(k7_relat_1('#skF_4','#skF_2')) ),
    inference(resolution,[status(thm)],[c_4,c_561])).

tff(c_575,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_60,c_571])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n018.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:48:56 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.53/1.45  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.53/1.46  
% 2.53/1.46  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.53/1.46  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k5_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.53/1.46  
% 2.53/1.46  %Foreground sorts:
% 2.53/1.46  
% 2.53/1.46  
% 2.53/1.46  %Background operators:
% 2.53/1.46  
% 2.53/1.46  
% 2.53/1.46  %Foreground operators:
% 2.53/1.46  tff(k5_relset_1, type, k5_relset_1: ($i * $i * $i * $i) > $i).
% 2.53/1.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.53/1.46  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.53/1.46  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.53/1.46  tff('#skF_2', type, '#skF_2': $i).
% 2.53/1.46  tff('#skF_3', type, '#skF_3': $i).
% 2.53/1.46  tff('#skF_1', type, '#skF_1': $i).
% 2.53/1.46  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.53/1.46  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.53/1.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.53/1.46  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.53/1.46  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.53/1.46  tff('#skF_4', type, '#skF_4': $i).
% 2.53/1.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.53/1.46  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.53/1.46  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.53/1.46  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.53/1.46  
% 2.89/1.47  tff(f_70, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C))) => m1_subset_1(k5_relset_1(A, C, D, B), k1_zfmisc_1(k2_zfmisc_1(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t33_relset_1)).
% 2.89/1.47  tff(f_45, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.89/1.47  tff(f_51, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.89/1.47  tff(f_41, axiom, (![A, B, C]: ((v1_relat_1(C) & v4_relat_1(C, B)) => ((v1_relat_1(k7_relat_1(C, A)) & v4_relat_1(k7_relat_1(C, A), A)) & v4_relat_1(k7_relat_1(C, A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc23_relat_1)).
% 2.89/1.47  tff(f_31, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 2.89/1.47  tff(f_59, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k5_relset_1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k5_relset_1)).
% 2.89/1.47  tff(f_55, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k5_relset_1(A, B, C, D), k1_zfmisc_1(k2_zfmisc_1(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_relset_1)).
% 2.89/1.47  tff(f_65, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C))) => (r1_tarski(k1_relat_1(D), B) => m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_relset_1)).
% 2.89/1.47  tff(c_26, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.89/1.47  tff(c_27, plain, (![C_24, A_25, B_26]: (v1_relat_1(C_24) | ~m1_subset_1(C_24, k1_zfmisc_1(k2_zfmisc_1(A_25, B_26))))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.89/1.47  tff(c_31, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_26, c_27])).
% 2.89/1.47  tff(c_44, plain, (![C_37, A_38, B_39]: (v4_relat_1(C_37, A_38) | ~m1_subset_1(C_37, k1_zfmisc_1(k2_zfmisc_1(A_38, B_39))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.89/1.47  tff(c_48, plain, (v4_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_26, c_44])).
% 2.89/1.47  tff(c_10, plain, (![C_5, A_3, B_4]: (v1_relat_1(k7_relat_1(C_5, A_3)) | ~v4_relat_1(C_5, B_4) | ~v1_relat_1(C_5))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.89/1.47  tff(c_50, plain, (![A_3]: (v1_relat_1(k7_relat_1('#skF_4', A_3)) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_48, c_10])).
% 2.89/1.47  tff(c_53, plain, (![A_3]: (v1_relat_1(k7_relat_1('#skF_4', A_3)))), inference(demodulation, [status(thm), theory('equality')], [c_31, c_50])).
% 2.89/1.47  tff(c_55, plain, (![C_41, A_42, B_43]: (v4_relat_1(k7_relat_1(C_41, A_42), A_42) | ~v4_relat_1(C_41, B_43) | ~v1_relat_1(C_41))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.89/1.47  tff(c_57, plain, (![A_42]: (v4_relat_1(k7_relat_1('#skF_4', A_42), A_42) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_48, c_55])).
% 2.89/1.47  tff(c_60, plain, (![A_42]: (v4_relat_1(k7_relat_1('#skF_4', A_42), A_42))), inference(demodulation, [status(thm), theory('equality')], [c_31, c_57])).
% 2.89/1.47  tff(c_4, plain, (![B_2, A_1]: (r1_tarski(k1_relat_1(B_2), A_1) | ~v4_relat_1(B_2, A_1) | ~v1_relat_1(B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.89/1.47  tff(c_127, plain, (![A_76, B_77, C_78, D_79]: (k5_relset_1(A_76, B_77, C_78, D_79)=k7_relat_1(C_78, D_79) | ~m1_subset_1(C_78, k1_zfmisc_1(k2_zfmisc_1(A_76, B_77))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.89/1.47  tff(c_130, plain, (![D_79]: (k5_relset_1('#skF_1', '#skF_3', '#skF_4', D_79)=k7_relat_1('#skF_4', D_79))), inference(resolution, [status(thm)], [c_26, c_127])).
% 2.89/1.47  tff(c_237, plain, (![A_107, B_108, C_109, D_110]: (m1_subset_1(k5_relset_1(A_107, B_108, C_109, D_110), k1_zfmisc_1(k2_zfmisc_1(A_107, B_108))) | ~m1_subset_1(C_109, k1_zfmisc_1(k2_zfmisc_1(A_107, B_108))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.89/1.47  tff(c_253, plain, (![D_79]: (m1_subset_1(k7_relat_1('#skF_4', D_79), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3'))))), inference(superposition, [status(thm), theory('equality')], [c_130, c_237])).
% 2.89/1.47  tff(c_272, plain, (![D_115]: (m1_subset_1(k7_relat_1('#skF_4', D_115), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_253])).
% 2.89/1.47  tff(c_22, plain, (![D_23, B_21, C_22, A_20]: (m1_subset_1(D_23, k1_zfmisc_1(k2_zfmisc_1(B_21, C_22))) | ~r1_tarski(k1_relat_1(D_23), B_21) | ~m1_subset_1(D_23, k1_zfmisc_1(k2_zfmisc_1(A_20, C_22))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.89/1.47  tff(c_535, plain, (![D_165, B_166]: (m1_subset_1(k7_relat_1('#skF_4', D_165), k1_zfmisc_1(k2_zfmisc_1(B_166, '#skF_3'))) | ~r1_tarski(k1_relat_1(k7_relat_1('#skF_4', D_165)), B_166))), inference(resolution, [status(thm)], [c_272, c_22])).
% 2.89/1.47  tff(c_24, plain, (~m1_subset_1(k5_relset_1('#skF_1', '#skF_3', '#skF_4', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.89/1.47  tff(c_131, plain, (~m1_subset_1(k7_relat_1('#skF_4', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_130, c_24])).
% 2.89/1.47  tff(c_561, plain, (~r1_tarski(k1_relat_1(k7_relat_1('#skF_4', '#skF_2')), '#skF_2')), inference(resolution, [status(thm)], [c_535, c_131])).
% 2.89/1.47  tff(c_571, plain, (~v4_relat_1(k7_relat_1('#skF_4', '#skF_2'), '#skF_2') | ~v1_relat_1(k7_relat_1('#skF_4', '#skF_2'))), inference(resolution, [status(thm)], [c_4, c_561])).
% 2.89/1.47  tff(c_575, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_53, c_60, c_571])).
% 2.89/1.47  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.89/1.47  
% 2.89/1.47  Inference rules
% 2.89/1.47  ----------------------
% 2.89/1.47  #Ref     : 0
% 2.89/1.47  #Sup     : 116
% 2.89/1.47  #Fact    : 0
% 2.89/1.47  #Define  : 0
% 2.89/1.47  #Split   : 0
% 2.89/1.47  #Chain   : 0
% 2.89/1.47  #Close   : 0
% 2.89/1.47  
% 2.89/1.47  Ordering : KBO
% 2.89/1.47  
% 2.89/1.47  Simplification rules
% 2.89/1.47  ----------------------
% 2.89/1.47  #Subsume      : 2
% 2.89/1.47  #Demod        : 110
% 2.89/1.47  #Tautology    : 40
% 2.89/1.47  #SimpNegUnit  : 0
% 2.89/1.47  #BackRed      : 2
% 2.89/1.47  
% 2.89/1.47  #Partial instantiations: 0
% 2.89/1.47  #Strategies tried      : 1
% 2.89/1.47  
% 2.89/1.47  Timing (in seconds)
% 2.89/1.47  ----------------------
% 2.89/1.47  Preprocessing        : 0.28
% 2.89/1.47  Parsing              : 0.15
% 2.89/1.47  CNF conversion       : 0.02
% 2.89/1.47  Main loop            : 0.35
% 2.89/1.47  Inferencing          : 0.13
% 2.89/1.47  Reduction            : 0.12
% 2.89/1.48  Demodulation         : 0.09
% 2.89/1.48  BG Simplification    : 0.02
% 2.89/1.48  Subsumption          : 0.05
% 2.89/1.48  Abstraction          : 0.02
% 2.89/1.48  MUC search           : 0.00
% 2.89/1.48  Cooper               : 0.00
% 2.89/1.48  Total                : 0.65
% 2.89/1.48  Index Insertion      : 0.00
% 2.89/1.48  Index Deletion       : 0.00
% 2.89/1.48  Index Matching       : 0.00
% 2.89/1.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
