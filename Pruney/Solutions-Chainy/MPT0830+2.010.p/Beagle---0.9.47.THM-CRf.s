%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:27 EST 2020

% Result     : Theorem 2.37s
% Output     : CNFRefutation 2.37s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 136 expanded)
%              Number of leaves         :   27 (  58 expanded)
%              Depth                    :   10
%              Number of atoms          :   84 ( 233 expanded)
%              Number of equality atoms :    3 (   6 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k5_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff(f_82,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C)))
       => m1_subset_1(k5_relset_1(A,C,D,B),k1_zfmisc_1(k2_zfmisc_1(B,C))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_relset_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v5_relat_1(C,B) )
     => ( v1_relat_1(k7_relat_1(C,A))
        & v5_relat_1(k7_relat_1(C,A),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc22_relat_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_47,axiom,(
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

tff(f_77,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_69,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k5_relset_1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k5_relset_1)).

tff(c_32,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_33,plain,(
    ! [C_24,A_25,B_26] :
      ( v1_relat_1(C_24)
      | ~ m1_subset_1(C_24,k1_zfmisc_1(k2_zfmisc_1(A_25,B_26))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_37,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_33])).

tff(c_38,plain,(
    ! [C_27,B_28,A_29] :
      ( v5_relat_1(C_27,B_28)
      | ~ m1_subset_1(C_27,k1_zfmisc_1(k2_zfmisc_1(A_29,B_28))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_42,plain,(
    v5_relat_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_38])).

tff(c_16,plain,(
    ! [C_10,A_8,B_9] :
      ( v5_relat_1(k7_relat_1(C_10,A_8),B_9)
      | ~ v5_relat_1(C_10,B_9)
      | ~ v1_relat_1(C_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_50,plain,(
    ! [C_36,A_37,B_38] :
      ( v1_relat_1(k7_relat_1(C_36,A_37))
      | ~ v5_relat_1(C_36,B_38)
      | ~ v1_relat_1(C_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_52,plain,(
    ! [A_37] :
      ( v1_relat_1(k7_relat_1('#skF_4',A_37))
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_42,c_50])).

tff(c_55,plain,(
    ! [A_37] : v1_relat_1(k7_relat_1('#skF_4',A_37)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_37,c_52])).

tff(c_8,plain,(
    ! [B_4,A_3] :
      ( r1_tarski(k2_relat_1(B_4),A_3)
      | ~ v5_relat_1(B_4,A_3)
      | ~ v1_relat_1(B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_63,plain,(
    ! [C_45,A_46,B_47] :
      ( v4_relat_1(C_45,A_46)
      | ~ m1_subset_1(C_45,k1_zfmisc_1(k2_zfmisc_1(A_46,B_47))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_67,plain,(
    v4_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_63])).

tff(c_81,plain,(
    ! [C_54,A_55,B_56] :
      ( v4_relat_1(k7_relat_1(C_54,A_55),A_55)
      | ~ v4_relat_1(C_54,B_56)
      | ~ v1_relat_1(C_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_85,plain,(
    ! [A_55] :
      ( v4_relat_1(k7_relat_1('#skF_4',A_55),A_55)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_67,c_81])).

tff(c_89,plain,(
    ! [A_55] : v4_relat_1(k7_relat_1('#skF_4',A_55),A_55) ),
    inference(demodulation,[status(thm),theory(equality)],[c_37,c_85])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( r1_tarski(k1_relat_1(B_2),A_1)
      | ~ v4_relat_1(B_2,A_1)
      | ~ v1_relat_1(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_223,plain,(
    ! [C_111,A_112,B_113] :
      ( m1_subset_1(C_111,k1_zfmisc_1(k2_zfmisc_1(A_112,B_113)))
      | ~ r1_tarski(k2_relat_1(C_111),B_113)
      | ~ r1_tarski(k1_relat_1(C_111),A_112)
      | ~ v1_relat_1(C_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_137,plain,(
    ! [A_76,B_77,C_78,D_79] :
      ( k5_relset_1(A_76,B_77,C_78,D_79) = k7_relat_1(C_78,D_79)
      | ~ m1_subset_1(C_78,k1_zfmisc_1(k2_zfmisc_1(A_76,B_77))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_140,plain,(
    ! [D_79] : k5_relset_1('#skF_1','#skF_3','#skF_4',D_79) = k7_relat_1('#skF_4',D_79) ),
    inference(resolution,[status(thm)],[c_32,c_137])).

tff(c_30,plain,(
    ~ m1_subset_1(k5_relset_1('#skF_1','#skF_3','#skF_4','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_141,plain,(
    ~ m1_subset_1(k7_relat_1('#skF_4','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_30])).

tff(c_226,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4','#skF_2')),'#skF_3')
    | ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_4','#skF_2')),'#skF_2')
    | ~ v1_relat_1(k7_relat_1('#skF_4','#skF_2')) ),
    inference(resolution,[status(thm)],[c_223,c_141])).

tff(c_240,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4','#skF_2')),'#skF_3')
    | ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_4','#skF_2')),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_226])).

tff(c_284,plain,(
    ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_4','#skF_2')),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_240])).

tff(c_287,plain,
    ( ~ v4_relat_1(k7_relat_1('#skF_4','#skF_2'),'#skF_2')
    | ~ v1_relat_1(k7_relat_1('#skF_4','#skF_2')) ),
    inference(resolution,[status(thm)],[c_4,c_284])).

tff(c_291,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_89,c_287])).

tff(c_292,plain,(
    ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4','#skF_2')),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_240])).

tff(c_296,plain,
    ( ~ v5_relat_1(k7_relat_1('#skF_4','#skF_2'),'#skF_3')
    | ~ v1_relat_1(k7_relat_1('#skF_4','#skF_2')) ),
    inference(resolution,[status(thm)],[c_8,c_292])).

tff(c_299,plain,(
    ~ v5_relat_1(k7_relat_1('#skF_4','#skF_2'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_296])).

tff(c_308,plain,
    ( ~ v5_relat_1('#skF_4','#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_16,c_299])).

tff(c_312,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_37,c_42,c_308])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 15:11:42 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.37/1.33  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.37/1.33  
% 2.37/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.37/1.34  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k5_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.37/1.34  
% 2.37/1.34  %Foreground sorts:
% 2.37/1.34  
% 2.37/1.34  
% 2.37/1.34  %Background operators:
% 2.37/1.34  
% 2.37/1.34  
% 2.37/1.34  %Foreground operators:
% 2.37/1.34  tff(k5_relset_1, type, k5_relset_1: ($i * $i * $i * $i) > $i).
% 2.37/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.37/1.34  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.37/1.34  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.37/1.34  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.37/1.34  tff('#skF_2', type, '#skF_2': $i).
% 2.37/1.34  tff('#skF_3', type, '#skF_3': $i).
% 2.37/1.34  tff('#skF_1', type, '#skF_1': $i).
% 2.37/1.34  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.37/1.34  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.37/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.37/1.34  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.37/1.34  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.37/1.34  tff('#skF_4', type, '#skF_4': $i).
% 2.37/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.37/1.34  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.37/1.34  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.37/1.34  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.37/1.34  
% 2.37/1.35  tff(f_82, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C))) => m1_subset_1(k5_relset_1(A, C, D, B), k1_zfmisc_1(k2_zfmisc_1(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t33_relset_1)).
% 2.37/1.35  tff(f_59, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.37/1.35  tff(f_65, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.37/1.35  tff(f_55, axiom, (![A, B, C]: ((v1_relat_1(C) & v5_relat_1(C, B)) => (v1_relat_1(k7_relat_1(C, A)) & v5_relat_1(k7_relat_1(C, A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc22_relat_1)).
% 2.37/1.35  tff(f_37, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 2.37/1.35  tff(f_47, axiom, (![A, B, C]: ((v1_relat_1(C) & v4_relat_1(C, B)) => ((v1_relat_1(k7_relat_1(C, A)) & v4_relat_1(k7_relat_1(C, A), A)) & v4_relat_1(k7_relat_1(C, A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc23_relat_1)).
% 2.37/1.35  tff(f_31, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 2.37/1.35  tff(f_77, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_relset_1)).
% 2.37/1.35  tff(f_69, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k5_relset_1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k5_relset_1)).
% 2.37/1.35  tff(c_32, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.37/1.35  tff(c_33, plain, (![C_24, A_25, B_26]: (v1_relat_1(C_24) | ~m1_subset_1(C_24, k1_zfmisc_1(k2_zfmisc_1(A_25, B_26))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.37/1.35  tff(c_37, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_32, c_33])).
% 2.37/1.35  tff(c_38, plain, (![C_27, B_28, A_29]: (v5_relat_1(C_27, B_28) | ~m1_subset_1(C_27, k1_zfmisc_1(k2_zfmisc_1(A_29, B_28))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.37/1.35  tff(c_42, plain, (v5_relat_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_32, c_38])).
% 2.37/1.35  tff(c_16, plain, (![C_10, A_8, B_9]: (v5_relat_1(k7_relat_1(C_10, A_8), B_9) | ~v5_relat_1(C_10, B_9) | ~v1_relat_1(C_10))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.37/1.35  tff(c_50, plain, (![C_36, A_37, B_38]: (v1_relat_1(k7_relat_1(C_36, A_37)) | ~v5_relat_1(C_36, B_38) | ~v1_relat_1(C_36))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.37/1.35  tff(c_52, plain, (![A_37]: (v1_relat_1(k7_relat_1('#skF_4', A_37)) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_42, c_50])).
% 2.37/1.35  tff(c_55, plain, (![A_37]: (v1_relat_1(k7_relat_1('#skF_4', A_37)))), inference(demodulation, [status(thm), theory('equality')], [c_37, c_52])).
% 2.37/1.35  tff(c_8, plain, (![B_4, A_3]: (r1_tarski(k2_relat_1(B_4), A_3) | ~v5_relat_1(B_4, A_3) | ~v1_relat_1(B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.37/1.35  tff(c_63, plain, (![C_45, A_46, B_47]: (v4_relat_1(C_45, A_46) | ~m1_subset_1(C_45, k1_zfmisc_1(k2_zfmisc_1(A_46, B_47))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.37/1.35  tff(c_67, plain, (v4_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_32, c_63])).
% 2.37/1.35  tff(c_81, plain, (![C_54, A_55, B_56]: (v4_relat_1(k7_relat_1(C_54, A_55), A_55) | ~v4_relat_1(C_54, B_56) | ~v1_relat_1(C_54))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.37/1.35  tff(c_85, plain, (![A_55]: (v4_relat_1(k7_relat_1('#skF_4', A_55), A_55) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_67, c_81])).
% 2.37/1.35  tff(c_89, plain, (![A_55]: (v4_relat_1(k7_relat_1('#skF_4', A_55), A_55))), inference(demodulation, [status(thm), theory('equality')], [c_37, c_85])).
% 2.37/1.35  tff(c_4, plain, (![B_2, A_1]: (r1_tarski(k1_relat_1(B_2), A_1) | ~v4_relat_1(B_2, A_1) | ~v1_relat_1(B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.37/1.35  tff(c_223, plain, (![C_111, A_112, B_113]: (m1_subset_1(C_111, k1_zfmisc_1(k2_zfmisc_1(A_112, B_113))) | ~r1_tarski(k2_relat_1(C_111), B_113) | ~r1_tarski(k1_relat_1(C_111), A_112) | ~v1_relat_1(C_111))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.37/1.35  tff(c_137, plain, (![A_76, B_77, C_78, D_79]: (k5_relset_1(A_76, B_77, C_78, D_79)=k7_relat_1(C_78, D_79) | ~m1_subset_1(C_78, k1_zfmisc_1(k2_zfmisc_1(A_76, B_77))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.37/1.35  tff(c_140, plain, (![D_79]: (k5_relset_1('#skF_1', '#skF_3', '#skF_4', D_79)=k7_relat_1('#skF_4', D_79))), inference(resolution, [status(thm)], [c_32, c_137])).
% 2.37/1.35  tff(c_30, plain, (~m1_subset_1(k5_relset_1('#skF_1', '#skF_3', '#skF_4', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.37/1.35  tff(c_141, plain, (~m1_subset_1(k7_relat_1('#skF_4', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_140, c_30])).
% 2.37/1.35  tff(c_226, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', '#skF_2')), '#skF_3') | ~r1_tarski(k1_relat_1(k7_relat_1('#skF_4', '#skF_2')), '#skF_2') | ~v1_relat_1(k7_relat_1('#skF_4', '#skF_2'))), inference(resolution, [status(thm)], [c_223, c_141])).
% 2.37/1.35  tff(c_240, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', '#skF_2')), '#skF_3') | ~r1_tarski(k1_relat_1(k7_relat_1('#skF_4', '#skF_2')), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_55, c_226])).
% 2.37/1.35  tff(c_284, plain, (~r1_tarski(k1_relat_1(k7_relat_1('#skF_4', '#skF_2')), '#skF_2')), inference(splitLeft, [status(thm)], [c_240])).
% 2.37/1.35  tff(c_287, plain, (~v4_relat_1(k7_relat_1('#skF_4', '#skF_2'), '#skF_2') | ~v1_relat_1(k7_relat_1('#skF_4', '#skF_2'))), inference(resolution, [status(thm)], [c_4, c_284])).
% 2.37/1.35  tff(c_291, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_55, c_89, c_287])).
% 2.37/1.35  tff(c_292, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', '#skF_2')), '#skF_3')), inference(splitRight, [status(thm)], [c_240])).
% 2.37/1.35  tff(c_296, plain, (~v5_relat_1(k7_relat_1('#skF_4', '#skF_2'), '#skF_3') | ~v1_relat_1(k7_relat_1('#skF_4', '#skF_2'))), inference(resolution, [status(thm)], [c_8, c_292])).
% 2.37/1.35  tff(c_299, plain, (~v5_relat_1(k7_relat_1('#skF_4', '#skF_2'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_55, c_296])).
% 2.37/1.35  tff(c_308, plain, (~v5_relat_1('#skF_4', '#skF_3') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_16, c_299])).
% 2.37/1.35  tff(c_312, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_37, c_42, c_308])).
% 2.37/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.37/1.35  
% 2.37/1.35  Inference rules
% 2.37/1.35  ----------------------
% 2.37/1.35  #Ref     : 0
% 2.37/1.35  #Sup     : 53
% 2.37/1.35  #Fact    : 0
% 2.37/1.35  #Define  : 0
% 2.37/1.35  #Split   : 1
% 2.37/1.35  #Chain   : 0
% 2.37/1.35  #Close   : 0
% 2.37/1.35  
% 2.37/1.35  Ordering : KBO
% 2.37/1.35  
% 2.37/1.35  Simplification rules
% 2.37/1.35  ----------------------
% 2.37/1.35  #Subsume      : 2
% 2.37/1.35  #Demod        : 64
% 2.37/1.35  #Tautology    : 18
% 2.37/1.35  #SimpNegUnit  : 0
% 2.37/1.35  #BackRed      : 1
% 2.37/1.35  
% 2.37/1.35  #Partial instantiations: 0
% 2.37/1.35  #Strategies tried      : 1
% 2.37/1.35  
% 2.37/1.35  Timing (in seconds)
% 2.37/1.35  ----------------------
% 2.37/1.35  Preprocessing        : 0.32
% 2.37/1.35  Parsing              : 0.17
% 2.37/1.35  CNF conversion       : 0.02
% 2.37/1.35  Main loop            : 0.22
% 2.37/1.35  Inferencing          : 0.08
% 2.37/1.35  Reduction            : 0.08
% 2.37/1.35  Demodulation         : 0.06
% 2.37/1.36  BG Simplification    : 0.01
% 2.37/1.36  Subsumption          : 0.04
% 2.37/1.36  Abstraction          : 0.01
% 2.37/1.36  MUC search           : 0.00
% 2.37/1.36  Cooper               : 0.00
% 2.37/1.36  Total                : 0.58
% 2.37/1.36  Index Insertion      : 0.00
% 2.37/1.36  Index Deletion       : 0.00
% 2.37/1.36  Index Matching       : 0.00
% 2.37/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
