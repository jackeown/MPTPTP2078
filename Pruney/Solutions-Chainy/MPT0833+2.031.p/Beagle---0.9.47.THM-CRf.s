%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:49 EST 2020

% Result     : Theorem 2.39s
% Output     : CNFRefutation 2.68s
% Verified   : 
% Statistics : Number of formulae       :   55 (  75 expanded)
%              Number of leaves         :   27 (  37 expanded)
%              Depth                    :   10
%              Number of atoms          :   77 ( 118 expanded)
%              Number of equality atoms :    8 (   8 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k6_relset_1 > k8_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k6_relset_1,type,(
    k6_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_88,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B)))
       => ( r1_tarski(B,C)
         => r2_relset_1(A,B,k6_relset_1(A,B,C,D),D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_relset_1)).

tff(f_81,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_50,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_48,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_69,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

tff(f_58,axiom,(
    ! [A,B] : r1_tarski(k2_relat_1(k2_zfmisc_1(A,B)),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t194_relat_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k8_relat_1(A,B) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_relat_1)).

tff(f_73,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k6_relset_1(A,B,C,D) = k8_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_relset_1)).

tff(c_34,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_265,plain,(
    ! [A_79,B_80,D_81] :
      ( r2_relset_1(A_79,B_80,D_81,D_81)
      | ~ m1_subset_1(D_81,k1_zfmisc_1(k2_zfmisc_1(A_79,B_80))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_272,plain,(
    r2_relset_1('#skF_1','#skF_2','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_34,c_265])).

tff(c_14,plain,(
    ! [A_12,B_13] : v1_relat_1(k2_zfmisc_1(A_12,B_13)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_47,plain,(
    ! [B_37,A_38] :
      ( v1_relat_1(B_37)
      | ~ m1_subset_1(B_37,k1_zfmisc_1(A_38))
      | ~ v1_relat_1(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_53,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_34,c_47])).

tff(c_57,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_53])).

tff(c_38,plain,(
    ! [A_35,B_36] :
      ( r1_tarski(A_35,B_36)
      | ~ m1_subset_1(A_35,k1_zfmisc_1(B_36)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_46,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_34,c_38])).

tff(c_330,plain,(
    ! [A_92,B_93] :
      ( r1_tarski(k2_relat_1(A_92),k2_relat_1(B_93))
      | ~ r1_tarski(A_92,B_93)
      | ~ v1_relat_1(B_93)
      | ~ v1_relat_1(A_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_18,plain,(
    ! [A_16,B_17] : r1_tarski(k2_relat_1(k2_zfmisc_1(A_16,B_17)),B_17) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_75,plain,(
    ! [A_43,C_44,B_45] :
      ( r1_tarski(A_43,C_44)
      | ~ r1_tarski(B_45,C_44)
      | ~ r1_tarski(A_43,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_83,plain,(
    ! [A_43,B_17,A_16] :
      ( r1_tarski(A_43,B_17)
      | ~ r1_tarski(A_43,k2_relat_1(k2_zfmisc_1(A_16,B_17))) ) ),
    inference(resolution,[status(thm)],[c_18,c_75])).

tff(c_339,plain,(
    ! [A_92,B_17,A_16] :
      ( r1_tarski(k2_relat_1(A_92),B_17)
      | ~ r1_tarski(A_92,k2_zfmisc_1(A_16,B_17))
      | ~ v1_relat_1(k2_zfmisc_1(A_16,B_17))
      | ~ v1_relat_1(A_92) ) ),
    inference(resolution,[status(thm)],[c_330,c_83])).

tff(c_359,plain,(
    ! [A_94,B_95,A_96] :
      ( r1_tarski(k2_relat_1(A_94),B_95)
      | ~ r1_tarski(A_94,k2_zfmisc_1(A_96,B_95))
      | ~ v1_relat_1(A_94) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_339])).

tff(c_372,plain,
    ( r1_tarski(k2_relat_1('#skF_4'),'#skF_2')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_359])).

tff(c_387,plain,(
    r1_tarski(k2_relat_1('#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_372])).

tff(c_32,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_84,plain,(
    ! [A_43] :
      ( r1_tarski(A_43,'#skF_3')
      | ~ r1_tarski(A_43,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_32,c_75])).

tff(c_414,plain,(
    r1_tarski(k2_relat_1('#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_387,c_84])).

tff(c_16,plain,(
    ! [A_14,B_15] :
      ( k8_relat_1(A_14,B_15) = B_15
      | ~ r1_tarski(k2_relat_1(B_15),A_14)
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_425,plain,
    ( k8_relat_1('#skF_3','#skF_4') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_414,c_16])).

tff(c_434,plain,(
    k8_relat_1('#skF_3','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_425])).

tff(c_389,plain,(
    ! [A_97,B_98,C_99,D_100] :
      ( k6_relset_1(A_97,B_98,C_99,D_100) = k8_relat_1(C_99,D_100)
      | ~ m1_subset_1(D_100,k1_zfmisc_1(k2_zfmisc_1(A_97,B_98))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_396,plain,(
    ! [C_99] : k6_relset_1('#skF_1','#skF_2',C_99,'#skF_4') = k8_relat_1(C_99,'#skF_4') ),
    inference(resolution,[status(thm)],[c_34,c_389])).

tff(c_30,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k6_relset_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_437,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k8_relat_1('#skF_3','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_396,c_30])).

tff(c_453,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_272,c_434,c_437])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n022.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 15:20:55 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.39/1.31  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.39/1.31  
% 2.39/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.39/1.31  %$ r2_relset_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k6_relset_1 > k8_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.39/1.31  
% 2.39/1.31  %Foreground sorts:
% 2.39/1.31  
% 2.39/1.31  
% 2.39/1.31  %Background operators:
% 2.39/1.31  
% 2.39/1.31  
% 2.39/1.31  %Foreground operators:
% 2.39/1.31  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 2.39/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.39/1.31  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 2.39/1.31  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.39/1.31  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.39/1.31  tff(k6_relset_1, type, k6_relset_1: ($i * $i * $i * $i) > $i).
% 2.39/1.31  tff('#skF_2', type, '#skF_2': $i).
% 2.39/1.31  tff('#skF_3', type, '#skF_3': $i).
% 2.39/1.31  tff('#skF_1', type, '#skF_1': $i).
% 2.39/1.31  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.39/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.39/1.31  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.39/1.31  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.39/1.31  tff('#skF_4', type, '#skF_4': $i).
% 2.39/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.39/1.31  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.39/1.31  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.39/1.31  
% 2.68/1.33  tff(f_88, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (r1_tarski(B, C) => r2_relset_1(A, B, k6_relset_1(A, B, C, D), D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_relset_1)).
% 2.68/1.33  tff(f_81, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 2.68/1.33  tff(f_50, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.68/1.33  tff(f_48, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.68/1.33  tff(f_41, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.68/1.33  tff(f_69, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_relat_1)).
% 2.68/1.33  tff(f_58, axiom, (![A, B]: r1_tarski(k2_relat_1(k2_zfmisc_1(A, B)), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t194_relat_1)).
% 2.68/1.33  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 2.68/1.33  tff(f_56, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k8_relat_1(A, B) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t125_relat_1)).
% 2.68/1.33  tff(f_73, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k6_relset_1(A, B, C, D) = k8_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_relset_1)).
% 2.68/1.33  tff(c_34, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.68/1.33  tff(c_265, plain, (![A_79, B_80, D_81]: (r2_relset_1(A_79, B_80, D_81, D_81) | ~m1_subset_1(D_81, k1_zfmisc_1(k2_zfmisc_1(A_79, B_80))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.68/1.33  tff(c_272, plain, (r2_relset_1('#skF_1', '#skF_2', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_34, c_265])).
% 2.68/1.33  tff(c_14, plain, (![A_12, B_13]: (v1_relat_1(k2_zfmisc_1(A_12, B_13)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.68/1.33  tff(c_47, plain, (![B_37, A_38]: (v1_relat_1(B_37) | ~m1_subset_1(B_37, k1_zfmisc_1(A_38)) | ~v1_relat_1(A_38))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.68/1.33  tff(c_53, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_34, c_47])).
% 2.68/1.33  tff(c_57, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_53])).
% 2.68/1.33  tff(c_38, plain, (![A_35, B_36]: (r1_tarski(A_35, B_36) | ~m1_subset_1(A_35, k1_zfmisc_1(B_36)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.68/1.33  tff(c_46, plain, (r1_tarski('#skF_4', k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_34, c_38])).
% 2.68/1.33  tff(c_330, plain, (![A_92, B_93]: (r1_tarski(k2_relat_1(A_92), k2_relat_1(B_93)) | ~r1_tarski(A_92, B_93) | ~v1_relat_1(B_93) | ~v1_relat_1(A_92))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.68/1.33  tff(c_18, plain, (![A_16, B_17]: (r1_tarski(k2_relat_1(k2_zfmisc_1(A_16, B_17)), B_17))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.68/1.33  tff(c_75, plain, (![A_43, C_44, B_45]: (r1_tarski(A_43, C_44) | ~r1_tarski(B_45, C_44) | ~r1_tarski(A_43, B_45))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.68/1.33  tff(c_83, plain, (![A_43, B_17, A_16]: (r1_tarski(A_43, B_17) | ~r1_tarski(A_43, k2_relat_1(k2_zfmisc_1(A_16, B_17))))), inference(resolution, [status(thm)], [c_18, c_75])).
% 2.68/1.33  tff(c_339, plain, (![A_92, B_17, A_16]: (r1_tarski(k2_relat_1(A_92), B_17) | ~r1_tarski(A_92, k2_zfmisc_1(A_16, B_17)) | ~v1_relat_1(k2_zfmisc_1(A_16, B_17)) | ~v1_relat_1(A_92))), inference(resolution, [status(thm)], [c_330, c_83])).
% 2.68/1.33  tff(c_359, plain, (![A_94, B_95, A_96]: (r1_tarski(k2_relat_1(A_94), B_95) | ~r1_tarski(A_94, k2_zfmisc_1(A_96, B_95)) | ~v1_relat_1(A_94))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_339])).
% 2.68/1.33  tff(c_372, plain, (r1_tarski(k2_relat_1('#skF_4'), '#skF_2') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_46, c_359])).
% 2.68/1.33  tff(c_387, plain, (r1_tarski(k2_relat_1('#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_57, c_372])).
% 2.68/1.33  tff(c_32, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.68/1.33  tff(c_84, plain, (![A_43]: (r1_tarski(A_43, '#skF_3') | ~r1_tarski(A_43, '#skF_2'))), inference(resolution, [status(thm)], [c_32, c_75])).
% 2.68/1.33  tff(c_414, plain, (r1_tarski(k2_relat_1('#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_387, c_84])).
% 2.68/1.33  tff(c_16, plain, (![A_14, B_15]: (k8_relat_1(A_14, B_15)=B_15 | ~r1_tarski(k2_relat_1(B_15), A_14) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.68/1.33  tff(c_425, plain, (k8_relat_1('#skF_3', '#skF_4')='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_414, c_16])).
% 2.68/1.33  tff(c_434, plain, (k8_relat_1('#skF_3', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_57, c_425])).
% 2.68/1.33  tff(c_389, plain, (![A_97, B_98, C_99, D_100]: (k6_relset_1(A_97, B_98, C_99, D_100)=k8_relat_1(C_99, D_100) | ~m1_subset_1(D_100, k1_zfmisc_1(k2_zfmisc_1(A_97, B_98))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.68/1.33  tff(c_396, plain, (![C_99]: (k6_relset_1('#skF_1', '#skF_2', C_99, '#skF_4')=k8_relat_1(C_99, '#skF_4'))), inference(resolution, [status(thm)], [c_34, c_389])).
% 2.68/1.33  tff(c_30, plain, (~r2_relset_1('#skF_1', '#skF_2', k6_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.68/1.33  tff(c_437, plain, (~r2_relset_1('#skF_1', '#skF_2', k8_relat_1('#skF_3', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_396, c_30])).
% 2.68/1.33  tff(c_453, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_272, c_434, c_437])).
% 2.68/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.68/1.33  
% 2.68/1.33  Inference rules
% 2.68/1.33  ----------------------
% 2.68/1.33  #Ref     : 0
% 2.68/1.33  #Sup     : 94
% 2.68/1.33  #Fact    : 0
% 2.68/1.33  #Define  : 0
% 2.68/1.33  #Split   : 3
% 2.68/1.33  #Chain   : 0
% 2.68/1.33  #Close   : 0
% 2.68/1.33  
% 2.68/1.33  Ordering : KBO
% 2.68/1.33  
% 2.68/1.33  Simplification rules
% 2.68/1.33  ----------------------
% 2.68/1.33  #Subsume      : 7
% 2.68/1.33  #Demod        : 28
% 2.68/1.33  #Tautology    : 18
% 2.68/1.33  #SimpNegUnit  : 0
% 2.68/1.33  #BackRed      : 1
% 2.68/1.33  
% 2.68/1.33  #Partial instantiations: 0
% 2.68/1.33  #Strategies tried      : 1
% 2.68/1.33  
% 2.68/1.33  Timing (in seconds)
% 2.68/1.33  ----------------------
% 2.68/1.33  Preprocessing        : 0.31
% 2.68/1.33  Parsing              : 0.16
% 2.68/1.33  CNF conversion       : 0.02
% 2.68/1.33  Main loop            : 0.27
% 2.68/1.33  Inferencing          : 0.10
% 2.68/1.33  Reduction            : 0.08
% 2.68/1.33  Demodulation         : 0.06
% 2.68/1.33  BG Simplification    : 0.01
% 2.68/1.33  Subsumption          : 0.05
% 2.68/1.33  Abstraction          : 0.02
% 2.68/1.33  MUC search           : 0.00
% 2.68/1.33  Cooper               : 0.00
% 2.68/1.33  Total                : 0.61
% 2.68/1.33  Index Insertion      : 0.00
% 2.68/1.33  Index Deletion       : 0.00
% 2.68/1.33  Index Matching       : 0.00
% 2.68/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
