%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:40 EST 2020

% Result     : Theorem 2.56s
% Output     : CNFRefutation 2.56s
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
%$ r2_relset_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k5_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A)))
       => ( r1_tarski(B,C)
         => r2_relset_1(B,A,k5_relset_1(B,A,D,C),D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_relset_1)).

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

tff(f_63,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

tff(f_52,axiom,(
    ! [A,B] : r1_tarski(k1_relat_1(k2_zfmisc_1(A,B)),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t193_relat_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_73,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k5_relset_1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_relset_1)).

tff(c_34,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_265,plain,(
    ! [A_79,B_80,D_81] :
      ( r2_relset_1(A_79,B_80,D_81,D_81)
      | ~ m1_subset_1(D_81,k1_zfmisc_1(k2_zfmisc_1(A_79,B_80))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_272,plain,(
    r2_relset_1('#skF_2','#skF_1','#skF_4','#skF_4') ),
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
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
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
    r1_tarski('#skF_4',k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_34,c_38])).

tff(c_319,plain,(
    ! [A_90,B_91] :
      ( r1_tarski(k1_relat_1(A_90),k1_relat_1(B_91))
      | ~ r1_tarski(A_90,B_91)
      | ~ v1_relat_1(B_91)
      | ~ v1_relat_1(A_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_16,plain,(
    ! [A_14,B_15] : r1_tarski(k1_relat_1(k2_zfmisc_1(A_14,B_15)),A_14) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_75,plain,(
    ! [A_43,C_44,B_45] :
      ( r1_tarski(A_43,C_44)
      | ~ r1_tarski(B_45,C_44)
      | ~ r1_tarski(A_43,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_83,plain,(
    ! [A_43,A_14,B_15] :
      ( r1_tarski(A_43,A_14)
      | ~ r1_tarski(A_43,k1_relat_1(k2_zfmisc_1(A_14,B_15))) ) ),
    inference(resolution,[status(thm)],[c_16,c_75])).

tff(c_328,plain,(
    ! [A_90,A_14,B_15] :
      ( r1_tarski(k1_relat_1(A_90),A_14)
      | ~ r1_tarski(A_90,k2_zfmisc_1(A_14,B_15))
      | ~ v1_relat_1(k2_zfmisc_1(A_14,B_15))
      | ~ v1_relat_1(A_90) ) ),
    inference(resolution,[status(thm)],[c_319,c_83])).

tff(c_348,plain,(
    ! [A_92,A_93,B_94] :
      ( r1_tarski(k1_relat_1(A_92),A_93)
      | ~ r1_tarski(A_92,k2_zfmisc_1(A_93,B_94))
      | ~ v1_relat_1(A_92) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_328])).

tff(c_361,plain,
    ( r1_tarski(k1_relat_1('#skF_4'),'#skF_2')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_348])).

tff(c_376,plain,(
    r1_tarski(k1_relat_1('#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_361])).

tff(c_32,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_84,plain,(
    ! [A_43] :
      ( r1_tarski(A_43,'#skF_3')
      | ~ r1_tarski(A_43,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_32,c_75])).

tff(c_395,plain,(
    r1_tarski(k1_relat_1('#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_376,c_84])).

tff(c_22,plain,(
    ! [B_20,A_19] :
      ( k7_relat_1(B_20,A_19) = B_20
      | ~ r1_tarski(k1_relat_1(B_20),A_19)
      | ~ v1_relat_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_417,plain,
    ( k7_relat_1('#skF_4','#skF_3') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_395,c_22])).

tff(c_426,plain,(
    k7_relat_1('#skF_4','#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_417])).

tff(c_508,plain,(
    ! [A_101,B_102,C_103,D_104] :
      ( k5_relset_1(A_101,B_102,C_103,D_104) = k7_relat_1(C_103,D_104)
      | ~ m1_subset_1(C_103,k1_zfmisc_1(k2_zfmisc_1(A_101,B_102))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_515,plain,(
    ! [D_104] : k5_relset_1('#skF_2','#skF_1','#skF_4',D_104) = k7_relat_1('#skF_4',D_104) ),
    inference(resolution,[status(thm)],[c_34,c_508])).

tff(c_30,plain,(
    ~ r2_relset_1('#skF_2','#skF_1',k5_relset_1('#skF_2','#skF_1','#skF_4','#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_517,plain,(
    ~ r2_relset_1('#skF_2','#skF_1',k7_relat_1('#skF_4','#skF_3'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_515,c_30])).

tff(c_520,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_272,c_426,c_517])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:03:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.56/1.39  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.56/1.39  
% 2.56/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.56/1.40  %$ r2_relset_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k5_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.56/1.40  
% 2.56/1.40  %Foreground sorts:
% 2.56/1.40  
% 2.56/1.40  
% 2.56/1.40  %Background operators:
% 2.56/1.40  
% 2.56/1.40  
% 2.56/1.40  %Foreground operators:
% 2.56/1.40  tff(k5_relset_1, type, k5_relset_1: ($i * $i * $i * $i) > $i).
% 2.56/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.56/1.40  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 2.56/1.40  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.56/1.40  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.56/1.40  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.56/1.40  tff('#skF_2', type, '#skF_2': $i).
% 2.56/1.40  tff('#skF_3', type, '#skF_3': $i).
% 2.56/1.40  tff('#skF_1', type, '#skF_1': $i).
% 2.56/1.40  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.56/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.56/1.40  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.56/1.40  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.56/1.40  tff('#skF_4', type, '#skF_4': $i).
% 2.56/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.56/1.40  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.56/1.40  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.56/1.40  
% 2.56/1.41  tff(f_88, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A))) => (r1_tarski(B, C) => r2_relset_1(B, A, k5_relset_1(B, A, D, C), D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_relset_1)).
% 2.56/1.41  tff(f_81, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 2.56/1.41  tff(f_50, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.56/1.41  tff(f_48, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.56/1.41  tff(f_41, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.56/1.41  tff(f_63, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_relat_1)).
% 2.56/1.41  tff(f_52, axiom, (![A, B]: r1_tarski(k1_relat_1(k2_zfmisc_1(A, B)), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t193_relat_1)).
% 2.56/1.41  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 2.56/1.41  tff(f_69, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_relat_1)).
% 2.56/1.41  tff(f_73, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k5_relset_1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k5_relset_1)).
% 2.56/1.41  tff(c_34, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.56/1.41  tff(c_265, plain, (![A_79, B_80, D_81]: (r2_relset_1(A_79, B_80, D_81, D_81) | ~m1_subset_1(D_81, k1_zfmisc_1(k2_zfmisc_1(A_79, B_80))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.56/1.41  tff(c_272, plain, (r2_relset_1('#skF_2', '#skF_1', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_34, c_265])).
% 2.56/1.41  tff(c_14, plain, (![A_12, B_13]: (v1_relat_1(k2_zfmisc_1(A_12, B_13)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.56/1.41  tff(c_47, plain, (![B_37, A_38]: (v1_relat_1(B_37) | ~m1_subset_1(B_37, k1_zfmisc_1(A_38)) | ~v1_relat_1(A_38))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.56/1.41  tff(c_53, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_34, c_47])).
% 2.56/1.41  tff(c_57, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_53])).
% 2.56/1.41  tff(c_38, plain, (![A_35, B_36]: (r1_tarski(A_35, B_36) | ~m1_subset_1(A_35, k1_zfmisc_1(B_36)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.56/1.41  tff(c_46, plain, (r1_tarski('#skF_4', k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_34, c_38])).
% 2.56/1.41  tff(c_319, plain, (![A_90, B_91]: (r1_tarski(k1_relat_1(A_90), k1_relat_1(B_91)) | ~r1_tarski(A_90, B_91) | ~v1_relat_1(B_91) | ~v1_relat_1(A_90))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.56/1.41  tff(c_16, plain, (![A_14, B_15]: (r1_tarski(k1_relat_1(k2_zfmisc_1(A_14, B_15)), A_14))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.56/1.41  tff(c_75, plain, (![A_43, C_44, B_45]: (r1_tarski(A_43, C_44) | ~r1_tarski(B_45, C_44) | ~r1_tarski(A_43, B_45))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.56/1.41  tff(c_83, plain, (![A_43, A_14, B_15]: (r1_tarski(A_43, A_14) | ~r1_tarski(A_43, k1_relat_1(k2_zfmisc_1(A_14, B_15))))), inference(resolution, [status(thm)], [c_16, c_75])).
% 2.56/1.41  tff(c_328, plain, (![A_90, A_14, B_15]: (r1_tarski(k1_relat_1(A_90), A_14) | ~r1_tarski(A_90, k2_zfmisc_1(A_14, B_15)) | ~v1_relat_1(k2_zfmisc_1(A_14, B_15)) | ~v1_relat_1(A_90))), inference(resolution, [status(thm)], [c_319, c_83])).
% 2.56/1.41  tff(c_348, plain, (![A_92, A_93, B_94]: (r1_tarski(k1_relat_1(A_92), A_93) | ~r1_tarski(A_92, k2_zfmisc_1(A_93, B_94)) | ~v1_relat_1(A_92))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_328])).
% 2.56/1.41  tff(c_361, plain, (r1_tarski(k1_relat_1('#skF_4'), '#skF_2') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_46, c_348])).
% 2.56/1.41  tff(c_376, plain, (r1_tarski(k1_relat_1('#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_57, c_361])).
% 2.56/1.41  tff(c_32, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.56/1.41  tff(c_84, plain, (![A_43]: (r1_tarski(A_43, '#skF_3') | ~r1_tarski(A_43, '#skF_2'))), inference(resolution, [status(thm)], [c_32, c_75])).
% 2.56/1.41  tff(c_395, plain, (r1_tarski(k1_relat_1('#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_376, c_84])).
% 2.56/1.41  tff(c_22, plain, (![B_20, A_19]: (k7_relat_1(B_20, A_19)=B_20 | ~r1_tarski(k1_relat_1(B_20), A_19) | ~v1_relat_1(B_20))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.56/1.41  tff(c_417, plain, (k7_relat_1('#skF_4', '#skF_3')='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_395, c_22])).
% 2.56/1.41  tff(c_426, plain, (k7_relat_1('#skF_4', '#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_57, c_417])).
% 2.56/1.41  tff(c_508, plain, (![A_101, B_102, C_103, D_104]: (k5_relset_1(A_101, B_102, C_103, D_104)=k7_relat_1(C_103, D_104) | ~m1_subset_1(C_103, k1_zfmisc_1(k2_zfmisc_1(A_101, B_102))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.56/1.41  tff(c_515, plain, (![D_104]: (k5_relset_1('#skF_2', '#skF_1', '#skF_4', D_104)=k7_relat_1('#skF_4', D_104))), inference(resolution, [status(thm)], [c_34, c_508])).
% 2.56/1.41  tff(c_30, plain, (~r2_relset_1('#skF_2', '#skF_1', k5_relset_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.56/1.41  tff(c_517, plain, (~r2_relset_1('#skF_2', '#skF_1', k7_relat_1('#skF_4', '#skF_3'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_515, c_30])).
% 2.56/1.41  tff(c_520, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_272, c_426, c_517])).
% 2.56/1.41  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.56/1.41  
% 2.56/1.41  Inference rules
% 2.56/1.41  ----------------------
% 2.56/1.41  #Ref     : 0
% 2.56/1.41  #Sup     : 107
% 2.56/1.41  #Fact    : 0
% 2.56/1.41  #Define  : 0
% 2.56/1.41  #Split   : 3
% 2.56/1.41  #Chain   : 0
% 2.56/1.41  #Close   : 0
% 2.56/1.41  
% 2.56/1.41  Ordering : KBO
% 2.56/1.41  
% 2.56/1.41  Simplification rules
% 2.56/1.41  ----------------------
% 2.56/1.41  #Subsume      : 10
% 2.56/1.41  #Demod        : 33
% 2.56/1.41  #Tautology    : 17
% 2.56/1.41  #SimpNegUnit  : 0
% 2.56/1.41  #BackRed      : 1
% 2.56/1.41  
% 2.56/1.41  #Partial instantiations: 0
% 2.56/1.41  #Strategies tried      : 1
% 2.56/1.41  
% 2.56/1.41  Timing (in seconds)
% 2.56/1.41  ----------------------
% 2.56/1.41  Preprocessing        : 0.31
% 2.56/1.41  Parsing              : 0.17
% 2.56/1.41  CNF conversion       : 0.02
% 2.56/1.41  Main loop            : 0.28
% 2.56/1.41  Inferencing          : 0.10
% 2.56/1.41  Reduction            : 0.09
% 2.56/1.41  Demodulation         : 0.06
% 2.56/1.41  BG Simplification    : 0.02
% 2.56/1.41  Subsumption          : 0.06
% 2.56/1.41  Abstraction          : 0.02
% 2.56/1.41  MUC search           : 0.00
% 2.56/1.41  Cooper               : 0.00
% 2.56/1.41  Total                : 0.62
% 2.56/1.41  Index Insertion      : 0.00
% 2.56/1.41  Index Deletion       : 0.00
% 2.56/1.41  Index Matching       : 0.00
% 2.56/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
