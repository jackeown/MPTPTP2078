%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:48 EST 2020

% Result     : Theorem 2.38s
% Output     : CNFRefutation 2.66s
% Verified   : 
% Statistics : Number of formulae       :   61 (  84 expanded)
%              Number of leaves         :   29 (  41 expanded)
%              Depth                    :   10
%              Number of atoms          :   89 ( 153 expanded)
%              Number of equality atoms :    9 (   9 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_partfun1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

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

tff(k2_partfun1,type,(
    k2_partfun1: ( $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_44,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_86,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( r1_tarski(A,C)
         => r2_relset_1(A,B,k2_partfun1(A,B,D,C),D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_funct_2)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_57,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

tff(f_46,axiom,(
    ! [A,B] : r1_tarski(k1_relat_1(k2_zfmisc_1(A,B)),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t193_relat_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_75,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_69,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_relset_1(A,B,C,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

tff(c_10,plain,(
    ! [A_9,B_10] : v1_relat_1(k2_zfmisc_1(A_9,B_10)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_28,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_45,plain,(
    ! [B_34,A_35] :
      ( v1_relat_1(B_34)
      | ~ m1_subset_1(B_34,k1_zfmisc_1(A_35))
      | ~ v1_relat_1(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_51,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_28,c_45])).

tff(c_55,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_51])).

tff(c_36,plain,(
    ! [A_32,B_33] :
      ( r1_tarski(A_32,B_33)
      | ~ m1_subset_1(A_32,k1_zfmisc_1(B_33)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_44,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_28,c_36])).

tff(c_337,plain,(
    ! [A_81,B_82] :
      ( r1_tarski(k1_relat_1(A_81),k1_relat_1(B_82))
      | ~ r1_tarski(A_81,B_82)
      | ~ v1_relat_1(B_82)
      | ~ v1_relat_1(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_12,plain,(
    ! [A_11,B_12] : r1_tarski(k1_relat_1(k2_zfmisc_1(A_11,B_12)),A_11) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_72,plain,(
    ! [A_38,C_39,B_40] :
      ( r1_tarski(A_38,C_39)
      | ~ r1_tarski(B_40,C_39)
      | ~ r1_tarski(A_38,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_80,plain,(
    ! [A_38,A_11,B_12] :
      ( r1_tarski(A_38,A_11)
      | ~ r1_tarski(A_38,k1_relat_1(k2_zfmisc_1(A_11,B_12))) ) ),
    inference(resolution,[status(thm)],[c_12,c_72])).

tff(c_346,plain,(
    ! [A_81,A_11,B_12] :
      ( r1_tarski(k1_relat_1(A_81),A_11)
      | ~ r1_tarski(A_81,k2_zfmisc_1(A_11,B_12))
      | ~ v1_relat_1(k2_zfmisc_1(A_11,B_12))
      | ~ v1_relat_1(A_81) ) ),
    inference(resolution,[status(thm)],[c_337,c_80])).

tff(c_362,plain,(
    ! [A_83,A_84,B_85] :
      ( r1_tarski(k1_relat_1(A_83),A_84)
      | ~ r1_tarski(A_83,k2_zfmisc_1(A_84,B_85))
      | ~ v1_relat_1(A_83) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_346])).

tff(c_371,plain,
    ( r1_tarski(k1_relat_1('#skF_4'),'#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_362])).

tff(c_380,plain,(
    r1_tarski(k1_relat_1('#skF_4'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_371])).

tff(c_26,plain,(
    r1_tarski('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_81,plain,(
    ! [A_38] :
      ( r1_tarski(A_38,'#skF_3')
      | ~ r1_tarski(A_38,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_26,c_72])).

tff(c_132,plain,(
    ! [B_52,A_53] :
      ( k7_relat_1(B_52,A_53) = B_52
      | ~ r1_tarski(k1_relat_1(B_52),A_53)
      | ~ v1_relat_1(B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_145,plain,(
    ! [B_52] :
      ( k7_relat_1(B_52,'#skF_3') = B_52
      | ~ v1_relat_1(B_52)
      | ~ r1_tarski(k1_relat_1(B_52),'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_81,c_132])).

tff(c_396,plain,
    ( k7_relat_1('#skF_4','#skF_3') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_380,c_145])).

tff(c_410,plain,(
    k7_relat_1('#skF_4','#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_396])).

tff(c_32,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_382,plain,(
    ! [A_86,B_87,C_88,D_89] :
      ( k2_partfun1(A_86,B_87,C_88,D_89) = k7_relat_1(C_88,D_89)
      | ~ m1_subset_1(C_88,k1_zfmisc_1(k2_zfmisc_1(A_86,B_87)))
      | ~ v1_funct_1(C_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_387,plain,(
    ! [D_89] :
      ( k2_partfun1('#skF_1','#skF_2','#skF_4',D_89) = k7_relat_1('#skF_4',D_89)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_28,c_382])).

tff(c_391,plain,(
    ! [D_89] : k2_partfun1('#skF_1','#skF_2','#skF_4',D_89) = k7_relat_1('#skF_4',D_89) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_387])).

tff(c_24,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_425,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k7_relat_1('#skF_4','#skF_3'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_391,c_24])).

tff(c_426,plain,(
    ~ r2_relset_1('#skF_1','#skF_2','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_410,c_425])).

tff(c_438,plain,(
    ! [A_91,B_92,C_93,D_94] :
      ( r2_relset_1(A_91,B_92,C_93,C_93)
      | ~ m1_subset_1(D_94,k1_zfmisc_1(k2_zfmisc_1(A_91,B_92)))
      | ~ m1_subset_1(C_93,k1_zfmisc_1(k2_zfmisc_1(A_91,B_92))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_512,plain,(
    ! [C_98] :
      ( r2_relset_1('#skF_1','#skF_2',C_98,C_98)
      | ~ m1_subset_1(C_98,k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_28,c_438])).

tff(c_517,plain,(
    r2_relset_1('#skF_1','#skF_2','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_512])).

tff(c_522,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_426,c_517])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:53:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.38/1.41  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.38/1.41  
% 2.38/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.38/1.41  %$ r2_relset_1 > v1_funct_2 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_partfun1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.38/1.41  
% 2.38/1.41  %Foreground sorts:
% 2.38/1.41  
% 2.38/1.41  
% 2.38/1.41  %Background operators:
% 2.38/1.41  
% 2.38/1.41  
% 2.38/1.41  %Foreground operators:
% 2.38/1.41  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.38/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.38/1.41  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 2.38/1.41  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.38/1.41  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.38/1.41  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.38/1.41  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.38/1.41  tff('#skF_2', type, '#skF_2': $i).
% 2.38/1.41  tff('#skF_3', type, '#skF_3': $i).
% 2.38/1.41  tff('#skF_1', type, '#skF_1': $i).
% 2.38/1.41  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.38/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.38/1.41  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.38/1.41  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.38/1.41  tff('#skF_4', type, '#skF_4': $i).
% 2.38/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.38/1.41  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 2.38/1.41  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.38/1.41  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.38/1.41  
% 2.66/1.43  tff(f_44, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.66/1.43  tff(f_86, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(A, C) => r2_relset_1(A, B, k2_partfun1(A, B, D, C), D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_funct_2)).
% 2.66/1.43  tff(f_42, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.66/1.43  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.66/1.43  tff(f_57, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_relat_1)).
% 2.66/1.43  tff(f_46, axiom, (![A, B]: r1_tarski(k1_relat_1(k2_zfmisc_1(A, B)), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t193_relat_1)).
% 2.66/1.43  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 2.66/1.43  tff(f_63, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_relat_1)).
% 2.66/1.43  tff(f_75, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 2.66/1.43  tff(f_69, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_relset_1(A, B, C, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', reflexivity_r2_relset_1)).
% 2.66/1.43  tff(c_10, plain, (![A_9, B_10]: (v1_relat_1(k2_zfmisc_1(A_9, B_10)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.66/1.43  tff(c_28, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.66/1.43  tff(c_45, plain, (![B_34, A_35]: (v1_relat_1(B_34) | ~m1_subset_1(B_34, k1_zfmisc_1(A_35)) | ~v1_relat_1(A_35))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.66/1.43  tff(c_51, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_28, c_45])).
% 2.66/1.43  tff(c_55, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_51])).
% 2.66/1.43  tff(c_36, plain, (![A_32, B_33]: (r1_tarski(A_32, B_33) | ~m1_subset_1(A_32, k1_zfmisc_1(B_33)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.66/1.43  tff(c_44, plain, (r1_tarski('#skF_4', k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_28, c_36])).
% 2.66/1.43  tff(c_337, plain, (![A_81, B_82]: (r1_tarski(k1_relat_1(A_81), k1_relat_1(B_82)) | ~r1_tarski(A_81, B_82) | ~v1_relat_1(B_82) | ~v1_relat_1(A_81))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.66/1.43  tff(c_12, plain, (![A_11, B_12]: (r1_tarski(k1_relat_1(k2_zfmisc_1(A_11, B_12)), A_11))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.66/1.43  tff(c_72, plain, (![A_38, C_39, B_40]: (r1_tarski(A_38, C_39) | ~r1_tarski(B_40, C_39) | ~r1_tarski(A_38, B_40))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.66/1.43  tff(c_80, plain, (![A_38, A_11, B_12]: (r1_tarski(A_38, A_11) | ~r1_tarski(A_38, k1_relat_1(k2_zfmisc_1(A_11, B_12))))), inference(resolution, [status(thm)], [c_12, c_72])).
% 2.66/1.43  tff(c_346, plain, (![A_81, A_11, B_12]: (r1_tarski(k1_relat_1(A_81), A_11) | ~r1_tarski(A_81, k2_zfmisc_1(A_11, B_12)) | ~v1_relat_1(k2_zfmisc_1(A_11, B_12)) | ~v1_relat_1(A_81))), inference(resolution, [status(thm)], [c_337, c_80])).
% 2.66/1.43  tff(c_362, plain, (![A_83, A_84, B_85]: (r1_tarski(k1_relat_1(A_83), A_84) | ~r1_tarski(A_83, k2_zfmisc_1(A_84, B_85)) | ~v1_relat_1(A_83))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_346])).
% 2.66/1.43  tff(c_371, plain, (r1_tarski(k1_relat_1('#skF_4'), '#skF_1') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_44, c_362])).
% 2.66/1.43  tff(c_380, plain, (r1_tarski(k1_relat_1('#skF_4'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_55, c_371])).
% 2.66/1.43  tff(c_26, plain, (r1_tarski('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.66/1.43  tff(c_81, plain, (![A_38]: (r1_tarski(A_38, '#skF_3') | ~r1_tarski(A_38, '#skF_1'))), inference(resolution, [status(thm)], [c_26, c_72])).
% 2.66/1.43  tff(c_132, plain, (![B_52, A_53]: (k7_relat_1(B_52, A_53)=B_52 | ~r1_tarski(k1_relat_1(B_52), A_53) | ~v1_relat_1(B_52))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.66/1.43  tff(c_145, plain, (![B_52]: (k7_relat_1(B_52, '#skF_3')=B_52 | ~v1_relat_1(B_52) | ~r1_tarski(k1_relat_1(B_52), '#skF_1'))), inference(resolution, [status(thm)], [c_81, c_132])).
% 2.66/1.43  tff(c_396, plain, (k7_relat_1('#skF_4', '#skF_3')='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_380, c_145])).
% 2.66/1.43  tff(c_410, plain, (k7_relat_1('#skF_4', '#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_55, c_396])).
% 2.66/1.43  tff(c_32, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.66/1.43  tff(c_382, plain, (![A_86, B_87, C_88, D_89]: (k2_partfun1(A_86, B_87, C_88, D_89)=k7_relat_1(C_88, D_89) | ~m1_subset_1(C_88, k1_zfmisc_1(k2_zfmisc_1(A_86, B_87))) | ~v1_funct_1(C_88))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.66/1.43  tff(c_387, plain, (![D_89]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_89)=k7_relat_1('#skF_4', D_89) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_28, c_382])).
% 2.66/1.43  tff(c_391, plain, (![D_89]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_89)=k7_relat_1('#skF_4', D_89))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_387])).
% 2.66/1.43  tff(c_24, plain, (~r2_relset_1('#skF_1', '#skF_2', k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.66/1.43  tff(c_425, plain, (~r2_relset_1('#skF_1', '#skF_2', k7_relat_1('#skF_4', '#skF_3'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_391, c_24])).
% 2.66/1.43  tff(c_426, plain, (~r2_relset_1('#skF_1', '#skF_2', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_410, c_425])).
% 2.66/1.43  tff(c_438, plain, (![A_91, B_92, C_93, D_94]: (r2_relset_1(A_91, B_92, C_93, C_93) | ~m1_subset_1(D_94, k1_zfmisc_1(k2_zfmisc_1(A_91, B_92))) | ~m1_subset_1(C_93, k1_zfmisc_1(k2_zfmisc_1(A_91, B_92))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.66/1.43  tff(c_512, plain, (![C_98]: (r2_relset_1('#skF_1', '#skF_2', C_98, C_98) | ~m1_subset_1(C_98, k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))))), inference(resolution, [status(thm)], [c_28, c_438])).
% 2.66/1.43  tff(c_517, plain, (r2_relset_1('#skF_1', '#skF_2', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_28, c_512])).
% 2.66/1.43  tff(c_522, plain, $false, inference(negUnitSimplification, [status(thm)], [c_426, c_517])).
% 2.66/1.43  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.66/1.43  
% 2.66/1.43  Inference rules
% 2.66/1.43  ----------------------
% 2.66/1.43  #Ref     : 0
% 2.66/1.43  #Sup     : 111
% 2.66/1.43  #Fact    : 0
% 2.66/1.43  #Define  : 0
% 2.66/1.43  #Split   : 5
% 2.66/1.43  #Chain   : 0
% 2.66/1.43  #Close   : 0
% 2.66/1.43  
% 2.66/1.43  Ordering : KBO
% 2.66/1.43  
% 2.66/1.43  Simplification rules
% 2.66/1.43  ----------------------
% 2.66/1.43  #Subsume      : 16
% 2.66/1.43  #Demod        : 24
% 2.66/1.43  #Tautology    : 20
% 2.66/1.43  #SimpNegUnit  : 1
% 2.66/1.43  #BackRed      : 1
% 2.66/1.43  
% 2.66/1.43  #Partial instantiations: 0
% 2.66/1.43  #Strategies tried      : 1
% 2.66/1.43  
% 2.66/1.43  Timing (in seconds)
% 2.66/1.43  ----------------------
% 2.66/1.43  Preprocessing        : 0.30
% 2.66/1.43  Parsing              : 0.17
% 2.66/1.43  CNF conversion       : 0.02
% 2.66/1.43  Main loop            : 0.30
% 2.66/1.43  Inferencing          : 0.11
% 2.66/1.43  Reduction            : 0.09
% 2.66/1.43  Demodulation         : 0.07
% 2.66/1.43  BG Simplification    : 0.02
% 2.66/1.43  Subsumption          : 0.06
% 2.66/1.43  Abstraction          : 0.02
% 2.66/1.43  MUC search           : 0.00
% 2.66/1.43  Cooper               : 0.00
% 2.66/1.43  Total                : 0.64
% 2.66/1.43  Index Insertion      : 0.00
% 2.66/1.43  Index Deletion       : 0.00
% 2.66/1.43  Index Matching       : 0.00
% 2.66/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
