%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:28 EST 2020

% Result     : Theorem 2.55s
% Output     : CNFRefutation 2.55s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 150 expanded)
%              Number of leaves         :   28 (  62 expanded)
%              Depth                    :   13
%              Number of atoms          :   85 ( 248 expanded)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_relset_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k7_relat_1(B,A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_relat_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_63,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k5_relset_1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_relset_1)).

tff(c_30,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_43,plain,(
    ! [C_37,A_38,B_39] :
      ( v1_relat_1(C_37)
      | ~ m1_subset_1(C_37,k1_zfmisc_1(k2_zfmisc_1(A_38,B_39))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_52,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_43])).

tff(c_14,plain,(
    ! [B_11,A_10] :
      ( r1_tarski(k7_relat_1(B_11,A_10),B_11)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_33,plain,(
    ! [A_33,B_34] :
      ( r1_tarski(A_33,B_34)
      | ~ m1_subset_1(A_33,k1_zfmisc_1(B_34)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_41,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_30,c_33])).

tff(c_73,plain,(
    ! [A_43,C_44,B_45] :
      ( r1_tarski(A_43,C_44)
      | ~ r1_tarski(B_45,C_44)
      | ~ r1_tarski(A_43,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_81,plain,(
    ! [A_43] :
      ( r1_tarski(A_43,k2_zfmisc_1('#skF_1','#skF_3'))
      | ~ r1_tarski(A_43,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_41,c_73])).

tff(c_6,plain,(
    ! [A_4,B_5] :
      ( m1_subset_1(A_4,k1_zfmisc_1(B_5))
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_106,plain,(
    ! [C_50,B_51,A_52] :
      ( v5_relat_1(C_50,B_51)
      | ~ m1_subset_1(C_50,k1_zfmisc_1(k2_zfmisc_1(A_52,B_51))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_116,plain,(
    ! [A_53,B_54,A_55] :
      ( v5_relat_1(A_53,B_54)
      | ~ r1_tarski(A_53,k2_zfmisc_1(A_55,B_54)) ) ),
    inference(resolution,[status(thm)],[c_6,c_106])).

tff(c_131,plain,(
    ! [A_43] :
      ( v5_relat_1(A_43,'#skF_3')
      | ~ r1_tarski(A_43,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_81,c_116])).

tff(c_83,plain,(
    ! [A_46] :
      ( r1_tarski(A_46,k2_zfmisc_1('#skF_1','#skF_3'))
      | ~ r1_tarski(A_46,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_41,c_73])).

tff(c_51,plain,(
    ! [A_4,A_38,B_39] :
      ( v1_relat_1(A_4)
      | ~ r1_tarski(A_4,k2_zfmisc_1(A_38,B_39)) ) ),
    inference(resolution,[status(thm)],[c_6,c_43])).

tff(c_91,plain,(
    ! [A_47] :
      ( v1_relat_1(A_47)
      | ~ r1_tarski(A_47,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_83,c_51])).

tff(c_99,plain,(
    ! [A_10] :
      ( v1_relat_1(k7_relat_1('#skF_4',A_10))
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_14,c_91])).

tff(c_103,plain,(
    ! [A_10] : v1_relat_1(k7_relat_1('#skF_4',A_10)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_99])).

tff(c_10,plain,(
    ! [B_7,A_6] :
      ( r1_tarski(k2_relat_1(B_7),A_6)
      | ~ v5_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_12,plain,(
    ! [B_9,A_8] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_9,A_8)),A_8)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_478,plain,(
    ! [C_138,A_139,B_140] :
      ( m1_subset_1(C_138,k1_zfmisc_1(k2_zfmisc_1(A_139,B_140)))
      | ~ r1_tarski(k2_relat_1(C_138),B_140)
      | ~ r1_tarski(k1_relat_1(C_138),A_139)
      | ~ v1_relat_1(C_138) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_250,plain,(
    ! [A_91,B_92,C_93,D_94] :
      ( k5_relset_1(A_91,B_92,C_93,D_94) = k7_relat_1(C_93,D_94)
      | ~ m1_subset_1(C_93,k1_zfmisc_1(k2_zfmisc_1(A_91,B_92))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_257,plain,(
    ! [D_94] : k5_relset_1('#skF_1','#skF_3','#skF_4',D_94) = k7_relat_1('#skF_4',D_94) ),
    inference(resolution,[status(thm)],[c_30,c_250])).

tff(c_28,plain,(
    ~ m1_subset_1(k5_relset_1('#skF_1','#skF_3','#skF_4','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_259,plain,(
    ~ m1_subset_1(k7_relat_1('#skF_4','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_257,c_28])).

tff(c_485,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4','#skF_2')),'#skF_3')
    | ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_4','#skF_2')),'#skF_2')
    | ~ v1_relat_1(k7_relat_1('#skF_4','#skF_2')) ),
    inference(resolution,[status(thm)],[c_478,c_259])).

tff(c_503,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4','#skF_2')),'#skF_3')
    | ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_4','#skF_2')),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_485])).

tff(c_518,plain,(
    ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_4','#skF_2')),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_503])).

tff(c_521,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_12,c_518])).

tff(c_525,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_521])).

tff(c_526,plain,(
    ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4','#skF_2')),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_503])).

tff(c_537,plain,
    ( ~ v5_relat_1(k7_relat_1('#skF_4','#skF_2'),'#skF_3')
    | ~ v1_relat_1(k7_relat_1('#skF_4','#skF_2')) ),
    inference(resolution,[status(thm)],[c_10,c_526])).

tff(c_540,plain,(
    ~ v5_relat_1(k7_relat_1('#skF_4','#skF_2'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_537])).

tff(c_550,plain,(
    ~ r1_tarski(k7_relat_1('#skF_4','#skF_2'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_131,c_540])).

tff(c_553,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_14,c_550])).

tff(c_557,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_553])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.11  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.32  % Computer   : n017.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % DateTime   : Tue Dec  1 09:26:31 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.55/1.36  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.55/1.37  
% 2.55/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.55/1.37  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k5_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.55/1.37  
% 2.55/1.37  %Foreground sorts:
% 2.55/1.37  
% 2.55/1.37  
% 2.55/1.37  %Background operators:
% 2.55/1.37  
% 2.55/1.37  
% 2.55/1.37  %Foreground operators:
% 2.55/1.37  tff(k5_relset_1, type, k5_relset_1: ($i * $i * $i * $i) > $i).
% 2.55/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.55/1.37  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.55/1.37  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.55/1.37  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.55/1.37  tff('#skF_2', type, '#skF_2': $i).
% 2.55/1.37  tff('#skF_3', type, '#skF_3': $i).
% 2.55/1.37  tff('#skF_1', type, '#skF_1': $i).
% 2.55/1.37  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.55/1.37  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.55/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.55/1.37  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.55/1.37  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.55/1.37  tff('#skF_4', type, '#skF_4': $i).
% 2.55/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.55/1.37  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.55/1.37  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.55/1.37  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.55/1.37  
% 2.55/1.39  tff(f_82, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C))) => m1_subset_1(k5_relset_1(A, C, D, B), k1_zfmisc_1(k2_zfmisc_1(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t33_relset_1)).
% 2.55/1.39  tff(f_53, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.55/1.39  tff(f_49, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k7_relat_1(B, A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_relat_1)).
% 2.55/1.39  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.55/1.39  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 2.55/1.39  tff(f_59, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.55/1.39  tff(f_41, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 2.55/1.39  tff(f_45, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_relat_1)).
% 2.55/1.39  tff(f_71, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_relset_1)).
% 2.55/1.39  tff(f_63, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k5_relset_1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k5_relset_1)).
% 2.55/1.39  tff(c_30, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.55/1.39  tff(c_43, plain, (![C_37, A_38, B_39]: (v1_relat_1(C_37) | ~m1_subset_1(C_37, k1_zfmisc_1(k2_zfmisc_1(A_38, B_39))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.55/1.39  tff(c_52, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_30, c_43])).
% 2.55/1.39  tff(c_14, plain, (![B_11, A_10]: (r1_tarski(k7_relat_1(B_11, A_10), B_11) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.55/1.39  tff(c_33, plain, (![A_33, B_34]: (r1_tarski(A_33, B_34) | ~m1_subset_1(A_33, k1_zfmisc_1(B_34)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.55/1.39  tff(c_41, plain, (r1_tarski('#skF_4', k2_zfmisc_1('#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_30, c_33])).
% 2.55/1.39  tff(c_73, plain, (![A_43, C_44, B_45]: (r1_tarski(A_43, C_44) | ~r1_tarski(B_45, C_44) | ~r1_tarski(A_43, B_45))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.55/1.39  tff(c_81, plain, (![A_43]: (r1_tarski(A_43, k2_zfmisc_1('#skF_1', '#skF_3')) | ~r1_tarski(A_43, '#skF_4'))), inference(resolution, [status(thm)], [c_41, c_73])).
% 2.55/1.39  tff(c_6, plain, (![A_4, B_5]: (m1_subset_1(A_4, k1_zfmisc_1(B_5)) | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.55/1.39  tff(c_106, plain, (![C_50, B_51, A_52]: (v5_relat_1(C_50, B_51) | ~m1_subset_1(C_50, k1_zfmisc_1(k2_zfmisc_1(A_52, B_51))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.55/1.39  tff(c_116, plain, (![A_53, B_54, A_55]: (v5_relat_1(A_53, B_54) | ~r1_tarski(A_53, k2_zfmisc_1(A_55, B_54)))), inference(resolution, [status(thm)], [c_6, c_106])).
% 2.55/1.39  tff(c_131, plain, (![A_43]: (v5_relat_1(A_43, '#skF_3') | ~r1_tarski(A_43, '#skF_4'))), inference(resolution, [status(thm)], [c_81, c_116])).
% 2.55/1.39  tff(c_83, plain, (![A_46]: (r1_tarski(A_46, k2_zfmisc_1('#skF_1', '#skF_3')) | ~r1_tarski(A_46, '#skF_4'))), inference(resolution, [status(thm)], [c_41, c_73])).
% 2.55/1.39  tff(c_51, plain, (![A_4, A_38, B_39]: (v1_relat_1(A_4) | ~r1_tarski(A_4, k2_zfmisc_1(A_38, B_39)))), inference(resolution, [status(thm)], [c_6, c_43])).
% 2.55/1.39  tff(c_91, plain, (![A_47]: (v1_relat_1(A_47) | ~r1_tarski(A_47, '#skF_4'))), inference(resolution, [status(thm)], [c_83, c_51])).
% 2.55/1.39  tff(c_99, plain, (![A_10]: (v1_relat_1(k7_relat_1('#skF_4', A_10)) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_14, c_91])).
% 2.55/1.39  tff(c_103, plain, (![A_10]: (v1_relat_1(k7_relat_1('#skF_4', A_10)))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_99])).
% 2.55/1.39  tff(c_10, plain, (![B_7, A_6]: (r1_tarski(k2_relat_1(B_7), A_6) | ~v5_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.55/1.39  tff(c_12, plain, (![B_9, A_8]: (r1_tarski(k1_relat_1(k7_relat_1(B_9, A_8)), A_8) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.55/1.39  tff(c_478, plain, (![C_138, A_139, B_140]: (m1_subset_1(C_138, k1_zfmisc_1(k2_zfmisc_1(A_139, B_140))) | ~r1_tarski(k2_relat_1(C_138), B_140) | ~r1_tarski(k1_relat_1(C_138), A_139) | ~v1_relat_1(C_138))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.55/1.39  tff(c_250, plain, (![A_91, B_92, C_93, D_94]: (k5_relset_1(A_91, B_92, C_93, D_94)=k7_relat_1(C_93, D_94) | ~m1_subset_1(C_93, k1_zfmisc_1(k2_zfmisc_1(A_91, B_92))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.55/1.39  tff(c_257, plain, (![D_94]: (k5_relset_1('#skF_1', '#skF_3', '#skF_4', D_94)=k7_relat_1('#skF_4', D_94))), inference(resolution, [status(thm)], [c_30, c_250])).
% 2.55/1.39  tff(c_28, plain, (~m1_subset_1(k5_relset_1('#skF_1', '#skF_3', '#skF_4', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.55/1.39  tff(c_259, plain, (~m1_subset_1(k7_relat_1('#skF_4', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_257, c_28])).
% 2.55/1.39  tff(c_485, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', '#skF_2')), '#skF_3') | ~r1_tarski(k1_relat_1(k7_relat_1('#skF_4', '#skF_2')), '#skF_2') | ~v1_relat_1(k7_relat_1('#skF_4', '#skF_2'))), inference(resolution, [status(thm)], [c_478, c_259])).
% 2.55/1.39  tff(c_503, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', '#skF_2')), '#skF_3') | ~r1_tarski(k1_relat_1(k7_relat_1('#skF_4', '#skF_2')), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_103, c_485])).
% 2.55/1.39  tff(c_518, plain, (~r1_tarski(k1_relat_1(k7_relat_1('#skF_4', '#skF_2')), '#skF_2')), inference(splitLeft, [status(thm)], [c_503])).
% 2.55/1.39  tff(c_521, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_12, c_518])).
% 2.55/1.39  tff(c_525, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_521])).
% 2.55/1.39  tff(c_526, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', '#skF_2')), '#skF_3')), inference(splitRight, [status(thm)], [c_503])).
% 2.55/1.39  tff(c_537, plain, (~v5_relat_1(k7_relat_1('#skF_4', '#skF_2'), '#skF_3') | ~v1_relat_1(k7_relat_1('#skF_4', '#skF_2'))), inference(resolution, [status(thm)], [c_10, c_526])).
% 2.55/1.39  tff(c_540, plain, (~v5_relat_1(k7_relat_1('#skF_4', '#skF_2'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_103, c_537])).
% 2.55/1.39  tff(c_550, plain, (~r1_tarski(k7_relat_1('#skF_4', '#skF_2'), '#skF_4')), inference(resolution, [status(thm)], [c_131, c_540])).
% 2.55/1.39  tff(c_553, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_14, c_550])).
% 2.55/1.39  tff(c_557, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_553])).
% 2.55/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.55/1.39  
% 2.55/1.39  Inference rules
% 2.55/1.39  ----------------------
% 2.55/1.39  #Ref     : 0
% 2.55/1.39  #Sup     : 110
% 2.55/1.39  #Fact    : 0
% 2.55/1.39  #Define  : 0
% 2.55/1.39  #Split   : 1
% 2.55/1.39  #Chain   : 0
% 2.55/1.39  #Close   : 0
% 2.55/1.39  
% 2.55/1.39  Ordering : KBO
% 2.55/1.39  
% 2.55/1.39  Simplification rules
% 2.55/1.39  ----------------------
% 2.55/1.39  #Subsume      : 7
% 2.55/1.39  #Demod        : 17
% 2.55/1.39  #Tautology    : 13
% 2.55/1.39  #SimpNegUnit  : 0
% 2.55/1.39  #BackRed      : 2
% 2.55/1.39  
% 2.55/1.39  #Partial instantiations: 0
% 2.55/1.39  #Strategies tried      : 1
% 2.55/1.39  
% 2.55/1.39  Timing (in seconds)
% 2.55/1.39  ----------------------
% 2.55/1.39  Preprocessing        : 0.29
% 2.55/1.39  Parsing              : 0.16
% 2.55/1.39  CNF conversion       : 0.02
% 2.55/1.39  Main loop            : 0.34
% 2.55/1.39  Inferencing          : 0.14
% 2.55/1.39  Reduction            : 0.09
% 2.55/1.39  Demodulation         : 0.06
% 2.55/1.39  BG Simplification    : 0.02
% 2.55/1.39  Subsumption          : 0.06
% 2.55/1.39  Abstraction          : 0.02
% 2.55/1.39  MUC search           : 0.00
% 2.55/1.39  Cooper               : 0.00
% 2.55/1.39  Total                : 0.66
% 2.55/1.39  Index Insertion      : 0.00
% 2.55/1.39  Index Deletion       : 0.00
% 2.81/1.39  Index Matching       : 0.00
% 2.81/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
