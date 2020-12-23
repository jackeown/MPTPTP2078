%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:03 EST 2020

% Result     : Theorem 2.30s
% Output     : CNFRefutation 2.30s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 292 expanded)
%              Number of leaves         :   27 ( 111 expanded)
%              Depth                    :   11
%              Number of atoms          :   96 ( 536 expanded)
%              Number of equality atoms :   24 ( 186 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v1_partfun1 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k8_relset_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_36,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_93,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_xboole_0,A)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,A))) )
       => k8_relset_1(k1_xboole_0,A,C,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_funct_2)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_51,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc3_relset_1)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_38,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_partfun1(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_partfun1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v1_partfun1(C,A) )
       => ( v1_funct_1(C)
          & v1_funct_2(C,A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_2)).

tff(f_55,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_84,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( B = k1_xboole_0
         => A = k1_xboole_0 )
       => k8_relset_1(A,B,C,B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_funct_2)).

tff(c_10,plain,(
    ! [B_3] : k2_zfmisc_1(k1_xboole_0,B_3) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_32,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,'#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_37,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_32])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_88,plain,(
    ! [C_38,A_39,B_40] :
      ( v1_xboole_0(C_38)
      | ~ m1_subset_1(C_38,k1_zfmisc_1(k2_zfmisc_1(A_39,B_40)))
      | ~ v1_xboole_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_98,plain,(
    ! [C_38] :
      ( v1_xboole_0(C_38)
      | ~ m1_subset_1(C_38,k1_zfmisc_1(k1_xboole_0))
      | ~ v1_xboole_0(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_88])).

tff(c_103,plain,(
    ! [C_41] :
      ( v1_xboole_0(C_41)
      | ~ m1_subset_1(C_41,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_98])).

tff(c_111,plain,(
    v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_37,c_103])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_131,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_111,c_4])).

tff(c_12,plain,(
    ! [A_4] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_4)) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_139,plain,(
    ! [A_4] : m1_subset_1('#skF_3',k1_zfmisc_1(A_4)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_12])).

tff(c_114,plain,(
    ! [C_42,A_43,B_44] :
      ( v1_partfun1(C_42,A_43)
      | ~ m1_subset_1(C_42,k1_zfmisc_1(k2_zfmisc_1(A_43,B_44)))
      | ~ v1_xboole_0(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_124,plain,(
    ! [C_42] :
      ( v1_partfun1(C_42,k1_xboole_0)
      | ~ m1_subset_1(C_42,k1_zfmisc_1(k1_xboole_0))
      | ~ v1_xboole_0(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_114])).

tff(c_127,plain,(
    ! [C_42] :
      ( v1_partfun1(C_42,k1_xboole_0)
      | ~ m1_subset_1(C_42,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_124])).

tff(c_233,plain,(
    ! [C_58] :
      ( v1_partfun1(C_58,'#skF_3')
      | ~ m1_subset_1(C_58,k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_131,c_127])).

tff(c_238,plain,(
    v1_partfun1('#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_139,c_233])).

tff(c_36,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_239,plain,(
    ! [C_59,A_60,B_61] :
      ( v1_funct_2(C_59,A_60,B_61)
      | ~ v1_partfun1(C_59,A_60)
      | ~ v1_funct_1(C_59)
      | ~ m1_subset_1(C_59,k1_zfmisc_1(k2_zfmisc_1(A_60,B_61))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_243,plain,(
    ! [A_60,B_61] :
      ( v1_funct_2('#skF_3',A_60,B_61)
      | ~ v1_partfun1('#skF_3',A_60)
      | ~ v1_funct_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_139,c_239])).

tff(c_252,plain,(
    ! [A_60,B_61] :
      ( v1_funct_2('#skF_3',A_60,B_61)
      | ~ v1_partfun1('#skF_3',A_60) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_243])).

tff(c_214,plain,(
    ! [A_50,B_51,C_52,D_53] :
      ( k8_relset_1(A_50,B_51,C_52,D_53) = k10_relat_1(C_52,D_53)
      | ~ m1_subset_1(C_52,k1_zfmisc_1(k2_zfmisc_1(A_50,B_51))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_222,plain,(
    ! [A_50,B_51,D_53] : k8_relset_1(A_50,B_51,'#skF_3',D_53) = k10_relat_1('#skF_3',D_53) ),
    inference(resolution,[status(thm)],[c_139,c_214])).

tff(c_26,plain,(
    ! [B_24,C_25] :
      ( k8_relset_1(k1_xboole_0,B_24,C_25,B_24) = k1_xboole_0
      | ~ m1_subset_1(C_25,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_24)))
      | ~ v1_funct_2(C_25,k1_xboole_0,B_24)
      | ~ v1_funct_1(C_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_38,plain,(
    ! [B_24,C_25] :
      ( k8_relset_1(k1_xboole_0,B_24,C_25,B_24) = k1_xboole_0
      | ~ m1_subset_1(C_25,k1_zfmisc_1(k1_xboole_0))
      | ~ v1_funct_2(C_25,k1_xboole_0,B_24)
      | ~ v1_funct_1(C_25) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_26])).

tff(c_290,plain,(
    ! [B_72,C_73] :
      ( k8_relset_1('#skF_3',B_72,C_73,B_72) = '#skF_3'
      | ~ m1_subset_1(C_73,k1_zfmisc_1('#skF_3'))
      | ~ v1_funct_2(C_73,'#skF_3',B_72)
      | ~ v1_funct_1(C_73) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_131,c_131,c_131,c_38])).

tff(c_293,plain,(
    ! [B_72] :
      ( k8_relset_1('#skF_3',B_72,'#skF_3',B_72) = '#skF_3'
      | ~ v1_funct_2('#skF_3','#skF_3',B_72)
      | ~ v1_funct_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_139,c_290])).

tff(c_297,plain,(
    ! [B_74] :
      ( k10_relat_1('#skF_3',B_74) = '#skF_3'
      | ~ v1_funct_2('#skF_3','#skF_3',B_74) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_222,c_293])).

tff(c_301,plain,(
    ! [B_61] :
      ( k10_relat_1('#skF_3',B_61) = '#skF_3'
      | ~ v1_partfun1('#skF_3','#skF_3') ) ),
    inference(resolution,[status(thm)],[c_252,c_297])).

tff(c_307,plain,(
    ! [B_61] : k10_relat_1('#skF_3',B_61) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_238,c_301])).

tff(c_30,plain,(
    k8_relset_1(k1_xboole_0,'#skF_1','#skF_3','#skF_2') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_136,plain,(
    k8_relset_1('#skF_3','#skF_1','#skF_3','#skF_2') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_131,c_30])).

tff(c_279,plain,(
    k10_relat_1('#skF_3','#skF_2') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_222,c_136])).

tff(c_313,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_307,c_279])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:09:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.30/1.42  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.30/1.43  
% 2.30/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.30/1.43  %$ v1_funct_2 > v1_partfun1 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k8_relset_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.30/1.43  
% 2.30/1.43  %Foreground sorts:
% 2.30/1.43  
% 2.30/1.43  
% 2.30/1.43  %Background operators:
% 2.30/1.43  
% 2.30/1.43  
% 2.30/1.43  %Foreground operators:
% 2.30/1.43  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.30/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.30/1.43  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.30/1.43  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 2.30/1.43  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.30/1.43  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.30/1.43  tff('#skF_2', type, '#skF_2': $i).
% 2.30/1.43  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 2.30/1.43  tff('#skF_3', type, '#skF_3': $i).
% 2.30/1.43  tff('#skF_1', type, '#skF_1': $i).
% 2.30/1.43  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.30/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.30/1.43  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.30/1.43  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.30/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.30/1.43  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.30/1.43  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.30/1.43  
% 2.30/1.45  tff(f_36, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.30/1.45  tff(f_93, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_xboole_0, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, A)))) => (k8_relset_1(k1_xboole_0, A, C, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_funct_2)).
% 2.30/1.45  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.30/1.45  tff(f_51, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_xboole_0(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc3_relset_1)).
% 2.30/1.45  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.30/1.45  tff(f_38, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 2.30/1.45  tff(f_72, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_partfun1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_partfun1)).
% 2.30/1.45  tff(f_65, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_partfun1(C, A)) => (v1_funct_1(C) & v1_funct_2(C, A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_funct_2)).
% 2.30/1.45  tff(f_55, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 2.30/1.45  tff(f_84, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((B = k1_xboole_0) => (A = k1_xboole_0)) => (k8_relset_1(A, B, C, B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_funct_2)).
% 2.30/1.45  tff(c_10, plain, (![B_3]: (k2_zfmisc_1(k1_xboole_0, B_3)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.30/1.45  tff(c_32, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.30/1.45  tff(c_37, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_32])).
% 2.30/1.45  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.30/1.45  tff(c_88, plain, (![C_38, A_39, B_40]: (v1_xboole_0(C_38) | ~m1_subset_1(C_38, k1_zfmisc_1(k2_zfmisc_1(A_39, B_40))) | ~v1_xboole_0(A_39))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.30/1.45  tff(c_98, plain, (![C_38]: (v1_xboole_0(C_38) | ~m1_subset_1(C_38, k1_zfmisc_1(k1_xboole_0)) | ~v1_xboole_0(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_88])).
% 2.30/1.45  tff(c_103, plain, (![C_41]: (v1_xboole_0(C_41) | ~m1_subset_1(C_41, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_98])).
% 2.30/1.45  tff(c_111, plain, (v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_37, c_103])).
% 2.30/1.45  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.30/1.45  tff(c_131, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_111, c_4])).
% 2.30/1.45  tff(c_12, plain, (![A_4]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.30/1.45  tff(c_139, plain, (![A_4]: (m1_subset_1('#skF_3', k1_zfmisc_1(A_4)))), inference(demodulation, [status(thm), theory('equality')], [c_131, c_12])).
% 2.30/1.45  tff(c_114, plain, (![C_42, A_43, B_44]: (v1_partfun1(C_42, A_43) | ~m1_subset_1(C_42, k1_zfmisc_1(k2_zfmisc_1(A_43, B_44))) | ~v1_xboole_0(A_43))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.30/1.45  tff(c_124, plain, (![C_42]: (v1_partfun1(C_42, k1_xboole_0) | ~m1_subset_1(C_42, k1_zfmisc_1(k1_xboole_0)) | ~v1_xboole_0(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_114])).
% 2.30/1.45  tff(c_127, plain, (![C_42]: (v1_partfun1(C_42, k1_xboole_0) | ~m1_subset_1(C_42, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_124])).
% 2.30/1.45  tff(c_233, plain, (![C_58]: (v1_partfun1(C_58, '#skF_3') | ~m1_subset_1(C_58, k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_131, c_131, c_127])).
% 2.30/1.45  tff(c_238, plain, (v1_partfun1('#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_139, c_233])).
% 2.30/1.45  tff(c_36, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.30/1.45  tff(c_239, plain, (![C_59, A_60, B_61]: (v1_funct_2(C_59, A_60, B_61) | ~v1_partfun1(C_59, A_60) | ~v1_funct_1(C_59) | ~m1_subset_1(C_59, k1_zfmisc_1(k2_zfmisc_1(A_60, B_61))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.30/1.45  tff(c_243, plain, (![A_60, B_61]: (v1_funct_2('#skF_3', A_60, B_61) | ~v1_partfun1('#skF_3', A_60) | ~v1_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_139, c_239])).
% 2.30/1.45  tff(c_252, plain, (![A_60, B_61]: (v1_funct_2('#skF_3', A_60, B_61) | ~v1_partfun1('#skF_3', A_60))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_243])).
% 2.30/1.45  tff(c_214, plain, (![A_50, B_51, C_52, D_53]: (k8_relset_1(A_50, B_51, C_52, D_53)=k10_relat_1(C_52, D_53) | ~m1_subset_1(C_52, k1_zfmisc_1(k2_zfmisc_1(A_50, B_51))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.30/1.45  tff(c_222, plain, (![A_50, B_51, D_53]: (k8_relset_1(A_50, B_51, '#skF_3', D_53)=k10_relat_1('#skF_3', D_53))), inference(resolution, [status(thm)], [c_139, c_214])).
% 2.30/1.45  tff(c_26, plain, (![B_24, C_25]: (k8_relset_1(k1_xboole_0, B_24, C_25, B_24)=k1_xboole_0 | ~m1_subset_1(C_25, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_24))) | ~v1_funct_2(C_25, k1_xboole_0, B_24) | ~v1_funct_1(C_25))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.30/1.45  tff(c_38, plain, (![B_24, C_25]: (k8_relset_1(k1_xboole_0, B_24, C_25, B_24)=k1_xboole_0 | ~m1_subset_1(C_25, k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_2(C_25, k1_xboole_0, B_24) | ~v1_funct_1(C_25))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_26])).
% 2.30/1.45  tff(c_290, plain, (![B_72, C_73]: (k8_relset_1('#skF_3', B_72, C_73, B_72)='#skF_3' | ~m1_subset_1(C_73, k1_zfmisc_1('#skF_3')) | ~v1_funct_2(C_73, '#skF_3', B_72) | ~v1_funct_1(C_73))), inference(demodulation, [status(thm), theory('equality')], [c_131, c_131, c_131, c_131, c_38])).
% 2.30/1.45  tff(c_293, plain, (![B_72]: (k8_relset_1('#skF_3', B_72, '#skF_3', B_72)='#skF_3' | ~v1_funct_2('#skF_3', '#skF_3', B_72) | ~v1_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_139, c_290])).
% 2.30/1.45  tff(c_297, plain, (![B_74]: (k10_relat_1('#skF_3', B_74)='#skF_3' | ~v1_funct_2('#skF_3', '#skF_3', B_74))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_222, c_293])).
% 2.30/1.45  tff(c_301, plain, (![B_61]: (k10_relat_1('#skF_3', B_61)='#skF_3' | ~v1_partfun1('#skF_3', '#skF_3'))), inference(resolution, [status(thm)], [c_252, c_297])).
% 2.30/1.45  tff(c_307, plain, (![B_61]: (k10_relat_1('#skF_3', B_61)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_238, c_301])).
% 2.30/1.45  tff(c_30, plain, (k8_relset_1(k1_xboole_0, '#skF_1', '#skF_3', '#skF_2')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.30/1.45  tff(c_136, plain, (k8_relset_1('#skF_3', '#skF_1', '#skF_3', '#skF_2')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_131, c_131, c_30])).
% 2.30/1.45  tff(c_279, plain, (k10_relat_1('#skF_3', '#skF_2')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_222, c_136])).
% 2.30/1.45  tff(c_313, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_307, c_279])).
% 2.30/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.30/1.45  
% 2.30/1.45  Inference rules
% 2.30/1.45  ----------------------
% 2.30/1.45  #Ref     : 0
% 2.30/1.45  #Sup     : 55
% 2.30/1.45  #Fact    : 0
% 2.30/1.45  #Define  : 0
% 2.30/1.45  #Split   : 0
% 2.30/1.45  #Chain   : 0
% 2.30/1.45  #Close   : 0
% 2.30/1.45  
% 2.30/1.45  Ordering : KBO
% 2.30/1.45  
% 2.30/1.45  Simplification rules
% 2.30/1.45  ----------------------
% 2.30/1.45  #Subsume      : 8
% 2.30/1.45  #Demod        : 47
% 2.30/1.45  #Tautology    : 31
% 2.30/1.45  #SimpNegUnit  : 0
% 2.30/1.45  #BackRed      : 15
% 2.30/1.45  
% 2.30/1.45  #Partial instantiations: 0
% 2.30/1.45  #Strategies tried      : 1
% 2.30/1.45  
% 2.53/1.45  Timing (in seconds)
% 2.53/1.45  ----------------------
% 2.53/1.45  Preprocessing        : 0.40
% 2.53/1.45  Parsing              : 0.24
% 2.53/1.45  CNF conversion       : 0.02
% 2.53/1.45  Main loop            : 0.21
% 2.53/1.45  Inferencing          : 0.07
% 2.53/1.45  Reduction            : 0.07
% 2.53/1.45  Demodulation         : 0.05
% 2.53/1.45  BG Simplification    : 0.02
% 2.53/1.45  Subsumption          : 0.04
% 2.53/1.45  Abstraction          : 0.01
% 2.53/1.45  MUC search           : 0.00
% 2.53/1.45  Cooper               : 0.00
% 2.53/1.45  Total                : 0.65
% 2.53/1.45  Index Insertion      : 0.00
% 2.53/1.45  Index Deletion       : 0.00
% 2.53/1.45  Index Matching       : 0.00
% 2.53/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
