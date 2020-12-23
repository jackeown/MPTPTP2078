%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:43 EST 2020

% Result     : Theorem 2.16s
% Output     : CNFRefutation 2.61s
% Verified   : 
% Statistics : Number of formulae       :   67 (  88 expanded)
%              Number of leaves         :   32 (  44 expanded)
%              Depth                    :   12
%              Number of atoms          :   85 ( 144 expanded)
%              Number of equality atoms :   19 (  20 expanded)
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

tff(f_90,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( r1_tarski(A,C)
         => r2_relset_1(A,B,k2_partfun1(A,B,D,C),D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_funct_2)).

tff(f_73,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_79,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(c_34,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_531,plain,(
    ! [A_70,B_71,D_72] :
      ( r2_relset_1(A_70,B_71,D_72,D_72)
      | ~ m1_subset_1(D_72,k1_zfmisc_1(k2_zfmisc_1(A_70,B_71))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_534,plain,(
    r2_relset_1('#skF_1','#skF_2','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_34,c_531])).

tff(c_63,plain,(
    ! [C_32,A_33,B_34] :
      ( v1_relat_1(C_32)
      | ~ m1_subset_1(C_32,k1_zfmisc_1(k2_zfmisc_1(A_33,B_34))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_67,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_34,c_63])).

tff(c_32,plain,(
    r1_tarski('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_41,plain,(
    ! [A_29,B_30] :
      ( k2_xboole_0(A_29,B_30) = B_30
      | ~ r1_tarski(A_29,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_49,plain,(
    k2_xboole_0('#skF_1','#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_32,c_41])).

tff(c_316,plain,(
    ! [C_61,A_62,B_63] :
      ( v4_relat_1(C_61,A_62)
      | ~ m1_subset_1(C_61,k1_zfmisc_1(k2_zfmisc_1(A_62,B_63))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_320,plain,(
    v4_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_316])).

tff(c_12,plain,(
    ! [B_9,A_8] :
      ( k7_relat_1(B_9,A_8) = B_9
      | ~ v4_relat_1(B_9,A_8)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_323,plain,
    ( k7_relat_1('#skF_4','#skF_1') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_320,c_12])).

tff(c_326,plain,(
    k7_relat_1('#skF_4','#skF_1') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_323])).

tff(c_14,plain,(
    ! [B_11,A_10] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_11,A_10)),A_10)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_330,plain,
    ( r1_tarski(k1_relat_1('#skF_4'),'#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_326,c_14])).

tff(c_334,plain,(
    r1_tarski(k1_relat_1('#skF_4'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_330])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( k2_xboole_0(A_6,B_7) = B_7
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_342,plain,(
    k2_xboole_0(k1_relat_1('#skF_4'),'#skF_1') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_334,c_10])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_87,plain,(
    ! [A_39,C_40,B_41] :
      ( r1_tarski(A_39,C_40)
      | ~ r1_tarski(k2_xboole_0(A_39,B_41),C_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_99,plain,(
    ! [A_42,B_43] : r1_tarski(A_42,k2_xboole_0(A_42,B_43)) ),
    inference(resolution,[status(thm)],[c_6,c_87])).

tff(c_8,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(A_3,C_5)
      | ~ r1_tarski(k2_xboole_0(A_3,B_4),C_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_115,plain,(
    ! [A_3,B_4,B_43] : r1_tarski(A_3,k2_xboole_0(k2_xboole_0(A_3,B_4),B_43)) ),
    inference(resolution,[status(thm)],[c_99,c_8])).

tff(c_361,plain,(
    ! [B_64] : r1_tarski(k1_relat_1('#skF_4'),k2_xboole_0('#skF_1',B_64)) ),
    inference(superposition,[status(thm),theory(equality)],[c_342,c_115])).

tff(c_374,plain,(
    r1_tarski(k1_relat_1('#skF_4'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_49,c_361])).

tff(c_390,plain,(
    ! [B_65,A_66] :
      ( k7_relat_1(B_65,A_66) = B_65
      | ~ r1_tarski(k1_relat_1(B_65),A_66)
      | ~ v1_relat_1(B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_393,plain,
    ( k7_relat_1('#skF_4','#skF_3') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_374,c_390])).

tff(c_417,plain,(
    k7_relat_1('#skF_4','#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_393])).

tff(c_38,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_691,plain,(
    ! [A_79,B_80,C_81,D_82] :
      ( k2_partfun1(A_79,B_80,C_81,D_82) = k7_relat_1(C_81,D_82)
      | ~ m1_subset_1(C_81,k1_zfmisc_1(k2_zfmisc_1(A_79,B_80)))
      | ~ v1_funct_1(C_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_693,plain,(
    ! [D_82] :
      ( k2_partfun1('#skF_1','#skF_2','#skF_4',D_82) = k7_relat_1('#skF_4',D_82)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_34,c_691])).

tff(c_696,plain,(
    ! [D_82] : k2_partfun1('#skF_1','#skF_2','#skF_4',D_82) = k7_relat_1('#skF_4',D_82) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_693])).

tff(c_30,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_697,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k7_relat_1('#skF_4','#skF_3'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_696,c_30])).

tff(c_700,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_534,c_417,c_697])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n001.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:37:45 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.16/1.33  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.61/1.33  
% 2.61/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.61/1.34  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_partfun1 > k7_relat_1 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.61/1.34  
% 2.61/1.34  %Foreground sorts:
% 2.61/1.34  
% 2.61/1.34  
% 2.61/1.34  %Background operators:
% 2.61/1.34  
% 2.61/1.34  
% 2.61/1.34  %Foreground operators:
% 2.61/1.34  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.61/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.61/1.34  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 2.61/1.34  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.61/1.34  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.61/1.34  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.61/1.34  tff('#skF_2', type, '#skF_2': $i).
% 2.61/1.34  tff('#skF_3', type, '#skF_3': $i).
% 2.61/1.34  tff('#skF_1', type, '#skF_1': $i).
% 2.61/1.34  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.61/1.34  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.61/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.61/1.34  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.61/1.34  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.61/1.34  tff('#skF_4', type, '#skF_4': $i).
% 2.61/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.61/1.34  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 2.61/1.34  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.61/1.34  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.61/1.34  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.61/1.34  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.61/1.34  
% 2.61/1.35  tff(f_90, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(A, C) => r2_relset_1(A, B, k2_partfun1(A, B, D, C), D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_funct_2)).
% 2.61/1.35  tff(f_73, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 2.61/1.35  tff(f_59, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.61/1.35  tff(f_39, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.61/1.35  tff(f_65, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.61/1.35  tff(f_45, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 2.61/1.35  tff(f_49, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_relat_1)).
% 2.61/1.35  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.61/1.35  tff(f_35, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 2.61/1.35  tff(f_55, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_relat_1)).
% 2.61/1.35  tff(f_79, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 2.61/1.35  tff(c_34, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.61/1.35  tff(c_531, plain, (![A_70, B_71, D_72]: (r2_relset_1(A_70, B_71, D_72, D_72) | ~m1_subset_1(D_72, k1_zfmisc_1(k2_zfmisc_1(A_70, B_71))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.61/1.35  tff(c_534, plain, (r2_relset_1('#skF_1', '#skF_2', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_34, c_531])).
% 2.61/1.35  tff(c_63, plain, (![C_32, A_33, B_34]: (v1_relat_1(C_32) | ~m1_subset_1(C_32, k1_zfmisc_1(k2_zfmisc_1(A_33, B_34))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.61/1.35  tff(c_67, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_34, c_63])).
% 2.61/1.35  tff(c_32, plain, (r1_tarski('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.61/1.35  tff(c_41, plain, (![A_29, B_30]: (k2_xboole_0(A_29, B_30)=B_30 | ~r1_tarski(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.61/1.35  tff(c_49, plain, (k2_xboole_0('#skF_1', '#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_32, c_41])).
% 2.61/1.35  tff(c_316, plain, (![C_61, A_62, B_63]: (v4_relat_1(C_61, A_62) | ~m1_subset_1(C_61, k1_zfmisc_1(k2_zfmisc_1(A_62, B_63))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.61/1.35  tff(c_320, plain, (v4_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_34, c_316])).
% 2.61/1.35  tff(c_12, plain, (![B_9, A_8]: (k7_relat_1(B_9, A_8)=B_9 | ~v4_relat_1(B_9, A_8) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.61/1.35  tff(c_323, plain, (k7_relat_1('#skF_4', '#skF_1')='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_320, c_12])).
% 2.61/1.35  tff(c_326, plain, (k7_relat_1('#skF_4', '#skF_1')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_67, c_323])).
% 2.61/1.35  tff(c_14, plain, (![B_11, A_10]: (r1_tarski(k1_relat_1(k7_relat_1(B_11, A_10)), A_10) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.61/1.35  tff(c_330, plain, (r1_tarski(k1_relat_1('#skF_4'), '#skF_1') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_326, c_14])).
% 2.61/1.35  tff(c_334, plain, (r1_tarski(k1_relat_1('#skF_4'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_67, c_330])).
% 2.61/1.35  tff(c_10, plain, (![A_6, B_7]: (k2_xboole_0(A_6, B_7)=B_7 | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.61/1.35  tff(c_342, plain, (k2_xboole_0(k1_relat_1('#skF_4'), '#skF_1')='#skF_1'), inference(resolution, [status(thm)], [c_334, c_10])).
% 2.61/1.35  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.61/1.35  tff(c_87, plain, (![A_39, C_40, B_41]: (r1_tarski(A_39, C_40) | ~r1_tarski(k2_xboole_0(A_39, B_41), C_40))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.61/1.35  tff(c_99, plain, (![A_42, B_43]: (r1_tarski(A_42, k2_xboole_0(A_42, B_43)))), inference(resolution, [status(thm)], [c_6, c_87])).
% 2.61/1.35  tff(c_8, plain, (![A_3, C_5, B_4]: (r1_tarski(A_3, C_5) | ~r1_tarski(k2_xboole_0(A_3, B_4), C_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.61/1.35  tff(c_115, plain, (![A_3, B_4, B_43]: (r1_tarski(A_3, k2_xboole_0(k2_xboole_0(A_3, B_4), B_43)))), inference(resolution, [status(thm)], [c_99, c_8])).
% 2.61/1.35  tff(c_361, plain, (![B_64]: (r1_tarski(k1_relat_1('#skF_4'), k2_xboole_0('#skF_1', B_64)))), inference(superposition, [status(thm), theory('equality')], [c_342, c_115])).
% 2.61/1.35  tff(c_374, plain, (r1_tarski(k1_relat_1('#skF_4'), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_49, c_361])).
% 2.61/1.35  tff(c_390, plain, (![B_65, A_66]: (k7_relat_1(B_65, A_66)=B_65 | ~r1_tarski(k1_relat_1(B_65), A_66) | ~v1_relat_1(B_65))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.61/1.35  tff(c_393, plain, (k7_relat_1('#skF_4', '#skF_3')='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_374, c_390])).
% 2.61/1.35  tff(c_417, plain, (k7_relat_1('#skF_4', '#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_67, c_393])).
% 2.61/1.35  tff(c_38, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.61/1.35  tff(c_691, plain, (![A_79, B_80, C_81, D_82]: (k2_partfun1(A_79, B_80, C_81, D_82)=k7_relat_1(C_81, D_82) | ~m1_subset_1(C_81, k1_zfmisc_1(k2_zfmisc_1(A_79, B_80))) | ~v1_funct_1(C_81))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.61/1.35  tff(c_693, plain, (![D_82]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_82)=k7_relat_1('#skF_4', D_82) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_34, c_691])).
% 2.61/1.35  tff(c_696, plain, (![D_82]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_82)=k7_relat_1('#skF_4', D_82))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_693])).
% 2.61/1.35  tff(c_30, plain, (~r2_relset_1('#skF_1', '#skF_2', k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.61/1.35  tff(c_697, plain, (~r2_relset_1('#skF_1', '#skF_2', k7_relat_1('#skF_4', '#skF_3'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_696, c_30])).
% 2.61/1.35  tff(c_700, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_534, c_417, c_697])).
% 2.61/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.61/1.35  
% 2.61/1.35  Inference rules
% 2.61/1.35  ----------------------
% 2.61/1.35  #Ref     : 0
% 2.61/1.35  #Sup     : 150
% 2.61/1.35  #Fact    : 0
% 2.61/1.35  #Define  : 0
% 2.61/1.35  #Split   : 3
% 2.61/1.35  #Chain   : 0
% 2.61/1.35  #Close   : 0
% 2.61/1.35  
% 2.61/1.35  Ordering : KBO
% 2.61/1.35  
% 2.61/1.35  Simplification rules
% 2.61/1.35  ----------------------
% 2.61/1.35  #Subsume      : 6
% 2.61/1.35  #Demod        : 82
% 2.61/1.35  #Tautology    : 86
% 2.61/1.35  #SimpNegUnit  : 0
% 2.61/1.35  #BackRed      : 1
% 2.61/1.35  
% 2.61/1.35  #Partial instantiations: 0
% 2.61/1.35  #Strategies tried      : 1
% 2.61/1.35  
% 2.61/1.35  Timing (in seconds)
% 2.61/1.35  ----------------------
% 2.61/1.35  Preprocessing        : 0.31
% 2.61/1.35  Parsing              : 0.17
% 2.61/1.35  CNF conversion       : 0.02
% 2.61/1.35  Main loop            : 0.29
% 2.61/1.36  Inferencing          : 0.10
% 2.61/1.36  Reduction            : 0.10
% 2.61/1.36  Demodulation         : 0.07
% 2.61/1.36  BG Simplification    : 0.01
% 2.61/1.36  Subsumption          : 0.06
% 2.61/1.36  Abstraction          : 0.02
% 2.61/1.36  MUC search           : 0.00
% 2.61/1.36  Cooper               : 0.00
% 2.61/1.36  Total                : 0.63
% 2.61/1.36  Index Insertion      : 0.00
% 2.61/1.36  Index Deletion       : 0.00
% 2.61/1.36  Index Matching       : 0.00
% 2.61/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
