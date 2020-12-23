%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:36 EST 2020

% Result     : Theorem 2.53s
% Output     : CNFRefutation 2.81s
% Verified   : 
% Statistics : Number of formulae       :   66 (  92 expanded)
%              Number of leaves         :   31 (  44 expanded)
%              Depth                    :   12
%              Number of atoms          :   84 ( 136 expanded)
%              Number of equality atoms :   18 (  19 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k5_relset_1 > k7_relat_1 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_89,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A)))
       => ( r1_tarski(B,C)
         => r2_relset_1(B,A,k5_relset_1(B,A,D,C),D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_relset_1)).

tff(f_82,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_48,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_46,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_58,axiom,(
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

tff(f_64,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_74,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k5_relset_1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_relset_1)).

tff(c_36,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_651,plain,(
    ! [A_79,B_80,D_81] :
      ( r2_relset_1(A_79,B_80,D_81,D_81)
      | ~ m1_subset_1(D_81,k1_zfmisc_1(k2_zfmisc_1(A_79,B_80))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_654,plain,(
    r2_relset_1('#skF_2','#skF_1','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_651])).

tff(c_14,plain,(
    ! [A_11,B_12] : v1_relat_1(k2_zfmisc_1(A_11,B_12)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_67,plain,(
    ! [B_38,A_39] :
      ( v1_relat_1(B_38)
      | ~ m1_subset_1(B_38,k1_zfmisc_1(A_39))
      | ~ v1_relat_1(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_70,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_36,c_67])).

tff(c_73,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_70])).

tff(c_34,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_40,plain,(
    ! [A_33,B_34] :
      ( k2_xboole_0(A_33,B_34) = B_34
      | ~ r1_tarski(A_33,B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_48,plain,(
    k2_xboole_0('#skF_2','#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_34,c_40])).

tff(c_305,plain,(
    ! [C_61,A_62,B_63] :
      ( v4_relat_1(C_61,A_62)
      | ~ m1_subset_1(C_61,k1_zfmisc_1(k2_zfmisc_1(A_62,B_63))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_309,plain,(
    v4_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_36,c_305])).

tff(c_16,plain,(
    ! [B_14,A_13] :
      ( k7_relat_1(B_14,A_13) = B_14
      | ~ v4_relat_1(B_14,A_13)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_312,plain,
    ( k7_relat_1('#skF_4','#skF_2') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_309,c_16])).

tff(c_315,plain,(
    k7_relat_1('#skF_4','#skF_2') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_312])).

tff(c_18,plain,(
    ! [B_16,A_15] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_16,A_15)),A_15)
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_319,plain,
    ( r1_tarski(k1_relat_1('#skF_4'),'#skF_2')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_315,c_18])).

tff(c_323,plain,(
    r1_tarski(k1_relat_1('#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_319])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( k2_xboole_0(A_6,B_7) = B_7
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_334,plain,(
    k2_xboole_0(k1_relat_1('#skF_4'),'#skF_2') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_323,c_10])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_88,plain,(
    ! [A_42,C_43,B_44] :
      ( r1_tarski(A_42,C_43)
      | ~ r1_tarski(k2_xboole_0(A_42,B_44),C_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_101,plain,(
    ! [A_47,B_48] : r1_tarski(A_47,k2_xboole_0(A_47,B_48)) ),
    inference(resolution,[status(thm)],[c_6,c_88])).

tff(c_8,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(A_3,C_5)
      | ~ r1_tarski(k2_xboole_0(A_3,B_4),C_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_117,plain,(
    ! [A_3,B_4,B_48] : r1_tarski(A_3,k2_xboole_0(k2_xboole_0(A_3,B_4),B_48)) ),
    inference(resolution,[status(thm)],[c_101,c_8])).

tff(c_364,plain,(
    ! [B_65] : r1_tarski(k1_relat_1('#skF_4'),k2_xboole_0('#skF_2',B_65)) ),
    inference(superposition,[status(thm),theory(equality)],[c_334,c_117])).

tff(c_377,plain,(
    r1_tarski(k1_relat_1('#skF_4'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_364])).

tff(c_456,plain,(
    ! [B_71,A_72] :
      ( k7_relat_1(B_71,A_72) = B_71
      | ~ r1_tarski(k1_relat_1(B_71),A_72)
      | ~ v1_relat_1(B_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_465,plain,
    ( k7_relat_1('#skF_4','#skF_3') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_377,c_456])).

tff(c_495,plain,(
    k7_relat_1('#skF_4','#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_465])).

tff(c_955,plain,(
    ! [A_94,B_95,C_96,D_97] :
      ( k5_relset_1(A_94,B_95,C_96,D_97) = k7_relat_1(C_96,D_97)
      | ~ m1_subset_1(C_96,k1_zfmisc_1(k2_zfmisc_1(A_94,B_95))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_958,plain,(
    ! [D_97] : k5_relset_1('#skF_2','#skF_1','#skF_4',D_97) = k7_relat_1('#skF_4',D_97) ),
    inference(resolution,[status(thm)],[c_36,c_955])).

tff(c_32,plain,(
    ~ r2_relset_1('#skF_2','#skF_1',k5_relset_1('#skF_2','#skF_1','#skF_4','#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_959,plain,(
    ~ r2_relset_1('#skF_2','#skF_1',k7_relat_1('#skF_4','#skF_3'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_958,c_32])).

tff(c_962,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_654,c_495,c_959])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:09:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.53/1.49  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.53/1.50  
% 2.53/1.50  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.53/1.50  %$ r2_relset_1 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k5_relset_1 > k7_relat_1 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.53/1.50  
% 2.53/1.50  %Foreground sorts:
% 2.53/1.50  
% 2.53/1.50  
% 2.53/1.50  %Background operators:
% 2.53/1.50  
% 2.53/1.50  
% 2.53/1.50  %Foreground operators:
% 2.53/1.50  tff(k5_relset_1, type, k5_relset_1: ($i * $i * $i * $i) > $i).
% 2.53/1.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.53/1.50  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 2.53/1.50  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.53/1.50  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.53/1.50  tff('#skF_2', type, '#skF_2': $i).
% 2.53/1.50  tff('#skF_3', type, '#skF_3': $i).
% 2.53/1.50  tff('#skF_1', type, '#skF_1': $i).
% 2.53/1.50  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.53/1.50  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.53/1.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.53/1.50  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.53/1.50  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.53/1.50  tff('#skF_4', type, '#skF_4': $i).
% 2.53/1.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.53/1.50  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.53/1.50  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.53/1.50  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.53/1.50  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.53/1.50  
% 2.81/1.51  tff(f_89, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A))) => (r1_tarski(B, C) => r2_relset_1(B, A, k5_relset_1(B, A, D, C), D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_relset_1)).
% 2.81/1.51  tff(f_82, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 2.81/1.51  tff(f_48, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.81/1.51  tff(f_46, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.81/1.51  tff(f_39, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.81/1.51  tff(f_70, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.81/1.51  tff(f_54, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 2.81/1.51  tff(f_58, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_relat_1)).
% 2.81/1.51  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.81/1.51  tff(f_35, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 2.81/1.51  tff(f_64, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_relat_1)).
% 2.81/1.51  tff(f_74, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k5_relset_1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k5_relset_1)).
% 2.81/1.51  tff(c_36, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.81/1.51  tff(c_651, plain, (![A_79, B_80, D_81]: (r2_relset_1(A_79, B_80, D_81, D_81) | ~m1_subset_1(D_81, k1_zfmisc_1(k2_zfmisc_1(A_79, B_80))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.81/1.51  tff(c_654, plain, (r2_relset_1('#skF_2', '#skF_1', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_36, c_651])).
% 2.81/1.51  tff(c_14, plain, (![A_11, B_12]: (v1_relat_1(k2_zfmisc_1(A_11, B_12)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.81/1.51  tff(c_67, plain, (![B_38, A_39]: (v1_relat_1(B_38) | ~m1_subset_1(B_38, k1_zfmisc_1(A_39)) | ~v1_relat_1(A_39))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.81/1.51  tff(c_70, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_36, c_67])).
% 2.81/1.51  tff(c_73, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_70])).
% 2.81/1.51  tff(c_34, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.81/1.51  tff(c_40, plain, (![A_33, B_34]: (k2_xboole_0(A_33, B_34)=B_34 | ~r1_tarski(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.81/1.51  tff(c_48, plain, (k2_xboole_0('#skF_2', '#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_34, c_40])).
% 2.81/1.51  tff(c_305, plain, (![C_61, A_62, B_63]: (v4_relat_1(C_61, A_62) | ~m1_subset_1(C_61, k1_zfmisc_1(k2_zfmisc_1(A_62, B_63))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.81/1.51  tff(c_309, plain, (v4_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_36, c_305])).
% 2.81/1.51  tff(c_16, plain, (![B_14, A_13]: (k7_relat_1(B_14, A_13)=B_14 | ~v4_relat_1(B_14, A_13) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.81/1.51  tff(c_312, plain, (k7_relat_1('#skF_4', '#skF_2')='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_309, c_16])).
% 2.81/1.51  tff(c_315, plain, (k7_relat_1('#skF_4', '#skF_2')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_73, c_312])).
% 2.81/1.51  tff(c_18, plain, (![B_16, A_15]: (r1_tarski(k1_relat_1(k7_relat_1(B_16, A_15)), A_15) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.81/1.51  tff(c_319, plain, (r1_tarski(k1_relat_1('#skF_4'), '#skF_2') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_315, c_18])).
% 2.81/1.51  tff(c_323, plain, (r1_tarski(k1_relat_1('#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_73, c_319])).
% 2.81/1.51  tff(c_10, plain, (![A_6, B_7]: (k2_xboole_0(A_6, B_7)=B_7 | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.81/1.51  tff(c_334, plain, (k2_xboole_0(k1_relat_1('#skF_4'), '#skF_2')='#skF_2'), inference(resolution, [status(thm)], [c_323, c_10])).
% 2.81/1.51  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.81/1.51  tff(c_88, plain, (![A_42, C_43, B_44]: (r1_tarski(A_42, C_43) | ~r1_tarski(k2_xboole_0(A_42, B_44), C_43))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.81/1.51  tff(c_101, plain, (![A_47, B_48]: (r1_tarski(A_47, k2_xboole_0(A_47, B_48)))), inference(resolution, [status(thm)], [c_6, c_88])).
% 2.81/1.51  tff(c_8, plain, (![A_3, C_5, B_4]: (r1_tarski(A_3, C_5) | ~r1_tarski(k2_xboole_0(A_3, B_4), C_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.81/1.51  tff(c_117, plain, (![A_3, B_4, B_48]: (r1_tarski(A_3, k2_xboole_0(k2_xboole_0(A_3, B_4), B_48)))), inference(resolution, [status(thm)], [c_101, c_8])).
% 2.81/1.51  tff(c_364, plain, (![B_65]: (r1_tarski(k1_relat_1('#skF_4'), k2_xboole_0('#skF_2', B_65)))), inference(superposition, [status(thm), theory('equality')], [c_334, c_117])).
% 2.81/1.51  tff(c_377, plain, (r1_tarski(k1_relat_1('#skF_4'), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_48, c_364])).
% 2.81/1.51  tff(c_456, plain, (![B_71, A_72]: (k7_relat_1(B_71, A_72)=B_71 | ~r1_tarski(k1_relat_1(B_71), A_72) | ~v1_relat_1(B_71))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.81/1.51  tff(c_465, plain, (k7_relat_1('#skF_4', '#skF_3')='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_377, c_456])).
% 2.81/1.51  tff(c_495, plain, (k7_relat_1('#skF_4', '#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_73, c_465])).
% 2.81/1.51  tff(c_955, plain, (![A_94, B_95, C_96, D_97]: (k5_relset_1(A_94, B_95, C_96, D_97)=k7_relat_1(C_96, D_97) | ~m1_subset_1(C_96, k1_zfmisc_1(k2_zfmisc_1(A_94, B_95))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.81/1.51  tff(c_958, plain, (![D_97]: (k5_relset_1('#skF_2', '#skF_1', '#skF_4', D_97)=k7_relat_1('#skF_4', D_97))), inference(resolution, [status(thm)], [c_36, c_955])).
% 2.81/1.51  tff(c_32, plain, (~r2_relset_1('#skF_2', '#skF_1', k5_relset_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.81/1.51  tff(c_959, plain, (~r2_relset_1('#skF_2', '#skF_1', k7_relat_1('#skF_4', '#skF_3'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_958, c_32])).
% 2.81/1.51  tff(c_962, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_654, c_495, c_959])).
% 2.81/1.51  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.81/1.51  
% 2.81/1.51  Inference rules
% 2.81/1.51  ----------------------
% 2.81/1.51  #Ref     : 0
% 2.81/1.51  #Sup     : 210
% 2.81/1.51  #Fact    : 0
% 2.81/1.51  #Define  : 0
% 2.81/1.51  #Split   : 4
% 2.81/1.51  #Chain   : 0
% 2.81/1.51  #Close   : 0
% 2.81/1.52  
% 2.81/1.52  Ordering : KBO
% 2.81/1.52  
% 2.81/1.52  Simplification rules
% 2.81/1.52  ----------------------
% 2.81/1.52  #Subsume      : 20
% 2.81/1.52  #Demod        : 112
% 2.81/1.52  #Tautology    : 120
% 2.81/1.52  #SimpNegUnit  : 0
% 2.81/1.52  #BackRed      : 1
% 2.81/1.52  
% 2.81/1.52  #Partial instantiations: 0
% 2.81/1.52  #Strategies tried      : 1
% 2.81/1.52  
% 2.81/1.52  Timing (in seconds)
% 2.81/1.52  ----------------------
% 2.81/1.52  Preprocessing        : 0.30
% 2.81/1.52  Parsing              : 0.16
% 2.81/1.52  CNF conversion       : 0.02
% 2.81/1.52  Main loop            : 0.34
% 2.81/1.52  Inferencing          : 0.12
% 2.81/1.52  Reduction            : 0.11
% 2.81/1.52  Demodulation         : 0.08
% 2.81/1.52  BG Simplification    : 0.02
% 2.81/1.52  Subsumption          : 0.07
% 2.81/1.52  Abstraction          : 0.02
% 2.81/1.52  MUC search           : 0.00
% 2.81/1.52  Cooper               : 0.00
% 2.81/1.52  Total                : 0.68
% 2.81/1.52  Index Insertion      : 0.00
% 2.81/1.52  Index Deletion       : 0.00
% 2.81/1.52  Index Matching       : 0.00
% 2.81/1.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
