%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:43 EST 2020

% Result     : Theorem 4.18s
% Output     : CNFRefutation 4.18s
% Verified   : 
% Statistics : Number of formulae       :   66 (  93 expanded)
%              Number of leaves         :   35 (  49 expanded)
%              Depth                    :   11
%              Number of atoms          :   91 ( 187 expanded)
%              Number of equality atoms :   24 (  38 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k6_subset_1 > k4_xboole_0 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_137,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( k1_relset_1(A,B,C) = A
         => ( v1_funct_1(C)
            & v1_funct_2(C,A,B)
            & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t130_funct_2)).

tff(f_86,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_92,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_82,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_114,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( ( B = k1_xboole_0
           => A = k1_xboole_0 )
         => ( v1_funct_2(C,A,B)
          <=> A = k1_relset_1(A,B,C) ) )
        & ( B = k1_xboole_0
         => ( A = k1_xboole_0
            | ( v1_funct_2(C,A,B)
            <=> C = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_59,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_39,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_96,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_124,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

tff(c_68,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_66,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_62,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_70,plain,(
    ~ v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_62])).

tff(c_221,plain,(
    ! [C_62,A_63,B_64] :
      ( v1_relat_1(C_62)
      | ~ m1_subset_1(C_62,k1_zfmisc_1(k2_zfmisc_1(A_63,B_64))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_238,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_66,c_221])).

tff(c_338,plain,(
    ! [C_76,B_77,A_78] :
      ( v5_relat_1(C_76,B_77)
      | ~ m1_subset_1(C_76,k1_zfmisc_1(k2_zfmisc_1(A_78,B_77))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_355,plain,(
    v5_relat_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_338])).

tff(c_34,plain,(
    ! [B_24,A_23] :
      ( r1_tarski(k2_relat_1(B_24),A_23)
      | ~ v5_relat_1(B_24,A_23)
      | ~ v1_relat_1(B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_64,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_1781,plain,(
    ! [B_212,C_213,A_214] :
      ( k1_xboole_0 = B_212
      | v1_funct_2(C_213,A_214,B_212)
      | k1_relset_1(A_214,B_212,C_213) != A_214
      | ~ m1_subset_1(C_213,k1_zfmisc_1(k2_zfmisc_1(A_214,B_212))) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_1802,plain,
    ( k1_xboole_0 = '#skF_3'
    | v1_funct_2('#skF_4','#skF_2','#skF_3')
    | k1_relset_1('#skF_2','#skF_3','#skF_4') != '#skF_2' ),
    inference(resolution,[status(thm)],[c_66,c_1781])).

tff(c_1820,plain,
    ( k1_xboole_0 = '#skF_3'
    | v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_1802])).

tff(c_1821,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_1820])).

tff(c_22,plain,(
    ! [A_14] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_14)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_116,plain,(
    ! [A_54,B_55] :
      ( r1_tarski(A_54,B_55)
      | ~ m1_subset_1(A_54,k1_zfmisc_1(B_55)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_132,plain,(
    ! [A_14] : r1_tarski(k1_xboole_0,A_14) ),
    inference(resolution,[status(thm)],[c_22,c_116])).

tff(c_1896,plain,(
    ! [A_217] : r1_tarski('#skF_3',A_217) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1821,c_132])).

tff(c_4,plain,(
    ! [B_4,A_3] :
      ( B_4 = A_3
      | ~ r1_tarski(B_4,A_3)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2129,plain,(
    ! [A_226] :
      ( A_226 = '#skF_3'
      | ~ r1_tarski(A_226,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_1896,c_4])).

tff(c_2626,plain,(
    ! [B_263] :
      ( k2_relat_1(B_263) = '#skF_3'
      | ~ v5_relat_1(B_263,'#skF_3')
      | ~ v1_relat_1(B_263) ) ),
    inference(resolution,[status(thm)],[c_34,c_2129])).

tff(c_2649,plain,
    ( k2_relat_1('#skF_4') = '#skF_3'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_355,c_2626])).

tff(c_2667,plain,(
    k2_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_238,c_2649])).

tff(c_843,plain,(
    ! [A_147,B_148,C_149] :
      ( k1_relset_1(A_147,B_148,C_149) = k1_relat_1(C_149)
      | ~ m1_subset_1(C_149,k1_zfmisc_1(k2_zfmisc_1(A_147,B_148))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_850,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_66,c_843])).

tff(c_861,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_850])).

tff(c_58,plain,(
    ! [A_37] :
      ( v1_funct_2(A_37,k1_relat_1(A_37),k2_relat_1(A_37))
      | ~ v1_funct_1(A_37)
      | ~ v1_relat_1(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_867,plain,
    ( v1_funct_2('#skF_4','#skF_2',k2_relat_1('#skF_4'))
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_861,c_58])).

tff(c_871,plain,(
    v1_funct_2('#skF_4','#skF_2',k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_238,c_68,c_867])).

tff(c_2690,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2667,c_871])).

tff(c_2697,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_2690])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:00:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.18/1.71  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.18/1.72  
% 4.18/1.72  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.18/1.72  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k6_subset_1 > k4_xboole_0 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 4.18/1.72  
% 4.18/1.72  %Foreground sorts:
% 4.18/1.72  
% 4.18/1.72  
% 4.18/1.72  %Background operators:
% 4.18/1.72  
% 4.18/1.72  
% 4.18/1.72  %Foreground operators:
% 4.18/1.72  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.18/1.72  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.18/1.72  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.18/1.72  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.18/1.72  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.18/1.72  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.18/1.72  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.18/1.72  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.18/1.72  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.18/1.72  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.18/1.72  tff('#skF_2', type, '#skF_2': $i).
% 4.18/1.72  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 4.18/1.72  tff('#skF_3', type, '#skF_3': $i).
% 4.18/1.72  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.18/1.72  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.18/1.72  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.18/1.72  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.18/1.72  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.18/1.72  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.18/1.72  tff('#skF_4', type, '#skF_4': $i).
% 4.18/1.72  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.18/1.72  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.18/1.72  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.18/1.72  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.18/1.72  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.18/1.72  
% 4.18/1.73  tff(f_137, negated_conjecture, ~(![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((k1_relset_1(A, B, C) = A) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t130_funct_2)).
% 4.18/1.73  tff(f_86, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.18/1.73  tff(f_92, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.18/1.73  tff(f_82, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 4.18/1.73  tff(f_114, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 4.18/1.73  tff(f_59, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 4.18/1.73  tff(f_63, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 4.18/1.73  tff(f_39, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.18/1.73  tff(f_96, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.18/1.73  tff(f_124, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_funct_2)).
% 4.18/1.73  tff(c_68, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_137])).
% 4.18/1.73  tff(c_66, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_137])).
% 4.18/1.73  tff(c_62, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_137])).
% 4.18/1.73  tff(c_70, plain, (~v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_62])).
% 4.18/1.73  tff(c_221, plain, (![C_62, A_63, B_64]: (v1_relat_1(C_62) | ~m1_subset_1(C_62, k1_zfmisc_1(k2_zfmisc_1(A_63, B_64))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.18/1.73  tff(c_238, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_66, c_221])).
% 4.18/1.73  tff(c_338, plain, (![C_76, B_77, A_78]: (v5_relat_1(C_76, B_77) | ~m1_subset_1(C_76, k1_zfmisc_1(k2_zfmisc_1(A_78, B_77))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.18/1.73  tff(c_355, plain, (v5_relat_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_66, c_338])).
% 4.18/1.73  tff(c_34, plain, (![B_24, A_23]: (r1_tarski(k2_relat_1(B_24), A_23) | ~v5_relat_1(B_24, A_23) | ~v1_relat_1(B_24))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.18/1.73  tff(c_64, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_137])).
% 4.18/1.73  tff(c_1781, plain, (![B_212, C_213, A_214]: (k1_xboole_0=B_212 | v1_funct_2(C_213, A_214, B_212) | k1_relset_1(A_214, B_212, C_213)!=A_214 | ~m1_subset_1(C_213, k1_zfmisc_1(k2_zfmisc_1(A_214, B_212))))), inference(cnfTransformation, [status(thm)], [f_114])).
% 4.18/1.73  tff(c_1802, plain, (k1_xboole_0='#skF_3' | v1_funct_2('#skF_4', '#skF_2', '#skF_3') | k1_relset_1('#skF_2', '#skF_3', '#skF_4')!='#skF_2'), inference(resolution, [status(thm)], [c_66, c_1781])).
% 4.18/1.73  tff(c_1820, plain, (k1_xboole_0='#skF_3' | v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_1802])).
% 4.18/1.73  tff(c_1821, plain, (k1_xboole_0='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_70, c_1820])).
% 4.18/1.73  tff(c_22, plain, (![A_14]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_14)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.18/1.73  tff(c_116, plain, (![A_54, B_55]: (r1_tarski(A_54, B_55) | ~m1_subset_1(A_54, k1_zfmisc_1(B_55)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.18/1.73  tff(c_132, plain, (![A_14]: (r1_tarski(k1_xboole_0, A_14))), inference(resolution, [status(thm)], [c_22, c_116])).
% 4.18/1.73  tff(c_1896, plain, (![A_217]: (r1_tarski('#skF_3', A_217))), inference(demodulation, [status(thm), theory('equality')], [c_1821, c_132])).
% 4.18/1.73  tff(c_4, plain, (![B_4, A_3]: (B_4=A_3 | ~r1_tarski(B_4, A_3) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.18/1.73  tff(c_2129, plain, (![A_226]: (A_226='#skF_3' | ~r1_tarski(A_226, '#skF_3'))), inference(resolution, [status(thm)], [c_1896, c_4])).
% 4.18/1.73  tff(c_2626, plain, (![B_263]: (k2_relat_1(B_263)='#skF_3' | ~v5_relat_1(B_263, '#skF_3') | ~v1_relat_1(B_263))), inference(resolution, [status(thm)], [c_34, c_2129])).
% 4.18/1.73  tff(c_2649, plain, (k2_relat_1('#skF_4')='#skF_3' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_355, c_2626])).
% 4.18/1.73  tff(c_2667, plain, (k2_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_238, c_2649])).
% 4.18/1.73  tff(c_843, plain, (![A_147, B_148, C_149]: (k1_relset_1(A_147, B_148, C_149)=k1_relat_1(C_149) | ~m1_subset_1(C_149, k1_zfmisc_1(k2_zfmisc_1(A_147, B_148))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.18/1.73  tff(c_850, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_66, c_843])).
% 4.18/1.73  tff(c_861, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_850])).
% 4.18/1.73  tff(c_58, plain, (![A_37]: (v1_funct_2(A_37, k1_relat_1(A_37), k2_relat_1(A_37)) | ~v1_funct_1(A_37) | ~v1_relat_1(A_37))), inference(cnfTransformation, [status(thm)], [f_124])).
% 4.18/1.73  tff(c_867, plain, (v1_funct_2('#skF_4', '#skF_2', k2_relat_1('#skF_4')) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_861, c_58])).
% 4.18/1.73  tff(c_871, plain, (v1_funct_2('#skF_4', '#skF_2', k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_238, c_68, c_867])).
% 4.18/1.73  tff(c_2690, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2667, c_871])).
% 4.18/1.73  tff(c_2697, plain, $false, inference(negUnitSimplification, [status(thm)], [c_70, c_2690])).
% 4.18/1.73  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.18/1.73  
% 4.18/1.73  Inference rules
% 4.18/1.73  ----------------------
% 4.18/1.73  #Ref     : 0
% 4.18/1.73  #Sup     : 540
% 4.18/1.73  #Fact    : 0
% 4.18/1.73  #Define  : 0
% 4.18/1.73  #Split   : 7
% 4.18/1.73  #Chain   : 0
% 4.18/1.73  #Close   : 0
% 4.18/1.73  
% 4.18/1.73  Ordering : KBO
% 4.18/1.73  
% 4.18/1.73  Simplification rules
% 4.18/1.73  ----------------------
% 4.18/1.73  #Subsume      : 92
% 4.18/1.73  #Demod        : 458
% 4.18/1.73  #Tautology    : 280
% 4.18/1.73  #SimpNegUnit  : 3
% 4.18/1.73  #BackRed      : 73
% 4.18/1.73  
% 4.18/1.73  #Partial instantiations: 0
% 4.18/1.73  #Strategies tried      : 1
% 4.18/1.73  
% 4.18/1.73  Timing (in seconds)
% 4.18/1.73  ----------------------
% 4.18/1.73  Preprocessing        : 0.33
% 4.18/1.73  Parsing              : 0.18
% 4.18/1.73  CNF conversion       : 0.02
% 4.18/1.73  Main loop            : 0.63
% 4.18/1.73  Inferencing          : 0.21
% 4.18/1.73  Reduction            : 0.23
% 4.18/1.73  Demodulation         : 0.17
% 4.18/1.73  BG Simplification    : 0.03
% 4.18/1.73  Subsumption          : 0.11
% 4.18/1.73  Abstraction          : 0.03
% 4.18/1.73  MUC search           : 0.00
% 4.18/1.73  Cooper               : 0.00
% 4.18/1.73  Total                : 0.99
% 4.18/1.73  Index Insertion      : 0.00
% 4.18/1.73  Index Deletion       : 0.00
% 4.18/1.73  Index Matching       : 0.00
% 4.18/1.73  BG Taut test         : 0.00
%------------------------------------------------------------------------------
