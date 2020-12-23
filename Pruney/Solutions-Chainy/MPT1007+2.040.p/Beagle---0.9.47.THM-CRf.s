%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:16 EST 2020

% Result     : Theorem 3.09s
% Output     : CNFRefutation 3.26s
% Verified   : 
% Statistics : Number of formulae       :   64 (  79 expanded)
%              Number of leaves         :   39 (  48 expanded)
%              Depth                    :    7
%              Number of atoms          :   81 ( 130 expanded)
%              Number of equality atoms :   26 (  34 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_140,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_tarski(A),B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r2_hidden(k1_funct_1(C,A),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_2)).

tff(f_100,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_106,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_110,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_128,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_96,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( k1_relat_1(B) = k1_tarski(A)
       => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_27,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(c_68,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_101,plain,(
    ! [C_68,A_69,B_70] :
      ( v1_relat_1(C_68)
      | ~ m1_subset_1(C_68,k1_zfmisc_1(k2_zfmisc_1(A_69,B_70))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_110,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_101])).

tff(c_126,plain,(
    ! [C_82,B_83,A_84] :
      ( v5_relat_1(C_82,B_83)
      | ~ m1_subset_1(C_82,k1_zfmisc_1(k2_zfmisc_1(A_84,B_83))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_135,plain,(
    v5_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_68,c_126])).

tff(c_30,plain,(
    ! [B_39,A_38] :
      ( r1_tarski(k2_relat_1(B_39),A_38)
      | ~ v5_relat_1(B_39,A_38)
      | ~ v1_relat_1(B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_72,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_66,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_70,plain,(
    v1_funct_2('#skF_3',k1_tarski('#skF_1'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_261,plain,(
    ! [A_135,B_136,C_137] :
      ( k1_relset_1(A_135,B_136,C_137) = k1_relat_1(C_137)
      | ~ m1_subset_1(C_137,k1_zfmisc_1(k2_zfmisc_1(A_135,B_136))) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_270,plain,(
    k1_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_261])).

tff(c_454,plain,(
    ! [B_193,A_194,C_195] :
      ( k1_xboole_0 = B_193
      | k1_relset_1(A_194,B_193,C_195) = A_194
      | ~ v1_funct_2(C_195,A_194,B_193)
      | ~ m1_subset_1(C_195,k1_zfmisc_1(k2_zfmisc_1(A_194,B_193))) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_461,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_3') = k1_tarski('#skF_1')
    | ~ v1_funct_2('#skF_3',k1_tarski('#skF_1'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_68,c_454])).

tff(c_465,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_tarski('#skF_1') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_270,c_461])).

tff(c_466,plain,(
    k1_tarski('#skF_1') = k1_relat_1('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_465])).

tff(c_306,plain,(
    ! [B_149,A_150] :
      ( k1_tarski(k1_funct_1(B_149,A_150)) = k2_relat_1(B_149)
      | k1_tarski(A_150) != k1_relat_1(B_149)
      | ~ v1_funct_1(B_149)
      | ~ v1_relat_1(B_149) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_2,plain,(
    ! [A_1] : k2_tarski(A_1,A_1) = k1_tarski(A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_117,plain,(
    ! [B_74,C_75,A_76] :
      ( r2_hidden(B_74,C_75)
      | ~ r1_tarski(k2_tarski(A_76,B_74),C_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_120,plain,(
    ! [A_1,C_75] :
      ( r2_hidden(A_1,C_75)
      | ~ r1_tarski(k1_tarski(A_1),C_75) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_117])).

tff(c_733,plain,(
    ! [B_236,A_237,C_238] :
      ( r2_hidden(k1_funct_1(B_236,A_237),C_238)
      | ~ r1_tarski(k2_relat_1(B_236),C_238)
      | k1_tarski(A_237) != k1_relat_1(B_236)
      | ~ v1_funct_1(B_236)
      | ~ v1_relat_1(B_236) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_306,c_120])).

tff(c_64,plain,(
    ~ r2_hidden(k1_funct_1('#skF_3','#skF_1'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_761,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_3'),'#skF_2')
    | k1_tarski('#skF_1') != k1_relat_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_733,c_64])).

tff(c_772,plain,(
    ~ r1_tarski(k2_relat_1('#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_72,c_466,c_761])).

tff(c_775,plain,
    ( ~ v5_relat_1('#skF_3','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_772])).

tff(c_779,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_135,c_775])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n002.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:17:21 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.09/1.46  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.09/1.46  
% 3.09/1.46  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.09/1.47  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.09/1.47  
% 3.09/1.47  %Foreground sorts:
% 3.09/1.47  
% 3.09/1.47  
% 3.09/1.47  %Background operators:
% 3.09/1.47  
% 3.09/1.47  
% 3.09/1.47  %Foreground operators:
% 3.09/1.47  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.09/1.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.09/1.47  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.09/1.47  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.09/1.47  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.09/1.47  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.09/1.47  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.09/1.47  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.09/1.47  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.09/1.47  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.09/1.47  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.09/1.47  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.09/1.47  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.09/1.47  tff('#skF_2', type, '#skF_2': $i).
% 3.09/1.47  tff('#skF_3', type, '#skF_3': $i).
% 3.09/1.47  tff('#skF_1', type, '#skF_1': $i).
% 3.09/1.47  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.09/1.47  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.09/1.47  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.09/1.47  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.09/1.47  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.09/1.47  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.09/1.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.09/1.47  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.09/1.47  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.09/1.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.09/1.47  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.09/1.47  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.09/1.47  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.09/1.47  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.09/1.47  
% 3.26/1.48  tff(f_140, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_tarski(A), B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r2_hidden(k1_funct_1(C, A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_2)).
% 3.26/1.48  tff(f_100, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.26/1.48  tff(f_106, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.26/1.48  tff(f_62, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 3.26/1.48  tff(f_110, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.26/1.48  tff(f_128, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 3.26/1.48  tff(f_96, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_funct_1)).
% 3.26/1.48  tff(f_27, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 3.26/1.48  tff(f_45, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 3.26/1.48  tff(c_68, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_140])).
% 3.26/1.48  tff(c_101, plain, (![C_68, A_69, B_70]: (v1_relat_1(C_68) | ~m1_subset_1(C_68, k1_zfmisc_1(k2_zfmisc_1(A_69, B_70))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.26/1.48  tff(c_110, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_101])).
% 3.26/1.48  tff(c_126, plain, (![C_82, B_83, A_84]: (v5_relat_1(C_82, B_83) | ~m1_subset_1(C_82, k1_zfmisc_1(k2_zfmisc_1(A_84, B_83))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.26/1.48  tff(c_135, plain, (v5_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_68, c_126])).
% 3.26/1.48  tff(c_30, plain, (![B_39, A_38]: (r1_tarski(k2_relat_1(B_39), A_38) | ~v5_relat_1(B_39, A_38) | ~v1_relat_1(B_39))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.26/1.48  tff(c_72, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_140])).
% 3.26/1.48  tff(c_66, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_140])).
% 3.26/1.48  tff(c_70, plain, (v1_funct_2('#skF_3', k1_tarski('#skF_1'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_140])).
% 3.26/1.48  tff(c_261, plain, (![A_135, B_136, C_137]: (k1_relset_1(A_135, B_136, C_137)=k1_relat_1(C_137) | ~m1_subset_1(C_137, k1_zfmisc_1(k2_zfmisc_1(A_135, B_136))))), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.26/1.48  tff(c_270, plain, (k1_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_261])).
% 3.26/1.48  tff(c_454, plain, (![B_193, A_194, C_195]: (k1_xboole_0=B_193 | k1_relset_1(A_194, B_193, C_195)=A_194 | ~v1_funct_2(C_195, A_194, B_193) | ~m1_subset_1(C_195, k1_zfmisc_1(k2_zfmisc_1(A_194, B_193))))), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.26/1.48  tff(c_461, plain, (k1_xboole_0='#skF_2' | k1_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_3')=k1_tarski('#skF_1') | ~v1_funct_2('#skF_3', k1_tarski('#skF_1'), '#skF_2')), inference(resolution, [status(thm)], [c_68, c_454])).
% 3.26/1.48  tff(c_465, plain, (k1_xboole_0='#skF_2' | k1_tarski('#skF_1')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_270, c_461])).
% 3.26/1.48  tff(c_466, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_66, c_465])).
% 3.26/1.48  tff(c_306, plain, (![B_149, A_150]: (k1_tarski(k1_funct_1(B_149, A_150))=k2_relat_1(B_149) | k1_tarski(A_150)!=k1_relat_1(B_149) | ~v1_funct_1(B_149) | ~v1_relat_1(B_149))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.26/1.48  tff(c_2, plain, (![A_1]: (k2_tarski(A_1, A_1)=k1_tarski(A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.26/1.48  tff(c_117, plain, (![B_74, C_75, A_76]: (r2_hidden(B_74, C_75) | ~r1_tarski(k2_tarski(A_76, B_74), C_75))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.26/1.48  tff(c_120, plain, (![A_1, C_75]: (r2_hidden(A_1, C_75) | ~r1_tarski(k1_tarski(A_1), C_75))), inference(superposition, [status(thm), theory('equality')], [c_2, c_117])).
% 3.26/1.48  tff(c_733, plain, (![B_236, A_237, C_238]: (r2_hidden(k1_funct_1(B_236, A_237), C_238) | ~r1_tarski(k2_relat_1(B_236), C_238) | k1_tarski(A_237)!=k1_relat_1(B_236) | ~v1_funct_1(B_236) | ~v1_relat_1(B_236))), inference(superposition, [status(thm), theory('equality')], [c_306, c_120])).
% 3.26/1.48  tff(c_64, plain, (~r2_hidden(k1_funct_1('#skF_3', '#skF_1'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_140])).
% 3.26/1.48  tff(c_761, plain, (~r1_tarski(k2_relat_1('#skF_3'), '#skF_2') | k1_tarski('#skF_1')!=k1_relat_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_733, c_64])).
% 3.26/1.48  tff(c_772, plain, (~r1_tarski(k2_relat_1('#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_110, c_72, c_466, c_761])).
% 3.26/1.48  tff(c_775, plain, (~v5_relat_1('#skF_3', '#skF_2') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_30, c_772])).
% 3.26/1.48  tff(c_779, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_110, c_135, c_775])).
% 3.26/1.48  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.26/1.48  
% 3.26/1.48  Inference rules
% 3.26/1.48  ----------------------
% 3.26/1.48  #Ref     : 0
% 3.26/1.48  #Sup     : 143
% 3.26/1.48  #Fact    : 0
% 3.26/1.48  #Define  : 0
% 3.26/1.48  #Split   : 1
% 3.26/1.48  #Chain   : 0
% 3.26/1.48  #Close   : 0
% 3.26/1.48  
% 3.26/1.48  Ordering : KBO
% 3.26/1.48  
% 3.26/1.48  Simplification rules
% 3.26/1.48  ----------------------
% 3.26/1.48  #Subsume      : 14
% 3.26/1.48  #Demod        : 40
% 3.26/1.48  #Tautology    : 49
% 3.26/1.48  #SimpNegUnit  : 6
% 3.26/1.48  #BackRed      : 5
% 3.26/1.48  
% 3.26/1.48  #Partial instantiations: 0
% 3.26/1.48  #Strategies tried      : 1
% 3.26/1.48  
% 3.26/1.48  Timing (in seconds)
% 3.26/1.48  ----------------------
% 3.26/1.48  Preprocessing        : 0.36
% 3.26/1.48  Parsing              : 0.19
% 3.26/1.48  CNF conversion       : 0.02
% 3.26/1.48  Main loop            : 0.36
% 3.26/1.48  Inferencing          : 0.14
% 3.26/1.48  Reduction            : 0.10
% 3.26/1.48  Demodulation         : 0.07
% 3.26/1.48  BG Simplification    : 0.03
% 3.26/1.48  Subsumption          : 0.06
% 3.26/1.48  Abstraction          : 0.02
% 3.26/1.48  MUC search           : 0.00
% 3.26/1.48  Cooper               : 0.00
% 3.26/1.48  Total                : 0.75
% 3.26/1.48  Index Insertion      : 0.00
% 3.26/1.48  Index Deletion       : 0.00
% 3.26/1.48  Index Matching       : 0.00
% 3.26/1.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
