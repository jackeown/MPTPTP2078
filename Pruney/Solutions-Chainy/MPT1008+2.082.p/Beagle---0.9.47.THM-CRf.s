%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:37 EST 2020

% Result     : Theorem 2.08s
% Output     : CNFRefutation 2.29s
% Verified   : 
% Statistics : Number of formulae       :   63 (  87 expanded)
%              Number of leaves         :   34 (  47 expanded)
%              Depth                    :    8
%              Number of atoms          :   79 ( 151 expanded)
%              Number of equality atoms :   44 (  69 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > m1_subset_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k2_enumset1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

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

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_97,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_tarski(A),B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => k2_relset_1(k1_tarski(A),B,C) = k1_tarski(k1_funct_1(C,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_funct_2)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( k1_relat_1(B) = k1_tarski(A)
       => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_85,axiom,(
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

tff(f_55,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( k7_relset_1(A,B,C,A) = k2_relset_1(A,B,C)
        & k8_relset_1(A,B,C,B) = k1_relset_1(A,B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_relset_1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
     => ( k7_relset_1(B,A,C,k8_relset_1(B,A,C,A)) = k2_relset_1(B,A,C)
        & k8_relset_1(B,A,C,k7_relset_1(B,A,C,B)) = k1_relset_1(B,A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_relset_1)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

tff(c_42,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_65,plain,(
    ! [C_32,A_33,B_34] :
      ( v1_relat_1(C_32)
      | ~ m1_subset_1(C_32,k1_zfmisc_1(k2_zfmisc_1(A_33,B_34))) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_69,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_65])).

tff(c_46,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_99,plain,(
    ! [B_43,A_44] :
      ( k1_tarski(k1_funct_1(B_43,A_44)) = k2_relat_1(B_43)
      | k1_tarski(A_44) != k1_relat_1(B_43)
      | ~ v1_funct_1(B_43)
      | ~ v1_relat_1(B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_89,plain,(
    ! [A_40,B_41,C_42] :
      ( k2_relset_1(A_40,B_41,C_42) = k2_relat_1(C_42)
      | ~ m1_subset_1(C_42,k1_zfmisc_1(k2_zfmisc_1(A_40,B_41))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_93,plain,(
    k2_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_89])).

tff(c_38,plain,(
    k2_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_3') != k1_tarski(k1_funct_1('#skF_3','#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_94,plain,(
    k1_tarski(k1_funct_1('#skF_3','#skF_1')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_38])).

tff(c_105,plain,
    ( k1_tarski('#skF_1') != k1_relat_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_99,c_94])).

tff(c_112,plain,(
    k1_tarski('#skF_1') != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_46,c_105])).

tff(c_40,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_44,plain,(
    v1_funct_2('#skF_3',k1_tarski('#skF_1'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_144,plain,(
    ! [B_62,A_63,C_64] :
      ( k1_xboole_0 = B_62
      | k1_relset_1(A_63,B_62,C_64) = A_63
      | ~ v1_funct_2(C_64,A_63,B_62)
      | ~ m1_subset_1(C_64,k1_zfmisc_1(k2_zfmisc_1(A_63,B_62))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_147,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_3') = k1_tarski('#skF_1')
    | ~ v1_funct_2('#skF_3',k1_tarski('#skF_1'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_144])).

tff(c_150,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_3') = k1_tarski('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_147])).

tff(c_151,plain,(
    k1_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_3') = k1_tarski('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_150])).

tff(c_114,plain,(
    ! [A_45,B_46,C_47,D_48] :
      ( k8_relset_1(A_45,B_46,C_47,D_48) = k10_relat_1(C_47,D_48)
      | ~ m1_subset_1(C_47,k1_zfmisc_1(k2_zfmisc_1(A_45,B_46))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_117,plain,(
    ! [D_48] : k8_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_3',D_48) = k10_relat_1('#skF_3',D_48) ),
    inference(resolution,[status(thm)],[c_42,c_114])).

tff(c_130,plain,(
    ! [A_56,B_57,C_58] :
      ( k7_relset_1(A_56,B_57,C_58,A_56) = k2_relset_1(A_56,B_57,C_58)
      | ~ m1_subset_1(C_58,k1_zfmisc_1(k2_zfmisc_1(A_56,B_57))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_132,plain,(
    k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_3',k1_tarski('#skF_1')) = k2_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_130])).

tff(c_134,plain,(
    k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_3',k1_tarski('#skF_1')) = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_132])).

tff(c_174,plain,(
    ! [B_71,A_72,C_73] :
      ( k8_relset_1(B_71,A_72,C_73,k7_relset_1(B_71,A_72,C_73,B_71)) = k1_relset_1(B_71,A_72,C_73)
      | ~ m1_subset_1(C_73,k1_zfmisc_1(k2_zfmisc_1(B_71,A_72))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_176,plain,(
    k8_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_3',k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_3',k1_tarski('#skF_1'))) = k1_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_174])).

tff(c_178,plain,(
    k10_relat_1('#skF_3',k2_relat_1('#skF_3')) = k1_tarski('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_151,c_117,c_134,c_176])).

tff(c_8,plain,(
    ! [A_7] :
      ( k10_relat_1(A_7,k2_relat_1(A_7)) = k1_relat_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_182,plain,
    ( k1_tarski('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_178,c_8])).

tff(c_189,plain,(
    k1_tarski('#skF_1') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_182])).

tff(c_191,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_112,c_189])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:59:53 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.08/1.36  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.29/1.37  
% 2.29/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.29/1.37  %$ v1_funct_2 > m1_subset_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k2_enumset1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.29/1.37  
% 2.29/1.37  %Foreground sorts:
% 2.29/1.37  
% 2.29/1.37  
% 2.29/1.37  %Background operators:
% 2.29/1.37  
% 2.29/1.37  
% 2.29/1.37  %Foreground operators:
% 2.29/1.37  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.29/1.37  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.29/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.29/1.37  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.29/1.37  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 2.29/1.37  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.29/1.37  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.29/1.37  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.29/1.37  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.29/1.37  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.29/1.37  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.29/1.37  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.29/1.37  tff('#skF_2', type, '#skF_2': $i).
% 2.29/1.37  tff('#skF_3', type, '#skF_3': $i).
% 2.29/1.37  tff('#skF_1', type, '#skF_1': $i).
% 2.29/1.37  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.29/1.37  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.29/1.37  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.29/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.29/1.37  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.29/1.37  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.29/1.37  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.29/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.29/1.37  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.29/1.37  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.29/1.37  
% 2.29/1.39  tff(f_97, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_tarski(A), B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => (k2_relset_1(k1_tarski(A), B, C) = k1_tarski(k1_funct_1(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_funct_2)).
% 2.29/1.39  tff(f_47, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.29/1.39  tff(f_43, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_funct_1)).
% 2.29/1.39  tff(f_51, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.29/1.39  tff(f_85, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 2.29/1.39  tff(f_55, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 2.29/1.39  tff(f_61, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((k7_relset_1(A, B, C, A) = k2_relset_1(A, B, C)) & (k8_relset_1(A, B, C, B) = k1_relset_1(A, B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_relset_1)).
% 2.29/1.39  tff(f_67, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => ((k7_relset_1(B, A, C, k8_relset_1(B, A, C, A)) = k2_relset_1(B, A, C)) & (k8_relset_1(B, A, C, k7_relset_1(B, A, C, B)) = k1_relset_1(B, A, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_relset_1)).
% 2.29/1.39  tff(f_35, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_relat_1)).
% 2.29/1.39  tff(c_42, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.29/1.39  tff(c_65, plain, (![C_32, A_33, B_34]: (v1_relat_1(C_32) | ~m1_subset_1(C_32, k1_zfmisc_1(k2_zfmisc_1(A_33, B_34))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.29/1.39  tff(c_69, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_42, c_65])).
% 2.29/1.39  tff(c_46, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.29/1.39  tff(c_99, plain, (![B_43, A_44]: (k1_tarski(k1_funct_1(B_43, A_44))=k2_relat_1(B_43) | k1_tarski(A_44)!=k1_relat_1(B_43) | ~v1_funct_1(B_43) | ~v1_relat_1(B_43))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.29/1.39  tff(c_89, plain, (![A_40, B_41, C_42]: (k2_relset_1(A_40, B_41, C_42)=k2_relat_1(C_42) | ~m1_subset_1(C_42, k1_zfmisc_1(k2_zfmisc_1(A_40, B_41))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.29/1.39  tff(c_93, plain, (k2_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_42, c_89])).
% 2.29/1.39  tff(c_38, plain, (k2_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_3')!=k1_tarski(k1_funct_1('#skF_3', '#skF_1'))), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.29/1.39  tff(c_94, plain, (k1_tarski(k1_funct_1('#skF_3', '#skF_1'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_93, c_38])).
% 2.29/1.39  tff(c_105, plain, (k1_tarski('#skF_1')!=k1_relat_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_99, c_94])).
% 2.29/1.39  tff(c_112, plain, (k1_tarski('#skF_1')!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_69, c_46, c_105])).
% 2.29/1.39  tff(c_40, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.29/1.39  tff(c_44, plain, (v1_funct_2('#skF_3', k1_tarski('#skF_1'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.29/1.39  tff(c_144, plain, (![B_62, A_63, C_64]: (k1_xboole_0=B_62 | k1_relset_1(A_63, B_62, C_64)=A_63 | ~v1_funct_2(C_64, A_63, B_62) | ~m1_subset_1(C_64, k1_zfmisc_1(k2_zfmisc_1(A_63, B_62))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.29/1.39  tff(c_147, plain, (k1_xboole_0='#skF_2' | k1_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_3')=k1_tarski('#skF_1') | ~v1_funct_2('#skF_3', k1_tarski('#skF_1'), '#skF_2')), inference(resolution, [status(thm)], [c_42, c_144])).
% 2.29/1.39  tff(c_150, plain, (k1_xboole_0='#skF_2' | k1_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_3')=k1_tarski('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_147])).
% 2.29/1.39  tff(c_151, plain, (k1_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_3')=k1_tarski('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_40, c_150])).
% 2.29/1.39  tff(c_114, plain, (![A_45, B_46, C_47, D_48]: (k8_relset_1(A_45, B_46, C_47, D_48)=k10_relat_1(C_47, D_48) | ~m1_subset_1(C_47, k1_zfmisc_1(k2_zfmisc_1(A_45, B_46))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.29/1.39  tff(c_117, plain, (![D_48]: (k8_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_3', D_48)=k10_relat_1('#skF_3', D_48))), inference(resolution, [status(thm)], [c_42, c_114])).
% 2.29/1.39  tff(c_130, plain, (![A_56, B_57, C_58]: (k7_relset_1(A_56, B_57, C_58, A_56)=k2_relset_1(A_56, B_57, C_58) | ~m1_subset_1(C_58, k1_zfmisc_1(k2_zfmisc_1(A_56, B_57))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.29/1.39  tff(c_132, plain, (k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_3', k1_tarski('#skF_1'))=k2_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_42, c_130])).
% 2.29/1.39  tff(c_134, plain, (k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_3', k1_tarski('#skF_1'))=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_93, c_132])).
% 2.29/1.39  tff(c_174, plain, (![B_71, A_72, C_73]: (k8_relset_1(B_71, A_72, C_73, k7_relset_1(B_71, A_72, C_73, B_71))=k1_relset_1(B_71, A_72, C_73) | ~m1_subset_1(C_73, k1_zfmisc_1(k2_zfmisc_1(B_71, A_72))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.29/1.39  tff(c_176, plain, (k8_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_3', k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_3', k1_tarski('#skF_1')))=k1_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_42, c_174])).
% 2.29/1.39  tff(c_178, plain, (k10_relat_1('#skF_3', k2_relat_1('#skF_3'))=k1_tarski('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_151, c_117, c_134, c_176])).
% 2.29/1.39  tff(c_8, plain, (![A_7]: (k10_relat_1(A_7, k2_relat_1(A_7))=k1_relat_1(A_7) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.29/1.39  tff(c_182, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_178, c_8])).
% 2.29/1.39  tff(c_189, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_69, c_182])).
% 2.29/1.39  tff(c_191, plain, $false, inference(negUnitSimplification, [status(thm)], [c_112, c_189])).
% 2.29/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.29/1.39  
% 2.29/1.39  Inference rules
% 2.29/1.39  ----------------------
% 2.29/1.39  #Ref     : 0
% 2.29/1.39  #Sup     : 34
% 2.29/1.39  #Fact    : 0
% 2.29/1.39  #Define  : 0
% 2.29/1.39  #Split   : 0
% 2.29/1.39  #Chain   : 0
% 2.29/1.39  #Close   : 0
% 2.29/1.39  
% 2.29/1.39  Ordering : KBO
% 2.29/1.39  
% 2.29/1.39  Simplification rules
% 2.29/1.39  ----------------------
% 2.29/1.39  #Subsume      : 0
% 2.29/1.39  #Demod        : 17
% 2.29/1.39  #Tautology    : 23
% 2.29/1.39  #SimpNegUnit  : 3
% 2.29/1.39  #BackRed      : 1
% 2.29/1.39  
% 2.29/1.39  #Partial instantiations: 0
% 2.29/1.39  #Strategies tried      : 1
% 2.29/1.39  
% 2.29/1.39  Timing (in seconds)
% 2.29/1.39  ----------------------
% 2.29/1.39  Preprocessing        : 0.39
% 2.29/1.39  Parsing              : 0.21
% 2.29/1.39  CNF conversion       : 0.02
% 2.29/1.39  Main loop            : 0.16
% 2.29/1.39  Inferencing          : 0.06
% 2.29/1.39  Reduction            : 0.06
% 2.29/1.39  Demodulation         : 0.04
% 2.29/1.39  BG Simplification    : 0.02
% 2.29/1.39  Subsumption          : 0.02
% 2.29/1.39  Abstraction          : 0.01
% 2.29/1.39  MUC search           : 0.00
% 2.29/1.39  Cooper               : 0.00
% 2.29/1.39  Total                : 0.59
% 2.29/1.39  Index Insertion      : 0.00
% 2.29/1.39  Index Deletion       : 0.00
% 2.29/1.39  Index Matching       : 0.00
% 2.29/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
