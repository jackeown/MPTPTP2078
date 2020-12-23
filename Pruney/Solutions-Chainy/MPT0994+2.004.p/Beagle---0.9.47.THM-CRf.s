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
% DateTime   : Thu Dec  3 10:13:49 EST 2020

% Result     : Theorem 2.19s
% Output     : CNFRefutation 2.19s
% Verified   : 
% Statistics : Number of formulae       :   65 (  85 expanded)
%              Number of leaves         :   34 (  46 expanded)
%              Depth                    :    6
%              Number of atoms          :  109 ( 194 expanded)
%              Number of equality atoms :   31 (  51 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k6_relset_1 > k1_relset_1 > k8_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k6_relset_1,type,(
    k6_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

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

tff(f_109,negated_conjecture,(
    ~ ! [A,B,C,D,E] :
        ( ( v1_funct_1(E)
          & v1_funct_2(E,A,B)
          & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ( r2_hidden(C,A)
            & r2_hidden(k1_funct_1(E,C),D) )
         => ( B = k1_xboole_0
            | k1_funct_1(k6_relset_1(A,B,D,E),C) = k1_funct_1(E,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_funct_2)).

tff(f_64,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k6_relset_1(A,B,C,D) = k8_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_relset_1)).

tff(f_34,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(A,k1_relat_1(k8_relat_1(B,C)))
      <=> ( r2_hidden(A,k1_relat_1(C))
          & r2_hidden(k1_funct_1(C,A),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_funct_1)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(A,k1_relat_1(k8_relat_1(B,C)))
       => k1_funct_1(k8_relat_1(B,C),A) = k1_funct_1(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_funct_1)).

tff(f_94,axiom,(
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

tff(f_76,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
     => ( ! [D] :
            ~ ( r2_hidden(D,B)
              & ! [E] : ~ r2_hidden(k4_tarski(D,E),C) )
      <=> k1_relset_1(B,A,C) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_relset_1)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
       => ( r2_hidden(A,k1_relat_1(C))
          & r2_hidden(B,k2_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_relat_1)).

tff(c_46,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_63,plain,(
    ! [A_48,B_49,C_50,D_51] :
      ( k6_relset_1(A_48,B_49,C_50,D_51) = k8_relat_1(C_50,D_51)
      | ~ m1_subset_1(D_51,k1_zfmisc_1(k2_zfmisc_1(A_48,B_49))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_66,plain,(
    ! [C_50] : k6_relset_1('#skF_3','#skF_4',C_50,'#skF_7') = k8_relat_1(C_50,'#skF_7') ),
    inference(resolution,[status(thm)],[c_46,c_63])).

tff(c_38,plain,(
    k1_funct_1(k6_relset_1('#skF_3','#skF_4','#skF_6','#skF_7'),'#skF_5') != k1_funct_1('#skF_7','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_68,plain,(
    k1_funct_1(k8_relat_1('#skF_6','#skF_7'),'#skF_5') != k1_funct_1('#skF_7','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_38])).

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_52,plain,(
    ! [B_37,A_38] :
      ( v1_relat_1(B_37)
      | ~ m1_subset_1(B_37,k1_zfmisc_1(A_38))
      | ~ v1_relat_1(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_55,plain,
    ( v1_relat_1('#skF_7')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_46,c_52])).

tff(c_58,plain,(
    v1_relat_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_55])).

tff(c_50,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_42,plain,(
    r2_hidden(k1_funct_1('#skF_7','#skF_5'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_108,plain,(
    ! [A_79,B_80,C_81] :
      ( r2_hidden(A_79,k1_relat_1(k8_relat_1(B_80,C_81)))
      | ~ r2_hidden(k1_funct_1(C_81,A_79),B_80)
      | ~ r2_hidden(A_79,k1_relat_1(C_81))
      | ~ v1_funct_1(C_81)
      | ~ v1_relat_1(C_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_16,plain,(
    ! [B_13,C_14,A_12] :
      ( k1_funct_1(k8_relat_1(B_13,C_14),A_12) = k1_funct_1(C_14,A_12)
      | ~ r2_hidden(A_12,k1_relat_1(k8_relat_1(B_13,C_14)))
      | ~ v1_funct_1(C_14)
      | ~ v1_relat_1(C_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_136,plain,(
    ! [B_82,C_83,A_84] :
      ( k1_funct_1(k8_relat_1(B_82,C_83),A_84) = k1_funct_1(C_83,A_84)
      | ~ r2_hidden(k1_funct_1(C_83,A_84),B_82)
      | ~ r2_hidden(A_84,k1_relat_1(C_83))
      | ~ v1_funct_1(C_83)
      | ~ v1_relat_1(C_83) ) ),
    inference(resolution,[status(thm)],[c_108,c_16])).

tff(c_143,plain,
    ( k1_funct_1(k8_relat_1('#skF_6','#skF_7'),'#skF_5') = k1_funct_1('#skF_7','#skF_5')
    | ~ r2_hidden('#skF_5',k1_relat_1('#skF_7'))
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_42,c_136])).

tff(c_147,plain,
    ( k1_funct_1(k8_relat_1('#skF_6','#skF_7'),'#skF_5') = k1_funct_1('#skF_7','#skF_5')
    | ~ r2_hidden('#skF_5',k1_relat_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_50,c_143])).

tff(c_148,plain,(
    ~ r2_hidden('#skF_5',k1_relat_1('#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_147])).

tff(c_40,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_48,plain,(
    v1_funct_2('#skF_7','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_81,plain,(
    ! [B_63,A_64,C_65] :
      ( k1_xboole_0 = B_63
      | k1_relset_1(A_64,B_63,C_65) = A_64
      | ~ v1_funct_2(C_65,A_64,B_63)
      | ~ m1_subset_1(C_65,k1_zfmisc_1(k2_zfmisc_1(A_64,B_63))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_84,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_7') = '#skF_3'
    | ~ v1_funct_2('#skF_7','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_81])).

tff(c_87,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_7') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_84])).

tff(c_88,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_7') = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_87])).

tff(c_44,plain,(
    r2_hidden('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_149,plain,(
    ! [D_85,A_86,B_87,C_88] :
      ( r2_hidden(k4_tarski(D_85,'#skF_2'(A_86,B_87,C_88,D_85)),C_88)
      | ~ r2_hidden(D_85,B_87)
      | k1_relset_1(B_87,A_86,C_88) != B_87
      | ~ m1_subset_1(C_88,k1_zfmisc_1(k2_zfmisc_1(B_87,A_86))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_8,plain,(
    ! [A_6,C_8,B_7] :
      ( r2_hidden(A_6,k1_relat_1(C_8))
      | ~ r2_hidden(k4_tarski(A_6,B_7),C_8)
      | ~ v1_relat_1(C_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_178,plain,(
    ! [D_89,C_90,B_91,A_92] :
      ( r2_hidden(D_89,k1_relat_1(C_90))
      | ~ v1_relat_1(C_90)
      | ~ r2_hidden(D_89,B_91)
      | k1_relset_1(B_91,A_92,C_90) != B_91
      | ~ m1_subset_1(C_90,k1_zfmisc_1(k2_zfmisc_1(B_91,A_92))) ) ),
    inference(resolution,[status(thm)],[c_149,c_8])).

tff(c_191,plain,(
    ! [C_93,A_94] :
      ( r2_hidden('#skF_5',k1_relat_1(C_93))
      | ~ v1_relat_1(C_93)
      | k1_relset_1('#skF_3',A_94,C_93) != '#skF_3'
      | ~ m1_subset_1(C_93,k1_zfmisc_1(k2_zfmisc_1('#skF_3',A_94))) ) ),
    inference(resolution,[status(thm)],[c_44,c_178])).

tff(c_194,plain,
    ( r2_hidden('#skF_5',k1_relat_1('#skF_7'))
    | ~ v1_relat_1('#skF_7')
    | k1_relset_1('#skF_3','#skF_4','#skF_7') != '#skF_3' ),
    inference(resolution,[status(thm)],[c_46,c_191])).

tff(c_197,plain,(
    r2_hidden('#skF_5',k1_relat_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_58,c_194])).

tff(c_199,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_148,c_197])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:38:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.19/1.28  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.19/1.28  
% 2.19/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.19/1.29  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k6_relset_1 > k1_relset_1 > k8_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_3 > #skF_4
% 2.19/1.29  
% 2.19/1.29  %Foreground sorts:
% 2.19/1.29  
% 2.19/1.29  
% 2.19/1.29  %Background operators:
% 2.19/1.29  
% 2.19/1.29  
% 2.19/1.29  %Foreground operators:
% 2.19/1.29  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 2.19/1.29  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.19/1.29  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.19/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.19/1.29  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.19/1.29  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.19/1.29  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.19/1.29  tff('#skF_7', type, '#skF_7': $i).
% 2.19/1.29  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.19/1.29  tff(k6_relset_1, type, k6_relset_1: ($i * $i * $i * $i) > $i).
% 2.19/1.29  tff('#skF_5', type, '#skF_5': $i).
% 2.19/1.29  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.19/1.29  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.19/1.29  tff('#skF_6', type, '#skF_6': $i).
% 2.19/1.29  tff('#skF_3', type, '#skF_3': $i).
% 2.19/1.29  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.19/1.29  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.19/1.29  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.19/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.19/1.29  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.19/1.29  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.19/1.29  tff('#skF_4', type, '#skF_4': $i).
% 2.19/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.19/1.29  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.19/1.29  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.19/1.29  
% 2.19/1.30  tff(f_109, negated_conjecture, ~(![A, B, C, D, E]: (((v1_funct_1(E) & v1_funct_2(E, A, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((r2_hidden(C, A) & r2_hidden(k1_funct_1(E, C), D)) => ((B = k1_xboole_0) | (k1_funct_1(k6_relset_1(A, B, D, E), C) = k1_funct_1(E, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_funct_2)).
% 2.19/1.30  tff(f_64, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k6_relset_1(A, B, C, D) = k8_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_relset_1)).
% 2.19/1.30  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.19/1.30  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.19/1.30  tff(f_52, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(k8_relat_1(B, C))) <=> (r2_hidden(A, k1_relat_1(C)) & r2_hidden(k1_funct_1(C, A), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_funct_1)).
% 2.19/1.30  tff(f_60, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(k8_relat_1(B, C))) => (k1_funct_1(k8_relat_1(B, C), A) = k1_funct_1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_funct_1)).
% 2.19/1.30  tff(f_94, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 2.19/1.30  tff(f_76, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => ((![D]: ~(r2_hidden(D, B) & (![E]: ~r2_hidden(k4_tarski(D, E), C)))) <=> (k1_relset_1(B, A, C) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_relset_1)).
% 2.19/1.30  tff(f_42, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) => (r2_hidden(A, k1_relat_1(C)) & r2_hidden(B, k2_relat_1(C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_relat_1)).
% 2.19/1.30  tff(c_46, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.19/1.30  tff(c_63, plain, (![A_48, B_49, C_50, D_51]: (k6_relset_1(A_48, B_49, C_50, D_51)=k8_relat_1(C_50, D_51) | ~m1_subset_1(D_51, k1_zfmisc_1(k2_zfmisc_1(A_48, B_49))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.19/1.30  tff(c_66, plain, (![C_50]: (k6_relset_1('#skF_3', '#skF_4', C_50, '#skF_7')=k8_relat_1(C_50, '#skF_7'))), inference(resolution, [status(thm)], [c_46, c_63])).
% 2.19/1.30  tff(c_38, plain, (k1_funct_1(k6_relset_1('#skF_3', '#skF_4', '#skF_6', '#skF_7'), '#skF_5')!=k1_funct_1('#skF_7', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.19/1.30  tff(c_68, plain, (k1_funct_1(k8_relat_1('#skF_6', '#skF_7'), '#skF_5')!=k1_funct_1('#skF_7', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_38])).
% 2.19/1.30  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.19/1.30  tff(c_52, plain, (![B_37, A_38]: (v1_relat_1(B_37) | ~m1_subset_1(B_37, k1_zfmisc_1(A_38)) | ~v1_relat_1(A_38))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.19/1.30  tff(c_55, plain, (v1_relat_1('#skF_7') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_46, c_52])).
% 2.19/1.30  tff(c_58, plain, (v1_relat_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_55])).
% 2.19/1.30  tff(c_50, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.19/1.30  tff(c_42, plain, (r2_hidden(k1_funct_1('#skF_7', '#skF_5'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.19/1.30  tff(c_108, plain, (![A_79, B_80, C_81]: (r2_hidden(A_79, k1_relat_1(k8_relat_1(B_80, C_81))) | ~r2_hidden(k1_funct_1(C_81, A_79), B_80) | ~r2_hidden(A_79, k1_relat_1(C_81)) | ~v1_funct_1(C_81) | ~v1_relat_1(C_81))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.19/1.30  tff(c_16, plain, (![B_13, C_14, A_12]: (k1_funct_1(k8_relat_1(B_13, C_14), A_12)=k1_funct_1(C_14, A_12) | ~r2_hidden(A_12, k1_relat_1(k8_relat_1(B_13, C_14))) | ~v1_funct_1(C_14) | ~v1_relat_1(C_14))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.19/1.30  tff(c_136, plain, (![B_82, C_83, A_84]: (k1_funct_1(k8_relat_1(B_82, C_83), A_84)=k1_funct_1(C_83, A_84) | ~r2_hidden(k1_funct_1(C_83, A_84), B_82) | ~r2_hidden(A_84, k1_relat_1(C_83)) | ~v1_funct_1(C_83) | ~v1_relat_1(C_83))), inference(resolution, [status(thm)], [c_108, c_16])).
% 2.19/1.30  tff(c_143, plain, (k1_funct_1(k8_relat_1('#skF_6', '#skF_7'), '#skF_5')=k1_funct_1('#skF_7', '#skF_5') | ~r2_hidden('#skF_5', k1_relat_1('#skF_7')) | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_42, c_136])).
% 2.19/1.30  tff(c_147, plain, (k1_funct_1(k8_relat_1('#skF_6', '#skF_7'), '#skF_5')=k1_funct_1('#skF_7', '#skF_5') | ~r2_hidden('#skF_5', k1_relat_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_50, c_143])).
% 2.19/1.30  tff(c_148, plain, (~r2_hidden('#skF_5', k1_relat_1('#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_68, c_147])).
% 2.19/1.30  tff(c_40, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.19/1.30  tff(c_48, plain, (v1_funct_2('#skF_7', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.19/1.30  tff(c_81, plain, (![B_63, A_64, C_65]: (k1_xboole_0=B_63 | k1_relset_1(A_64, B_63, C_65)=A_64 | ~v1_funct_2(C_65, A_64, B_63) | ~m1_subset_1(C_65, k1_zfmisc_1(k2_zfmisc_1(A_64, B_63))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.19/1.30  tff(c_84, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_7')='#skF_3' | ~v1_funct_2('#skF_7', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_46, c_81])).
% 2.19/1.30  tff(c_87, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_7')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_84])).
% 2.19/1.30  tff(c_88, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_7')='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_40, c_87])).
% 2.19/1.30  tff(c_44, plain, (r2_hidden('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.19/1.30  tff(c_149, plain, (![D_85, A_86, B_87, C_88]: (r2_hidden(k4_tarski(D_85, '#skF_2'(A_86, B_87, C_88, D_85)), C_88) | ~r2_hidden(D_85, B_87) | k1_relset_1(B_87, A_86, C_88)!=B_87 | ~m1_subset_1(C_88, k1_zfmisc_1(k2_zfmisc_1(B_87, A_86))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.19/1.30  tff(c_8, plain, (![A_6, C_8, B_7]: (r2_hidden(A_6, k1_relat_1(C_8)) | ~r2_hidden(k4_tarski(A_6, B_7), C_8) | ~v1_relat_1(C_8))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.19/1.30  tff(c_178, plain, (![D_89, C_90, B_91, A_92]: (r2_hidden(D_89, k1_relat_1(C_90)) | ~v1_relat_1(C_90) | ~r2_hidden(D_89, B_91) | k1_relset_1(B_91, A_92, C_90)!=B_91 | ~m1_subset_1(C_90, k1_zfmisc_1(k2_zfmisc_1(B_91, A_92))))), inference(resolution, [status(thm)], [c_149, c_8])).
% 2.19/1.30  tff(c_191, plain, (![C_93, A_94]: (r2_hidden('#skF_5', k1_relat_1(C_93)) | ~v1_relat_1(C_93) | k1_relset_1('#skF_3', A_94, C_93)!='#skF_3' | ~m1_subset_1(C_93, k1_zfmisc_1(k2_zfmisc_1('#skF_3', A_94))))), inference(resolution, [status(thm)], [c_44, c_178])).
% 2.19/1.30  tff(c_194, plain, (r2_hidden('#skF_5', k1_relat_1('#skF_7')) | ~v1_relat_1('#skF_7') | k1_relset_1('#skF_3', '#skF_4', '#skF_7')!='#skF_3'), inference(resolution, [status(thm)], [c_46, c_191])).
% 2.19/1.30  tff(c_197, plain, (r2_hidden('#skF_5', k1_relat_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_58, c_194])).
% 2.19/1.30  tff(c_199, plain, $false, inference(negUnitSimplification, [status(thm)], [c_148, c_197])).
% 2.19/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.19/1.30  
% 2.19/1.30  Inference rules
% 2.19/1.30  ----------------------
% 2.19/1.30  #Ref     : 0
% 2.19/1.30  #Sup     : 28
% 2.19/1.30  #Fact    : 0
% 2.19/1.30  #Define  : 0
% 2.19/1.30  #Split   : 0
% 2.19/1.30  #Chain   : 0
% 2.19/1.30  #Close   : 0
% 2.19/1.30  
% 2.19/1.30  Ordering : KBO
% 2.19/1.30  
% 2.19/1.30  Simplification rules
% 2.19/1.30  ----------------------
% 2.19/1.30  #Subsume      : 0
% 2.19/1.30  #Demod        : 10
% 2.19/1.30  #Tautology    : 8
% 2.19/1.30  #SimpNegUnit  : 4
% 2.19/1.30  #BackRed      : 1
% 2.19/1.30  
% 2.19/1.30  #Partial instantiations: 0
% 2.19/1.30  #Strategies tried      : 1
% 2.19/1.30  
% 2.19/1.30  Timing (in seconds)
% 2.19/1.30  ----------------------
% 2.19/1.30  Preprocessing        : 0.32
% 2.19/1.30  Parsing              : 0.17
% 2.19/1.30  CNF conversion       : 0.02
% 2.19/1.30  Main loop            : 0.19
% 2.19/1.30  Inferencing          : 0.07
% 2.19/1.30  Reduction            : 0.06
% 2.19/1.30  Demodulation         : 0.04
% 2.19/1.30  BG Simplification    : 0.02
% 2.19/1.30  Subsumption          : 0.03
% 2.19/1.30  Abstraction          : 0.01
% 2.19/1.30  MUC search           : 0.00
% 2.19/1.30  Cooper               : 0.00
% 2.19/1.30  Total                : 0.55
% 2.19/1.30  Index Insertion      : 0.00
% 2.19/1.30  Index Deletion       : 0.00
% 2.19/1.30  Index Matching       : 0.00
% 2.19/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
