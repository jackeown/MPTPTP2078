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
% DateTime   : Thu Dec  3 10:14:54 EST 2020

% Result     : Theorem 11.63s
% Output     : CNFRefutation 11.63s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 123 expanded)
%              Number of leaves         :   37 (  62 expanded)
%              Depth                    :   10
%              Number of atoms          :   88 ( 245 expanded)
%              Number of equality atoms :   33 (  91 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_130,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,k1_tarski(A),B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r1_tarski(k7_relset_1(k1_tarski(A),B,D,C),k1_tarski(k1_funct_1(D,A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_2)).

tff(f_92,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_96,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_118,axiom,(
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

tff(f_43,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(f_88,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( ( r2_hidden(A,k1_relat_1(C))
          & r2_hidden(B,k1_relat_1(C)) )
       => k9_relat_1(C,k2_tarski(A,B)) = k2_tarski(k1_funct_1(C,A),k1_funct_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t118_funct_1)).

tff(f_78,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k9_relat_1(B,A),k9_relat_1(B,k1_relat_1(B))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_relat_1)).

tff(f_100,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(c_76,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_4'),'#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_184,plain,(
    ! [C_84,A_85,B_86] :
      ( v1_relat_1(C_84)
      | ~ m1_subset_1(C_84,k1_zfmisc_1(k2_zfmisc_1(A_85,B_86))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_188,plain,(
    v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_76,c_184])).

tff(c_80,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_74,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_78,plain,(
    v1_funct_2('#skF_7',k1_tarski('#skF_4'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_377,plain,(
    ! [A_125,B_126,C_127] :
      ( k1_relset_1(A_125,B_126,C_127) = k1_relat_1(C_127)
      | ~ m1_subset_1(C_127,k1_zfmisc_1(k2_zfmisc_1(A_125,B_126))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_381,plain,(
    k1_relset_1(k1_tarski('#skF_4'),'#skF_5','#skF_7') = k1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_76,c_377])).

tff(c_1535,plain,(
    ! [B_2177,A_2178,C_2179] :
      ( k1_xboole_0 = B_2177
      | k1_relset_1(A_2178,B_2177,C_2179) = A_2178
      | ~ v1_funct_2(C_2179,A_2178,B_2177)
      | ~ m1_subset_1(C_2179,k1_zfmisc_1(k2_zfmisc_1(A_2178,B_2177))) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_1538,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relset_1(k1_tarski('#skF_4'),'#skF_5','#skF_7') = k1_tarski('#skF_4')
    | ~ v1_funct_2('#skF_7',k1_tarski('#skF_4'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_76,c_1535])).

tff(c_1541,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_tarski('#skF_4') = k1_relat_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_381,c_1538])).

tff(c_1542,plain,(
    k1_tarski('#skF_4') = k1_relat_1('#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_1541])).

tff(c_83,plain,(
    ! [A_44] : k2_tarski(A_44,A_44) = k1_tarski(A_44) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_10,plain,(
    ! [D_11,A_6] : r2_hidden(D_11,k2_tarski(A_6,D_11)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_89,plain,(
    ! [A_44] : r2_hidden(A_44,k1_tarski(A_44)) ),
    inference(superposition,[status(thm),theory(equality)],[c_83,c_10])).

tff(c_1579,plain,(
    r2_hidden('#skF_4',k1_relat_1('#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1542,c_89])).

tff(c_26,plain,(
    ! [A_12] : k2_tarski(A_12,A_12) = k1_tarski(A_12) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_3827,plain,(
    ! [C_6890,A_6891,B_6892] :
      ( k2_tarski(k1_funct_1(C_6890,A_6891),k1_funct_1(C_6890,B_6892)) = k9_relat_1(C_6890,k2_tarski(A_6891,B_6892))
      | ~ r2_hidden(B_6892,k1_relat_1(C_6890))
      | ~ r2_hidden(A_6891,k1_relat_1(C_6890))
      | ~ v1_funct_1(C_6890)
      | ~ v1_relat_1(C_6890) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_4027,plain,(
    ! [C_6890,A_6891] :
      ( k9_relat_1(C_6890,k2_tarski(A_6891,A_6891)) = k1_tarski(k1_funct_1(C_6890,A_6891))
      | ~ r2_hidden(A_6891,k1_relat_1(C_6890))
      | ~ r2_hidden(A_6891,k1_relat_1(C_6890))
      | ~ v1_funct_1(C_6890)
      | ~ v1_relat_1(C_6890) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_3827])).

tff(c_47540,plain,(
    ! [C_30472,A_30473] :
      ( k9_relat_1(C_30472,k1_tarski(A_30473)) = k1_tarski(k1_funct_1(C_30472,A_30473))
      | ~ r2_hidden(A_30473,k1_relat_1(C_30472))
      | ~ r2_hidden(A_30473,k1_relat_1(C_30472))
      | ~ v1_funct_1(C_30472)
      | ~ v1_relat_1(C_30472) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_4027])).

tff(c_47589,plain,
    ( k9_relat_1('#skF_7',k1_tarski('#skF_4')) = k1_tarski(k1_funct_1('#skF_7','#skF_4'))
    | ~ r2_hidden('#skF_4',k1_relat_1('#skF_7'))
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_1579,c_47540])).

tff(c_47601,plain,(
    k9_relat_1('#skF_7',k1_relat_1('#skF_7')) = k1_tarski(k1_funct_1('#skF_7','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_188,c_80,c_1579,c_1542,c_47589])).

tff(c_50,plain,(
    ! [B_23,A_22] :
      ( r1_tarski(k9_relat_1(B_23,A_22),k9_relat_1(B_23,k1_relat_1(B_23)))
      | ~ v1_relat_1(B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_47610,plain,(
    ! [A_22] :
      ( r1_tarski(k9_relat_1('#skF_7',A_22),k1_tarski(k1_funct_1('#skF_7','#skF_4')))
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_47601,c_50])).

tff(c_47658,plain,(
    ! [A_22] : r1_tarski(k9_relat_1('#skF_7',A_22),k1_tarski(k1_funct_1('#skF_7','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_188,c_47610])).

tff(c_1327,plain,(
    ! [A_1988,B_1989,C_1990,D_1991] :
      ( k7_relset_1(A_1988,B_1989,C_1990,D_1991) = k9_relat_1(C_1990,D_1991)
      | ~ m1_subset_1(C_1990,k1_zfmisc_1(k2_zfmisc_1(A_1988,B_1989))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_1334,plain,(
    ! [D_1991] : k7_relset_1(k1_tarski('#skF_4'),'#skF_5','#skF_7',D_1991) = k9_relat_1('#skF_7',D_1991) ),
    inference(resolution,[status(thm)],[c_76,c_1327])).

tff(c_72,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski('#skF_4'),'#skF_5','#skF_7','#skF_6'),k1_tarski(k1_funct_1('#skF_7','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_1335,plain,(
    ~ r1_tarski(k9_relat_1('#skF_7','#skF_6'),k1_tarski(k1_funct_1('#skF_7','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1334,c_72])).

tff(c_47662,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_47658,c_1335])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 18:03:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.63/4.38  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.63/4.38  
% 11.63/4.38  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.63/4.38  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 11.63/4.38  
% 11.63/4.38  %Foreground sorts:
% 11.63/4.38  
% 11.63/4.38  
% 11.63/4.38  %Background operators:
% 11.63/4.38  
% 11.63/4.38  
% 11.63/4.38  %Foreground operators:
% 11.63/4.38  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 11.63/4.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.63/4.38  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 11.63/4.38  tff(k1_tarski, type, k1_tarski: $i > $i).
% 11.63/4.38  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 11.63/4.38  tff('#skF_7', type, '#skF_7': $i).
% 11.63/4.38  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.63/4.38  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 11.63/4.38  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 11.63/4.38  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 11.63/4.38  tff('#skF_5', type, '#skF_5': $i).
% 11.63/4.38  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 11.63/4.38  tff('#skF_6', type, '#skF_6': $i).
% 11.63/4.38  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 11.63/4.38  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 11.63/4.38  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 11.63/4.38  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 11.63/4.38  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 11.63/4.38  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 11.63/4.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.63/4.38  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 11.63/4.38  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 11.63/4.38  tff('#skF_4', type, '#skF_4': $i).
% 11.63/4.38  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 11.63/4.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.63/4.38  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 11.63/4.38  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 11.63/4.38  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 11.63/4.38  
% 11.63/4.39  tff(f_130, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, k1_tarski(A), B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r1_tarski(k7_relset_1(k1_tarski(A), B, D, C), k1_tarski(k1_funct_1(D, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_funct_2)).
% 11.63/4.39  tff(f_92, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 11.63/4.39  tff(f_96, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 11.63/4.39  tff(f_118, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 11.63/4.39  tff(f_43, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 11.63/4.39  tff(f_41, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 11.63/4.39  tff(f_88, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r2_hidden(A, k1_relat_1(C)) & r2_hidden(B, k1_relat_1(C))) => (k9_relat_1(C, k2_tarski(A, B)) = k2_tarski(k1_funct_1(C, A), k1_funct_1(C, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t118_funct_1)).
% 11.63/4.39  tff(f_78, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k9_relat_1(B, A), k9_relat_1(B, k1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t147_relat_1)).
% 11.63/4.39  tff(f_100, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 11.63/4.39  tff(c_76, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_4'), '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_130])).
% 11.63/4.39  tff(c_184, plain, (![C_84, A_85, B_86]: (v1_relat_1(C_84) | ~m1_subset_1(C_84, k1_zfmisc_1(k2_zfmisc_1(A_85, B_86))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 11.63/4.39  tff(c_188, plain, (v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_76, c_184])).
% 11.63/4.39  tff(c_80, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_130])).
% 11.63/4.39  tff(c_74, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_130])).
% 11.63/4.39  tff(c_78, plain, (v1_funct_2('#skF_7', k1_tarski('#skF_4'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_130])).
% 11.63/4.39  tff(c_377, plain, (![A_125, B_126, C_127]: (k1_relset_1(A_125, B_126, C_127)=k1_relat_1(C_127) | ~m1_subset_1(C_127, k1_zfmisc_1(k2_zfmisc_1(A_125, B_126))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 11.63/4.39  tff(c_381, plain, (k1_relset_1(k1_tarski('#skF_4'), '#skF_5', '#skF_7')=k1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_76, c_377])).
% 11.63/4.39  tff(c_1535, plain, (![B_2177, A_2178, C_2179]: (k1_xboole_0=B_2177 | k1_relset_1(A_2178, B_2177, C_2179)=A_2178 | ~v1_funct_2(C_2179, A_2178, B_2177) | ~m1_subset_1(C_2179, k1_zfmisc_1(k2_zfmisc_1(A_2178, B_2177))))), inference(cnfTransformation, [status(thm)], [f_118])).
% 11.63/4.39  tff(c_1538, plain, (k1_xboole_0='#skF_5' | k1_relset_1(k1_tarski('#skF_4'), '#skF_5', '#skF_7')=k1_tarski('#skF_4') | ~v1_funct_2('#skF_7', k1_tarski('#skF_4'), '#skF_5')), inference(resolution, [status(thm)], [c_76, c_1535])).
% 11.63/4.39  tff(c_1541, plain, (k1_xboole_0='#skF_5' | k1_tarski('#skF_4')=k1_relat_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_381, c_1538])).
% 11.63/4.39  tff(c_1542, plain, (k1_tarski('#skF_4')=k1_relat_1('#skF_7')), inference(negUnitSimplification, [status(thm)], [c_74, c_1541])).
% 11.63/4.39  tff(c_83, plain, (![A_44]: (k2_tarski(A_44, A_44)=k1_tarski(A_44))), inference(cnfTransformation, [status(thm)], [f_43])).
% 11.63/4.39  tff(c_10, plain, (![D_11, A_6]: (r2_hidden(D_11, k2_tarski(A_6, D_11)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 11.63/4.39  tff(c_89, plain, (![A_44]: (r2_hidden(A_44, k1_tarski(A_44)))), inference(superposition, [status(thm), theory('equality')], [c_83, c_10])).
% 11.63/4.39  tff(c_1579, plain, (r2_hidden('#skF_4', k1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_1542, c_89])).
% 11.63/4.39  tff(c_26, plain, (![A_12]: (k2_tarski(A_12, A_12)=k1_tarski(A_12))), inference(cnfTransformation, [status(thm)], [f_43])).
% 11.63/4.39  tff(c_3827, plain, (![C_6890, A_6891, B_6892]: (k2_tarski(k1_funct_1(C_6890, A_6891), k1_funct_1(C_6890, B_6892))=k9_relat_1(C_6890, k2_tarski(A_6891, B_6892)) | ~r2_hidden(B_6892, k1_relat_1(C_6890)) | ~r2_hidden(A_6891, k1_relat_1(C_6890)) | ~v1_funct_1(C_6890) | ~v1_relat_1(C_6890))), inference(cnfTransformation, [status(thm)], [f_88])).
% 11.63/4.39  tff(c_4027, plain, (![C_6890, A_6891]: (k9_relat_1(C_6890, k2_tarski(A_6891, A_6891))=k1_tarski(k1_funct_1(C_6890, A_6891)) | ~r2_hidden(A_6891, k1_relat_1(C_6890)) | ~r2_hidden(A_6891, k1_relat_1(C_6890)) | ~v1_funct_1(C_6890) | ~v1_relat_1(C_6890))), inference(superposition, [status(thm), theory('equality')], [c_26, c_3827])).
% 11.63/4.39  tff(c_47540, plain, (![C_30472, A_30473]: (k9_relat_1(C_30472, k1_tarski(A_30473))=k1_tarski(k1_funct_1(C_30472, A_30473)) | ~r2_hidden(A_30473, k1_relat_1(C_30472)) | ~r2_hidden(A_30473, k1_relat_1(C_30472)) | ~v1_funct_1(C_30472) | ~v1_relat_1(C_30472))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_4027])).
% 11.63/4.39  tff(c_47589, plain, (k9_relat_1('#skF_7', k1_tarski('#skF_4'))=k1_tarski(k1_funct_1('#skF_7', '#skF_4')) | ~r2_hidden('#skF_4', k1_relat_1('#skF_7')) | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_1579, c_47540])).
% 11.63/4.39  tff(c_47601, plain, (k9_relat_1('#skF_7', k1_relat_1('#skF_7'))=k1_tarski(k1_funct_1('#skF_7', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_188, c_80, c_1579, c_1542, c_47589])).
% 11.63/4.39  tff(c_50, plain, (![B_23, A_22]: (r1_tarski(k9_relat_1(B_23, A_22), k9_relat_1(B_23, k1_relat_1(B_23))) | ~v1_relat_1(B_23))), inference(cnfTransformation, [status(thm)], [f_78])).
% 11.63/4.39  tff(c_47610, plain, (![A_22]: (r1_tarski(k9_relat_1('#skF_7', A_22), k1_tarski(k1_funct_1('#skF_7', '#skF_4'))) | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_47601, c_50])).
% 11.63/4.39  tff(c_47658, plain, (![A_22]: (r1_tarski(k9_relat_1('#skF_7', A_22), k1_tarski(k1_funct_1('#skF_7', '#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_188, c_47610])).
% 11.63/4.39  tff(c_1327, plain, (![A_1988, B_1989, C_1990, D_1991]: (k7_relset_1(A_1988, B_1989, C_1990, D_1991)=k9_relat_1(C_1990, D_1991) | ~m1_subset_1(C_1990, k1_zfmisc_1(k2_zfmisc_1(A_1988, B_1989))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 11.63/4.39  tff(c_1334, plain, (![D_1991]: (k7_relset_1(k1_tarski('#skF_4'), '#skF_5', '#skF_7', D_1991)=k9_relat_1('#skF_7', D_1991))), inference(resolution, [status(thm)], [c_76, c_1327])).
% 11.63/4.39  tff(c_72, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_4'), '#skF_5', '#skF_7', '#skF_6'), k1_tarski(k1_funct_1('#skF_7', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_130])).
% 11.63/4.39  tff(c_1335, plain, (~r1_tarski(k9_relat_1('#skF_7', '#skF_6'), k1_tarski(k1_funct_1('#skF_7', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_1334, c_72])).
% 11.63/4.39  tff(c_47662, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_47658, c_1335])).
% 11.63/4.39  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.63/4.39  
% 11.63/4.39  Inference rules
% 11.63/4.39  ----------------------
% 11.63/4.39  #Ref     : 0
% 11.63/4.39  #Sup     : 7002
% 11.63/4.39  #Fact    : 50
% 11.63/4.39  #Define  : 0
% 11.63/4.39  #Split   : 7
% 11.63/4.39  #Chain   : 0
% 11.63/4.39  #Close   : 0
% 11.63/4.39  
% 11.63/4.39  Ordering : KBO
% 11.63/4.39  
% 11.63/4.39  Simplification rules
% 11.63/4.39  ----------------------
% 11.63/4.39  #Subsume      : 2360
% 11.63/4.40  #Demod        : 1486
% 11.63/4.40  #Tautology    : 948
% 11.63/4.40  #SimpNegUnit  : 4
% 11.63/4.40  #BackRed      : 6
% 11.63/4.40  
% 11.63/4.40  #Partial instantiations: 16259
% 11.63/4.40  #Strategies tried      : 1
% 11.63/4.40  
% 11.63/4.40  Timing (in seconds)
% 11.63/4.40  ----------------------
% 11.63/4.40  Preprocessing        : 0.37
% 11.63/4.40  Parsing              : 0.18
% 11.63/4.40  CNF conversion       : 0.03
% 11.63/4.40  Main loop            : 3.26
% 11.63/4.40  Inferencing          : 1.29
% 11.63/4.40  Reduction            : 0.93
% 11.63/4.40  Demodulation         : 0.70
% 11.63/4.40  BG Simplification    : 0.14
% 11.63/4.40  Subsumption          : 0.61
% 11.63/4.40  Abstraction          : 0.23
% 11.63/4.40  MUC search           : 0.00
% 11.63/4.40  Cooper               : 0.00
% 11.63/4.40  Total                : 3.66
% 11.63/4.40  Index Insertion      : 0.00
% 11.63/4.40  Index Deletion       : 0.00
% 11.63/4.40  Index Matching       : 0.00
% 11.63/4.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
