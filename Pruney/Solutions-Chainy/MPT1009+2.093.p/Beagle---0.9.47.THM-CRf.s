%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:55 EST 2020

% Result     : Theorem 3.08s
% Output     : CNFRefutation 3.08s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 103 expanded)
%              Number of leaves         :   33 (  52 expanded)
%              Depth                    :    8
%              Number of atoms          :   93 ( 209 expanded)
%              Number of equality atoms :   28 (  52 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k1_relset_1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

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

tff(f_97,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,k1_tarski(A),B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r1_tarski(k7_relset_1(k1_tarski(A),B,D,C),k1_tarski(k1_funct_1(D,A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_2)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_85,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_57,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_49,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k7_relset_1(A,B,C,D),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relset_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_41,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( k1_relat_1(B) = k1_tarski(A)
       => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_75,axiom,(
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

tff(c_42,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_75,plain,(
    ! [C_33,A_34,B_35] :
      ( v1_relat_1(C_33)
      | ~ m1_subset_1(C_33,k1_zfmisc_1(k2_zfmisc_1(A_34,B_35))) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_83,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_75])).

tff(c_46,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_32,plain,(
    ! [A_25] :
      ( m1_subset_1(A_25,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_25),k2_relat_1(A_25))))
      | ~ v1_funct_1(A_25)
      | ~ v1_relat_1(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_149,plain,(
    ! [A_51,B_52,C_53,D_54] :
      ( k7_relset_1(A_51,B_52,C_53,D_54) = k9_relat_1(C_53,D_54)
      | ~ m1_subset_1(C_53,k1_zfmisc_1(k2_zfmisc_1(A_51,B_52))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_157,plain,(
    ! [A_25,D_54] :
      ( k7_relset_1(k1_relat_1(A_25),k2_relat_1(A_25),A_25,D_54) = k9_relat_1(A_25,D_54)
      | ~ v1_funct_1(A_25)
      | ~ v1_relat_1(A_25) ) ),
    inference(resolution,[status(thm)],[c_32,c_149])).

tff(c_170,plain,(
    ! [A_56,B_57,C_58,D_59] :
      ( m1_subset_1(k7_relset_1(A_56,B_57,C_58,D_59),k1_zfmisc_1(B_57))
      | ~ m1_subset_1(C_58,k1_zfmisc_1(k2_zfmisc_1(A_56,B_57))) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_6,plain,(
    ! [A_4,B_5] :
      ( r1_tarski(A_4,B_5)
      | ~ m1_subset_1(A_4,k1_zfmisc_1(B_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_219,plain,(
    ! [A_68,B_69,C_70,D_71] :
      ( r1_tarski(k7_relset_1(A_68,B_69,C_70,D_71),B_69)
      | ~ m1_subset_1(C_70,k1_zfmisc_1(k2_zfmisc_1(A_68,B_69))) ) ),
    inference(resolution,[status(thm)],[c_170,c_6])).

tff(c_536,plain,(
    ! [A_126,D_127] :
      ( r1_tarski(k7_relset_1(k1_relat_1(A_126),k2_relat_1(A_126),A_126,D_127),k2_relat_1(A_126))
      | ~ v1_funct_1(A_126)
      | ~ v1_relat_1(A_126) ) ),
    inference(resolution,[status(thm)],[c_32,c_219])).

tff(c_562,plain,(
    ! [A_131,D_132] :
      ( r1_tarski(k9_relat_1(A_131,D_132),k2_relat_1(A_131))
      | ~ v1_funct_1(A_131)
      | ~ v1_relat_1(A_131)
      | ~ v1_funct_1(A_131)
      | ~ v1_relat_1(A_131) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_157,c_536])).

tff(c_261,plain,(
    ! [B_78,A_79] :
      ( k1_tarski(k1_funct_1(B_78,A_79)) = k2_relat_1(B_78)
      | k1_tarski(A_79) != k1_relat_1(B_78)
      | ~ v1_funct_1(B_78)
      | ~ v1_relat_1(B_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_158,plain,(
    ! [D_54] : k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4',D_54) = k9_relat_1('#skF_4',D_54) ),
    inference(resolution,[status(thm)],[c_42,c_149])).

tff(c_38,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_160,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_158,c_38])).

tff(c_267,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_261,c_160])).

tff(c_273,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_46,c_267])).

tff(c_286,plain,(
    k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_273])).

tff(c_40,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_44,plain,(
    v1_funct_2('#skF_4',k1_tarski('#skF_1'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_92,plain,(
    ! [A_40,B_41,C_42] :
      ( k1_relset_1(A_40,B_41,C_42) = k1_relat_1(C_42)
      | ~ m1_subset_1(C_42,k1_zfmisc_1(k2_zfmisc_1(A_40,B_41))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_100,plain,(
    k1_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_92])).

tff(c_381,plain,(
    ! [B_110,A_111,C_112] :
      ( k1_xboole_0 = B_110
      | k1_relset_1(A_111,B_110,C_112) = A_111
      | ~ v1_funct_2(C_112,A_111,B_110)
      | ~ m1_subset_1(C_112,k1_zfmisc_1(k2_zfmisc_1(A_111,B_110))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_391,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4') = k1_tarski('#skF_1')
    | ~ v1_funct_2('#skF_4',k1_tarski('#skF_1'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_381])).

tff(c_400,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_tarski('#skF_1') = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_100,c_391])).

tff(c_402,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_286,c_40,c_400])).

tff(c_403,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_273])).

tff(c_565,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_562,c_403])).

tff(c_569,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_46,c_565])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:08:47 EST 2020
% 0.20/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.08/1.64  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.08/1.64  
% 3.08/1.64  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.08/1.64  %$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k1_relset_1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.08/1.64  
% 3.08/1.64  %Foreground sorts:
% 3.08/1.64  
% 3.08/1.64  
% 3.08/1.64  %Background operators:
% 3.08/1.64  
% 3.08/1.64  
% 3.08/1.64  %Foreground operators:
% 3.08/1.64  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.08/1.64  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.08/1.64  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.08/1.64  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.08/1.64  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.08/1.64  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.08/1.64  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 3.08/1.64  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.08/1.64  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.08/1.64  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.08/1.64  tff('#skF_2', type, '#skF_2': $i).
% 3.08/1.64  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.08/1.64  tff('#skF_3', type, '#skF_3': $i).
% 3.08/1.64  tff('#skF_1', type, '#skF_1': $i).
% 3.08/1.64  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.08/1.64  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.08/1.64  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.08/1.64  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.08/1.64  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.08/1.64  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.08/1.64  tff('#skF_4', type, '#skF_4': $i).
% 3.08/1.64  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.08/1.64  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.08/1.64  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.08/1.64  
% 3.08/1.66  tff(f_97, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, k1_tarski(A), B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r1_tarski(k7_relset_1(k1_tarski(A), B, D, C), k1_tarski(k1_funct_1(D, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_funct_2)).
% 3.08/1.66  tff(f_45, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.08/1.66  tff(f_85, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_funct_2)).
% 3.08/1.66  tff(f_57, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 3.08/1.66  tff(f_49, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k7_relset_1(A, B, C, D), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relset_1)).
% 3.08/1.66  tff(f_33, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.08/1.66  tff(f_41, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_funct_1)).
% 3.08/1.66  tff(f_53, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.08/1.66  tff(f_75, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 3.08/1.66  tff(c_42, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.08/1.66  tff(c_75, plain, (![C_33, A_34, B_35]: (v1_relat_1(C_33) | ~m1_subset_1(C_33, k1_zfmisc_1(k2_zfmisc_1(A_34, B_35))))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.08/1.66  tff(c_83, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_42, c_75])).
% 3.08/1.66  tff(c_46, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.08/1.66  tff(c_32, plain, (![A_25]: (m1_subset_1(A_25, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_25), k2_relat_1(A_25)))) | ~v1_funct_1(A_25) | ~v1_relat_1(A_25))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.08/1.66  tff(c_149, plain, (![A_51, B_52, C_53, D_54]: (k7_relset_1(A_51, B_52, C_53, D_54)=k9_relat_1(C_53, D_54) | ~m1_subset_1(C_53, k1_zfmisc_1(k2_zfmisc_1(A_51, B_52))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.08/1.66  tff(c_157, plain, (![A_25, D_54]: (k7_relset_1(k1_relat_1(A_25), k2_relat_1(A_25), A_25, D_54)=k9_relat_1(A_25, D_54) | ~v1_funct_1(A_25) | ~v1_relat_1(A_25))), inference(resolution, [status(thm)], [c_32, c_149])).
% 3.08/1.66  tff(c_170, plain, (![A_56, B_57, C_58, D_59]: (m1_subset_1(k7_relset_1(A_56, B_57, C_58, D_59), k1_zfmisc_1(B_57)) | ~m1_subset_1(C_58, k1_zfmisc_1(k2_zfmisc_1(A_56, B_57))))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.08/1.66  tff(c_6, plain, (![A_4, B_5]: (r1_tarski(A_4, B_5) | ~m1_subset_1(A_4, k1_zfmisc_1(B_5)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.08/1.66  tff(c_219, plain, (![A_68, B_69, C_70, D_71]: (r1_tarski(k7_relset_1(A_68, B_69, C_70, D_71), B_69) | ~m1_subset_1(C_70, k1_zfmisc_1(k2_zfmisc_1(A_68, B_69))))), inference(resolution, [status(thm)], [c_170, c_6])).
% 3.08/1.66  tff(c_536, plain, (![A_126, D_127]: (r1_tarski(k7_relset_1(k1_relat_1(A_126), k2_relat_1(A_126), A_126, D_127), k2_relat_1(A_126)) | ~v1_funct_1(A_126) | ~v1_relat_1(A_126))), inference(resolution, [status(thm)], [c_32, c_219])).
% 3.08/1.66  tff(c_562, plain, (![A_131, D_132]: (r1_tarski(k9_relat_1(A_131, D_132), k2_relat_1(A_131)) | ~v1_funct_1(A_131) | ~v1_relat_1(A_131) | ~v1_funct_1(A_131) | ~v1_relat_1(A_131))), inference(superposition, [status(thm), theory('equality')], [c_157, c_536])).
% 3.08/1.66  tff(c_261, plain, (![B_78, A_79]: (k1_tarski(k1_funct_1(B_78, A_79))=k2_relat_1(B_78) | k1_tarski(A_79)!=k1_relat_1(B_78) | ~v1_funct_1(B_78) | ~v1_relat_1(B_78))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.08/1.66  tff(c_158, plain, (![D_54]: (k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', D_54)=k9_relat_1('#skF_4', D_54))), inference(resolution, [status(thm)], [c_42, c_149])).
% 3.08/1.66  tff(c_38, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.08/1.66  tff(c_160, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_158, c_38])).
% 3.08/1.66  tff(c_267, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_261, c_160])).
% 3.08/1.66  tff(c_273, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_83, c_46, c_267])).
% 3.08/1.66  tff(c_286, plain, (k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(splitLeft, [status(thm)], [c_273])).
% 3.08/1.66  tff(c_40, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.08/1.66  tff(c_44, plain, (v1_funct_2('#skF_4', k1_tarski('#skF_1'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.08/1.66  tff(c_92, plain, (![A_40, B_41, C_42]: (k1_relset_1(A_40, B_41, C_42)=k1_relat_1(C_42) | ~m1_subset_1(C_42, k1_zfmisc_1(k2_zfmisc_1(A_40, B_41))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.08/1.66  tff(c_100, plain, (k1_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_42, c_92])).
% 3.08/1.66  tff(c_381, plain, (![B_110, A_111, C_112]: (k1_xboole_0=B_110 | k1_relset_1(A_111, B_110, C_112)=A_111 | ~v1_funct_2(C_112, A_111, B_110) | ~m1_subset_1(C_112, k1_zfmisc_1(k2_zfmisc_1(A_111, B_110))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.08/1.66  tff(c_391, plain, (k1_xboole_0='#skF_2' | k1_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4')=k1_tarski('#skF_1') | ~v1_funct_2('#skF_4', k1_tarski('#skF_1'), '#skF_2')), inference(resolution, [status(thm)], [c_42, c_381])).
% 3.08/1.66  tff(c_400, plain, (k1_xboole_0='#skF_2' | k1_tarski('#skF_1')=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_100, c_391])).
% 3.08/1.66  tff(c_402, plain, $false, inference(negUnitSimplification, [status(thm)], [c_286, c_40, c_400])).
% 3.08/1.66  tff(c_403, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4'))), inference(splitRight, [status(thm)], [c_273])).
% 3.08/1.66  tff(c_565, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_562, c_403])).
% 3.08/1.66  tff(c_569, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_83, c_46, c_565])).
% 3.08/1.66  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.08/1.66  
% 3.08/1.66  Inference rules
% 3.08/1.66  ----------------------
% 3.08/1.66  #Ref     : 0
% 3.08/1.66  #Sup     : 108
% 3.08/1.66  #Fact    : 0
% 3.08/1.66  #Define  : 0
% 3.08/1.66  #Split   : 1
% 3.08/1.66  #Chain   : 0
% 3.08/1.66  #Close   : 0
% 3.08/1.66  
% 3.08/1.66  Ordering : KBO
% 3.08/1.66  
% 3.08/1.66  Simplification rules
% 3.08/1.66  ----------------------
% 3.08/1.66  #Subsume      : 11
% 3.08/1.66  #Demod        : 41
% 3.08/1.66  #Tautology    : 43
% 3.08/1.66  #SimpNegUnit  : 5
% 3.08/1.66  #BackRed      : 7
% 3.08/1.66  
% 3.08/1.66  #Partial instantiations: 0
% 3.08/1.66  #Strategies tried      : 1
% 3.08/1.66  
% 3.08/1.66  Timing (in seconds)
% 3.08/1.66  ----------------------
% 3.08/1.66  Preprocessing        : 0.42
% 3.08/1.66  Parsing              : 0.19
% 3.08/1.66  CNF conversion       : 0.03
% 3.08/1.66  Main loop            : 0.46
% 3.08/1.66  Inferencing          : 0.18
% 3.08/1.66  Reduction            : 0.13
% 3.08/1.66  Demodulation         : 0.09
% 3.08/1.66  BG Simplification    : 0.03
% 3.08/1.66  Subsumption          : 0.07
% 3.08/1.66  Abstraction          : 0.03
% 3.08/1.66  MUC search           : 0.00
% 3.08/1.66  Cooper               : 0.00
% 3.08/1.66  Total                : 0.92
% 3.08/1.66  Index Insertion      : 0.00
% 3.08/1.66  Index Deletion       : 0.00
% 3.08/1.66  Index Matching       : 0.00
% 3.08/1.66  BG Taut test         : 0.00
%------------------------------------------------------------------------------
