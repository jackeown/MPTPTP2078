%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:04 EST 2020

% Result     : Theorem 2.95s
% Output     : CNFRefutation 2.95s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 117 expanded)
%              Number of leaves         :   39 (  60 expanded)
%              Depth                    :    8
%              Number of atoms          :   99 ( 227 expanded)
%              Number of equality atoms :   28 (  52 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k7_relset_1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_52,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_112,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,k1_tarski(A),B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r1_tarski(k7_relset_1(k1_tarski(A),B,D,C),k1_tarski(k1_funct_1(D,A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_2)).

tff(f_50,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_100,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_72,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_64,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k7_relset_1(A,B,C,D),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relset_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_60,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( k1_relat_1(B) = k1_tarski(A)
       => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_90,axiom,(
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

tff(c_22,plain,(
    ! [A_34,B_35] : v1_relat_1(k2_zfmisc_1(A_34,B_35)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_54,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_88,plain,(
    ! [B_62,A_63] :
      ( v1_relat_1(B_62)
      | ~ m1_subset_1(B_62,k1_zfmisc_1(A_63))
      | ~ v1_relat_1(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_91,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2')) ),
    inference(resolution,[status(thm)],[c_54,c_88])).

tff(c_97,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_91])).

tff(c_58,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_44,plain,(
    ! [A_52] :
      ( m1_subset_1(A_52,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_52),k2_relat_1(A_52))))
      | ~ v1_funct_1(A_52)
      | ~ v1_relat_1(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_265,plain,(
    ! [A_109,B_110,C_111,D_112] :
      ( k7_relset_1(A_109,B_110,C_111,D_112) = k9_relat_1(C_111,D_112)
      | ~ m1_subset_1(C_111,k1_zfmisc_1(k2_zfmisc_1(A_109,B_110))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_277,plain,(
    ! [A_52,D_112] :
      ( k7_relset_1(k1_relat_1(A_52),k2_relat_1(A_52),A_52,D_112) = k9_relat_1(A_52,D_112)
      | ~ v1_funct_1(A_52)
      | ~ v1_relat_1(A_52) ) ),
    inference(resolution,[status(thm)],[c_44,c_265])).

tff(c_195,plain,(
    ! [A_90,B_91,C_92,D_93] :
      ( m1_subset_1(k7_relset_1(A_90,B_91,C_92,D_93),k1_zfmisc_1(B_91))
      | ~ m1_subset_1(C_92,k1_zfmisc_1(k2_zfmisc_1(A_90,B_91))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_16,plain,(
    ! [A_29,B_30] :
      ( r1_tarski(A_29,B_30)
      | ~ m1_subset_1(A_29,k1_zfmisc_1(B_30)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_209,plain,(
    ! [A_94,B_95,C_96,D_97] :
      ( r1_tarski(k7_relset_1(A_94,B_95,C_96,D_97),B_95)
      | ~ m1_subset_1(C_96,k1_zfmisc_1(k2_zfmisc_1(A_94,B_95))) ) ),
    inference(resolution,[status(thm)],[c_195,c_16])).

tff(c_642,plain,(
    ! [A_188,D_189] :
      ( r1_tarski(k7_relset_1(k1_relat_1(A_188),k2_relat_1(A_188),A_188,D_189),k2_relat_1(A_188))
      | ~ v1_funct_1(A_188)
      | ~ v1_relat_1(A_188) ) ),
    inference(resolution,[status(thm)],[c_44,c_209])).

tff(c_667,plain,(
    ! [A_194,D_195] :
      ( r1_tarski(k9_relat_1(A_194,D_195),k2_relat_1(A_194))
      | ~ v1_funct_1(A_194)
      | ~ v1_relat_1(A_194)
      | ~ v1_funct_1(A_194)
      | ~ v1_relat_1(A_194) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_277,c_642])).

tff(c_24,plain,(
    ! [B_37,A_36] :
      ( k1_tarski(k1_funct_1(B_37,A_36)) = k2_relat_1(B_37)
      | k1_tarski(A_36) != k1_relat_1(B_37)
      | ~ v1_funct_1(B_37)
      | ~ v1_relat_1(B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_278,plain,(
    ! [D_112] : k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4',D_112) = k9_relat_1('#skF_4',D_112) ),
    inference(resolution,[status(thm)],[c_54,c_265])).

tff(c_50,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_281,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_278,c_50])).

tff(c_309,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_281])).

tff(c_311,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_58,c_309])).

tff(c_322,plain,(
    k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_311])).

tff(c_52,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_56,plain,(
    v1_funct_2('#skF_4',k1_tarski('#skF_1'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_131,plain,(
    ! [A_76,B_77,C_78] :
      ( k1_relset_1(A_76,B_77,C_78) = k1_relat_1(C_78)
      | ~ m1_subset_1(C_78,k1_zfmisc_1(k2_zfmisc_1(A_76,B_77))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_139,plain,(
    k1_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_131])).

tff(c_454,plain,(
    ! [B_159,A_160,C_161] :
      ( k1_xboole_0 = B_159
      | k1_relset_1(A_160,B_159,C_161) = A_160
      | ~ v1_funct_2(C_161,A_160,B_159)
      | ~ m1_subset_1(C_161,k1_zfmisc_1(k2_zfmisc_1(A_160,B_159))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_464,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4') = k1_tarski('#skF_1')
    | ~ v1_funct_2('#skF_4',k1_tarski('#skF_1'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_454])).

tff(c_473,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_tarski('#skF_1') = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_139,c_464])).

tff(c_475,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_322,c_52,c_473])).

tff(c_476,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_311])).

tff(c_670,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_667,c_476])).

tff(c_677,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_58,c_670])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n024.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:31:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.95/1.48  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.95/1.48  
% 2.95/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.95/1.49  %$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k7_relset_1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.95/1.49  
% 2.95/1.49  %Foreground sorts:
% 2.95/1.49  
% 2.95/1.49  
% 2.95/1.49  %Background operators:
% 2.95/1.49  
% 2.95/1.49  
% 2.95/1.49  %Foreground operators:
% 2.95/1.49  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.95/1.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.95/1.49  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.95/1.49  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.95/1.49  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.95/1.49  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.95/1.49  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.95/1.49  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.95/1.49  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.95/1.49  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.95/1.49  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.95/1.49  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.95/1.49  tff('#skF_2', type, '#skF_2': $i).
% 2.95/1.49  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.95/1.49  tff('#skF_3', type, '#skF_3': $i).
% 2.95/1.49  tff('#skF_1', type, '#skF_1': $i).
% 2.95/1.49  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.95/1.49  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.95/1.49  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.95/1.49  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.95/1.49  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.95/1.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.95/1.49  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.95/1.49  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.95/1.49  tff('#skF_4', type, '#skF_4': $i).
% 2.95/1.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.95/1.49  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.95/1.49  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.95/1.49  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.95/1.49  
% 2.95/1.50  tff(f_52, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.95/1.50  tff(f_112, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, k1_tarski(A), B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r1_tarski(k7_relset_1(k1_tarski(A), B, D, C), k1_tarski(k1_funct_1(D, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_funct_2)).
% 2.95/1.50  tff(f_50, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.95/1.50  tff(f_100, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_funct_2)).
% 2.95/1.50  tff(f_72, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 2.95/1.50  tff(f_64, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k7_relset_1(A, B, C, D), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relset_1)).
% 2.95/1.50  tff(f_43, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.95/1.50  tff(f_60, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_funct_1)).
% 2.95/1.50  tff(f_68, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.95/1.50  tff(f_90, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 2.95/1.50  tff(c_22, plain, (![A_34, B_35]: (v1_relat_1(k2_zfmisc_1(A_34, B_35)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.95/1.50  tff(c_54, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_112])).
% 2.95/1.50  tff(c_88, plain, (![B_62, A_63]: (v1_relat_1(B_62) | ~m1_subset_1(B_62, k1_zfmisc_1(A_63)) | ~v1_relat_1(A_63))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.95/1.50  tff(c_91, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2'))), inference(resolution, [status(thm)], [c_54, c_88])).
% 2.95/1.50  tff(c_97, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_91])).
% 2.95/1.50  tff(c_58, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_112])).
% 2.95/1.50  tff(c_44, plain, (![A_52]: (m1_subset_1(A_52, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_52), k2_relat_1(A_52)))) | ~v1_funct_1(A_52) | ~v1_relat_1(A_52))), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.95/1.50  tff(c_265, plain, (![A_109, B_110, C_111, D_112]: (k7_relset_1(A_109, B_110, C_111, D_112)=k9_relat_1(C_111, D_112) | ~m1_subset_1(C_111, k1_zfmisc_1(k2_zfmisc_1(A_109, B_110))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.95/1.50  tff(c_277, plain, (![A_52, D_112]: (k7_relset_1(k1_relat_1(A_52), k2_relat_1(A_52), A_52, D_112)=k9_relat_1(A_52, D_112) | ~v1_funct_1(A_52) | ~v1_relat_1(A_52))), inference(resolution, [status(thm)], [c_44, c_265])).
% 2.95/1.50  tff(c_195, plain, (![A_90, B_91, C_92, D_93]: (m1_subset_1(k7_relset_1(A_90, B_91, C_92, D_93), k1_zfmisc_1(B_91)) | ~m1_subset_1(C_92, k1_zfmisc_1(k2_zfmisc_1(A_90, B_91))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.95/1.50  tff(c_16, plain, (![A_29, B_30]: (r1_tarski(A_29, B_30) | ~m1_subset_1(A_29, k1_zfmisc_1(B_30)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.95/1.50  tff(c_209, plain, (![A_94, B_95, C_96, D_97]: (r1_tarski(k7_relset_1(A_94, B_95, C_96, D_97), B_95) | ~m1_subset_1(C_96, k1_zfmisc_1(k2_zfmisc_1(A_94, B_95))))), inference(resolution, [status(thm)], [c_195, c_16])).
% 2.95/1.50  tff(c_642, plain, (![A_188, D_189]: (r1_tarski(k7_relset_1(k1_relat_1(A_188), k2_relat_1(A_188), A_188, D_189), k2_relat_1(A_188)) | ~v1_funct_1(A_188) | ~v1_relat_1(A_188))), inference(resolution, [status(thm)], [c_44, c_209])).
% 2.95/1.50  tff(c_667, plain, (![A_194, D_195]: (r1_tarski(k9_relat_1(A_194, D_195), k2_relat_1(A_194)) | ~v1_funct_1(A_194) | ~v1_relat_1(A_194) | ~v1_funct_1(A_194) | ~v1_relat_1(A_194))), inference(superposition, [status(thm), theory('equality')], [c_277, c_642])).
% 2.95/1.50  tff(c_24, plain, (![B_37, A_36]: (k1_tarski(k1_funct_1(B_37, A_36))=k2_relat_1(B_37) | k1_tarski(A_36)!=k1_relat_1(B_37) | ~v1_funct_1(B_37) | ~v1_relat_1(B_37))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.95/1.50  tff(c_278, plain, (![D_112]: (k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', D_112)=k9_relat_1('#skF_4', D_112))), inference(resolution, [status(thm)], [c_54, c_265])).
% 2.95/1.50  tff(c_50, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_112])).
% 2.95/1.50  tff(c_281, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_278, c_50])).
% 2.95/1.50  tff(c_309, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_24, c_281])).
% 2.95/1.50  tff(c_311, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_97, c_58, c_309])).
% 2.95/1.50  tff(c_322, plain, (k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(splitLeft, [status(thm)], [c_311])).
% 2.95/1.50  tff(c_52, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_112])).
% 2.95/1.50  tff(c_56, plain, (v1_funct_2('#skF_4', k1_tarski('#skF_1'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_112])).
% 2.95/1.50  tff(c_131, plain, (![A_76, B_77, C_78]: (k1_relset_1(A_76, B_77, C_78)=k1_relat_1(C_78) | ~m1_subset_1(C_78, k1_zfmisc_1(k2_zfmisc_1(A_76, B_77))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.95/1.50  tff(c_139, plain, (k1_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_54, c_131])).
% 2.95/1.50  tff(c_454, plain, (![B_159, A_160, C_161]: (k1_xboole_0=B_159 | k1_relset_1(A_160, B_159, C_161)=A_160 | ~v1_funct_2(C_161, A_160, B_159) | ~m1_subset_1(C_161, k1_zfmisc_1(k2_zfmisc_1(A_160, B_159))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.95/1.50  tff(c_464, plain, (k1_xboole_0='#skF_2' | k1_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4')=k1_tarski('#skF_1') | ~v1_funct_2('#skF_4', k1_tarski('#skF_1'), '#skF_2')), inference(resolution, [status(thm)], [c_54, c_454])).
% 2.95/1.50  tff(c_473, plain, (k1_xboole_0='#skF_2' | k1_tarski('#skF_1')=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_139, c_464])).
% 2.95/1.50  tff(c_475, plain, $false, inference(negUnitSimplification, [status(thm)], [c_322, c_52, c_473])).
% 2.95/1.50  tff(c_476, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4'))), inference(splitRight, [status(thm)], [c_311])).
% 2.95/1.50  tff(c_670, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_667, c_476])).
% 2.95/1.50  tff(c_677, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_97, c_58, c_670])).
% 2.95/1.50  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.95/1.50  
% 2.95/1.50  Inference rules
% 2.95/1.50  ----------------------
% 2.95/1.50  #Ref     : 0
% 2.95/1.50  #Sup     : 131
% 2.95/1.50  #Fact    : 0
% 2.95/1.50  #Define  : 0
% 2.95/1.50  #Split   : 2
% 2.95/1.50  #Chain   : 0
% 2.95/1.50  #Close   : 0
% 2.95/1.50  
% 2.95/1.50  Ordering : KBO
% 2.95/1.50  
% 2.95/1.50  Simplification rules
% 2.95/1.50  ----------------------
% 2.95/1.50  #Subsume      : 18
% 2.95/1.50  #Demod        : 47
% 2.95/1.50  #Tautology    : 53
% 2.95/1.50  #SimpNegUnit  : 1
% 2.95/1.50  #BackRed      : 8
% 2.95/1.50  
% 2.95/1.50  #Partial instantiations: 0
% 2.95/1.50  #Strategies tried      : 1
% 2.95/1.50  
% 2.95/1.50  Timing (in seconds)
% 2.95/1.50  ----------------------
% 2.95/1.50  Preprocessing        : 0.35
% 2.95/1.50  Parsing              : 0.19
% 2.95/1.50  CNF conversion       : 0.02
% 2.95/1.50  Main loop            : 0.32
% 2.95/1.50  Inferencing          : 0.13
% 2.95/1.50  Reduction            : 0.10
% 2.95/1.50  Demodulation         : 0.07
% 2.95/1.50  BG Simplification    : 0.02
% 2.95/1.50  Subsumption          : 0.05
% 2.95/1.50  Abstraction          : 0.02
% 2.95/1.50  MUC search           : 0.00
% 2.95/1.50  Cooper               : 0.00
% 2.95/1.50  Total                : 0.70
% 2.95/1.50  Index Insertion      : 0.00
% 2.95/1.50  Index Deletion       : 0.00
% 2.95/1.50  Index Matching       : 0.00
% 2.95/1.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
