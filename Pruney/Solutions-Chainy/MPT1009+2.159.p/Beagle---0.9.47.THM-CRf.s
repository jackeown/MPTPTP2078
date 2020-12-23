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
% DateTime   : Thu Dec  3 10:15:04 EST 2020

% Result     : Theorem 2.88s
% Output     : CNFRefutation 2.88s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 169 expanded)
%              Number of leaves         :   36 (  77 expanded)
%              Depth                    :   12
%              Number of atoms          :  100 ( 402 expanded)
%              Number of equality atoms :   40 ( 157 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_enumset1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff(f_40,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_101,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,k1_tarski(A),B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r1_tarski(k7_relset_1(k1_tarski(A),B,D,C),k1_tarski(k1_funct_1(D,A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_2)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_44,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k9_relat_1(B,A),k9_relat_1(B,k1_relat_1(B))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_relat_1)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_78,axiom,(
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

tff(f_56,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_89,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,k1_tarski(A),B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
     => ( B != k1_xboole_0
       => k2_relset_1(k1_tarski(A),B,C) = k1_tarski(k1_funct_1(C,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_funct_2)).

tff(f_60,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(c_10,plain,(
    ! [A_10,B_11] : v1_relat_1(k2_zfmisc_1(A_10,B_11)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_40,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_64,plain,(
    ! [B_36,A_37] :
      ( v1_relat_1(B_36)
      | ~ m1_subset_1(B_36,k1_zfmisc_1(A_37))
      | ~ v1_relat_1(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_67,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2')) ),
    inference(resolution,[status(thm)],[c_40,c_64])).

tff(c_70,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_67])).

tff(c_12,plain,(
    ! [A_12] :
      ( k9_relat_1(A_12,k1_relat_1(A_12)) = k2_relat_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_89,plain,(
    ! [B_42,A_43] :
      ( r1_tarski(k9_relat_1(B_42,A_43),k9_relat_1(B_42,k1_relat_1(B_42)))
      | ~ v1_relat_1(B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_95,plain,(
    ! [A_12,A_43] :
      ( r1_tarski(k9_relat_1(A_12,A_43),k2_relat_1(A_12))
      | ~ v1_relat_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_89])).

tff(c_38,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_44,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_42,plain,(
    v1_funct_2('#skF_4',k1_tarski('#skF_1'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_115,plain,(
    ! [A_52,B_53,C_54] :
      ( k1_relset_1(A_52,B_53,C_54) = k1_relat_1(C_54)
      | ~ m1_subset_1(C_54,k1_zfmisc_1(k2_zfmisc_1(A_52,B_53))) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_119,plain,(
    k1_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_115])).

tff(c_141,plain,(
    ! [B_66,A_67,C_68] :
      ( k1_xboole_0 = B_66
      | k1_relset_1(A_67,B_66,C_68) = A_67
      | ~ v1_funct_2(C_68,A_67,B_66)
      | ~ m1_subset_1(C_68,k1_zfmisc_1(k2_zfmisc_1(A_67,B_66))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_144,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4') = k1_tarski('#skF_1')
    | ~ v1_funct_2('#skF_4',k1_tarski('#skF_1'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_40,c_141])).

tff(c_147,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_tarski('#skF_1') = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_119,c_144])).

tff(c_148,plain,(
    k1_tarski('#skF_1') = k1_relat_1('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_147])).

tff(c_153,plain,(
    v1_funct_2('#skF_4',k1_relat_1('#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_42])).

tff(c_104,plain,(
    ! [A_47,B_48,C_49] :
      ( k2_relset_1(A_47,B_48,C_49) = k2_relat_1(C_49)
      | ~ m1_subset_1(C_49,k1_zfmisc_1(k2_zfmisc_1(A_47,B_48))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_108,plain,(
    k2_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_104])).

tff(c_151,plain,(
    k2_relset_1(k1_relat_1('#skF_4'),'#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_108])).

tff(c_152,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_40])).

tff(c_211,plain,(
    ! [A_73,B_74,C_75] :
      ( k2_relset_1(k1_tarski(A_73),B_74,C_75) = k1_tarski(k1_funct_1(C_75,A_73))
      | k1_xboole_0 = B_74
      | ~ m1_subset_1(C_75,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A_73),B_74)))
      | ~ v1_funct_2(C_75,k1_tarski(A_73),B_74)
      | ~ v1_funct_1(C_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_214,plain,(
    ! [B_74,C_75] :
      ( k2_relset_1(k1_tarski('#skF_1'),B_74,C_75) = k1_tarski(k1_funct_1(C_75,'#skF_1'))
      | k1_xboole_0 = B_74
      | ~ m1_subset_1(C_75,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),B_74)))
      | ~ v1_funct_2(C_75,k1_tarski('#skF_1'),B_74)
      | ~ v1_funct_1(C_75) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_148,c_211])).

tff(c_216,plain,(
    ! [B_76,C_77] :
      ( k2_relset_1(k1_relat_1('#skF_4'),B_76,C_77) = k1_tarski(k1_funct_1(C_77,'#skF_1'))
      | k1_xboole_0 = B_76
      | ~ m1_subset_1(C_77,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),B_76)))
      | ~ v1_funct_2(C_77,k1_relat_1('#skF_4'),B_76)
      | ~ v1_funct_1(C_77) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_148,c_214])).

tff(c_219,plain,
    ( k2_relset_1(k1_relat_1('#skF_4'),'#skF_2','#skF_4') = k1_tarski(k1_funct_1('#skF_4','#skF_1'))
    | k1_xboole_0 = '#skF_2'
    | ~ v1_funct_2('#skF_4',k1_relat_1('#skF_4'),'#skF_2')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_152,c_216])).

tff(c_222,plain,
    ( k1_tarski(k1_funct_1('#skF_4','#skF_1')) = k2_relat_1('#skF_4')
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_153,c_151,c_219])).

tff(c_223,plain,(
    k1_tarski(k1_funct_1('#skF_4','#skF_1')) = k2_relat_1('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_222])).

tff(c_124,plain,(
    ! [A_55,B_56,C_57,D_58] :
      ( k7_relset_1(A_55,B_56,C_57,D_58) = k9_relat_1(C_57,D_58)
      | ~ m1_subset_1(C_57,k1_zfmisc_1(k2_zfmisc_1(A_55,B_56))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_127,plain,(
    ! [D_58] : k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4',D_58) = k9_relat_1('#skF_4',D_58) ),
    inference(resolution,[status(thm)],[c_40,c_124])).

tff(c_36,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_128,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_36])).

tff(c_224,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_223,c_128])).

tff(c_235,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_95,c_224])).

tff(c_239,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_235])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:49:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.88/1.74  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.88/1.75  
% 2.88/1.75  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.88/1.76  %$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_enumset1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.88/1.76  
% 2.88/1.76  %Foreground sorts:
% 2.88/1.76  
% 2.88/1.76  
% 2.88/1.76  %Background operators:
% 2.88/1.76  
% 2.88/1.76  
% 2.88/1.76  %Foreground operators:
% 2.88/1.76  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.88/1.76  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.88/1.76  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.88/1.76  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.88/1.76  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.88/1.76  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.88/1.76  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.88/1.76  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.88/1.76  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.88/1.76  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.88/1.76  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.88/1.76  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.88/1.76  tff('#skF_2', type, '#skF_2': $i).
% 2.88/1.76  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.88/1.76  tff('#skF_3', type, '#skF_3': $i).
% 2.88/1.76  tff('#skF_1', type, '#skF_1': $i).
% 2.88/1.76  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.88/1.76  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.88/1.76  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.88/1.76  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.88/1.76  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.88/1.76  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.88/1.76  tff('#skF_4', type, '#skF_4': $i).
% 2.88/1.76  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.88/1.76  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.88/1.76  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.88/1.76  
% 2.88/1.78  tff(f_40, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.88/1.78  tff(f_101, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, k1_tarski(A), B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r1_tarski(k7_relset_1(k1_tarski(A), B, D, C), k1_tarski(k1_funct_1(D, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_funct_2)).
% 2.88/1.78  tff(f_38, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.88/1.78  tff(f_44, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_relat_1)).
% 2.88/1.78  tff(f_48, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k9_relat_1(B, A), k9_relat_1(B, k1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t147_relat_1)).
% 2.88/1.78  tff(f_52, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.88/1.78  tff(f_78, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 2.88/1.78  tff(f_56, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.88/1.78  tff(f_89, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_tarski(A), B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => (k2_relset_1(k1_tarski(A), B, C) = k1_tarski(k1_funct_1(C, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_funct_2)).
% 2.88/1.78  tff(f_60, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 2.88/1.78  tff(c_10, plain, (![A_10, B_11]: (v1_relat_1(k2_zfmisc_1(A_10, B_11)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.88/1.78  tff(c_40, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.88/1.78  tff(c_64, plain, (![B_36, A_37]: (v1_relat_1(B_36) | ~m1_subset_1(B_36, k1_zfmisc_1(A_37)) | ~v1_relat_1(A_37))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.88/1.78  tff(c_67, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2'))), inference(resolution, [status(thm)], [c_40, c_64])).
% 2.88/1.78  tff(c_70, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_67])).
% 2.88/1.78  tff(c_12, plain, (![A_12]: (k9_relat_1(A_12, k1_relat_1(A_12))=k2_relat_1(A_12) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.88/1.78  tff(c_89, plain, (![B_42, A_43]: (r1_tarski(k9_relat_1(B_42, A_43), k9_relat_1(B_42, k1_relat_1(B_42))) | ~v1_relat_1(B_42))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.88/1.78  tff(c_95, plain, (![A_12, A_43]: (r1_tarski(k9_relat_1(A_12, A_43), k2_relat_1(A_12)) | ~v1_relat_1(A_12) | ~v1_relat_1(A_12))), inference(superposition, [status(thm), theory('equality')], [c_12, c_89])).
% 2.88/1.78  tff(c_38, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.88/1.78  tff(c_44, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.88/1.78  tff(c_42, plain, (v1_funct_2('#skF_4', k1_tarski('#skF_1'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.88/1.78  tff(c_115, plain, (![A_52, B_53, C_54]: (k1_relset_1(A_52, B_53, C_54)=k1_relat_1(C_54) | ~m1_subset_1(C_54, k1_zfmisc_1(k2_zfmisc_1(A_52, B_53))))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.88/1.78  tff(c_119, plain, (k1_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_40, c_115])).
% 2.88/1.78  tff(c_141, plain, (![B_66, A_67, C_68]: (k1_xboole_0=B_66 | k1_relset_1(A_67, B_66, C_68)=A_67 | ~v1_funct_2(C_68, A_67, B_66) | ~m1_subset_1(C_68, k1_zfmisc_1(k2_zfmisc_1(A_67, B_66))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.88/1.78  tff(c_144, plain, (k1_xboole_0='#skF_2' | k1_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4')=k1_tarski('#skF_1') | ~v1_funct_2('#skF_4', k1_tarski('#skF_1'), '#skF_2')), inference(resolution, [status(thm)], [c_40, c_141])).
% 2.88/1.78  tff(c_147, plain, (k1_xboole_0='#skF_2' | k1_tarski('#skF_1')=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_119, c_144])).
% 2.88/1.78  tff(c_148, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_38, c_147])).
% 2.88/1.78  tff(c_153, plain, (v1_funct_2('#skF_4', k1_relat_1('#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_148, c_42])).
% 2.88/1.78  tff(c_104, plain, (![A_47, B_48, C_49]: (k2_relset_1(A_47, B_48, C_49)=k2_relat_1(C_49) | ~m1_subset_1(C_49, k1_zfmisc_1(k2_zfmisc_1(A_47, B_48))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.88/1.78  tff(c_108, plain, (k2_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_40, c_104])).
% 2.88/1.78  tff(c_151, plain, (k2_relset_1(k1_relat_1('#skF_4'), '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_148, c_108])).
% 2.88/1.78  tff(c_152, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_148, c_40])).
% 2.88/1.78  tff(c_211, plain, (![A_73, B_74, C_75]: (k2_relset_1(k1_tarski(A_73), B_74, C_75)=k1_tarski(k1_funct_1(C_75, A_73)) | k1_xboole_0=B_74 | ~m1_subset_1(C_75, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A_73), B_74))) | ~v1_funct_2(C_75, k1_tarski(A_73), B_74) | ~v1_funct_1(C_75))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.88/1.78  tff(c_214, plain, (![B_74, C_75]: (k2_relset_1(k1_tarski('#skF_1'), B_74, C_75)=k1_tarski(k1_funct_1(C_75, '#skF_1')) | k1_xboole_0=B_74 | ~m1_subset_1(C_75, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), B_74))) | ~v1_funct_2(C_75, k1_tarski('#skF_1'), B_74) | ~v1_funct_1(C_75))), inference(superposition, [status(thm), theory('equality')], [c_148, c_211])).
% 2.88/1.78  tff(c_216, plain, (![B_76, C_77]: (k2_relset_1(k1_relat_1('#skF_4'), B_76, C_77)=k1_tarski(k1_funct_1(C_77, '#skF_1')) | k1_xboole_0=B_76 | ~m1_subset_1(C_77, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), B_76))) | ~v1_funct_2(C_77, k1_relat_1('#skF_4'), B_76) | ~v1_funct_1(C_77))), inference(demodulation, [status(thm), theory('equality')], [c_148, c_148, c_214])).
% 2.88/1.78  tff(c_219, plain, (k2_relset_1(k1_relat_1('#skF_4'), '#skF_2', '#skF_4')=k1_tarski(k1_funct_1('#skF_4', '#skF_1')) | k1_xboole_0='#skF_2' | ~v1_funct_2('#skF_4', k1_relat_1('#skF_4'), '#skF_2') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_152, c_216])).
% 2.88/1.78  tff(c_222, plain, (k1_tarski(k1_funct_1('#skF_4', '#skF_1'))=k2_relat_1('#skF_4') | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_44, c_153, c_151, c_219])).
% 2.88/1.78  tff(c_223, plain, (k1_tarski(k1_funct_1('#skF_4', '#skF_1'))=k2_relat_1('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_38, c_222])).
% 2.88/1.78  tff(c_124, plain, (![A_55, B_56, C_57, D_58]: (k7_relset_1(A_55, B_56, C_57, D_58)=k9_relat_1(C_57, D_58) | ~m1_subset_1(C_57, k1_zfmisc_1(k2_zfmisc_1(A_55, B_56))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.88/1.78  tff(c_127, plain, (![D_58]: (k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', D_58)=k9_relat_1('#skF_4', D_58))), inference(resolution, [status(thm)], [c_40, c_124])).
% 2.88/1.78  tff(c_36, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.88/1.78  tff(c_128, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_127, c_36])).
% 2.88/1.78  tff(c_224, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_223, c_128])).
% 2.88/1.78  tff(c_235, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_95, c_224])).
% 2.88/1.78  tff(c_239, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_235])).
% 2.88/1.78  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.88/1.78  
% 2.88/1.78  Inference rules
% 2.88/1.78  ----------------------
% 2.88/1.78  #Ref     : 0
% 2.88/1.78  #Sup     : 43
% 2.88/1.78  #Fact    : 0
% 2.88/1.78  #Define  : 0
% 2.88/1.78  #Split   : 0
% 2.88/1.78  #Chain   : 0
% 2.88/1.78  #Close   : 0
% 2.88/1.78  
% 2.88/1.78  Ordering : KBO
% 2.88/1.78  
% 2.88/1.78  Simplification rules
% 2.88/1.78  ----------------------
% 2.88/1.78  #Subsume      : 1
% 2.88/1.78  #Demod        : 27
% 2.88/1.78  #Tautology    : 30
% 2.88/1.78  #SimpNegUnit  : 4
% 2.88/1.78  #BackRed      : 7
% 2.88/1.78  
% 2.88/1.78  #Partial instantiations: 0
% 2.88/1.78  #Strategies tried      : 1
% 2.88/1.78  
% 2.88/1.78  Timing (in seconds)
% 2.88/1.78  ----------------------
% 2.88/1.79  Preprocessing        : 0.53
% 2.88/1.79  Parsing              : 0.28
% 2.88/1.79  CNF conversion       : 0.03
% 2.88/1.79  Main loop            : 0.32
% 2.88/1.79  Inferencing          : 0.12
% 2.88/1.79  Reduction            : 0.10
% 2.88/1.79  Demodulation         : 0.07
% 2.88/1.79  BG Simplification    : 0.02
% 2.88/1.79  Subsumption          : 0.05
% 2.88/1.79  Abstraction          : 0.02
% 2.88/1.79  MUC search           : 0.00
% 2.88/1.79  Cooper               : 0.00
% 2.88/1.79  Total                : 0.91
% 2.88/1.79  Index Insertion      : 0.00
% 2.88/1.79  Index Deletion       : 0.00
% 2.88/1.79  Index Matching       : 0.00
% 2.88/1.79  BG Taut test         : 0.00
%------------------------------------------------------------------------------
