%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:55 EST 2020

% Result     : Theorem 2.22s
% Output     : CNFRefutation 2.22s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 166 expanded)
%              Number of leaves         :   35 (  76 expanded)
%              Depth                    :   12
%              Number of atoms          :   94 ( 396 expanded)
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

tff(f_96,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,k1_tarski(A),B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r1_tarski(k7_relset_1(k1_tarski(A),B,D,C),k1_tarski(k1_funct_1(D,A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_2)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k9_relat_1(B,A),k9_relat_1(B,k1_relat_1(B))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_relat_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_73,axiom,(
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

tff(f_51,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_84,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,k1_tarski(A),B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
     => ( B != k1_xboole_0
       => k2_relset_1(k1_tarski(A),B,C) = k1_tarski(k1_funct_1(C,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_funct_2)).

tff(f_55,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(c_38,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_70,plain,(
    ! [C_33,A_34,B_35] :
      ( v1_relat_1(C_33)
      | ~ m1_subset_1(C_33,k1_zfmisc_1(k2_zfmisc_1(A_34,B_35))) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_74,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_70])).

tff(c_8,plain,(
    ! [A_7] :
      ( k9_relat_1(A_7,k1_relat_1(A_7)) = k2_relat_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_84,plain,(
    ! [B_39,A_40] :
      ( r1_tarski(k9_relat_1(B_39,A_40),k9_relat_1(B_39,k1_relat_1(B_39)))
      | ~ v1_relat_1(B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_90,plain,(
    ! [A_7,A_40] :
      ( r1_tarski(k9_relat_1(A_7,A_40),k2_relat_1(A_7))
      | ~ v1_relat_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_84])).

tff(c_36,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_42,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_40,plain,(
    v1_funct_2('#skF_4',k1_tarski('#skF_1'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_109,plain,(
    ! [A_48,B_49,C_50] :
      ( k1_relset_1(A_48,B_49,C_50) = k1_relat_1(C_50)
      | ~ m1_subset_1(C_50,k1_zfmisc_1(k2_zfmisc_1(A_48,B_49))) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_113,plain,(
    k1_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_109])).

tff(c_136,plain,(
    ! [B_63,A_64,C_65] :
      ( k1_xboole_0 = B_63
      | k1_relset_1(A_64,B_63,C_65) = A_64
      | ~ v1_funct_2(C_65,A_64,B_63)
      | ~ m1_subset_1(C_65,k1_zfmisc_1(k2_zfmisc_1(A_64,B_63))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_139,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4') = k1_tarski('#skF_1')
    | ~ v1_funct_2('#skF_4',k1_tarski('#skF_1'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_136])).

tff(c_142,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_tarski('#skF_1') = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_113,c_139])).

tff(c_143,plain,(
    k1_tarski('#skF_1') = k1_relat_1('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_142])).

tff(c_148,plain,(
    v1_funct_2('#skF_4',k1_relat_1('#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_143,c_40])).

tff(c_100,plain,(
    ! [A_45,B_46,C_47] :
      ( k2_relset_1(A_45,B_46,C_47) = k2_relat_1(C_47)
      | ~ m1_subset_1(C_47,k1_zfmisc_1(k2_zfmisc_1(A_45,B_46))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_104,plain,(
    k2_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_100])).

tff(c_146,plain,(
    k2_relset_1(k1_relat_1('#skF_4'),'#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_143,c_104])).

tff(c_147,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_143,c_38])).

tff(c_204,plain,(
    ! [A_70,B_71,C_72] :
      ( k2_relset_1(k1_tarski(A_70),B_71,C_72) = k1_tarski(k1_funct_1(C_72,A_70))
      | k1_xboole_0 = B_71
      | ~ m1_subset_1(C_72,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A_70),B_71)))
      | ~ v1_funct_2(C_72,k1_tarski(A_70),B_71)
      | ~ v1_funct_1(C_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_207,plain,(
    ! [B_71,C_72] :
      ( k2_relset_1(k1_tarski('#skF_1'),B_71,C_72) = k1_tarski(k1_funct_1(C_72,'#skF_1'))
      | k1_xboole_0 = B_71
      | ~ m1_subset_1(C_72,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),B_71)))
      | ~ v1_funct_2(C_72,k1_tarski('#skF_1'),B_71)
      | ~ v1_funct_1(C_72) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_143,c_204])).

tff(c_209,plain,(
    ! [B_73,C_74] :
      ( k2_relset_1(k1_relat_1('#skF_4'),B_73,C_74) = k1_tarski(k1_funct_1(C_74,'#skF_1'))
      | k1_xboole_0 = B_73
      | ~ m1_subset_1(C_74,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),B_73)))
      | ~ v1_funct_2(C_74,k1_relat_1('#skF_4'),B_73)
      | ~ v1_funct_1(C_74) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_143,c_143,c_207])).

tff(c_212,plain,
    ( k2_relset_1(k1_relat_1('#skF_4'),'#skF_2','#skF_4') = k1_tarski(k1_funct_1('#skF_4','#skF_1'))
    | k1_xboole_0 = '#skF_2'
    | ~ v1_funct_2('#skF_4',k1_relat_1('#skF_4'),'#skF_2')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_147,c_209])).

tff(c_215,plain,
    ( k1_tarski(k1_funct_1('#skF_4','#skF_1')) = k2_relat_1('#skF_4')
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_148,c_146,c_212])).

tff(c_216,plain,(
    k1_tarski(k1_funct_1('#skF_4','#skF_1')) = k2_relat_1('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_215])).

tff(c_120,plain,(
    ! [A_54,B_55,C_56,D_57] :
      ( k7_relset_1(A_54,B_55,C_56,D_57) = k9_relat_1(C_56,D_57)
      | ~ m1_subset_1(C_56,k1_zfmisc_1(k2_zfmisc_1(A_54,B_55))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_123,plain,(
    ! [D_57] : k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4',D_57) = k9_relat_1('#skF_4',D_57) ),
    inference(resolution,[status(thm)],[c_38,c_120])).

tff(c_34,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_124,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_34])).

tff(c_217,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_216,c_124])).

tff(c_228,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_90,c_217])).

tff(c_232,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_228])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n011.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 19:34:57 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.22/1.20  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.22/1.21  
% 2.22/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.22/1.21  %$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_enumset1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.22/1.21  
% 2.22/1.21  %Foreground sorts:
% 2.22/1.21  
% 2.22/1.21  
% 2.22/1.21  %Background operators:
% 2.22/1.21  
% 2.22/1.21  
% 2.22/1.21  %Foreground operators:
% 2.22/1.21  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.22/1.21  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.22/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.22/1.21  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.22/1.21  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.22/1.21  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.22/1.21  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.22/1.21  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.22/1.21  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.22/1.21  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.22/1.21  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.22/1.21  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.22/1.21  tff('#skF_2', type, '#skF_2': $i).
% 2.22/1.21  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.22/1.21  tff('#skF_3', type, '#skF_3': $i).
% 2.22/1.21  tff('#skF_1', type, '#skF_1': $i).
% 2.22/1.21  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.22/1.21  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.22/1.21  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.22/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.22/1.21  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.22/1.21  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.22/1.21  tff('#skF_4', type, '#skF_4': $i).
% 2.22/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.22/1.21  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.22/1.21  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.22/1.21  
% 2.22/1.22  tff(f_96, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, k1_tarski(A), B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r1_tarski(k7_relset_1(k1_tarski(A), B, D, C), k1_tarski(k1_funct_1(D, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_funct_2)).
% 2.22/1.22  tff(f_43, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.22/1.22  tff(f_35, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_relat_1)).
% 2.22/1.22  tff(f_39, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k9_relat_1(B, A), k9_relat_1(B, k1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t147_relat_1)).
% 2.22/1.22  tff(f_47, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.22/1.22  tff(f_73, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 2.22/1.22  tff(f_51, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.22/1.22  tff(f_84, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_tarski(A), B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => (k2_relset_1(k1_tarski(A), B, C) = k1_tarski(k1_funct_1(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_funct_2)).
% 2.22/1.22  tff(f_55, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 2.22/1.22  tff(c_38, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.22/1.22  tff(c_70, plain, (![C_33, A_34, B_35]: (v1_relat_1(C_33) | ~m1_subset_1(C_33, k1_zfmisc_1(k2_zfmisc_1(A_34, B_35))))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.22/1.22  tff(c_74, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_38, c_70])).
% 2.22/1.22  tff(c_8, plain, (![A_7]: (k9_relat_1(A_7, k1_relat_1(A_7))=k2_relat_1(A_7) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.22/1.22  tff(c_84, plain, (![B_39, A_40]: (r1_tarski(k9_relat_1(B_39, A_40), k9_relat_1(B_39, k1_relat_1(B_39))) | ~v1_relat_1(B_39))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.22/1.22  tff(c_90, plain, (![A_7, A_40]: (r1_tarski(k9_relat_1(A_7, A_40), k2_relat_1(A_7)) | ~v1_relat_1(A_7) | ~v1_relat_1(A_7))), inference(superposition, [status(thm), theory('equality')], [c_8, c_84])).
% 2.22/1.22  tff(c_36, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.22/1.22  tff(c_42, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.22/1.22  tff(c_40, plain, (v1_funct_2('#skF_4', k1_tarski('#skF_1'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.22/1.22  tff(c_109, plain, (![A_48, B_49, C_50]: (k1_relset_1(A_48, B_49, C_50)=k1_relat_1(C_50) | ~m1_subset_1(C_50, k1_zfmisc_1(k2_zfmisc_1(A_48, B_49))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.22/1.22  tff(c_113, plain, (k1_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_38, c_109])).
% 2.22/1.22  tff(c_136, plain, (![B_63, A_64, C_65]: (k1_xboole_0=B_63 | k1_relset_1(A_64, B_63, C_65)=A_64 | ~v1_funct_2(C_65, A_64, B_63) | ~m1_subset_1(C_65, k1_zfmisc_1(k2_zfmisc_1(A_64, B_63))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.22/1.22  tff(c_139, plain, (k1_xboole_0='#skF_2' | k1_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4')=k1_tarski('#skF_1') | ~v1_funct_2('#skF_4', k1_tarski('#skF_1'), '#skF_2')), inference(resolution, [status(thm)], [c_38, c_136])).
% 2.22/1.22  tff(c_142, plain, (k1_xboole_0='#skF_2' | k1_tarski('#skF_1')=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_113, c_139])).
% 2.22/1.22  tff(c_143, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_36, c_142])).
% 2.22/1.22  tff(c_148, plain, (v1_funct_2('#skF_4', k1_relat_1('#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_143, c_40])).
% 2.22/1.22  tff(c_100, plain, (![A_45, B_46, C_47]: (k2_relset_1(A_45, B_46, C_47)=k2_relat_1(C_47) | ~m1_subset_1(C_47, k1_zfmisc_1(k2_zfmisc_1(A_45, B_46))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.22/1.22  tff(c_104, plain, (k2_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_38, c_100])).
% 2.22/1.22  tff(c_146, plain, (k2_relset_1(k1_relat_1('#skF_4'), '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_143, c_104])).
% 2.22/1.22  tff(c_147, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_143, c_38])).
% 2.22/1.22  tff(c_204, plain, (![A_70, B_71, C_72]: (k2_relset_1(k1_tarski(A_70), B_71, C_72)=k1_tarski(k1_funct_1(C_72, A_70)) | k1_xboole_0=B_71 | ~m1_subset_1(C_72, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A_70), B_71))) | ~v1_funct_2(C_72, k1_tarski(A_70), B_71) | ~v1_funct_1(C_72))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.22/1.22  tff(c_207, plain, (![B_71, C_72]: (k2_relset_1(k1_tarski('#skF_1'), B_71, C_72)=k1_tarski(k1_funct_1(C_72, '#skF_1')) | k1_xboole_0=B_71 | ~m1_subset_1(C_72, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), B_71))) | ~v1_funct_2(C_72, k1_tarski('#skF_1'), B_71) | ~v1_funct_1(C_72))), inference(superposition, [status(thm), theory('equality')], [c_143, c_204])).
% 2.22/1.22  tff(c_209, plain, (![B_73, C_74]: (k2_relset_1(k1_relat_1('#skF_4'), B_73, C_74)=k1_tarski(k1_funct_1(C_74, '#skF_1')) | k1_xboole_0=B_73 | ~m1_subset_1(C_74, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), B_73))) | ~v1_funct_2(C_74, k1_relat_1('#skF_4'), B_73) | ~v1_funct_1(C_74))), inference(demodulation, [status(thm), theory('equality')], [c_143, c_143, c_207])).
% 2.22/1.22  tff(c_212, plain, (k2_relset_1(k1_relat_1('#skF_4'), '#skF_2', '#skF_4')=k1_tarski(k1_funct_1('#skF_4', '#skF_1')) | k1_xboole_0='#skF_2' | ~v1_funct_2('#skF_4', k1_relat_1('#skF_4'), '#skF_2') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_147, c_209])).
% 2.22/1.22  tff(c_215, plain, (k1_tarski(k1_funct_1('#skF_4', '#skF_1'))=k2_relat_1('#skF_4') | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_148, c_146, c_212])).
% 2.22/1.22  tff(c_216, plain, (k1_tarski(k1_funct_1('#skF_4', '#skF_1'))=k2_relat_1('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_36, c_215])).
% 2.22/1.22  tff(c_120, plain, (![A_54, B_55, C_56, D_57]: (k7_relset_1(A_54, B_55, C_56, D_57)=k9_relat_1(C_56, D_57) | ~m1_subset_1(C_56, k1_zfmisc_1(k2_zfmisc_1(A_54, B_55))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.22/1.22  tff(c_123, plain, (![D_57]: (k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', D_57)=k9_relat_1('#skF_4', D_57))), inference(resolution, [status(thm)], [c_38, c_120])).
% 2.22/1.22  tff(c_34, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.22/1.22  tff(c_124, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_123, c_34])).
% 2.22/1.22  tff(c_217, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_216, c_124])).
% 2.22/1.22  tff(c_228, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_90, c_217])).
% 2.22/1.22  tff(c_232, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74, c_228])).
% 2.22/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.22/1.22  
% 2.22/1.22  Inference rules
% 2.22/1.22  ----------------------
% 2.22/1.22  #Ref     : 0
% 2.22/1.22  #Sup     : 43
% 2.22/1.22  #Fact    : 0
% 2.22/1.22  #Define  : 0
% 2.22/1.22  #Split   : 0
% 2.22/1.22  #Chain   : 0
% 2.22/1.22  #Close   : 0
% 2.22/1.22  
% 2.22/1.22  Ordering : KBO
% 2.22/1.22  
% 2.22/1.22  Simplification rules
% 2.22/1.22  ----------------------
% 2.22/1.22  #Subsume      : 1
% 2.22/1.23  #Demod        : 25
% 2.22/1.23  #Tautology    : 30
% 2.22/1.23  #SimpNegUnit  : 4
% 2.22/1.23  #BackRed      : 7
% 2.22/1.23  
% 2.22/1.23  #Partial instantiations: 0
% 2.22/1.23  #Strategies tried      : 1
% 2.22/1.23  
% 2.22/1.23  Timing (in seconds)
% 2.22/1.23  ----------------------
% 2.22/1.23  Preprocessing        : 0.33
% 2.22/1.23  Parsing              : 0.18
% 2.22/1.23  CNF conversion       : 0.02
% 2.22/1.23  Main loop            : 0.19
% 2.22/1.23  Inferencing          : 0.07
% 2.22/1.23  Reduction            : 0.06
% 2.22/1.23  Demodulation         : 0.04
% 2.22/1.23  BG Simplification    : 0.01
% 2.22/1.23  Subsumption          : 0.03
% 2.22/1.23  Abstraction          : 0.01
% 2.22/1.23  MUC search           : 0.00
% 2.22/1.23  Cooper               : 0.00
% 2.22/1.23  Total                : 0.56
% 2.22/1.23  Index Insertion      : 0.00
% 2.22/1.23  Index Deletion       : 0.00
% 2.22/1.23  Index Matching       : 0.00
% 2.22/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
