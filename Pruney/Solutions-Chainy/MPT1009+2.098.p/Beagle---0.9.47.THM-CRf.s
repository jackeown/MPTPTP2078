%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:55 EST 2020

% Result     : Theorem 2.94s
% Output     : CNFRefutation 2.94s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 108 expanded)
%              Number of leaves         :   37 (  57 expanded)
%              Depth                    :    8
%              Number of atoms          :   99 ( 220 expanded)
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

tff(f_107,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,k1_tarski(A),B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r1_tarski(k7_relset_1(k1_tarski(A),B,D,C),k1_tarski(k1_funct_1(D,A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_2)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_87,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_59,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_95,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r1_tarski(k7_relset_1(A,B,D,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_funct_2)).

tff(f_47,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( k1_relat_1(B) = k1_tarski(A)
       => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_77,axiom,(
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

tff(c_48,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_71,plain,(
    ! [C_52,A_53,B_54] :
      ( v1_relat_1(C_52)
      | ~ m1_subset_1(C_52,k1_zfmisc_1(k2_zfmisc_1(A_53,B_54))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_75,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_71])).

tff(c_52,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_38,plain,(
    ! [A_44] :
      ( v1_funct_2(A_44,k1_relat_1(A_44),k2_relat_1(A_44))
      | ~ v1_funct_1(A_44)
      | ~ v1_relat_1(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_36,plain,(
    ! [A_44] :
      ( m1_subset_1(A_44,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_44),k2_relat_1(A_44))))
      | ~ v1_funct_1(A_44)
      | ~ v1_relat_1(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_133,plain,(
    ! [A_76,B_77,C_78,D_79] :
      ( k7_relset_1(A_76,B_77,C_78,D_79) = k9_relat_1(C_78,D_79)
      | ~ m1_subset_1(C_78,k1_zfmisc_1(k2_zfmisc_1(A_76,B_77))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_138,plain,(
    ! [A_44,D_79] :
      ( k7_relset_1(k1_relat_1(A_44),k2_relat_1(A_44),A_44,D_79) = k9_relat_1(A_44,D_79)
      | ~ v1_funct_1(A_44)
      | ~ v1_relat_1(A_44) ) ),
    inference(resolution,[status(thm)],[c_36,c_133])).

tff(c_288,plain,(
    ! [A_124,B_125,D_126,C_127] :
      ( r1_tarski(k7_relset_1(A_124,B_125,D_126,C_127),B_125)
      | ~ m1_subset_1(D_126,k1_zfmisc_1(k2_zfmisc_1(A_124,B_125)))
      | ~ v1_funct_2(D_126,A_124,B_125)
      | ~ v1_funct_1(D_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_297,plain,(
    ! [A_128,C_129] :
      ( r1_tarski(k7_relset_1(k1_relat_1(A_128),k2_relat_1(A_128),A_128,C_129),k2_relat_1(A_128))
      | ~ v1_funct_2(A_128,k1_relat_1(A_128),k2_relat_1(A_128))
      | ~ v1_funct_1(A_128)
      | ~ v1_relat_1(A_128) ) ),
    inference(resolution,[status(thm)],[c_36,c_288])).

tff(c_302,plain,(
    ! [A_131,D_132] :
      ( r1_tarski(k9_relat_1(A_131,D_132),k2_relat_1(A_131))
      | ~ v1_funct_2(A_131,k1_relat_1(A_131),k2_relat_1(A_131))
      | ~ v1_funct_1(A_131)
      | ~ v1_relat_1(A_131)
      | ~ v1_funct_1(A_131)
      | ~ v1_relat_1(A_131) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_138,c_297])).

tff(c_306,plain,(
    ! [A_133,D_134] :
      ( r1_tarski(k9_relat_1(A_133,D_134),k2_relat_1(A_133))
      | ~ v1_funct_1(A_133)
      | ~ v1_relat_1(A_133) ) ),
    inference(resolution,[status(thm)],[c_38,c_302])).

tff(c_150,plain,(
    ! [B_81,A_82] :
      ( k1_tarski(k1_funct_1(B_81,A_82)) = k2_relat_1(B_81)
      | k1_tarski(A_82) != k1_relat_1(B_81)
      | ~ v1_funct_1(B_81)
      | ~ v1_relat_1(B_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_139,plain,(
    ! [D_79] : k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4',D_79) = k9_relat_1('#skF_4',D_79) ),
    inference(resolution,[status(thm)],[c_48,c_133])).

tff(c_44,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_140,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_44])).

tff(c_156,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_150,c_140])).

tff(c_162,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_52,c_156])).

tff(c_164,plain,(
    k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_162])).

tff(c_46,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_50,plain,(
    v1_funct_2('#skF_4',k1_tarski('#skF_1'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_95,plain,(
    ! [A_63,B_64,C_65] :
      ( k1_relset_1(A_63,B_64,C_65) = k1_relat_1(C_65)
      | ~ m1_subset_1(C_65,k1_zfmisc_1(k2_zfmisc_1(A_63,B_64))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_99,plain,(
    k1_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_95])).

tff(c_185,plain,(
    ! [B_95,A_96,C_97] :
      ( k1_xboole_0 = B_95
      | k1_relset_1(A_96,B_95,C_97) = A_96
      | ~ v1_funct_2(C_97,A_96,B_95)
      | ~ m1_subset_1(C_97,k1_zfmisc_1(k2_zfmisc_1(A_96,B_95))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_191,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4') = k1_tarski('#skF_1')
    | ~ v1_funct_2('#skF_4',k1_tarski('#skF_1'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_185])).

tff(c_195,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_tarski('#skF_1') = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_99,c_191])).

tff(c_197,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_164,c_46,c_195])).

tff(c_198,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_162])).

tff(c_309,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_306,c_198])).

tff(c_313,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_52,c_309])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.34  % Computer   : n021.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % DateTime   : Tue Dec  1 15:36:49 EST 2020
% 0.15/0.34  % CPUTime    : 
% 0.15/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.94/1.73  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.94/1.73  
% 2.94/1.73  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.94/1.74  %$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k7_relset_1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.94/1.74  
% 2.94/1.74  %Foreground sorts:
% 2.94/1.74  
% 2.94/1.74  
% 2.94/1.74  %Background operators:
% 2.94/1.74  
% 2.94/1.74  
% 2.94/1.74  %Foreground operators:
% 2.94/1.74  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.94/1.74  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.94/1.74  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.94/1.74  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.94/1.74  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.94/1.74  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.94/1.74  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.94/1.74  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.94/1.74  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.94/1.74  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.94/1.74  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.94/1.74  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.94/1.74  tff('#skF_2', type, '#skF_2': $i).
% 2.94/1.74  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.94/1.74  tff('#skF_3', type, '#skF_3': $i).
% 2.94/1.74  tff('#skF_1', type, '#skF_1': $i).
% 2.94/1.74  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.94/1.74  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.94/1.74  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.94/1.74  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.94/1.74  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.94/1.74  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.94/1.74  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.94/1.74  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.94/1.74  tff('#skF_4', type, '#skF_4': $i).
% 2.94/1.74  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.94/1.74  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.94/1.74  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.94/1.74  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.94/1.74  
% 2.94/1.76  tff(f_107, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, k1_tarski(A), B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r1_tarski(k7_relset_1(k1_tarski(A), B, D, C), k1_tarski(k1_funct_1(D, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_funct_2)).
% 2.94/1.76  tff(f_51, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.94/1.76  tff(f_87, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_funct_2)).
% 2.94/1.76  tff(f_59, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 2.94/1.76  tff(f_95, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r1_tarski(k7_relset_1(A, B, D, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_funct_2)).
% 2.94/1.76  tff(f_47, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_funct_1)).
% 2.94/1.76  tff(f_55, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.94/1.76  tff(f_77, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 2.94/1.76  tff(c_48, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.94/1.76  tff(c_71, plain, (![C_52, A_53, B_54]: (v1_relat_1(C_52) | ~m1_subset_1(C_52, k1_zfmisc_1(k2_zfmisc_1(A_53, B_54))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.94/1.76  tff(c_75, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_48, c_71])).
% 2.94/1.76  tff(c_52, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.94/1.76  tff(c_38, plain, (![A_44]: (v1_funct_2(A_44, k1_relat_1(A_44), k2_relat_1(A_44)) | ~v1_funct_1(A_44) | ~v1_relat_1(A_44))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.94/1.76  tff(c_36, plain, (![A_44]: (m1_subset_1(A_44, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_44), k2_relat_1(A_44)))) | ~v1_funct_1(A_44) | ~v1_relat_1(A_44))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.94/1.76  tff(c_133, plain, (![A_76, B_77, C_78, D_79]: (k7_relset_1(A_76, B_77, C_78, D_79)=k9_relat_1(C_78, D_79) | ~m1_subset_1(C_78, k1_zfmisc_1(k2_zfmisc_1(A_76, B_77))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.94/1.76  tff(c_138, plain, (![A_44, D_79]: (k7_relset_1(k1_relat_1(A_44), k2_relat_1(A_44), A_44, D_79)=k9_relat_1(A_44, D_79) | ~v1_funct_1(A_44) | ~v1_relat_1(A_44))), inference(resolution, [status(thm)], [c_36, c_133])).
% 2.94/1.76  tff(c_288, plain, (![A_124, B_125, D_126, C_127]: (r1_tarski(k7_relset_1(A_124, B_125, D_126, C_127), B_125) | ~m1_subset_1(D_126, k1_zfmisc_1(k2_zfmisc_1(A_124, B_125))) | ~v1_funct_2(D_126, A_124, B_125) | ~v1_funct_1(D_126))), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.94/1.76  tff(c_297, plain, (![A_128, C_129]: (r1_tarski(k7_relset_1(k1_relat_1(A_128), k2_relat_1(A_128), A_128, C_129), k2_relat_1(A_128)) | ~v1_funct_2(A_128, k1_relat_1(A_128), k2_relat_1(A_128)) | ~v1_funct_1(A_128) | ~v1_relat_1(A_128))), inference(resolution, [status(thm)], [c_36, c_288])).
% 2.94/1.76  tff(c_302, plain, (![A_131, D_132]: (r1_tarski(k9_relat_1(A_131, D_132), k2_relat_1(A_131)) | ~v1_funct_2(A_131, k1_relat_1(A_131), k2_relat_1(A_131)) | ~v1_funct_1(A_131) | ~v1_relat_1(A_131) | ~v1_funct_1(A_131) | ~v1_relat_1(A_131))), inference(superposition, [status(thm), theory('equality')], [c_138, c_297])).
% 2.94/1.76  tff(c_306, plain, (![A_133, D_134]: (r1_tarski(k9_relat_1(A_133, D_134), k2_relat_1(A_133)) | ~v1_funct_1(A_133) | ~v1_relat_1(A_133))), inference(resolution, [status(thm)], [c_38, c_302])).
% 2.94/1.76  tff(c_150, plain, (![B_81, A_82]: (k1_tarski(k1_funct_1(B_81, A_82))=k2_relat_1(B_81) | k1_tarski(A_82)!=k1_relat_1(B_81) | ~v1_funct_1(B_81) | ~v1_relat_1(B_81))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.94/1.76  tff(c_139, plain, (![D_79]: (k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', D_79)=k9_relat_1('#skF_4', D_79))), inference(resolution, [status(thm)], [c_48, c_133])).
% 2.94/1.76  tff(c_44, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.94/1.76  tff(c_140, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_139, c_44])).
% 2.94/1.76  tff(c_156, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_150, c_140])).
% 2.94/1.76  tff(c_162, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_75, c_52, c_156])).
% 2.94/1.76  tff(c_164, plain, (k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(splitLeft, [status(thm)], [c_162])).
% 2.94/1.76  tff(c_46, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.94/1.76  tff(c_50, plain, (v1_funct_2('#skF_4', k1_tarski('#skF_1'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.94/1.76  tff(c_95, plain, (![A_63, B_64, C_65]: (k1_relset_1(A_63, B_64, C_65)=k1_relat_1(C_65) | ~m1_subset_1(C_65, k1_zfmisc_1(k2_zfmisc_1(A_63, B_64))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.94/1.76  tff(c_99, plain, (k1_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_48, c_95])).
% 2.94/1.76  tff(c_185, plain, (![B_95, A_96, C_97]: (k1_xboole_0=B_95 | k1_relset_1(A_96, B_95, C_97)=A_96 | ~v1_funct_2(C_97, A_96, B_95) | ~m1_subset_1(C_97, k1_zfmisc_1(k2_zfmisc_1(A_96, B_95))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.94/1.76  tff(c_191, plain, (k1_xboole_0='#skF_2' | k1_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4')=k1_tarski('#skF_1') | ~v1_funct_2('#skF_4', k1_tarski('#skF_1'), '#skF_2')), inference(resolution, [status(thm)], [c_48, c_185])).
% 2.94/1.76  tff(c_195, plain, (k1_xboole_0='#skF_2' | k1_tarski('#skF_1')=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_99, c_191])).
% 2.94/1.76  tff(c_197, plain, $false, inference(negUnitSimplification, [status(thm)], [c_164, c_46, c_195])).
% 2.94/1.76  tff(c_198, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4'))), inference(splitRight, [status(thm)], [c_162])).
% 2.94/1.76  tff(c_309, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_306, c_198])).
% 2.94/1.76  tff(c_313, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_75, c_52, c_309])).
% 2.94/1.76  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.94/1.76  
% 2.94/1.76  Inference rules
% 2.94/1.76  ----------------------
% 2.94/1.76  #Ref     : 0
% 2.94/1.76  #Sup     : 55
% 2.94/1.76  #Fact    : 0
% 2.94/1.76  #Define  : 0
% 2.94/1.76  #Split   : 1
% 2.94/1.76  #Chain   : 0
% 2.94/1.76  #Close   : 0
% 2.94/1.76  
% 2.94/1.76  Ordering : KBO
% 2.94/1.76  
% 2.94/1.76  Simplification rules
% 2.94/1.76  ----------------------
% 2.94/1.76  #Subsume      : 4
% 2.94/1.76  #Demod        : 21
% 2.94/1.76  #Tautology    : 41
% 2.94/1.76  #SimpNegUnit  : 3
% 2.94/1.76  #BackRed      : 5
% 2.94/1.76  
% 2.94/1.76  #Partial instantiations: 0
% 2.94/1.76  #Strategies tried      : 1
% 2.94/1.76  
% 2.94/1.76  Timing (in seconds)
% 2.94/1.76  ----------------------
% 2.94/1.77  Preprocessing        : 0.56
% 2.94/1.77  Parsing              : 0.29
% 2.94/1.77  CNF conversion       : 0.03
% 2.94/1.77  Main loop            : 0.37
% 2.94/1.77  Inferencing          : 0.15
% 2.94/1.77  Reduction            : 0.11
% 2.94/1.77  Demodulation         : 0.08
% 2.94/1.77  BG Simplification    : 0.03
% 2.94/1.77  Subsumption          : 0.05
% 2.94/1.77  Abstraction          : 0.02
% 2.94/1.77  MUC search           : 0.00
% 2.94/1.77  Cooper               : 0.00
% 2.94/1.77  Total                : 0.97
% 2.94/1.77  Index Insertion      : 0.00
% 2.94/1.77  Index Deletion       : 0.00
% 2.94/1.77  Index Matching       : 0.00
% 2.94/1.77  BG Taut test         : 0.00
%------------------------------------------------------------------------------
