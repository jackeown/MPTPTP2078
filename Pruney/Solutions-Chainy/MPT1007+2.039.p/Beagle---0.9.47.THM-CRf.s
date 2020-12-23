%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:16 EST 2020

% Result     : Theorem 2.74s
% Output     : CNFRefutation 3.05s
% Verified   : 
% Statistics : Number of formulae       :   71 (  88 expanded)
%              Number of leaves         :   40 (  51 expanded)
%              Depth                    :    8
%              Number of atoms          :   94 ( 149 expanded)
%              Number of equality atoms :   20 (  28 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_110,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_tarski(A),B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r2_hidden(k1_funct_1(C,A),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_2)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_80,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_98,axiom,(
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

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_34,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => r2_hidden(k1_funct_1(B,A),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_funct_1)).

tff(c_58,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_2'),'#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_81,plain,(
    ! [C_56,A_57,B_58] :
      ( v1_relat_1(C_56)
      | ~ m1_subset_1(C_56,k1_zfmisc_1(k2_zfmisc_1(A_57,B_58))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_85,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_81])).

tff(c_150,plain,(
    ! [C_86,B_87,A_88] :
      ( v5_relat_1(C_86,B_87)
      | ~ m1_subset_1(C_86,k1_zfmisc_1(k2_zfmisc_1(A_88,B_87))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_154,plain,(
    v5_relat_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_150])).

tff(c_30,plain,(
    ! [B_38,A_37] :
      ( r1_tarski(k2_relat_1(B_38),A_37)
      | ~ v5_relat_1(B_38,A_37)
      | ~ v1_relat_1(B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_62,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_56,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_60,plain,(
    v1_funct_2('#skF_4',k1_tarski('#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_209,plain,(
    ! [A_107,B_108,C_109] :
      ( k1_relset_1(A_107,B_108,C_109) = k1_relat_1(C_109)
      | ~ m1_subset_1(C_109,k1_zfmisc_1(k2_zfmisc_1(A_107,B_108))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_213,plain,(
    k1_relset_1(k1_tarski('#skF_2'),'#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_209])).

tff(c_316,plain,(
    ! [B_153,A_154,C_155] :
      ( k1_xboole_0 = B_153
      | k1_relset_1(A_154,B_153,C_155) = A_154
      | ~ v1_funct_2(C_155,A_154,B_153)
      | ~ m1_subset_1(C_155,k1_zfmisc_1(k2_zfmisc_1(A_154,B_153))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_319,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1(k1_tarski('#skF_2'),'#skF_3','#skF_4') = k1_tarski('#skF_2')
    | ~ v1_funct_2('#skF_4',k1_tarski('#skF_2'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_316])).

tff(c_322,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_tarski('#skF_2') = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_213,c_319])).

tff(c_323,plain,(
    k1_tarski('#skF_2') = k1_relat_1('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_322])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_92,plain,(
    ! [A_66,B_67] :
      ( ~ r2_hidden('#skF_1'(A_66,B_67),B_67)
      | r1_tarski(A_66,B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_98,plain,(
    ! [A_68] : r1_tarski(A_68,A_68) ),
    inference(resolution,[status(thm)],[c_6,c_92])).

tff(c_8,plain,(
    ! [A_6] : k2_tarski(A_6,A_6) = k1_tarski(A_6) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_86,plain,(
    ! [A_59,C_60,B_61] :
      ( r2_hidden(A_59,C_60)
      | ~ r1_tarski(k2_tarski(A_59,B_61),C_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_89,plain,(
    ! [A_6,C_60] :
      ( r2_hidden(A_6,C_60)
      | ~ r1_tarski(k1_tarski(A_6),C_60) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_86])).

tff(c_107,plain,(
    ! [A_6] : r2_hidden(A_6,k1_tarski(A_6)) ),
    inference(resolution,[status(thm)],[c_98,c_89])).

tff(c_339,plain,(
    r2_hidden('#skF_2',k1_relat_1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_323,c_107])).

tff(c_228,plain,(
    ! [B_117,A_118] :
      ( r2_hidden(k1_funct_1(B_117,A_118),k2_relat_1(B_117))
      | ~ r2_hidden(A_118,k1_relat_1(B_117))
      | ~ v1_funct_1(B_117)
      | ~ v1_relat_1(B_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_504,plain,(
    ! [B_174,A_175,B_176] :
      ( r2_hidden(k1_funct_1(B_174,A_175),B_176)
      | ~ r1_tarski(k2_relat_1(B_174),B_176)
      | ~ r2_hidden(A_175,k1_relat_1(B_174))
      | ~ v1_funct_1(B_174)
      | ~ v1_relat_1(B_174) ) ),
    inference(resolution,[status(thm)],[c_228,c_2])).

tff(c_54,plain,(
    ~ r2_hidden(k1_funct_1('#skF_4','#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_512,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_3')
    | ~ r2_hidden('#skF_2',k1_relat_1('#skF_4'))
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_504,c_54])).

tff(c_517,plain,(
    ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_62,c_339,c_512])).

tff(c_520,plain,
    ( ~ v5_relat_1('#skF_4','#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_517])).

tff(c_524,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_154,c_520])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:21:59 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.74/1.43  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.74/1.44  
% 2.74/1.44  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.74/1.44  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.74/1.44  
% 2.74/1.44  %Foreground sorts:
% 2.74/1.44  
% 2.74/1.44  
% 2.74/1.44  %Background operators:
% 2.74/1.44  
% 2.74/1.44  
% 2.74/1.44  %Foreground operators:
% 2.74/1.44  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.74/1.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.74/1.44  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.74/1.44  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.74/1.44  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.74/1.44  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.74/1.44  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.74/1.44  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.74/1.44  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.74/1.44  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.74/1.44  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.74/1.44  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.74/1.44  tff('#skF_2', type, '#skF_2': $i).
% 2.74/1.44  tff('#skF_3', type, '#skF_3': $i).
% 2.74/1.44  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.74/1.44  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.74/1.44  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.74/1.44  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.74/1.44  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.74/1.44  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.74/1.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.74/1.44  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.74/1.44  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.74/1.44  tff('#skF_4', type, '#skF_4': $i).
% 2.74/1.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.74/1.44  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.74/1.44  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.74/1.44  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.74/1.44  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.74/1.44  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.74/1.44  
% 3.05/1.46  tff(f_110, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_tarski(A), B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r2_hidden(k1_funct_1(C, A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_2)).
% 3.05/1.46  tff(f_70, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.05/1.46  tff(f_76, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.05/1.46  tff(f_58, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 3.05/1.46  tff(f_80, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.05/1.46  tff(f_98, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 3.05/1.46  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.05/1.46  tff(f_34, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 3.05/1.46  tff(f_52, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 3.05/1.46  tff(f_66, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, A), k2_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_funct_1)).
% 3.05/1.46  tff(c_58, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_2'), '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.05/1.46  tff(c_81, plain, (![C_56, A_57, B_58]: (v1_relat_1(C_56) | ~m1_subset_1(C_56, k1_zfmisc_1(k2_zfmisc_1(A_57, B_58))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.05/1.46  tff(c_85, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_58, c_81])).
% 3.05/1.46  tff(c_150, plain, (![C_86, B_87, A_88]: (v5_relat_1(C_86, B_87) | ~m1_subset_1(C_86, k1_zfmisc_1(k2_zfmisc_1(A_88, B_87))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.05/1.46  tff(c_154, plain, (v5_relat_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_58, c_150])).
% 3.05/1.46  tff(c_30, plain, (![B_38, A_37]: (r1_tarski(k2_relat_1(B_38), A_37) | ~v5_relat_1(B_38, A_37) | ~v1_relat_1(B_38))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.05/1.46  tff(c_62, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.05/1.46  tff(c_56, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.05/1.46  tff(c_60, plain, (v1_funct_2('#skF_4', k1_tarski('#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.05/1.46  tff(c_209, plain, (![A_107, B_108, C_109]: (k1_relset_1(A_107, B_108, C_109)=k1_relat_1(C_109) | ~m1_subset_1(C_109, k1_zfmisc_1(k2_zfmisc_1(A_107, B_108))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.05/1.46  tff(c_213, plain, (k1_relset_1(k1_tarski('#skF_2'), '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_58, c_209])).
% 3.05/1.46  tff(c_316, plain, (![B_153, A_154, C_155]: (k1_xboole_0=B_153 | k1_relset_1(A_154, B_153, C_155)=A_154 | ~v1_funct_2(C_155, A_154, B_153) | ~m1_subset_1(C_155, k1_zfmisc_1(k2_zfmisc_1(A_154, B_153))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.05/1.46  tff(c_319, plain, (k1_xboole_0='#skF_3' | k1_relset_1(k1_tarski('#skF_2'), '#skF_3', '#skF_4')=k1_tarski('#skF_2') | ~v1_funct_2('#skF_4', k1_tarski('#skF_2'), '#skF_3')), inference(resolution, [status(thm)], [c_58, c_316])).
% 3.05/1.46  tff(c_322, plain, (k1_xboole_0='#skF_3' | k1_tarski('#skF_2')=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_213, c_319])).
% 3.05/1.46  tff(c_323, plain, (k1_tarski('#skF_2')=k1_relat_1('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_56, c_322])).
% 3.05/1.46  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.05/1.46  tff(c_92, plain, (![A_66, B_67]: (~r2_hidden('#skF_1'(A_66, B_67), B_67) | r1_tarski(A_66, B_67))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.05/1.46  tff(c_98, plain, (![A_68]: (r1_tarski(A_68, A_68))), inference(resolution, [status(thm)], [c_6, c_92])).
% 3.05/1.46  tff(c_8, plain, (![A_6]: (k2_tarski(A_6, A_6)=k1_tarski(A_6))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.05/1.46  tff(c_86, plain, (![A_59, C_60, B_61]: (r2_hidden(A_59, C_60) | ~r1_tarski(k2_tarski(A_59, B_61), C_60))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.05/1.46  tff(c_89, plain, (![A_6, C_60]: (r2_hidden(A_6, C_60) | ~r1_tarski(k1_tarski(A_6), C_60))), inference(superposition, [status(thm), theory('equality')], [c_8, c_86])).
% 3.05/1.46  tff(c_107, plain, (![A_6]: (r2_hidden(A_6, k1_tarski(A_6)))), inference(resolution, [status(thm)], [c_98, c_89])).
% 3.05/1.46  tff(c_339, plain, (r2_hidden('#skF_2', k1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_323, c_107])).
% 3.05/1.46  tff(c_228, plain, (![B_117, A_118]: (r2_hidden(k1_funct_1(B_117, A_118), k2_relat_1(B_117)) | ~r2_hidden(A_118, k1_relat_1(B_117)) | ~v1_funct_1(B_117) | ~v1_relat_1(B_117))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.05/1.46  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.05/1.46  tff(c_504, plain, (![B_174, A_175, B_176]: (r2_hidden(k1_funct_1(B_174, A_175), B_176) | ~r1_tarski(k2_relat_1(B_174), B_176) | ~r2_hidden(A_175, k1_relat_1(B_174)) | ~v1_funct_1(B_174) | ~v1_relat_1(B_174))), inference(resolution, [status(thm)], [c_228, c_2])).
% 3.05/1.46  tff(c_54, plain, (~r2_hidden(k1_funct_1('#skF_4', '#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.05/1.46  tff(c_512, plain, (~r1_tarski(k2_relat_1('#skF_4'), '#skF_3') | ~r2_hidden('#skF_2', k1_relat_1('#skF_4')) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_504, c_54])).
% 3.05/1.46  tff(c_517, plain, (~r1_tarski(k2_relat_1('#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_85, c_62, c_339, c_512])).
% 3.05/1.46  tff(c_520, plain, (~v5_relat_1('#skF_4', '#skF_3') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_30, c_517])).
% 3.05/1.46  tff(c_524, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_85, c_154, c_520])).
% 3.05/1.46  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.05/1.46  
% 3.05/1.46  Inference rules
% 3.05/1.46  ----------------------
% 3.05/1.46  #Ref     : 0
% 3.05/1.46  #Sup     : 104
% 3.05/1.46  #Fact    : 0
% 3.05/1.46  #Define  : 0
% 3.05/1.46  #Split   : 0
% 3.05/1.46  #Chain   : 0
% 3.05/1.46  #Close   : 0
% 3.05/1.46  
% 3.05/1.46  Ordering : KBO
% 3.05/1.46  
% 3.05/1.46  Simplification rules
% 3.05/1.46  ----------------------
% 3.05/1.46  #Subsume      : 15
% 3.05/1.46  #Demod        : 28
% 3.05/1.46  #Tautology    : 36
% 3.05/1.46  #SimpNegUnit  : 3
% 3.05/1.46  #BackRed      : 4
% 3.05/1.46  
% 3.05/1.46  #Partial instantiations: 0
% 3.05/1.46  #Strategies tried      : 1
% 3.05/1.46  
% 3.05/1.46  Timing (in seconds)
% 3.05/1.46  ----------------------
% 3.05/1.46  Preprocessing        : 0.34
% 3.05/1.46  Parsing              : 0.18
% 3.05/1.46  CNF conversion       : 0.02
% 3.05/1.46  Main loop            : 0.30
% 3.05/1.46  Inferencing          : 0.11
% 3.05/1.46  Reduction            : 0.09
% 3.05/1.46  Demodulation         : 0.06
% 3.05/1.46  BG Simplification    : 0.02
% 3.11/1.46  Subsumption          : 0.06
% 3.11/1.46  Abstraction          : 0.01
% 3.11/1.46  MUC search           : 0.00
% 3.11/1.46  Cooper               : 0.00
% 3.11/1.46  Total                : 0.67
% 3.11/1.46  Index Insertion      : 0.00
% 3.11/1.46  Index Deletion       : 0.00
% 3.11/1.46  Index Matching       : 0.00
% 3.11/1.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
