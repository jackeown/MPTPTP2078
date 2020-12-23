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
% DateTime   : Thu Dec  3 10:14:19 EST 2020

% Result     : Theorem 3.32s
% Output     : CNFRefutation 3.32s
% Verified   : 
% Statistics : Number of formulae       :   73 (  85 expanded)
%              Number of leaves         :   38 (  46 expanded)
%              Depth                    :    8
%              Number of atoms          :   98 ( 142 expanded)
%              Number of equality atoms :   25 (  33 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_subset_1 > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_106,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_tarski(A),B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r2_hidden(k1_funct_1(C,A),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_2)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

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

tff(f_27,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_39,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_41,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => r2_hidden(k1_funct_1(B,A),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_funct_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(c_48,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_52,plain,(
    v1_funct_2('#skF_3',k1_tarski('#skF_1'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_50,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_307,plain,(
    ! [A_98,B_99,C_100] :
      ( k1_relset_1(A_98,B_99,C_100) = k1_relat_1(C_100)
      | ~ m1_subset_1(C_100,k1_zfmisc_1(k2_zfmisc_1(A_98,B_99))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_320,plain,(
    k1_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_307])).

tff(c_746,plain,(
    ! [B_165,A_166,C_167] :
      ( k1_xboole_0 = B_165
      | k1_relset_1(A_166,B_165,C_167) = A_166
      | ~ v1_funct_2(C_167,A_166,B_165)
      | ~ m1_subset_1(C_167,k1_zfmisc_1(k2_zfmisc_1(A_166,B_165))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_761,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_3') = k1_tarski('#skF_1')
    | ~ v1_funct_2('#skF_3',k1_tarski('#skF_1'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_746])).

tff(c_771,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_tarski('#skF_1') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_320,c_761])).

tff(c_772,plain,(
    k1_tarski('#skF_1') = k1_relat_1('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_771])).

tff(c_2,plain,(
    ! [A_1] : k2_tarski(A_1,A_1) = k1_tarski(A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_14,plain,(
    ! [A_10] : k2_subset_1(A_10) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_16,plain,(
    ! [A_11] : m1_subset_1(k2_subset_1(A_11),k1_zfmisc_1(A_11)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_55,plain,(
    ! [A_11] : m1_subset_1(A_11,k1_zfmisc_1(A_11)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_16])).

tff(c_84,plain,(
    ! [A_40,B_41] :
      ( r1_tarski(A_40,B_41)
      | ~ m1_subset_1(A_40,k1_zfmisc_1(B_41)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_88,plain,(
    ! [A_11] : r1_tarski(A_11,A_11) ),
    inference(resolution,[status(thm)],[c_55,c_84])).

tff(c_99,plain,(
    ! [A_45,C_46,B_47] :
      ( r2_hidden(A_45,C_46)
      | ~ r1_tarski(k2_tarski(A_45,B_47),C_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_108,plain,(
    ! [A_48,B_49] : r2_hidden(A_48,k2_tarski(A_48,B_49)) ),
    inference(resolution,[status(thm)],[c_88,c_99])).

tff(c_111,plain,(
    ! [A_1] : r2_hidden(A_1,k1_tarski(A_1)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_108])).

tff(c_792,plain,(
    r2_hidden('#skF_1',k1_relat_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_772,c_111])).

tff(c_134,plain,(
    ! [C_58,A_59,B_60] :
      ( v1_relat_1(C_58)
      | ~ m1_subset_1(C_58,k1_zfmisc_1(k2_zfmisc_1(A_59,B_60))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_147,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_134])).

tff(c_54,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_251,plain,(
    ! [A_88,B_89,C_90] :
      ( k2_relset_1(A_88,B_89,C_90) = k2_relat_1(C_90)
      | ~ m1_subset_1(C_90,k1_zfmisc_1(k2_zfmisc_1(A_88,B_89))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_264,plain,(
    k2_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_251])).

tff(c_357,plain,(
    ! [A_106,B_107,C_108] :
      ( m1_subset_1(k2_relset_1(A_106,B_107,C_108),k1_zfmisc_1(B_107))
      | ~ m1_subset_1(C_108,k1_zfmisc_1(k2_zfmisc_1(A_106,B_107))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_378,plain,
    ( m1_subset_1(k2_relat_1('#skF_3'),k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_264,c_357])).

tff(c_386,plain,(
    m1_subset_1(k2_relat_1('#skF_3'),k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_378])).

tff(c_391,plain,(
    ! [B_109,A_110] :
      ( r2_hidden(k1_funct_1(B_109,A_110),k2_relat_1(B_109))
      | ~ r2_hidden(A_110,k1_relat_1(B_109))
      | ~ v1_funct_1(B_109)
      | ~ v1_relat_1(B_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_18,plain,(
    ! [C_15,A_12,B_13] :
      ( r2_hidden(C_15,A_12)
      | ~ r2_hidden(C_15,B_13)
      | ~ m1_subset_1(B_13,k1_zfmisc_1(A_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_1205,plain,(
    ! [B_208,A_209,A_210] :
      ( r2_hidden(k1_funct_1(B_208,A_209),A_210)
      | ~ m1_subset_1(k2_relat_1(B_208),k1_zfmisc_1(A_210))
      | ~ r2_hidden(A_209,k1_relat_1(B_208))
      | ~ v1_funct_1(B_208)
      | ~ v1_relat_1(B_208) ) ),
    inference(resolution,[status(thm)],[c_391,c_18])).

tff(c_1211,plain,(
    ! [A_209] :
      ( r2_hidden(k1_funct_1('#skF_3',A_209),'#skF_2')
      | ~ r2_hidden(A_209,k1_relat_1('#skF_3'))
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_386,c_1205])).

tff(c_1229,plain,(
    ! [A_211] :
      ( r2_hidden(k1_funct_1('#skF_3',A_211),'#skF_2')
      | ~ r2_hidden(A_211,k1_relat_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_147,c_54,c_1211])).

tff(c_46,plain,(
    ~ r2_hidden(k1_funct_1('#skF_3','#skF_1'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_1234,plain,(
    ~ r2_hidden('#skF_1',k1_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_1229,c_46])).

tff(c_1239,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_792,c_1234])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:35:49 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.32/1.50  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.32/1.50  
% 3.32/1.50  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.32/1.51  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_subset_1 > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.32/1.51  
% 3.32/1.51  %Foreground sorts:
% 3.32/1.51  
% 3.32/1.51  
% 3.32/1.51  %Background operators:
% 3.32/1.51  
% 3.32/1.51  
% 3.32/1.51  %Foreground operators:
% 3.32/1.51  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.32/1.51  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.32/1.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.32/1.51  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.32/1.51  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.32/1.51  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.32/1.51  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.32/1.51  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.32/1.51  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.32/1.51  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.32/1.51  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.32/1.51  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.32/1.51  tff('#skF_2', type, '#skF_2': $i).
% 3.32/1.51  tff('#skF_3', type, '#skF_3': $i).
% 3.32/1.51  tff('#skF_1', type, '#skF_1': $i).
% 3.32/1.51  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.32/1.51  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.32/1.51  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.32/1.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.32/1.51  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.32/1.51  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.32/1.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.32/1.51  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 3.32/1.51  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.32/1.51  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.32/1.51  
% 3.32/1.52  tff(f_106, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_tarski(A), B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r2_hidden(k1_funct_1(C, A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_2)).
% 3.32/1.52  tff(f_72, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.32/1.52  tff(f_94, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 3.32/1.52  tff(f_27, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 3.32/1.52  tff(f_39, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 3.32/1.52  tff(f_41, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 3.32/1.52  tff(f_52, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.32/1.52  tff(f_37, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 3.32/1.52  tff(f_64, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.32/1.52  tff(f_76, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.32/1.52  tff(f_68, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 3.32/1.52  tff(f_60, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, A), k2_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_funct_1)).
% 3.32/1.52  tff(f_48, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 3.32/1.52  tff(c_48, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.32/1.52  tff(c_52, plain, (v1_funct_2('#skF_3', k1_tarski('#skF_1'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.32/1.52  tff(c_50, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.32/1.52  tff(c_307, plain, (![A_98, B_99, C_100]: (k1_relset_1(A_98, B_99, C_100)=k1_relat_1(C_100) | ~m1_subset_1(C_100, k1_zfmisc_1(k2_zfmisc_1(A_98, B_99))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.32/1.52  tff(c_320, plain, (k1_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_50, c_307])).
% 3.32/1.52  tff(c_746, plain, (![B_165, A_166, C_167]: (k1_xboole_0=B_165 | k1_relset_1(A_166, B_165, C_167)=A_166 | ~v1_funct_2(C_167, A_166, B_165) | ~m1_subset_1(C_167, k1_zfmisc_1(k2_zfmisc_1(A_166, B_165))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.32/1.52  tff(c_761, plain, (k1_xboole_0='#skF_2' | k1_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_3')=k1_tarski('#skF_1') | ~v1_funct_2('#skF_3', k1_tarski('#skF_1'), '#skF_2')), inference(resolution, [status(thm)], [c_50, c_746])).
% 3.32/1.52  tff(c_771, plain, (k1_xboole_0='#skF_2' | k1_tarski('#skF_1')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_320, c_761])).
% 3.32/1.52  tff(c_772, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_48, c_771])).
% 3.32/1.52  tff(c_2, plain, (![A_1]: (k2_tarski(A_1, A_1)=k1_tarski(A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.32/1.52  tff(c_14, plain, (![A_10]: (k2_subset_1(A_10)=A_10)), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.32/1.52  tff(c_16, plain, (![A_11]: (m1_subset_1(k2_subset_1(A_11), k1_zfmisc_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.32/1.52  tff(c_55, plain, (![A_11]: (m1_subset_1(A_11, k1_zfmisc_1(A_11)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_16])).
% 3.32/1.52  tff(c_84, plain, (![A_40, B_41]: (r1_tarski(A_40, B_41) | ~m1_subset_1(A_40, k1_zfmisc_1(B_41)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.32/1.52  tff(c_88, plain, (![A_11]: (r1_tarski(A_11, A_11))), inference(resolution, [status(thm)], [c_55, c_84])).
% 3.32/1.52  tff(c_99, plain, (![A_45, C_46, B_47]: (r2_hidden(A_45, C_46) | ~r1_tarski(k2_tarski(A_45, B_47), C_46))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.32/1.52  tff(c_108, plain, (![A_48, B_49]: (r2_hidden(A_48, k2_tarski(A_48, B_49)))), inference(resolution, [status(thm)], [c_88, c_99])).
% 3.32/1.52  tff(c_111, plain, (![A_1]: (r2_hidden(A_1, k1_tarski(A_1)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_108])).
% 3.32/1.52  tff(c_792, plain, (r2_hidden('#skF_1', k1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_772, c_111])).
% 3.32/1.52  tff(c_134, plain, (![C_58, A_59, B_60]: (v1_relat_1(C_58) | ~m1_subset_1(C_58, k1_zfmisc_1(k2_zfmisc_1(A_59, B_60))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.32/1.52  tff(c_147, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_50, c_134])).
% 3.32/1.52  tff(c_54, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.32/1.52  tff(c_251, plain, (![A_88, B_89, C_90]: (k2_relset_1(A_88, B_89, C_90)=k2_relat_1(C_90) | ~m1_subset_1(C_90, k1_zfmisc_1(k2_zfmisc_1(A_88, B_89))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.32/1.52  tff(c_264, plain, (k2_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_50, c_251])).
% 3.32/1.52  tff(c_357, plain, (![A_106, B_107, C_108]: (m1_subset_1(k2_relset_1(A_106, B_107, C_108), k1_zfmisc_1(B_107)) | ~m1_subset_1(C_108, k1_zfmisc_1(k2_zfmisc_1(A_106, B_107))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.32/1.52  tff(c_378, plain, (m1_subset_1(k2_relat_1('#skF_3'), k1_zfmisc_1('#skF_2')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_264, c_357])).
% 3.32/1.52  tff(c_386, plain, (m1_subset_1(k2_relat_1('#skF_3'), k1_zfmisc_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_378])).
% 3.32/1.52  tff(c_391, plain, (![B_109, A_110]: (r2_hidden(k1_funct_1(B_109, A_110), k2_relat_1(B_109)) | ~r2_hidden(A_110, k1_relat_1(B_109)) | ~v1_funct_1(B_109) | ~v1_relat_1(B_109))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.32/1.52  tff(c_18, plain, (![C_15, A_12, B_13]: (r2_hidden(C_15, A_12) | ~r2_hidden(C_15, B_13) | ~m1_subset_1(B_13, k1_zfmisc_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.32/1.52  tff(c_1205, plain, (![B_208, A_209, A_210]: (r2_hidden(k1_funct_1(B_208, A_209), A_210) | ~m1_subset_1(k2_relat_1(B_208), k1_zfmisc_1(A_210)) | ~r2_hidden(A_209, k1_relat_1(B_208)) | ~v1_funct_1(B_208) | ~v1_relat_1(B_208))), inference(resolution, [status(thm)], [c_391, c_18])).
% 3.32/1.52  tff(c_1211, plain, (![A_209]: (r2_hidden(k1_funct_1('#skF_3', A_209), '#skF_2') | ~r2_hidden(A_209, k1_relat_1('#skF_3')) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_386, c_1205])).
% 3.32/1.52  tff(c_1229, plain, (![A_211]: (r2_hidden(k1_funct_1('#skF_3', A_211), '#skF_2') | ~r2_hidden(A_211, k1_relat_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_147, c_54, c_1211])).
% 3.32/1.52  tff(c_46, plain, (~r2_hidden(k1_funct_1('#skF_3', '#skF_1'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.32/1.52  tff(c_1234, plain, (~r2_hidden('#skF_1', k1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_1229, c_46])).
% 3.32/1.52  tff(c_1239, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_792, c_1234])).
% 3.32/1.52  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.32/1.52  
% 3.32/1.52  Inference rules
% 3.32/1.52  ----------------------
% 3.32/1.52  #Ref     : 0
% 3.32/1.52  #Sup     : 234
% 3.32/1.52  #Fact    : 0
% 3.32/1.52  #Define  : 0
% 3.32/1.52  #Split   : 1
% 3.32/1.52  #Chain   : 0
% 3.32/1.52  #Close   : 0
% 3.32/1.52  
% 3.32/1.52  Ordering : KBO
% 3.32/1.52  
% 3.32/1.52  Simplification rules
% 3.32/1.52  ----------------------
% 3.32/1.52  #Subsume      : 27
% 3.32/1.52  #Demod        : 83
% 3.32/1.52  #Tautology    : 77
% 3.32/1.52  #SimpNegUnit  : 6
% 3.32/1.52  #BackRed      : 7
% 3.32/1.52  
% 3.32/1.52  #Partial instantiations: 0
% 3.32/1.52  #Strategies tried      : 1
% 3.32/1.52  
% 3.32/1.52  Timing (in seconds)
% 3.32/1.52  ----------------------
% 3.48/1.52  Preprocessing        : 0.33
% 3.48/1.52  Parsing              : 0.17
% 3.48/1.52  CNF conversion       : 0.02
% 3.48/1.52  Main loop            : 0.43
% 3.48/1.52  Inferencing          : 0.17
% 3.48/1.52  Reduction            : 0.13
% 3.48/1.52  Demodulation         : 0.10
% 3.48/1.52  BG Simplification    : 0.02
% 3.48/1.52  Subsumption          : 0.08
% 3.48/1.52  Abstraction          : 0.02
% 3.48/1.52  MUC search           : 0.00
% 3.48/1.52  Cooper               : 0.00
% 3.48/1.52  Total                : 0.79
% 3.48/1.52  Index Insertion      : 0.00
% 3.48/1.52  Index Deletion       : 0.00
% 3.48/1.52  Index Matching       : 0.00
% 3.48/1.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
