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
% DateTime   : Thu Dec  3 10:14:35 EST 2020

% Result     : Theorem 2.29s
% Output     : CNFRefutation 2.29s
% Verified   : 
% Statistics : Number of formulae       :   65 (  82 expanded)
%              Number of leaves         :   37 (  47 expanded)
%              Depth                    :    8
%              Number of atoms          :   81 ( 136 expanded)
%              Number of equality atoms :   34 (  52 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k7_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_100,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_tarski(A),B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => k2_relset_1(k1_tarski(A),B,C) = k1_tarski(k1_funct_1(C,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_funct_2)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_88,axiom,(
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
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => k2_relat_1(k7_relat_1(B,k1_tarski(A))) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t168_funct_1)).

tff(c_48,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_52,plain,(
    v1_funct_2('#skF_5',k1_tarski('#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_50,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_3'),'#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_128,plain,(
    ! [A_59,B_60,C_61] :
      ( k1_relset_1(A_59,B_60,C_61) = k1_relat_1(C_61)
      | ~ m1_subset_1(C_61,k1_zfmisc_1(k2_zfmisc_1(A_59,B_60))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_132,plain,(
    k1_relset_1(k1_tarski('#skF_3'),'#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_128])).

tff(c_198,plain,(
    ! [B_81,A_82,C_83] :
      ( k1_xboole_0 = B_81
      | k1_relset_1(A_82,B_81,C_83) = A_82
      | ~ v1_funct_2(C_83,A_82,B_81)
      | ~ m1_subset_1(C_83,k1_zfmisc_1(k2_zfmisc_1(A_82,B_81))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_201,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1(k1_tarski('#skF_3'),'#skF_4','#skF_5') = k1_tarski('#skF_3')
    | ~ v1_funct_2('#skF_5',k1_tarski('#skF_3'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_198])).

tff(c_204,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_tarski('#skF_3') = k1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_132,c_201])).

tff(c_205,plain,(
    k1_tarski('#skF_3') = k1_relat_1('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_204])).

tff(c_4,plain,(
    ! [C_5] : r2_hidden(C_5,k1_tarski(C_5)) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_230,plain,(
    r2_hidden('#skF_3',k1_relat_1('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_205,c_4])).

tff(c_116,plain,(
    ! [A_53,B_54,C_55] :
      ( k2_relset_1(A_53,B_54,C_55) = k2_relat_1(C_55)
      | ~ m1_subset_1(C_55,k1_zfmisc_1(k2_zfmisc_1(A_53,B_54))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_120,plain,(
    k2_relset_1(k1_tarski('#skF_3'),'#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_116])).

tff(c_46,plain,(
    k2_relset_1(k1_tarski('#skF_3'),'#skF_4','#skF_5') != k1_tarski(k1_funct_1('#skF_5','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_121,plain,(
    k1_tarski(k1_funct_1('#skF_5','#skF_3')) != k2_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_46])).

tff(c_80,plain,(
    ! [C_37,A_38,B_39] :
      ( v1_relat_1(C_37)
      | ~ m1_subset_1(C_37,k1_zfmisc_1(k2_zfmisc_1(A_38,B_39))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_84,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_80])).

tff(c_54,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_85,plain,(
    ! [C_40,A_41,B_42] :
      ( v4_relat_1(C_40,A_41)
      | ~ m1_subset_1(C_40,k1_zfmisc_1(k2_zfmisc_1(A_41,B_42))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_89,plain,(
    v4_relat_1('#skF_5',k1_tarski('#skF_3')) ),
    inference(resolution,[status(thm)],[c_50,c_85])).

tff(c_90,plain,(
    ! [B_43,A_44] :
      ( k7_relat_1(B_43,A_44) = B_43
      | ~ v4_relat_1(B_43,A_44)
      | ~ v1_relat_1(B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_93,plain,
    ( k7_relat_1('#skF_5',k1_tarski('#skF_3')) = '#skF_5'
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_89,c_90])).

tff(c_96,plain,(
    k7_relat_1('#skF_5',k1_tarski('#skF_3')) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_93])).

tff(c_183,plain,(
    ! [B_79,A_80] :
      ( k2_relat_1(k7_relat_1(B_79,k1_tarski(A_80))) = k1_tarski(k1_funct_1(B_79,A_80))
      | ~ r2_hidden(A_80,k1_relat_1(B_79))
      | ~ v1_funct_1(B_79)
      | ~ v1_relat_1(B_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_192,plain,
    ( k1_tarski(k1_funct_1('#skF_5','#skF_3')) = k2_relat_1('#skF_5')
    | ~ r2_hidden('#skF_3',k1_relat_1('#skF_5'))
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_183])).

tff(c_196,plain,
    ( k1_tarski(k1_funct_1('#skF_5','#skF_3')) = k2_relat_1('#skF_5')
    | ~ r2_hidden('#skF_3',k1_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_54,c_192])).

tff(c_197,plain,(
    ~ r2_hidden('#skF_3',k1_relat_1('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_121,c_196])).

tff(c_244,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_230,c_197])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:27:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.29/1.28  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.29/1.29  
% 2.29/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.29/1.29  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k7_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.29/1.29  
% 2.29/1.29  %Foreground sorts:
% 2.29/1.29  
% 2.29/1.29  
% 2.29/1.29  %Background operators:
% 2.29/1.29  
% 2.29/1.29  
% 2.29/1.29  %Foreground operators:
% 2.29/1.29  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.29/1.29  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.29/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.29/1.29  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.29/1.29  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.29/1.29  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.29/1.29  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.29/1.29  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.29/1.29  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.29/1.29  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.29/1.29  tff('#skF_5', type, '#skF_5': $i).
% 2.29/1.29  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.29/1.29  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.29/1.29  tff('#skF_3', type, '#skF_3': $i).
% 2.29/1.29  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.29/1.29  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.29/1.29  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.29/1.29  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.29/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.29/1.29  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.29/1.29  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.29/1.29  tff('#skF_4', type, '#skF_4': $i).
% 2.29/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.29/1.29  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.29/1.29  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.29/1.29  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.29/1.29  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.29/1.29  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.29/1.29  
% 2.29/1.30  tff(f_100, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_tarski(A), B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => (k2_relset_1(k1_tarski(A), B, C) = k1_tarski(k1_funct_1(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_funct_2)).
% 2.29/1.30  tff(f_66, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.29/1.30  tff(f_88, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 2.29/1.30  tff(f_32, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 2.29/1.30  tff(f_70, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.29/1.30  tff(f_56, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.29/1.30  tff(f_62, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.29/1.30  tff(f_44, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 2.29/1.30  tff(f_52, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => (k2_relat_1(k7_relat_1(B, k1_tarski(A))) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t168_funct_1)).
% 2.29/1.30  tff(c_48, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.29/1.30  tff(c_52, plain, (v1_funct_2('#skF_5', k1_tarski('#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.29/1.30  tff(c_50, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_3'), '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.29/1.30  tff(c_128, plain, (![A_59, B_60, C_61]: (k1_relset_1(A_59, B_60, C_61)=k1_relat_1(C_61) | ~m1_subset_1(C_61, k1_zfmisc_1(k2_zfmisc_1(A_59, B_60))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.29/1.30  tff(c_132, plain, (k1_relset_1(k1_tarski('#skF_3'), '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_50, c_128])).
% 2.29/1.30  tff(c_198, plain, (![B_81, A_82, C_83]: (k1_xboole_0=B_81 | k1_relset_1(A_82, B_81, C_83)=A_82 | ~v1_funct_2(C_83, A_82, B_81) | ~m1_subset_1(C_83, k1_zfmisc_1(k2_zfmisc_1(A_82, B_81))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.29/1.30  tff(c_201, plain, (k1_xboole_0='#skF_4' | k1_relset_1(k1_tarski('#skF_3'), '#skF_4', '#skF_5')=k1_tarski('#skF_3') | ~v1_funct_2('#skF_5', k1_tarski('#skF_3'), '#skF_4')), inference(resolution, [status(thm)], [c_50, c_198])).
% 2.29/1.30  tff(c_204, plain, (k1_xboole_0='#skF_4' | k1_tarski('#skF_3')=k1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_132, c_201])).
% 2.29/1.30  tff(c_205, plain, (k1_tarski('#skF_3')=k1_relat_1('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_48, c_204])).
% 2.29/1.30  tff(c_4, plain, (![C_5]: (r2_hidden(C_5, k1_tarski(C_5)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.29/1.30  tff(c_230, plain, (r2_hidden('#skF_3', k1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_205, c_4])).
% 2.29/1.30  tff(c_116, plain, (![A_53, B_54, C_55]: (k2_relset_1(A_53, B_54, C_55)=k2_relat_1(C_55) | ~m1_subset_1(C_55, k1_zfmisc_1(k2_zfmisc_1(A_53, B_54))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.29/1.30  tff(c_120, plain, (k2_relset_1(k1_tarski('#skF_3'), '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_50, c_116])).
% 2.29/1.30  tff(c_46, plain, (k2_relset_1(k1_tarski('#skF_3'), '#skF_4', '#skF_5')!=k1_tarski(k1_funct_1('#skF_5', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.29/1.30  tff(c_121, plain, (k1_tarski(k1_funct_1('#skF_5', '#skF_3'))!=k2_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_120, c_46])).
% 2.29/1.30  tff(c_80, plain, (![C_37, A_38, B_39]: (v1_relat_1(C_37) | ~m1_subset_1(C_37, k1_zfmisc_1(k2_zfmisc_1(A_38, B_39))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.29/1.30  tff(c_84, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_50, c_80])).
% 2.29/1.30  tff(c_54, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.29/1.30  tff(c_85, plain, (![C_40, A_41, B_42]: (v4_relat_1(C_40, A_41) | ~m1_subset_1(C_40, k1_zfmisc_1(k2_zfmisc_1(A_41, B_42))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.29/1.30  tff(c_89, plain, (v4_relat_1('#skF_5', k1_tarski('#skF_3'))), inference(resolution, [status(thm)], [c_50, c_85])).
% 2.29/1.30  tff(c_90, plain, (![B_43, A_44]: (k7_relat_1(B_43, A_44)=B_43 | ~v4_relat_1(B_43, A_44) | ~v1_relat_1(B_43))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.29/1.30  tff(c_93, plain, (k7_relat_1('#skF_5', k1_tarski('#skF_3'))='#skF_5' | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_89, c_90])).
% 2.29/1.30  tff(c_96, plain, (k7_relat_1('#skF_5', k1_tarski('#skF_3'))='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_84, c_93])).
% 2.29/1.30  tff(c_183, plain, (![B_79, A_80]: (k2_relat_1(k7_relat_1(B_79, k1_tarski(A_80)))=k1_tarski(k1_funct_1(B_79, A_80)) | ~r2_hidden(A_80, k1_relat_1(B_79)) | ~v1_funct_1(B_79) | ~v1_relat_1(B_79))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.29/1.30  tff(c_192, plain, (k1_tarski(k1_funct_1('#skF_5', '#skF_3'))=k2_relat_1('#skF_5') | ~r2_hidden('#skF_3', k1_relat_1('#skF_5')) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_96, c_183])).
% 2.29/1.30  tff(c_196, plain, (k1_tarski(k1_funct_1('#skF_5', '#skF_3'))=k2_relat_1('#skF_5') | ~r2_hidden('#skF_3', k1_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_54, c_192])).
% 2.29/1.30  tff(c_197, plain, (~r2_hidden('#skF_3', k1_relat_1('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_121, c_196])).
% 2.29/1.30  tff(c_244, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_230, c_197])).
% 2.29/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.29/1.30  
% 2.29/1.30  Inference rules
% 2.29/1.30  ----------------------
% 2.29/1.30  #Ref     : 0
% 2.29/1.30  #Sup     : 40
% 2.29/1.30  #Fact    : 0
% 2.29/1.30  #Define  : 0
% 2.29/1.30  #Split   : 0
% 2.29/1.30  #Chain   : 0
% 2.29/1.30  #Close   : 0
% 2.29/1.30  
% 2.29/1.30  Ordering : KBO
% 2.29/1.30  
% 2.29/1.30  Simplification rules
% 2.29/1.30  ----------------------
% 2.29/1.30  #Subsume      : 0
% 2.29/1.30  #Demod        : 26
% 2.29/1.30  #Tautology    : 23
% 2.29/1.30  #SimpNegUnit  : 3
% 2.29/1.30  #BackRed      : 7
% 2.29/1.30  
% 2.29/1.30  #Partial instantiations: 0
% 2.29/1.30  #Strategies tried      : 1
% 2.29/1.30  
% 2.29/1.30  Timing (in seconds)
% 2.29/1.30  ----------------------
% 2.29/1.31  Preprocessing        : 0.33
% 2.29/1.31  Parsing              : 0.17
% 2.29/1.31  CNF conversion       : 0.02
% 2.29/1.31  Main loop            : 0.21
% 2.29/1.31  Inferencing          : 0.08
% 2.29/1.31  Reduction            : 0.06
% 2.29/1.31  Demodulation         : 0.05
% 2.29/1.31  BG Simplification    : 0.02
% 2.29/1.31  Subsumption          : 0.04
% 2.29/1.31  Abstraction          : 0.01
% 2.29/1.31  MUC search           : 0.00
% 2.29/1.31  Cooper               : 0.00
% 2.29/1.31  Total                : 0.57
% 2.29/1.31  Index Insertion      : 0.00
% 2.29/1.31  Index Deletion       : 0.00
% 2.29/1.31  Index Matching       : 0.00
% 2.29/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
