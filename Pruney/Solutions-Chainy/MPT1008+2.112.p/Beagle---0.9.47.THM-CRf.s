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
% DateTime   : Thu Dec  3 10:14:41 EST 2020

% Result     : Theorem 2.54s
% Output     : CNFRefutation 2.54s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 112 expanded)
%              Number of leaves         :   38 (  58 expanded)
%              Depth                    :    8
%              Number of atoms          :   86 ( 226 expanded)
%              Number of equality atoms :   39 ( 105 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_101,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_tarski(A),B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => k2_relset_1(k1_tarski(A),B,C) = k1_tarski(k1_funct_1(C,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_funct_2)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_89,axiom,(
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

tff(f_65,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( k7_relset_1(A,B,C,A) = k2_relset_1(A,B,C)
        & k8_relset_1(A,B,C,B) = k1_relset_1(A,B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_relset_1)).

tff(f_45,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_43,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_49,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => k2_relat_1(k7_relat_1(B,k1_tarski(A))) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t168_funct_1)).

tff(c_48,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_52,plain,(
    v1_funct_2('#skF_5',k1_tarski('#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_50,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_3'),'#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_106,plain,(
    ! [A_50,B_51,C_52] :
      ( k1_relset_1(A_50,B_51,C_52) = k1_relat_1(C_52)
      | ~ m1_subset_1(C_52,k1_zfmisc_1(k2_zfmisc_1(A_50,B_51))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_110,plain,(
    k1_relset_1(k1_tarski('#skF_3'),'#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_106])).

tff(c_180,plain,(
    ! [B_76,A_77,C_78] :
      ( k1_xboole_0 = B_76
      | k1_relset_1(A_77,B_76,C_78) = A_77
      | ~ v1_funct_2(C_78,A_77,B_76)
      | ~ m1_subset_1(C_78,k1_zfmisc_1(k2_zfmisc_1(A_77,B_76))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_183,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1(k1_tarski('#skF_3'),'#skF_4','#skF_5') = k1_tarski('#skF_3')
    | ~ v1_funct_2('#skF_5',k1_tarski('#skF_3'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_180])).

tff(c_186,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_tarski('#skF_3') = k1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_110,c_183])).

tff(c_187,plain,(
    k1_tarski('#skF_3') = k1_relat_1('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_186])).

tff(c_121,plain,(
    ! [A_55,B_56,C_57,D_58] :
      ( k7_relset_1(A_55,B_56,C_57,D_58) = k9_relat_1(C_57,D_58)
      | ~ m1_subset_1(C_57,k1_zfmisc_1(k2_zfmisc_1(A_55,B_56))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_124,plain,(
    ! [D_58] : k7_relset_1(k1_tarski('#skF_3'),'#skF_4','#skF_5',D_58) = k9_relat_1('#skF_5',D_58) ),
    inference(resolution,[status(thm)],[c_50,c_121])).

tff(c_158,plain,(
    ! [A_64,B_65,C_66] :
      ( k7_relset_1(A_64,B_65,C_66,A_64) = k2_relset_1(A_64,B_65,C_66)
      | ~ m1_subset_1(C_66,k1_zfmisc_1(k2_zfmisc_1(A_64,B_65))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_160,plain,(
    k7_relset_1(k1_tarski('#skF_3'),'#skF_4','#skF_5',k1_tarski('#skF_3')) = k2_relset_1(k1_tarski('#skF_3'),'#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_158])).

tff(c_162,plain,(
    k2_relset_1(k1_tarski('#skF_3'),'#skF_4','#skF_5') = k9_relat_1('#skF_5',k1_tarski('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_160])).

tff(c_46,plain,(
    k2_relset_1(k1_tarski('#skF_3'),'#skF_4','#skF_5') != k1_tarski(k1_funct_1('#skF_5','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_172,plain,(
    k9_relat_1('#skF_5',k1_tarski('#skF_3')) != k1_tarski(k1_funct_1('#skF_5','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_162,c_46])).

tff(c_188,plain,(
    k9_relat_1('#skF_5',k1_relat_1('#skF_5')) != k1_tarski(k1_funct_1('#skF_5','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_187,c_172])).

tff(c_20,plain,(
    ! [A_12,B_13] : v1_relat_1(k2_zfmisc_1(A_12,B_13)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_81,plain,(
    ! [B_39,A_40] :
      ( v1_relat_1(B_39)
      | ~ m1_subset_1(B_39,k1_zfmisc_1(A_40))
      | ~ v1_relat_1(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_84,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1(k1_tarski('#skF_3'),'#skF_4')) ),
    inference(resolution,[status(thm)],[c_50,c_81])).

tff(c_87,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_84])).

tff(c_54,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_4,plain,(
    ! [C_5] : r2_hidden(C_5,k1_tarski(C_5)) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_210,plain,(
    r2_hidden('#skF_3',k1_relat_1('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_187,c_4])).

tff(c_22,plain,(
    ! [B_15,A_14] :
      ( k2_relat_1(k7_relat_1(B_15,A_14)) = k9_relat_1(B_15,A_14)
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_217,plain,(
    ! [B_79,A_80] :
      ( k2_relat_1(k7_relat_1(B_79,k1_tarski(A_80))) = k1_tarski(k1_funct_1(B_79,A_80))
      | ~ r2_hidden(A_80,k1_relat_1(B_79))
      | ~ v1_funct_1(B_79)
      | ~ v1_relat_1(B_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_333,plain,(
    ! [B_88,A_89] :
      ( k9_relat_1(B_88,k1_tarski(A_89)) = k1_tarski(k1_funct_1(B_88,A_89))
      | ~ r2_hidden(A_89,k1_relat_1(B_88))
      | ~ v1_funct_1(B_88)
      | ~ v1_relat_1(B_88)
      | ~ v1_relat_1(B_88) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_217])).

tff(c_336,plain,
    ( k9_relat_1('#skF_5',k1_tarski('#skF_3')) = k1_tarski(k1_funct_1('#skF_5','#skF_3'))
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_210,c_333])).

tff(c_347,plain,(
    k9_relat_1('#skF_5',k1_relat_1('#skF_5')) = k1_tarski(k1_funct_1('#skF_5','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_54,c_187,c_336])).

tff(c_349,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_188,c_347])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:49:30 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.54/1.33  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.54/1.34  
% 2.54/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.54/1.34  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.54/1.34  
% 2.54/1.34  %Foreground sorts:
% 2.54/1.34  
% 2.54/1.34  
% 2.54/1.34  %Background operators:
% 2.54/1.34  
% 2.54/1.34  
% 2.54/1.34  %Foreground operators:
% 2.54/1.34  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.54/1.34  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.54/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.54/1.34  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.54/1.34  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.54/1.34  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.54/1.34  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 2.54/1.34  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.54/1.34  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.54/1.34  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.54/1.34  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.54/1.34  tff('#skF_5', type, '#skF_5': $i).
% 2.54/1.34  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.54/1.34  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.54/1.34  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.54/1.34  tff('#skF_3', type, '#skF_3': $i).
% 2.54/1.34  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.54/1.34  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.54/1.34  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.54/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.54/1.34  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.54/1.34  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.54/1.34  tff('#skF_4', type, '#skF_4': $i).
% 2.54/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.54/1.34  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.54/1.34  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.54/1.34  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.54/1.34  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.54/1.34  
% 2.54/1.35  tff(f_101, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_tarski(A), B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => (k2_relset_1(k1_tarski(A), B, C) = k1_tarski(k1_funct_1(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_funct_2)).
% 2.54/1.35  tff(f_61, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.54/1.35  tff(f_89, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 2.54/1.35  tff(f_65, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 2.54/1.35  tff(f_71, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((k7_relset_1(A, B, C, A) = k2_relset_1(A, B, C)) & (k8_relset_1(A, B, C, B) = k1_relset_1(A, B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_relset_1)).
% 2.54/1.35  tff(f_45, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.54/1.35  tff(f_43, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.54/1.35  tff(f_32, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 2.54/1.35  tff(f_49, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 2.54/1.35  tff(f_57, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => (k2_relat_1(k7_relat_1(B, k1_tarski(A))) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t168_funct_1)).
% 2.54/1.35  tff(c_48, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.54/1.35  tff(c_52, plain, (v1_funct_2('#skF_5', k1_tarski('#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.54/1.35  tff(c_50, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_3'), '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.54/1.35  tff(c_106, plain, (![A_50, B_51, C_52]: (k1_relset_1(A_50, B_51, C_52)=k1_relat_1(C_52) | ~m1_subset_1(C_52, k1_zfmisc_1(k2_zfmisc_1(A_50, B_51))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.54/1.35  tff(c_110, plain, (k1_relset_1(k1_tarski('#skF_3'), '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_50, c_106])).
% 2.54/1.35  tff(c_180, plain, (![B_76, A_77, C_78]: (k1_xboole_0=B_76 | k1_relset_1(A_77, B_76, C_78)=A_77 | ~v1_funct_2(C_78, A_77, B_76) | ~m1_subset_1(C_78, k1_zfmisc_1(k2_zfmisc_1(A_77, B_76))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.54/1.35  tff(c_183, plain, (k1_xboole_0='#skF_4' | k1_relset_1(k1_tarski('#skF_3'), '#skF_4', '#skF_5')=k1_tarski('#skF_3') | ~v1_funct_2('#skF_5', k1_tarski('#skF_3'), '#skF_4')), inference(resolution, [status(thm)], [c_50, c_180])).
% 2.54/1.35  tff(c_186, plain, (k1_xboole_0='#skF_4' | k1_tarski('#skF_3')=k1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_110, c_183])).
% 2.54/1.35  tff(c_187, plain, (k1_tarski('#skF_3')=k1_relat_1('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_48, c_186])).
% 2.54/1.35  tff(c_121, plain, (![A_55, B_56, C_57, D_58]: (k7_relset_1(A_55, B_56, C_57, D_58)=k9_relat_1(C_57, D_58) | ~m1_subset_1(C_57, k1_zfmisc_1(k2_zfmisc_1(A_55, B_56))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.54/1.35  tff(c_124, plain, (![D_58]: (k7_relset_1(k1_tarski('#skF_3'), '#skF_4', '#skF_5', D_58)=k9_relat_1('#skF_5', D_58))), inference(resolution, [status(thm)], [c_50, c_121])).
% 2.54/1.35  tff(c_158, plain, (![A_64, B_65, C_66]: (k7_relset_1(A_64, B_65, C_66, A_64)=k2_relset_1(A_64, B_65, C_66) | ~m1_subset_1(C_66, k1_zfmisc_1(k2_zfmisc_1(A_64, B_65))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.54/1.35  tff(c_160, plain, (k7_relset_1(k1_tarski('#skF_3'), '#skF_4', '#skF_5', k1_tarski('#skF_3'))=k2_relset_1(k1_tarski('#skF_3'), '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_50, c_158])).
% 2.54/1.35  tff(c_162, plain, (k2_relset_1(k1_tarski('#skF_3'), '#skF_4', '#skF_5')=k9_relat_1('#skF_5', k1_tarski('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_124, c_160])).
% 2.54/1.35  tff(c_46, plain, (k2_relset_1(k1_tarski('#skF_3'), '#skF_4', '#skF_5')!=k1_tarski(k1_funct_1('#skF_5', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.54/1.35  tff(c_172, plain, (k9_relat_1('#skF_5', k1_tarski('#skF_3'))!=k1_tarski(k1_funct_1('#skF_5', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_162, c_46])).
% 2.54/1.35  tff(c_188, plain, (k9_relat_1('#skF_5', k1_relat_1('#skF_5'))!=k1_tarski(k1_funct_1('#skF_5', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_187, c_172])).
% 2.54/1.35  tff(c_20, plain, (![A_12, B_13]: (v1_relat_1(k2_zfmisc_1(A_12, B_13)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.54/1.35  tff(c_81, plain, (![B_39, A_40]: (v1_relat_1(B_39) | ~m1_subset_1(B_39, k1_zfmisc_1(A_40)) | ~v1_relat_1(A_40))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.54/1.35  tff(c_84, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1(k1_tarski('#skF_3'), '#skF_4'))), inference(resolution, [status(thm)], [c_50, c_81])).
% 2.54/1.35  tff(c_87, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_84])).
% 2.54/1.35  tff(c_54, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.54/1.35  tff(c_4, plain, (![C_5]: (r2_hidden(C_5, k1_tarski(C_5)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.54/1.35  tff(c_210, plain, (r2_hidden('#skF_3', k1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_187, c_4])).
% 2.54/1.35  tff(c_22, plain, (![B_15, A_14]: (k2_relat_1(k7_relat_1(B_15, A_14))=k9_relat_1(B_15, A_14) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.54/1.35  tff(c_217, plain, (![B_79, A_80]: (k2_relat_1(k7_relat_1(B_79, k1_tarski(A_80)))=k1_tarski(k1_funct_1(B_79, A_80)) | ~r2_hidden(A_80, k1_relat_1(B_79)) | ~v1_funct_1(B_79) | ~v1_relat_1(B_79))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.54/1.35  tff(c_333, plain, (![B_88, A_89]: (k9_relat_1(B_88, k1_tarski(A_89))=k1_tarski(k1_funct_1(B_88, A_89)) | ~r2_hidden(A_89, k1_relat_1(B_88)) | ~v1_funct_1(B_88) | ~v1_relat_1(B_88) | ~v1_relat_1(B_88))), inference(superposition, [status(thm), theory('equality')], [c_22, c_217])).
% 2.54/1.35  tff(c_336, plain, (k9_relat_1('#skF_5', k1_tarski('#skF_3'))=k1_tarski(k1_funct_1('#skF_5', '#skF_3')) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_210, c_333])).
% 2.54/1.35  tff(c_347, plain, (k9_relat_1('#skF_5', k1_relat_1('#skF_5'))=k1_tarski(k1_funct_1('#skF_5', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_87, c_54, c_187, c_336])).
% 2.54/1.35  tff(c_349, plain, $false, inference(negUnitSimplification, [status(thm)], [c_188, c_347])).
% 2.54/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.54/1.35  
% 2.54/1.35  Inference rules
% 2.54/1.35  ----------------------
% 2.54/1.35  #Ref     : 0
% 2.54/1.35  #Sup     : 66
% 2.54/1.35  #Fact    : 0
% 2.54/1.35  #Define  : 0
% 2.54/1.35  #Split   : 0
% 2.54/1.35  #Chain   : 0
% 2.54/1.35  #Close   : 0
% 2.54/1.35  
% 2.54/1.35  Ordering : KBO
% 2.54/1.36  
% 2.54/1.36  Simplification rules
% 2.54/1.36  ----------------------
% 2.54/1.36  #Subsume      : 3
% 2.54/1.36  #Demod        : 41
% 2.54/1.36  #Tautology    : 44
% 2.54/1.36  #SimpNegUnit  : 4
% 2.54/1.36  #BackRed      : 8
% 2.54/1.36  
% 2.54/1.36  #Partial instantiations: 0
% 2.54/1.36  #Strategies tried      : 1
% 2.54/1.36  
% 2.54/1.36  Timing (in seconds)
% 2.54/1.36  ----------------------
% 2.54/1.36  Preprocessing        : 0.34
% 2.54/1.36  Parsing              : 0.18
% 2.54/1.36  CNF conversion       : 0.02
% 2.54/1.36  Main loop            : 0.24
% 2.54/1.36  Inferencing          : 0.09
% 2.54/1.36  Reduction            : 0.07
% 2.54/1.36  Demodulation         : 0.05
% 2.54/1.36  BG Simplification    : 0.02
% 2.54/1.36  Subsumption          : 0.05
% 2.54/1.36  Abstraction          : 0.01
% 2.54/1.36  MUC search           : 0.00
% 2.54/1.36  Cooper               : 0.00
% 2.54/1.36  Total                : 0.62
% 2.54/1.36  Index Insertion      : 0.00
% 2.54/1.36  Index Deletion       : 0.00
% 2.54/1.36  Index Matching       : 0.00
% 2.54/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
