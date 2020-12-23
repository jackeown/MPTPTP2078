%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:54 EST 2020

% Result     : Theorem 3.06s
% Output     : CNFRefutation 3.24s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 104 expanded)
%              Number of leaves         :   38 (  55 expanded)
%              Depth                    :    9
%              Number of atoms          :   82 ( 190 expanded)
%              Number of equality atoms :   33 (  63 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

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

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k11_relat_1,type,(
    k11_relat_1: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_99,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,k1_tarski(A),B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r1_tarski(k7_relset_1(k1_tarski(A),B,D,C),k1_tarski(k1_funct_1(D,A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_2)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_87,axiom,(
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

tff(f_45,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] : k11_relat_1(A,B) = k9_relat_1(A,k1_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k9_relat_1(B,A),k9_relat_1(B,k1_relat_1(B))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_relat_1)).

tff(f_36,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(f_57,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => k11_relat_1(B,A) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_funct_1)).

tff(f_69,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(c_54,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_3'),'#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_87,plain,(
    ! [C_41,A_42,B_43] :
      ( v1_relat_1(C_41)
      | ~ m1_subset_1(C_41,k1_zfmisc_1(k2_zfmisc_1(A_42,B_43))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_91,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_54,c_87])).

tff(c_52,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_56,plain,(
    v1_funct_2('#skF_6',k1_tarski('#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_134,plain,(
    ! [A_56,B_57,C_58] :
      ( k1_relset_1(A_56,B_57,C_58) = k1_relat_1(C_58)
      | ~ m1_subset_1(C_58,k1_zfmisc_1(k2_zfmisc_1(A_56,B_57))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_138,plain,(
    k1_relset_1(k1_tarski('#skF_3'),'#skF_4','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_54,c_134])).

tff(c_173,plain,(
    ! [B_87,A_88,C_89] :
      ( k1_xboole_0 = B_87
      | k1_relset_1(A_88,B_87,C_89) = A_88
      | ~ v1_funct_2(C_89,A_88,B_87)
      | ~ m1_subset_1(C_89,k1_zfmisc_1(k2_zfmisc_1(A_88,B_87))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_176,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1(k1_tarski('#skF_3'),'#skF_4','#skF_6') = k1_tarski('#skF_3')
    | ~ v1_funct_2('#skF_6',k1_tarski('#skF_3'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_173])).

tff(c_179,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_tarski('#skF_3') = k1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_138,c_176])).

tff(c_180,plain,(
    k1_tarski('#skF_3') = k1_relat_1('#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_179])).

tff(c_26,plain,(
    ! [A_13,B_15] :
      ( k9_relat_1(A_13,k1_tarski(B_15)) = k11_relat_1(A_13,B_15)
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1368,plain,(
    ! [A_2824] :
      ( k9_relat_1(A_2824,k1_relat_1('#skF_6')) = k11_relat_1(A_2824,'#skF_3')
      | ~ v1_relat_1(A_2824) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_180,c_26])).

tff(c_28,plain,(
    ! [B_17,A_16] :
      ( r1_tarski(k9_relat_1(B_17,A_16),k9_relat_1(B_17,k1_relat_1(B_17)))
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1382,plain,(
    ! [A_16] :
      ( r1_tarski(k9_relat_1('#skF_6',A_16),k11_relat_1('#skF_6','#skF_3'))
      | ~ v1_relat_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1368,c_28])).

tff(c_1392,plain,(
    ! [A_16] : r1_tarski(k9_relat_1('#skF_6',A_16),k11_relat_1('#skF_6','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_91,c_1382])).

tff(c_58,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_20,plain,(
    ! [A_7] : k2_tarski(A_7,A_7) = k1_tarski(A_7) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_68,plain,(
    ! [D_34,B_35] : r2_hidden(D_34,k2_tarski(D_34,B_35)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_71,plain,(
    ! [A_7] : r2_hidden(A_7,k1_tarski(A_7)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_68])).

tff(c_194,plain,(
    r2_hidden('#skF_3',k1_relat_1('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_180,c_71])).

tff(c_30,plain,(
    ! [B_19,A_18] :
      ( k1_tarski(k1_funct_1(B_19,A_18)) = k11_relat_1(B_19,A_18)
      | ~ r2_hidden(A_18,k1_relat_1(B_19))
      | ~ v1_funct_1(B_19)
      | ~ v1_relat_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_677,plain,
    ( k1_tarski(k1_funct_1('#skF_6','#skF_3')) = k11_relat_1('#skF_6','#skF_3')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_194,c_30])).

tff(c_680,plain,(
    k1_tarski(k1_funct_1('#skF_6','#skF_3')) = k11_relat_1('#skF_6','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_58,c_677])).

tff(c_146,plain,(
    ! [A_64,B_65,C_66,D_67] :
      ( k7_relset_1(A_64,B_65,C_66,D_67) = k9_relat_1(C_66,D_67)
      | ~ m1_subset_1(C_66,k1_zfmisc_1(k2_zfmisc_1(A_64,B_65))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_149,plain,(
    ! [D_67] : k7_relset_1(k1_tarski('#skF_3'),'#skF_4','#skF_6',D_67) = k9_relat_1('#skF_6',D_67) ),
    inference(resolution,[status(thm)],[c_54,c_146])).

tff(c_50,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski('#skF_3'),'#skF_4','#skF_6','#skF_5'),k1_tarski(k1_funct_1('#skF_6','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_150,plain,(
    ~ r1_tarski(k9_relat_1('#skF_6','#skF_5'),k1_tarski(k1_funct_1('#skF_6','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_149,c_50])).

tff(c_715,plain,(
    ~ r1_tarski(k9_relat_1('#skF_6','#skF_5'),k11_relat_1('#skF_6','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_680,c_150])).

tff(c_1399,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1392,c_715])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n008.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 09:47:45 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.06/1.46  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.06/1.47  
% 3.06/1.47  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.06/1.47  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4
% 3.06/1.47  
% 3.06/1.47  %Foreground sorts:
% 3.06/1.47  
% 3.06/1.47  
% 3.06/1.47  %Background operators:
% 3.06/1.47  
% 3.06/1.47  
% 3.06/1.47  %Foreground operators:
% 3.06/1.47  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.06/1.47  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.06/1.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.06/1.47  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.06/1.47  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.06/1.47  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.06/1.47  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.06/1.47  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.06/1.47  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 3.06/1.47  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.06/1.47  tff('#skF_5', type, '#skF_5': $i).
% 3.06/1.47  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.06/1.47  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 3.06/1.47  tff('#skF_6', type, '#skF_6': $i).
% 3.06/1.47  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.06/1.47  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.06/1.47  tff('#skF_3', type, '#skF_3': $i).
% 3.06/1.47  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.06/1.47  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.06/1.47  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.06/1.47  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.06/1.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.06/1.47  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.06/1.47  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.06/1.47  tff('#skF_4', type, '#skF_4': $i).
% 3.06/1.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.06/1.47  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.06/1.47  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.06/1.47  
% 3.24/1.48  tff(f_99, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, k1_tarski(A), B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r1_tarski(k7_relset_1(k1_tarski(A), B, D, C), k1_tarski(k1_funct_1(D, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_funct_2)).
% 3.24/1.48  tff(f_61, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.24/1.48  tff(f_65, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.24/1.48  tff(f_87, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 3.24/1.48  tff(f_45, axiom, (![A]: (v1_relat_1(A) => (![B]: (k11_relat_1(A, B) = k9_relat_1(A, k1_tarski(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d16_relat_1)).
% 3.24/1.48  tff(f_49, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k9_relat_1(B, A), k9_relat_1(B, k1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t147_relat_1)).
% 3.24/1.48  tff(f_36, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 3.24/1.48  tff(f_34, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 3.24/1.48  tff(f_57, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => (k11_relat_1(B, A) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t117_funct_1)).
% 3.24/1.48  tff(f_69, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 3.24/1.48  tff(c_54, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_3'), '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.24/1.48  tff(c_87, plain, (![C_41, A_42, B_43]: (v1_relat_1(C_41) | ~m1_subset_1(C_41, k1_zfmisc_1(k2_zfmisc_1(A_42, B_43))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.24/1.48  tff(c_91, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_54, c_87])).
% 3.24/1.48  tff(c_52, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.24/1.48  tff(c_56, plain, (v1_funct_2('#skF_6', k1_tarski('#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.24/1.48  tff(c_134, plain, (![A_56, B_57, C_58]: (k1_relset_1(A_56, B_57, C_58)=k1_relat_1(C_58) | ~m1_subset_1(C_58, k1_zfmisc_1(k2_zfmisc_1(A_56, B_57))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.24/1.48  tff(c_138, plain, (k1_relset_1(k1_tarski('#skF_3'), '#skF_4', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_54, c_134])).
% 3.24/1.48  tff(c_173, plain, (![B_87, A_88, C_89]: (k1_xboole_0=B_87 | k1_relset_1(A_88, B_87, C_89)=A_88 | ~v1_funct_2(C_89, A_88, B_87) | ~m1_subset_1(C_89, k1_zfmisc_1(k2_zfmisc_1(A_88, B_87))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.24/1.48  tff(c_176, plain, (k1_xboole_0='#skF_4' | k1_relset_1(k1_tarski('#skF_3'), '#skF_4', '#skF_6')=k1_tarski('#skF_3') | ~v1_funct_2('#skF_6', k1_tarski('#skF_3'), '#skF_4')), inference(resolution, [status(thm)], [c_54, c_173])).
% 3.24/1.48  tff(c_179, plain, (k1_xboole_0='#skF_4' | k1_tarski('#skF_3')=k1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_138, c_176])).
% 3.24/1.48  tff(c_180, plain, (k1_tarski('#skF_3')=k1_relat_1('#skF_6')), inference(negUnitSimplification, [status(thm)], [c_52, c_179])).
% 3.24/1.48  tff(c_26, plain, (![A_13, B_15]: (k9_relat_1(A_13, k1_tarski(B_15))=k11_relat_1(A_13, B_15) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.24/1.48  tff(c_1368, plain, (![A_2824]: (k9_relat_1(A_2824, k1_relat_1('#skF_6'))=k11_relat_1(A_2824, '#skF_3') | ~v1_relat_1(A_2824))), inference(superposition, [status(thm), theory('equality')], [c_180, c_26])).
% 3.24/1.48  tff(c_28, plain, (![B_17, A_16]: (r1_tarski(k9_relat_1(B_17, A_16), k9_relat_1(B_17, k1_relat_1(B_17))) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.24/1.48  tff(c_1382, plain, (![A_16]: (r1_tarski(k9_relat_1('#skF_6', A_16), k11_relat_1('#skF_6', '#skF_3')) | ~v1_relat_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_1368, c_28])).
% 3.24/1.48  tff(c_1392, plain, (![A_16]: (r1_tarski(k9_relat_1('#skF_6', A_16), k11_relat_1('#skF_6', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_91, c_91, c_1382])).
% 3.24/1.48  tff(c_58, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.24/1.48  tff(c_20, plain, (![A_7]: (k2_tarski(A_7, A_7)=k1_tarski(A_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.24/1.48  tff(c_68, plain, (![D_34, B_35]: (r2_hidden(D_34, k2_tarski(D_34, B_35)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.24/1.48  tff(c_71, plain, (![A_7]: (r2_hidden(A_7, k1_tarski(A_7)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_68])).
% 3.24/1.48  tff(c_194, plain, (r2_hidden('#skF_3', k1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_180, c_71])).
% 3.24/1.48  tff(c_30, plain, (![B_19, A_18]: (k1_tarski(k1_funct_1(B_19, A_18))=k11_relat_1(B_19, A_18) | ~r2_hidden(A_18, k1_relat_1(B_19)) | ~v1_funct_1(B_19) | ~v1_relat_1(B_19))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.24/1.48  tff(c_677, plain, (k1_tarski(k1_funct_1('#skF_6', '#skF_3'))=k11_relat_1('#skF_6', '#skF_3') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_194, c_30])).
% 3.24/1.48  tff(c_680, plain, (k1_tarski(k1_funct_1('#skF_6', '#skF_3'))=k11_relat_1('#skF_6', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_91, c_58, c_677])).
% 3.24/1.48  tff(c_146, plain, (![A_64, B_65, C_66, D_67]: (k7_relset_1(A_64, B_65, C_66, D_67)=k9_relat_1(C_66, D_67) | ~m1_subset_1(C_66, k1_zfmisc_1(k2_zfmisc_1(A_64, B_65))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.24/1.48  tff(c_149, plain, (![D_67]: (k7_relset_1(k1_tarski('#skF_3'), '#skF_4', '#skF_6', D_67)=k9_relat_1('#skF_6', D_67))), inference(resolution, [status(thm)], [c_54, c_146])).
% 3.24/1.48  tff(c_50, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_3'), '#skF_4', '#skF_6', '#skF_5'), k1_tarski(k1_funct_1('#skF_6', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.24/1.48  tff(c_150, plain, (~r1_tarski(k9_relat_1('#skF_6', '#skF_5'), k1_tarski(k1_funct_1('#skF_6', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_149, c_50])).
% 3.24/1.48  tff(c_715, plain, (~r1_tarski(k9_relat_1('#skF_6', '#skF_5'), k11_relat_1('#skF_6', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_680, c_150])).
% 3.24/1.48  tff(c_1399, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1392, c_715])).
% 3.24/1.48  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.24/1.48  
% 3.24/1.48  Inference rules
% 3.24/1.48  ----------------------
% 3.24/1.48  #Ref     : 0
% 3.24/1.48  #Sup     : 150
% 3.24/1.48  #Fact    : 4
% 3.24/1.48  #Define  : 0
% 3.24/1.48  #Split   : 0
% 3.24/1.48  #Chain   : 0
% 3.24/1.48  #Close   : 0
% 3.24/1.48  
% 3.24/1.48  Ordering : KBO
% 3.24/1.48  
% 3.24/1.48  Simplification rules
% 3.24/1.48  ----------------------
% 3.24/1.48  #Subsume      : 13
% 3.24/1.48  #Demod        : 29
% 3.24/1.48  #Tautology    : 44
% 3.24/1.48  #SimpNegUnit  : 4
% 3.24/1.48  #BackRed      : 7
% 3.24/1.48  
% 3.24/1.48  #Partial instantiations: 1615
% 3.24/1.48  #Strategies tried      : 1
% 3.24/1.48  
% 3.24/1.48  Timing (in seconds)
% 3.24/1.48  ----------------------
% 3.24/1.49  Preprocessing        : 0.32
% 3.24/1.49  Parsing              : 0.16
% 3.24/1.49  CNF conversion       : 0.02
% 3.24/1.49  Main loop            : 0.39
% 3.24/1.49  Inferencing          : 0.22
% 3.24/1.49  Reduction            : 0.09
% 3.24/1.49  Demodulation         : 0.06
% 3.24/1.49  BG Simplification    : 0.02
% 3.24/1.49  Subsumption          : 0.05
% 3.24/1.49  Abstraction          : 0.02
% 3.24/1.49  MUC search           : 0.00
% 3.24/1.49  Cooper               : 0.00
% 3.24/1.49  Total                : 0.74
% 3.24/1.49  Index Insertion      : 0.00
% 3.24/1.49  Index Deletion       : 0.00
% 3.24/1.49  Index Matching       : 0.00
% 3.24/1.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
