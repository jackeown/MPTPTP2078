%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:55 EST 2020

% Result     : Theorem 6.43s
% Output     : CNFRefutation 6.43s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 132 expanded)
%              Number of leaves         :   38 (  65 expanded)
%              Depth                    :   12
%              Number of atoms          :   93 ( 262 expanded)
%              Number of equality atoms :   36 (  96 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4

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

tff(f_100,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,k1_tarski(A),B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r1_tarski(k7_relset_1(k1_tarski(A),B,D,C),k1_tarski(k1_funct_1(D,A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_2)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k9_relat_1(B,A),k2_relat_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_relat_1)).

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

tff(f_36,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( ( r2_hidden(A,k1_relat_1(C))
          & r2_hidden(B,k1_relat_1(C)) )
       => k9_relat_1(C,k2_tarski(A,B)) = k2_tarski(k1_funct_1(C,A),k1_funct_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t118_funct_1)).

tff(f_48,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_70,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(c_54,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_3'),'#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_100,plain,(
    ! [C_43,A_44,B_45] :
      ( v1_relat_1(C_43)
      | ~ m1_subset_1(C_43,k1_zfmisc_1(k2_zfmisc_1(A_44,B_45))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_104,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_54,c_100])).

tff(c_26,plain,(
    ! [B_14,A_13] :
      ( r1_tarski(k9_relat_1(B_14,A_13),k2_relat_1(B_14))
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_58,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_52,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_56,plain,(
    v1_funct_2('#skF_6',k1_tarski('#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_135,plain,(
    ! [A_55,B_56,C_57] :
      ( k1_relset_1(A_55,B_56,C_57) = k1_relat_1(C_57)
      | ~ m1_subset_1(C_57,k1_zfmisc_1(k2_zfmisc_1(A_55,B_56))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_139,plain,(
    k1_relset_1(k1_tarski('#skF_3'),'#skF_4','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_54,c_135])).

tff(c_172,plain,(
    ! [B_82,A_83,C_84] :
      ( k1_xboole_0 = B_82
      | k1_relset_1(A_83,B_82,C_84) = A_83
      | ~ v1_funct_2(C_84,A_83,B_82)
      | ~ m1_subset_1(C_84,k1_zfmisc_1(k2_zfmisc_1(A_83,B_82))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_175,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1(k1_tarski('#skF_3'),'#skF_4','#skF_6') = k1_tarski('#skF_3')
    | ~ v1_funct_2('#skF_6',k1_tarski('#skF_3'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_172])).

tff(c_178,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_tarski('#skF_3') = k1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_139,c_175])).

tff(c_179,plain,(
    k1_tarski('#skF_3') = k1_relat_1('#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_178])).

tff(c_20,plain,(
    ! [A_7] : k2_tarski(A_7,A_7) = k1_tarski(A_7) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_68,plain,(
    ! [D_33,B_34] : r2_hidden(D_33,k2_tarski(D_33,B_34)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_71,plain,(
    ! [A_7] : r2_hidden(A_7,k1_tarski(A_7)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_68])).

tff(c_190,plain,(
    r2_hidden('#skF_3',k1_relat_1('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_179,c_71])).

tff(c_2306,plain,(
    ! [C_6172,A_6173,B_6174] :
      ( k2_tarski(k1_funct_1(C_6172,A_6173),k1_funct_1(C_6172,B_6174)) = k9_relat_1(C_6172,k2_tarski(A_6173,B_6174))
      | ~ r2_hidden(B_6174,k1_relat_1(C_6172))
      | ~ r2_hidden(A_6173,k1_relat_1(C_6172))
      | ~ v1_funct_1(C_6172)
      | ~ v1_relat_1(C_6172) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_2328,plain,(
    ! [C_6172,B_6174] :
      ( k9_relat_1(C_6172,k2_tarski(B_6174,B_6174)) = k1_tarski(k1_funct_1(C_6172,B_6174))
      | ~ r2_hidden(B_6174,k1_relat_1(C_6172))
      | ~ r2_hidden(B_6174,k1_relat_1(C_6172))
      | ~ v1_funct_1(C_6172)
      | ~ v1_relat_1(C_6172) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2306,c_20])).

tff(c_7221,plain,(
    ! [C_10458,B_10459] :
      ( k9_relat_1(C_10458,k1_tarski(B_10459)) = k1_tarski(k1_funct_1(C_10458,B_10459))
      | ~ r2_hidden(B_10459,k1_relat_1(C_10458))
      | ~ r2_hidden(B_10459,k1_relat_1(C_10458))
      | ~ v1_funct_1(C_10458)
      | ~ v1_relat_1(C_10458) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_2328])).

tff(c_7270,plain,
    ( k9_relat_1('#skF_6',k1_tarski('#skF_3')) = k1_tarski(k1_funct_1('#skF_6','#skF_3'))
    | ~ r2_hidden('#skF_3',k1_relat_1('#skF_6'))
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_190,c_7221])).

tff(c_7276,plain,(
    k9_relat_1('#skF_6',k1_relat_1('#skF_6')) = k1_tarski(k1_funct_1('#skF_6','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_58,c_190,c_179,c_7270])).

tff(c_28,plain,(
    ! [A_15] :
      ( k9_relat_1(A_15,k1_relat_1(A_15)) = k2_relat_1(A_15)
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_7283,plain,
    ( k1_tarski(k1_funct_1('#skF_6','#skF_3')) = k2_relat_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_7276,c_28])).

tff(c_7333,plain,(
    k1_tarski(k1_funct_1('#skF_6','#skF_3')) = k2_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_7283])).

tff(c_145,plain,(
    ! [A_59,B_60,C_61,D_62] :
      ( k7_relset_1(A_59,B_60,C_61,D_62) = k9_relat_1(C_61,D_62)
      | ~ m1_subset_1(C_61,k1_zfmisc_1(k2_zfmisc_1(A_59,B_60))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_148,plain,(
    ! [D_62] : k7_relset_1(k1_tarski('#skF_3'),'#skF_4','#skF_6',D_62) = k9_relat_1('#skF_6',D_62) ),
    inference(resolution,[status(thm)],[c_54,c_145])).

tff(c_50,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski('#skF_3'),'#skF_4','#skF_6','#skF_5'),k1_tarski(k1_funct_1('#skF_6','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_149,plain,(
    ~ r1_tarski(k9_relat_1('#skF_6','#skF_5'),k1_tarski(k1_funct_1('#skF_6','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_50])).

tff(c_7338,plain,(
    ~ r1_tarski(k9_relat_1('#skF_6','#skF_5'),k2_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7333,c_149])).

tff(c_7407,plain,(
    ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_26,c_7338])).

tff(c_7411,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_7407])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:12:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.43/2.33  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.43/2.34  
% 6.43/2.34  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.43/2.34  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4
% 6.43/2.34  
% 6.43/2.34  %Foreground sorts:
% 6.43/2.34  
% 6.43/2.34  
% 6.43/2.34  %Background operators:
% 6.43/2.34  
% 6.43/2.34  
% 6.43/2.34  %Foreground operators:
% 6.43/2.34  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 6.43/2.34  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.43/2.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.43/2.34  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.43/2.34  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.43/2.34  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.43/2.34  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.43/2.34  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 6.43/2.34  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.43/2.34  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 6.43/2.34  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.43/2.34  tff('#skF_5', type, '#skF_5': $i).
% 6.43/2.34  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.43/2.34  tff('#skF_6', type, '#skF_6': $i).
% 6.43/2.34  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.43/2.34  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 6.43/2.34  tff('#skF_3', type, '#skF_3': $i).
% 6.43/2.34  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 6.43/2.34  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 6.43/2.34  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.43/2.34  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 6.43/2.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.43/2.34  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.43/2.34  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.43/2.34  tff('#skF_4', type, '#skF_4': $i).
% 6.43/2.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.43/2.34  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.43/2.34  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.43/2.34  
% 6.43/2.35  tff(f_100, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, k1_tarski(A), B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r1_tarski(k7_relset_1(k1_tarski(A), B, D, C), k1_tarski(k1_funct_1(D, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_funct_2)).
% 6.43/2.35  tff(f_62, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 6.43/2.35  tff(f_44, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k9_relat_1(B, A), k2_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t144_relat_1)).
% 6.43/2.35  tff(f_66, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 6.43/2.35  tff(f_88, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 6.43/2.35  tff(f_36, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 6.43/2.35  tff(f_34, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 6.43/2.35  tff(f_58, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r2_hidden(A, k1_relat_1(C)) & r2_hidden(B, k1_relat_1(C))) => (k9_relat_1(C, k2_tarski(A, B)) = k2_tarski(k1_funct_1(C, A), k1_funct_1(C, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t118_funct_1)).
% 6.43/2.35  tff(f_48, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_relat_1)).
% 6.43/2.35  tff(f_70, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 6.43/2.35  tff(c_54, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_3'), '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_100])).
% 6.43/2.35  tff(c_100, plain, (![C_43, A_44, B_45]: (v1_relat_1(C_43) | ~m1_subset_1(C_43, k1_zfmisc_1(k2_zfmisc_1(A_44, B_45))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 6.43/2.35  tff(c_104, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_54, c_100])).
% 6.43/2.35  tff(c_26, plain, (![B_14, A_13]: (r1_tarski(k9_relat_1(B_14, A_13), k2_relat_1(B_14)) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_44])).
% 6.43/2.35  tff(c_58, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_100])).
% 6.43/2.35  tff(c_52, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_100])).
% 6.43/2.35  tff(c_56, plain, (v1_funct_2('#skF_6', k1_tarski('#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_100])).
% 6.43/2.35  tff(c_135, plain, (![A_55, B_56, C_57]: (k1_relset_1(A_55, B_56, C_57)=k1_relat_1(C_57) | ~m1_subset_1(C_57, k1_zfmisc_1(k2_zfmisc_1(A_55, B_56))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 6.43/2.35  tff(c_139, plain, (k1_relset_1(k1_tarski('#skF_3'), '#skF_4', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_54, c_135])).
% 6.43/2.35  tff(c_172, plain, (![B_82, A_83, C_84]: (k1_xboole_0=B_82 | k1_relset_1(A_83, B_82, C_84)=A_83 | ~v1_funct_2(C_84, A_83, B_82) | ~m1_subset_1(C_84, k1_zfmisc_1(k2_zfmisc_1(A_83, B_82))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 6.43/2.35  tff(c_175, plain, (k1_xboole_0='#skF_4' | k1_relset_1(k1_tarski('#skF_3'), '#skF_4', '#skF_6')=k1_tarski('#skF_3') | ~v1_funct_2('#skF_6', k1_tarski('#skF_3'), '#skF_4')), inference(resolution, [status(thm)], [c_54, c_172])).
% 6.43/2.35  tff(c_178, plain, (k1_xboole_0='#skF_4' | k1_tarski('#skF_3')=k1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_139, c_175])).
% 6.43/2.35  tff(c_179, plain, (k1_tarski('#skF_3')=k1_relat_1('#skF_6')), inference(negUnitSimplification, [status(thm)], [c_52, c_178])).
% 6.43/2.35  tff(c_20, plain, (![A_7]: (k2_tarski(A_7, A_7)=k1_tarski(A_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 6.43/2.35  tff(c_68, plain, (![D_33, B_34]: (r2_hidden(D_33, k2_tarski(D_33, B_34)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 6.43/2.35  tff(c_71, plain, (![A_7]: (r2_hidden(A_7, k1_tarski(A_7)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_68])).
% 6.43/2.35  tff(c_190, plain, (r2_hidden('#skF_3', k1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_179, c_71])).
% 6.43/2.35  tff(c_2306, plain, (![C_6172, A_6173, B_6174]: (k2_tarski(k1_funct_1(C_6172, A_6173), k1_funct_1(C_6172, B_6174))=k9_relat_1(C_6172, k2_tarski(A_6173, B_6174)) | ~r2_hidden(B_6174, k1_relat_1(C_6172)) | ~r2_hidden(A_6173, k1_relat_1(C_6172)) | ~v1_funct_1(C_6172) | ~v1_relat_1(C_6172))), inference(cnfTransformation, [status(thm)], [f_58])).
% 6.43/2.35  tff(c_2328, plain, (![C_6172, B_6174]: (k9_relat_1(C_6172, k2_tarski(B_6174, B_6174))=k1_tarski(k1_funct_1(C_6172, B_6174)) | ~r2_hidden(B_6174, k1_relat_1(C_6172)) | ~r2_hidden(B_6174, k1_relat_1(C_6172)) | ~v1_funct_1(C_6172) | ~v1_relat_1(C_6172))), inference(superposition, [status(thm), theory('equality')], [c_2306, c_20])).
% 6.43/2.35  tff(c_7221, plain, (![C_10458, B_10459]: (k9_relat_1(C_10458, k1_tarski(B_10459))=k1_tarski(k1_funct_1(C_10458, B_10459)) | ~r2_hidden(B_10459, k1_relat_1(C_10458)) | ~r2_hidden(B_10459, k1_relat_1(C_10458)) | ~v1_funct_1(C_10458) | ~v1_relat_1(C_10458))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_2328])).
% 6.43/2.35  tff(c_7270, plain, (k9_relat_1('#skF_6', k1_tarski('#skF_3'))=k1_tarski(k1_funct_1('#skF_6', '#skF_3')) | ~r2_hidden('#skF_3', k1_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_190, c_7221])).
% 6.43/2.35  tff(c_7276, plain, (k9_relat_1('#skF_6', k1_relat_1('#skF_6'))=k1_tarski(k1_funct_1('#skF_6', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_104, c_58, c_190, c_179, c_7270])).
% 6.43/2.35  tff(c_28, plain, (![A_15]: (k9_relat_1(A_15, k1_relat_1(A_15))=k2_relat_1(A_15) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_48])).
% 6.43/2.35  tff(c_7283, plain, (k1_tarski(k1_funct_1('#skF_6', '#skF_3'))=k2_relat_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_7276, c_28])).
% 6.43/2.35  tff(c_7333, plain, (k1_tarski(k1_funct_1('#skF_6', '#skF_3'))=k2_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_104, c_7283])).
% 6.43/2.35  tff(c_145, plain, (![A_59, B_60, C_61, D_62]: (k7_relset_1(A_59, B_60, C_61, D_62)=k9_relat_1(C_61, D_62) | ~m1_subset_1(C_61, k1_zfmisc_1(k2_zfmisc_1(A_59, B_60))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 6.43/2.35  tff(c_148, plain, (![D_62]: (k7_relset_1(k1_tarski('#skF_3'), '#skF_4', '#skF_6', D_62)=k9_relat_1('#skF_6', D_62))), inference(resolution, [status(thm)], [c_54, c_145])).
% 6.43/2.35  tff(c_50, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_3'), '#skF_4', '#skF_6', '#skF_5'), k1_tarski(k1_funct_1('#skF_6', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_100])).
% 6.43/2.35  tff(c_149, plain, (~r1_tarski(k9_relat_1('#skF_6', '#skF_5'), k1_tarski(k1_funct_1('#skF_6', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_148, c_50])).
% 6.43/2.35  tff(c_7338, plain, (~r1_tarski(k9_relat_1('#skF_6', '#skF_5'), k2_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_7333, c_149])).
% 6.43/2.35  tff(c_7407, plain, (~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_26, c_7338])).
% 6.43/2.35  tff(c_7411, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_104, c_7407])).
% 6.43/2.35  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.43/2.35  
% 6.43/2.35  Inference rules
% 6.43/2.35  ----------------------
% 6.43/2.35  #Ref     : 0
% 6.43/2.35  #Sup     : 1161
% 6.43/2.35  #Fact    : 44
% 6.43/2.35  #Define  : 0
% 6.43/2.35  #Split   : 5
% 6.43/2.35  #Chain   : 0
% 6.43/2.35  #Close   : 0
% 6.43/2.35  
% 6.43/2.35  Ordering : KBO
% 6.43/2.35  
% 6.43/2.35  Simplification rules
% 6.43/2.35  ----------------------
% 6.43/2.35  #Subsume      : 444
% 6.43/2.35  #Demod        : 162
% 6.43/2.35  #Tautology    : 399
% 6.43/2.35  #SimpNegUnit  : 4
% 6.43/2.35  #BackRed      : 7
% 6.43/2.35  
% 6.43/2.35  #Partial instantiations: 5460
% 6.43/2.35  #Strategies tried      : 1
% 6.43/2.35  
% 6.43/2.35  Timing (in seconds)
% 6.43/2.35  ----------------------
% 6.43/2.36  Preprocessing        : 0.34
% 6.43/2.36  Parsing              : 0.17
% 6.43/2.36  CNF conversion       : 0.02
% 6.43/2.36  Main loop            : 1.24
% 6.43/2.36  Inferencing          : 0.58
% 6.43/2.36  Reduction            : 0.27
% 6.43/2.36  Demodulation         : 0.19
% 6.43/2.36  BG Simplification    : 0.06
% 6.43/2.36  Subsumption          : 0.27
% 6.43/2.36  Abstraction          : 0.06
% 6.43/2.36  MUC search           : 0.00
% 6.43/2.36  Cooper               : 0.00
% 6.43/2.36  Total                : 1.61
% 6.43/2.36  Index Insertion      : 0.00
% 6.43/2.36  Index Deletion       : 0.00
% 6.43/2.36  Index Matching       : 0.00
% 6.43/2.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
