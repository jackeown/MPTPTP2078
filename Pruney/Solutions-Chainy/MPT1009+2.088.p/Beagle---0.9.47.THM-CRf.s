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
% DateTime   : Thu Dec  3 10:14:54 EST 2020

% Result     : Theorem 3.63s
% Output     : CNFRefutation 3.63s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 113 expanded)
%              Number of leaves         :   39 (  58 expanded)
%              Depth                    :   11
%              Number of atoms          :   88 ( 207 expanded)
%              Number of equality atoms :   37 (  68 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k1_relset_1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4

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

tff(f_101,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,k1_tarski(A),B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r1_tarski(k7_relset_1(k1_tarski(A),B,D,C),k1_tarski(k1_funct_1(D,A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_2)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k9_relat_1(B,A),k2_relat_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_relat_1)).

tff(f_67,axiom,(
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

tff(f_43,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] : k11_relat_1(A,B) = k9_relat_1(A,k1_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_relat_1)).

tff(f_51,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

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

tff(f_59,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => k11_relat_1(B,A) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_funct_1)).

tff(f_71,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(c_54,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_3'),'#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_100,plain,(
    ! [C_42,A_43,B_44] :
      ( v1_relat_1(C_42)
      | ~ m1_subset_1(C_42,k1_zfmisc_1(k2_zfmisc_1(A_43,B_44))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_104,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_54,c_100])).

tff(c_26,plain,(
    ! [B_14,A_13] :
      ( r1_tarski(k9_relat_1(B_14,A_13),k2_relat_1(B_14))
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_52,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_56,plain,(
    v1_funct_2('#skF_6',k1_tarski('#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_140,plain,(
    ! [A_56,B_57,C_58] :
      ( k1_relset_1(A_56,B_57,C_58) = k1_relat_1(C_58)
      | ~ m1_subset_1(C_58,k1_zfmisc_1(k2_zfmisc_1(A_56,B_57))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_144,plain,(
    k1_relset_1(k1_tarski('#skF_3'),'#skF_4','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_54,c_140])).

tff(c_177,plain,(
    ! [B_84,A_85,C_86] :
      ( k1_xboole_0 = B_84
      | k1_relset_1(A_85,B_84,C_86) = A_85
      | ~ v1_funct_2(C_86,A_85,B_84)
      | ~ m1_subset_1(C_86,k1_zfmisc_1(k2_zfmisc_1(A_85,B_84))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_180,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1(k1_tarski('#skF_3'),'#skF_4','#skF_6') = k1_tarski('#skF_3')
    | ~ v1_funct_2('#skF_6',k1_tarski('#skF_3'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_177])).

tff(c_183,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_tarski('#skF_3') = k1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_144,c_180])).

tff(c_184,plain,(
    k1_tarski('#skF_3') = k1_relat_1('#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_183])).

tff(c_24,plain,(
    ! [A_10,B_12] :
      ( k9_relat_1(A_10,k1_tarski(B_12)) = k11_relat_1(A_10,B_12)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1379,plain,(
    ! [A_2755] :
      ( k9_relat_1(A_2755,k1_relat_1('#skF_6')) = k11_relat_1(A_2755,'#skF_3')
      | ~ v1_relat_1(A_2755) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_184,c_24])).

tff(c_28,plain,(
    ! [A_15] :
      ( k9_relat_1(A_15,k1_relat_1(A_15)) = k2_relat_1(A_15)
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1389,plain,
    ( k11_relat_1('#skF_6','#skF_3') = k2_relat_1('#skF_6')
    | ~ v1_relat_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_1379,c_28])).

tff(c_1401,plain,(
    k11_relat_1('#skF_6','#skF_3') = k2_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_104,c_1389])).

tff(c_58,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_20,plain,(
    ! [A_7] : k2_tarski(A_7,A_7) = k1_tarski(A_7) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_68,plain,(
    ! [D_32,B_33] : r2_hidden(D_32,k2_tarski(D_32,B_33)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_71,plain,(
    ! [A_7] : r2_hidden(A_7,k1_tarski(A_7)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_68])).

tff(c_680,plain,(
    r2_hidden('#skF_3',k1_relat_1('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_184,c_71])).

tff(c_30,plain,(
    ! [B_17,A_16] :
      ( k1_tarski(k1_funct_1(B_17,A_16)) = k11_relat_1(B_17,A_16)
      | ~ r2_hidden(A_16,k1_relat_1(B_17))
      | ~ v1_funct_1(B_17)
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_686,plain,
    ( k1_tarski(k1_funct_1('#skF_6','#skF_3')) = k11_relat_1('#skF_6','#skF_3')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_680,c_30])).

tff(c_689,plain,(
    k1_tarski(k1_funct_1('#skF_6','#skF_3')) = k11_relat_1('#skF_6','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_58,c_686])).

tff(c_149,plain,(
    ! [A_59,B_60,C_61,D_62] :
      ( k7_relset_1(A_59,B_60,C_61,D_62) = k9_relat_1(C_61,D_62)
      | ~ m1_subset_1(C_61,k1_zfmisc_1(k2_zfmisc_1(A_59,B_60))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_152,plain,(
    ! [D_62] : k7_relset_1(k1_tarski('#skF_3'),'#skF_4','#skF_6',D_62) = k9_relat_1('#skF_6',D_62) ),
    inference(resolution,[status(thm)],[c_54,c_149])).

tff(c_50,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski('#skF_3'),'#skF_4','#skF_6','#skF_5'),k1_tarski(k1_funct_1('#skF_6','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_153,plain,(
    ~ r1_tarski(k9_relat_1('#skF_6','#skF_5'),k1_tarski(k1_funct_1('#skF_6','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_50])).

tff(c_724,plain,(
    ~ r1_tarski(k9_relat_1('#skF_6','#skF_5'),k11_relat_1('#skF_6','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_689,c_153])).

tff(c_1406,plain,(
    ~ r1_tarski(k9_relat_1('#skF_6','#skF_5'),k2_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1401,c_724])).

tff(c_1422,plain,(
    ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_26,c_1406])).

tff(c_1426,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_1422])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:22:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.63/1.54  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.63/1.54  
% 3.63/1.54  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.63/1.55  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k1_relset_1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4
% 3.63/1.55  
% 3.63/1.55  %Foreground sorts:
% 3.63/1.55  
% 3.63/1.55  
% 3.63/1.55  %Background operators:
% 3.63/1.55  
% 3.63/1.55  
% 3.63/1.55  %Foreground operators:
% 3.63/1.55  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.63/1.55  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.63/1.55  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.63/1.55  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.63/1.55  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.63/1.55  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.63/1.55  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.63/1.55  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.63/1.55  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 3.63/1.55  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.63/1.55  tff('#skF_5', type, '#skF_5': $i).
% 3.63/1.55  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.63/1.55  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 3.63/1.55  tff('#skF_6', type, '#skF_6': $i).
% 3.63/1.55  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.63/1.55  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.63/1.55  tff('#skF_3', type, '#skF_3': $i).
% 3.63/1.55  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.63/1.55  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.63/1.55  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.63/1.55  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.63/1.55  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.63/1.55  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.63/1.55  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.63/1.55  tff('#skF_4', type, '#skF_4': $i).
% 3.63/1.55  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.63/1.55  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.63/1.55  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.63/1.55  
% 3.63/1.56  tff(f_101, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, k1_tarski(A), B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r1_tarski(k7_relset_1(k1_tarski(A), B, D, C), k1_tarski(k1_funct_1(D, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_funct_2)).
% 3.63/1.56  tff(f_63, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.63/1.56  tff(f_47, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k9_relat_1(B, A), k2_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t144_relat_1)).
% 3.63/1.56  tff(f_67, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.63/1.56  tff(f_89, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 3.63/1.56  tff(f_43, axiom, (![A]: (v1_relat_1(A) => (![B]: (k11_relat_1(A, B) = k9_relat_1(A, k1_tarski(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d16_relat_1)).
% 3.63/1.56  tff(f_51, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_relat_1)).
% 3.63/1.56  tff(f_36, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 3.63/1.56  tff(f_34, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 3.63/1.56  tff(f_59, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => (k11_relat_1(B, A) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t117_funct_1)).
% 3.63/1.56  tff(f_71, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 3.63/1.56  tff(c_54, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_3'), '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.63/1.56  tff(c_100, plain, (![C_42, A_43, B_44]: (v1_relat_1(C_42) | ~m1_subset_1(C_42, k1_zfmisc_1(k2_zfmisc_1(A_43, B_44))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.63/1.56  tff(c_104, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_54, c_100])).
% 3.63/1.56  tff(c_26, plain, (![B_14, A_13]: (r1_tarski(k9_relat_1(B_14, A_13), k2_relat_1(B_14)) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.63/1.56  tff(c_52, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.63/1.56  tff(c_56, plain, (v1_funct_2('#skF_6', k1_tarski('#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.63/1.56  tff(c_140, plain, (![A_56, B_57, C_58]: (k1_relset_1(A_56, B_57, C_58)=k1_relat_1(C_58) | ~m1_subset_1(C_58, k1_zfmisc_1(k2_zfmisc_1(A_56, B_57))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.63/1.56  tff(c_144, plain, (k1_relset_1(k1_tarski('#skF_3'), '#skF_4', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_54, c_140])).
% 3.63/1.56  tff(c_177, plain, (![B_84, A_85, C_86]: (k1_xboole_0=B_84 | k1_relset_1(A_85, B_84, C_86)=A_85 | ~v1_funct_2(C_86, A_85, B_84) | ~m1_subset_1(C_86, k1_zfmisc_1(k2_zfmisc_1(A_85, B_84))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.63/1.56  tff(c_180, plain, (k1_xboole_0='#skF_4' | k1_relset_1(k1_tarski('#skF_3'), '#skF_4', '#skF_6')=k1_tarski('#skF_3') | ~v1_funct_2('#skF_6', k1_tarski('#skF_3'), '#skF_4')), inference(resolution, [status(thm)], [c_54, c_177])).
% 3.63/1.56  tff(c_183, plain, (k1_xboole_0='#skF_4' | k1_tarski('#skF_3')=k1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_144, c_180])).
% 3.63/1.56  tff(c_184, plain, (k1_tarski('#skF_3')=k1_relat_1('#skF_6')), inference(negUnitSimplification, [status(thm)], [c_52, c_183])).
% 3.63/1.56  tff(c_24, plain, (![A_10, B_12]: (k9_relat_1(A_10, k1_tarski(B_12))=k11_relat_1(A_10, B_12) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.63/1.56  tff(c_1379, plain, (![A_2755]: (k9_relat_1(A_2755, k1_relat_1('#skF_6'))=k11_relat_1(A_2755, '#skF_3') | ~v1_relat_1(A_2755))), inference(superposition, [status(thm), theory('equality')], [c_184, c_24])).
% 3.63/1.56  tff(c_28, plain, (![A_15]: (k9_relat_1(A_15, k1_relat_1(A_15))=k2_relat_1(A_15) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.63/1.56  tff(c_1389, plain, (k11_relat_1('#skF_6', '#skF_3')=k2_relat_1('#skF_6') | ~v1_relat_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_1379, c_28])).
% 3.63/1.56  tff(c_1401, plain, (k11_relat_1('#skF_6', '#skF_3')=k2_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_104, c_104, c_1389])).
% 3.63/1.56  tff(c_58, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.63/1.56  tff(c_20, plain, (![A_7]: (k2_tarski(A_7, A_7)=k1_tarski(A_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.63/1.56  tff(c_68, plain, (![D_32, B_33]: (r2_hidden(D_32, k2_tarski(D_32, B_33)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.63/1.56  tff(c_71, plain, (![A_7]: (r2_hidden(A_7, k1_tarski(A_7)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_68])).
% 3.63/1.56  tff(c_680, plain, (r2_hidden('#skF_3', k1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_184, c_71])).
% 3.63/1.56  tff(c_30, plain, (![B_17, A_16]: (k1_tarski(k1_funct_1(B_17, A_16))=k11_relat_1(B_17, A_16) | ~r2_hidden(A_16, k1_relat_1(B_17)) | ~v1_funct_1(B_17) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.63/1.56  tff(c_686, plain, (k1_tarski(k1_funct_1('#skF_6', '#skF_3'))=k11_relat_1('#skF_6', '#skF_3') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_680, c_30])).
% 3.63/1.56  tff(c_689, plain, (k1_tarski(k1_funct_1('#skF_6', '#skF_3'))=k11_relat_1('#skF_6', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_104, c_58, c_686])).
% 3.63/1.56  tff(c_149, plain, (![A_59, B_60, C_61, D_62]: (k7_relset_1(A_59, B_60, C_61, D_62)=k9_relat_1(C_61, D_62) | ~m1_subset_1(C_61, k1_zfmisc_1(k2_zfmisc_1(A_59, B_60))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.63/1.56  tff(c_152, plain, (![D_62]: (k7_relset_1(k1_tarski('#skF_3'), '#skF_4', '#skF_6', D_62)=k9_relat_1('#skF_6', D_62))), inference(resolution, [status(thm)], [c_54, c_149])).
% 3.63/1.56  tff(c_50, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_3'), '#skF_4', '#skF_6', '#skF_5'), k1_tarski(k1_funct_1('#skF_6', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.63/1.56  tff(c_153, plain, (~r1_tarski(k9_relat_1('#skF_6', '#skF_5'), k1_tarski(k1_funct_1('#skF_6', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_152, c_50])).
% 3.63/1.56  tff(c_724, plain, (~r1_tarski(k9_relat_1('#skF_6', '#skF_5'), k11_relat_1('#skF_6', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_689, c_153])).
% 3.63/1.56  tff(c_1406, plain, (~r1_tarski(k9_relat_1('#skF_6', '#skF_5'), k2_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_1401, c_724])).
% 3.63/1.56  tff(c_1422, plain, (~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_26, c_1406])).
% 3.63/1.56  tff(c_1426, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_104, c_1422])).
% 3.63/1.56  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.63/1.56  
% 3.63/1.56  Inference rules
% 3.63/1.56  ----------------------
% 3.63/1.56  #Ref     : 0
% 3.63/1.56  #Sup     : 155
% 3.63/1.56  #Fact    : 4
% 3.63/1.56  #Define  : 0
% 3.63/1.56  #Split   : 0
% 3.63/1.56  #Chain   : 0
% 3.63/1.56  #Close   : 0
% 3.63/1.56  
% 3.63/1.56  Ordering : KBO
% 3.63/1.56  
% 3.63/1.56  Simplification rules
% 3.63/1.56  ----------------------
% 3.63/1.56  #Subsume      : 13
% 3.63/1.56  #Demod        : 34
% 3.63/1.56  #Tautology    : 48
% 3.63/1.56  #SimpNegUnit  : 4
% 3.63/1.56  #BackRed      : 9
% 3.63/1.56  
% 3.63/1.56  #Partial instantiations: 1805
% 3.63/1.56  #Strategies tried      : 1
% 3.63/1.56  
% 3.63/1.56  Timing (in seconds)
% 3.63/1.56  ----------------------
% 3.63/1.56  Preprocessing        : 0.35
% 3.63/1.56  Parsing              : 0.18
% 3.63/1.56  CNF conversion       : 0.02
% 3.63/1.56  Main loop            : 0.44
% 3.63/1.57  Inferencing          : 0.25
% 3.63/1.57  Reduction            : 0.09
% 3.63/1.57  Demodulation         : 0.07
% 3.63/1.57  BG Simplification    : 0.03
% 3.63/1.57  Subsumption          : 0.05
% 3.63/1.57  Abstraction          : 0.02
% 3.63/1.57  MUC search           : 0.00
% 3.63/1.57  Cooper               : 0.00
% 3.63/1.57  Total                : 0.83
% 3.63/1.57  Index Insertion      : 0.00
% 3.63/1.57  Index Deletion       : 0.00
% 3.63/1.57  Index Matching       : 0.00
% 3.63/1.57  BG Taut test         : 0.00
%------------------------------------------------------------------------------
