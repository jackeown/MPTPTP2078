%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:15 EST 2020

% Result     : Theorem 3.02s
% Output     : CNFRefutation 3.20s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 102 expanded)
%              Number of leaves         :   35 (  52 expanded)
%              Depth                    :    7
%              Number of atoms          :   93 ( 214 expanded)
%              Number of equality atoms :   35 (  79 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_31,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_108,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,k1_tarski(B))
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
       => ( r2_hidden(C,A)
         => k1_funct_1(D,C) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_2)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_79,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_97,axiom,(
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

tff(f_71,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B,C] :
          ( ( r2_hidden(B,k1_relat_1(A))
           => ( C = k1_funct_1(A,B)
            <=> r2_hidden(k4_tarski(B,C),A) ) )
          & ( ~ r2_hidden(B,k1_relat_1(A))
           => ( C = k1_funct_1(A,B)
            <=> C = k1_xboole_0 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_funct_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_43,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,k1_tarski(D)))
    <=> ( r2_hidden(A,C)
        & B = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t129_zfmisc_1)).

tff(f_46,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(c_4,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_66,plain,(
    ! [A_38,B_39] :
      ( k2_xboole_0(A_38,B_39) = B_39
      | ~ r1_tarski(A_38,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_70,plain,(
    ! [A_3] : k2_xboole_0(k1_xboole_0,A_3) = A_3 ),
    inference(resolution,[status(thm)],[c_4,c_66])).

tff(c_46,plain,(
    k1_funct_1('#skF_4','#skF_3') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_48,plain,(
    r2_hidden('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_50,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1',k1_tarski('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_89,plain,(
    ! [C_43,A_44,B_45] :
      ( v1_relat_1(C_43)
      | ~ m1_subset_1(C_43,k1_zfmisc_1(k2_zfmisc_1(A_44,B_45))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_93,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_89])).

tff(c_54,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_52,plain,(
    v1_funct_2('#skF_4','#skF_1',k1_tarski('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_123,plain,(
    ! [A_64,B_65,C_66] :
      ( k1_relset_1(A_64,B_65,C_66) = k1_relat_1(C_66)
      | ~ m1_subset_1(C_66,k1_zfmisc_1(k2_zfmisc_1(A_64,B_65))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_127,plain,(
    k1_relset_1('#skF_1',k1_tarski('#skF_2'),'#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_123])).

tff(c_171,plain,(
    ! [B_88,A_89,C_90] :
      ( k1_xboole_0 = B_88
      | k1_relset_1(A_89,B_88,C_90) = A_89
      | ~ v1_funct_2(C_90,A_89,B_88)
      | ~ m1_subset_1(C_90,k1_zfmisc_1(k2_zfmisc_1(A_89,B_88))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_174,plain,
    ( k1_tarski('#skF_2') = k1_xboole_0
    | k1_relset_1('#skF_1',k1_tarski('#skF_2'),'#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1',k1_tarski('#skF_2')) ),
    inference(resolution,[status(thm)],[c_50,c_171])).

tff(c_177,plain,
    ( k1_tarski('#skF_2') = k1_xboole_0
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_127,c_174])).

tff(c_178,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_177])).

tff(c_140,plain,(
    ! [B_76,A_77] :
      ( r2_hidden(k4_tarski(B_76,k1_funct_1(A_77,B_76)),A_77)
      | ~ r2_hidden(B_76,k1_relat_1(A_77))
      | ~ v1_funct_1(A_77)
      | ~ v1_relat_1(A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_20,plain,(
    ! [C_19,A_16,B_17] :
      ( r2_hidden(C_19,A_16)
      | ~ r2_hidden(C_19,B_17)
      | ~ m1_subset_1(B_17,k1_zfmisc_1(A_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_215,plain,(
    ! [B_97,A_98,A_99] :
      ( r2_hidden(k4_tarski(B_97,k1_funct_1(A_98,B_97)),A_99)
      | ~ m1_subset_1(A_98,k1_zfmisc_1(A_99))
      | ~ r2_hidden(B_97,k1_relat_1(A_98))
      | ~ v1_funct_1(A_98)
      | ~ v1_relat_1(A_98) ) ),
    inference(resolution,[status(thm)],[c_140,c_20])).

tff(c_14,plain,(
    ! [D_13,B_11,A_10,C_12] :
      ( D_13 = B_11
      | ~ r2_hidden(k4_tarski(A_10,B_11),k2_zfmisc_1(C_12,k1_tarski(D_13))) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_239,plain,(
    ! [A_104,B_105,D_106,C_107] :
      ( k1_funct_1(A_104,B_105) = D_106
      | ~ m1_subset_1(A_104,k1_zfmisc_1(k2_zfmisc_1(C_107,k1_tarski(D_106))))
      | ~ r2_hidden(B_105,k1_relat_1(A_104))
      | ~ v1_funct_1(A_104)
      | ~ v1_relat_1(A_104) ) ),
    inference(resolution,[status(thm)],[c_215,c_14])).

tff(c_241,plain,(
    ! [B_105] :
      ( k1_funct_1('#skF_4',B_105) = '#skF_2'
      | ~ r2_hidden(B_105,k1_relat_1('#skF_4'))
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_50,c_239])).

tff(c_245,plain,(
    ! [B_108] :
      ( k1_funct_1('#skF_4',B_108) = '#skF_2'
      | ~ r2_hidden(B_108,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_54,c_178,c_241])).

tff(c_259,plain,(
    k1_funct_1('#skF_4','#skF_3') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_48,c_245])).

tff(c_266,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_259])).

tff(c_267,plain,(
    k1_tarski('#skF_2') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_177])).

tff(c_18,plain,(
    ! [A_14,B_15] : k2_xboole_0(k1_tarski(A_14),B_15) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_284,plain,(
    ! [B_15] : k2_xboole_0(k1_xboole_0,B_15) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_267,c_18])).

tff(c_287,plain,(
    ! [B_15] : k1_xboole_0 != B_15 ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_284])).

tff(c_298,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_287,c_267])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:00:35 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.02/1.80  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.13/1.80  
% 3.13/1.80  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.13/1.81  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.13/1.81  
% 3.13/1.81  %Foreground sorts:
% 3.13/1.81  
% 3.13/1.81  
% 3.13/1.81  %Background operators:
% 3.13/1.81  
% 3.13/1.81  
% 3.13/1.81  %Foreground operators:
% 3.13/1.81  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.13/1.81  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.13/1.81  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.13/1.81  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.13/1.81  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.13/1.81  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.13/1.81  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.13/1.81  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.13/1.81  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.13/1.81  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.13/1.81  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.13/1.81  tff('#skF_2', type, '#skF_2': $i).
% 3.13/1.81  tff('#skF_3', type, '#skF_3': $i).
% 3.13/1.81  tff('#skF_1', type, '#skF_1': $i).
% 3.13/1.81  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.13/1.81  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.13/1.81  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.13/1.81  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.13/1.81  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.13/1.81  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.13/1.81  tff('#skF_4', type, '#skF_4': $i).
% 3.13/1.81  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.13/1.81  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.13/1.81  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.13/1.81  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.13/1.81  
% 3.20/1.83  tff(f_31, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.20/1.83  tff(f_29, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 3.20/1.83  tff(f_108, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_funct_2)).
% 3.20/1.83  tff(f_75, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.20/1.83  tff(f_79, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.20/1.83  tff(f_97, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 3.20/1.83  tff(f_71, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: ((r2_hidden(B, k1_relat_1(A)) => ((C = k1_funct_1(A, B)) <=> r2_hidden(k4_tarski(B, C), A))) & (~r2_hidden(B, k1_relat_1(A)) => ((C = k1_funct_1(A, B)) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_funct_1)).
% 3.20/1.83  tff(f_53, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 3.20/1.83  tff(f_43, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, k1_tarski(D))) <=> (r2_hidden(A, C) & (B = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t129_zfmisc_1)).
% 3.20/1.83  tff(f_46, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 3.20/1.83  tff(c_4, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.20/1.83  tff(c_66, plain, (![A_38, B_39]: (k2_xboole_0(A_38, B_39)=B_39 | ~r1_tarski(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.20/1.83  tff(c_70, plain, (![A_3]: (k2_xboole_0(k1_xboole_0, A_3)=A_3)), inference(resolution, [status(thm)], [c_4, c_66])).
% 3.20/1.83  tff(c_46, plain, (k1_funct_1('#skF_4', '#skF_3')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.20/1.83  tff(c_48, plain, (r2_hidden('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.20/1.83  tff(c_50, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', k1_tarski('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.20/1.83  tff(c_89, plain, (![C_43, A_44, B_45]: (v1_relat_1(C_43) | ~m1_subset_1(C_43, k1_zfmisc_1(k2_zfmisc_1(A_44, B_45))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.20/1.83  tff(c_93, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_50, c_89])).
% 3.20/1.83  tff(c_54, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.20/1.83  tff(c_52, plain, (v1_funct_2('#skF_4', '#skF_1', k1_tarski('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.20/1.83  tff(c_123, plain, (![A_64, B_65, C_66]: (k1_relset_1(A_64, B_65, C_66)=k1_relat_1(C_66) | ~m1_subset_1(C_66, k1_zfmisc_1(k2_zfmisc_1(A_64, B_65))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.20/1.83  tff(c_127, plain, (k1_relset_1('#skF_1', k1_tarski('#skF_2'), '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_50, c_123])).
% 3.20/1.83  tff(c_171, plain, (![B_88, A_89, C_90]: (k1_xboole_0=B_88 | k1_relset_1(A_89, B_88, C_90)=A_89 | ~v1_funct_2(C_90, A_89, B_88) | ~m1_subset_1(C_90, k1_zfmisc_1(k2_zfmisc_1(A_89, B_88))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.20/1.83  tff(c_174, plain, (k1_tarski('#skF_2')=k1_xboole_0 | k1_relset_1('#skF_1', k1_tarski('#skF_2'), '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', k1_tarski('#skF_2'))), inference(resolution, [status(thm)], [c_50, c_171])).
% 3.20/1.83  tff(c_177, plain, (k1_tarski('#skF_2')=k1_xboole_0 | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_127, c_174])).
% 3.20/1.83  tff(c_178, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(splitLeft, [status(thm)], [c_177])).
% 3.20/1.83  tff(c_140, plain, (![B_76, A_77]: (r2_hidden(k4_tarski(B_76, k1_funct_1(A_77, B_76)), A_77) | ~r2_hidden(B_76, k1_relat_1(A_77)) | ~v1_funct_1(A_77) | ~v1_relat_1(A_77))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.20/1.83  tff(c_20, plain, (![C_19, A_16, B_17]: (r2_hidden(C_19, A_16) | ~r2_hidden(C_19, B_17) | ~m1_subset_1(B_17, k1_zfmisc_1(A_16)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.20/1.83  tff(c_215, plain, (![B_97, A_98, A_99]: (r2_hidden(k4_tarski(B_97, k1_funct_1(A_98, B_97)), A_99) | ~m1_subset_1(A_98, k1_zfmisc_1(A_99)) | ~r2_hidden(B_97, k1_relat_1(A_98)) | ~v1_funct_1(A_98) | ~v1_relat_1(A_98))), inference(resolution, [status(thm)], [c_140, c_20])).
% 3.20/1.83  tff(c_14, plain, (![D_13, B_11, A_10, C_12]: (D_13=B_11 | ~r2_hidden(k4_tarski(A_10, B_11), k2_zfmisc_1(C_12, k1_tarski(D_13))))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.20/1.83  tff(c_239, plain, (![A_104, B_105, D_106, C_107]: (k1_funct_1(A_104, B_105)=D_106 | ~m1_subset_1(A_104, k1_zfmisc_1(k2_zfmisc_1(C_107, k1_tarski(D_106)))) | ~r2_hidden(B_105, k1_relat_1(A_104)) | ~v1_funct_1(A_104) | ~v1_relat_1(A_104))), inference(resolution, [status(thm)], [c_215, c_14])).
% 3.20/1.83  tff(c_241, plain, (![B_105]: (k1_funct_1('#skF_4', B_105)='#skF_2' | ~r2_hidden(B_105, k1_relat_1('#skF_4')) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_50, c_239])).
% 3.20/1.83  tff(c_245, plain, (![B_108]: (k1_funct_1('#skF_4', B_108)='#skF_2' | ~r2_hidden(B_108, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_93, c_54, c_178, c_241])).
% 3.20/1.83  tff(c_259, plain, (k1_funct_1('#skF_4', '#skF_3')='#skF_2'), inference(resolution, [status(thm)], [c_48, c_245])).
% 3.20/1.83  tff(c_266, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_259])).
% 3.20/1.83  tff(c_267, plain, (k1_tarski('#skF_2')=k1_xboole_0), inference(splitRight, [status(thm)], [c_177])).
% 3.20/1.83  tff(c_18, plain, (![A_14, B_15]: (k2_xboole_0(k1_tarski(A_14), B_15)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.20/1.83  tff(c_284, plain, (![B_15]: (k2_xboole_0(k1_xboole_0, B_15)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_267, c_18])).
% 3.20/1.83  tff(c_287, plain, (![B_15]: (k1_xboole_0!=B_15)), inference(demodulation, [status(thm), theory('equality')], [c_70, c_284])).
% 3.20/1.83  tff(c_298, plain, $false, inference(negUnitSimplification, [status(thm)], [c_287, c_267])).
% 3.20/1.83  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.20/1.83  
% 3.20/1.83  Inference rules
% 3.20/1.83  ----------------------
% 3.20/1.83  #Ref     : 0
% 3.20/1.83  #Sup     : 51
% 3.20/1.83  #Fact    : 0
% 3.20/1.83  #Define  : 0
% 3.20/1.83  #Split   : 2
% 3.20/1.83  #Chain   : 0
% 3.20/1.83  #Close   : 0
% 3.20/1.83  
% 3.20/1.83  Ordering : KBO
% 3.20/1.83  
% 3.20/1.83  Simplification rules
% 3.20/1.83  ----------------------
% 3.20/1.83  #Subsume      : 5
% 3.20/1.83  #Demod        : 19
% 3.20/1.83  #Tautology    : 21
% 3.20/1.83  #SimpNegUnit  : 9
% 3.20/1.83  #BackRed      : 12
% 3.20/1.83  
% 3.20/1.83  #Partial instantiations: 0
% 3.20/1.83  #Strategies tried      : 1
% 3.20/1.83  
% 3.20/1.83  Timing (in seconds)
% 3.20/1.83  ----------------------
% 3.20/1.83  Preprocessing        : 0.52
% 3.20/1.83  Parsing              : 0.27
% 3.20/1.83  CNF conversion       : 0.04
% 3.20/1.83  Main loop            : 0.38
% 3.20/1.83  Inferencing          : 0.14
% 3.20/1.83  Reduction            : 0.11
% 3.20/1.83  Demodulation         : 0.07
% 3.20/1.83  BG Simplification    : 0.03
% 3.20/1.83  Subsumption          : 0.07
% 3.20/1.83  Abstraction          : 0.02
% 3.20/1.83  MUC search           : 0.00
% 3.20/1.83  Cooper               : 0.00
% 3.20/1.83  Total                : 0.96
% 3.20/1.83  Index Insertion      : 0.00
% 3.20/1.84  Index Deletion       : 0.00
% 3.20/1.84  Index Matching       : 0.00
% 3.20/1.84  BG Taut test         : 0.00
%------------------------------------------------------------------------------
