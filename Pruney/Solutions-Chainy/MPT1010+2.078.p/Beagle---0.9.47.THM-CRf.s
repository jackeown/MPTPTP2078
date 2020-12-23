%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:15 EST 2020

% Result     : Theorem 2.32s
% Output     : CNFRefutation 2.32s
% Verified   : 
% Statistics : Number of formulae       :   64 (  82 expanded)
%              Number of leaves         :   33 (  44 expanded)
%              Depth                    :    9
%              Number of atoms          :  103 ( 158 expanded)
%              Number of equality atoms :   38 (  53 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k4_xboole_0 > k4_tarski > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_108,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,k1_tarski(B))
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
       => ( r2_hidden(C,A)
         => k1_funct_1(D,C) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_2)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),B) = k1_tarski(A)
    <=> ~ r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l33_zfmisc_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),B) = k1_xboole_0
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l35_zfmisc_1)).

tff(f_79,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_funct_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_46,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,k1_tarski(D)))
    <=> ( r2_hidden(A,C)
        & B = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t129_zfmisc_1)).

tff(c_48,plain,(
    k1_funct_1('#skF_4','#skF_3') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_50,plain,(
    r2_hidden('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_52,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1',k1_tarski('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_89,plain,(
    ! [C_40,A_41,B_42] :
      ( v1_relat_1(C_40)
      | ~ m1_subset_1(C_40,k1_zfmisc_1(k2_zfmisc_1(A_41,B_42))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_93,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_89])).

tff(c_56,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_94,plain,(
    ! [A_43,B_44] :
      ( k4_xboole_0(k1_tarski(A_43),B_44) = k1_tarski(A_43)
      | r2_hidden(A_43,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_12,plain,(
    ! [A_9,B_10] :
      ( r2_hidden(A_9,B_10)
      | k4_xboole_0(k1_tarski(A_9),B_10) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_103,plain,(
    ! [A_43,B_44] :
      ( r2_hidden(A_43,B_44)
      | k1_tarski(A_43) != k1_xboole_0
      | r2_hidden(A_43,B_44) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_94,c_12])).

tff(c_137,plain,(
    ! [A_43,B_44] :
      ( k1_tarski(A_43) != k1_xboole_0
      | r2_hidden(A_43,B_44) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_103])).

tff(c_14,plain,(
    ! [A_9,B_10] :
      ( k4_xboole_0(k1_tarski(A_9),B_10) = k1_xboole_0
      | ~ r2_hidden(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_112,plain,(
    ! [A_45,B_46] :
      ( ~ r2_hidden(A_45,B_46)
      | k4_xboole_0(k1_tarski(A_45),B_46) != k1_tarski(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_155,plain,(
    ! [A_65,B_66] :
      ( ~ r2_hidden(A_65,B_66)
      | k1_tarski(A_65) != k1_xboole_0
      | ~ r2_hidden(A_65,B_66) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_112])).

tff(c_164,plain,(
    ! [A_67,B_68] :
      ( ~ r2_hidden(A_67,B_68)
      | k1_tarski(A_67) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_137,c_155])).

tff(c_171,plain,(
    ! [A_43] : k1_tarski(A_43) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_137,c_164])).

tff(c_54,plain,(
    v1_funct_2('#skF_4','#skF_1',k1_tarski('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_193,plain,(
    ! [A_80,B_81,C_82] :
      ( k1_relset_1(A_80,B_81,C_82) = k1_relat_1(C_82)
      | ~ m1_subset_1(C_82,k1_zfmisc_1(k2_zfmisc_1(A_80,B_81))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_197,plain,(
    k1_relset_1('#skF_1',k1_tarski('#skF_2'),'#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_193])).

tff(c_236,plain,(
    ! [B_101,A_102,C_103] :
      ( k1_xboole_0 = B_101
      | k1_relset_1(A_102,B_101,C_103) = A_102
      | ~ v1_funct_2(C_103,A_102,B_101)
      | ~ m1_subset_1(C_103,k1_zfmisc_1(k2_zfmisc_1(A_102,B_101))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_239,plain,
    ( k1_tarski('#skF_2') = k1_xboole_0
    | k1_relset_1('#skF_1',k1_tarski('#skF_2'),'#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1',k1_tarski('#skF_2')) ),
    inference(resolution,[status(thm)],[c_52,c_236])).

tff(c_242,plain,
    ( k1_tarski('#skF_2') = k1_xboole_0
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_197,c_239])).

tff(c_243,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_171,c_242])).

tff(c_205,plain,(
    ! [B_89,A_90] :
      ( r2_hidden(k4_tarski(B_89,k1_funct_1(A_90,B_89)),A_90)
      | ~ r2_hidden(B_89,k1_relat_1(A_90))
      | ~ v1_funct_1(A_90)
      | ~ v1_relat_1(A_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_22,plain,(
    ! [C_18,A_15,B_16] :
      ( r2_hidden(C_18,A_15)
      | ~ r2_hidden(C_18,B_16)
      | ~ m1_subset_1(B_16,k1_zfmisc_1(A_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_280,plain,(
    ! [B_110,A_111,A_112] :
      ( r2_hidden(k4_tarski(B_110,k1_funct_1(A_111,B_110)),A_112)
      | ~ m1_subset_1(A_111,k1_zfmisc_1(A_112))
      | ~ r2_hidden(B_110,k1_relat_1(A_111))
      | ~ v1_funct_1(A_111)
      | ~ v1_relat_1(A_111) ) ),
    inference(resolution,[status(thm)],[c_205,c_22])).

tff(c_18,plain,(
    ! [D_14,B_12,A_11,C_13] :
      ( D_14 = B_12
      | ~ r2_hidden(k4_tarski(A_11,B_12),k2_zfmisc_1(C_13,k1_tarski(D_14))) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_305,plain,(
    ! [A_117,B_118,D_119,C_120] :
      ( k1_funct_1(A_117,B_118) = D_119
      | ~ m1_subset_1(A_117,k1_zfmisc_1(k2_zfmisc_1(C_120,k1_tarski(D_119))))
      | ~ r2_hidden(B_118,k1_relat_1(A_117))
      | ~ v1_funct_1(A_117)
      | ~ v1_relat_1(A_117) ) ),
    inference(resolution,[status(thm)],[c_280,c_18])).

tff(c_307,plain,(
    ! [B_118] :
      ( k1_funct_1('#skF_4',B_118) = '#skF_2'
      | ~ r2_hidden(B_118,k1_relat_1('#skF_4'))
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_52,c_305])).

tff(c_311,plain,(
    ! [B_121] :
      ( k1_funct_1('#skF_4',B_121) = '#skF_2'
      | ~ r2_hidden(B_121,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_56,c_243,c_307])).

tff(c_325,plain,(
    k1_funct_1('#skF_4','#skF_3') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_50,c_311])).

tff(c_332,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_325])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.31  % Computer   : n014.cluster.edu
% 0.12/0.31  % Model      : x86_64 x86_64
% 0.12/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.31  % Memory     : 8042.1875MB
% 0.12/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.31  % CPULimit   : 60
% 0.12/0.31  % DateTime   : Tue Dec  1 12:56:22 EST 2020
% 0.12/0.31  % CPUTime    : 
% 0.12/0.32  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.32/1.40  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.32/1.40  
% 2.32/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.32/1.40  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k4_xboole_0 > k4_tarski > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.32/1.40  
% 2.32/1.40  %Foreground sorts:
% 2.32/1.40  
% 2.32/1.40  
% 2.32/1.40  %Background operators:
% 2.32/1.40  
% 2.32/1.40  
% 2.32/1.40  %Foreground operators:
% 2.32/1.40  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.32/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.32/1.40  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.32/1.40  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.32/1.40  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.32/1.40  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.32/1.40  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.32/1.40  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.32/1.40  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.32/1.40  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.32/1.40  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.32/1.40  tff('#skF_2', type, '#skF_2': $i).
% 2.32/1.40  tff('#skF_3', type, '#skF_3': $i).
% 2.32/1.40  tff('#skF_1', type, '#skF_1': $i).
% 2.32/1.40  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.32/1.40  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.32/1.40  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.32/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.32/1.40  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.32/1.40  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.32/1.40  tff('#skF_4', type, '#skF_4': $i).
% 2.32/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.32/1.40  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.32/1.40  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.32/1.40  
% 2.32/1.42  tff(f_108, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_funct_2)).
% 2.32/1.42  tff(f_75, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.32/1.42  tff(f_36, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_tarski(A)) <=> ~r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l33_zfmisc_1)).
% 2.32/1.42  tff(f_40, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_xboole_0) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l35_zfmisc_1)).
% 2.32/1.42  tff(f_79, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.32/1.42  tff(f_97, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 2.32/1.42  tff(f_71, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: ((r2_hidden(B, k1_relat_1(A)) => ((C = k1_funct_1(A, B)) <=> r2_hidden(k4_tarski(B, C), A))) & (~r2_hidden(B, k1_relat_1(A)) => ((C = k1_funct_1(A, B)) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_funct_1)).
% 2.32/1.42  tff(f_53, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 2.32/1.42  tff(f_46, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, k1_tarski(D))) <=> (r2_hidden(A, C) & (B = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t129_zfmisc_1)).
% 2.32/1.42  tff(c_48, plain, (k1_funct_1('#skF_4', '#skF_3')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.32/1.42  tff(c_50, plain, (r2_hidden('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.32/1.42  tff(c_52, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', k1_tarski('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.32/1.42  tff(c_89, plain, (![C_40, A_41, B_42]: (v1_relat_1(C_40) | ~m1_subset_1(C_40, k1_zfmisc_1(k2_zfmisc_1(A_41, B_42))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.32/1.42  tff(c_93, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_52, c_89])).
% 2.32/1.42  tff(c_56, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.32/1.42  tff(c_94, plain, (![A_43, B_44]: (k4_xboole_0(k1_tarski(A_43), B_44)=k1_tarski(A_43) | r2_hidden(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.32/1.42  tff(c_12, plain, (![A_9, B_10]: (r2_hidden(A_9, B_10) | k4_xboole_0(k1_tarski(A_9), B_10)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.32/1.42  tff(c_103, plain, (![A_43, B_44]: (r2_hidden(A_43, B_44) | k1_tarski(A_43)!=k1_xboole_0 | r2_hidden(A_43, B_44))), inference(superposition, [status(thm), theory('equality')], [c_94, c_12])).
% 2.32/1.42  tff(c_137, plain, (![A_43, B_44]: (k1_tarski(A_43)!=k1_xboole_0 | r2_hidden(A_43, B_44))), inference(factorization, [status(thm), theory('equality')], [c_103])).
% 2.32/1.42  tff(c_14, plain, (![A_9, B_10]: (k4_xboole_0(k1_tarski(A_9), B_10)=k1_xboole_0 | ~r2_hidden(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.32/1.42  tff(c_112, plain, (![A_45, B_46]: (~r2_hidden(A_45, B_46) | k4_xboole_0(k1_tarski(A_45), B_46)!=k1_tarski(A_45))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.32/1.42  tff(c_155, plain, (![A_65, B_66]: (~r2_hidden(A_65, B_66) | k1_tarski(A_65)!=k1_xboole_0 | ~r2_hidden(A_65, B_66))), inference(superposition, [status(thm), theory('equality')], [c_14, c_112])).
% 2.32/1.42  tff(c_164, plain, (![A_67, B_68]: (~r2_hidden(A_67, B_68) | k1_tarski(A_67)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_137, c_155])).
% 2.32/1.42  tff(c_171, plain, (![A_43]: (k1_tarski(A_43)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_137, c_164])).
% 2.32/1.42  tff(c_54, plain, (v1_funct_2('#skF_4', '#skF_1', k1_tarski('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.32/1.42  tff(c_193, plain, (![A_80, B_81, C_82]: (k1_relset_1(A_80, B_81, C_82)=k1_relat_1(C_82) | ~m1_subset_1(C_82, k1_zfmisc_1(k2_zfmisc_1(A_80, B_81))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.32/1.42  tff(c_197, plain, (k1_relset_1('#skF_1', k1_tarski('#skF_2'), '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_52, c_193])).
% 2.32/1.42  tff(c_236, plain, (![B_101, A_102, C_103]: (k1_xboole_0=B_101 | k1_relset_1(A_102, B_101, C_103)=A_102 | ~v1_funct_2(C_103, A_102, B_101) | ~m1_subset_1(C_103, k1_zfmisc_1(k2_zfmisc_1(A_102, B_101))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.32/1.42  tff(c_239, plain, (k1_tarski('#skF_2')=k1_xboole_0 | k1_relset_1('#skF_1', k1_tarski('#skF_2'), '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', k1_tarski('#skF_2'))), inference(resolution, [status(thm)], [c_52, c_236])).
% 2.32/1.42  tff(c_242, plain, (k1_tarski('#skF_2')=k1_xboole_0 | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_54, c_197, c_239])).
% 2.32/1.42  tff(c_243, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_171, c_242])).
% 2.32/1.42  tff(c_205, plain, (![B_89, A_90]: (r2_hidden(k4_tarski(B_89, k1_funct_1(A_90, B_89)), A_90) | ~r2_hidden(B_89, k1_relat_1(A_90)) | ~v1_funct_1(A_90) | ~v1_relat_1(A_90))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.32/1.42  tff(c_22, plain, (![C_18, A_15, B_16]: (r2_hidden(C_18, A_15) | ~r2_hidden(C_18, B_16) | ~m1_subset_1(B_16, k1_zfmisc_1(A_15)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.32/1.42  tff(c_280, plain, (![B_110, A_111, A_112]: (r2_hidden(k4_tarski(B_110, k1_funct_1(A_111, B_110)), A_112) | ~m1_subset_1(A_111, k1_zfmisc_1(A_112)) | ~r2_hidden(B_110, k1_relat_1(A_111)) | ~v1_funct_1(A_111) | ~v1_relat_1(A_111))), inference(resolution, [status(thm)], [c_205, c_22])).
% 2.32/1.42  tff(c_18, plain, (![D_14, B_12, A_11, C_13]: (D_14=B_12 | ~r2_hidden(k4_tarski(A_11, B_12), k2_zfmisc_1(C_13, k1_tarski(D_14))))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.32/1.42  tff(c_305, plain, (![A_117, B_118, D_119, C_120]: (k1_funct_1(A_117, B_118)=D_119 | ~m1_subset_1(A_117, k1_zfmisc_1(k2_zfmisc_1(C_120, k1_tarski(D_119)))) | ~r2_hidden(B_118, k1_relat_1(A_117)) | ~v1_funct_1(A_117) | ~v1_relat_1(A_117))), inference(resolution, [status(thm)], [c_280, c_18])).
% 2.32/1.42  tff(c_307, plain, (![B_118]: (k1_funct_1('#skF_4', B_118)='#skF_2' | ~r2_hidden(B_118, k1_relat_1('#skF_4')) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_52, c_305])).
% 2.32/1.42  tff(c_311, plain, (![B_121]: (k1_funct_1('#skF_4', B_121)='#skF_2' | ~r2_hidden(B_121, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_93, c_56, c_243, c_307])).
% 2.32/1.42  tff(c_325, plain, (k1_funct_1('#skF_4', '#skF_3')='#skF_2'), inference(resolution, [status(thm)], [c_50, c_311])).
% 2.32/1.42  tff(c_332, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_325])).
% 2.32/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.32/1.42  
% 2.32/1.42  Inference rules
% 2.32/1.42  ----------------------
% 2.32/1.42  #Ref     : 0
% 2.32/1.42  #Sup     : 57
% 2.32/1.42  #Fact    : 2
% 2.32/1.42  #Define  : 0
% 2.32/1.42  #Split   : 1
% 2.32/1.42  #Chain   : 0
% 2.32/1.42  #Close   : 0
% 2.32/1.42  
% 2.32/1.42  Ordering : KBO
% 2.32/1.42  
% 2.32/1.42  Simplification rules
% 2.32/1.42  ----------------------
% 2.32/1.42  #Subsume      : 12
% 2.32/1.42  #Demod        : 16
% 2.32/1.42  #Tautology    : 25
% 2.32/1.42  #SimpNegUnit  : 3
% 2.32/1.42  #BackRed      : 1
% 2.32/1.42  
% 2.32/1.42  #Partial instantiations: 0
% 2.32/1.42  #Strategies tried      : 1
% 2.32/1.42  
% 2.32/1.42  Timing (in seconds)
% 2.32/1.42  ----------------------
% 2.32/1.42  Preprocessing        : 0.40
% 2.32/1.42  Parsing              : 0.20
% 2.32/1.42  CNF conversion       : 0.02
% 2.32/1.42  Main loop            : 0.23
% 2.32/1.42  Inferencing          : 0.08
% 2.32/1.42  Reduction            : 0.06
% 2.32/1.42  Demodulation         : 0.05
% 2.32/1.42  BG Simplification    : 0.02
% 2.32/1.42  Subsumption          : 0.05
% 2.32/1.42  Abstraction          : 0.01
% 2.32/1.42  MUC search           : 0.00
% 2.32/1.42  Cooper               : 0.00
% 2.32/1.42  Total                : 0.66
% 2.32/1.42  Index Insertion      : 0.00
% 2.32/1.42  Index Deletion       : 0.00
% 2.32/1.42  Index Matching       : 0.00
% 2.32/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
