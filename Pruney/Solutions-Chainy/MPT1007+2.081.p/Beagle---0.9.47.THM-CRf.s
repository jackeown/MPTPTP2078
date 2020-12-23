%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:22 EST 2020

% Result     : Theorem 8.11s
% Output     : CNFRefutation 8.11s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 105 expanded)
%              Number of leaves         :   33 (  52 expanded)
%              Depth                    :    9
%              Number of atoms          :  101 ( 235 expanded)
%              Number of equality atoms :   27 (  76 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4

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

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff(f_112,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_tarski(A),B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r2_hidden(k1_funct_1(C,A),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_2)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_100,axiom,(
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

tff(f_60,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_58,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_78,axiom,(
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

tff(f_51,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_44,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(k1_tarski(C),D))
    <=> ( A = C
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t128_zfmisc_1)).

tff(c_60,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_64,plain,(
    v1_funct_2('#skF_5',k1_tarski('#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_62,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_3'),'#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_162,plain,(
    ! [A_76,B_77,C_78] :
      ( k1_relset_1(A_76,B_77,C_78) = k1_relat_1(C_78)
      | ~ m1_subset_1(C_78,k1_zfmisc_1(k2_zfmisc_1(A_76,B_77))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_166,plain,(
    k1_relset_1(k1_tarski('#skF_3'),'#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_62,c_162])).

tff(c_275,plain,(
    ! [B_115,A_116,C_117] :
      ( k1_xboole_0 = B_115
      | k1_relset_1(A_116,B_115,C_117) = A_116
      | ~ v1_funct_2(C_117,A_116,B_115)
      | ~ m1_subset_1(C_117,k1_zfmisc_1(k2_zfmisc_1(A_116,B_115))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_278,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1(k1_tarski('#skF_3'),'#skF_4','#skF_5') = k1_tarski('#skF_3')
    | ~ v1_funct_2('#skF_5',k1_tarski('#skF_3'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_275])).

tff(c_281,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_tarski('#skF_3') = k1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_166,c_278])).

tff(c_282,plain,(
    k1_tarski('#skF_3') = k1_relat_1('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_281])).

tff(c_20,plain,(
    ! [A_7] : k2_tarski(A_7,A_7) = k1_tarski(A_7) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_77,plain,(
    ! [D_37,A_38] : r2_hidden(D_37,k2_tarski(A_38,D_37)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_80,plain,(
    ! [A_7] : r2_hidden(A_7,k1_tarski(A_7)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_77])).

tff(c_310,plain,(
    r2_hidden('#skF_3',k1_relat_1('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_282,c_80])).

tff(c_34,plain,(
    ! [A_21,B_22] : v1_relat_1(k2_zfmisc_1(A_21,B_22)) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_96,plain,(
    ! [B_44,A_45] :
      ( v1_relat_1(B_44)
      | ~ m1_subset_1(B_44,k1_zfmisc_1(A_45))
      | ~ v1_relat_1(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_99,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1(k1_tarski('#skF_3'),'#skF_4')) ),
    inference(resolution,[status(thm)],[c_62,c_96])).

tff(c_102,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_99])).

tff(c_66,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_284,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'),'#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_282,c_62])).

tff(c_179,plain,(
    ! [B_86,A_87] :
      ( r2_hidden(k4_tarski(B_86,k1_funct_1(A_87,B_86)),A_87)
      | ~ r2_hidden(B_86,k1_relat_1(A_87))
      | ~ v1_funct_1(A_87)
      | ~ v1_relat_1(A_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_30,plain,(
    ! [C_17,A_14,B_15] :
      ( r2_hidden(C_17,A_14)
      | ~ r2_hidden(C_17,B_15)
      | ~ m1_subset_1(B_15,k1_zfmisc_1(A_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_8125,plain,(
    ! [B_10393,A_10394,A_10395] :
      ( r2_hidden(k4_tarski(B_10393,k1_funct_1(A_10394,B_10393)),A_10395)
      | ~ m1_subset_1(A_10394,k1_zfmisc_1(A_10395))
      | ~ r2_hidden(B_10393,k1_relat_1(A_10394))
      | ~ v1_funct_1(A_10394)
      | ~ v1_relat_1(A_10394) ) ),
    inference(resolution,[status(thm)],[c_179,c_30])).

tff(c_26,plain,(
    ! [B_11,D_13,A_10,C_12] :
      ( r2_hidden(B_11,D_13)
      | ~ r2_hidden(k4_tarski(A_10,B_11),k2_zfmisc_1(k1_tarski(C_12),D_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_10453,plain,(
    ! [A_13315,B_13316,D_13317,C_13318] :
      ( r2_hidden(k1_funct_1(A_13315,B_13316),D_13317)
      | ~ m1_subset_1(A_13315,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(C_13318),D_13317)))
      | ~ r2_hidden(B_13316,k1_relat_1(A_13315))
      | ~ v1_funct_1(A_13315)
      | ~ v1_relat_1(A_13315) ) ),
    inference(resolution,[status(thm)],[c_8125,c_26])).

tff(c_10603,plain,(
    ! [A_13506,B_13507,D_13508] :
      ( r2_hidden(k1_funct_1(A_13506,B_13507),D_13508)
      | ~ m1_subset_1(A_13506,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'),D_13508)))
      | ~ r2_hidden(B_13507,k1_relat_1(A_13506))
      | ~ v1_funct_1(A_13506)
      | ~ v1_relat_1(A_13506) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_282,c_10453])).

tff(c_10614,plain,(
    ! [B_13507] :
      ( r2_hidden(k1_funct_1('#skF_5',B_13507),'#skF_4')
      | ~ r2_hidden(B_13507,k1_relat_1('#skF_5'))
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_284,c_10603])).

tff(c_10618,plain,(
    ! [B_13601] :
      ( r2_hidden(k1_funct_1('#skF_5',B_13601),'#skF_4')
      | ~ r2_hidden(B_13601,k1_relat_1('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_66,c_10614])).

tff(c_58,plain,(
    ~ r2_hidden(k1_funct_1('#skF_5','#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_10634,plain,(
    ~ r2_hidden('#skF_3',k1_relat_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_10618,c_58])).

tff(c_10651,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_310,c_10634])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:41:42 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.11/2.75  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.11/2.75  
% 8.11/2.75  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.11/2.75  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4
% 8.11/2.75  
% 8.11/2.75  %Foreground sorts:
% 8.11/2.75  
% 8.11/2.75  
% 8.11/2.75  %Background operators:
% 8.11/2.75  
% 8.11/2.75  
% 8.11/2.75  %Foreground operators:
% 8.11/2.75  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 8.11/2.75  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 8.11/2.75  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.11/2.75  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.11/2.75  tff(k1_tarski, type, k1_tarski: $i > $i).
% 8.11/2.75  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 8.11/2.75  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.11/2.75  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 8.11/2.75  tff('#skF_5', type, '#skF_5': $i).
% 8.11/2.75  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 8.11/2.75  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 8.11/2.75  tff('#skF_3', type, '#skF_3': $i).
% 8.11/2.75  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 8.11/2.75  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 8.11/2.75  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.11/2.75  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 8.11/2.75  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.11/2.75  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 8.11/2.75  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 8.11/2.75  tff('#skF_4', type, '#skF_4': $i).
% 8.11/2.75  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.11/2.75  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 8.11/2.75  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.11/2.75  
% 8.11/2.76  tff(f_112, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_tarski(A), B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r2_hidden(k1_funct_1(C, A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_2)).
% 8.11/2.76  tff(f_82, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 8.11/2.76  tff(f_100, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 8.11/2.76  tff(f_36, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 8.11/2.76  tff(f_34, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 8.11/2.76  tff(f_60, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 8.11/2.76  tff(f_58, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 8.11/2.76  tff(f_78, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: ((r2_hidden(B, k1_relat_1(A)) => ((C = k1_funct_1(A, B)) <=> r2_hidden(k4_tarski(B, C), A))) & (~r2_hidden(B, k1_relat_1(A)) => ((C = k1_funct_1(A, B)) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_funct_1)).
% 8.11/2.76  tff(f_51, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 8.11/2.76  tff(f_44, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(k1_tarski(C), D)) <=> ((A = C) & r2_hidden(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t128_zfmisc_1)).
% 8.11/2.76  tff(c_60, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_112])).
% 8.11/2.76  tff(c_64, plain, (v1_funct_2('#skF_5', k1_tarski('#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_112])).
% 8.11/2.76  tff(c_62, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_3'), '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_112])).
% 8.11/2.76  tff(c_162, plain, (![A_76, B_77, C_78]: (k1_relset_1(A_76, B_77, C_78)=k1_relat_1(C_78) | ~m1_subset_1(C_78, k1_zfmisc_1(k2_zfmisc_1(A_76, B_77))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 8.11/2.76  tff(c_166, plain, (k1_relset_1(k1_tarski('#skF_3'), '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_62, c_162])).
% 8.11/2.76  tff(c_275, plain, (![B_115, A_116, C_117]: (k1_xboole_0=B_115 | k1_relset_1(A_116, B_115, C_117)=A_116 | ~v1_funct_2(C_117, A_116, B_115) | ~m1_subset_1(C_117, k1_zfmisc_1(k2_zfmisc_1(A_116, B_115))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 8.11/2.76  tff(c_278, plain, (k1_xboole_0='#skF_4' | k1_relset_1(k1_tarski('#skF_3'), '#skF_4', '#skF_5')=k1_tarski('#skF_3') | ~v1_funct_2('#skF_5', k1_tarski('#skF_3'), '#skF_4')), inference(resolution, [status(thm)], [c_62, c_275])).
% 8.11/2.76  tff(c_281, plain, (k1_xboole_0='#skF_4' | k1_tarski('#skF_3')=k1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_166, c_278])).
% 8.11/2.76  tff(c_282, plain, (k1_tarski('#skF_3')=k1_relat_1('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_60, c_281])).
% 8.11/2.76  tff(c_20, plain, (![A_7]: (k2_tarski(A_7, A_7)=k1_tarski(A_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 8.11/2.76  tff(c_77, plain, (![D_37, A_38]: (r2_hidden(D_37, k2_tarski(A_38, D_37)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 8.11/2.76  tff(c_80, plain, (![A_7]: (r2_hidden(A_7, k1_tarski(A_7)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_77])).
% 8.11/2.76  tff(c_310, plain, (r2_hidden('#skF_3', k1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_282, c_80])).
% 8.11/2.76  tff(c_34, plain, (![A_21, B_22]: (v1_relat_1(k2_zfmisc_1(A_21, B_22)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 8.11/2.76  tff(c_96, plain, (![B_44, A_45]: (v1_relat_1(B_44) | ~m1_subset_1(B_44, k1_zfmisc_1(A_45)) | ~v1_relat_1(A_45))), inference(cnfTransformation, [status(thm)], [f_58])).
% 8.11/2.76  tff(c_99, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1(k1_tarski('#skF_3'), '#skF_4'))), inference(resolution, [status(thm)], [c_62, c_96])).
% 8.11/2.76  tff(c_102, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_99])).
% 8.11/2.76  tff(c_66, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_112])).
% 8.11/2.76  tff(c_284, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'), '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_282, c_62])).
% 8.11/2.76  tff(c_179, plain, (![B_86, A_87]: (r2_hidden(k4_tarski(B_86, k1_funct_1(A_87, B_86)), A_87) | ~r2_hidden(B_86, k1_relat_1(A_87)) | ~v1_funct_1(A_87) | ~v1_relat_1(A_87))), inference(cnfTransformation, [status(thm)], [f_78])).
% 8.11/2.76  tff(c_30, plain, (![C_17, A_14, B_15]: (r2_hidden(C_17, A_14) | ~r2_hidden(C_17, B_15) | ~m1_subset_1(B_15, k1_zfmisc_1(A_14)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 8.11/2.76  tff(c_8125, plain, (![B_10393, A_10394, A_10395]: (r2_hidden(k4_tarski(B_10393, k1_funct_1(A_10394, B_10393)), A_10395) | ~m1_subset_1(A_10394, k1_zfmisc_1(A_10395)) | ~r2_hidden(B_10393, k1_relat_1(A_10394)) | ~v1_funct_1(A_10394) | ~v1_relat_1(A_10394))), inference(resolution, [status(thm)], [c_179, c_30])).
% 8.11/2.76  tff(c_26, plain, (![B_11, D_13, A_10, C_12]: (r2_hidden(B_11, D_13) | ~r2_hidden(k4_tarski(A_10, B_11), k2_zfmisc_1(k1_tarski(C_12), D_13)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 8.11/2.76  tff(c_10453, plain, (![A_13315, B_13316, D_13317, C_13318]: (r2_hidden(k1_funct_1(A_13315, B_13316), D_13317) | ~m1_subset_1(A_13315, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(C_13318), D_13317))) | ~r2_hidden(B_13316, k1_relat_1(A_13315)) | ~v1_funct_1(A_13315) | ~v1_relat_1(A_13315))), inference(resolution, [status(thm)], [c_8125, c_26])).
% 8.11/2.76  tff(c_10603, plain, (![A_13506, B_13507, D_13508]: (r2_hidden(k1_funct_1(A_13506, B_13507), D_13508) | ~m1_subset_1(A_13506, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'), D_13508))) | ~r2_hidden(B_13507, k1_relat_1(A_13506)) | ~v1_funct_1(A_13506) | ~v1_relat_1(A_13506))), inference(superposition, [status(thm), theory('equality')], [c_282, c_10453])).
% 8.11/2.76  tff(c_10614, plain, (![B_13507]: (r2_hidden(k1_funct_1('#skF_5', B_13507), '#skF_4') | ~r2_hidden(B_13507, k1_relat_1('#skF_5')) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_284, c_10603])).
% 8.11/2.76  tff(c_10618, plain, (![B_13601]: (r2_hidden(k1_funct_1('#skF_5', B_13601), '#skF_4') | ~r2_hidden(B_13601, k1_relat_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_102, c_66, c_10614])).
% 8.11/2.76  tff(c_58, plain, (~r2_hidden(k1_funct_1('#skF_5', '#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_112])).
% 8.11/2.76  tff(c_10634, plain, (~r2_hidden('#skF_3', k1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_10618, c_58])).
% 8.11/2.76  tff(c_10651, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_310, c_10634])).
% 8.11/2.76  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.11/2.76  
% 8.11/2.76  Inference rules
% 8.11/2.76  ----------------------
% 8.11/2.76  #Ref     : 0
% 8.11/2.76  #Sup     : 1791
% 8.11/2.76  #Fact    : 44
% 8.11/2.76  #Define  : 0
% 8.11/2.76  #Split   : 8
% 8.11/2.76  #Chain   : 0
% 8.11/2.76  #Close   : 0
% 8.11/2.76  
% 8.11/2.76  Ordering : KBO
% 8.11/2.76  
% 8.11/2.76  Simplification rules
% 8.11/2.76  ----------------------
% 8.11/2.76  #Subsume      : 659
% 8.11/2.76  #Demod        : 238
% 8.11/2.76  #Tautology    : 526
% 8.11/2.76  #SimpNegUnit  : 106
% 8.11/2.76  #BackRed      : 3
% 8.11/2.76  
% 8.11/2.76  #Partial instantiations: 7540
% 8.11/2.76  #Strategies tried      : 1
% 8.11/2.76  
% 8.11/2.76  Timing (in seconds)
% 8.11/2.76  ----------------------
% 8.11/2.77  Preprocessing        : 0.34
% 8.11/2.77  Parsing              : 0.18
% 8.11/2.77  CNF conversion       : 0.02
% 8.11/2.77  Main loop            : 1.63
% 8.11/2.77  Inferencing          : 0.73
% 8.11/2.77  Reduction            : 0.37
% 8.11/2.77  Demodulation         : 0.24
% 8.11/2.77  BG Simplification    : 0.07
% 8.11/2.77  Subsumption          : 0.36
% 8.11/2.77  Abstraction          : 0.09
% 8.11/2.77  MUC search           : 0.00
% 8.11/2.77  Cooper               : 0.00
% 8.11/2.77  Total                : 2.01
% 8.11/2.77  Index Insertion      : 0.00
% 8.11/2.77  Index Deletion       : 0.00
% 8.11/2.77  Index Matching       : 0.00
% 8.11/2.77  BG Taut test         : 0.00
%------------------------------------------------------------------------------
