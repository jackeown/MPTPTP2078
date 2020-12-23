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
% DateTime   : Thu Dec  3 10:15:08 EST 2020

% Result     : Theorem 3.49s
% Output     : CNFRefutation 3.49s
% Verified   : 
% Statistics : Number of formulae       :   67 (  91 expanded)
%              Number of leaves         :   37 (  50 expanded)
%              Depth                    :    9
%              Number of atoms          :   88 ( 170 expanded)
%              Number of equality atoms :   27 (  54 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_3 > #skF_5 > #skF_2 > #skF_6 > #skF_8 > #skF_1 > #skF_4

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

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_112,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,k1_tarski(B))
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
       => ( r2_hidden(C,A)
         => k1_funct_1(D,C) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_2)).

tff(f_79,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_101,axiom,(
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

tff(f_64,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A)
        & v1_funct_1(B) )
     => ! [C] :
          ( r2_hidden(C,k1_relat_1(B))
         => r2_hidden(k1_funct_1(B,C),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_funct_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_69,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_68,plain,(
    k1_funct_1('#skF_8','#skF_7') != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_72,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_5',k1_tarski('#skF_6')))) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_186,plain,(
    ! [C_77,B_78,A_79] :
      ( v5_relat_1(C_77,B_78)
      | ~ m1_subset_1(C_77,k1_zfmisc_1(k2_zfmisc_1(A_79,B_78))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_190,plain,(
    v5_relat_1('#skF_8',k1_tarski('#skF_6')) ),
    inference(resolution,[status(thm)],[c_72,c_186])).

tff(c_70,plain,(
    r2_hidden('#skF_7','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_156,plain,(
    ! [C_58,A_59,B_60] :
      ( v1_relat_1(C_58)
      | ~ m1_subset_1(C_58,k1_zfmisc_1(k2_zfmisc_1(A_59,B_60))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_160,plain,(
    v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_72,c_156])).

tff(c_76,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_74,plain,(
    v1_funct_2('#skF_8','#skF_5',k1_tarski('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_608,plain,(
    ! [A_1250,B_1251,C_1252] :
      ( k1_relset_1(A_1250,B_1251,C_1252) = k1_relat_1(C_1252)
      | ~ m1_subset_1(C_1252,k1_zfmisc_1(k2_zfmisc_1(A_1250,B_1251))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_614,plain,(
    k1_relset_1('#skF_5',k1_tarski('#skF_6'),'#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_72,c_608])).

tff(c_1564,plain,(
    ! [B_2177,A_2178,C_2179] :
      ( k1_xboole_0 = B_2177
      | k1_relset_1(A_2178,B_2177,C_2179) = A_2178
      | ~ v1_funct_2(C_2179,A_2178,B_2177)
      | ~ m1_subset_1(C_2179,k1_zfmisc_1(k2_zfmisc_1(A_2178,B_2177))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_1569,plain,
    ( k1_tarski('#skF_6') = k1_xboole_0
    | k1_relset_1('#skF_5',k1_tarski('#skF_6'),'#skF_8') = '#skF_5'
    | ~ v1_funct_2('#skF_8','#skF_5',k1_tarski('#skF_6')) ),
    inference(resolution,[status(thm)],[c_72,c_1564])).

tff(c_1572,plain,
    ( k1_tarski('#skF_6') = k1_xboole_0
    | k1_relat_1('#skF_8') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_614,c_1569])).

tff(c_1573,plain,(
    k1_relat_1('#skF_8') = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_1572])).

tff(c_1402,plain,(
    ! [B_1968,C_1969,A_1970] :
      ( r2_hidden(k1_funct_1(B_1968,C_1969),A_1970)
      | ~ r2_hidden(C_1969,k1_relat_1(B_1968))
      | ~ v1_funct_1(B_1968)
      | ~ v5_relat_1(B_1968,A_1970)
      | ~ v1_relat_1(B_1968) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_28,plain,(
    ! [C_13,A_9] :
      ( C_13 = A_9
      | ~ r2_hidden(C_13,k1_tarski(A_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1435,plain,(
    ! [B_1968,C_1969,A_9] :
      ( k1_funct_1(B_1968,C_1969) = A_9
      | ~ r2_hidden(C_1969,k1_relat_1(B_1968))
      | ~ v1_funct_1(B_1968)
      | ~ v5_relat_1(B_1968,k1_tarski(A_9))
      | ~ v1_relat_1(B_1968) ) ),
    inference(resolution,[status(thm)],[c_1402,c_28])).

tff(c_1577,plain,(
    ! [C_1969,A_9] :
      ( k1_funct_1('#skF_8',C_1969) = A_9
      | ~ r2_hidden(C_1969,'#skF_5')
      | ~ v1_funct_1('#skF_8')
      | ~ v5_relat_1('#skF_8',k1_tarski(A_9))
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1573,c_1435])).

tff(c_1658,plain,(
    ! [C_2316,A_2317] :
      ( k1_funct_1('#skF_8',C_2316) = A_2317
      | ~ r2_hidden(C_2316,'#skF_5')
      | ~ v5_relat_1('#skF_8',k1_tarski(A_2317)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_160,c_76,c_1577])).

tff(c_1676,plain,(
    ! [A_2345] :
      ( k1_funct_1('#skF_8','#skF_7') = A_2345
      | ~ v5_relat_1('#skF_8',k1_tarski(A_2345)) ) ),
    inference(resolution,[status(thm)],[c_70,c_1658])).

tff(c_1683,plain,(
    k1_funct_1('#skF_8','#skF_7') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_190,c_1676])).

tff(c_1687,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_1683])).

tff(c_1688,plain,(
    k1_tarski('#skF_6') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_1572])).

tff(c_30,plain,(
    ! [C_13] : r2_hidden(C_13,k1_tarski(C_13)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_94,plain,(
    ! [B_40,A_41] :
      ( ~ r1_tarski(B_40,A_41)
      | ~ r2_hidden(A_41,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_101,plain,(
    ! [C_13] : ~ r1_tarski(k1_tarski(C_13),C_13) ),
    inference(resolution,[status(thm)],[c_30,c_94])).

tff(c_1706,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_1688,c_101])).

tff(c_1763,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_1706])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:41:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.49/1.71  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.49/1.72  
% 3.49/1.72  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.49/1.72  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_3 > #skF_5 > #skF_2 > #skF_6 > #skF_8 > #skF_1 > #skF_4
% 3.49/1.72  
% 3.49/1.72  %Foreground sorts:
% 3.49/1.72  
% 3.49/1.72  
% 3.49/1.72  %Background operators:
% 3.49/1.72  
% 3.49/1.72  
% 3.49/1.72  %Foreground operators:
% 3.49/1.72  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.49/1.72  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.49/1.72  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.49/1.72  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.49/1.72  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.49/1.72  tff('#skF_7', type, '#skF_7': $i).
% 3.49/1.72  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.49/1.72  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.49/1.72  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.49/1.72  tff('#skF_5', type, '#skF_5': $i).
% 3.49/1.72  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.49/1.72  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 3.49/1.72  tff('#skF_6', type, '#skF_6': $i).
% 3.49/1.72  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.49/1.72  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.49/1.72  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.49/1.72  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.49/1.72  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.49/1.72  tff('#skF_8', type, '#skF_8': $i).
% 3.49/1.72  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.49/1.72  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.49/1.72  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.49/1.72  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.49/1.72  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.49/1.72  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 3.49/1.72  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.49/1.72  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.49/1.72  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.49/1.72  
% 3.49/1.73  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.49/1.73  tff(f_112, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_funct_2)).
% 3.49/1.73  tff(f_79, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.49/1.73  tff(f_73, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.49/1.73  tff(f_83, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.49/1.73  tff(f_101, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 3.49/1.73  tff(f_64, axiom, (![A, B]: (((v1_relat_1(B) & v5_relat_1(B, A)) & v1_funct_1(B)) => (![C]: (r2_hidden(C, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, C), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t172_funct_1)).
% 3.49/1.73  tff(f_49, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 3.49/1.73  tff(f_69, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 3.49/1.73  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.49/1.73  tff(c_68, plain, (k1_funct_1('#skF_8', '#skF_7')!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.49/1.73  tff(c_72, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_5', k1_tarski('#skF_6'))))), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.49/1.73  tff(c_186, plain, (![C_77, B_78, A_79]: (v5_relat_1(C_77, B_78) | ~m1_subset_1(C_77, k1_zfmisc_1(k2_zfmisc_1(A_79, B_78))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.49/1.73  tff(c_190, plain, (v5_relat_1('#skF_8', k1_tarski('#skF_6'))), inference(resolution, [status(thm)], [c_72, c_186])).
% 3.49/1.73  tff(c_70, plain, (r2_hidden('#skF_7', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.49/1.73  tff(c_156, plain, (![C_58, A_59, B_60]: (v1_relat_1(C_58) | ~m1_subset_1(C_58, k1_zfmisc_1(k2_zfmisc_1(A_59, B_60))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.49/1.73  tff(c_160, plain, (v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_72, c_156])).
% 3.49/1.73  tff(c_76, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.49/1.73  tff(c_74, plain, (v1_funct_2('#skF_8', '#skF_5', k1_tarski('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.49/1.73  tff(c_608, plain, (![A_1250, B_1251, C_1252]: (k1_relset_1(A_1250, B_1251, C_1252)=k1_relat_1(C_1252) | ~m1_subset_1(C_1252, k1_zfmisc_1(k2_zfmisc_1(A_1250, B_1251))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.49/1.73  tff(c_614, plain, (k1_relset_1('#skF_5', k1_tarski('#skF_6'), '#skF_8')=k1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_72, c_608])).
% 3.49/1.73  tff(c_1564, plain, (![B_2177, A_2178, C_2179]: (k1_xboole_0=B_2177 | k1_relset_1(A_2178, B_2177, C_2179)=A_2178 | ~v1_funct_2(C_2179, A_2178, B_2177) | ~m1_subset_1(C_2179, k1_zfmisc_1(k2_zfmisc_1(A_2178, B_2177))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.49/1.73  tff(c_1569, plain, (k1_tarski('#skF_6')=k1_xboole_0 | k1_relset_1('#skF_5', k1_tarski('#skF_6'), '#skF_8')='#skF_5' | ~v1_funct_2('#skF_8', '#skF_5', k1_tarski('#skF_6'))), inference(resolution, [status(thm)], [c_72, c_1564])).
% 3.49/1.73  tff(c_1572, plain, (k1_tarski('#skF_6')=k1_xboole_0 | k1_relat_1('#skF_8')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_614, c_1569])).
% 3.49/1.73  tff(c_1573, plain, (k1_relat_1('#skF_8')='#skF_5'), inference(splitLeft, [status(thm)], [c_1572])).
% 3.49/1.73  tff(c_1402, plain, (![B_1968, C_1969, A_1970]: (r2_hidden(k1_funct_1(B_1968, C_1969), A_1970) | ~r2_hidden(C_1969, k1_relat_1(B_1968)) | ~v1_funct_1(B_1968) | ~v5_relat_1(B_1968, A_1970) | ~v1_relat_1(B_1968))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.49/1.73  tff(c_28, plain, (![C_13, A_9]: (C_13=A_9 | ~r2_hidden(C_13, k1_tarski(A_9)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.49/1.73  tff(c_1435, plain, (![B_1968, C_1969, A_9]: (k1_funct_1(B_1968, C_1969)=A_9 | ~r2_hidden(C_1969, k1_relat_1(B_1968)) | ~v1_funct_1(B_1968) | ~v5_relat_1(B_1968, k1_tarski(A_9)) | ~v1_relat_1(B_1968))), inference(resolution, [status(thm)], [c_1402, c_28])).
% 3.49/1.73  tff(c_1577, plain, (![C_1969, A_9]: (k1_funct_1('#skF_8', C_1969)=A_9 | ~r2_hidden(C_1969, '#skF_5') | ~v1_funct_1('#skF_8') | ~v5_relat_1('#skF_8', k1_tarski(A_9)) | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_1573, c_1435])).
% 3.49/1.73  tff(c_1658, plain, (![C_2316, A_2317]: (k1_funct_1('#skF_8', C_2316)=A_2317 | ~r2_hidden(C_2316, '#skF_5') | ~v5_relat_1('#skF_8', k1_tarski(A_2317)))), inference(demodulation, [status(thm), theory('equality')], [c_160, c_76, c_1577])).
% 3.49/1.73  tff(c_1676, plain, (![A_2345]: (k1_funct_1('#skF_8', '#skF_7')=A_2345 | ~v5_relat_1('#skF_8', k1_tarski(A_2345)))), inference(resolution, [status(thm)], [c_70, c_1658])).
% 3.49/1.73  tff(c_1683, plain, (k1_funct_1('#skF_8', '#skF_7')='#skF_6'), inference(resolution, [status(thm)], [c_190, c_1676])).
% 3.49/1.73  tff(c_1687, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_1683])).
% 3.49/1.73  tff(c_1688, plain, (k1_tarski('#skF_6')=k1_xboole_0), inference(splitRight, [status(thm)], [c_1572])).
% 3.49/1.73  tff(c_30, plain, (![C_13]: (r2_hidden(C_13, k1_tarski(C_13)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.49/1.73  tff(c_94, plain, (![B_40, A_41]: (~r1_tarski(B_40, A_41) | ~r2_hidden(A_41, B_40))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.49/1.73  tff(c_101, plain, (![C_13]: (~r1_tarski(k1_tarski(C_13), C_13))), inference(resolution, [status(thm)], [c_30, c_94])).
% 3.49/1.73  tff(c_1706, plain, (~r1_tarski(k1_xboole_0, '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_1688, c_101])).
% 3.49/1.73  tff(c_1763, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_1706])).
% 3.49/1.73  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.49/1.73  
% 3.49/1.73  Inference rules
% 3.49/1.73  ----------------------
% 3.49/1.73  #Ref     : 0
% 3.49/1.73  #Sup     : 243
% 3.49/1.73  #Fact    : 0
% 3.49/1.73  #Define  : 0
% 3.49/1.73  #Split   : 6
% 3.49/1.73  #Chain   : 0
% 3.49/1.73  #Close   : 0
% 3.49/1.73  
% 3.49/1.73  Ordering : KBO
% 3.49/1.73  
% 3.49/1.73  Simplification rules
% 3.49/1.73  ----------------------
% 3.49/1.73  #Subsume      : 42
% 3.49/1.73  #Demod        : 48
% 3.49/1.73  #Tautology    : 82
% 3.49/1.73  #SimpNegUnit  : 1
% 3.49/1.73  #BackRed      : 5
% 3.49/1.73  
% 3.49/1.73  #Partial instantiations: 1377
% 3.49/1.73  #Strategies tried      : 1
% 3.49/1.73  
% 3.49/1.73  Timing (in seconds)
% 3.49/1.73  ----------------------
% 3.49/1.74  Preprocessing        : 0.45
% 3.49/1.74  Parsing              : 0.25
% 3.49/1.74  CNF conversion       : 0.03
% 3.49/1.74  Main loop            : 0.48
% 3.49/1.74  Inferencing          : 0.23
% 3.49/1.74  Reduction            : 0.12
% 3.49/1.74  Demodulation         : 0.08
% 3.49/1.74  BG Simplification    : 0.03
% 3.49/1.74  Subsumption          : 0.07
% 3.49/1.74  Abstraction          : 0.03
% 3.49/1.74  MUC search           : 0.00
% 3.49/1.74  Cooper               : 0.00
% 3.49/1.74  Total                : 0.96
% 3.49/1.74  Index Insertion      : 0.00
% 3.49/1.74  Index Deletion       : 0.00
% 3.49/1.74  Index Matching       : 0.00
% 3.49/1.74  BG Taut test         : 0.00
%------------------------------------------------------------------------------
