%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:19 EST 2020

% Result     : Theorem 11.88s
% Output     : CNFRefutation 11.88s
% Verified   : 
% Statistics : Number of formulae       :   70 (  93 expanded)
%              Number of leaves         :   37 (  49 expanded)
%              Depth                    :    7
%              Number of atoms          :  101 ( 180 expanded)
%              Number of equality atoms :   31 (  56 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_110,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,k1_tarski(B))
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
       => ( r2_hidden(C,A)
         => k1_funct_1(D,C) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_2)).

tff(f_62,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_60,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_99,axiom,(
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

tff(f_72,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

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

tff(f_38,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(f_77,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_60,plain,(
    k1_funct_1('#skF_6','#skF_5') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_62,plain,(
    r2_hidden('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_36,plain,(
    ! [A_22,B_23] : v1_relat_1(k2_zfmisc_1(A_22,B_23)) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_64,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3',k1_tarski('#skF_4')))) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_125,plain,(
    ! [B_53,A_54] :
      ( v1_relat_1(B_53)
      | ~ m1_subset_1(B_53,k1_zfmisc_1(A_54))
      | ~ v1_relat_1(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_128,plain,
    ( v1_relat_1('#skF_6')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3',k1_tarski('#skF_4'))) ),
    inference(resolution,[status(thm)],[c_64,c_125])).

tff(c_131,plain,(
    v1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_128])).

tff(c_68,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_66,plain,(
    v1_funct_2('#skF_6','#skF_3',k1_tarski('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_196,plain,(
    ! [A_87,B_88,C_89] :
      ( k1_relset_1(A_87,B_88,C_89) = k1_relat_1(C_89)
      | ~ m1_subset_1(C_89,k1_zfmisc_1(k2_zfmisc_1(A_87,B_88))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_200,plain,(
    k1_relset_1('#skF_3',k1_tarski('#skF_4'),'#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_64,c_196])).

tff(c_347,plain,(
    ! [B_125,A_126,C_127] :
      ( k1_xboole_0 = B_125
      | k1_relset_1(A_126,B_125,C_127) = A_126
      | ~ v1_funct_2(C_127,A_126,B_125)
      | ~ m1_subset_1(C_127,k1_zfmisc_1(k2_zfmisc_1(A_126,B_125))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_350,plain,
    ( k1_tarski('#skF_4') = k1_xboole_0
    | k1_relset_1('#skF_3',k1_tarski('#skF_4'),'#skF_6') = '#skF_3'
    | ~ v1_funct_2('#skF_6','#skF_3',k1_tarski('#skF_4')) ),
    inference(resolution,[status(thm)],[c_64,c_347])).

tff(c_353,plain,
    ( k1_tarski('#skF_4') = k1_xboole_0
    | k1_relat_1('#skF_6') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_200,c_350])).

tff(c_354,plain,(
    k1_relat_1('#skF_6') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_353])).

tff(c_251,plain,(
    ! [A_100,C_101] :
      ( r2_hidden(k4_tarski(A_100,k1_funct_1(C_101,A_100)),C_101)
      | ~ r2_hidden(A_100,k1_relat_1(C_101))
      | ~ v1_funct_1(C_101)
      | ~ v1_relat_1(C_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_32,plain,(
    ! [C_18,A_15,B_16] :
      ( r2_hidden(C_18,A_15)
      | ~ r2_hidden(C_18,B_16)
      | ~ m1_subset_1(B_16,k1_zfmisc_1(A_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_25373,plain,(
    ! [A_13425,C_13426,A_13427] :
      ( r2_hidden(k4_tarski(A_13425,k1_funct_1(C_13426,A_13425)),A_13427)
      | ~ m1_subset_1(C_13426,k1_zfmisc_1(A_13427))
      | ~ r2_hidden(A_13425,k1_relat_1(C_13426))
      | ~ v1_funct_1(C_13426)
      | ~ v1_relat_1(C_13426) ) ),
    inference(resolution,[status(thm)],[c_251,c_32])).

tff(c_28,plain,(
    ! [D_14,B_12,A_11,C_13] :
      ( D_14 = B_12
      | ~ r2_hidden(k4_tarski(A_11,B_12),k2_zfmisc_1(C_13,k1_tarski(D_14))) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_28061,plain,(
    ! [C_16126,A_16127,D_16128,C_16129] :
      ( k1_funct_1(C_16126,A_16127) = D_16128
      | ~ m1_subset_1(C_16126,k1_zfmisc_1(k2_zfmisc_1(C_16129,k1_tarski(D_16128))))
      | ~ r2_hidden(A_16127,k1_relat_1(C_16126))
      | ~ v1_funct_1(C_16126)
      | ~ v1_relat_1(C_16126) ) ),
    inference(resolution,[status(thm)],[c_25373,c_28])).

tff(c_28124,plain,(
    ! [A_16127] :
      ( k1_funct_1('#skF_6',A_16127) = '#skF_4'
      | ~ r2_hidden(A_16127,k1_relat_1('#skF_6'))
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_64,c_28061])).

tff(c_28128,plain,(
    ! [A_16245] :
      ( k1_funct_1('#skF_6',A_16245) = '#skF_4'
      | ~ r2_hidden(A_16245,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_68,c_354,c_28124])).

tff(c_28256,plain,(
    k1_funct_1('#skF_6','#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_62,c_28128])).

tff(c_28268,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_28256])).

tff(c_28269,plain,(
    k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_353])).

tff(c_73,plain,(
    ! [A_42] : k2_tarski(A_42,A_42) = k1_tarski(A_42) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_8,plain,(
    ! [D_7,B_3] : r2_hidden(D_7,k2_tarski(D_7,B_3)) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_79,plain,(
    ! [A_42] : r2_hidden(A_42,k1_tarski(A_42)) ),
    inference(superposition,[status(thm),theory(equality)],[c_73,c_8])).

tff(c_90,plain,(
    ! [B_44,A_45] :
      ( ~ r1_tarski(B_44,A_45)
      | ~ r2_hidden(A_45,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_103,plain,(
    ! [A_42] : ~ r1_tarski(k1_tarski(A_42),A_42) ),
    inference(resolution,[status(thm)],[c_79,c_90])).

tff(c_28302,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_28269,c_103])).

tff(c_28312,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_28302])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 19:21:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.88/4.29  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.88/4.29  
% 11.88/4.29  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.88/4.30  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4
% 11.88/4.30  
% 11.88/4.30  %Foreground sorts:
% 11.88/4.30  
% 11.88/4.30  
% 11.88/4.30  %Background operators:
% 11.88/4.30  
% 11.88/4.30  
% 11.88/4.30  %Foreground operators:
% 11.88/4.30  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 11.88/4.30  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 11.88/4.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.88/4.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 11.88/4.30  tff(k1_tarski, type, k1_tarski: $i > $i).
% 11.88/4.30  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 11.88/4.30  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 11.88/4.30  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.88/4.30  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 11.88/4.30  tff('#skF_5', type, '#skF_5': $i).
% 11.88/4.30  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 11.88/4.30  tff('#skF_6', type, '#skF_6': $i).
% 11.88/4.30  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 11.88/4.30  tff('#skF_3', type, '#skF_3': $i).
% 11.88/4.30  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 11.88/4.30  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 11.88/4.30  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 11.88/4.30  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 11.88/4.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.88/4.30  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 11.88/4.30  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 11.88/4.30  tff('#skF_4', type, '#skF_4': $i).
% 11.88/4.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.88/4.30  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 11.88/4.30  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 11.88/4.30  
% 11.88/4.31  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 11.88/4.31  tff(f_110, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_funct_2)).
% 11.88/4.31  tff(f_62, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 11.88/4.31  tff(f_60, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 11.88/4.31  tff(f_81, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 11.88/4.31  tff(f_99, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 11.88/4.31  tff(f_72, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_1)).
% 11.88/4.31  tff(f_53, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 11.88/4.31  tff(f_46, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, k1_tarski(D))) <=> (r2_hidden(A, C) & (B = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t129_zfmisc_1)).
% 11.88/4.31  tff(f_38, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 11.88/4.31  tff(f_36, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 11.88/4.31  tff(f_77, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 11.88/4.31  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 11.88/4.31  tff(c_60, plain, (k1_funct_1('#skF_6', '#skF_5')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_110])).
% 11.88/4.31  tff(c_62, plain, (r2_hidden('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_110])).
% 11.88/4.31  tff(c_36, plain, (![A_22, B_23]: (v1_relat_1(k2_zfmisc_1(A_22, B_23)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 11.88/4.31  tff(c_64, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', k1_tarski('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_110])).
% 11.88/4.31  tff(c_125, plain, (![B_53, A_54]: (v1_relat_1(B_53) | ~m1_subset_1(B_53, k1_zfmisc_1(A_54)) | ~v1_relat_1(A_54))), inference(cnfTransformation, [status(thm)], [f_60])).
% 11.88/4.31  tff(c_128, plain, (v1_relat_1('#skF_6') | ~v1_relat_1(k2_zfmisc_1('#skF_3', k1_tarski('#skF_4')))), inference(resolution, [status(thm)], [c_64, c_125])).
% 11.88/4.31  tff(c_131, plain, (v1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_128])).
% 11.88/4.31  tff(c_68, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_110])).
% 11.88/4.31  tff(c_66, plain, (v1_funct_2('#skF_6', '#skF_3', k1_tarski('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_110])).
% 11.88/4.31  tff(c_196, plain, (![A_87, B_88, C_89]: (k1_relset_1(A_87, B_88, C_89)=k1_relat_1(C_89) | ~m1_subset_1(C_89, k1_zfmisc_1(k2_zfmisc_1(A_87, B_88))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 11.88/4.31  tff(c_200, plain, (k1_relset_1('#skF_3', k1_tarski('#skF_4'), '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_64, c_196])).
% 11.88/4.31  tff(c_347, plain, (![B_125, A_126, C_127]: (k1_xboole_0=B_125 | k1_relset_1(A_126, B_125, C_127)=A_126 | ~v1_funct_2(C_127, A_126, B_125) | ~m1_subset_1(C_127, k1_zfmisc_1(k2_zfmisc_1(A_126, B_125))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 11.88/4.31  tff(c_350, plain, (k1_tarski('#skF_4')=k1_xboole_0 | k1_relset_1('#skF_3', k1_tarski('#skF_4'), '#skF_6')='#skF_3' | ~v1_funct_2('#skF_6', '#skF_3', k1_tarski('#skF_4'))), inference(resolution, [status(thm)], [c_64, c_347])).
% 11.88/4.31  tff(c_353, plain, (k1_tarski('#skF_4')=k1_xboole_0 | k1_relat_1('#skF_6')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_200, c_350])).
% 11.88/4.31  tff(c_354, plain, (k1_relat_1('#skF_6')='#skF_3'), inference(splitLeft, [status(thm)], [c_353])).
% 11.88/4.31  tff(c_251, plain, (![A_100, C_101]: (r2_hidden(k4_tarski(A_100, k1_funct_1(C_101, A_100)), C_101) | ~r2_hidden(A_100, k1_relat_1(C_101)) | ~v1_funct_1(C_101) | ~v1_relat_1(C_101))), inference(cnfTransformation, [status(thm)], [f_72])).
% 11.88/4.31  tff(c_32, plain, (![C_18, A_15, B_16]: (r2_hidden(C_18, A_15) | ~r2_hidden(C_18, B_16) | ~m1_subset_1(B_16, k1_zfmisc_1(A_15)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 11.88/4.31  tff(c_25373, plain, (![A_13425, C_13426, A_13427]: (r2_hidden(k4_tarski(A_13425, k1_funct_1(C_13426, A_13425)), A_13427) | ~m1_subset_1(C_13426, k1_zfmisc_1(A_13427)) | ~r2_hidden(A_13425, k1_relat_1(C_13426)) | ~v1_funct_1(C_13426) | ~v1_relat_1(C_13426))), inference(resolution, [status(thm)], [c_251, c_32])).
% 11.88/4.31  tff(c_28, plain, (![D_14, B_12, A_11, C_13]: (D_14=B_12 | ~r2_hidden(k4_tarski(A_11, B_12), k2_zfmisc_1(C_13, k1_tarski(D_14))))), inference(cnfTransformation, [status(thm)], [f_46])).
% 11.88/4.31  tff(c_28061, plain, (![C_16126, A_16127, D_16128, C_16129]: (k1_funct_1(C_16126, A_16127)=D_16128 | ~m1_subset_1(C_16126, k1_zfmisc_1(k2_zfmisc_1(C_16129, k1_tarski(D_16128)))) | ~r2_hidden(A_16127, k1_relat_1(C_16126)) | ~v1_funct_1(C_16126) | ~v1_relat_1(C_16126))), inference(resolution, [status(thm)], [c_25373, c_28])).
% 11.88/4.31  tff(c_28124, plain, (![A_16127]: (k1_funct_1('#skF_6', A_16127)='#skF_4' | ~r2_hidden(A_16127, k1_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_64, c_28061])).
% 11.88/4.31  tff(c_28128, plain, (![A_16245]: (k1_funct_1('#skF_6', A_16245)='#skF_4' | ~r2_hidden(A_16245, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_131, c_68, c_354, c_28124])).
% 11.88/4.31  tff(c_28256, plain, (k1_funct_1('#skF_6', '#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_62, c_28128])).
% 11.88/4.31  tff(c_28268, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_28256])).
% 11.88/4.31  tff(c_28269, plain, (k1_tarski('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_353])).
% 11.88/4.31  tff(c_73, plain, (![A_42]: (k2_tarski(A_42, A_42)=k1_tarski(A_42))), inference(cnfTransformation, [status(thm)], [f_38])).
% 11.88/4.31  tff(c_8, plain, (![D_7, B_3]: (r2_hidden(D_7, k2_tarski(D_7, B_3)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 11.88/4.31  tff(c_79, plain, (![A_42]: (r2_hidden(A_42, k1_tarski(A_42)))), inference(superposition, [status(thm), theory('equality')], [c_73, c_8])).
% 11.88/4.31  tff(c_90, plain, (![B_44, A_45]: (~r1_tarski(B_44, A_45) | ~r2_hidden(A_45, B_44))), inference(cnfTransformation, [status(thm)], [f_77])).
% 11.88/4.31  tff(c_103, plain, (![A_42]: (~r1_tarski(k1_tarski(A_42), A_42))), inference(resolution, [status(thm)], [c_79, c_90])).
% 11.88/4.31  tff(c_28302, plain, (~r1_tarski(k1_xboole_0, '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_28269, c_103])).
% 11.88/4.31  tff(c_28312, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_28302])).
% 11.88/4.31  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.88/4.31  
% 11.88/4.31  Inference rules
% 11.88/4.31  ----------------------
% 11.88/4.31  #Ref     : 0
% 11.88/4.31  #Sup     : 3526
% 11.88/4.31  #Fact    : 44
% 11.88/4.31  #Define  : 0
% 11.88/4.31  #Split   : 15
% 11.88/4.31  #Chain   : 0
% 11.88/4.31  #Close   : 0
% 11.88/4.31  
% 11.88/4.31  Ordering : KBO
% 11.88/4.31  
% 11.88/4.31  Simplification rules
% 11.88/4.31  ----------------------
% 11.88/4.31  #Subsume      : 569
% 11.88/4.31  #Demod        : 400
% 11.88/4.31  #Tautology    : 379
% 11.88/4.31  #SimpNegUnit  : 1
% 11.88/4.31  #BackRed      : 4
% 11.88/4.31  
% 11.88/4.31  #Partial instantiations: 11136
% 11.88/4.31  #Strategies tried      : 1
% 11.88/4.31  
% 11.88/4.31  Timing (in seconds)
% 11.88/4.31  ----------------------
% 11.88/4.31  Preprocessing        : 0.34
% 11.88/4.31  Parsing              : 0.17
% 11.88/4.31  CNF conversion       : 0.02
% 11.88/4.31  Main loop            : 3.19
% 11.88/4.31  Inferencing          : 1.13
% 11.88/4.31  Reduction            : 0.61
% 11.88/4.31  Demodulation         : 0.42
% 11.88/4.31  BG Simplification    : 0.18
% 11.88/4.31  Subsumption          : 1.12
% 11.88/4.31  Abstraction          : 0.25
% 11.88/4.31  MUC search           : 0.00
% 11.88/4.31  Cooper               : 0.00
% 11.88/4.31  Total                : 3.55
% 11.88/4.31  Index Insertion      : 0.00
% 11.88/4.31  Index Deletion       : 0.00
% 11.88/4.31  Index Matching       : 0.00
% 11.88/4.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
