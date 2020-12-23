%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:11 EST 2020

% Result     : Theorem 4.09s
% Output     : CNFRefutation 4.16s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 109 expanded)
%              Number of leaves         :   46 (  60 expanded)
%              Depth                    :   11
%              Number of atoms          :  104 ( 191 expanded)
%              Number of equality atoms :   32 (  58 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_11 > #skF_1 > #skF_10 > #skF_2 > #skF_13 > #skF_8 > #skF_9 > #skF_3 > #skF_7 > #skF_5 > #skF_12 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_13',type,(
    '#skF_13': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i ) > $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_135,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,k1_tarski(B))
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
       => ( r2_hidden(C,A)
         => k1_funct_1(D,C) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_2)).

tff(f_102,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_124,axiom,(
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

tff(f_94,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_90,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( B = k2_relat_1(A)
        <=> ! [C] :
              ( r2_hidden(C,B)
            <=> ? [D] :
                  ( r2_hidden(D,k1_relat_1(A))
                  & C = k1_funct_1(A,D) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).

tff(f_106,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_98,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_63,axiom,(
    ! [A] : ~ v1_xboole_0(k1_tarski(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_xboole_0)).

tff(f_69,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_54,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_94,plain,(
    k1_funct_1('#skF_13','#skF_12') != '#skF_11' ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_96,plain,(
    r2_hidden('#skF_12','#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_100,plain,(
    v1_funct_2('#skF_13','#skF_10',k1_tarski('#skF_11')) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_98,plain,(
    m1_subset_1('#skF_13',k1_zfmisc_1(k2_zfmisc_1('#skF_10',k1_tarski('#skF_11')))) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_486,plain,(
    ! [A_154,B_155,C_156] :
      ( k1_relset_1(A_154,B_155,C_156) = k1_relat_1(C_156)
      | ~ m1_subset_1(C_156,k1_zfmisc_1(k2_zfmisc_1(A_154,B_155))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_490,plain,(
    k1_relset_1('#skF_10',k1_tarski('#skF_11'),'#skF_13') = k1_relat_1('#skF_13') ),
    inference(resolution,[status(thm)],[c_98,c_486])).

tff(c_1659,plain,(
    ! [B_280,A_281,C_282] :
      ( k1_xboole_0 = B_280
      | k1_relset_1(A_281,B_280,C_282) = A_281
      | ~ v1_funct_2(C_282,A_281,B_280)
      | ~ m1_subset_1(C_282,k1_zfmisc_1(k2_zfmisc_1(A_281,B_280))) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_1666,plain,
    ( k1_tarski('#skF_11') = k1_xboole_0
    | k1_relset_1('#skF_10',k1_tarski('#skF_11'),'#skF_13') = '#skF_10'
    | ~ v1_funct_2('#skF_13','#skF_10',k1_tarski('#skF_11')) ),
    inference(resolution,[status(thm)],[c_98,c_1659])).

tff(c_1670,plain,
    ( k1_tarski('#skF_11') = k1_xboole_0
    | k1_relat_1('#skF_13') = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_490,c_1666])).

tff(c_1671,plain,(
    k1_relat_1('#skF_13') = '#skF_10' ),
    inference(splitLeft,[status(thm)],[c_1670])).

tff(c_226,plain,(
    ! [C_117,A_118,B_119] :
      ( v1_relat_1(C_117)
      | ~ m1_subset_1(C_117,k1_zfmisc_1(k2_zfmisc_1(A_118,B_119))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_230,plain,(
    v1_relat_1('#skF_13') ),
    inference(resolution,[status(thm)],[c_98,c_226])).

tff(c_102,plain,(
    v1_funct_1('#skF_13') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_1096,plain,(
    ! [A_217,D_218] :
      ( r2_hidden(k1_funct_1(A_217,D_218),k2_relat_1(A_217))
      | ~ r2_hidden(D_218,k1_relat_1(A_217))
      | ~ v1_funct_1(A_217)
      | ~ v1_relat_1(A_217) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_340,plain,(
    ! [A_139,B_140,C_141] :
      ( k2_relset_1(A_139,B_140,C_141) = k2_relat_1(C_141)
      | ~ m1_subset_1(C_141,k1_zfmisc_1(k2_zfmisc_1(A_139,B_140))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_344,plain,(
    k2_relset_1('#skF_10',k1_tarski('#skF_11'),'#skF_13') = k2_relat_1('#skF_13') ),
    inference(resolution,[status(thm)],[c_98,c_340])).

tff(c_499,plain,(
    ! [A_161,B_162,C_163] :
      ( m1_subset_1(k2_relset_1(A_161,B_162,C_163),k1_zfmisc_1(B_162))
      | ~ m1_subset_1(C_163,k1_zfmisc_1(k2_zfmisc_1(A_161,B_162))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_516,plain,
    ( m1_subset_1(k2_relat_1('#skF_13'),k1_zfmisc_1(k1_tarski('#skF_11')))
    | ~ m1_subset_1('#skF_13',k1_zfmisc_1(k2_zfmisc_1('#skF_10',k1_tarski('#skF_11')))) ),
    inference(superposition,[status(thm),theory(equality)],[c_344,c_499])).

tff(c_522,plain,(
    m1_subset_1(k2_relat_1('#skF_13'),k1_zfmisc_1(k1_tarski('#skF_11'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_516])).

tff(c_54,plain,(
    ! [A_26,C_28,B_27] :
      ( m1_subset_1(A_26,C_28)
      | ~ m1_subset_1(B_27,k1_zfmisc_1(C_28))
      | ~ r2_hidden(A_26,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_551,plain,(
    ! [A_26] :
      ( m1_subset_1(A_26,k1_tarski('#skF_11'))
      | ~ r2_hidden(A_26,k2_relat_1('#skF_13')) ) ),
    inference(resolution,[status(thm)],[c_522,c_54])).

tff(c_1100,plain,(
    ! [D_218] :
      ( m1_subset_1(k1_funct_1('#skF_13',D_218),k1_tarski('#skF_11'))
      | ~ r2_hidden(D_218,k1_relat_1('#skF_13'))
      | ~ v1_funct_1('#skF_13')
      | ~ v1_relat_1('#skF_13') ) ),
    inference(resolution,[status(thm)],[c_1096,c_551])).

tff(c_1108,plain,(
    ! [D_219] :
      ( m1_subset_1(k1_funct_1('#skF_13',D_219),k1_tarski('#skF_11'))
      | ~ r2_hidden(D_219,k1_relat_1('#skF_13')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_230,c_102,c_1100])).

tff(c_50,plain,(
    ! [A_23] : ~ v1_xboole_0(k1_tarski(A_23)) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_213,plain,(
    ! [A_113,B_114] :
      ( r2_hidden(A_113,B_114)
      | v1_xboole_0(B_114)
      | ~ m1_subset_1(A_113,B_114) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_32,plain,(
    ! [C_16,A_12] :
      ( C_16 = A_12
      | ~ r2_hidden(C_16,k1_tarski(A_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_217,plain,(
    ! [A_12,A_113] :
      ( A_12 = A_113
      | v1_xboole_0(k1_tarski(A_12))
      | ~ m1_subset_1(A_113,k1_tarski(A_12)) ) ),
    inference(resolution,[status(thm)],[c_213,c_32])).

tff(c_223,plain,(
    ! [A_12,A_113] :
      ( A_12 = A_113
      | ~ m1_subset_1(A_113,k1_tarski(A_12)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_217])).

tff(c_1112,plain,(
    ! [D_219] :
      ( k1_funct_1('#skF_13',D_219) = '#skF_11'
      | ~ r2_hidden(D_219,k1_relat_1('#skF_13')) ) ),
    inference(resolution,[status(thm)],[c_1108,c_223])).

tff(c_1705,plain,(
    ! [D_283] :
      ( k1_funct_1('#skF_13',D_283) = '#skF_11'
      | ~ r2_hidden(D_283,'#skF_10') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1671,c_1112])).

tff(c_1724,plain,(
    k1_funct_1('#skF_13','#skF_12') = '#skF_11' ),
    inference(resolution,[status(thm)],[c_96,c_1705])).

tff(c_1736,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_1724])).

tff(c_1737,plain,(
    k1_tarski('#skF_11') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_1670])).

tff(c_1776,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1737,c_50])).

tff(c_1784,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1776])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:59:17 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.09/1.67  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.09/1.67  
% 4.09/1.67  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.09/1.67  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_11 > #skF_1 > #skF_10 > #skF_2 > #skF_13 > #skF_8 > #skF_9 > #skF_3 > #skF_7 > #skF_5 > #skF_12 > #skF_4
% 4.09/1.67  
% 4.09/1.67  %Foreground sorts:
% 4.09/1.67  
% 4.09/1.67  
% 4.09/1.67  %Background operators:
% 4.09/1.67  
% 4.09/1.67  
% 4.09/1.67  %Foreground operators:
% 4.09/1.67  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.09/1.67  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 4.09/1.67  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.09/1.67  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.09/1.67  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.09/1.67  tff('#skF_11', type, '#skF_11': $i).
% 4.09/1.67  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.09/1.67  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.09/1.67  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.09/1.67  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.09/1.67  tff('#skF_10', type, '#skF_10': $i).
% 4.09/1.67  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.09/1.67  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.09/1.67  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.09/1.67  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 4.09/1.67  tff('#skF_13', type, '#skF_13': $i).
% 4.09/1.67  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.09/1.67  tff('#skF_8', type, '#skF_8': ($i * $i) > $i).
% 4.09/1.67  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.09/1.67  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.09/1.67  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.09/1.67  tff('#skF_9', type, '#skF_9': ($i * $i * $i) > $i).
% 4.09/1.67  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.09/1.67  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.09/1.67  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.09/1.67  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.09/1.67  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 4.09/1.67  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 4.09/1.67  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.09/1.67  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 4.09/1.67  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.09/1.67  tff('#skF_12', type, '#skF_12': $i).
% 4.09/1.67  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 4.09/1.67  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.09/1.67  
% 4.16/1.69  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 4.16/1.69  tff(f_135, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_funct_2)).
% 4.16/1.69  tff(f_102, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.16/1.69  tff(f_124, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 4.16/1.69  tff(f_94, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.16/1.69  tff(f_90, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_funct_1)).
% 4.16/1.69  tff(f_106, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 4.16/1.69  tff(f_98, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 4.16/1.69  tff(f_75, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 4.16/1.69  tff(f_63, axiom, (![A]: ~v1_xboole_0(k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_xboole_0)).
% 4.16/1.69  tff(f_69, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 4.16/1.69  tff(f_54, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 4.16/1.69  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.16/1.69  tff(c_94, plain, (k1_funct_1('#skF_13', '#skF_12')!='#skF_11'), inference(cnfTransformation, [status(thm)], [f_135])).
% 4.16/1.69  tff(c_96, plain, (r2_hidden('#skF_12', '#skF_10')), inference(cnfTransformation, [status(thm)], [f_135])).
% 4.16/1.69  tff(c_100, plain, (v1_funct_2('#skF_13', '#skF_10', k1_tarski('#skF_11'))), inference(cnfTransformation, [status(thm)], [f_135])).
% 4.16/1.69  tff(c_98, plain, (m1_subset_1('#skF_13', k1_zfmisc_1(k2_zfmisc_1('#skF_10', k1_tarski('#skF_11'))))), inference(cnfTransformation, [status(thm)], [f_135])).
% 4.16/1.69  tff(c_486, plain, (![A_154, B_155, C_156]: (k1_relset_1(A_154, B_155, C_156)=k1_relat_1(C_156) | ~m1_subset_1(C_156, k1_zfmisc_1(k2_zfmisc_1(A_154, B_155))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 4.16/1.69  tff(c_490, plain, (k1_relset_1('#skF_10', k1_tarski('#skF_11'), '#skF_13')=k1_relat_1('#skF_13')), inference(resolution, [status(thm)], [c_98, c_486])).
% 4.16/1.69  tff(c_1659, plain, (![B_280, A_281, C_282]: (k1_xboole_0=B_280 | k1_relset_1(A_281, B_280, C_282)=A_281 | ~v1_funct_2(C_282, A_281, B_280) | ~m1_subset_1(C_282, k1_zfmisc_1(k2_zfmisc_1(A_281, B_280))))), inference(cnfTransformation, [status(thm)], [f_124])).
% 4.16/1.69  tff(c_1666, plain, (k1_tarski('#skF_11')=k1_xboole_0 | k1_relset_1('#skF_10', k1_tarski('#skF_11'), '#skF_13')='#skF_10' | ~v1_funct_2('#skF_13', '#skF_10', k1_tarski('#skF_11'))), inference(resolution, [status(thm)], [c_98, c_1659])).
% 4.16/1.69  tff(c_1670, plain, (k1_tarski('#skF_11')=k1_xboole_0 | k1_relat_1('#skF_13')='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_100, c_490, c_1666])).
% 4.16/1.69  tff(c_1671, plain, (k1_relat_1('#skF_13')='#skF_10'), inference(splitLeft, [status(thm)], [c_1670])).
% 4.16/1.69  tff(c_226, plain, (![C_117, A_118, B_119]: (v1_relat_1(C_117) | ~m1_subset_1(C_117, k1_zfmisc_1(k2_zfmisc_1(A_118, B_119))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 4.16/1.69  tff(c_230, plain, (v1_relat_1('#skF_13')), inference(resolution, [status(thm)], [c_98, c_226])).
% 4.16/1.69  tff(c_102, plain, (v1_funct_1('#skF_13')), inference(cnfTransformation, [status(thm)], [f_135])).
% 4.16/1.69  tff(c_1096, plain, (![A_217, D_218]: (r2_hidden(k1_funct_1(A_217, D_218), k2_relat_1(A_217)) | ~r2_hidden(D_218, k1_relat_1(A_217)) | ~v1_funct_1(A_217) | ~v1_relat_1(A_217))), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.16/1.69  tff(c_340, plain, (![A_139, B_140, C_141]: (k2_relset_1(A_139, B_140, C_141)=k2_relat_1(C_141) | ~m1_subset_1(C_141, k1_zfmisc_1(k2_zfmisc_1(A_139, B_140))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 4.16/1.69  tff(c_344, plain, (k2_relset_1('#skF_10', k1_tarski('#skF_11'), '#skF_13')=k2_relat_1('#skF_13')), inference(resolution, [status(thm)], [c_98, c_340])).
% 4.16/1.69  tff(c_499, plain, (![A_161, B_162, C_163]: (m1_subset_1(k2_relset_1(A_161, B_162, C_163), k1_zfmisc_1(B_162)) | ~m1_subset_1(C_163, k1_zfmisc_1(k2_zfmisc_1(A_161, B_162))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 4.16/1.69  tff(c_516, plain, (m1_subset_1(k2_relat_1('#skF_13'), k1_zfmisc_1(k1_tarski('#skF_11'))) | ~m1_subset_1('#skF_13', k1_zfmisc_1(k2_zfmisc_1('#skF_10', k1_tarski('#skF_11'))))), inference(superposition, [status(thm), theory('equality')], [c_344, c_499])).
% 4.16/1.69  tff(c_522, plain, (m1_subset_1(k2_relat_1('#skF_13'), k1_zfmisc_1(k1_tarski('#skF_11')))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_516])).
% 4.16/1.69  tff(c_54, plain, (![A_26, C_28, B_27]: (m1_subset_1(A_26, C_28) | ~m1_subset_1(B_27, k1_zfmisc_1(C_28)) | ~r2_hidden(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.16/1.69  tff(c_551, plain, (![A_26]: (m1_subset_1(A_26, k1_tarski('#skF_11')) | ~r2_hidden(A_26, k2_relat_1('#skF_13')))), inference(resolution, [status(thm)], [c_522, c_54])).
% 4.16/1.69  tff(c_1100, plain, (![D_218]: (m1_subset_1(k1_funct_1('#skF_13', D_218), k1_tarski('#skF_11')) | ~r2_hidden(D_218, k1_relat_1('#skF_13')) | ~v1_funct_1('#skF_13') | ~v1_relat_1('#skF_13'))), inference(resolution, [status(thm)], [c_1096, c_551])).
% 4.16/1.69  tff(c_1108, plain, (![D_219]: (m1_subset_1(k1_funct_1('#skF_13', D_219), k1_tarski('#skF_11')) | ~r2_hidden(D_219, k1_relat_1('#skF_13')))), inference(demodulation, [status(thm), theory('equality')], [c_230, c_102, c_1100])).
% 4.16/1.69  tff(c_50, plain, (![A_23]: (~v1_xboole_0(k1_tarski(A_23)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.16/1.69  tff(c_213, plain, (![A_113, B_114]: (r2_hidden(A_113, B_114) | v1_xboole_0(B_114) | ~m1_subset_1(A_113, B_114))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.16/1.69  tff(c_32, plain, (![C_16, A_12]: (C_16=A_12 | ~r2_hidden(C_16, k1_tarski(A_12)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.16/1.69  tff(c_217, plain, (![A_12, A_113]: (A_12=A_113 | v1_xboole_0(k1_tarski(A_12)) | ~m1_subset_1(A_113, k1_tarski(A_12)))), inference(resolution, [status(thm)], [c_213, c_32])).
% 4.16/1.69  tff(c_223, plain, (![A_12, A_113]: (A_12=A_113 | ~m1_subset_1(A_113, k1_tarski(A_12)))), inference(negUnitSimplification, [status(thm)], [c_50, c_217])).
% 4.16/1.69  tff(c_1112, plain, (![D_219]: (k1_funct_1('#skF_13', D_219)='#skF_11' | ~r2_hidden(D_219, k1_relat_1('#skF_13')))), inference(resolution, [status(thm)], [c_1108, c_223])).
% 4.16/1.69  tff(c_1705, plain, (![D_283]: (k1_funct_1('#skF_13', D_283)='#skF_11' | ~r2_hidden(D_283, '#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_1671, c_1112])).
% 4.16/1.69  tff(c_1724, plain, (k1_funct_1('#skF_13', '#skF_12')='#skF_11'), inference(resolution, [status(thm)], [c_96, c_1705])).
% 4.16/1.69  tff(c_1736, plain, $false, inference(negUnitSimplification, [status(thm)], [c_94, c_1724])).
% 4.16/1.69  tff(c_1737, plain, (k1_tarski('#skF_11')=k1_xboole_0), inference(splitRight, [status(thm)], [c_1670])).
% 4.16/1.69  tff(c_1776, plain, (~v1_xboole_0(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1737, c_50])).
% 4.16/1.69  tff(c_1784, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_1776])).
% 4.16/1.69  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.16/1.69  
% 4.16/1.69  Inference rules
% 4.16/1.69  ----------------------
% 4.16/1.69  #Ref     : 0
% 4.16/1.69  #Sup     : 344
% 4.16/1.69  #Fact    : 2
% 4.16/1.69  #Define  : 0
% 4.16/1.69  #Split   : 10
% 4.16/1.69  #Chain   : 0
% 4.16/1.69  #Close   : 0
% 4.16/1.69  
% 4.16/1.69  Ordering : KBO
% 4.16/1.69  
% 4.16/1.69  Simplification rules
% 4.16/1.69  ----------------------
% 4.16/1.69  #Subsume      : 50
% 4.16/1.69  #Demod        : 193
% 4.16/1.69  #Tautology    : 143
% 4.16/1.69  #SimpNegUnit  : 23
% 4.16/1.69  #BackRed      : 37
% 4.16/1.69  
% 4.16/1.69  #Partial instantiations: 0
% 4.16/1.69  #Strategies tried      : 1
% 4.16/1.69  
% 4.16/1.69  Timing (in seconds)
% 4.16/1.69  ----------------------
% 4.16/1.69  Preprocessing        : 0.38
% 4.16/1.69  Parsing              : 0.18
% 4.16/1.69  CNF conversion       : 0.03
% 4.16/1.69  Main loop            : 0.56
% 4.16/1.69  Inferencing          : 0.20
% 4.16/1.69  Reduction            : 0.17
% 4.16/1.69  Demodulation         : 0.11
% 4.16/1.69  BG Simplification    : 0.04
% 4.16/1.69  Subsumption          : 0.10
% 4.16/1.69  Abstraction          : 0.04
% 4.16/1.69  MUC search           : 0.00
% 4.16/1.69  Cooper               : 0.00
% 4.16/1.69  Total                : 0.97
% 4.16/1.69  Index Insertion      : 0.00
% 4.16/1.69  Index Deletion       : 0.00
% 4.16/1.69  Index Matching       : 0.00
% 4.16/1.69  BG Taut test         : 0.00
%------------------------------------------------------------------------------
