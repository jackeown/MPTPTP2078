%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:08 EST 2020

% Result     : Theorem 3.83s
% Output     : CNFRefutation 3.83s
% Verified   : 
% Statistics : Number of formulae       :   74 (  98 expanded)
%              Number of leaves         :   40 (  53 expanded)
%              Depth                    :   10
%              Number of atoms          :   99 ( 181 expanded)
%              Number of equality atoms :   27 (  54 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_3 > #skF_5 > #skF_2 > #skF_6 > #skF_8 > #skF_1 > #skF_4

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_120,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,k1_tarski(B))
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
       => ( r2_hidden(C,A)
         => k1_funct_1(D,C) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_2)).

tff(f_87,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_91,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_109,axiom,(
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

tff(f_72,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v5_relat_1(C,A)
        & v1_funct_1(C) )
     => ( r2_hidden(B,k1_relat_1(C))
       => m1_subset_1(k1_funct_1(C,B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t176_funct_1)).

tff(f_56,axiom,(
    ! [A] : ~ v1_xboole_0(k1_tarski(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_xboole_0)).

tff(f_62,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_49,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_77,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_72,plain,(
    k1_funct_1('#skF_8','#skF_7') != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_76,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_5',k1_tarski('#skF_6')))) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_211,plain,(
    ! [C_87,B_88,A_89] :
      ( v5_relat_1(C_87,B_88)
      | ~ m1_subset_1(C_87,k1_zfmisc_1(k2_zfmisc_1(A_89,B_88))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_215,plain,(
    v5_relat_1('#skF_8',k1_tarski('#skF_6')) ),
    inference(resolution,[status(thm)],[c_76,c_211])).

tff(c_74,plain,(
    r2_hidden('#skF_7','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_193,plain,(
    ! [C_76,A_77,B_78] :
      ( v1_relat_1(C_76)
      | ~ m1_subset_1(C_76,k1_zfmisc_1(k2_zfmisc_1(A_77,B_78))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_197,plain,(
    v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_76,c_193])).

tff(c_80,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_78,plain,(
    v1_funct_2('#skF_8','#skF_5',k1_tarski('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_663,plain,(
    ! [A_1567,B_1568,C_1569] :
      ( k1_relset_1(A_1567,B_1568,C_1569) = k1_relat_1(C_1569)
      | ~ m1_subset_1(C_1569,k1_zfmisc_1(k2_zfmisc_1(A_1567,B_1568))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_669,plain,(
    k1_relset_1('#skF_5',k1_tarski('#skF_6'),'#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_76,c_663])).

tff(c_1919,plain,(
    ! [B_2550,A_2551,C_2552] :
      ( k1_xboole_0 = B_2550
      | k1_relset_1(A_2551,B_2550,C_2552) = A_2551
      | ~ v1_funct_2(C_2552,A_2551,B_2550)
      | ~ m1_subset_1(C_2552,k1_zfmisc_1(k2_zfmisc_1(A_2551,B_2550))) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_1924,plain,
    ( k1_tarski('#skF_6') = k1_xboole_0
    | k1_relset_1('#skF_5',k1_tarski('#skF_6'),'#skF_8') = '#skF_5'
    | ~ v1_funct_2('#skF_8','#skF_5',k1_tarski('#skF_6')) ),
    inference(resolution,[status(thm)],[c_76,c_1919])).

tff(c_1927,plain,
    ( k1_tarski('#skF_6') = k1_xboole_0
    | k1_relat_1('#skF_8') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_669,c_1924])).

tff(c_1928,plain,(
    k1_relat_1('#skF_8') = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_1927])).

tff(c_48,plain,(
    ! [C_22,B_21,A_20] :
      ( m1_subset_1(k1_funct_1(C_22,B_21),A_20)
      | ~ r2_hidden(B_21,k1_relat_1(C_22))
      | ~ v1_funct_1(C_22)
      | ~ v5_relat_1(C_22,A_20)
      | ~ v1_relat_1(C_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_1932,plain,(
    ! [B_21,A_20] :
      ( m1_subset_1(k1_funct_1('#skF_8',B_21),A_20)
      | ~ r2_hidden(B_21,'#skF_5')
      | ~ v1_funct_1('#skF_8')
      | ~ v5_relat_1('#skF_8',A_20)
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1928,c_48])).

tff(c_1988,plain,(
    ! [B_2661,A_2662] :
      ( m1_subset_1(k1_funct_1('#skF_8',B_2661),A_2662)
      | ~ r2_hidden(B_2661,'#skF_5')
      | ~ v5_relat_1('#skF_8',A_2662) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_197,c_80,c_1932])).

tff(c_44,plain,(
    ! [A_17] : ~ v1_xboole_0(k1_tarski(A_17)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_181,plain,(
    ! [A_74,B_75] :
      ( r2_hidden(A_74,B_75)
      | v1_xboole_0(B_75)
      | ~ m1_subset_1(A_74,B_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_28,plain,(
    ! [C_13,A_9] :
      ( C_13 = A_9
      | ~ r2_hidden(C_13,k1_tarski(A_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_188,plain,(
    ! [A_9,A_74] :
      ( A_9 = A_74
      | v1_xboole_0(k1_tarski(A_9))
      | ~ m1_subset_1(A_74,k1_tarski(A_9)) ) ),
    inference(resolution,[status(thm)],[c_181,c_28])).

tff(c_192,plain,(
    ! [A_9,A_74] :
      ( A_9 = A_74
      | ~ m1_subset_1(A_74,k1_tarski(A_9)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_188])).

tff(c_2049,plain,(
    ! [B_2717,A_2718] :
      ( k1_funct_1('#skF_8',B_2717) = A_2718
      | ~ r2_hidden(B_2717,'#skF_5')
      | ~ v5_relat_1('#skF_8',k1_tarski(A_2718)) ) ),
    inference(resolution,[status(thm)],[c_1988,c_192])).

tff(c_2067,plain,(
    ! [A_2746] :
      ( k1_funct_1('#skF_8','#skF_7') = A_2746
      | ~ v5_relat_1('#skF_8',k1_tarski(A_2746)) ) ),
    inference(resolution,[status(thm)],[c_74,c_2049])).

tff(c_2074,plain,(
    k1_funct_1('#skF_8','#skF_7') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_215,c_2067])).

tff(c_2078,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_2074])).

tff(c_2079,plain,(
    k1_tarski('#skF_6') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_1927])).

tff(c_30,plain,(
    ! [C_13] : r2_hidden(C_13,k1_tarski(C_13)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_99,plain,(
    ! [B_43,A_44] :
      ( ~ r1_tarski(B_43,A_44)
      | ~ r2_hidden(A_44,B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_106,plain,(
    ! [C_13] : ~ r1_tarski(k1_tarski(C_13),C_13) ),
    inference(resolution,[status(thm)],[c_30,c_99])).

tff(c_2115,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_2079,c_106])).

tff(c_2176,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_2115])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:11:17 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.83/1.65  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.83/1.65  
% 3.83/1.65  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.83/1.66  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_3 > #skF_5 > #skF_2 > #skF_6 > #skF_8 > #skF_1 > #skF_4
% 3.83/1.66  
% 3.83/1.66  %Foreground sorts:
% 3.83/1.66  
% 3.83/1.66  
% 3.83/1.66  %Background operators:
% 3.83/1.66  
% 3.83/1.66  
% 3.83/1.66  %Foreground operators:
% 3.83/1.66  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.83/1.66  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.83/1.66  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.83/1.66  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.83/1.66  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.83/1.66  tff('#skF_7', type, '#skF_7': $i).
% 3.83/1.66  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.83/1.66  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.83/1.66  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.83/1.66  tff('#skF_5', type, '#skF_5': $i).
% 3.83/1.66  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.83/1.66  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 3.83/1.66  tff('#skF_6', type, '#skF_6': $i).
% 3.83/1.66  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.83/1.66  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.83/1.66  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.83/1.66  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.83/1.66  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.83/1.66  tff('#skF_8', type, '#skF_8': $i).
% 3.83/1.66  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.83/1.66  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.83/1.66  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.83/1.66  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.83/1.66  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.83/1.66  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 3.83/1.66  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.83/1.66  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.83/1.66  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.83/1.66  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.83/1.66  
% 3.83/1.67  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.83/1.67  tff(f_120, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_funct_2)).
% 3.83/1.67  tff(f_87, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.83/1.67  tff(f_81, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.83/1.67  tff(f_91, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.83/1.67  tff(f_109, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 3.83/1.67  tff(f_72, axiom, (![A, B, C]: (((v1_relat_1(C) & v5_relat_1(C, A)) & v1_funct_1(C)) => (r2_hidden(B, k1_relat_1(C)) => m1_subset_1(k1_funct_1(C, B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t176_funct_1)).
% 3.83/1.67  tff(f_56, axiom, (![A]: ~v1_xboole_0(k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_xboole_0)).
% 3.83/1.67  tff(f_62, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 3.83/1.67  tff(f_49, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 3.83/1.67  tff(f_77, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 3.83/1.67  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.83/1.67  tff(c_72, plain, (k1_funct_1('#skF_8', '#skF_7')!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_120])).
% 3.83/1.67  tff(c_76, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_5', k1_tarski('#skF_6'))))), inference(cnfTransformation, [status(thm)], [f_120])).
% 3.83/1.67  tff(c_211, plain, (![C_87, B_88, A_89]: (v5_relat_1(C_87, B_88) | ~m1_subset_1(C_87, k1_zfmisc_1(k2_zfmisc_1(A_89, B_88))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.83/1.67  tff(c_215, plain, (v5_relat_1('#skF_8', k1_tarski('#skF_6'))), inference(resolution, [status(thm)], [c_76, c_211])).
% 3.83/1.67  tff(c_74, plain, (r2_hidden('#skF_7', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_120])).
% 3.83/1.67  tff(c_193, plain, (![C_76, A_77, B_78]: (v1_relat_1(C_76) | ~m1_subset_1(C_76, k1_zfmisc_1(k2_zfmisc_1(A_77, B_78))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.83/1.67  tff(c_197, plain, (v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_76, c_193])).
% 3.83/1.67  tff(c_80, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_120])).
% 3.83/1.67  tff(c_78, plain, (v1_funct_2('#skF_8', '#skF_5', k1_tarski('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_120])).
% 3.83/1.67  tff(c_663, plain, (![A_1567, B_1568, C_1569]: (k1_relset_1(A_1567, B_1568, C_1569)=k1_relat_1(C_1569) | ~m1_subset_1(C_1569, k1_zfmisc_1(k2_zfmisc_1(A_1567, B_1568))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.83/1.67  tff(c_669, plain, (k1_relset_1('#skF_5', k1_tarski('#skF_6'), '#skF_8')=k1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_76, c_663])).
% 3.83/1.67  tff(c_1919, plain, (![B_2550, A_2551, C_2552]: (k1_xboole_0=B_2550 | k1_relset_1(A_2551, B_2550, C_2552)=A_2551 | ~v1_funct_2(C_2552, A_2551, B_2550) | ~m1_subset_1(C_2552, k1_zfmisc_1(k2_zfmisc_1(A_2551, B_2550))))), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.83/1.67  tff(c_1924, plain, (k1_tarski('#skF_6')=k1_xboole_0 | k1_relset_1('#skF_5', k1_tarski('#skF_6'), '#skF_8')='#skF_5' | ~v1_funct_2('#skF_8', '#skF_5', k1_tarski('#skF_6'))), inference(resolution, [status(thm)], [c_76, c_1919])).
% 3.83/1.67  tff(c_1927, plain, (k1_tarski('#skF_6')=k1_xboole_0 | k1_relat_1('#skF_8')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_78, c_669, c_1924])).
% 3.83/1.67  tff(c_1928, plain, (k1_relat_1('#skF_8')='#skF_5'), inference(splitLeft, [status(thm)], [c_1927])).
% 3.83/1.67  tff(c_48, plain, (![C_22, B_21, A_20]: (m1_subset_1(k1_funct_1(C_22, B_21), A_20) | ~r2_hidden(B_21, k1_relat_1(C_22)) | ~v1_funct_1(C_22) | ~v5_relat_1(C_22, A_20) | ~v1_relat_1(C_22))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.83/1.67  tff(c_1932, plain, (![B_21, A_20]: (m1_subset_1(k1_funct_1('#skF_8', B_21), A_20) | ~r2_hidden(B_21, '#skF_5') | ~v1_funct_1('#skF_8') | ~v5_relat_1('#skF_8', A_20) | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_1928, c_48])).
% 3.83/1.67  tff(c_1988, plain, (![B_2661, A_2662]: (m1_subset_1(k1_funct_1('#skF_8', B_2661), A_2662) | ~r2_hidden(B_2661, '#skF_5') | ~v5_relat_1('#skF_8', A_2662))), inference(demodulation, [status(thm), theory('equality')], [c_197, c_80, c_1932])).
% 3.83/1.67  tff(c_44, plain, (![A_17]: (~v1_xboole_0(k1_tarski(A_17)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.83/1.67  tff(c_181, plain, (![A_74, B_75]: (r2_hidden(A_74, B_75) | v1_xboole_0(B_75) | ~m1_subset_1(A_74, B_75))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.83/1.67  tff(c_28, plain, (![C_13, A_9]: (C_13=A_9 | ~r2_hidden(C_13, k1_tarski(A_9)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.83/1.67  tff(c_188, plain, (![A_9, A_74]: (A_9=A_74 | v1_xboole_0(k1_tarski(A_9)) | ~m1_subset_1(A_74, k1_tarski(A_9)))), inference(resolution, [status(thm)], [c_181, c_28])).
% 3.83/1.67  tff(c_192, plain, (![A_9, A_74]: (A_9=A_74 | ~m1_subset_1(A_74, k1_tarski(A_9)))), inference(negUnitSimplification, [status(thm)], [c_44, c_188])).
% 3.83/1.67  tff(c_2049, plain, (![B_2717, A_2718]: (k1_funct_1('#skF_8', B_2717)=A_2718 | ~r2_hidden(B_2717, '#skF_5') | ~v5_relat_1('#skF_8', k1_tarski(A_2718)))), inference(resolution, [status(thm)], [c_1988, c_192])).
% 3.83/1.67  tff(c_2067, plain, (![A_2746]: (k1_funct_1('#skF_8', '#skF_7')=A_2746 | ~v5_relat_1('#skF_8', k1_tarski(A_2746)))), inference(resolution, [status(thm)], [c_74, c_2049])).
% 3.83/1.67  tff(c_2074, plain, (k1_funct_1('#skF_8', '#skF_7')='#skF_6'), inference(resolution, [status(thm)], [c_215, c_2067])).
% 3.83/1.67  tff(c_2078, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_2074])).
% 3.83/1.67  tff(c_2079, plain, (k1_tarski('#skF_6')=k1_xboole_0), inference(splitRight, [status(thm)], [c_1927])).
% 3.83/1.67  tff(c_30, plain, (![C_13]: (r2_hidden(C_13, k1_tarski(C_13)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.83/1.67  tff(c_99, plain, (![B_43, A_44]: (~r1_tarski(B_43, A_44) | ~r2_hidden(A_44, B_43))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.83/1.67  tff(c_106, plain, (![C_13]: (~r1_tarski(k1_tarski(C_13), C_13))), inference(resolution, [status(thm)], [c_30, c_99])).
% 3.83/1.67  tff(c_2115, plain, (~r1_tarski(k1_xboole_0, '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_2079, c_106])).
% 3.83/1.67  tff(c_2176, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_2115])).
% 3.83/1.67  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.83/1.67  
% 3.83/1.67  Inference rules
% 3.83/1.67  ----------------------
% 3.83/1.67  #Ref     : 0
% 3.83/1.67  #Sup     : 308
% 3.83/1.67  #Fact    : 0
% 3.83/1.67  #Define  : 0
% 3.83/1.67  #Split   : 9
% 3.83/1.67  #Chain   : 0
% 3.83/1.67  #Close   : 0
% 3.83/1.67  
% 3.83/1.67  Ordering : KBO
% 3.83/1.67  
% 3.83/1.67  Simplification rules
% 3.83/1.67  ----------------------
% 3.83/1.67  #Subsume      : 63
% 3.83/1.67  #Demod        : 68
% 3.83/1.67  #Tautology    : 96
% 3.83/1.67  #SimpNegUnit  : 6
% 3.83/1.67  #BackRed      : 6
% 3.83/1.67  
% 3.83/1.67  #Partial instantiations: 1632
% 3.83/1.67  #Strategies tried      : 1
% 3.83/1.67  
% 3.83/1.67  Timing (in seconds)
% 3.83/1.67  ----------------------
% 3.83/1.67  Preprocessing        : 0.36
% 3.83/1.67  Parsing              : 0.18
% 3.83/1.67  CNF conversion       : 0.03
% 3.83/1.67  Main loop            : 0.55
% 3.83/1.67  Inferencing          : 0.25
% 3.83/1.67  Reduction            : 0.14
% 3.83/1.67  Demodulation         : 0.09
% 3.83/1.67  BG Simplification    : 0.03
% 3.83/1.67  Subsumption          : 0.09
% 3.83/1.67  Abstraction          : 0.03
% 3.83/1.67  MUC search           : 0.00
% 3.83/1.67  Cooper               : 0.00
% 3.83/1.67  Total                : 0.93
% 3.83/1.67  Index Insertion      : 0.00
% 3.83/1.67  Index Deletion       : 0.00
% 3.83/1.67  Index Matching       : 0.00
% 3.83/1.67  BG Taut test         : 0.00
%------------------------------------------------------------------------------
