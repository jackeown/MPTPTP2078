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
% DateTime   : Thu Dec  3 10:15:18 EST 2020

% Result     : Theorem 3.70s
% Output     : CNFRefutation 3.70s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 101 expanded)
%              Number of leaves         :   41 (  54 expanded)
%              Depth                    :   10
%              Number of atoms          :  105 ( 187 expanded)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_125,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,k1_tarski(B))
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
       => ( r2_hidden(C,A)
         => k1_funct_1(D,C) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_2)).

tff(f_92,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_71,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_69,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_96,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_114,axiom,(
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

tff(f_81,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v5_relat_1(C,A)
        & v1_funct_1(C) )
     => ( r2_hidden(B,k1_relat_1(C))
       => m1_subset_1(k1_funct_1(C,B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t176_funct_1)).

tff(f_56,axiom,(
    ! [A] : ~ v1_xboole_0(k1_tarski(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_xboole_0)).

tff(f_62,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_49,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_86,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_74,plain,(
    k1_funct_1('#skF_8','#skF_7') != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_78,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_5',k1_tarski('#skF_6')))) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_216,plain,(
    ! [C_90,B_91,A_92] :
      ( v5_relat_1(C_90,B_91)
      | ~ m1_subset_1(C_90,k1_zfmisc_1(k2_zfmisc_1(A_92,B_91))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_220,plain,(
    v5_relat_1('#skF_8',k1_tarski('#skF_6')) ),
    inference(resolution,[status(thm)],[c_78,c_216])).

tff(c_76,plain,(
    r2_hidden('#skF_7','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_50,plain,(
    ! [A_23,B_24] : v1_relat_1(k2_zfmisc_1(A_23,B_24)) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_185,plain,(
    ! [B_73,A_74] :
      ( v1_relat_1(B_73)
      | ~ m1_subset_1(B_73,k1_zfmisc_1(A_74))
      | ~ v1_relat_1(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_188,plain,
    ( v1_relat_1('#skF_8')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_5',k1_tarski('#skF_6'))) ),
    inference(resolution,[status(thm)],[c_78,c_185])).

tff(c_191,plain,(
    v1_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_188])).

tff(c_82,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_80,plain,(
    v1_funct_2('#skF_8','#skF_5',k1_tarski('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_654,plain,(
    ! [A_1649,B_1650,C_1651] :
      ( k1_relset_1(A_1649,B_1650,C_1651) = k1_relat_1(C_1651)
      | ~ m1_subset_1(C_1651,k1_zfmisc_1(k2_zfmisc_1(A_1649,B_1650))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_660,plain,(
    k1_relset_1('#skF_5',k1_tarski('#skF_6'),'#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_78,c_654])).

tff(c_1956,plain,(
    ! [B_2744,A_2745,C_2746] :
      ( k1_xboole_0 = B_2744
      | k1_relset_1(A_2745,B_2744,C_2746) = A_2745
      | ~ v1_funct_2(C_2746,A_2745,B_2744)
      | ~ m1_subset_1(C_2746,k1_zfmisc_1(k2_zfmisc_1(A_2745,B_2744))) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_1961,plain,
    ( k1_tarski('#skF_6') = k1_xboole_0
    | k1_relset_1('#skF_5',k1_tarski('#skF_6'),'#skF_8') = '#skF_5'
    | ~ v1_funct_2('#skF_8','#skF_5',k1_tarski('#skF_6')) ),
    inference(resolution,[status(thm)],[c_78,c_1956])).

tff(c_1964,plain,
    ( k1_tarski('#skF_6') = k1_xboole_0
    | k1_relat_1('#skF_8') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_660,c_1961])).

tff(c_1965,plain,(
    k1_relat_1('#skF_8') = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_1964])).

tff(c_52,plain,(
    ! [C_27,B_26,A_25] :
      ( m1_subset_1(k1_funct_1(C_27,B_26),A_25)
      | ~ r2_hidden(B_26,k1_relat_1(C_27))
      | ~ v1_funct_1(C_27)
      | ~ v5_relat_1(C_27,A_25)
      | ~ v1_relat_1(C_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_1969,plain,(
    ! [B_26,A_25] :
      ( m1_subset_1(k1_funct_1('#skF_8',B_26),A_25)
      | ~ r2_hidden(B_26,'#skF_5')
      | ~ v1_funct_1('#skF_8')
      | ~ v5_relat_1('#skF_8',A_25)
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1965,c_52])).

tff(c_2026,plain,(
    ! [B_2828,A_2829] :
      ( m1_subset_1(k1_funct_1('#skF_8',B_2828),A_2829)
      | ~ r2_hidden(B_2828,'#skF_5')
      | ~ v5_relat_1('#skF_8',A_2829) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_191,c_82,c_1969])).

tff(c_44,plain,(
    ! [A_17] : ~ v1_xboole_0(k1_tarski(A_17)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_154,plain,(
    ! [A_63,B_64] :
      ( r2_hidden(A_63,B_64)
      | v1_xboole_0(B_64)
      | ~ m1_subset_1(A_63,B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_28,plain,(
    ! [C_13,A_9] :
      ( C_13 = A_9
      | ~ r2_hidden(C_13,k1_tarski(A_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_161,plain,(
    ! [A_9,A_63] :
      ( A_9 = A_63
      | v1_xboole_0(k1_tarski(A_9))
      | ~ m1_subset_1(A_63,k1_tarski(A_9)) ) ),
    inference(resolution,[status(thm)],[c_154,c_28])).

tff(c_165,plain,(
    ! [A_9,A_63] :
      ( A_9 = A_63
      | ~ m1_subset_1(A_63,k1_tarski(A_9)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_161])).

tff(c_2087,plain,(
    ! [B_2884,A_2885] :
      ( k1_funct_1('#skF_8',B_2884) = A_2885
      | ~ r2_hidden(B_2884,'#skF_5')
      | ~ v5_relat_1('#skF_8',k1_tarski(A_2885)) ) ),
    inference(resolution,[status(thm)],[c_2026,c_165])).

tff(c_2108,plain,(
    ! [A_2913] :
      ( k1_funct_1('#skF_8','#skF_7') = A_2913
      | ~ v5_relat_1('#skF_8',k1_tarski(A_2913)) ) ),
    inference(resolution,[status(thm)],[c_76,c_2087])).

tff(c_2115,plain,(
    k1_funct_1('#skF_8','#skF_7') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_220,c_2108])).

tff(c_2119,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_2115])).

tff(c_2120,plain,(
    k1_tarski('#skF_6') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_1964])).

tff(c_30,plain,(
    ! [C_13] : r2_hidden(C_13,k1_tarski(C_13)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_105,plain,(
    ! [B_56,A_57] :
      ( ~ r1_tarski(B_56,A_57)
      | ~ r2_hidden(A_57,B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_124,plain,(
    ! [C_13] : ~ r1_tarski(k1_tarski(C_13),C_13) ),
    inference(resolution,[status(thm)],[c_30,c_105])).

tff(c_2156,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_2120,c_124])).

tff(c_2217,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_2156])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n012.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 10:36:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.70/1.66  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.70/1.67  
% 3.70/1.67  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.70/1.67  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_3 > #skF_5 > #skF_2 > #skF_6 > #skF_8 > #skF_1 > #skF_4
% 3.70/1.67  
% 3.70/1.67  %Foreground sorts:
% 3.70/1.67  
% 3.70/1.67  
% 3.70/1.67  %Background operators:
% 3.70/1.67  
% 3.70/1.67  
% 3.70/1.67  %Foreground operators:
% 3.70/1.67  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.70/1.67  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.70/1.67  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.70/1.67  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.70/1.67  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.70/1.67  tff('#skF_7', type, '#skF_7': $i).
% 3.70/1.67  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.70/1.67  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.70/1.67  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.70/1.67  tff('#skF_5', type, '#skF_5': $i).
% 3.70/1.67  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.70/1.67  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 3.70/1.67  tff('#skF_6', type, '#skF_6': $i).
% 3.70/1.67  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.70/1.67  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.70/1.67  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.70/1.67  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.70/1.67  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.70/1.67  tff('#skF_8', type, '#skF_8': $i).
% 3.70/1.67  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.70/1.67  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.70/1.67  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.70/1.67  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.70/1.67  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.70/1.67  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 3.70/1.67  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.70/1.67  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.70/1.67  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.70/1.67  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.70/1.67  
% 3.70/1.68  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.70/1.68  tff(f_125, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_funct_2)).
% 3.70/1.68  tff(f_92, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.70/1.68  tff(f_71, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.70/1.68  tff(f_69, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.70/1.68  tff(f_96, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.70/1.68  tff(f_114, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 3.70/1.68  tff(f_81, axiom, (![A, B, C]: (((v1_relat_1(C) & v5_relat_1(C, A)) & v1_funct_1(C)) => (r2_hidden(B, k1_relat_1(C)) => m1_subset_1(k1_funct_1(C, B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t176_funct_1)).
% 3.70/1.68  tff(f_56, axiom, (![A]: ~v1_xboole_0(k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_xboole_0)).
% 3.70/1.68  tff(f_62, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 3.70/1.68  tff(f_49, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 3.70/1.68  tff(f_86, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 3.70/1.68  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.70/1.68  tff(c_74, plain, (k1_funct_1('#skF_8', '#skF_7')!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_125])).
% 3.70/1.68  tff(c_78, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_5', k1_tarski('#skF_6'))))), inference(cnfTransformation, [status(thm)], [f_125])).
% 3.70/1.68  tff(c_216, plain, (![C_90, B_91, A_92]: (v5_relat_1(C_90, B_91) | ~m1_subset_1(C_90, k1_zfmisc_1(k2_zfmisc_1(A_92, B_91))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.70/1.68  tff(c_220, plain, (v5_relat_1('#skF_8', k1_tarski('#skF_6'))), inference(resolution, [status(thm)], [c_78, c_216])).
% 3.70/1.68  tff(c_76, plain, (r2_hidden('#skF_7', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_125])).
% 3.70/1.68  tff(c_50, plain, (![A_23, B_24]: (v1_relat_1(k2_zfmisc_1(A_23, B_24)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.70/1.68  tff(c_185, plain, (![B_73, A_74]: (v1_relat_1(B_73) | ~m1_subset_1(B_73, k1_zfmisc_1(A_74)) | ~v1_relat_1(A_74))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.70/1.68  tff(c_188, plain, (v1_relat_1('#skF_8') | ~v1_relat_1(k2_zfmisc_1('#skF_5', k1_tarski('#skF_6')))), inference(resolution, [status(thm)], [c_78, c_185])).
% 3.70/1.68  tff(c_191, plain, (v1_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_188])).
% 3.70/1.68  tff(c_82, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_125])).
% 3.70/1.68  tff(c_80, plain, (v1_funct_2('#skF_8', '#skF_5', k1_tarski('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_125])).
% 3.70/1.68  tff(c_654, plain, (![A_1649, B_1650, C_1651]: (k1_relset_1(A_1649, B_1650, C_1651)=k1_relat_1(C_1651) | ~m1_subset_1(C_1651, k1_zfmisc_1(k2_zfmisc_1(A_1649, B_1650))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.70/1.68  tff(c_660, plain, (k1_relset_1('#skF_5', k1_tarski('#skF_6'), '#skF_8')=k1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_78, c_654])).
% 3.70/1.68  tff(c_1956, plain, (![B_2744, A_2745, C_2746]: (k1_xboole_0=B_2744 | k1_relset_1(A_2745, B_2744, C_2746)=A_2745 | ~v1_funct_2(C_2746, A_2745, B_2744) | ~m1_subset_1(C_2746, k1_zfmisc_1(k2_zfmisc_1(A_2745, B_2744))))), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.70/1.68  tff(c_1961, plain, (k1_tarski('#skF_6')=k1_xboole_0 | k1_relset_1('#skF_5', k1_tarski('#skF_6'), '#skF_8')='#skF_5' | ~v1_funct_2('#skF_8', '#skF_5', k1_tarski('#skF_6'))), inference(resolution, [status(thm)], [c_78, c_1956])).
% 3.70/1.68  tff(c_1964, plain, (k1_tarski('#skF_6')=k1_xboole_0 | k1_relat_1('#skF_8')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_80, c_660, c_1961])).
% 3.70/1.68  tff(c_1965, plain, (k1_relat_1('#skF_8')='#skF_5'), inference(splitLeft, [status(thm)], [c_1964])).
% 3.70/1.68  tff(c_52, plain, (![C_27, B_26, A_25]: (m1_subset_1(k1_funct_1(C_27, B_26), A_25) | ~r2_hidden(B_26, k1_relat_1(C_27)) | ~v1_funct_1(C_27) | ~v5_relat_1(C_27, A_25) | ~v1_relat_1(C_27))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.70/1.68  tff(c_1969, plain, (![B_26, A_25]: (m1_subset_1(k1_funct_1('#skF_8', B_26), A_25) | ~r2_hidden(B_26, '#skF_5') | ~v1_funct_1('#skF_8') | ~v5_relat_1('#skF_8', A_25) | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_1965, c_52])).
% 3.70/1.68  tff(c_2026, plain, (![B_2828, A_2829]: (m1_subset_1(k1_funct_1('#skF_8', B_2828), A_2829) | ~r2_hidden(B_2828, '#skF_5') | ~v5_relat_1('#skF_8', A_2829))), inference(demodulation, [status(thm), theory('equality')], [c_191, c_82, c_1969])).
% 3.70/1.68  tff(c_44, plain, (![A_17]: (~v1_xboole_0(k1_tarski(A_17)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.70/1.68  tff(c_154, plain, (![A_63, B_64]: (r2_hidden(A_63, B_64) | v1_xboole_0(B_64) | ~m1_subset_1(A_63, B_64))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.70/1.68  tff(c_28, plain, (![C_13, A_9]: (C_13=A_9 | ~r2_hidden(C_13, k1_tarski(A_9)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.70/1.68  tff(c_161, plain, (![A_9, A_63]: (A_9=A_63 | v1_xboole_0(k1_tarski(A_9)) | ~m1_subset_1(A_63, k1_tarski(A_9)))), inference(resolution, [status(thm)], [c_154, c_28])).
% 3.70/1.68  tff(c_165, plain, (![A_9, A_63]: (A_9=A_63 | ~m1_subset_1(A_63, k1_tarski(A_9)))), inference(negUnitSimplification, [status(thm)], [c_44, c_161])).
% 3.70/1.68  tff(c_2087, plain, (![B_2884, A_2885]: (k1_funct_1('#skF_8', B_2884)=A_2885 | ~r2_hidden(B_2884, '#skF_5') | ~v5_relat_1('#skF_8', k1_tarski(A_2885)))), inference(resolution, [status(thm)], [c_2026, c_165])).
% 3.70/1.68  tff(c_2108, plain, (![A_2913]: (k1_funct_1('#skF_8', '#skF_7')=A_2913 | ~v5_relat_1('#skF_8', k1_tarski(A_2913)))), inference(resolution, [status(thm)], [c_76, c_2087])).
% 3.70/1.68  tff(c_2115, plain, (k1_funct_1('#skF_8', '#skF_7')='#skF_6'), inference(resolution, [status(thm)], [c_220, c_2108])).
% 3.70/1.68  tff(c_2119, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74, c_2115])).
% 3.70/1.68  tff(c_2120, plain, (k1_tarski('#skF_6')=k1_xboole_0), inference(splitRight, [status(thm)], [c_1964])).
% 3.70/1.68  tff(c_30, plain, (![C_13]: (r2_hidden(C_13, k1_tarski(C_13)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.70/1.68  tff(c_105, plain, (![B_56, A_57]: (~r1_tarski(B_56, A_57) | ~r2_hidden(A_57, B_56))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.70/1.68  tff(c_124, plain, (![C_13]: (~r1_tarski(k1_tarski(C_13), C_13))), inference(resolution, [status(thm)], [c_30, c_105])).
% 3.70/1.68  tff(c_2156, plain, (~r1_tarski(k1_xboole_0, '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_2120, c_124])).
% 3.70/1.68  tff(c_2217, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_2156])).
% 3.70/1.68  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.70/1.68  
% 3.70/1.68  Inference rules
% 3.70/1.68  ----------------------
% 3.70/1.68  #Ref     : 0
% 3.70/1.68  #Sup     : 303
% 3.70/1.68  #Fact    : 0
% 3.70/1.68  #Define  : 0
% 3.70/1.68  #Split   : 9
% 3.70/1.68  #Chain   : 0
% 3.70/1.68  #Close   : 0
% 3.70/1.68  
% 3.70/1.68  Ordering : KBO
% 3.70/1.68  
% 3.70/1.68  Simplification rules
% 3.70/1.68  ----------------------
% 3.70/1.68  #Subsume      : 64
% 3.70/1.68  #Demod        : 69
% 3.70/1.68  #Tautology    : 91
% 3.70/1.68  #SimpNegUnit  : 6
% 3.70/1.68  #BackRed      : 6
% 3.70/1.68  
% 3.70/1.68  #Partial instantiations: 1734
% 3.70/1.68  #Strategies tried      : 1
% 3.70/1.68  
% 3.70/1.68  Timing (in seconds)
% 3.70/1.68  ----------------------
% 4.01/1.69  Preprocessing        : 0.35
% 4.01/1.69  Parsing              : 0.17
% 4.01/1.69  CNF conversion       : 0.03
% 4.01/1.69  Main loop            : 0.57
% 4.01/1.69  Inferencing          : 0.26
% 4.01/1.69  Reduction            : 0.15
% 4.01/1.69  Demodulation         : 0.10
% 4.01/1.69  BG Simplification    : 0.03
% 4.01/1.69  Subsumption          : 0.09
% 4.01/1.69  Abstraction          : 0.03
% 4.01/1.69  MUC search           : 0.00
% 4.01/1.69  Cooper               : 0.00
% 4.01/1.69  Total                : 0.95
% 4.01/1.69  Index Insertion      : 0.00
% 4.01/1.69  Index Deletion       : 0.00
% 4.01/1.69  Index Matching       : 0.00
% 4.01/1.69  BG Taut test         : 0.00
%------------------------------------------------------------------------------
