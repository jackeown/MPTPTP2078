%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:09 EST 2020

% Result     : Theorem 3.10s
% Output     : CNFRefutation 3.10s
% Verified   : 
% Statistics : Number of formulae       :   75 (  99 expanded)
%              Number of leaves         :   41 (  54 expanded)
%              Depth                    :   10
%              Number of atoms          :   99 ( 181 expanded)
%              Number of equality atoms :   27 (  54 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_8 > #skF_2 > #skF_1

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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

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

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i * $i ) > $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

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

tff(f_86,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

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

tff(f_77,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v5_relat_1(C,A)
        & v1_funct_1(C) )
     => ( r2_hidden(B,k1_relat_1(C))
       => m1_subset_1(k1_funct_1(C,B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t176_funct_1)).

tff(f_43,axiom,(
    ! [A] : ~ v1_xboole_0(k1_tarski(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_xboole_0)).

tff(f_67,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_34,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_82,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_80,plain,(
    k1_funct_1('#skF_8','#skF_7') != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_84,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_5',k1_tarski('#skF_6')))) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_178,plain,(
    ! [C_96,B_97,A_98] :
      ( v5_relat_1(C_96,B_97)
      | ~ m1_subset_1(C_96,k1_zfmisc_1(k2_zfmisc_1(A_98,B_97))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_182,plain,(
    v5_relat_1('#skF_8',k1_tarski('#skF_6')) ),
    inference(resolution,[status(thm)],[c_84,c_178])).

tff(c_82,plain,(
    r2_hidden('#skF_7','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_147,plain,(
    ! [C_72,A_73,B_74] :
      ( v1_relat_1(C_72)
      | ~ m1_subset_1(C_72,k1_zfmisc_1(k2_zfmisc_1(A_73,B_74))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_151,plain,(
    v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_84,c_147])).

tff(c_88,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_86,plain,(
    v1_funct_2('#skF_8','#skF_5',k1_tarski('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_299,plain,(
    ! [A_135,B_136,C_137] :
      ( k1_relset_1(A_135,B_136,C_137) = k1_relat_1(C_137)
      | ~ m1_subset_1(C_137,k1_zfmisc_1(k2_zfmisc_1(A_135,B_136))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_303,plain,(
    k1_relset_1('#skF_5',k1_tarski('#skF_6'),'#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_84,c_299])).

tff(c_603,plain,(
    ! [B_183,A_184,C_185] :
      ( k1_xboole_0 = B_183
      | k1_relset_1(A_184,B_183,C_185) = A_184
      | ~ v1_funct_2(C_185,A_184,B_183)
      | ~ m1_subset_1(C_185,k1_zfmisc_1(k2_zfmisc_1(A_184,B_183))) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_606,plain,
    ( k1_tarski('#skF_6') = k1_xboole_0
    | k1_relset_1('#skF_5',k1_tarski('#skF_6'),'#skF_8') = '#skF_5'
    | ~ v1_funct_2('#skF_8','#skF_5',k1_tarski('#skF_6')) ),
    inference(resolution,[status(thm)],[c_84,c_603])).

tff(c_609,plain,
    ( k1_tarski('#skF_6') = k1_xboole_0
    | k1_relat_1('#skF_8') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_303,c_606])).

tff(c_610,plain,(
    k1_relat_1('#skF_8') = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_609])).

tff(c_56,plain,(
    ! [C_26,B_25,A_24] :
      ( m1_subset_1(k1_funct_1(C_26,B_25),A_24)
      | ~ r2_hidden(B_25,k1_relat_1(C_26))
      | ~ v1_funct_1(C_26)
      | ~ v5_relat_1(C_26,A_24)
      | ~ v1_relat_1(C_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_614,plain,(
    ! [B_25,A_24] :
      ( m1_subset_1(k1_funct_1('#skF_8',B_25),A_24)
      | ~ r2_hidden(B_25,'#skF_5')
      | ~ v1_funct_1('#skF_8')
      | ~ v5_relat_1('#skF_8',A_24)
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_610,c_56])).

tff(c_630,plain,(
    ! [B_189,A_190] :
      ( m1_subset_1(k1_funct_1('#skF_8',B_189),A_190)
      | ~ r2_hidden(B_189,'#skF_5')
      | ~ v5_relat_1('#skF_8',A_190) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_151,c_88,c_614])).

tff(c_22,plain,(
    ! [A_13] : ~ v1_xboole_0(k1_tarski(A_13)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_155,plain,(
    ! [A_87,B_88] :
      ( r2_hidden(A_87,B_88)
      | v1_xboole_0(B_88)
      | ~ m1_subset_1(A_87,B_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_4,plain,(
    ! [C_6,A_2] :
      ( C_6 = A_2
      | ~ r2_hidden(C_6,k1_tarski(A_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_162,plain,(
    ! [A_87,A_2] :
      ( A_87 = A_2
      | v1_xboole_0(k1_tarski(A_2))
      | ~ m1_subset_1(A_87,k1_tarski(A_2)) ) ),
    inference(resolution,[status(thm)],[c_155,c_4])).

tff(c_166,plain,(
    ! [A_87,A_2] :
      ( A_87 = A_2
      | ~ m1_subset_1(A_87,k1_tarski(A_2)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_162])).

tff(c_692,plain,(
    ! [B_191,A_192] :
      ( k1_funct_1('#skF_8',B_191) = A_192
      | ~ r2_hidden(B_191,'#skF_5')
      | ~ v5_relat_1('#skF_8',k1_tarski(A_192)) ) ),
    inference(resolution,[status(thm)],[c_630,c_166])).

tff(c_708,plain,(
    ! [A_193] :
      ( k1_funct_1('#skF_8','#skF_7') = A_193
      | ~ v5_relat_1('#skF_8',k1_tarski(A_193)) ) ),
    inference(resolution,[status(thm)],[c_82,c_692])).

tff(c_711,plain,(
    k1_funct_1('#skF_8','#skF_7') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_182,c_708])).

tff(c_715,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_711])).

tff(c_716,plain,(
    k1_tarski('#skF_6') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_609])).

tff(c_6,plain,(
    ! [C_6] : r2_hidden(C_6,k1_tarski(C_6)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_107,plain,(
    ! [B_47,A_48] :
      ( ~ r1_tarski(B_47,A_48)
      | ~ r2_hidden(A_48,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_114,plain,(
    ! [C_6] : ~ r1_tarski(k1_tarski(C_6),C_6) ),
    inference(resolution,[status(thm)],[c_6,c_107])).

tff(c_743,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_716,c_114])).

tff(c_761,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_743])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 19:57:20 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.10/1.49  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.10/1.50  
% 3.10/1.50  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.10/1.50  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_8 > #skF_2 > #skF_1
% 3.10/1.50  
% 3.10/1.50  %Foreground sorts:
% 3.10/1.50  
% 3.10/1.50  
% 3.10/1.50  %Background operators:
% 3.10/1.50  
% 3.10/1.50  
% 3.10/1.50  %Foreground operators:
% 3.10/1.50  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.10/1.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.10/1.50  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.10/1.50  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.10/1.50  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.10/1.50  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i * $i) > $i).
% 3.10/1.50  tff('#skF_7', type, '#skF_7': $i).
% 3.10/1.50  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.10/1.50  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.10/1.50  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.10/1.50  tff('#skF_5', type, '#skF_5': $i).
% 3.10/1.50  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.10/1.50  tff('#skF_6', type, '#skF_6': $i).
% 3.10/1.50  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.10/1.50  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.10/1.50  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.10/1.50  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.10/1.50  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.10/1.50  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i * $i) > $i).
% 3.10/1.50  tff('#skF_8', type, '#skF_8': $i).
% 3.10/1.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.10/1.50  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.10/1.50  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.10/1.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.10/1.50  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.10/1.50  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.10/1.50  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.10/1.50  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.10/1.50  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.10/1.50  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.10/1.50  
% 3.10/1.51  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.10/1.51  tff(f_125, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_funct_2)).
% 3.10/1.51  tff(f_92, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.10/1.51  tff(f_86, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.10/1.51  tff(f_96, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.10/1.51  tff(f_114, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 3.10/1.51  tff(f_77, axiom, (![A, B, C]: (((v1_relat_1(C) & v5_relat_1(C, A)) & v1_funct_1(C)) => (r2_hidden(B, k1_relat_1(C)) => m1_subset_1(k1_funct_1(C, B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t176_funct_1)).
% 3.10/1.51  tff(f_43, axiom, (![A]: ~v1_xboole_0(k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_xboole_0)).
% 3.10/1.51  tff(f_67, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 3.10/1.51  tff(f_34, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 3.10/1.51  tff(f_82, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 3.10/1.51  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.10/1.51  tff(c_80, plain, (k1_funct_1('#skF_8', '#skF_7')!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_125])).
% 3.10/1.51  tff(c_84, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_5', k1_tarski('#skF_6'))))), inference(cnfTransformation, [status(thm)], [f_125])).
% 3.10/1.51  tff(c_178, plain, (![C_96, B_97, A_98]: (v5_relat_1(C_96, B_97) | ~m1_subset_1(C_96, k1_zfmisc_1(k2_zfmisc_1(A_98, B_97))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.10/1.51  tff(c_182, plain, (v5_relat_1('#skF_8', k1_tarski('#skF_6'))), inference(resolution, [status(thm)], [c_84, c_178])).
% 3.10/1.51  tff(c_82, plain, (r2_hidden('#skF_7', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_125])).
% 3.10/1.51  tff(c_147, plain, (![C_72, A_73, B_74]: (v1_relat_1(C_72) | ~m1_subset_1(C_72, k1_zfmisc_1(k2_zfmisc_1(A_73, B_74))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.10/1.51  tff(c_151, plain, (v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_84, c_147])).
% 3.10/1.51  tff(c_88, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_125])).
% 3.10/1.51  tff(c_86, plain, (v1_funct_2('#skF_8', '#skF_5', k1_tarski('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_125])).
% 3.10/1.51  tff(c_299, plain, (![A_135, B_136, C_137]: (k1_relset_1(A_135, B_136, C_137)=k1_relat_1(C_137) | ~m1_subset_1(C_137, k1_zfmisc_1(k2_zfmisc_1(A_135, B_136))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.10/1.51  tff(c_303, plain, (k1_relset_1('#skF_5', k1_tarski('#skF_6'), '#skF_8')=k1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_84, c_299])).
% 3.10/1.51  tff(c_603, plain, (![B_183, A_184, C_185]: (k1_xboole_0=B_183 | k1_relset_1(A_184, B_183, C_185)=A_184 | ~v1_funct_2(C_185, A_184, B_183) | ~m1_subset_1(C_185, k1_zfmisc_1(k2_zfmisc_1(A_184, B_183))))), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.10/1.51  tff(c_606, plain, (k1_tarski('#skF_6')=k1_xboole_0 | k1_relset_1('#skF_5', k1_tarski('#skF_6'), '#skF_8')='#skF_5' | ~v1_funct_2('#skF_8', '#skF_5', k1_tarski('#skF_6'))), inference(resolution, [status(thm)], [c_84, c_603])).
% 3.10/1.51  tff(c_609, plain, (k1_tarski('#skF_6')=k1_xboole_0 | k1_relat_1('#skF_8')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_86, c_303, c_606])).
% 3.10/1.51  tff(c_610, plain, (k1_relat_1('#skF_8')='#skF_5'), inference(splitLeft, [status(thm)], [c_609])).
% 3.10/1.51  tff(c_56, plain, (![C_26, B_25, A_24]: (m1_subset_1(k1_funct_1(C_26, B_25), A_24) | ~r2_hidden(B_25, k1_relat_1(C_26)) | ~v1_funct_1(C_26) | ~v5_relat_1(C_26, A_24) | ~v1_relat_1(C_26))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.10/1.51  tff(c_614, plain, (![B_25, A_24]: (m1_subset_1(k1_funct_1('#skF_8', B_25), A_24) | ~r2_hidden(B_25, '#skF_5') | ~v1_funct_1('#skF_8') | ~v5_relat_1('#skF_8', A_24) | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_610, c_56])).
% 3.10/1.51  tff(c_630, plain, (![B_189, A_190]: (m1_subset_1(k1_funct_1('#skF_8', B_189), A_190) | ~r2_hidden(B_189, '#skF_5') | ~v5_relat_1('#skF_8', A_190))), inference(demodulation, [status(thm), theory('equality')], [c_151, c_88, c_614])).
% 3.10/1.51  tff(c_22, plain, (![A_13]: (~v1_xboole_0(k1_tarski(A_13)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.10/1.51  tff(c_155, plain, (![A_87, B_88]: (r2_hidden(A_87, B_88) | v1_xboole_0(B_88) | ~m1_subset_1(A_87, B_88))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.10/1.51  tff(c_4, plain, (![C_6, A_2]: (C_6=A_2 | ~r2_hidden(C_6, k1_tarski(A_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.10/1.51  tff(c_162, plain, (![A_87, A_2]: (A_87=A_2 | v1_xboole_0(k1_tarski(A_2)) | ~m1_subset_1(A_87, k1_tarski(A_2)))), inference(resolution, [status(thm)], [c_155, c_4])).
% 3.10/1.51  tff(c_166, plain, (![A_87, A_2]: (A_87=A_2 | ~m1_subset_1(A_87, k1_tarski(A_2)))), inference(negUnitSimplification, [status(thm)], [c_22, c_162])).
% 3.10/1.51  tff(c_692, plain, (![B_191, A_192]: (k1_funct_1('#skF_8', B_191)=A_192 | ~r2_hidden(B_191, '#skF_5') | ~v5_relat_1('#skF_8', k1_tarski(A_192)))), inference(resolution, [status(thm)], [c_630, c_166])).
% 3.10/1.51  tff(c_708, plain, (![A_193]: (k1_funct_1('#skF_8', '#skF_7')=A_193 | ~v5_relat_1('#skF_8', k1_tarski(A_193)))), inference(resolution, [status(thm)], [c_82, c_692])).
% 3.10/1.51  tff(c_711, plain, (k1_funct_1('#skF_8', '#skF_7')='#skF_6'), inference(resolution, [status(thm)], [c_182, c_708])).
% 3.10/1.51  tff(c_715, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_711])).
% 3.10/1.51  tff(c_716, plain, (k1_tarski('#skF_6')=k1_xboole_0), inference(splitRight, [status(thm)], [c_609])).
% 3.10/1.51  tff(c_6, plain, (![C_6]: (r2_hidden(C_6, k1_tarski(C_6)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.10/1.51  tff(c_107, plain, (![B_47, A_48]: (~r1_tarski(B_47, A_48) | ~r2_hidden(A_48, B_47))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.10/1.51  tff(c_114, plain, (![C_6]: (~r1_tarski(k1_tarski(C_6), C_6))), inference(resolution, [status(thm)], [c_6, c_107])).
% 3.10/1.51  tff(c_743, plain, (~r1_tarski(k1_xboole_0, '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_716, c_114])).
% 3.10/1.51  tff(c_761, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_743])).
% 3.10/1.51  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.10/1.51  
% 3.10/1.51  Inference rules
% 3.10/1.51  ----------------------
% 3.10/1.51  #Ref     : 0
% 3.10/1.51  #Sup     : 144
% 3.10/1.51  #Fact    : 0
% 3.10/1.51  #Define  : 0
% 3.10/1.51  #Split   : 3
% 3.10/1.51  #Chain   : 0
% 3.10/1.51  #Close   : 0
% 3.10/1.51  
% 3.10/1.51  Ordering : KBO
% 3.10/1.51  
% 3.10/1.51  Simplification rules
% 3.10/1.51  ----------------------
% 3.10/1.51  #Subsume      : 25
% 3.10/1.51  #Demod        : 52
% 3.10/1.51  #Tautology    : 48
% 3.10/1.51  #SimpNegUnit  : 5
% 3.10/1.51  #BackRed      : 5
% 3.10/1.51  
% 3.10/1.52  #Partial instantiations: 0
% 3.10/1.52  #Strategies tried      : 1
% 3.10/1.52  
% 3.10/1.52  Timing (in seconds)
% 3.10/1.52  ----------------------
% 3.10/1.52  Preprocessing        : 0.37
% 3.10/1.52  Parsing              : 0.18
% 3.10/1.52  CNF conversion       : 0.03
% 3.10/1.52  Main loop            : 0.37
% 3.10/1.52  Inferencing          : 0.13
% 3.10/1.52  Reduction            : 0.11
% 3.10/1.52  Demodulation         : 0.07
% 3.10/1.52  BG Simplification    : 0.02
% 3.10/1.52  Subsumption          : 0.08
% 3.10/1.52  Abstraction          : 0.03
% 3.10/1.52  MUC search           : 0.00
% 3.10/1.52  Cooper               : 0.00
% 3.10/1.52  Total                : 0.77
% 3.10/1.52  Index Insertion      : 0.00
% 3.10/1.52  Index Deletion       : 0.00
% 3.10/1.52  Index Matching       : 0.00
% 3.10/1.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
