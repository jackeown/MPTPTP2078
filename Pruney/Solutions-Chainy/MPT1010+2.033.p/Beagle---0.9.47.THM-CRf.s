%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:09 EST 2020

% Result     : Theorem 3.29s
% Output     : CNFRefutation 3.42s
% Verified   : 
% Statistics : Number of formulae       :   72 (  96 expanded)
%              Number of leaves         :   42 (  55 expanded)
%              Depth                    :    9
%              Number of atoms          :   88 ( 170 expanded)
%              Number of equality atoms :   27 (  54 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_3 > #skF_7 > #skF_5 > #skF_6 > #skF_4 > #skF_8 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

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

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_137,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,k1_tarski(B))
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
       => ( r2_hidden(C,A)
         => k1_funct_1(D,C) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_2)).

tff(f_104,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_98,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_108,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_126,axiom,(
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

tff(f_89,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A)
        & v1_funct_1(B) )
     => ! [C] :
          ( r2_hidden(C,k1_relat_1(B))
         => r2_hidden(k1_funct_1(B,C),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_funct_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_94,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_108,plain,(
    k1_funct_1('#skF_8','#skF_7') != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_112,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_5',k1_tarski('#skF_6')))) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_167,plain,(
    ! [C_81,B_82,A_83] :
      ( v5_relat_1(C_81,B_82)
      | ~ m1_subset_1(C_81,k1_zfmisc_1(k2_zfmisc_1(A_83,B_82))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_171,plain,(
    v5_relat_1('#skF_8',k1_tarski('#skF_6')) ),
    inference(resolution,[status(thm)],[c_112,c_167])).

tff(c_110,plain,(
    r2_hidden('#skF_7','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_153,plain,(
    ! [C_75,A_76,B_77] :
      ( v1_relat_1(C_75)
      | ~ m1_subset_1(C_75,k1_zfmisc_1(k2_zfmisc_1(A_76,B_77))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_157,plain,(
    v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_112,c_153])).

tff(c_116,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_114,plain,(
    v1_funct_2('#skF_8','#skF_5',k1_tarski('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_237,plain,(
    ! [A_224,B_225,C_226] :
      ( k1_relset_1(A_224,B_225,C_226) = k1_relat_1(C_226)
      | ~ m1_subset_1(C_226,k1_zfmisc_1(k2_zfmisc_1(A_224,B_225))) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_241,plain,(
    k1_relset_1('#skF_5',k1_tarski('#skF_6'),'#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_112,c_237])).

tff(c_424,plain,(
    ! [B_266,A_267,C_268] :
      ( k1_xboole_0 = B_266
      | k1_relset_1(A_267,B_266,C_268) = A_267
      | ~ v1_funct_2(C_268,A_267,B_266)
      | ~ m1_subset_1(C_268,k1_zfmisc_1(k2_zfmisc_1(A_267,B_266))) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_427,plain,
    ( k1_tarski('#skF_6') = k1_xboole_0
    | k1_relset_1('#skF_5',k1_tarski('#skF_6'),'#skF_8') = '#skF_5'
    | ~ v1_funct_2('#skF_8','#skF_5',k1_tarski('#skF_6')) ),
    inference(resolution,[status(thm)],[c_112,c_424])).

tff(c_430,plain,
    ( k1_tarski('#skF_6') = k1_xboole_0
    | k1_relat_1('#skF_8') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_241,c_427])).

tff(c_431,plain,(
    k1_relat_1('#skF_8') = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_430])).

tff(c_403,plain,(
    ! [B_258,C_259,A_260] :
      ( r2_hidden(k1_funct_1(B_258,C_259),A_260)
      | ~ r2_hidden(C_259,k1_relat_1(B_258))
      | ~ v1_funct_1(B_258)
      | ~ v5_relat_1(B_258,A_260)
      | ~ v1_relat_1(B_258) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_4,plain,(
    ! [C_6,A_2] :
      ( C_6 = A_2
      | ~ r2_hidden(C_6,k1_tarski(A_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_470,plain,(
    ! [B_274,C_275,A_276] :
      ( k1_funct_1(B_274,C_275) = A_276
      | ~ r2_hidden(C_275,k1_relat_1(B_274))
      | ~ v1_funct_1(B_274)
      | ~ v5_relat_1(B_274,k1_tarski(A_276))
      | ~ v1_relat_1(B_274) ) ),
    inference(resolution,[status(thm)],[c_403,c_4])).

tff(c_472,plain,(
    ! [C_275,A_276] :
      ( k1_funct_1('#skF_8',C_275) = A_276
      | ~ r2_hidden(C_275,'#skF_5')
      | ~ v1_funct_1('#skF_8')
      | ~ v5_relat_1('#skF_8',k1_tarski(A_276))
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_431,c_470])).

tff(c_487,plain,(
    ! [C_277,A_278] :
      ( k1_funct_1('#skF_8',C_277) = A_278
      | ~ r2_hidden(C_277,'#skF_5')
      | ~ v5_relat_1('#skF_8',k1_tarski(A_278)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_157,c_116,c_472])).

tff(c_560,plain,(
    ! [A_286] :
      ( k1_funct_1('#skF_8','#skF_7') = A_286
      | ~ v5_relat_1('#skF_8',k1_tarski(A_286)) ) ),
    inference(resolution,[status(thm)],[c_110,c_487])).

tff(c_563,plain,(
    k1_funct_1('#skF_8','#skF_7') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_171,c_560])).

tff(c_567,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_108,c_563])).

tff(c_568,plain,(
    k1_tarski('#skF_6') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_430])).

tff(c_6,plain,(
    ! [C_6] : r2_hidden(C_6,k1_tarski(C_6)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_134,plain,(
    ! [B_70,A_71] :
      ( ~ r1_tarski(B_70,A_71)
      | ~ r2_hidden(A_71,B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_141,plain,(
    ! [C_6] : ~ r1_tarski(k1_tarski(C_6),C_6) ),
    inference(resolution,[status(thm)],[c_6,c_134])).

tff(c_586,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_568,c_141])).

tff(c_600,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_586])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:25:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.29/1.46  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.29/1.47  
% 3.29/1.47  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.29/1.47  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_3 > #skF_7 > #skF_5 > #skF_6 > #skF_4 > #skF_8 > #skF_2 > #skF_1
% 3.29/1.47  
% 3.29/1.47  %Foreground sorts:
% 3.29/1.47  
% 3.29/1.47  
% 3.29/1.47  %Background operators:
% 3.29/1.47  
% 3.29/1.47  
% 3.29/1.47  %Foreground operators:
% 3.29/1.47  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.29/1.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.29/1.47  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.29/1.47  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.29/1.47  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.29/1.47  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.29/1.47  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.29/1.47  tff('#skF_7', type, '#skF_7': $i).
% 3.29/1.47  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.29/1.47  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.29/1.47  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.29/1.47  tff('#skF_5', type, '#skF_5': $i).
% 3.29/1.47  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.29/1.47  tff('#skF_6', type, '#skF_6': $i).
% 3.29/1.47  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.29/1.47  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.29/1.47  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.29/1.47  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.29/1.47  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.29/1.47  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.29/1.47  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.29/1.47  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.29/1.47  tff('#skF_8', type, '#skF_8': $i).
% 3.29/1.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.29/1.47  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.29/1.47  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.29/1.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.29/1.47  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.29/1.47  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.29/1.47  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.29/1.47  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.29/1.47  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.29/1.47  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.29/1.47  
% 3.42/1.48  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.42/1.48  tff(f_137, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_funct_2)).
% 3.42/1.48  tff(f_104, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.42/1.48  tff(f_98, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.42/1.48  tff(f_108, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.42/1.48  tff(f_126, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 3.42/1.48  tff(f_89, axiom, (![A, B]: (((v1_relat_1(B) & v5_relat_1(B, A)) & v1_funct_1(B)) => (![C]: (r2_hidden(C, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, C), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t172_funct_1)).
% 3.42/1.48  tff(f_34, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 3.42/1.48  tff(f_94, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 3.42/1.48  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.42/1.48  tff(c_108, plain, (k1_funct_1('#skF_8', '#skF_7')!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_137])).
% 3.42/1.48  tff(c_112, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_5', k1_tarski('#skF_6'))))), inference(cnfTransformation, [status(thm)], [f_137])).
% 3.42/1.48  tff(c_167, plain, (![C_81, B_82, A_83]: (v5_relat_1(C_81, B_82) | ~m1_subset_1(C_81, k1_zfmisc_1(k2_zfmisc_1(A_83, B_82))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.42/1.48  tff(c_171, plain, (v5_relat_1('#skF_8', k1_tarski('#skF_6'))), inference(resolution, [status(thm)], [c_112, c_167])).
% 3.42/1.48  tff(c_110, plain, (r2_hidden('#skF_7', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_137])).
% 3.42/1.48  tff(c_153, plain, (![C_75, A_76, B_77]: (v1_relat_1(C_75) | ~m1_subset_1(C_75, k1_zfmisc_1(k2_zfmisc_1(A_76, B_77))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.42/1.48  tff(c_157, plain, (v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_112, c_153])).
% 3.42/1.48  tff(c_116, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_137])).
% 3.42/1.48  tff(c_114, plain, (v1_funct_2('#skF_8', '#skF_5', k1_tarski('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_137])).
% 3.42/1.48  tff(c_237, plain, (![A_224, B_225, C_226]: (k1_relset_1(A_224, B_225, C_226)=k1_relat_1(C_226) | ~m1_subset_1(C_226, k1_zfmisc_1(k2_zfmisc_1(A_224, B_225))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.42/1.48  tff(c_241, plain, (k1_relset_1('#skF_5', k1_tarski('#skF_6'), '#skF_8')=k1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_112, c_237])).
% 3.42/1.48  tff(c_424, plain, (![B_266, A_267, C_268]: (k1_xboole_0=B_266 | k1_relset_1(A_267, B_266, C_268)=A_267 | ~v1_funct_2(C_268, A_267, B_266) | ~m1_subset_1(C_268, k1_zfmisc_1(k2_zfmisc_1(A_267, B_266))))), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.42/1.48  tff(c_427, plain, (k1_tarski('#skF_6')=k1_xboole_0 | k1_relset_1('#skF_5', k1_tarski('#skF_6'), '#skF_8')='#skF_5' | ~v1_funct_2('#skF_8', '#skF_5', k1_tarski('#skF_6'))), inference(resolution, [status(thm)], [c_112, c_424])).
% 3.42/1.48  tff(c_430, plain, (k1_tarski('#skF_6')=k1_xboole_0 | k1_relat_1('#skF_8')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_114, c_241, c_427])).
% 3.42/1.48  tff(c_431, plain, (k1_relat_1('#skF_8')='#skF_5'), inference(splitLeft, [status(thm)], [c_430])).
% 3.42/1.48  tff(c_403, plain, (![B_258, C_259, A_260]: (r2_hidden(k1_funct_1(B_258, C_259), A_260) | ~r2_hidden(C_259, k1_relat_1(B_258)) | ~v1_funct_1(B_258) | ~v5_relat_1(B_258, A_260) | ~v1_relat_1(B_258))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.42/1.48  tff(c_4, plain, (![C_6, A_2]: (C_6=A_2 | ~r2_hidden(C_6, k1_tarski(A_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.42/1.48  tff(c_470, plain, (![B_274, C_275, A_276]: (k1_funct_1(B_274, C_275)=A_276 | ~r2_hidden(C_275, k1_relat_1(B_274)) | ~v1_funct_1(B_274) | ~v5_relat_1(B_274, k1_tarski(A_276)) | ~v1_relat_1(B_274))), inference(resolution, [status(thm)], [c_403, c_4])).
% 3.42/1.48  tff(c_472, plain, (![C_275, A_276]: (k1_funct_1('#skF_8', C_275)=A_276 | ~r2_hidden(C_275, '#skF_5') | ~v1_funct_1('#skF_8') | ~v5_relat_1('#skF_8', k1_tarski(A_276)) | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_431, c_470])).
% 3.42/1.48  tff(c_487, plain, (![C_277, A_278]: (k1_funct_1('#skF_8', C_277)=A_278 | ~r2_hidden(C_277, '#skF_5') | ~v5_relat_1('#skF_8', k1_tarski(A_278)))), inference(demodulation, [status(thm), theory('equality')], [c_157, c_116, c_472])).
% 3.42/1.48  tff(c_560, plain, (![A_286]: (k1_funct_1('#skF_8', '#skF_7')=A_286 | ~v5_relat_1('#skF_8', k1_tarski(A_286)))), inference(resolution, [status(thm)], [c_110, c_487])).
% 3.42/1.48  tff(c_563, plain, (k1_funct_1('#skF_8', '#skF_7')='#skF_6'), inference(resolution, [status(thm)], [c_171, c_560])).
% 3.42/1.48  tff(c_567, plain, $false, inference(negUnitSimplification, [status(thm)], [c_108, c_563])).
% 3.42/1.48  tff(c_568, plain, (k1_tarski('#skF_6')=k1_xboole_0), inference(splitRight, [status(thm)], [c_430])).
% 3.42/1.48  tff(c_6, plain, (![C_6]: (r2_hidden(C_6, k1_tarski(C_6)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.42/1.48  tff(c_134, plain, (![B_70, A_71]: (~r1_tarski(B_70, A_71) | ~r2_hidden(A_71, B_70))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.42/1.48  tff(c_141, plain, (![C_6]: (~r1_tarski(k1_tarski(C_6), C_6))), inference(resolution, [status(thm)], [c_6, c_134])).
% 3.42/1.48  tff(c_586, plain, (~r1_tarski(k1_xboole_0, '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_568, c_141])).
% 3.42/1.48  tff(c_600, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_586])).
% 3.42/1.48  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.42/1.48  
% 3.42/1.48  Inference rules
% 3.42/1.48  ----------------------
% 3.42/1.48  #Ref     : 0
% 3.42/1.48  #Sup     : 106
% 3.42/1.48  #Fact    : 0
% 3.42/1.48  #Define  : 0
% 3.42/1.48  #Split   : 2
% 3.42/1.48  #Chain   : 0
% 3.42/1.48  #Close   : 0
% 3.42/1.48  
% 3.42/1.48  Ordering : KBO
% 3.42/1.48  
% 3.42/1.48  Simplification rules
% 3.42/1.48  ----------------------
% 3.42/1.48  #Subsume      : 6
% 3.42/1.48  #Demod        : 40
% 3.42/1.48  #Tautology    : 42
% 3.42/1.48  #SimpNegUnit  : 1
% 3.42/1.48  #BackRed      : 5
% 3.42/1.48  
% 3.42/1.48  #Partial instantiations: 0
% 3.42/1.48  #Strategies tried      : 1
% 3.42/1.48  
% 3.42/1.48  Timing (in seconds)
% 3.42/1.48  ----------------------
% 3.42/1.48  Preprocessing        : 0.37
% 3.42/1.48  Parsing              : 0.18
% 3.42/1.48  CNF conversion       : 0.03
% 3.42/1.48  Main loop            : 0.34
% 3.42/1.48  Inferencing          : 0.10
% 3.42/1.48  Reduction            : 0.10
% 3.42/1.48  Demodulation         : 0.07
% 3.42/1.48  BG Simplification    : 0.03
% 3.42/1.48  Subsumption          : 0.10
% 3.42/1.48  Abstraction          : 0.03
% 3.42/1.48  MUC search           : 0.00
% 3.42/1.48  Cooper               : 0.00
% 3.42/1.48  Total                : 0.74
% 3.42/1.48  Index Insertion      : 0.00
% 3.42/1.49  Index Deletion       : 0.00
% 3.42/1.49  Index Matching       : 0.00
% 3.42/1.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
