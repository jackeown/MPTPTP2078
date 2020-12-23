%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:12 EST 2020

% Result     : Theorem 3.00s
% Output     : CNFRefutation 3.00s
% Verified   : 
% Statistics : Number of formulae       :   70 (  93 expanded)
%              Number of leaves         :   37 (  49 expanded)
%              Depth                    :    7
%              Number of atoms          :  102 ( 181 expanded)
%              Number of equality atoms :   36 (  61 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_6 > #skF_3 > #skF_4 > #skF_1

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

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_119,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,k1_tarski(B))
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
       => ( r2_hidden(C,A)
         => k1_funct_1(D,C) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_2)).

tff(f_86,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_90,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_108,axiom,(
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

tff(f_77,axiom,(
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

tff(f_59,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_52,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,k1_tarski(D)))
    <=> ( r2_hidden(A,C)
        & B = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t129_zfmisc_1)).

tff(f_44,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_46,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_42,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_82,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_66,plain,(
    k1_funct_1('#skF_6','#skF_5') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_68,plain,(
    r2_hidden('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_70,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3',k1_tarski('#skF_4')))) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_149,plain,(
    ! [C_64,A_65,B_66] :
      ( v1_relat_1(C_64)
      | ~ m1_subset_1(C_64,k1_zfmisc_1(k2_zfmisc_1(A_65,B_66))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_153,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_70,c_149])).

tff(c_74,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_72,plain,(
    v1_funct_2('#skF_6','#skF_3',k1_tarski('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_284,plain,(
    ! [A_123,B_124,C_125] :
      ( k1_relset_1(A_123,B_124,C_125) = k1_relat_1(C_125)
      | ~ m1_subset_1(C_125,k1_zfmisc_1(k2_zfmisc_1(A_123,B_124))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_288,plain,(
    k1_relset_1('#skF_3',k1_tarski('#skF_4'),'#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_70,c_284])).

tff(c_345,plain,(
    ! [B_148,A_149,C_150] :
      ( k1_xboole_0 = B_148
      | k1_relset_1(A_149,B_148,C_150) = A_149
      | ~ v1_funct_2(C_150,A_149,B_148)
      | ~ m1_subset_1(C_150,k1_zfmisc_1(k2_zfmisc_1(A_149,B_148))) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_348,plain,
    ( k1_tarski('#skF_4') = k1_xboole_0
    | k1_relset_1('#skF_3',k1_tarski('#skF_4'),'#skF_6') = '#skF_3'
    | ~ v1_funct_2('#skF_6','#skF_3',k1_tarski('#skF_4')) ),
    inference(resolution,[status(thm)],[c_70,c_345])).

tff(c_351,plain,
    ( k1_tarski('#skF_4') = k1_xboole_0
    | k1_relat_1('#skF_6') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_288,c_348])).

tff(c_352,plain,(
    k1_relat_1('#skF_6') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_351])).

tff(c_295,plain,(
    ! [B_130,A_131] :
      ( r2_hidden(k4_tarski(B_130,k1_funct_1(A_131,B_130)),A_131)
      | ~ r2_hidden(B_130,k1_relat_1(A_131))
      | ~ v1_funct_1(A_131)
      | ~ v1_relat_1(A_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_38,plain,(
    ! [C_19,A_16,B_17] :
      ( r2_hidden(C_19,A_16)
      | ~ r2_hidden(C_19,B_17)
      | ~ m1_subset_1(B_17,k1_zfmisc_1(A_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_539,plain,(
    ! [B_182,A_183,A_184] :
      ( r2_hidden(k4_tarski(B_182,k1_funct_1(A_183,B_182)),A_184)
      | ~ m1_subset_1(A_183,k1_zfmisc_1(A_184))
      | ~ r2_hidden(B_182,k1_relat_1(A_183))
      | ~ v1_funct_1(A_183)
      | ~ v1_relat_1(A_183) ) ),
    inference(resolution,[status(thm)],[c_295,c_38])).

tff(c_34,plain,(
    ! [D_15,B_13,A_12,C_14] :
      ( D_15 = B_13
      | ~ r2_hidden(k4_tarski(A_12,B_13),k2_zfmisc_1(C_14,k1_tarski(D_15))) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_624,plain,(
    ! [A_196,B_197,D_198,C_199] :
      ( k1_funct_1(A_196,B_197) = D_198
      | ~ m1_subset_1(A_196,k1_zfmisc_1(k2_zfmisc_1(C_199,k1_tarski(D_198))))
      | ~ r2_hidden(B_197,k1_relat_1(A_196))
      | ~ v1_funct_1(A_196)
      | ~ v1_relat_1(A_196) ) ),
    inference(resolution,[status(thm)],[c_539,c_34])).

tff(c_626,plain,(
    ! [B_197] :
      ( k1_funct_1('#skF_6',B_197) = '#skF_4'
      | ~ r2_hidden(B_197,k1_relat_1('#skF_6'))
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_70,c_624])).

tff(c_630,plain,(
    ! [B_200] :
      ( k1_funct_1('#skF_6',B_200) = '#skF_4'
      | ~ r2_hidden(B_200,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_153,c_74,c_352,c_626])).

tff(c_648,plain,(
    k1_funct_1('#skF_6','#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_68,c_630])).

tff(c_656,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_648])).

tff(c_657,plain,(
    k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_351])).

tff(c_28,plain,(
    ! [A_9] : k2_tarski(A_9,A_9) = k1_tarski(A_9) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_108,plain,(
    ! [A_58,B_59] : k1_enumset1(A_58,A_58,B_59) = k2_tarski(A_58,B_59) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_10,plain,(
    ! [E_8,B_3,C_4] : r2_hidden(E_8,k1_enumset1(E_8,B_3,C_4)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_135,plain,(
    ! [A_60,B_61] : r2_hidden(A_60,k2_tarski(A_60,B_61)) ),
    inference(superposition,[status(thm),theory(equality)],[c_108,c_10])).

tff(c_143,plain,(
    ! [A_62] : r2_hidden(A_62,k1_tarski(A_62)) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_135])).

tff(c_48,plain,(
    ! [B_26,A_25] :
      ( ~ r1_tarski(B_26,A_25)
      | ~ r2_hidden(A_25,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_147,plain,(
    ! [A_62] : ~ r1_tarski(k1_tarski(A_62),A_62) ),
    inference(resolution,[status(thm)],[c_143,c_48])).

tff(c_684,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_657,c_147])).

tff(c_692,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_684])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n006.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 09:42:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.00/1.49  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.00/1.50  
% 3.00/1.50  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.00/1.50  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_6 > #skF_3 > #skF_4 > #skF_1
% 3.00/1.50  
% 3.00/1.50  %Foreground sorts:
% 3.00/1.50  
% 3.00/1.50  
% 3.00/1.50  %Background operators:
% 3.00/1.50  
% 3.00/1.50  
% 3.00/1.50  %Foreground operators:
% 3.00/1.50  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.00/1.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.00/1.50  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.00/1.50  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.00/1.50  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.00/1.50  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.00/1.50  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.00/1.50  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.00/1.50  tff('#skF_5', type, '#skF_5': $i).
% 3.00/1.50  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.00/1.50  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 3.00/1.50  tff('#skF_6', type, '#skF_6': $i).
% 3.00/1.50  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.00/1.50  tff('#skF_3', type, '#skF_3': $i).
% 3.00/1.50  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.00/1.50  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.00/1.50  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.00/1.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.00/1.50  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.00/1.50  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.00/1.50  tff('#skF_4', type, '#skF_4': $i).
% 3.00/1.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.00/1.50  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 3.00/1.50  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.00/1.50  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.00/1.50  
% 3.00/1.51  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.00/1.51  tff(f_119, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_funct_2)).
% 3.00/1.51  tff(f_86, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.00/1.51  tff(f_90, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.00/1.51  tff(f_108, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 3.00/1.51  tff(f_77, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: ((r2_hidden(B, k1_relat_1(A)) => ((C = k1_funct_1(A, B)) <=> r2_hidden(k4_tarski(B, C), A))) & (~r2_hidden(B, k1_relat_1(A)) => ((C = k1_funct_1(A, B)) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_funct_1)).
% 3.00/1.51  tff(f_59, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 3.00/1.51  tff(f_52, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, k1_tarski(D))) <=> (r2_hidden(A, C) & (B = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t129_zfmisc_1)).
% 3.00/1.51  tff(f_44, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 3.00/1.51  tff(f_46, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 3.00/1.51  tff(f_42, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 3.00/1.51  tff(f_82, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 3.00/1.51  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.00/1.51  tff(c_66, plain, (k1_funct_1('#skF_6', '#skF_5')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.00/1.51  tff(c_68, plain, (r2_hidden('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.00/1.51  tff(c_70, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', k1_tarski('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.00/1.51  tff(c_149, plain, (![C_64, A_65, B_66]: (v1_relat_1(C_64) | ~m1_subset_1(C_64, k1_zfmisc_1(k2_zfmisc_1(A_65, B_66))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.00/1.51  tff(c_153, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_70, c_149])).
% 3.00/1.51  tff(c_74, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.00/1.51  tff(c_72, plain, (v1_funct_2('#skF_6', '#skF_3', k1_tarski('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.00/1.51  tff(c_284, plain, (![A_123, B_124, C_125]: (k1_relset_1(A_123, B_124, C_125)=k1_relat_1(C_125) | ~m1_subset_1(C_125, k1_zfmisc_1(k2_zfmisc_1(A_123, B_124))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.00/1.51  tff(c_288, plain, (k1_relset_1('#skF_3', k1_tarski('#skF_4'), '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_70, c_284])).
% 3.00/1.51  tff(c_345, plain, (![B_148, A_149, C_150]: (k1_xboole_0=B_148 | k1_relset_1(A_149, B_148, C_150)=A_149 | ~v1_funct_2(C_150, A_149, B_148) | ~m1_subset_1(C_150, k1_zfmisc_1(k2_zfmisc_1(A_149, B_148))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.00/1.51  tff(c_348, plain, (k1_tarski('#skF_4')=k1_xboole_0 | k1_relset_1('#skF_3', k1_tarski('#skF_4'), '#skF_6')='#skF_3' | ~v1_funct_2('#skF_6', '#skF_3', k1_tarski('#skF_4'))), inference(resolution, [status(thm)], [c_70, c_345])).
% 3.00/1.51  tff(c_351, plain, (k1_tarski('#skF_4')=k1_xboole_0 | k1_relat_1('#skF_6')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_288, c_348])).
% 3.00/1.51  tff(c_352, plain, (k1_relat_1('#skF_6')='#skF_3'), inference(splitLeft, [status(thm)], [c_351])).
% 3.00/1.51  tff(c_295, plain, (![B_130, A_131]: (r2_hidden(k4_tarski(B_130, k1_funct_1(A_131, B_130)), A_131) | ~r2_hidden(B_130, k1_relat_1(A_131)) | ~v1_funct_1(A_131) | ~v1_relat_1(A_131))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.00/1.51  tff(c_38, plain, (![C_19, A_16, B_17]: (r2_hidden(C_19, A_16) | ~r2_hidden(C_19, B_17) | ~m1_subset_1(B_17, k1_zfmisc_1(A_16)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.00/1.51  tff(c_539, plain, (![B_182, A_183, A_184]: (r2_hidden(k4_tarski(B_182, k1_funct_1(A_183, B_182)), A_184) | ~m1_subset_1(A_183, k1_zfmisc_1(A_184)) | ~r2_hidden(B_182, k1_relat_1(A_183)) | ~v1_funct_1(A_183) | ~v1_relat_1(A_183))), inference(resolution, [status(thm)], [c_295, c_38])).
% 3.00/1.51  tff(c_34, plain, (![D_15, B_13, A_12, C_14]: (D_15=B_13 | ~r2_hidden(k4_tarski(A_12, B_13), k2_zfmisc_1(C_14, k1_tarski(D_15))))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.00/1.51  tff(c_624, plain, (![A_196, B_197, D_198, C_199]: (k1_funct_1(A_196, B_197)=D_198 | ~m1_subset_1(A_196, k1_zfmisc_1(k2_zfmisc_1(C_199, k1_tarski(D_198)))) | ~r2_hidden(B_197, k1_relat_1(A_196)) | ~v1_funct_1(A_196) | ~v1_relat_1(A_196))), inference(resolution, [status(thm)], [c_539, c_34])).
% 3.00/1.51  tff(c_626, plain, (![B_197]: (k1_funct_1('#skF_6', B_197)='#skF_4' | ~r2_hidden(B_197, k1_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_70, c_624])).
% 3.00/1.51  tff(c_630, plain, (![B_200]: (k1_funct_1('#skF_6', B_200)='#skF_4' | ~r2_hidden(B_200, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_153, c_74, c_352, c_626])).
% 3.00/1.51  tff(c_648, plain, (k1_funct_1('#skF_6', '#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_68, c_630])).
% 3.00/1.51  tff(c_656, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_648])).
% 3.00/1.51  tff(c_657, plain, (k1_tarski('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_351])).
% 3.00/1.51  tff(c_28, plain, (![A_9]: (k2_tarski(A_9, A_9)=k1_tarski(A_9))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.00/1.51  tff(c_108, plain, (![A_58, B_59]: (k1_enumset1(A_58, A_58, B_59)=k2_tarski(A_58, B_59))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.00/1.51  tff(c_10, plain, (![E_8, B_3, C_4]: (r2_hidden(E_8, k1_enumset1(E_8, B_3, C_4)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.00/1.51  tff(c_135, plain, (![A_60, B_61]: (r2_hidden(A_60, k2_tarski(A_60, B_61)))), inference(superposition, [status(thm), theory('equality')], [c_108, c_10])).
% 3.00/1.51  tff(c_143, plain, (![A_62]: (r2_hidden(A_62, k1_tarski(A_62)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_135])).
% 3.00/1.51  tff(c_48, plain, (![B_26, A_25]: (~r1_tarski(B_26, A_25) | ~r2_hidden(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.00/1.51  tff(c_147, plain, (![A_62]: (~r1_tarski(k1_tarski(A_62), A_62))), inference(resolution, [status(thm)], [c_143, c_48])).
% 3.00/1.51  tff(c_684, plain, (~r1_tarski(k1_xboole_0, '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_657, c_147])).
% 3.00/1.51  tff(c_692, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_684])).
% 3.00/1.51  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.00/1.51  
% 3.00/1.51  Inference rules
% 3.00/1.51  ----------------------
% 3.00/1.51  #Ref     : 0
% 3.00/1.51  #Sup     : 138
% 3.00/1.51  #Fact    : 0
% 3.00/1.51  #Define  : 0
% 3.00/1.51  #Split   : 3
% 3.00/1.51  #Chain   : 0
% 3.00/1.51  #Close   : 0
% 3.00/1.52  
% 3.00/1.52  Ordering : KBO
% 3.00/1.52  
% 3.00/1.52  Simplification rules
% 3.00/1.52  ----------------------
% 3.00/1.52  #Subsume      : 19
% 3.00/1.52  #Demod        : 33
% 3.00/1.52  #Tautology    : 29
% 3.00/1.52  #SimpNegUnit  : 1
% 3.00/1.52  #BackRed      : 4
% 3.00/1.52  
% 3.00/1.52  #Partial instantiations: 0
% 3.00/1.52  #Strategies tried      : 1
% 3.00/1.52  
% 3.00/1.52  Timing (in seconds)
% 3.00/1.52  ----------------------
% 3.00/1.52  Preprocessing        : 0.35
% 3.00/1.52  Parsing              : 0.19
% 3.00/1.52  CNF conversion       : 0.03
% 3.00/1.52  Main loop            : 0.34
% 3.00/1.52  Inferencing          : 0.12
% 3.00/1.52  Reduction            : 0.10
% 3.00/1.52  Demodulation         : 0.07
% 3.00/1.52  BG Simplification    : 0.02
% 3.00/1.52  Subsumption          : 0.07
% 3.00/1.52  Abstraction          : 0.02
% 3.00/1.52  MUC search           : 0.00
% 3.00/1.52  Cooper               : 0.00
% 3.00/1.52  Total                : 0.73
% 3.00/1.52  Index Insertion      : 0.00
% 3.00/1.52  Index Deletion       : 0.00
% 3.00/1.52  Index Matching       : 0.00
% 3.00/1.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
