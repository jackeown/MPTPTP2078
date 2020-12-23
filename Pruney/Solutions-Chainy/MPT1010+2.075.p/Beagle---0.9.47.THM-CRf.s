%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:15 EST 2020

% Result     : Theorem 2.28s
% Output     : CNFRefutation 2.28s
% Verified   : 
% Statistics : Number of formulae       :   63 (  86 expanded)
%              Number of leaves         :   34 (  46 expanded)
%              Depth                    :    7
%              Number of atoms          :   90 ( 169 expanded)
%              Number of equality atoms :   30 (  55 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_103,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,k1_tarski(B))
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
       => ( r2_hidden(C,A)
         => k1_funct_1(D,C) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_2)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_92,axiom,(
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

tff(f_66,axiom,(
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

tff(f_48,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_41,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,k1_tarski(D)))
    <=> ( r2_hidden(A,C)
        & B = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t129_zfmisc_1)).

tff(f_28,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_35,axiom,(
    ! [A,B] : ~ v1_xboole_0(k2_tarski(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_xboole_0)).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_44,plain,(
    k1_funct_1('#skF_4','#skF_3') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_46,plain,(
    r2_hidden('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_48,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1',k1_tarski('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_75,plain,(
    ! [C_37,A_38,B_39] :
      ( v1_relat_1(C_37)
      | ~ m1_subset_1(C_37,k1_zfmisc_1(k2_zfmisc_1(A_38,B_39))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_79,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_75])).

tff(c_52,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_50,plain,(
    v1_funct_2('#skF_4','#skF_1',k1_tarski('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_114,plain,(
    ! [A_61,B_62,C_63] :
      ( k1_relset_1(A_61,B_62,C_63) = k1_relat_1(C_63)
      | ~ m1_subset_1(C_63,k1_zfmisc_1(k2_zfmisc_1(A_61,B_62))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_118,plain,(
    k1_relset_1('#skF_1',k1_tarski('#skF_2'),'#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_114])).

tff(c_142,plain,(
    ! [B_79,A_80,C_81] :
      ( k1_xboole_0 = B_79
      | k1_relset_1(A_80,B_79,C_81) = A_80
      | ~ v1_funct_2(C_81,A_80,B_79)
      | ~ m1_subset_1(C_81,k1_zfmisc_1(k2_zfmisc_1(A_80,B_79))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_145,plain,
    ( k1_tarski('#skF_2') = k1_xboole_0
    | k1_relset_1('#skF_1',k1_tarski('#skF_2'),'#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1',k1_tarski('#skF_2')) ),
    inference(resolution,[status(thm)],[c_48,c_142])).

tff(c_148,plain,
    ( k1_tarski('#skF_2') = k1_xboole_0
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_118,c_145])).

tff(c_149,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_148])).

tff(c_125,plain,(
    ! [B_68,A_69] :
      ( r2_hidden(k4_tarski(B_68,k1_funct_1(A_69,B_68)),A_69)
      | ~ r2_hidden(B_68,k1_relat_1(A_69))
      | ~ v1_funct_1(A_69)
      | ~ v1_relat_1(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_18,plain,(
    ! [C_16,A_13,B_14] :
      ( r2_hidden(C_16,A_13)
      | ~ r2_hidden(C_16,B_14)
      | ~ m1_subset_1(B_14,k1_zfmisc_1(A_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_201,plain,(
    ! [B_91,A_92,A_93] :
      ( r2_hidden(k4_tarski(B_91,k1_funct_1(A_92,B_91)),A_93)
      | ~ m1_subset_1(A_92,k1_zfmisc_1(A_93))
      | ~ r2_hidden(B_91,k1_relat_1(A_92))
      | ~ v1_funct_1(A_92)
      | ~ v1_relat_1(A_92) ) ),
    inference(resolution,[status(thm)],[c_125,c_18])).

tff(c_14,plain,(
    ! [D_12,B_10,A_9,C_11] :
      ( D_12 = B_10
      | ~ r2_hidden(k4_tarski(A_9,B_10),k2_zfmisc_1(C_11,k1_tarski(D_12))) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_225,plain,(
    ! [A_98,B_99,D_100,C_101] :
      ( k1_funct_1(A_98,B_99) = D_100
      | ~ m1_subset_1(A_98,k1_zfmisc_1(k2_zfmisc_1(C_101,k1_tarski(D_100))))
      | ~ r2_hidden(B_99,k1_relat_1(A_98))
      | ~ v1_funct_1(A_98)
      | ~ v1_relat_1(A_98) ) ),
    inference(resolution,[status(thm)],[c_201,c_14])).

tff(c_227,plain,(
    ! [B_99] :
      ( k1_funct_1('#skF_4',B_99) = '#skF_2'
      | ~ r2_hidden(B_99,k1_relat_1('#skF_4'))
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_48,c_225])).

tff(c_231,plain,(
    ! [B_102] :
      ( k1_funct_1('#skF_4',B_102) = '#skF_2'
      | ~ r2_hidden(B_102,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_52,c_149,c_227])).

tff(c_245,plain,(
    k1_funct_1('#skF_4','#skF_3') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_46,c_231])).

tff(c_252,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_245])).

tff(c_253,plain,(
    k1_tarski('#skF_2') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_148])).

tff(c_54,plain,(
    ! [A_33] : k2_tarski(A_33,A_33) = k1_tarski(A_33) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_10,plain,(
    ! [A_7,B_8] : ~ v1_xboole_0(k2_tarski(A_7,B_8)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_59,plain,(
    ! [A_33] : ~ v1_xboole_0(k1_tarski(A_33)) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_10])).

tff(c_270,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_253,c_59])).

tff(c_275,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_270])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:34:12 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.28/1.29  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.28/1.29  
% 2.28/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.28/1.29  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.28/1.29  
% 2.28/1.29  %Foreground sorts:
% 2.28/1.29  
% 2.28/1.29  
% 2.28/1.29  %Background operators:
% 2.28/1.29  
% 2.28/1.29  
% 2.28/1.29  %Foreground operators:
% 2.28/1.29  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.28/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.28/1.29  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.28/1.29  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.28/1.29  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.28/1.29  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.28/1.29  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.28/1.29  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.28/1.29  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.28/1.29  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.28/1.29  tff('#skF_2', type, '#skF_2': $i).
% 2.28/1.29  tff('#skF_3', type, '#skF_3': $i).
% 2.28/1.29  tff('#skF_1', type, '#skF_1': $i).
% 2.28/1.29  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.28/1.29  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.28/1.29  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.28/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.28/1.29  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.28/1.29  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.28/1.29  tff('#skF_4', type, '#skF_4': $i).
% 2.28/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.28/1.29  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.28/1.29  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.28/1.29  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.28/1.29  
% 2.28/1.31  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.28/1.31  tff(f_103, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_funct_2)).
% 2.28/1.31  tff(f_70, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.28/1.31  tff(f_74, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.28/1.31  tff(f_92, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 2.28/1.31  tff(f_66, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: ((r2_hidden(B, k1_relat_1(A)) => ((C = k1_funct_1(A, B)) <=> r2_hidden(k4_tarski(B, C), A))) & (~r2_hidden(B, k1_relat_1(A)) => ((C = k1_funct_1(A, B)) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_funct_1)).
% 2.28/1.31  tff(f_48, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 2.28/1.31  tff(f_41, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, k1_tarski(D))) <=> (r2_hidden(A, C) & (B = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t129_zfmisc_1)).
% 2.28/1.31  tff(f_28, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.28/1.31  tff(f_35, axiom, (![A, B]: ~v1_xboole_0(k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_xboole_0)).
% 2.28/1.31  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.28/1.31  tff(c_44, plain, (k1_funct_1('#skF_4', '#skF_3')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.28/1.31  tff(c_46, plain, (r2_hidden('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.28/1.31  tff(c_48, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', k1_tarski('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.28/1.31  tff(c_75, plain, (![C_37, A_38, B_39]: (v1_relat_1(C_37) | ~m1_subset_1(C_37, k1_zfmisc_1(k2_zfmisc_1(A_38, B_39))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.28/1.31  tff(c_79, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_48, c_75])).
% 2.28/1.31  tff(c_52, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.28/1.31  tff(c_50, plain, (v1_funct_2('#skF_4', '#skF_1', k1_tarski('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.28/1.31  tff(c_114, plain, (![A_61, B_62, C_63]: (k1_relset_1(A_61, B_62, C_63)=k1_relat_1(C_63) | ~m1_subset_1(C_63, k1_zfmisc_1(k2_zfmisc_1(A_61, B_62))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.28/1.31  tff(c_118, plain, (k1_relset_1('#skF_1', k1_tarski('#skF_2'), '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_48, c_114])).
% 2.28/1.31  tff(c_142, plain, (![B_79, A_80, C_81]: (k1_xboole_0=B_79 | k1_relset_1(A_80, B_79, C_81)=A_80 | ~v1_funct_2(C_81, A_80, B_79) | ~m1_subset_1(C_81, k1_zfmisc_1(k2_zfmisc_1(A_80, B_79))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.28/1.31  tff(c_145, plain, (k1_tarski('#skF_2')=k1_xboole_0 | k1_relset_1('#skF_1', k1_tarski('#skF_2'), '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', k1_tarski('#skF_2'))), inference(resolution, [status(thm)], [c_48, c_142])).
% 2.28/1.31  tff(c_148, plain, (k1_tarski('#skF_2')=k1_xboole_0 | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_50, c_118, c_145])).
% 2.28/1.31  tff(c_149, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(splitLeft, [status(thm)], [c_148])).
% 2.28/1.31  tff(c_125, plain, (![B_68, A_69]: (r2_hidden(k4_tarski(B_68, k1_funct_1(A_69, B_68)), A_69) | ~r2_hidden(B_68, k1_relat_1(A_69)) | ~v1_funct_1(A_69) | ~v1_relat_1(A_69))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.28/1.31  tff(c_18, plain, (![C_16, A_13, B_14]: (r2_hidden(C_16, A_13) | ~r2_hidden(C_16, B_14) | ~m1_subset_1(B_14, k1_zfmisc_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.28/1.31  tff(c_201, plain, (![B_91, A_92, A_93]: (r2_hidden(k4_tarski(B_91, k1_funct_1(A_92, B_91)), A_93) | ~m1_subset_1(A_92, k1_zfmisc_1(A_93)) | ~r2_hidden(B_91, k1_relat_1(A_92)) | ~v1_funct_1(A_92) | ~v1_relat_1(A_92))), inference(resolution, [status(thm)], [c_125, c_18])).
% 2.28/1.31  tff(c_14, plain, (![D_12, B_10, A_9, C_11]: (D_12=B_10 | ~r2_hidden(k4_tarski(A_9, B_10), k2_zfmisc_1(C_11, k1_tarski(D_12))))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.28/1.31  tff(c_225, plain, (![A_98, B_99, D_100, C_101]: (k1_funct_1(A_98, B_99)=D_100 | ~m1_subset_1(A_98, k1_zfmisc_1(k2_zfmisc_1(C_101, k1_tarski(D_100)))) | ~r2_hidden(B_99, k1_relat_1(A_98)) | ~v1_funct_1(A_98) | ~v1_relat_1(A_98))), inference(resolution, [status(thm)], [c_201, c_14])).
% 2.28/1.31  tff(c_227, plain, (![B_99]: (k1_funct_1('#skF_4', B_99)='#skF_2' | ~r2_hidden(B_99, k1_relat_1('#skF_4')) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_48, c_225])).
% 2.28/1.31  tff(c_231, plain, (![B_102]: (k1_funct_1('#skF_4', B_102)='#skF_2' | ~r2_hidden(B_102, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_79, c_52, c_149, c_227])).
% 2.28/1.31  tff(c_245, plain, (k1_funct_1('#skF_4', '#skF_3')='#skF_2'), inference(resolution, [status(thm)], [c_46, c_231])).
% 2.28/1.31  tff(c_252, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_245])).
% 2.28/1.31  tff(c_253, plain, (k1_tarski('#skF_2')=k1_xboole_0), inference(splitRight, [status(thm)], [c_148])).
% 2.28/1.31  tff(c_54, plain, (![A_33]: (k2_tarski(A_33, A_33)=k1_tarski(A_33))), inference(cnfTransformation, [status(thm)], [f_28])).
% 2.28/1.31  tff(c_10, plain, (![A_7, B_8]: (~v1_xboole_0(k2_tarski(A_7, B_8)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.28/1.31  tff(c_59, plain, (![A_33]: (~v1_xboole_0(k1_tarski(A_33)))), inference(superposition, [status(thm), theory('equality')], [c_54, c_10])).
% 2.28/1.31  tff(c_270, plain, (~v1_xboole_0(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_253, c_59])).
% 2.28/1.31  tff(c_275, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_270])).
% 2.28/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.28/1.31  
% 2.28/1.31  Inference rules
% 2.28/1.31  ----------------------
% 2.28/1.31  #Ref     : 0
% 2.28/1.31  #Sup     : 49
% 2.28/1.31  #Fact    : 0
% 2.28/1.31  #Define  : 0
% 2.28/1.31  #Split   : 2
% 2.28/1.31  #Chain   : 0
% 2.28/1.31  #Close   : 0
% 2.28/1.31  
% 2.28/1.31  Ordering : KBO
% 2.28/1.31  
% 2.28/1.31  Simplification rules
% 2.28/1.31  ----------------------
% 2.28/1.31  #Subsume      : 3
% 2.28/1.31  #Demod        : 19
% 2.28/1.31  #Tautology    : 18
% 2.28/1.31  #SimpNegUnit  : 1
% 2.28/1.31  #BackRed      : 4
% 2.28/1.31  
% 2.28/1.31  #Partial instantiations: 0
% 2.28/1.31  #Strategies tried      : 1
% 2.28/1.31  
% 2.28/1.31  Timing (in seconds)
% 2.28/1.31  ----------------------
% 2.28/1.31  Preprocessing        : 0.32
% 2.28/1.31  Parsing              : 0.17
% 2.28/1.31  CNF conversion       : 0.02
% 2.28/1.31  Main loop            : 0.22
% 2.28/1.31  Inferencing          : 0.08
% 2.28/1.31  Reduction            : 0.06
% 2.28/1.31  Demodulation         : 0.04
% 2.28/1.31  BG Simplification    : 0.02
% 2.28/1.31  Subsumption          : 0.04
% 2.28/1.31  Abstraction          : 0.01
% 2.28/1.31  MUC search           : 0.00
% 2.28/1.31  Cooper               : 0.00
% 2.28/1.31  Total                : 0.58
% 2.28/1.31  Index Insertion      : 0.00
% 2.28/1.31  Index Deletion       : 0.00
% 2.28/1.31  Index Matching       : 0.00
% 2.28/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
