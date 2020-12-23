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
% DateTime   : Thu Dec  3 10:15:16 EST 2020

% Result     : Theorem 2.48s
% Output     : CNFRefutation 2.48s
% Verified   : 
% Statistics : Number of formulae       :   68 (  98 expanded)
%              Number of leaves         :   37 (  52 expanded)
%              Depth                    :   10
%              Number of atoms          :   95 ( 194 expanded)
%              Number of equality atoms :   21 (  40 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k2_relset_1 > k1_enumset1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

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

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(f_94,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,k1_tarski(B))
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
       => ( r2_hidden(C,A)
         => k1_funct_1(D,C) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_2)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_83,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),k2_relset_1(A,B,D)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_funct_2)).

tff(f_35,axiom,(
    ! [A] : ~ v1_xboole_0(k1_tarski(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_xboole_0)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_63,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

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

tff(c_36,plain,(
    k1_funct_1('#skF_5','#skF_4') != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_38,plain,(
    r2_hidden('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_44,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_42,plain,(
    v1_funct_2('#skF_5','#skF_2',k1_tarski('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_40,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2',k1_tarski('#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_107,plain,(
    ! [A_59,B_60,C_61] :
      ( k2_relset_1(A_59,B_60,C_61) = k2_relat_1(C_61)
      | ~ m1_subset_1(C_61,k1_zfmisc_1(k2_zfmisc_1(A_59,B_60))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_111,plain,(
    k2_relset_1('#skF_2',k1_tarski('#skF_3'),'#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_40,c_107])).

tff(c_287,plain,(
    ! [D_109,C_110,A_111,B_112] :
      ( r2_hidden(k1_funct_1(D_109,C_110),k2_relset_1(A_111,B_112,D_109))
      | k1_xboole_0 = B_112
      | ~ r2_hidden(C_110,A_111)
      | ~ m1_subset_1(D_109,k1_zfmisc_1(k2_zfmisc_1(A_111,B_112)))
      | ~ v1_funct_2(D_109,A_111,B_112)
      | ~ v1_funct_1(D_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_294,plain,(
    ! [C_110] :
      ( r2_hidden(k1_funct_1('#skF_5',C_110),k2_relat_1('#skF_5'))
      | k1_tarski('#skF_3') = k1_xboole_0
      | ~ r2_hidden(C_110,'#skF_2')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2',k1_tarski('#skF_3'))))
      | ~ v1_funct_2('#skF_5','#skF_2',k1_tarski('#skF_3'))
      | ~ v1_funct_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_111,c_287])).

tff(c_298,plain,(
    ! [C_110] :
      ( r2_hidden(k1_funct_1('#skF_5',C_110),k2_relat_1('#skF_5'))
      | k1_tarski('#skF_3') = k1_xboole_0
      | ~ r2_hidden(C_110,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_294])).

tff(c_299,plain,(
    k1_tarski('#skF_3') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_298])).

tff(c_10,plain,(
    ! [A_7] : ~ v1_xboole_0(k1_tarski(A_7)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_322,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_299,c_10])).

tff(c_329,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_322])).

tff(c_359,plain,(
    ! [C_116] :
      ( r2_hidden(k1_funct_1('#skF_5',C_116),k2_relat_1('#skF_5'))
      | ~ r2_hidden(C_116,'#skF_2') ) ),
    inference(splitRight,[status(thm)],[c_298])).

tff(c_64,plain,(
    ! [C_37,A_38,B_39] :
      ( v1_relat_1(C_37)
      | ~ m1_subset_1(C_37,k1_zfmisc_1(k2_zfmisc_1(A_38,B_39))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_68,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_40,c_64])).

tff(c_28,plain,(
    ! [A_22] :
      ( k9_relat_1(A_22,k1_relat_1(A_22)) = k2_relat_1(A_22)
      | ~ v1_relat_1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_124,plain,(
    ! [A_68,B_69,C_70] :
      ( r2_hidden(k4_tarski('#skF_1'(A_68,B_69,C_70),A_68),C_70)
      | ~ r2_hidden(A_68,k9_relat_1(C_70,B_69))
      | ~ v1_relat_1(C_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_18,plain,(
    ! [C_15,A_12,B_13] :
      ( r2_hidden(C_15,A_12)
      | ~ r2_hidden(C_15,B_13)
      | ~ m1_subset_1(B_13,k1_zfmisc_1(A_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_190,plain,(
    ! [A_95,B_96,C_97,A_98] :
      ( r2_hidden(k4_tarski('#skF_1'(A_95,B_96,C_97),A_95),A_98)
      | ~ m1_subset_1(C_97,k1_zfmisc_1(A_98))
      | ~ r2_hidden(A_95,k9_relat_1(C_97,B_96))
      | ~ v1_relat_1(C_97) ) ),
    inference(resolution,[status(thm)],[c_124,c_18])).

tff(c_14,plain,(
    ! [D_11,B_9,A_8,C_10] :
      ( D_11 = B_9
      | ~ r2_hidden(k4_tarski(A_8,B_9),k2_zfmisc_1(C_10,k1_tarski(D_11))) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_212,plain,(
    ! [C_99,C_102,D_103,A_100,B_101] :
      ( D_103 = A_100
      | ~ m1_subset_1(C_99,k1_zfmisc_1(k2_zfmisc_1(C_102,k1_tarski(D_103))))
      | ~ r2_hidden(A_100,k9_relat_1(C_99,B_101))
      | ~ v1_relat_1(C_99) ) ),
    inference(resolution,[status(thm)],[c_190,c_14])).

tff(c_214,plain,(
    ! [A_100,B_101] :
      ( A_100 = '#skF_3'
      | ~ r2_hidden(A_100,k9_relat_1('#skF_5',B_101))
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_40,c_212])).

tff(c_218,plain,(
    ! [A_104,B_105] :
      ( A_104 = '#skF_3'
      | ~ r2_hidden(A_104,k9_relat_1('#skF_5',B_105)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_214])).

tff(c_238,plain,(
    ! [A_104] :
      ( A_104 = '#skF_3'
      | ~ r2_hidden(A_104,k2_relat_1('#skF_5'))
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_218])).

tff(c_244,plain,(
    ! [A_104] :
      ( A_104 = '#skF_3'
      | ~ r2_hidden(A_104,k2_relat_1('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_238])).

tff(c_370,plain,(
    ! [C_117] :
      ( k1_funct_1('#skF_5',C_117) = '#skF_3'
      | ~ r2_hidden(C_117,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_359,c_244])).

tff(c_389,plain,(
    k1_funct_1('#skF_5','#skF_4') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_38,c_370])).

tff(c_397,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_389])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 20:57:57 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.48/1.36  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.48/1.37  
% 2.48/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.48/1.37  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k2_relset_1 > k1_enumset1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4
% 2.48/1.37  
% 2.48/1.37  %Foreground sorts:
% 2.48/1.37  
% 2.48/1.37  
% 2.48/1.37  %Background operators:
% 2.48/1.37  
% 2.48/1.37  
% 2.48/1.37  %Foreground operators:
% 2.48/1.37  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.48/1.37  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.48/1.37  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.48/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.48/1.37  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.48/1.37  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.48/1.37  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.48/1.37  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.48/1.37  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.48/1.37  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.48/1.37  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.48/1.37  tff('#skF_5', type, '#skF_5': $i).
% 2.48/1.37  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.48/1.37  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.48/1.37  tff('#skF_2', type, '#skF_2': $i).
% 2.48/1.37  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.48/1.37  tff('#skF_3', type, '#skF_3': $i).
% 2.48/1.37  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.48/1.37  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.48/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.48/1.37  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.48/1.37  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.48/1.37  tff('#skF_4', type, '#skF_4': $i).
% 2.48/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.48/1.37  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.48/1.37  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.48/1.37  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.48/1.37  
% 2.48/1.38  tff(f_94, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_funct_2)).
% 2.48/1.38  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.48/1.38  tff(f_71, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.48/1.38  tff(f_83, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), k2_relset_1(A, B, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_funct_2)).
% 2.48/1.38  tff(f_35, axiom, (![A]: ~v1_xboole_0(k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_xboole_0)).
% 2.48/1.38  tff(f_67, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.48/1.38  tff(f_63, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_relat_1)).
% 2.48/1.38  tff(f_59, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_relat_1)).
% 2.48/1.38  tff(f_48, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 2.48/1.38  tff(f_41, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, k1_tarski(D))) <=> (r2_hidden(A, C) & (B = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t129_zfmisc_1)).
% 2.48/1.38  tff(c_36, plain, (k1_funct_1('#skF_5', '#skF_4')!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.48/1.38  tff(c_38, plain, (r2_hidden('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.48/1.38  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.48/1.38  tff(c_44, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.48/1.38  tff(c_42, plain, (v1_funct_2('#skF_5', '#skF_2', k1_tarski('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.48/1.38  tff(c_40, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', k1_tarski('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.48/1.38  tff(c_107, plain, (![A_59, B_60, C_61]: (k2_relset_1(A_59, B_60, C_61)=k2_relat_1(C_61) | ~m1_subset_1(C_61, k1_zfmisc_1(k2_zfmisc_1(A_59, B_60))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.48/1.38  tff(c_111, plain, (k2_relset_1('#skF_2', k1_tarski('#skF_3'), '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_40, c_107])).
% 2.48/1.38  tff(c_287, plain, (![D_109, C_110, A_111, B_112]: (r2_hidden(k1_funct_1(D_109, C_110), k2_relset_1(A_111, B_112, D_109)) | k1_xboole_0=B_112 | ~r2_hidden(C_110, A_111) | ~m1_subset_1(D_109, k1_zfmisc_1(k2_zfmisc_1(A_111, B_112))) | ~v1_funct_2(D_109, A_111, B_112) | ~v1_funct_1(D_109))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.48/1.38  tff(c_294, plain, (![C_110]: (r2_hidden(k1_funct_1('#skF_5', C_110), k2_relat_1('#skF_5')) | k1_tarski('#skF_3')=k1_xboole_0 | ~r2_hidden(C_110, '#skF_2') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', k1_tarski('#skF_3')))) | ~v1_funct_2('#skF_5', '#skF_2', k1_tarski('#skF_3')) | ~v1_funct_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_111, c_287])).
% 2.48/1.38  tff(c_298, plain, (![C_110]: (r2_hidden(k1_funct_1('#skF_5', C_110), k2_relat_1('#skF_5')) | k1_tarski('#skF_3')=k1_xboole_0 | ~r2_hidden(C_110, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_40, c_294])).
% 2.48/1.38  tff(c_299, plain, (k1_tarski('#skF_3')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_298])).
% 2.48/1.38  tff(c_10, plain, (![A_7]: (~v1_xboole_0(k1_tarski(A_7)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.48/1.38  tff(c_322, plain, (~v1_xboole_0(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_299, c_10])).
% 2.48/1.38  tff(c_329, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_322])).
% 2.48/1.38  tff(c_359, plain, (![C_116]: (r2_hidden(k1_funct_1('#skF_5', C_116), k2_relat_1('#skF_5')) | ~r2_hidden(C_116, '#skF_2'))), inference(splitRight, [status(thm)], [c_298])).
% 2.48/1.38  tff(c_64, plain, (![C_37, A_38, B_39]: (v1_relat_1(C_37) | ~m1_subset_1(C_37, k1_zfmisc_1(k2_zfmisc_1(A_38, B_39))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.48/1.38  tff(c_68, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_40, c_64])).
% 2.48/1.38  tff(c_28, plain, (![A_22]: (k9_relat_1(A_22, k1_relat_1(A_22))=k2_relat_1(A_22) | ~v1_relat_1(A_22))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.48/1.38  tff(c_124, plain, (![A_68, B_69, C_70]: (r2_hidden(k4_tarski('#skF_1'(A_68, B_69, C_70), A_68), C_70) | ~r2_hidden(A_68, k9_relat_1(C_70, B_69)) | ~v1_relat_1(C_70))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.48/1.38  tff(c_18, plain, (![C_15, A_12, B_13]: (r2_hidden(C_15, A_12) | ~r2_hidden(C_15, B_13) | ~m1_subset_1(B_13, k1_zfmisc_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.48/1.38  tff(c_190, plain, (![A_95, B_96, C_97, A_98]: (r2_hidden(k4_tarski('#skF_1'(A_95, B_96, C_97), A_95), A_98) | ~m1_subset_1(C_97, k1_zfmisc_1(A_98)) | ~r2_hidden(A_95, k9_relat_1(C_97, B_96)) | ~v1_relat_1(C_97))), inference(resolution, [status(thm)], [c_124, c_18])).
% 2.48/1.38  tff(c_14, plain, (![D_11, B_9, A_8, C_10]: (D_11=B_9 | ~r2_hidden(k4_tarski(A_8, B_9), k2_zfmisc_1(C_10, k1_tarski(D_11))))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.48/1.38  tff(c_212, plain, (![C_99, C_102, D_103, A_100, B_101]: (D_103=A_100 | ~m1_subset_1(C_99, k1_zfmisc_1(k2_zfmisc_1(C_102, k1_tarski(D_103)))) | ~r2_hidden(A_100, k9_relat_1(C_99, B_101)) | ~v1_relat_1(C_99))), inference(resolution, [status(thm)], [c_190, c_14])).
% 2.48/1.38  tff(c_214, plain, (![A_100, B_101]: (A_100='#skF_3' | ~r2_hidden(A_100, k9_relat_1('#skF_5', B_101)) | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_40, c_212])).
% 2.48/1.38  tff(c_218, plain, (![A_104, B_105]: (A_104='#skF_3' | ~r2_hidden(A_104, k9_relat_1('#skF_5', B_105)))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_214])).
% 2.48/1.38  tff(c_238, plain, (![A_104]: (A_104='#skF_3' | ~r2_hidden(A_104, k2_relat_1('#skF_5')) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_28, c_218])).
% 2.48/1.38  tff(c_244, plain, (![A_104]: (A_104='#skF_3' | ~r2_hidden(A_104, k2_relat_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_238])).
% 2.48/1.38  tff(c_370, plain, (![C_117]: (k1_funct_1('#skF_5', C_117)='#skF_3' | ~r2_hidden(C_117, '#skF_2'))), inference(resolution, [status(thm)], [c_359, c_244])).
% 2.48/1.38  tff(c_389, plain, (k1_funct_1('#skF_5', '#skF_4')='#skF_3'), inference(resolution, [status(thm)], [c_38, c_370])).
% 2.48/1.38  tff(c_397, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_389])).
% 2.48/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.48/1.38  
% 2.48/1.38  Inference rules
% 2.48/1.38  ----------------------
% 2.48/1.38  #Ref     : 0
% 2.48/1.38  #Sup     : 78
% 2.48/1.38  #Fact    : 0
% 2.48/1.38  #Define  : 0
% 2.48/1.38  #Split   : 1
% 2.48/1.38  #Chain   : 0
% 2.48/1.38  #Close   : 0
% 2.48/1.38  
% 2.48/1.38  Ordering : KBO
% 2.48/1.38  
% 2.48/1.38  Simplification rules
% 2.48/1.38  ----------------------
% 2.48/1.38  #Subsume      : 0
% 2.48/1.38  #Demod        : 13
% 2.48/1.38  #Tautology    : 13
% 2.48/1.38  #SimpNegUnit  : 1
% 2.48/1.38  #BackRed      : 3
% 2.48/1.38  
% 2.48/1.38  #Partial instantiations: 0
% 2.48/1.38  #Strategies tried      : 1
% 2.48/1.38  
% 2.48/1.38  Timing (in seconds)
% 2.48/1.38  ----------------------
% 2.48/1.38  Preprocessing        : 0.31
% 2.48/1.39  Parsing              : 0.16
% 2.48/1.39  CNF conversion       : 0.02
% 2.48/1.39  Main loop            : 0.25
% 2.48/1.39  Inferencing          : 0.10
% 2.48/1.39  Reduction            : 0.07
% 2.48/1.39  Demodulation         : 0.05
% 2.48/1.39  BG Simplification    : 0.02
% 2.48/1.39  Subsumption          : 0.05
% 2.48/1.39  Abstraction          : 0.02
% 2.48/1.39  MUC search           : 0.00
% 2.48/1.39  Cooper               : 0.00
% 2.48/1.39  Total                : 0.59
% 2.48/1.39  Index Insertion      : 0.00
% 2.48/1.39  Index Deletion       : 0.00
% 2.48/1.39  Index Matching       : 0.00
% 2.48/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
