%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:14 EST 2020

% Result     : Theorem 2.98s
% Output     : CNFRefutation 3.22s
% Verified   : 
% Statistics : Number of formulae       :   74 (  97 expanded)
%              Number of leaves         :   39 (  51 expanded)
%              Depth                    :    7
%              Number of atoms          :  103 ( 182 expanded)
%              Number of equality atoms :   37 (  62 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_5 > #skF_6 > #skF_3 > #skF_1 > #skF_4

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i * $i ) > $i )).

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

tff(f_116,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,k1_tarski(B))
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
       => ( r2_hidden(C,A)
         => k1_funct_1(D,C) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_2)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_87,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_105,axiom,(
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

tff(f_74,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_39,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,k1_tarski(D)))
    <=> ( r2_hidden(A,C)
        & B = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t129_zfmisc_1)).

tff(f_29,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_31,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_57,axiom,(
    ! [A,B,C,D,E] :
      ( E = k2_enumset1(A,B,C,D)
    <=> ! [F] :
          ( r2_hidden(F,E)
        <=> ~ ( F != A
              & F != B
              & F != C
              & F != D ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_enumset1)).

tff(f_79,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_72,plain,(
    k1_funct_1('#skF_6','#skF_5') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_74,plain,(
    r2_hidden('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_76,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3',k1_tarski('#skF_4')))) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_126,plain,(
    ! [C_64,A_65,B_66] :
      ( v1_relat_1(C_64)
      | ~ m1_subset_1(C_64,k1_zfmisc_1(k2_zfmisc_1(A_65,B_66))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_130,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_76,c_126])).

tff(c_80,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_78,plain,(
    v1_funct_2('#skF_6','#skF_3',k1_tarski('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_329,plain,(
    ! [A_169,B_170,C_171] :
      ( k1_relset_1(A_169,B_170,C_171) = k1_relat_1(C_171)
      | ~ m1_subset_1(C_171,k1_zfmisc_1(k2_zfmisc_1(A_169,B_170))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_333,plain,(
    k1_relset_1('#skF_3',k1_tarski('#skF_4'),'#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_76,c_329])).

tff(c_575,plain,(
    ! [B_209,A_210,C_211] :
      ( k1_xboole_0 = B_209
      | k1_relset_1(A_210,B_209,C_211) = A_210
      | ~ v1_funct_2(C_211,A_210,B_209)
      | ~ m1_subset_1(C_211,k1_zfmisc_1(k2_zfmisc_1(A_210,B_209))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_578,plain,
    ( k1_tarski('#skF_4') = k1_xboole_0
    | k1_relset_1('#skF_3',k1_tarski('#skF_4'),'#skF_6') = '#skF_3'
    | ~ v1_funct_2('#skF_6','#skF_3',k1_tarski('#skF_4')) ),
    inference(resolution,[status(thm)],[c_76,c_575])).

tff(c_581,plain,
    ( k1_tarski('#skF_4') = k1_xboole_0
    | k1_relat_1('#skF_6') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_333,c_578])).

tff(c_582,plain,(
    k1_relat_1('#skF_6') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_581])).

tff(c_513,plain,(
    ! [A_196,C_197] :
      ( r2_hidden(k4_tarski(A_196,k1_funct_1(C_197,A_196)),C_197)
      | ~ r2_hidden(A_196,k1_relat_1(C_197))
      | ~ v1_funct_1(C_197)
      | ~ v1_relat_1(C_197) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_46,plain,(
    ! [C_23,A_20,B_21] :
      ( r2_hidden(C_23,A_20)
      | ~ r2_hidden(C_23,B_21)
      | ~ m1_subset_1(B_21,k1_zfmisc_1(A_20)) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_622,plain,(
    ! [A_230,C_231,A_232] :
      ( r2_hidden(k4_tarski(A_230,k1_funct_1(C_231,A_230)),A_232)
      | ~ m1_subset_1(C_231,k1_zfmisc_1(A_232))
      | ~ r2_hidden(A_230,k1_relat_1(C_231))
      | ~ v1_funct_1(C_231)
      | ~ v1_relat_1(C_231) ) ),
    inference(resolution,[status(thm)],[c_513,c_46])).

tff(c_12,plain,(
    ! [D_11,B_9,A_8,C_10] :
      ( D_11 = B_9
      | ~ r2_hidden(k4_tarski(A_8,B_9),k2_zfmisc_1(C_10,k1_tarski(D_11))) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_678,plain,(
    ! [C_237,A_238,D_239,C_240] :
      ( k1_funct_1(C_237,A_238) = D_239
      | ~ m1_subset_1(C_237,k1_zfmisc_1(k2_zfmisc_1(C_240,k1_tarski(D_239))))
      | ~ r2_hidden(A_238,k1_relat_1(C_237))
      | ~ v1_funct_1(C_237)
      | ~ v1_relat_1(C_237) ) ),
    inference(resolution,[status(thm)],[c_622,c_12])).

tff(c_680,plain,(
    ! [A_238] :
      ( k1_funct_1('#skF_6',A_238) = '#skF_4'
      | ~ r2_hidden(A_238,k1_relat_1('#skF_6'))
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_76,c_678])).

tff(c_684,plain,(
    ! [A_241] :
      ( k1_funct_1('#skF_6',A_241) = '#skF_4'
      | ~ r2_hidden(A_241,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_80,c_582,c_680])).

tff(c_695,plain,(
    k1_funct_1('#skF_6','#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_74,c_684])).

tff(c_701,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_695])).

tff(c_702,plain,(
    k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_581])).

tff(c_4,plain,(
    ! [A_2] : k2_tarski(A_2,A_2) = k1_tarski(A_2) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6,plain,(
    ! [A_3,B_4] : k1_enumset1(A_3,A_3,B_4) = k2_tarski(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_133,plain,(
    ! [A_75,B_76,C_77] : k2_enumset1(A_75,A_75,B_76,C_77) = k1_enumset1(A_75,B_76,C_77) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_22,plain,(
    ! [F_19,A_12,C_14,D_15] : r2_hidden(F_19,k2_enumset1(A_12,F_19,C_14,D_15)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_163,plain,(
    ! [A_78,B_79,C_80] : r2_hidden(A_78,k1_enumset1(A_78,B_79,C_80)) ),
    inference(superposition,[status(thm),theory(equality)],[c_133,c_22])).

tff(c_171,plain,(
    ! [A_81,B_82] : r2_hidden(A_81,k2_tarski(A_81,B_82)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_163])).

tff(c_179,plain,(
    ! [A_83] : r2_hidden(A_83,k1_tarski(A_83)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_171])).

tff(c_54,plain,(
    ! [B_28,A_27] :
      ( ~ r1_tarski(B_28,A_27)
      | ~ r2_hidden(A_27,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_183,plain,(
    ! [A_83] : ~ r1_tarski(k1_tarski(A_83),A_83) ),
    inference(resolution,[status(thm)],[c_179,c_54])).

tff(c_730,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_702,c_183])).

tff(c_738,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_730])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:07:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.98/1.48  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.22/1.49  
% 3.22/1.49  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.22/1.49  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_5 > #skF_6 > #skF_3 > #skF_1 > #skF_4
% 3.22/1.49  
% 3.22/1.49  %Foreground sorts:
% 3.22/1.49  
% 3.22/1.49  
% 3.22/1.49  %Background operators:
% 3.22/1.49  
% 3.22/1.49  
% 3.22/1.49  %Foreground operators:
% 3.22/1.49  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.22/1.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.22/1.49  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.22/1.49  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.22/1.49  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i) > $i).
% 3.22/1.49  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.22/1.49  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.22/1.49  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.22/1.49  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.22/1.49  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.22/1.49  tff('#skF_5', type, '#skF_5': $i).
% 3.22/1.49  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.22/1.49  tff('#skF_6', type, '#skF_6': $i).
% 3.22/1.49  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.22/1.49  tff('#skF_3', type, '#skF_3': $i).
% 3.22/1.49  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.22/1.49  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.22/1.49  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.22/1.49  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i) > $i).
% 3.22/1.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.22/1.49  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.22/1.49  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.22/1.49  tff('#skF_4', type, '#skF_4': $i).
% 3.22/1.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.22/1.49  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.22/1.49  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.22/1.49  
% 3.22/1.50  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.22/1.50  tff(f_116, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_funct_2)).
% 3.22/1.50  tff(f_83, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.22/1.50  tff(f_87, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.22/1.50  tff(f_105, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 3.22/1.50  tff(f_74, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_1)).
% 3.22/1.50  tff(f_64, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 3.22/1.50  tff(f_39, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, k1_tarski(D))) <=> (r2_hidden(A, C) & (B = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t129_zfmisc_1)).
% 3.22/1.50  tff(f_29, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 3.22/1.50  tff(f_31, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 3.22/1.50  tff(f_33, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 3.22/1.50  tff(f_57, axiom, (![A, B, C, D, E]: ((E = k2_enumset1(A, B, C, D)) <=> (![F]: (r2_hidden(F, E) <=> ~(((~(F = A) & ~(F = B)) & ~(F = C)) & ~(F = D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_enumset1)).
% 3.22/1.50  tff(f_79, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 3.22/1.50  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.22/1.50  tff(c_72, plain, (k1_funct_1('#skF_6', '#skF_5')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.22/1.50  tff(c_74, plain, (r2_hidden('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.22/1.50  tff(c_76, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', k1_tarski('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.22/1.50  tff(c_126, plain, (![C_64, A_65, B_66]: (v1_relat_1(C_64) | ~m1_subset_1(C_64, k1_zfmisc_1(k2_zfmisc_1(A_65, B_66))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.22/1.50  tff(c_130, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_76, c_126])).
% 3.22/1.50  tff(c_80, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.22/1.50  tff(c_78, plain, (v1_funct_2('#skF_6', '#skF_3', k1_tarski('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.22/1.50  tff(c_329, plain, (![A_169, B_170, C_171]: (k1_relset_1(A_169, B_170, C_171)=k1_relat_1(C_171) | ~m1_subset_1(C_171, k1_zfmisc_1(k2_zfmisc_1(A_169, B_170))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.22/1.50  tff(c_333, plain, (k1_relset_1('#skF_3', k1_tarski('#skF_4'), '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_76, c_329])).
% 3.22/1.50  tff(c_575, plain, (![B_209, A_210, C_211]: (k1_xboole_0=B_209 | k1_relset_1(A_210, B_209, C_211)=A_210 | ~v1_funct_2(C_211, A_210, B_209) | ~m1_subset_1(C_211, k1_zfmisc_1(k2_zfmisc_1(A_210, B_209))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.22/1.50  tff(c_578, plain, (k1_tarski('#skF_4')=k1_xboole_0 | k1_relset_1('#skF_3', k1_tarski('#skF_4'), '#skF_6')='#skF_3' | ~v1_funct_2('#skF_6', '#skF_3', k1_tarski('#skF_4'))), inference(resolution, [status(thm)], [c_76, c_575])).
% 3.22/1.50  tff(c_581, plain, (k1_tarski('#skF_4')=k1_xboole_0 | k1_relat_1('#skF_6')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_78, c_333, c_578])).
% 3.22/1.50  tff(c_582, plain, (k1_relat_1('#skF_6')='#skF_3'), inference(splitLeft, [status(thm)], [c_581])).
% 3.22/1.50  tff(c_513, plain, (![A_196, C_197]: (r2_hidden(k4_tarski(A_196, k1_funct_1(C_197, A_196)), C_197) | ~r2_hidden(A_196, k1_relat_1(C_197)) | ~v1_funct_1(C_197) | ~v1_relat_1(C_197))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.22/1.50  tff(c_46, plain, (![C_23, A_20, B_21]: (r2_hidden(C_23, A_20) | ~r2_hidden(C_23, B_21) | ~m1_subset_1(B_21, k1_zfmisc_1(A_20)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.22/1.50  tff(c_622, plain, (![A_230, C_231, A_232]: (r2_hidden(k4_tarski(A_230, k1_funct_1(C_231, A_230)), A_232) | ~m1_subset_1(C_231, k1_zfmisc_1(A_232)) | ~r2_hidden(A_230, k1_relat_1(C_231)) | ~v1_funct_1(C_231) | ~v1_relat_1(C_231))), inference(resolution, [status(thm)], [c_513, c_46])).
% 3.22/1.50  tff(c_12, plain, (![D_11, B_9, A_8, C_10]: (D_11=B_9 | ~r2_hidden(k4_tarski(A_8, B_9), k2_zfmisc_1(C_10, k1_tarski(D_11))))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.22/1.50  tff(c_678, plain, (![C_237, A_238, D_239, C_240]: (k1_funct_1(C_237, A_238)=D_239 | ~m1_subset_1(C_237, k1_zfmisc_1(k2_zfmisc_1(C_240, k1_tarski(D_239)))) | ~r2_hidden(A_238, k1_relat_1(C_237)) | ~v1_funct_1(C_237) | ~v1_relat_1(C_237))), inference(resolution, [status(thm)], [c_622, c_12])).
% 3.22/1.50  tff(c_680, plain, (![A_238]: (k1_funct_1('#skF_6', A_238)='#skF_4' | ~r2_hidden(A_238, k1_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_76, c_678])).
% 3.22/1.50  tff(c_684, plain, (![A_241]: (k1_funct_1('#skF_6', A_241)='#skF_4' | ~r2_hidden(A_241, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_130, c_80, c_582, c_680])).
% 3.22/1.50  tff(c_695, plain, (k1_funct_1('#skF_6', '#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_74, c_684])).
% 3.22/1.50  tff(c_701, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_695])).
% 3.22/1.50  tff(c_702, plain, (k1_tarski('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_581])).
% 3.22/1.50  tff(c_4, plain, (![A_2]: (k2_tarski(A_2, A_2)=k1_tarski(A_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.22/1.50  tff(c_6, plain, (![A_3, B_4]: (k1_enumset1(A_3, A_3, B_4)=k2_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.22/1.50  tff(c_133, plain, (![A_75, B_76, C_77]: (k2_enumset1(A_75, A_75, B_76, C_77)=k1_enumset1(A_75, B_76, C_77))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.22/1.50  tff(c_22, plain, (![F_19, A_12, C_14, D_15]: (r2_hidden(F_19, k2_enumset1(A_12, F_19, C_14, D_15)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.22/1.50  tff(c_163, plain, (![A_78, B_79, C_80]: (r2_hidden(A_78, k1_enumset1(A_78, B_79, C_80)))), inference(superposition, [status(thm), theory('equality')], [c_133, c_22])).
% 3.22/1.50  tff(c_171, plain, (![A_81, B_82]: (r2_hidden(A_81, k2_tarski(A_81, B_82)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_163])).
% 3.22/1.50  tff(c_179, plain, (![A_83]: (r2_hidden(A_83, k1_tarski(A_83)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_171])).
% 3.22/1.50  tff(c_54, plain, (![B_28, A_27]: (~r1_tarski(B_28, A_27) | ~r2_hidden(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.22/1.50  tff(c_183, plain, (![A_83]: (~r1_tarski(k1_tarski(A_83), A_83))), inference(resolution, [status(thm)], [c_179, c_54])).
% 3.22/1.50  tff(c_730, plain, (~r1_tarski(k1_xboole_0, '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_702, c_183])).
% 3.22/1.50  tff(c_738, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_730])).
% 3.22/1.50  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.22/1.50  
% 3.22/1.50  Inference rules
% 3.22/1.50  ----------------------
% 3.22/1.50  #Ref     : 0
% 3.22/1.50  #Sup     : 148
% 3.22/1.50  #Fact    : 0
% 3.22/1.50  #Define  : 0
% 3.22/1.50  #Split   : 2
% 3.22/1.50  #Chain   : 0
% 3.22/1.50  #Close   : 0
% 3.22/1.50  
% 3.22/1.50  Ordering : KBO
% 3.22/1.50  
% 3.22/1.50  Simplification rules
% 3.22/1.50  ----------------------
% 3.22/1.50  #Subsume      : 18
% 3.22/1.50  #Demod        : 18
% 3.22/1.50  #Tautology    : 32
% 3.22/1.50  #SimpNegUnit  : 1
% 3.22/1.50  #BackRed      : 4
% 3.22/1.50  
% 3.22/1.50  #Partial instantiations: 0
% 3.22/1.50  #Strategies tried      : 1
% 3.22/1.50  
% 3.22/1.50  Timing (in seconds)
% 3.22/1.50  ----------------------
% 3.22/1.51  Preprocessing        : 0.33
% 3.22/1.51  Parsing              : 0.16
% 3.22/1.51  CNF conversion       : 0.03
% 3.22/1.51  Main loop            : 0.37
% 3.22/1.51  Inferencing          : 0.13
% 3.22/1.51  Reduction            : 0.11
% 3.22/1.51  Demodulation         : 0.08
% 3.22/1.51  BG Simplification    : 0.02
% 3.22/1.51  Subsumption          : 0.08
% 3.22/1.51  Abstraction          : 0.02
% 3.22/1.51  MUC search           : 0.00
% 3.22/1.51  Cooper               : 0.00
% 3.22/1.51  Total                : 0.74
% 3.22/1.51  Index Insertion      : 0.00
% 3.22/1.51  Index Deletion       : 0.00
% 3.22/1.51  Index Matching       : 0.00
% 3.22/1.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
