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
% DateTime   : Thu Dec  3 10:17:56 EST 2020

% Result     : Theorem 2.73s
% Output     : CNFRefutation 2.73s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 120 expanded)
%              Number of leaves         :   29 (  55 expanded)
%              Depth                    :   12
%              Number of atoms          :  102 ( 319 expanded)
%              Number of equality atoms :   11 (  21 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k3_funct_2 > k2_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k3_funct_2,type,(
    k3_funct_2: ( $i * $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_129,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ~ v1_xboole_0(B)
           => ! [C] :
                ( m1_subset_1(C,A)
               => ! [D] :
                    ( ( v1_funct_1(D)
                      & v1_funct_2(D,A,B)
                      & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
                   => r2_hidden(k3_funct_2(A,B,D,C),k2_relset_1(A,B,D)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t189_funct_2)).

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_109,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),k2_relset_1(A,B,D)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_funct_2)).

tff(f_97,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,A) )
     => k3_funct_2(A,B,C,D) = k1_funct_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

tff(f_34,axiom,(
    ! [A] :
    ? [B] : m1_subset_1(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).

tff(f_36,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_43,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_44,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_46,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_42,plain,(
    m1_subset_1('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_14,plain,(
    ! [A_9,B_10] :
      ( r2_hidden(A_9,B_10)
      | v1_xboole_0(B_10)
      | ~ m1_subset_1(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_40,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_38,plain,(
    v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_36,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_32,plain,(
    ! [D_29,C_28,A_26,B_27] :
      ( r2_hidden(k1_funct_1(D_29,C_28),k2_relset_1(A_26,B_27,D_29))
      | k1_xboole_0 = B_27
      | ~ r2_hidden(C_28,A_26)
      | ~ m1_subset_1(D_29,k1_zfmisc_1(k2_zfmisc_1(A_26,B_27)))
      | ~ v1_funct_2(D_29,A_26,B_27)
      | ~ v1_funct_1(D_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_448,plain,(
    ! [A_112,B_113,C_114,D_115] :
      ( k3_funct_2(A_112,B_113,C_114,D_115) = k1_funct_1(C_114,D_115)
      | ~ m1_subset_1(D_115,A_112)
      | ~ m1_subset_1(C_114,k1_zfmisc_1(k2_zfmisc_1(A_112,B_113)))
      | ~ v1_funct_2(C_114,A_112,B_113)
      | ~ v1_funct_1(C_114)
      | v1_xboole_0(A_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_466,plain,(
    ! [B_113,C_114] :
      ( k3_funct_2('#skF_2',B_113,C_114,'#skF_4') = k1_funct_1(C_114,'#skF_4')
      | ~ m1_subset_1(C_114,k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_113)))
      | ~ v1_funct_2(C_114,'#skF_2',B_113)
      | ~ v1_funct_1(C_114)
      | v1_xboole_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_42,c_448])).

tff(c_483,plain,(
    ! [B_117,C_118] :
      ( k3_funct_2('#skF_2',B_117,C_118,'#skF_4') = k1_funct_1(C_118,'#skF_4')
      | ~ m1_subset_1(C_118,k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_117)))
      | ~ v1_funct_2(C_118,'#skF_2',B_117)
      | ~ v1_funct_1(C_118) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_466])).

tff(c_498,plain,
    ( k3_funct_2('#skF_2','#skF_3','#skF_5','#skF_4') = k1_funct_1('#skF_5','#skF_4')
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_36,c_483])).

tff(c_516,plain,(
    k3_funct_2('#skF_2','#skF_3','#skF_5','#skF_4') = k1_funct_1('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_498])).

tff(c_34,plain,(
    ~ r2_hidden(k3_funct_2('#skF_2','#skF_3','#skF_5','#skF_4'),k2_relset_1('#skF_2','#skF_3','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_520,plain,(
    ~ r2_hidden(k1_funct_1('#skF_5','#skF_4'),k2_relset_1('#skF_2','#skF_3','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_516,c_34])).

tff(c_527,plain,
    ( k1_xboole_0 = '#skF_3'
    | ~ r2_hidden('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_32,c_520])).

tff(c_533,plain,
    ( k1_xboole_0 = '#skF_3'
    | ~ r2_hidden('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_36,c_527])).

tff(c_535,plain,(
    ~ r2_hidden('#skF_4','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_533])).

tff(c_538,plain,
    ( v1_xboole_0('#skF_2')
    | ~ m1_subset_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_14,c_535])).

tff(c_541,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_538])).

tff(c_543,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_541])).

tff(c_544,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_533])).

tff(c_8,plain,(
    ! [A_3] : m1_subset_1('#skF_1'(A_3),A_3) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_10,plain,(
    ! [A_5] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_73,plain,(
    ! [A_49,B_50] :
      ( r1_tarski(A_49,B_50)
      | ~ m1_subset_1(A_49,k1_zfmisc_1(B_50)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_90,plain,(
    ! [A_5] : r1_tarski(k1_xboole_0,A_5) ),
    inference(resolution,[status(thm)],[c_10,c_73])).

tff(c_109,plain,(
    ! [B_57,A_58] :
      ( v1_xboole_0(B_57)
      | ~ m1_subset_1(B_57,k1_zfmisc_1(A_58))
      | ~ v1_xboole_0(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_126,plain,(
    ! [A_5] :
      ( v1_xboole_0(k1_xboole_0)
      | ~ v1_xboole_0(A_5) ) ),
    inference(resolution,[status(thm)],[c_10,c_109])).

tff(c_131,plain,(
    ! [A_5] : ~ v1_xboole_0(A_5) ),
    inference(splitLeft,[status(thm)],[c_126])).

tff(c_135,plain,(
    ! [A_60,B_61] :
      ( r2_hidden(A_60,B_61)
      | ~ m1_subset_1(A_60,B_61) ) ),
    inference(negUnitSimplification,[status(thm)],[c_131,c_14])).

tff(c_22,plain,(
    ! [B_17,A_16] :
      ( ~ r1_tarski(B_17,A_16)
      | ~ r2_hidden(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_165,plain,(
    ! [B_67,A_68] :
      ( ~ r1_tarski(B_67,A_68)
      | ~ m1_subset_1(A_68,B_67) ) ),
    inference(resolution,[status(thm)],[c_135,c_22])).

tff(c_178,plain,(
    ! [A_69] : ~ m1_subset_1(A_69,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_90,c_165])).

tff(c_183,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_8,c_178])).

tff(c_184,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_126])).

tff(c_549,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_544,c_184])).

tff(c_556,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_549])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:53:27 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.73/1.38  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.73/1.38  
% 2.73/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.73/1.39  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k3_funct_2 > k2_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4
% 2.73/1.39  
% 2.73/1.39  %Foreground sorts:
% 2.73/1.39  
% 2.73/1.39  
% 2.73/1.39  %Background operators:
% 2.73/1.39  
% 2.73/1.39  
% 2.73/1.39  %Foreground operators:
% 2.73/1.39  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.73/1.39  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.73/1.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.73/1.39  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.73/1.39  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.73/1.39  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.73/1.39  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.73/1.39  tff('#skF_5', type, '#skF_5': $i).
% 2.73/1.39  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.73/1.39  tff('#skF_2', type, '#skF_2': $i).
% 2.73/1.39  tff('#skF_3', type, '#skF_3': $i).
% 2.73/1.39  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.73/1.39  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.73/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.73/1.39  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.73/1.39  tff('#skF_4', type, '#skF_4': $i).
% 2.73/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.73/1.39  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.73/1.39  tff(k3_funct_2, type, k3_funct_2: ($i * $i * $i * $i) > $i).
% 2.73/1.39  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.73/1.39  
% 2.73/1.40  tff(f_129, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, A) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_hidden(k3_funct_2(A, B, D, C), k2_relset_1(A, B, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t189_funct_2)).
% 2.73/1.40  tff(f_49, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 2.73/1.40  tff(f_109, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), k2_relset_1(A, B, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_funct_2)).
% 2.73/1.40  tff(f_97, axiom, (![A, B, C, D]: (((((~v1_xboole_0(A) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, A)) => (k3_funct_2(A, B, C, D) = k1_funct_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k3_funct_2)).
% 2.73/1.40  tff(f_34, axiom, (![A]: (?[B]: m1_subset_1(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', existence_m1_subset_1)).
% 2.73/1.40  tff(f_36, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 2.73/1.40  tff(f_53, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.73/1.40  tff(f_43, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_subset_1)).
% 2.73/1.40  tff(f_64, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 2.73/1.40  tff(c_44, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_129])).
% 2.73/1.40  tff(c_46, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_129])).
% 2.73/1.40  tff(c_42, plain, (m1_subset_1('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_129])).
% 2.73/1.40  tff(c_14, plain, (![A_9, B_10]: (r2_hidden(A_9, B_10) | v1_xboole_0(B_10) | ~m1_subset_1(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.73/1.40  tff(c_40, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_129])).
% 2.73/1.40  tff(c_38, plain, (v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_129])).
% 2.73/1.40  tff(c_36, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_129])).
% 2.73/1.40  tff(c_32, plain, (![D_29, C_28, A_26, B_27]: (r2_hidden(k1_funct_1(D_29, C_28), k2_relset_1(A_26, B_27, D_29)) | k1_xboole_0=B_27 | ~r2_hidden(C_28, A_26) | ~m1_subset_1(D_29, k1_zfmisc_1(k2_zfmisc_1(A_26, B_27))) | ~v1_funct_2(D_29, A_26, B_27) | ~v1_funct_1(D_29))), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.73/1.40  tff(c_448, plain, (![A_112, B_113, C_114, D_115]: (k3_funct_2(A_112, B_113, C_114, D_115)=k1_funct_1(C_114, D_115) | ~m1_subset_1(D_115, A_112) | ~m1_subset_1(C_114, k1_zfmisc_1(k2_zfmisc_1(A_112, B_113))) | ~v1_funct_2(C_114, A_112, B_113) | ~v1_funct_1(C_114) | v1_xboole_0(A_112))), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.73/1.40  tff(c_466, plain, (![B_113, C_114]: (k3_funct_2('#skF_2', B_113, C_114, '#skF_4')=k1_funct_1(C_114, '#skF_4') | ~m1_subset_1(C_114, k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_113))) | ~v1_funct_2(C_114, '#skF_2', B_113) | ~v1_funct_1(C_114) | v1_xboole_0('#skF_2'))), inference(resolution, [status(thm)], [c_42, c_448])).
% 2.73/1.40  tff(c_483, plain, (![B_117, C_118]: (k3_funct_2('#skF_2', B_117, C_118, '#skF_4')=k1_funct_1(C_118, '#skF_4') | ~m1_subset_1(C_118, k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_117))) | ~v1_funct_2(C_118, '#skF_2', B_117) | ~v1_funct_1(C_118))), inference(negUnitSimplification, [status(thm)], [c_46, c_466])).
% 2.73/1.40  tff(c_498, plain, (k3_funct_2('#skF_2', '#skF_3', '#skF_5', '#skF_4')=k1_funct_1('#skF_5', '#skF_4') | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_36, c_483])).
% 2.73/1.40  tff(c_516, plain, (k3_funct_2('#skF_2', '#skF_3', '#skF_5', '#skF_4')=k1_funct_1('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_498])).
% 2.73/1.40  tff(c_34, plain, (~r2_hidden(k3_funct_2('#skF_2', '#skF_3', '#skF_5', '#skF_4'), k2_relset_1('#skF_2', '#skF_3', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_129])).
% 2.73/1.40  tff(c_520, plain, (~r2_hidden(k1_funct_1('#skF_5', '#skF_4'), k2_relset_1('#skF_2', '#skF_3', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_516, c_34])).
% 2.73/1.40  tff(c_527, plain, (k1_xboole_0='#skF_3' | ~r2_hidden('#skF_4', '#skF_2') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_32, c_520])).
% 2.73/1.40  tff(c_533, plain, (k1_xboole_0='#skF_3' | ~r2_hidden('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_36, c_527])).
% 2.73/1.40  tff(c_535, plain, (~r2_hidden('#skF_4', '#skF_2')), inference(splitLeft, [status(thm)], [c_533])).
% 2.73/1.40  tff(c_538, plain, (v1_xboole_0('#skF_2') | ~m1_subset_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_14, c_535])).
% 2.73/1.40  tff(c_541, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_538])).
% 2.73/1.40  tff(c_543, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_541])).
% 2.73/1.40  tff(c_544, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_533])).
% 2.73/1.40  tff(c_8, plain, (![A_3]: (m1_subset_1('#skF_1'(A_3), A_3))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.73/1.40  tff(c_10, plain, (![A_5]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.73/1.40  tff(c_73, plain, (![A_49, B_50]: (r1_tarski(A_49, B_50) | ~m1_subset_1(A_49, k1_zfmisc_1(B_50)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.73/1.40  tff(c_90, plain, (![A_5]: (r1_tarski(k1_xboole_0, A_5))), inference(resolution, [status(thm)], [c_10, c_73])).
% 2.73/1.40  tff(c_109, plain, (![B_57, A_58]: (v1_xboole_0(B_57) | ~m1_subset_1(B_57, k1_zfmisc_1(A_58)) | ~v1_xboole_0(A_58))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.73/1.40  tff(c_126, plain, (![A_5]: (v1_xboole_0(k1_xboole_0) | ~v1_xboole_0(A_5))), inference(resolution, [status(thm)], [c_10, c_109])).
% 2.73/1.40  tff(c_131, plain, (![A_5]: (~v1_xboole_0(A_5))), inference(splitLeft, [status(thm)], [c_126])).
% 2.73/1.40  tff(c_135, plain, (![A_60, B_61]: (r2_hidden(A_60, B_61) | ~m1_subset_1(A_60, B_61))), inference(negUnitSimplification, [status(thm)], [c_131, c_14])).
% 2.73/1.40  tff(c_22, plain, (![B_17, A_16]: (~r1_tarski(B_17, A_16) | ~r2_hidden(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.73/1.40  tff(c_165, plain, (![B_67, A_68]: (~r1_tarski(B_67, A_68) | ~m1_subset_1(A_68, B_67))), inference(resolution, [status(thm)], [c_135, c_22])).
% 2.73/1.40  tff(c_178, plain, (![A_69]: (~m1_subset_1(A_69, k1_xboole_0))), inference(resolution, [status(thm)], [c_90, c_165])).
% 2.73/1.40  tff(c_183, plain, $false, inference(resolution, [status(thm)], [c_8, c_178])).
% 2.73/1.40  tff(c_184, plain, (v1_xboole_0(k1_xboole_0)), inference(splitRight, [status(thm)], [c_126])).
% 2.73/1.40  tff(c_549, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_544, c_184])).
% 2.73/1.40  tff(c_556, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_549])).
% 2.73/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.73/1.40  
% 2.73/1.40  Inference rules
% 2.73/1.40  ----------------------
% 2.73/1.40  #Ref     : 0
% 2.73/1.40  #Sup     : 101
% 2.73/1.40  #Fact    : 0
% 2.73/1.40  #Define  : 0
% 2.73/1.40  #Split   : 7
% 2.73/1.40  #Chain   : 0
% 2.73/1.40  #Close   : 0
% 2.73/1.40  
% 2.73/1.40  Ordering : KBO
% 2.73/1.40  
% 2.73/1.40  Simplification rules
% 2.73/1.40  ----------------------
% 2.73/1.40  #Subsume      : 13
% 2.73/1.40  #Demod        : 40
% 2.73/1.40  #Tautology    : 23
% 2.73/1.40  #SimpNegUnit  : 13
% 2.73/1.40  #BackRed      : 12
% 2.73/1.40  
% 2.73/1.40  #Partial instantiations: 0
% 2.73/1.40  #Strategies tried      : 1
% 2.73/1.40  
% 2.73/1.40  Timing (in seconds)
% 2.73/1.40  ----------------------
% 2.73/1.40  Preprocessing        : 0.32
% 2.73/1.40  Parsing              : 0.17
% 2.73/1.40  CNF conversion       : 0.02
% 2.73/1.40  Main loop            : 0.32
% 2.73/1.40  Inferencing          : 0.11
% 2.73/1.40  Reduction            : 0.10
% 2.73/1.40  Demodulation         : 0.06
% 2.73/1.40  BG Simplification    : 0.02
% 2.73/1.41  Subsumption          : 0.06
% 2.73/1.41  Abstraction          : 0.02
% 2.73/1.41  MUC search           : 0.00
% 2.73/1.41  Cooper               : 0.00
% 2.73/1.41  Total                : 0.68
% 2.73/1.41  Index Insertion      : 0.00
% 2.73/1.41  Index Deletion       : 0.00
% 2.73/1.41  Index Matching       : 0.00
% 2.73/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
