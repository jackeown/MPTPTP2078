%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:05 EST 2020

% Result     : Theorem 2.77s
% Output     : CNFRefutation 2.77s
% Verified   : 
% Statistics : Number of formulae       :   61 (  92 expanded)
%              Number of leaves         :   33 (  48 expanded)
%              Depth                    :    8
%              Number of atoms          :   87 ( 181 expanded)
%              Number of equality atoms :   19 (  36 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4

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

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_38,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_101,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,B,C)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
       => ~ ( r2_hidden(A,k2_relset_1(B,C,D))
            & ! [E] :
                ( m1_subset_1(E,B)
               => A != k1_funct_1(D,E) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t190_funct_2)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_79,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_85,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( k7_relset_1(A,B,C,A) = k2_relset_1(A,B,C)
        & k8_relset_1(A,B,C,B) = k1_relset_1(A,B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_relset_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_75,axiom,(
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

tff(c_6,plain,(
    ! [A_6,B_7] : v1_relat_1(k2_zfmisc_1(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_38,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_50,plain,(
    ! [B_36,A_37] :
      ( v1_relat_1(B_36)
      | ~ m1_subset_1(B_36,k1_zfmisc_1(A_37))
      | ~ v1_relat_1(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_53,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_38,c_50])).

tff(c_56,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_53])).

tff(c_80,plain,(
    ! [A_51,B_52,C_53,D_54] :
      ( k7_relset_1(A_51,B_52,C_53,D_54) = k9_relat_1(C_53,D_54)
      | ~ m1_subset_1(C_53,k1_zfmisc_1(k2_zfmisc_1(A_51,B_52))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_83,plain,(
    ! [D_54] : k7_relset_1('#skF_3','#skF_4','#skF_5',D_54) = k9_relat_1('#skF_5',D_54) ),
    inference(resolution,[status(thm)],[c_38,c_80])).

tff(c_162,plain,(
    ! [A_76,B_77,C_78] :
      ( k7_relset_1(A_76,B_77,C_78,A_76) = k2_relset_1(A_76,B_77,C_78)
      | ~ m1_subset_1(C_78,k1_zfmisc_1(k2_zfmisc_1(A_76,B_77))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_164,plain,(
    k7_relset_1('#skF_3','#skF_4','#skF_5','#skF_3') = k2_relset_1('#skF_3','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_38,c_162])).

tff(c_166,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k9_relat_1('#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_164])).

tff(c_36,plain,(
    r2_hidden('#skF_2',k2_relset_1('#skF_3','#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_168,plain,(
    r2_hidden('#skF_2',k9_relat_1('#skF_5','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_166,c_36])).

tff(c_75,plain,(
    ! [A_48,B_49,C_50] :
      ( r2_hidden('#skF_1'(A_48,B_49,C_50),B_49)
      | ~ r2_hidden(A_48,k9_relat_1(C_50,B_49))
      | ~ v1_relat_1(C_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(A_1,B_2)
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_79,plain,(
    ! [A_48,B_49,C_50] :
      ( m1_subset_1('#skF_1'(A_48,B_49,C_50),B_49)
      | ~ r2_hidden(A_48,k9_relat_1(C_50,B_49))
      | ~ v1_relat_1(C_50) ) ),
    inference(resolution,[status(thm)],[c_75,c_2])).

tff(c_177,plain,
    ( m1_subset_1('#skF_1'('#skF_2','#skF_3','#skF_5'),'#skF_3')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_168,c_79])).

tff(c_186,plain,(
    m1_subset_1('#skF_1'('#skF_2','#skF_3','#skF_5'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_177])).

tff(c_34,plain,(
    ! [E_30] :
      ( k1_funct_1('#skF_5',E_30) != '#skF_2'
      | ~ m1_subset_1(E_30,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_196,plain,(
    k1_funct_1('#skF_5','#skF_1'('#skF_2','#skF_3','#skF_5')) != '#skF_2' ),
    inference(resolution,[status(thm)],[c_186,c_34])).

tff(c_42,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_14,plain,(
    ! [A_8,B_9,C_10] :
      ( r2_hidden('#skF_1'(A_8,B_9,C_10),k1_relat_1(C_10))
      | ~ r2_hidden(A_8,k9_relat_1(C_10,B_9))
      | ~ v1_relat_1(C_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_12,plain,(
    ! [A_8,B_9,C_10] :
      ( r2_hidden(k4_tarski('#skF_1'(A_8,B_9,C_10),A_8),C_10)
      | ~ r2_hidden(A_8,k9_relat_1(C_10,B_9))
      | ~ v1_relat_1(C_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_203,plain,(
    ! [A_83,B_84,C_85] :
      ( k1_funct_1(A_83,B_84) = C_85
      | ~ r2_hidden(k4_tarski(B_84,C_85),A_83)
      | ~ r2_hidden(B_84,k1_relat_1(A_83))
      | ~ v1_funct_1(A_83)
      | ~ v1_relat_1(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_556,plain,(
    ! [C_126,A_127,B_128] :
      ( k1_funct_1(C_126,'#skF_1'(A_127,B_128,C_126)) = A_127
      | ~ r2_hidden('#skF_1'(A_127,B_128,C_126),k1_relat_1(C_126))
      | ~ v1_funct_1(C_126)
      | ~ r2_hidden(A_127,k9_relat_1(C_126,B_128))
      | ~ v1_relat_1(C_126) ) ),
    inference(resolution,[status(thm)],[c_12,c_203])).

tff(c_576,plain,(
    ! [C_129,A_130,B_131] :
      ( k1_funct_1(C_129,'#skF_1'(A_130,B_131,C_129)) = A_130
      | ~ v1_funct_1(C_129)
      | ~ r2_hidden(A_130,k9_relat_1(C_129,B_131))
      | ~ v1_relat_1(C_129) ) ),
    inference(resolution,[status(thm)],[c_14,c_556])).

tff(c_582,plain,
    ( k1_funct_1('#skF_5','#skF_1'('#skF_2','#skF_3','#skF_5')) = '#skF_2'
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_168,c_576])).

tff(c_596,plain,(
    k1_funct_1('#skF_5','#skF_1'('#skF_2','#skF_3','#skF_5')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_42,c_582])).

tff(c_598,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_196,c_596])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:07:44 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.77/1.41  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.77/1.41  
% 2.77/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.77/1.42  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4
% 2.77/1.42  
% 2.77/1.42  %Foreground sorts:
% 2.77/1.42  
% 2.77/1.42  
% 2.77/1.42  %Background operators:
% 2.77/1.42  
% 2.77/1.42  
% 2.77/1.42  %Foreground operators:
% 2.77/1.42  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.77/1.42  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.77/1.42  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.77/1.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.77/1.42  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.77/1.42  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.77/1.42  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 2.77/1.42  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.77/1.42  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.77/1.42  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.77/1.42  tff('#skF_5', type, '#skF_5': $i).
% 2.77/1.42  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.77/1.42  tff('#skF_2', type, '#skF_2': $i).
% 2.77/1.42  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.77/1.42  tff('#skF_3', type, '#skF_3': $i).
% 2.77/1.42  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.77/1.42  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.77/1.42  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.77/1.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.77/1.42  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.77/1.42  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.77/1.42  tff('#skF_4', type, '#skF_4': $i).
% 2.77/1.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.77/1.42  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.77/1.42  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.77/1.42  
% 2.77/1.43  tff(f_38, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.77/1.43  tff(f_101, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ~(r2_hidden(A, k2_relset_1(B, C, D)) & (![E]: (m1_subset_1(E, B) => ~(A = k1_funct_1(D, E))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t190_funct_2)).
% 2.77/1.43  tff(f_36, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.77/1.43  tff(f_79, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 2.77/1.43  tff(f_85, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((k7_relset_1(A, B, C, A) = k2_relset_1(A, B, C)) & (k8_relset_1(A, B, C, B) = k1_relset_1(A, B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_relset_1)).
% 2.77/1.43  tff(f_49, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_relat_1)).
% 2.77/1.43  tff(f_29, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 2.77/1.43  tff(f_75, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: ((r2_hidden(B, k1_relat_1(A)) => ((C = k1_funct_1(A, B)) <=> r2_hidden(k4_tarski(B, C), A))) & (~r2_hidden(B, k1_relat_1(A)) => ((C = k1_funct_1(A, B)) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_funct_1)).
% 2.77/1.43  tff(c_6, plain, (![A_6, B_7]: (v1_relat_1(k2_zfmisc_1(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.77/1.43  tff(c_38, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.77/1.43  tff(c_50, plain, (![B_36, A_37]: (v1_relat_1(B_36) | ~m1_subset_1(B_36, k1_zfmisc_1(A_37)) | ~v1_relat_1(A_37))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.77/1.43  tff(c_53, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_38, c_50])).
% 2.77/1.43  tff(c_56, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_53])).
% 2.77/1.43  tff(c_80, plain, (![A_51, B_52, C_53, D_54]: (k7_relset_1(A_51, B_52, C_53, D_54)=k9_relat_1(C_53, D_54) | ~m1_subset_1(C_53, k1_zfmisc_1(k2_zfmisc_1(A_51, B_52))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.77/1.43  tff(c_83, plain, (![D_54]: (k7_relset_1('#skF_3', '#skF_4', '#skF_5', D_54)=k9_relat_1('#skF_5', D_54))), inference(resolution, [status(thm)], [c_38, c_80])).
% 2.77/1.43  tff(c_162, plain, (![A_76, B_77, C_78]: (k7_relset_1(A_76, B_77, C_78, A_76)=k2_relset_1(A_76, B_77, C_78) | ~m1_subset_1(C_78, k1_zfmisc_1(k2_zfmisc_1(A_76, B_77))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.77/1.43  tff(c_164, plain, (k7_relset_1('#skF_3', '#skF_4', '#skF_5', '#skF_3')=k2_relset_1('#skF_3', '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_38, c_162])).
% 2.77/1.43  tff(c_166, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k9_relat_1('#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_83, c_164])).
% 2.77/1.43  tff(c_36, plain, (r2_hidden('#skF_2', k2_relset_1('#skF_3', '#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.77/1.43  tff(c_168, plain, (r2_hidden('#skF_2', k9_relat_1('#skF_5', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_166, c_36])).
% 2.77/1.43  tff(c_75, plain, (![A_48, B_49, C_50]: (r2_hidden('#skF_1'(A_48, B_49, C_50), B_49) | ~r2_hidden(A_48, k9_relat_1(C_50, B_49)) | ~v1_relat_1(C_50))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.77/1.43  tff(c_2, plain, (![A_1, B_2]: (m1_subset_1(A_1, B_2) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.77/1.43  tff(c_79, plain, (![A_48, B_49, C_50]: (m1_subset_1('#skF_1'(A_48, B_49, C_50), B_49) | ~r2_hidden(A_48, k9_relat_1(C_50, B_49)) | ~v1_relat_1(C_50))), inference(resolution, [status(thm)], [c_75, c_2])).
% 2.77/1.43  tff(c_177, plain, (m1_subset_1('#skF_1'('#skF_2', '#skF_3', '#skF_5'), '#skF_3') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_168, c_79])).
% 2.77/1.43  tff(c_186, plain, (m1_subset_1('#skF_1'('#skF_2', '#skF_3', '#skF_5'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_177])).
% 2.77/1.43  tff(c_34, plain, (![E_30]: (k1_funct_1('#skF_5', E_30)!='#skF_2' | ~m1_subset_1(E_30, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.77/1.43  tff(c_196, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_2', '#skF_3', '#skF_5'))!='#skF_2'), inference(resolution, [status(thm)], [c_186, c_34])).
% 2.77/1.43  tff(c_42, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.77/1.43  tff(c_14, plain, (![A_8, B_9, C_10]: (r2_hidden('#skF_1'(A_8, B_9, C_10), k1_relat_1(C_10)) | ~r2_hidden(A_8, k9_relat_1(C_10, B_9)) | ~v1_relat_1(C_10))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.77/1.43  tff(c_12, plain, (![A_8, B_9, C_10]: (r2_hidden(k4_tarski('#skF_1'(A_8, B_9, C_10), A_8), C_10) | ~r2_hidden(A_8, k9_relat_1(C_10, B_9)) | ~v1_relat_1(C_10))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.77/1.43  tff(c_203, plain, (![A_83, B_84, C_85]: (k1_funct_1(A_83, B_84)=C_85 | ~r2_hidden(k4_tarski(B_84, C_85), A_83) | ~r2_hidden(B_84, k1_relat_1(A_83)) | ~v1_funct_1(A_83) | ~v1_relat_1(A_83))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.77/1.43  tff(c_556, plain, (![C_126, A_127, B_128]: (k1_funct_1(C_126, '#skF_1'(A_127, B_128, C_126))=A_127 | ~r2_hidden('#skF_1'(A_127, B_128, C_126), k1_relat_1(C_126)) | ~v1_funct_1(C_126) | ~r2_hidden(A_127, k9_relat_1(C_126, B_128)) | ~v1_relat_1(C_126))), inference(resolution, [status(thm)], [c_12, c_203])).
% 2.77/1.43  tff(c_576, plain, (![C_129, A_130, B_131]: (k1_funct_1(C_129, '#skF_1'(A_130, B_131, C_129))=A_130 | ~v1_funct_1(C_129) | ~r2_hidden(A_130, k9_relat_1(C_129, B_131)) | ~v1_relat_1(C_129))), inference(resolution, [status(thm)], [c_14, c_556])).
% 2.77/1.43  tff(c_582, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_2', '#skF_3', '#skF_5'))='#skF_2' | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_168, c_576])).
% 2.77/1.43  tff(c_596, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_2', '#skF_3', '#skF_5'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_42, c_582])).
% 2.77/1.43  tff(c_598, plain, $false, inference(negUnitSimplification, [status(thm)], [c_196, c_596])).
% 2.77/1.43  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.77/1.43  
% 2.77/1.43  Inference rules
% 2.77/1.43  ----------------------
% 2.77/1.43  #Ref     : 0
% 2.77/1.43  #Sup     : 131
% 2.77/1.43  #Fact    : 0
% 2.77/1.43  #Define  : 0
% 2.77/1.43  #Split   : 2
% 2.77/1.43  #Chain   : 0
% 2.77/1.43  #Close   : 0
% 2.77/1.43  
% 2.77/1.43  Ordering : KBO
% 2.77/1.43  
% 2.77/1.43  Simplification rules
% 2.77/1.43  ----------------------
% 2.77/1.43  #Subsume      : 16
% 2.77/1.43  #Demod        : 9
% 2.77/1.43  #Tautology    : 29
% 2.77/1.43  #SimpNegUnit  : 1
% 2.77/1.43  #BackRed      : 2
% 2.77/1.43  
% 2.77/1.43  #Partial instantiations: 0
% 2.77/1.43  #Strategies tried      : 1
% 2.77/1.43  
% 2.77/1.43  Timing (in seconds)
% 2.77/1.43  ----------------------
% 2.77/1.43  Preprocessing        : 0.32
% 2.77/1.43  Parsing              : 0.17
% 2.77/1.43  CNF conversion       : 0.02
% 2.77/1.43  Main loop            : 0.35
% 2.77/1.43  Inferencing          : 0.14
% 2.77/1.43  Reduction            : 0.10
% 2.77/1.43  Demodulation         : 0.07
% 2.77/1.43  BG Simplification    : 0.02
% 2.77/1.43  Subsumption          : 0.07
% 2.77/1.43  Abstraction          : 0.02
% 2.77/1.43  MUC search           : 0.00
% 2.77/1.43  Cooper               : 0.00
% 2.77/1.43  Total                : 0.70
% 2.77/1.43  Index Insertion      : 0.00
% 2.77/1.43  Index Deletion       : 0.00
% 2.77/1.43  Index Matching       : 0.00
% 2.77/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
