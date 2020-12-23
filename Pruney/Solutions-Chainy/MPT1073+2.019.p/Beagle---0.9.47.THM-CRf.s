%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:00 EST 2020

% Result     : Theorem 2.70s
% Output     : CNFRefutation 2.70s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 118 expanded)
%              Number of leaves         :   33 (  56 expanded)
%              Depth                    :   11
%              Number of atoms          :   90 ( 236 expanded)
%              Number of equality atoms :   20 (  44 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k9_relat_1 > k7_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4

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

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_90,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,B,C)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
       => ~ ( r2_hidden(A,k2_relset_1(B,C,D))
            & ! [E] :
                ( m1_subset_1(E,B)
               => A != k1_funct_1(D,E) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t190_funct_2)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_40,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

tff(c_34,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_76,plain,(
    ! [A_43,B_44,C_45] :
      ( k2_relset_1(A_43,B_44,C_45) = k2_relat_1(C_45)
      | ~ m1_subset_1(C_45,k1_zfmisc_1(k2_zfmisc_1(A_43,B_44))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_80,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_34,c_76])).

tff(c_32,plain,(
    r2_hidden('#skF_2',k2_relset_1('#skF_3','#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_95,plain,(
    r2_hidden('#skF_2',k2_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_32])).

tff(c_45,plain,(
    ! [C_30,A_31,B_32] :
      ( v1_relat_1(C_30)
      | ~ m1_subset_1(C_30,k1_zfmisc_1(k2_zfmisc_1(A_31,B_32))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_49,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_34,c_45])).

tff(c_65,plain,(
    ! [C_40,A_41,B_42] :
      ( v4_relat_1(C_40,A_41)
      | ~ m1_subset_1(C_40,k1_zfmisc_1(k2_zfmisc_1(A_41,B_42))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_69,plain,(
    v4_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_65])).

tff(c_14,plain,(
    ! [B_12,A_11] :
      ( k7_relat_1(B_12,A_11) = B_12
      | ~ v4_relat_1(B_12,A_11)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_72,plain,
    ( k7_relat_1('#skF_5','#skF_3') = '#skF_5'
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_69,c_14])).

tff(c_75,plain,(
    k7_relat_1('#skF_5','#skF_3') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_49,c_72])).

tff(c_12,plain,(
    ! [B_10,A_9] :
      ( k2_relat_1(k7_relat_1(B_10,A_9)) = k9_relat_1(B_10,A_9)
      | ~ v1_relat_1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_84,plain,
    ( k9_relat_1('#skF_5','#skF_3') = k2_relat_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_75,c_12])).

tff(c_88,plain,(
    k9_relat_1('#skF_5','#skF_3') = k2_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_49,c_84])).

tff(c_106,plain,(
    ! [A_49,B_50,C_51] :
      ( r2_hidden('#skF_1'(A_49,B_50,C_51),B_50)
      | ~ r2_hidden(A_49,k9_relat_1(C_51,B_50))
      | ~ v1_relat_1(C_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(A_1,B_2)
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_117,plain,(
    ! [A_58,B_59,C_60] :
      ( m1_subset_1('#skF_1'(A_58,B_59,C_60),B_59)
      | ~ r2_hidden(A_58,k9_relat_1(C_60,B_59))
      | ~ v1_relat_1(C_60) ) ),
    inference(resolution,[status(thm)],[c_106,c_2])).

tff(c_122,plain,(
    ! [A_58] :
      ( m1_subset_1('#skF_1'(A_58,'#skF_3','#skF_5'),'#skF_3')
      | ~ r2_hidden(A_58,k2_relat_1('#skF_5'))
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_117])).

tff(c_126,plain,(
    ! [A_61] :
      ( m1_subset_1('#skF_1'(A_61,'#skF_3','#skF_5'),'#skF_3')
      | ~ r2_hidden(A_61,k2_relat_1('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_49,c_122])).

tff(c_135,plain,(
    m1_subset_1('#skF_1'('#skF_2','#skF_3','#skF_5'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_95,c_126])).

tff(c_30,plain,(
    ! [E_26] :
      ( k1_funct_1('#skF_5',E_26) != '#skF_2'
      | ~ m1_subset_1(E_26,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_139,plain,(
    k1_funct_1('#skF_5','#skF_1'('#skF_2','#skF_3','#skF_5')) != '#skF_2' ),
    inference(resolution,[status(thm)],[c_135,c_30])).

tff(c_38,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_141,plain,(
    ! [A_65,B_66,C_67] :
      ( r2_hidden(k4_tarski('#skF_1'(A_65,B_66,C_67),A_65),C_67)
      | ~ r2_hidden(A_65,k9_relat_1(C_67,B_66))
      | ~ v1_relat_1(C_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_18,plain,(
    ! [C_15,A_13,B_14] :
      ( k1_funct_1(C_15,A_13) = B_14
      | ~ r2_hidden(k4_tarski(A_13,B_14),C_15)
      | ~ v1_funct_1(C_15)
      | ~ v1_relat_1(C_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_254,plain,(
    ! [C_79,A_80,B_81] :
      ( k1_funct_1(C_79,'#skF_1'(A_80,B_81,C_79)) = A_80
      | ~ v1_funct_1(C_79)
      | ~ r2_hidden(A_80,k9_relat_1(C_79,B_81))
      | ~ v1_relat_1(C_79) ) ),
    inference(resolution,[status(thm)],[c_141,c_18])).

tff(c_265,plain,(
    ! [A_80] :
      ( k1_funct_1('#skF_5','#skF_1'(A_80,'#skF_3','#skF_5')) = A_80
      | ~ v1_funct_1('#skF_5')
      | ~ r2_hidden(A_80,k2_relat_1('#skF_5'))
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_254])).

tff(c_271,plain,(
    ! [A_82] :
      ( k1_funct_1('#skF_5','#skF_1'(A_82,'#skF_3','#skF_5')) = A_82
      | ~ r2_hidden(A_82,k2_relat_1('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_49,c_38,c_265])).

tff(c_286,plain,(
    k1_funct_1('#skF_5','#skF_1'('#skF_2','#skF_3','#skF_5')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_95,c_271])).

tff(c_293,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_139,c_286])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n021.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:05:49 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.70/1.39  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.70/1.40  
% 2.70/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.70/1.40  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k9_relat_1 > k7_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4
% 2.70/1.40  
% 2.70/1.40  %Foreground sorts:
% 2.70/1.40  
% 2.70/1.40  
% 2.70/1.40  %Background operators:
% 2.70/1.40  
% 2.70/1.40  
% 2.70/1.40  %Foreground operators:
% 2.70/1.40  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.70/1.40  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.70/1.40  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.70/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.70/1.40  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.70/1.40  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.70/1.40  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.70/1.40  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.70/1.40  tff('#skF_5', type, '#skF_5': $i).
% 2.70/1.40  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.70/1.40  tff('#skF_2', type, '#skF_2': $i).
% 2.70/1.40  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.70/1.40  tff('#skF_3', type, '#skF_3': $i).
% 2.70/1.40  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.70/1.40  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.70/1.40  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.70/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.70/1.40  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.70/1.40  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.70/1.40  tff('#skF_4', type, '#skF_4': $i).
% 2.70/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.70/1.40  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.70/1.40  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.70/1.40  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.70/1.40  
% 2.70/1.42  tff(f_90, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ~(r2_hidden(A, k2_relset_1(B, C, D)) & (![E]: (m1_subset_1(E, B) => ~(A = k1_funct_1(D, E))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t190_funct_2)).
% 2.70/1.42  tff(f_74, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.70/1.42  tff(f_64, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.70/1.42  tff(f_70, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.70/1.42  tff(f_50, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 2.70/1.42  tff(f_44, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 2.70/1.42  tff(f_40, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t143_relat_1)).
% 2.70/1.42  tff(f_29, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 2.70/1.42  tff(f_60, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_funct_1)).
% 2.70/1.42  tff(c_34, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.70/1.42  tff(c_76, plain, (![A_43, B_44, C_45]: (k2_relset_1(A_43, B_44, C_45)=k2_relat_1(C_45) | ~m1_subset_1(C_45, k1_zfmisc_1(k2_zfmisc_1(A_43, B_44))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.70/1.42  tff(c_80, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_34, c_76])).
% 2.70/1.42  tff(c_32, plain, (r2_hidden('#skF_2', k2_relset_1('#skF_3', '#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.70/1.42  tff(c_95, plain, (r2_hidden('#skF_2', k2_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_32])).
% 2.70/1.42  tff(c_45, plain, (![C_30, A_31, B_32]: (v1_relat_1(C_30) | ~m1_subset_1(C_30, k1_zfmisc_1(k2_zfmisc_1(A_31, B_32))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.70/1.42  tff(c_49, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_34, c_45])).
% 2.70/1.42  tff(c_65, plain, (![C_40, A_41, B_42]: (v4_relat_1(C_40, A_41) | ~m1_subset_1(C_40, k1_zfmisc_1(k2_zfmisc_1(A_41, B_42))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.70/1.42  tff(c_69, plain, (v4_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_34, c_65])).
% 2.70/1.42  tff(c_14, plain, (![B_12, A_11]: (k7_relat_1(B_12, A_11)=B_12 | ~v4_relat_1(B_12, A_11) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.70/1.42  tff(c_72, plain, (k7_relat_1('#skF_5', '#skF_3')='#skF_5' | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_69, c_14])).
% 2.70/1.42  tff(c_75, plain, (k7_relat_1('#skF_5', '#skF_3')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_49, c_72])).
% 2.70/1.42  tff(c_12, plain, (![B_10, A_9]: (k2_relat_1(k7_relat_1(B_10, A_9))=k9_relat_1(B_10, A_9) | ~v1_relat_1(B_10))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.70/1.42  tff(c_84, plain, (k9_relat_1('#skF_5', '#skF_3')=k2_relat_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_75, c_12])).
% 2.70/1.42  tff(c_88, plain, (k9_relat_1('#skF_5', '#skF_3')=k2_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_49, c_84])).
% 2.70/1.42  tff(c_106, plain, (![A_49, B_50, C_51]: (r2_hidden('#skF_1'(A_49, B_50, C_51), B_50) | ~r2_hidden(A_49, k9_relat_1(C_51, B_50)) | ~v1_relat_1(C_51))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.70/1.42  tff(c_2, plain, (![A_1, B_2]: (m1_subset_1(A_1, B_2) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.70/1.42  tff(c_117, plain, (![A_58, B_59, C_60]: (m1_subset_1('#skF_1'(A_58, B_59, C_60), B_59) | ~r2_hidden(A_58, k9_relat_1(C_60, B_59)) | ~v1_relat_1(C_60))), inference(resolution, [status(thm)], [c_106, c_2])).
% 2.70/1.42  tff(c_122, plain, (![A_58]: (m1_subset_1('#skF_1'(A_58, '#skF_3', '#skF_5'), '#skF_3') | ~r2_hidden(A_58, k2_relat_1('#skF_5')) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_88, c_117])).
% 2.70/1.42  tff(c_126, plain, (![A_61]: (m1_subset_1('#skF_1'(A_61, '#skF_3', '#skF_5'), '#skF_3') | ~r2_hidden(A_61, k2_relat_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_49, c_122])).
% 2.70/1.42  tff(c_135, plain, (m1_subset_1('#skF_1'('#skF_2', '#skF_3', '#skF_5'), '#skF_3')), inference(resolution, [status(thm)], [c_95, c_126])).
% 2.70/1.42  tff(c_30, plain, (![E_26]: (k1_funct_1('#skF_5', E_26)!='#skF_2' | ~m1_subset_1(E_26, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.70/1.42  tff(c_139, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_2', '#skF_3', '#skF_5'))!='#skF_2'), inference(resolution, [status(thm)], [c_135, c_30])).
% 2.70/1.42  tff(c_38, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.70/1.42  tff(c_141, plain, (![A_65, B_66, C_67]: (r2_hidden(k4_tarski('#skF_1'(A_65, B_66, C_67), A_65), C_67) | ~r2_hidden(A_65, k9_relat_1(C_67, B_66)) | ~v1_relat_1(C_67))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.70/1.42  tff(c_18, plain, (![C_15, A_13, B_14]: (k1_funct_1(C_15, A_13)=B_14 | ~r2_hidden(k4_tarski(A_13, B_14), C_15) | ~v1_funct_1(C_15) | ~v1_relat_1(C_15))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.70/1.42  tff(c_254, plain, (![C_79, A_80, B_81]: (k1_funct_1(C_79, '#skF_1'(A_80, B_81, C_79))=A_80 | ~v1_funct_1(C_79) | ~r2_hidden(A_80, k9_relat_1(C_79, B_81)) | ~v1_relat_1(C_79))), inference(resolution, [status(thm)], [c_141, c_18])).
% 2.70/1.42  tff(c_265, plain, (![A_80]: (k1_funct_1('#skF_5', '#skF_1'(A_80, '#skF_3', '#skF_5'))=A_80 | ~v1_funct_1('#skF_5') | ~r2_hidden(A_80, k2_relat_1('#skF_5')) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_88, c_254])).
% 2.70/1.42  tff(c_271, plain, (![A_82]: (k1_funct_1('#skF_5', '#skF_1'(A_82, '#skF_3', '#skF_5'))=A_82 | ~r2_hidden(A_82, k2_relat_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_49, c_38, c_265])).
% 2.70/1.42  tff(c_286, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_2', '#skF_3', '#skF_5'))='#skF_2'), inference(resolution, [status(thm)], [c_95, c_271])).
% 2.70/1.42  tff(c_293, plain, $false, inference(negUnitSimplification, [status(thm)], [c_139, c_286])).
% 2.70/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.70/1.42  
% 2.70/1.42  Inference rules
% 2.70/1.42  ----------------------
% 2.70/1.42  #Ref     : 0
% 2.70/1.42  #Sup     : 56
% 2.70/1.42  #Fact    : 0
% 2.70/1.42  #Define  : 0
% 2.70/1.42  #Split   : 0
% 2.70/1.42  #Chain   : 0
% 2.70/1.42  #Close   : 0
% 2.70/1.42  
% 2.70/1.42  Ordering : KBO
% 2.70/1.42  
% 2.70/1.42  Simplification rules
% 2.70/1.42  ----------------------
% 2.70/1.42  #Subsume      : 1
% 2.70/1.42  #Demod        : 8
% 2.70/1.42  #Tautology    : 11
% 2.70/1.42  #SimpNegUnit  : 1
% 2.70/1.42  #BackRed      : 2
% 2.70/1.42  
% 2.70/1.42  #Partial instantiations: 0
% 2.70/1.42  #Strategies tried      : 1
% 2.70/1.42  
% 2.70/1.42  Timing (in seconds)
% 2.70/1.42  ----------------------
% 2.70/1.42  Preprocessing        : 0.33
% 2.70/1.42  Parsing              : 0.17
% 2.70/1.42  CNF conversion       : 0.02
% 2.70/1.42  Main loop            : 0.32
% 2.70/1.42  Inferencing          : 0.13
% 2.70/1.42  Reduction            : 0.09
% 2.70/1.42  Demodulation         : 0.06
% 2.70/1.42  BG Simplification    : 0.02
% 2.70/1.42  Subsumption          : 0.06
% 2.70/1.42  Abstraction          : 0.02
% 2.70/1.42  MUC search           : 0.00
% 2.70/1.42  Cooper               : 0.00
% 2.70/1.42  Total                : 0.69
% 2.70/1.42  Index Insertion      : 0.00
% 2.70/1.42  Index Deletion       : 0.00
% 2.70/1.42  Index Matching       : 0.00
% 2.70/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
