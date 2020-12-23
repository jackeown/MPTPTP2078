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
% DateTime   : Thu Dec  3 10:18:03 EST 2020

% Result     : Theorem 2.49s
% Output     : CNFRefutation 2.49s
% Verified   : 
% Statistics : Number of formulae       :   62 (  93 expanded)
%              Number of leaves         :   32 (  47 expanded)
%              Depth                    :   10
%              Number of atoms          :   85 ( 182 expanded)
%              Number of equality atoms :   19 (  38 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4

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

tff(f_90,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,B,C)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
       => ~ ( r2_hidden(A,k2_relset_1(B,C,D))
            & ! [E] :
                ( m1_subset_1(E,B)
               => A != k1_funct_1(D,E) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t190_funct_2)).

tff(f_68,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( k7_relset_1(A,B,C,A) = k2_relset_1(A,B,C)
        & k8_relset_1(A,B,C,B) = k1_relset_1(A,B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_relset_1)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k1_relset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_relset_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

tff(c_34,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_90,plain,(
    ! [A_55,B_56,C_57,D_58] :
      ( k7_relset_1(A_55,B_56,C_57,D_58) = k9_relat_1(C_57,D_58)
      | ~ m1_subset_1(C_57,k1_zfmisc_1(k2_zfmisc_1(A_55,B_56))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_97,plain,(
    ! [D_58] : k7_relset_1('#skF_3','#skF_4','#skF_5',D_58) = k9_relat_1('#skF_5',D_58) ),
    inference(resolution,[status(thm)],[c_34,c_90])).

tff(c_127,plain,(
    ! [A_67,B_68,C_69] :
      ( k7_relset_1(A_67,B_68,C_69,A_67) = k2_relset_1(A_67,B_68,C_69)
      | ~ m1_subset_1(C_69,k1_zfmisc_1(k2_zfmisc_1(A_67,B_68))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_132,plain,(
    k7_relset_1('#skF_3','#skF_4','#skF_5','#skF_3') = k2_relset_1('#skF_3','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_34,c_127])).

tff(c_135,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k9_relat_1('#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_132])).

tff(c_32,plain,(
    r2_hidden('#skF_2',k2_relset_1('#skF_3','#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_136,plain,(
    r2_hidden('#skF_2',k9_relat_1('#skF_5','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_32])).

tff(c_40,plain,(
    ! [C_32,A_33,B_34] :
      ( v1_relat_1(C_32)
      | ~ m1_subset_1(C_32,k1_zfmisc_1(k2_zfmisc_1(A_33,B_34))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_44,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_34,c_40])).

tff(c_113,plain,(
    ! [A_62,B_63,C_64] :
      ( r2_hidden('#skF_1'(A_62,B_63,C_64),k1_relat_1(C_64))
      | ~ r2_hidden(A_62,k9_relat_1(C_64,B_63))
      | ~ v1_relat_1(C_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_50,plain,(
    ! [A_39,B_40,C_41] :
      ( k1_relset_1(A_39,B_40,C_41) = k1_relat_1(C_41)
      | ~ m1_subset_1(C_41,k1_zfmisc_1(k2_zfmisc_1(A_39,B_40))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_54,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_34,c_50])).

tff(c_60,plain,(
    ! [A_45,B_46,C_47] :
      ( m1_subset_1(k1_relset_1(A_45,B_46,C_47),k1_zfmisc_1(A_45))
      | ~ m1_subset_1(C_47,k1_zfmisc_1(k2_zfmisc_1(A_45,B_46))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_73,plain,
    ( m1_subset_1(k1_relat_1('#skF_5'),k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_60])).

tff(c_78,plain,(
    m1_subset_1(k1_relat_1('#skF_5'),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_73])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( m1_subset_1(A_1,C_3)
      | ~ m1_subset_1(B_2,k1_zfmisc_1(C_3))
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_81,plain,(
    ! [A_1] :
      ( m1_subset_1(A_1,'#skF_3')
      | ~ r2_hidden(A_1,k1_relat_1('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_78,c_2])).

tff(c_117,plain,(
    ! [A_62,B_63] :
      ( m1_subset_1('#skF_1'(A_62,B_63,'#skF_5'),'#skF_3')
      | ~ r2_hidden(A_62,k9_relat_1('#skF_5',B_63))
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_113,c_81])).

tff(c_120,plain,(
    ! [A_62,B_63] :
      ( m1_subset_1('#skF_1'(A_62,B_63,'#skF_5'),'#skF_3')
      | ~ r2_hidden(A_62,k9_relat_1('#skF_5',B_63)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_117])).

tff(c_144,plain,(
    m1_subset_1('#skF_1'('#skF_2','#skF_3','#skF_5'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_136,c_120])).

tff(c_30,plain,(
    ! [E_30] :
      ( k1_funct_1('#skF_5',E_30) != '#skF_2'
      | ~ m1_subset_1(E_30,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_172,plain,(
    k1_funct_1('#skF_5','#skF_1'('#skF_2','#skF_3','#skF_5')) != '#skF_2' ),
    inference(resolution,[status(thm)],[c_144,c_30])).

tff(c_38,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_145,plain,(
    ! [A_70,B_71,C_72] :
      ( r2_hidden(k4_tarski('#skF_1'(A_70,B_71,C_72),A_70),C_72)
      | ~ r2_hidden(A_70,k9_relat_1(C_72,B_71))
      | ~ v1_relat_1(C_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_14,plain,(
    ! [C_12,A_10,B_11] :
      ( k1_funct_1(C_12,A_10) = B_11
      | ~ r2_hidden(k4_tarski(A_10,B_11),C_12)
      | ~ v1_funct_1(C_12)
      | ~ v1_relat_1(C_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_251,plain,(
    ! [C_90,A_91,B_92] :
      ( k1_funct_1(C_90,'#skF_1'(A_91,B_92,C_90)) = A_91
      | ~ v1_funct_1(C_90)
      | ~ r2_hidden(A_91,k9_relat_1(C_90,B_92))
      | ~ v1_relat_1(C_90) ) ),
    inference(resolution,[status(thm)],[c_145,c_14])).

tff(c_259,plain,
    ( k1_funct_1('#skF_5','#skF_1'('#skF_2','#skF_3','#skF_5')) = '#skF_2'
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_136,c_251])).

tff(c_267,plain,(
    k1_funct_1('#skF_5','#skF_1'('#skF_2','#skF_3','#skF_5')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_38,c_259])).

tff(c_269,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_172,c_267])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n018.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 15:23:42 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.49/1.40  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.49/1.41  
% 2.49/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.49/1.41  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4
% 2.49/1.41  
% 2.49/1.41  %Foreground sorts:
% 2.49/1.41  
% 2.49/1.41  
% 2.49/1.41  %Background operators:
% 2.49/1.41  
% 2.49/1.41  
% 2.49/1.41  %Foreground operators:
% 2.49/1.41  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.49/1.41  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.49/1.41  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.49/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.49/1.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.49/1.41  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.49/1.41  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 2.49/1.41  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.49/1.41  tff('#skF_5', type, '#skF_5': $i).
% 2.49/1.41  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.49/1.41  tff('#skF_2', type, '#skF_2': $i).
% 2.49/1.41  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.49/1.41  tff('#skF_3', type, '#skF_3': $i).
% 2.49/1.41  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.49/1.41  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.49/1.41  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.49/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.49/1.41  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.49/1.41  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.49/1.41  tff('#skF_4', type, '#skF_4': $i).
% 2.49/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.49/1.41  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.49/1.41  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.49/1.41  
% 2.49/1.42  tff(f_90, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ~(r2_hidden(A, k2_relset_1(B, C, D)) & (![E]: (m1_subset_1(E, B) => ~(A = k1_funct_1(D, E))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t190_funct_2)).
% 2.49/1.42  tff(f_68, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 2.49/1.42  tff(f_74, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((k7_relset_1(A, B, C, A) = k2_relset_1(A, B, C)) & (k8_relset_1(A, B, C, B) = k1_relset_1(A, B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_relset_1)).
% 2.49/1.42  tff(f_56, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.49/1.42  tff(f_42, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_relat_1)).
% 2.49/1.42  tff(f_64, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.49/1.42  tff(f_60, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k1_relset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_relset_1)).
% 2.49/1.42  tff(f_31, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 2.49/1.42  tff(f_52, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_1)).
% 2.49/1.42  tff(c_34, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.49/1.42  tff(c_90, plain, (![A_55, B_56, C_57, D_58]: (k7_relset_1(A_55, B_56, C_57, D_58)=k9_relat_1(C_57, D_58) | ~m1_subset_1(C_57, k1_zfmisc_1(k2_zfmisc_1(A_55, B_56))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.49/1.42  tff(c_97, plain, (![D_58]: (k7_relset_1('#skF_3', '#skF_4', '#skF_5', D_58)=k9_relat_1('#skF_5', D_58))), inference(resolution, [status(thm)], [c_34, c_90])).
% 2.49/1.42  tff(c_127, plain, (![A_67, B_68, C_69]: (k7_relset_1(A_67, B_68, C_69, A_67)=k2_relset_1(A_67, B_68, C_69) | ~m1_subset_1(C_69, k1_zfmisc_1(k2_zfmisc_1(A_67, B_68))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.49/1.42  tff(c_132, plain, (k7_relset_1('#skF_3', '#skF_4', '#skF_5', '#skF_3')=k2_relset_1('#skF_3', '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_34, c_127])).
% 2.49/1.42  tff(c_135, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k9_relat_1('#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_97, c_132])).
% 2.49/1.42  tff(c_32, plain, (r2_hidden('#skF_2', k2_relset_1('#skF_3', '#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.49/1.42  tff(c_136, plain, (r2_hidden('#skF_2', k9_relat_1('#skF_5', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_135, c_32])).
% 2.49/1.42  tff(c_40, plain, (![C_32, A_33, B_34]: (v1_relat_1(C_32) | ~m1_subset_1(C_32, k1_zfmisc_1(k2_zfmisc_1(A_33, B_34))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.49/1.42  tff(c_44, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_34, c_40])).
% 2.49/1.42  tff(c_113, plain, (![A_62, B_63, C_64]: (r2_hidden('#skF_1'(A_62, B_63, C_64), k1_relat_1(C_64)) | ~r2_hidden(A_62, k9_relat_1(C_64, B_63)) | ~v1_relat_1(C_64))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.49/1.42  tff(c_50, plain, (![A_39, B_40, C_41]: (k1_relset_1(A_39, B_40, C_41)=k1_relat_1(C_41) | ~m1_subset_1(C_41, k1_zfmisc_1(k2_zfmisc_1(A_39, B_40))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.49/1.42  tff(c_54, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_34, c_50])).
% 2.49/1.42  tff(c_60, plain, (![A_45, B_46, C_47]: (m1_subset_1(k1_relset_1(A_45, B_46, C_47), k1_zfmisc_1(A_45)) | ~m1_subset_1(C_47, k1_zfmisc_1(k2_zfmisc_1(A_45, B_46))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.49/1.42  tff(c_73, plain, (m1_subset_1(k1_relat_1('#skF_5'), k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_54, c_60])).
% 2.49/1.42  tff(c_78, plain, (m1_subset_1(k1_relat_1('#skF_5'), k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_73])).
% 2.49/1.42  tff(c_2, plain, (![A_1, C_3, B_2]: (m1_subset_1(A_1, C_3) | ~m1_subset_1(B_2, k1_zfmisc_1(C_3)) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.49/1.42  tff(c_81, plain, (![A_1]: (m1_subset_1(A_1, '#skF_3') | ~r2_hidden(A_1, k1_relat_1('#skF_5')))), inference(resolution, [status(thm)], [c_78, c_2])).
% 2.49/1.42  tff(c_117, plain, (![A_62, B_63]: (m1_subset_1('#skF_1'(A_62, B_63, '#skF_5'), '#skF_3') | ~r2_hidden(A_62, k9_relat_1('#skF_5', B_63)) | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_113, c_81])).
% 2.49/1.42  tff(c_120, plain, (![A_62, B_63]: (m1_subset_1('#skF_1'(A_62, B_63, '#skF_5'), '#skF_3') | ~r2_hidden(A_62, k9_relat_1('#skF_5', B_63)))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_117])).
% 2.49/1.42  tff(c_144, plain, (m1_subset_1('#skF_1'('#skF_2', '#skF_3', '#skF_5'), '#skF_3')), inference(resolution, [status(thm)], [c_136, c_120])).
% 2.49/1.42  tff(c_30, plain, (![E_30]: (k1_funct_1('#skF_5', E_30)!='#skF_2' | ~m1_subset_1(E_30, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.49/1.42  tff(c_172, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_2', '#skF_3', '#skF_5'))!='#skF_2'), inference(resolution, [status(thm)], [c_144, c_30])).
% 2.49/1.42  tff(c_38, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.49/1.42  tff(c_145, plain, (![A_70, B_71, C_72]: (r2_hidden(k4_tarski('#skF_1'(A_70, B_71, C_72), A_70), C_72) | ~r2_hidden(A_70, k9_relat_1(C_72, B_71)) | ~v1_relat_1(C_72))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.49/1.42  tff(c_14, plain, (![C_12, A_10, B_11]: (k1_funct_1(C_12, A_10)=B_11 | ~r2_hidden(k4_tarski(A_10, B_11), C_12) | ~v1_funct_1(C_12) | ~v1_relat_1(C_12))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.49/1.42  tff(c_251, plain, (![C_90, A_91, B_92]: (k1_funct_1(C_90, '#skF_1'(A_91, B_92, C_90))=A_91 | ~v1_funct_1(C_90) | ~r2_hidden(A_91, k9_relat_1(C_90, B_92)) | ~v1_relat_1(C_90))), inference(resolution, [status(thm)], [c_145, c_14])).
% 2.49/1.42  tff(c_259, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_2', '#skF_3', '#skF_5'))='#skF_2' | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_136, c_251])).
% 2.49/1.42  tff(c_267, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_2', '#skF_3', '#skF_5'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_44, c_38, c_259])).
% 2.49/1.42  tff(c_269, plain, $false, inference(negUnitSimplification, [status(thm)], [c_172, c_267])).
% 2.49/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.49/1.42  
% 2.49/1.42  Inference rules
% 2.49/1.42  ----------------------
% 2.49/1.42  #Ref     : 0
% 2.49/1.42  #Sup     : 52
% 2.49/1.42  #Fact    : 0
% 2.49/1.42  #Define  : 0
% 2.49/1.42  #Split   : 1
% 2.49/1.42  #Chain   : 0
% 2.49/1.42  #Close   : 0
% 2.49/1.42  
% 2.49/1.42  Ordering : KBO
% 2.49/1.42  
% 2.49/1.42  Simplification rules
% 2.49/1.42  ----------------------
% 2.49/1.42  #Subsume      : 2
% 2.49/1.42  #Demod        : 8
% 2.49/1.42  #Tautology    : 10
% 2.49/1.42  #SimpNegUnit  : 1
% 2.49/1.42  #BackRed      : 1
% 2.49/1.42  
% 2.49/1.42  #Partial instantiations: 0
% 2.49/1.42  #Strategies tried      : 1
% 2.49/1.42  
% 2.49/1.42  Timing (in seconds)
% 2.49/1.42  ----------------------
% 2.49/1.43  Preprocessing        : 0.40
% 2.49/1.43  Parsing              : 0.22
% 2.49/1.43  CNF conversion       : 0.03
% 2.49/1.43  Main loop            : 0.23
% 2.49/1.43  Inferencing          : 0.08
% 2.49/1.43  Reduction            : 0.06
% 2.49/1.43  Demodulation         : 0.05
% 2.49/1.43  BG Simplification    : 0.02
% 2.49/1.43  Subsumption          : 0.04
% 2.49/1.43  Abstraction          : 0.02
% 2.49/1.43  MUC search           : 0.00
% 2.49/1.43  Cooper               : 0.00
% 2.49/1.43  Total                : 0.66
% 2.49/1.43  Index Insertion      : 0.00
% 2.49/1.43  Index Deletion       : 0.00
% 2.49/1.43  Index Matching       : 0.00
% 2.49/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
