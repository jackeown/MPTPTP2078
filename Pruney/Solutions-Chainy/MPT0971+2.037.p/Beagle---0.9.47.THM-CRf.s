%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:34 EST 2020

% Result     : Theorem 2.00s
% Output     : CNFRefutation 2.00s
% Verified   : 
% Statistics : Number of formulae       :   54 (  84 expanded)
%              Number of leaves         :   30 (  44 expanded)
%              Depth                    :    7
%              Number of atoms          :   70 ( 159 expanded)
%              Number of equality atoms :   18 (  35 expanded)
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

tff(f_34,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_81,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ~ ( r2_hidden(C,k2_relset_1(A,B,D))
            & ! [E] :
                ~ ( r2_hidden(E,A)
                  & k1_funct_1(D,E) = C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_funct_2)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_59,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( k7_relset_1(A,B,C,A) = k2_relset_1(A,B,C)
        & k8_relset_1(A,B,C,B) = k1_relset_1(A,B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_relset_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_30,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_37,plain,(
    ! [B_27,A_28] :
      ( v1_relat_1(B_27)
      | ~ m1_subset_1(B_27,k1_zfmisc_1(A_28))
      | ~ v1_relat_1(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_40,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_30,c_37])).

tff(c_43,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_40])).

tff(c_52,plain,(
    ! [A_38,B_39,C_40,D_41] :
      ( k7_relset_1(A_38,B_39,C_40,D_41) = k9_relat_1(C_40,D_41)
      | ~ m1_subset_1(C_40,k1_zfmisc_1(k2_zfmisc_1(A_38,B_39))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_55,plain,(
    ! [D_41] : k7_relset_1('#skF_2','#skF_3','#skF_5',D_41) = k9_relat_1('#skF_5',D_41) ),
    inference(resolution,[status(thm)],[c_30,c_52])).

tff(c_80,plain,(
    ! [A_51,B_52,C_53] :
      ( k7_relset_1(A_51,B_52,C_53,A_51) = k2_relset_1(A_51,B_52,C_53)
      | ~ m1_subset_1(C_53,k1_zfmisc_1(k2_zfmisc_1(A_51,B_52))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_82,plain,(
    k7_relset_1('#skF_2','#skF_3','#skF_5','#skF_2') = k2_relset_1('#skF_2','#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_30,c_80])).

tff(c_84,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_5') = k9_relat_1('#skF_5','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_82])).

tff(c_28,plain,(
    r2_hidden('#skF_4',k2_relset_1('#skF_2','#skF_3','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_85,plain,(
    r2_hidden('#skF_4',k9_relat_1('#skF_5','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_28])).

tff(c_46,plain,(
    ! [A_35,B_36,C_37] :
      ( r2_hidden('#skF_1'(A_35,B_36,C_37),B_36)
      | ~ r2_hidden(A_35,k9_relat_1(C_37,B_36))
      | ~ v1_relat_1(C_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_26,plain,(
    ! [E_23] :
      ( k1_funct_1('#skF_5',E_23) != '#skF_4'
      | ~ r2_hidden(E_23,'#skF_2') ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_51,plain,(
    ! [A_35,C_37] :
      ( k1_funct_1('#skF_5','#skF_1'(A_35,'#skF_2',C_37)) != '#skF_4'
      | ~ r2_hidden(A_35,k9_relat_1(C_37,'#skF_2'))
      | ~ v1_relat_1(C_37) ) ),
    inference(resolution,[status(thm)],[c_46,c_26])).

tff(c_92,plain,
    ( k1_funct_1('#skF_5','#skF_1'('#skF_4','#skF_2','#skF_5')) != '#skF_4'
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_85,c_51])).

tff(c_95,plain,(
    k1_funct_1('#skF_5','#skF_1'('#skF_4','#skF_2','#skF_5')) != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_43,c_92])).

tff(c_34,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_96,plain,(
    ! [A_54,B_55,C_56] :
      ( r2_hidden(k4_tarski('#skF_1'(A_54,B_55,C_56),A_54),C_56)
      | ~ r2_hidden(A_54,k9_relat_1(C_56,B_55))
      | ~ v1_relat_1(C_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_16,plain,(
    ! [C_14,A_12,B_13] :
      ( k1_funct_1(C_14,A_12) = B_13
      | ~ r2_hidden(k4_tarski(A_12,B_13),C_14)
      | ~ v1_funct_1(C_14)
      | ~ v1_relat_1(C_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_135,plain,(
    ! [C_59,A_60,B_61] :
      ( k1_funct_1(C_59,'#skF_1'(A_60,B_61,C_59)) = A_60
      | ~ v1_funct_1(C_59)
      | ~ r2_hidden(A_60,k9_relat_1(C_59,B_61))
      | ~ v1_relat_1(C_59) ) ),
    inference(resolution,[status(thm)],[c_96,c_16])).

tff(c_143,plain,
    ( k1_funct_1('#skF_5','#skF_1'('#skF_4','#skF_2','#skF_5')) = '#skF_4'
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_85,c_135])).

tff(c_151,plain,(
    k1_funct_1('#skF_5','#skF_1'('#skF_4','#skF_2','#skF_5')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_43,c_34,c_143])).

tff(c_153,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_95,c_151])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n008.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 13:43:30 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.00/1.28  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.00/1.28  
% 2.00/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.00/1.28  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4
% 2.00/1.28  
% 2.00/1.28  %Foreground sorts:
% 2.00/1.28  
% 2.00/1.28  
% 2.00/1.28  %Background operators:
% 2.00/1.28  
% 2.00/1.28  
% 2.00/1.28  %Foreground operators:
% 2.00/1.28  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.00/1.28  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.00/1.28  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.00/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.00/1.28  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.00/1.28  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.00/1.28  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 2.00/1.28  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.00/1.28  tff('#skF_5', type, '#skF_5': $i).
% 2.00/1.28  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.00/1.28  tff('#skF_2', type, '#skF_2': $i).
% 2.00/1.28  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.00/1.28  tff('#skF_3', type, '#skF_3': $i).
% 2.00/1.28  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.00/1.28  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.00/1.28  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.00/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.00/1.28  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.00/1.28  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.00/1.28  tff('#skF_4', type, '#skF_4': $i).
% 2.00/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.00/1.28  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.00/1.28  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.00/1.28  
% 2.00/1.29  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.00/1.29  tff(f_81, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ~(r2_hidden(C, k2_relset_1(A, B, D)) & (![E]: ~(r2_hidden(E, A) & (k1_funct_1(D, E) = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_funct_2)).
% 2.00/1.29  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.00/1.29  tff(f_59, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 2.00/1.29  tff(f_65, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((k7_relset_1(A, B, C, A) = k2_relset_1(A, B, C)) & (k8_relset_1(A, B, C, B) = k1_relset_1(A, B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_relset_1)).
% 2.00/1.29  tff(f_45, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_relat_1)).
% 2.00/1.29  tff(f_55, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_1)).
% 2.00/1.29  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.00/1.29  tff(c_30, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.00/1.29  tff(c_37, plain, (![B_27, A_28]: (v1_relat_1(B_27) | ~m1_subset_1(B_27, k1_zfmisc_1(A_28)) | ~v1_relat_1(A_28))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.00/1.29  tff(c_40, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_30, c_37])).
% 2.00/1.29  tff(c_43, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_40])).
% 2.00/1.29  tff(c_52, plain, (![A_38, B_39, C_40, D_41]: (k7_relset_1(A_38, B_39, C_40, D_41)=k9_relat_1(C_40, D_41) | ~m1_subset_1(C_40, k1_zfmisc_1(k2_zfmisc_1(A_38, B_39))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.00/1.29  tff(c_55, plain, (![D_41]: (k7_relset_1('#skF_2', '#skF_3', '#skF_5', D_41)=k9_relat_1('#skF_5', D_41))), inference(resolution, [status(thm)], [c_30, c_52])).
% 2.00/1.29  tff(c_80, plain, (![A_51, B_52, C_53]: (k7_relset_1(A_51, B_52, C_53, A_51)=k2_relset_1(A_51, B_52, C_53) | ~m1_subset_1(C_53, k1_zfmisc_1(k2_zfmisc_1(A_51, B_52))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.00/1.29  tff(c_82, plain, (k7_relset_1('#skF_2', '#skF_3', '#skF_5', '#skF_2')=k2_relset_1('#skF_2', '#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_30, c_80])).
% 2.00/1.29  tff(c_84, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_5')=k9_relat_1('#skF_5', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_55, c_82])).
% 2.00/1.29  tff(c_28, plain, (r2_hidden('#skF_4', k2_relset_1('#skF_2', '#skF_3', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.00/1.29  tff(c_85, plain, (r2_hidden('#skF_4', k9_relat_1('#skF_5', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_28])).
% 2.00/1.29  tff(c_46, plain, (![A_35, B_36, C_37]: (r2_hidden('#skF_1'(A_35, B_36, C_37), B_36) | ~r2_hidden(A_35, k9_relat_1(C_37, B_36)) | ~v1_relat_1(C_37))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.00/1.29  tff(c_26, plain, (![E_23]: (k1_funct_1('#skF_5', E_23)!='#skF_4' | ~r2_hidden(E_23, '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.00/1.29  tff(c_51, plain, (![A_35, C_37]: (k1_funct_1('#skF_5', '#skF_1'(A_35, '#skF_2', C_37))!='#skF_4' | ~r2_hidden(A_35, k9_relat_1(C_37, '#skF_2')) | ~v1_relat_1(C_37))), inference(resolution, [status(thm)], [c_46, c_26])).
% 2.00/1.29  tff(c_92, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_4', '#skF_2', '#skF_5'))!='#skF_4' | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_85, c_51])).
% 2.00/1.29  tff(c_95, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_4', '#skF_2', '#skF_5'))!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_43, c_92])).
% 2.00/1.29  tff(c_34, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.00/1.29  tff(c_96, plain, (![A_54, B_55, C_56]: (r2_hidden(k4_tarski('#skF_1'(A_54, B_55, C_56), A_54), C_56) | ~r2_hidden(A_54, k9_relat_1(C_56, B_55)) | ~v1_relat_1(C_56))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.00/1.29  tff(c_16, plain, (![C_14, A_12, B_13]: (k1_funct_1(C_14, A_12)=B_13 | ~r2_hidden(k4_tarski(A_12, B_13), C_14) | ~v1_funct_1(C_14) | ~v1_relat_1(C_14))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.00/1.29  tff(c_135, plain, (![C_59, A_60, B_61]: (k1_funct_1(C_59, '#skF_1'(A_60, B_61, C_59))=A_60 | ~v1_funct_1(C_59) | ~r2_hidden(A_60, k9_relat_1(C_59, B_61)) | ~v1_relat_1(C_59))), inference(resolution, [status(thm)], [c_96, c_16])).
% 2.00/1.29  tff(c_143, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_4', '#skF_2', '#skF_5'))='#skF_4' | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_85, c_135])).
% 2.00/1.29  tff(c_151, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_4', '#skF_2', '#skF_5'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_43, c_34, c_143])).
% 2.00/1.29  tff(c_153, plain, $false, inference(negUnitSimplification, [status(thm)], [c_95, c_151])).
% 2.00/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.00/1.29  
% 2.00/1.29  Inference rules
% 2.00/1.29  ----------------------
% 2.00/1.29  #Ref     : 0
% 2.00/1.29  #Sup     : 25
% 2.00/1.29  #Fact    : 0
% 2.00/1.29  #Define  : 0
% 2.00/1.29  #Split   : 0
% 2.00/1.29  #Chain   : 0
% 2.00/1.29  #Close   : 0
% 2.00/1.29  
% 2.00/1.29  Ordering : KBO
% 2.00/1.29  
% 2.00/1.29  Simplification rules
% 2.00/1.29  ----------------------
% 2.00/1.29  #Subsume      : 1
% 2.00/1.29  #Demod        : 6
% 2.00/1.29  #Tautology    : 8
% 2.00/1.29  #SimpNegUnit  : 1
% 2.00/1.29  #BackRed      : 1
% 2.00/1.29  
% 2.00/1.29  #Partial instantiations: 0
% 2.00/1.29  #Strategies tried      : 1
% 2.00/1.29  
% 2.00/1.29  Timing (in seconds)
% 2.00/1.29  ----------------------
% 2.00/1.30  Preprocessing        : 0.33
% 2.00/1.30  Parsing              : 0.17
% 2.00/1.30  CNF conversion       : 0.02
% 2.00/1.30  Main loop            : 0.15
% 2.00/1.30  Inferencing          : 0.06
% 2.00/1.30  Reduction            : 0.05
% 2.00/1.30  Demodulation         : 0.04
% 2.00/1.30  BG Simplification    : 0.01
% 2.00/1.30  Subsumption          : 0.02
% 2.00/1.30  Abstraction          : 0.01
% 2.00/1.30  MUC search           : 0.00
% 2.00/1.30  Cooper               : 0.00
% 2.00/1.30  Total                : 0.51
% 2.00/1.30  Index Insertion      : 0.00
% 2.00/1.30  Index Deletion       : 0.00
% 2.00/1.30  Index Matching       : 0.00
% 2.00/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
