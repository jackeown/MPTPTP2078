%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:30 EST 2020

% Result     : Theorem 1.93s
% Output     : CNFRefutation 1.93s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 115 expanded)
%              Number of leaves         :   32 (  55 expanded)
%              Depth                    :   10
%              Number of atoms          :   85 ( 231 expanded)
%              Number of equality atoms :   23 (  47 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

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

tff(f_86,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ~ ( r2_hidden(C,k2_relset_1(A,B,D))
            & ! [E] :
                ~ ( r2_hidden(E,A)
                  & k1_funct_1(D,E) = C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_funct_2)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

tff(c_32,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_82,plain,(
    ! [A_39,B_40,C_41] :
      ( k2_relset_1(A_39,B_40,C_41) = k2_relat_1(C_41)
      | ~ m1_subset_1(C_41,k1_zfmisc_1(k2_zfmisc_1(A_39,B_40))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_86,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_32,c_82])).

tff(c_30,plain,(
    r2_hidden('#skF_4',k2_relset_1('#skF_2','#skF_3','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_87,plain,(
    r2_hidden('#skF_4',k2_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_30])).

tff(c_38,plain,(
    ! [C_26,A_27,B_28] :
      ( v1_relat_1(C_26)
      | ~ m1_subset_1(C_26,k1_zfmisc_1(k2_zfmisc_1(A_27,B_28))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_42,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_32,c_38])).

tff(c_58,plain,(
    ! [C_36,A_37,B_38] :
      ( v4_relat_1(C_36,A_37)
      | ~ m1_subset_1(C_36,k1_zfmisc_1(k2_zfmisc_1(A_37,B_38))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_62,plain,(
    v4_relat_1('#skF_5','#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_58])).

tff(c_12,plain,(
    ! [B_10,A_9] :
      ( k7_relat_1(B_10,A_9) = B_10
      | ~ v4_relat_1(B_10,A_9)
      | ~ v1_relat_1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_65,plain,
    ( k7_relat_1('#skF_5','#skF_2') = '#skF_5'
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_62,c_12])).

tff(c_68,plain,(
    k7_relat_1('#skF_5','#skF_2') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_65])).

tff(c_10,plain,(
    ! [B_8,A_7] :
      ( k2_relat_1(k7_relat_1(B_8,A_7)) = k9_relat_1(B_8,A_7)
      | ~ v1_relat_1(B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_72,plain,
    ( k9_relat_1('#skF_5','#skF_2') = k2_relat_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_10])).

tff(c_76,plain,(
    k9_relat_1('#skF_5','#skF_2') = k2_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_72])).

tff(c_93,plain,(
    ! [A_45,B_46,C_47] :
      ( r2_hidden('#skF_1'(A_45,B_46,C_47),B_46)
      | ~ r2_hidden(A_45,k9_relat_1(C_47,B_46))
      | ~ v1_relat_1(C_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_28,plain,(
    ! [E_24] :
      ( k1_funct_1('#skF_5',E_24) != '#skF_4'
      | ~ r2_hidden(E_24,'#skF_2') ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_101,plain,(
    ! [A_54,C_55] :
      ( k1_funct_1('#skF_5','#skF_1'(A_54,'#skF_2',C_55)) != '#skF_4'
      | ~ r2_hidden(A_54,k9_relat_1(C_55,'#skF_2'))
      | ~ v1_relat_1(C_55) ) ),
    inference(resolution,[status(thm)],[c_93,c_28])).

tff(c_108,plain,(
    ! [A_54] :
      ( k1_funct_1('#skF_5','#skF_1'(A_54,'#skF_2','#skF_5')) != '#skF_4'
      | ~ r2_hidden(A_54,k2_relat_1('#skF_5'))
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_101])).

tff(c_112,plain,(
    ! [A_56] :
      ( k1_funct_1('#skF_5','#skF_1'(A_56,'#skF_2','#skF_5')) != '#skF_4'
      | ~ r2_hidden(A_56,k2_relat_1('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_108])).

tff(c_121,plain,(
    k1_funct_1('#skF_5','#skF_1'('#skF_4','#skF_2','#skF_5')) != '#skF_4' ),
    inference(resolution,[status(thm)],[c_87,c_112])).

tff(c_36,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_122,plain,(
    ! [A_57,B_58,C_59] :
      ( r2_hidden(k4_tarski('#skF_1'(A_57,B_58,C_59),A_57),C_59)
      | ~ r2_hidden(A_57,k9_relat_1(C_59,B_58))
      | ~ v1_relat_1(C_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_16,plain,(
    ! [C_13,A_11,B_12] :
      ( k1_funct_1(C_13,A_11) = B_12
      | ~ r2_hidden(k4_tarski(A_11,B_12),C_13)
      | ~ v1_funct_1(C_13)
      | ~ v1_relat_1(C_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_172,plain,(
    ! [C_62,A_63,B_64] :
      ( k1_funct_1(C_62,'#skF_1'(A_63,B_64,C_62)) = A_63
      | ~ v1_funct_1(C_62)
      | ~ r2_hidden(A_63,k9_relat_1(C_62,B_64))
      | ~ v1_relat_1(C_62) ) ),
    inference(resolution,[status(thm)],[c_122,c_16])).

tff(c_183,plain,(
    ! [A_63] :
      ( k1_funct_1('#skF_5','#skF_1'(A_63,'#skF_2','#skF_5')) = A_63
      | ~ v1_funct_1('#skF_5')
      | ~ r2_hidden(A_63,k2_relat_1('#skF_5'))
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_172])).

tff(c_189,plain,(
    ! [A_65] :
      ( k1_funct_1('#skF_5','#skF_1'(A_65,'#skF_2','#skF_5')) = A_65
      | ~ r2_hidden(A_65,k2_relat_1('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_36,c_183])).

tff(c_204,plain,(
    k1_funct_1('#skF_5','#skF_1'('#skF_4','#skF_2','#skF_5')) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_87,c_189])).

tff(c_211,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_121,c_204])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:10:01 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.93/1.20  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.93/1.21  
% 1.93/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.93/1.21  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k9_relat_1 > k7_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4
% 1.93/1.21  
% 1.93/1.21  %Foreground sorts:
% 1.93/1.21  
% 1.93/1.21  
% 1.93/1.21  %Background operators:
% 1.93/1.21  
% 1.93/1.21  
% 1.93/1.21  %Foreground operators:
% 1.93/1.21  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 1.93/1.21  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.93/1.21  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.93/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.93/1.21  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.93/1.21  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.93/1.21  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.93/1.21  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.93/1.21  tff('#skF_5', type, '#skF_5': $i).
% 1.93/1.21  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 1.93/1.21  tff('#skF_2', type, '#skF_2': $i).
% 1.93/1.21  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.93/1.21  tff('#skF_3', type, '#skF_3': $i).
% 1.93/1.21  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 1.93/1.21  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.93/1.21  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 1.93/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.93/1.21  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.93/1.21  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.93/1.21  tff('#skF_4', type, '#skF_4': $i).
% 1.93/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.93/1.21  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 1.93/1.21  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.93/1.21  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.93/1.21  
% 1.93/1.22  tff(f_86, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ~(r2_hidden(C, k2_relset_1(A, B, D)) & (![E]: ~(r2_hidden(E, A) & (k1_funct_1(D, E) = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_funct_2)).
% 1.93/1.22  tff(f_70, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 1.93/1.22  tff(f_60, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 1.93/1.22  tff(f_66, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 1.93/1.22  tff(f_46, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 1.93/1.22  tff(f_40, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 1.93/1.22  tff(f_36, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t143_relat_1)).
% 1.93/1.22  tff(f_56, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_funct_1)).
% 1.93/1.22  tff(c_32, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_86])).
% 1.93/1.22  tff(c_82, plain, (![A_39, B_40, C_41]: (k2_relset_1(A_39, B_40, C_41)=k2_relat_1(C_41) | ~m1_subset_1(C_41, k1_zfmisc_1(k2_zfmisc_1(A_39, B_40))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 1.93/1.22  tff(c_86, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_32, c_82])).
% 1.93/1.22  tff(c_30, plain, (r2_hidden('#skF_4', k2_relset_1('#skF_2', '#skF_3', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_86])).
% 1.93/1.22  tff(c_87, plain, (r2_hidden('#skF_4', k2_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_30])).
% 1.93/1.22  tff(c_38, plain, (![C_26, A_27, B_28]: (v1_relat_1(C_26) | ~m1_subset_1(C_26, k1_zfmisc_1(k2_zfmisc_1(A_27, B_28))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.93/1.22  tff(c_42, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_32, c_38])).
% 1.93/1.22  tff(c_58, plain, (![C_36, A_37, B_38]: (v4_relat_1(C_36, A_37) | ~m1_subset_1(C_36, k1_zfmisc_1(k2_zfmisc_1(A_37, B_38))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.93/1.22  tff(c_62, plain, (v4_relat_1('#skF_5', '#skF_2')), inference(resolution, [status(thm)], [c_32, c_58])).
% 1.93/1.22  tff(c_12, plain, (![B_10, A_9]: (k7_relat_1(B_10, A_9)=B_10 | ~v4_relat_1(B_10, A_9) | ~v1_relat_1(B_10))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.93/1.22  tff(c_65, plain, (k7_relat_1('#skF_5', '#skF_2')='#skF_5' | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_62, c_12])).
% 1.93/1.22  tff(c_68, plain, (k7_relat_1('#skF_5', '#skF_2')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_65])).
% 1.93/1.22  tff(c_10, plain, (![B_8, A_7]: (k2_relat_1(k7_relat_1(B_8, A_7))=k9_relat_1(B_8, A_7) | ~v1_relat_1(B_8))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.93/1.22  tff(c_72, plain, (k9_relat_1('#skF_5', '#skF_2')=k2_relat_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_68, c_10])).
% 1.93/1.22  tff(c_76, plain, (k9_relat_1('#skF_5', '#skF_2')=k2_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_72])).
% 1.93/1.22  tff(c_93, plain, (![A_45, B_46, C_47]: (r2_hidden('#skF_1'(A_45, B_46, C_47), B_46) | ~r2_hidden(A_45, k9_relat_1(C_47, B_46)) | ~v1_relat_1(C_47))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.93/1.22  tff(c_28, plain, (![E_24]: (k1_funct_1('#skF_5', E_24)!='#skF_4' | ~r2_hidden(E_24, '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_86])).
% 1.93/1.22  tff(c_101, plain, (![A_54, C_55]: (k1_funct_1('#skF_5', '#skF_1'(A_54, '#skF_2', C_55))!='#skF_4' | ~r2_hidden(A_54, k9_relat_1(C_55, '#skF_2')) | ~v1_relat_1(C_55))), inference(resolution, [status(thm)], [c_93, c_28])).
% 1.93/1.22  tff(c_108, plain, (![A_54]: (k1_funct_1('#skF_5', '#skF_1'(A_54, '#skF_2', '#skF_5'))!='#skF_4' | ~r2_hidden(A_54, k2_relat_1('#skF_5')) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_76, c_101])).
% 1.93/1.22  tff(c_112, plain, (![A_56]: (k1_funct_1('#skF_5', '#skF_1'(A_56, '#skF_2', '#skF_5'))!='#skF_4' | ~r2_hidden(A_56, k2_relat_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_108])).
% 1.93/1.22  tff(c_121, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_4', '#skF_2', '#skF_5'))!='#skF_4'), inference(resolution, [status(thm)], [c_87, c_112])).
% 1.93/1.22  tff(c_36, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_86])).
% 1.93/1.22  tff(c_122, plain, (![A_57, B_58, C_59]: (r2_hidden(k4_tarski('#skF_1'(A_57, B_58, C_59), A_57), C_59) | ~r2_hidden(A_57, k9_relat_1(C_59, B_58)) | ~v1_relat_1(C_59))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.93/1.22  tff(c_16, plain, (![C_13, A_11, B_12]: (k1_funct_1(C_13, A_11)=B_12 | ~r2_hidden(k4_tarski(A_11, B_12), C_13) | ~v1_funct_1(C_13) | ~v1_relat_1(C_13))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.93/1.22  tff(c_172, plain, (![C_62, A_63, B_64]: (k1_funct_1(C_62, '#skF_1'(A_63, B_64, C_62))=A_63 | ~v1_funct_1(C_62) | ~r2_hidden(A_63, k9_relat_1(C_62, B_64)) | ~v1_relat_1(C_62))), inference(resolution, [status(thm)], [c_122, c_16])).
% 1.93/1.22  tff(c_183, plain, (![A_63]: (k1_funct_1('#skF_5', '#skF_1'(A_63, '#skF_2', '#skF_5'))=A_63 | ~v1_funct_1('#skF_5') | ~r2_hidden(A_63, k2_relat_1('#skF_5')) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_76, c_172])).
% 1.93/1.22  tff(c_189, plain, (![A_65]: (k1_funct_1('#skF_5', '#skF_1'(A_65, '#skF_2', '#skF_5'))=A_65 | ~r2_hidden(A_65, k2_relat_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_36, c_183])).
% 1.93/1.22  tff(c_204, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_4', '#skF_2', '#skF_5'))='#skF_4'), inference(resolution, [status(thm)], [c_87, c_189])).
% 1.93/1.22  tff(c_211, plain, $false, inference(negUnitSimplification, [status(thm)], [c_121, c_204])).
% 1.93/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.93/1.22  
% 1.93/1.22  Inference rules
% 1.93/1.22  ----------------------
% 1.93/1.22  #Ref     : 0
% 1.93/1.22  #Sup     : 37
% 1.93/1.22  #Fact    : 0
% 1.93/1.22  #Define  : 0
% 1.93/1.22  #Split   : 1
% 1.93/1.22  #Chain   : 0
% 1.93/1.22  #Close   : 0
% 1.93/1.22  
% 1.93/1.22  Ordering : KBO
% 1.93/1.22  
% 1.93/1.22  Simplification rules
% 1.93/1.22  ----------------------
% 1.93/1.22  #Subsume      : 2
% 1.93/1.22  #Demod        : 6
% 1.93/1.22  #Tautology    : 10
% 1.93/1.22  #SimpNegUnit  : 1
% 1.93/1.22  #BackRed      : 1
% 1.93/1.22  
% 1.93/1.22  #Partial instantiations: 0
% 1.93/1.22  #Strategies tried      : 1
% 1.93/1.22  
% 1.93/1.22  Timing (in seconds)
% 1.93/1.22  ----------------------
% 1.93/1.23  Preprocessing        : 0.29
% 1.93/1.23  Parsing              : 0.15
% 1.93/1.23  CNF conversion       : 0.02
% 1.93/1.23  Main loop            : 0.18
% 1.93/1.23  Inferencing          : 0.07
% 1.93/1.23  Reduction            : 0.05
% 1.93/1.23  Demodulation         : 0.04
% 1.93/1.23  BG Simplification    : 0.01
% 1.93/1.23  Subsumption          : 0.03
% 1.93/1.23  Abstraction          : 0.01
% 1.93/1.23  MUC search           : 0.00
% 1.93/1.23  Cooper               : 0.00
% 1.93/1.23  Total                : 0.50
% 1.93/1.23  Index Insertion      : 0.00
% 1.93/1.23  Index Deletion       : 0.00
% 1.93/1.23  Index Matching       : 0.00
% 1.93/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
