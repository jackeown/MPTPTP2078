%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:30 EST 2020

% Result     : Theorem 2.42s
% Output     : CNFRefutation 2.42s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 179 expanded)
%              Number of leaves         :   29 (  76 expanded)
%              Depth                    :   15
%              Number of atoms          :   98 ( 449 expanded)
%              Number of equality atoms :   11 (  58 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_47,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_91,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [E] :
            ~ ( r2_hidden(E,k7_relset_1(A,B,D,C))
              & ! [F] :
                  ~ ( r2_hidden(F,A)
                    & r2_hidden(F,C)
                    & E = k1_funct_1(D,F) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t115_funct_2)).

tff(f_45,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_72,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_31,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(c_12,plain,(
    ! [A_12,B_13] : v1_relat_1(k2_zfmisc_1(A_12,B_13)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_34,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_40,plain,(
    ! [B_34,A_35] :
      ( v1_relat_1(B_34)
      | ~ m1_subset_1(B_34,k1_zfmisc_1(A_35))
      | ~ v1_relat_1(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_43,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_34,c_40])).

tff(c_46,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_43])).

tff(c_90,plain,(
    ! [A_62,B_63,C_64,D_65] :
      ( k7_relset_1(A_62,B_63,C_64,D_65) = k9_relat_1(C_64,D_65)
      | ~ m1_subset_1(C_64,k1_zfmisc_1(k2_zfmisc_1(A_62,B_63))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_93,plain,(
    ! [D_65] : k7_relset_1('#skF_2','#skF_3','#skF_5',D_65) = k9_relat_1('#skF_5',D_65) ),
    inference(resolution,[status(thm)],[c_34,c_90])).

tff(c_32,plain,(
    r2_hidden('#skF_6',k7_relset_1('#skF_2','#skF_3','#skF_5','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_95,plain,(
    r2_hidden('#skF_6',k9_relat_1('#skF_5','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_32])).

tff(c_16,plain,(
    ! [A_14,B_15,C_16] :
      ( r2_hidden('#skF_1'(A_14,B_15,C_16),B_15)
      | ~ r2_hidden(A_14,k9_relat_1(C_16,B_15))
      | ~ v1_relat_1(C_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_38,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_114,plain,(
    ! [A_73,B_74,C_75] :
      ( r2_hidden(k4_tarski('#skF_1'(A_73,B_74,C_75),A_73),C_75)
      | ~ r2_hidden(A_73,k9_relat_1(C_75,B_74))
      | ~ v1_relat_1(C_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_24,plain,(
    ! [C_22,A_20,B_21] :
      ( k1_funct_1(C_22,A_20) = B_21
      | ~ r2_hidden(k4_tarski(A_20,B_21),C_22)
      | ~ v1_funct_1(C_22)
      | ~ v1_relat_1(C_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_242,plain,(
    ! [C_89,A_90,B_91] :
      ( k1_funct_1(C_89,'#skF_1'(A_90,B_91,C_89)) = A_90
      | ~ v1_funct_1(C_89)
      | ~ r2_hidden(A_90,k9_relat_1(C_89,B_91))
      | ~ v1_relat_1(C_89) ) ),
    inference(resolution,[status(thm)],[c_114,c_24])).

tff(c_253,plain,
    ( k1_funct_1('#skF_5','#skF_1'('#skF_6','#skF_4','#skF_5')) = '#skF_6'
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_95,c_242])).

tff(c_262,plain,(
    k1_funct_1('#skF_5','#skF_1'('#skF_6','#skF_4','#skF_5')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_38,c_253])).

tff(c_20,plain,(
    ! [A_14,B_15,C_16] :
      ( r2_hidden('#skF_1'(A_14,B_15,C_16),k1_relat_1(C_16))
      | ~ r2_hidden(A_14,k9_relat_1(C_16,B_15))
      | ~ v1_relat_1(C_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_22,plain,(
    ! [A_20,C_22] :
      ( r2_hidden(k4_tarski(A_20,k1_funct_1(C_22,A_20)),C_22)
      | ~ r2_hidden(A_20,k1_relat_1(C_22))
      | ~ v1_funct_1(C_22)
      | ~ v1_relat_1(C_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_268,plain,
    ( r2_hidden(k4_tarski('#skF_1'('#skF_6','#skF_4','#skF_5'),'#skF_6'),'#skF_5')
    | ~ r2_hidden('#skF_1'('#skF_6','#skF_4','#skF_5'),k1_relat_1('#skF_5'))
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_262,c_22])).

tff(c_272,plain,
    ( r2_hidden(k4_tarski('#skF_1'('#skF_6','#skF_4','#skF_5'),'#skF_6'),'#skF_5')
    | ~ r2_hidden('#skF_1'('#skF_6','#skF_4','#skF_5'),k1_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_38,c_268])).

tff(c_274,plain,(
    ~ r2_hidden('#skF_1'('#skF_6','#skF_4','#skF_5'),k1_relat_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_272])).

tff(c_277,plain,
    ( ~ r2_hidden('#skF_6',k9_relat_1('#skF_5','#skF_4'))
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_20,c_274])).

tff(c_281,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_95,c_277])).

tff(c_282,plain,(
    r2_hidden(k4_tarski('#skF_1'('#skF_6','#skF_4','#skF_5'),'#skF_6'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_272])).

tff(c_8,plain,(
    ! [C_8,A_5,B_6] :
      ( r2_hidden(C_8,A_5)
      | ~ r2_hidden(C_8,B_6)
      | ~ m1_subset_1(B_6,k1_zfmisc_1(A_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_331,plain,(
    ! [A_97] :
      ( r2_hidden(k4_tarski('#skF_1'('#skF_6','#skF_4','#skF_5'),'#skF_6'),A_97)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_97)) ) ),
    inference(resolution,[status(thm)],[c_282,c_8])).

tff(c_6,plain,(
    ! [A_1,C_3,B_2,D_4] :
      ( r2_hidden(A_1,C_3)
      | ~ r2_hidden(k4_tarski(A_1,B_2),k2_zfmisc_1(C_3,D_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_388,plain,(
    ! [C_101,D_102] :
      ( r2_hidden('#skF_1'('#skF_6','#skF_4','#skF_5'),C_101)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(C_101,D_102))) ) ),
    inference(resolution,[status(thm)],[c_331,c_6])).

tff(c_392,plain,(
    r2_hidden('#skF_1'('#skF_6','#skF_4','#skF_5'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_388])).

tff(c_30,plain,(
    ! [F_31] :
      ( k1_funct_1('#skF_5',F_31) != '#skF_6'
      | ~ r2_hidden(F_31,'#skF_4')
      | ~ r2_hidden(F_31,'#skF_2') ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_435,plain,
    ( k1_funct_1('#skF_5','#skF_1'('#skF_6','#skF_4','#skF_5')) != '#skF_6'
    | ~ r2_hidden('#skF_1'('#skF_6','#skF_4','#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_392,c_30])).

tff(c_441,plain,(
    ~ r2_hidden('#skF_1'('#skF_6','#skF_4','#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_262,c_435])).

tff(c_444,plain,
    ( ~ r2_hidden('#skF_6',k9_relat_1('#skF_5','#skF_4'))
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_16,c_441])).

tff(c_448,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_95,c_444])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 19:12:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.42/1.41  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.42/1.41  
% 2.42/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.42/1.42  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4
% 2.42/1.42  
% 2.42/1.42  %Foreground sorts:
% 2.42/1.42  
% 2.42/1.42  
% 2.42/1.42  %Background operators:
% 2.42/1.42  
% 2.42/1.42  
% 2.42/1.42  %Foreground operators:
% 2.42/1.42  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.42/1.42  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.42/1.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.42/1.42  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.42/1.42  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.42/1.42  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.42/1.42  tff('#skF_5', type, '#skF_5': $i).
% 2.42/1.42  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.42/1.42  tff('#skF_6', type, '#skF_6': $i).
% 2.42/1.42  tff('#skF_2', type, '#skF_2': $i).
% 2.42/1.42  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.42/1.42  tff('#skF_3', type, '#skF_3': $i).
% 2.42/1.42  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.42/1.42  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.42/1.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.42/1.42  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.42/1.42  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.42/1.42  tff('#skF_4', type, '#skF_4': $i).
% 2.42/1.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.42/1.42  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.42/1.42  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.42/1.42  
% 2.42/1.43  tff(f_47, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.42/1.43  tff(f_91, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: ~(r2_hidden(E, k7_relset_1(A, B, D, C)) & (![F]: ~((r2_hidden(F, A) & r2_hidden(F, C)) & (E = k1_funct_1(D, F)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t115_funct_2)).
% 2.42/1.43  tff(f_45, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.42/1.43  tff(f_72, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 2.42/1.43  tff(f_58, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t143_relat_1)).
% 2.42/1.43  tff(f_68, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_funct_1)).
% 2.42/1.43  tff(f_38, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 2.42/1.43  tff(f_31, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 2.42/1.43  tff(c_12, plain, (![A_12, B_13]: (v1_relat_1(k2_zfmisc_1(A_12, B_13)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.42/1.43  tff(c_34, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.42/1.43  tff(c_40, plain, (![B_34, A_35]: (v1_relat_1(B_34) | ~m1_subset_1(B_34, k1_zfmisc_1(A_35)) | ~v1_relat_1(A_35))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.42/1.43  tff(c_43, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_34, c_40])).
% 2.42/1.43  tff(c_46, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_43])).
% 2.42/1.43  tff(c_90, plain, (![A_62, B_63, C_64, D_65]: (k7_relset_1(A_62, B_63, C_64, D_65)=k9_relat_1(C_64, D_65) | ~m1_subset_1(C_64, k1_zfmisc_1(k2_zfmisc_1(A_62, B_63))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.42/1.43  tff(c_93, plain, (![D_65]: (k7_relset_1('#skF_2', '#skF_3', '#skF_5', D_65)=k9_relat_1('#skF_5', D_65))), inference(resolution, [status(thm)], [c_34, c_90])).
% 2.42/1.43  tff(c_32, plain, (r2_hidden('#skF_6', k7_relset_1('#skF_2', '#skF_3', '#skF_5', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.42/1.43  tff(c_95, plain, (r2_hidden('#skF_6', k9_relat_1('#skF_5', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_93, c_32])).
% 2.42/1.43  tff(c_16, plain, (![A_14, B_15, C_16]: (r2_hidden('#skF_1'(A_14, B_15, C_16), B_15) | ~r2_hidden(A_14, k9_relat_1(C_16, B_15)) | ~v1_relat_1(C_16))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.42/1.43  tff(c_38, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.42/1.43  tff(c_114, plain, (![A_73, B_74, C_75]: (r2_hidden(k4_tarski('#skF_1'(A_73, B_74, C_75), A_73), C_75) | ~r2_hidden(A_73, k9_relat_1(C_75, B_74)) | ~v1_relat_1(C_75))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.42/1.43  tff(c_24, plain, (![C_22, A_20, B_21]: (k1_funct_1(C_22, A_20)=B_21 | ~r2_hidden(k4_tarski(A_20, B_21), C_22) | ~v1_funct_1(C_22) | ~v1_relat_1(C_22))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.42/1.43  tff(c_242, plain, (![C_89, A_90, B_91]: (k1_funct_1(C_89, '#skF_1'(A_90, B_91, C_89))=A_90 | ~v1_funct_1(C_89) | ~r2_hidden(A_90, k9_relat_1(C_89, B_91)) | ~v1_relat_1(C_89))), inference(resolution, [status(thm)], [c_114, c_24])).
% 2.42/1.43  tff(c_253, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_6', '#skF_4', '#skF_5'))='#skF_6' | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_95, c_242])).
% 2.42/1.43  tff(c_262, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_6', '#skF_4', '#skF_5'))='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_46, c_38, c_253])).
% 2.42/1.43  tff(c_20, plain, (![A_14, B_15, C_16]: (r2_hidden('#skF_1'(A_14, B_15, C_16), k1_relat_1(C_16)) | ~r2_hidden(A_14, k9_relat_1(C_16, B_15)) | ~v1_relat_1(C_16))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.42/1.43  tff(c_22, plain, (![A_20, C_22]: (r2_hidden(k4_tarski(A_20, k1_funct_1(C_22, A_20)), C_22) | ~r2_hidden(A_20, k1_relat_1(C_22)) | ~v1_funct_1(C_22) | ~v1_relat_1(C_22))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.42/1.43  tff(c_268, plain, (r2_hidden(k4_tarski('#skF_1'('#skF_6', '#skF_4', '#skF_5'), '#skF_6'), '#skF_5') | ~r2_hidden('#skF_1'('#skF_6', '#skF_4', '#skF_5'), k1_relat_1('#skF_5')) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_262, c_22])).
% 2.42/1.43  tff(c_272, plain, (r2_hidden(k4_tarski('#skF_1'('#skF_6', '#skF_4', '#skF_5'), '#skF_6'), '#skF_5') | ~r2_hidden('#skF_1'('#skF_6', '#skF_4', '#skF_5'), k1_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_38, c_268])).
% 2.42/1.43  tff(c_274, plain, (~r2_hidden('#skF_1'('#skF_6', '#skF_4', '#skF_5'), k1_relat_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_272])).
% 2.42/1.43  tff(c_277, plain, (~r2_hidden('#skF_6', k9_relat_1('#skF_5', '#skF_4')) | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_20, c_274])).
% 2.42/1.43  tff(c_281, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_95, c_277])).
% 2.42/1.43  tff(c_282, plain, (r2_hidden(k4_tarski('#skF_1'('#skF_6', '#skF_4', '#skF_5'), '#skF_6'), '#skF_5')), inference(splitRight, [status(thm)], [c_272])).
% 2.42/1.43  tff(c_8, plain, (![C_8, A_5, B_6]: (r2_hidden(C_8, A_5) | ~r2_hidden(C_8, B_6) | ~m1_subset_1(B_6, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.42/1.43  tff(c_331, plain, (![A_97]: (r2_hidden(k4_tarski('#skF_1'('#skF_6', '#skF_4', '#skF_5'), '#skF_6'), A_97) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_97)))), inference(resolution, [status(thm)], [c_282, c_8])).
% 2.42/1.43  tff(c_6, plain, (![A_1, C_3, B_2, D_4]: (r2_hidden(A_1, C_3) | ~r2_hidden(k4_tarski(A_1, B_2), k2_zfmisc_1(C_3, D_4)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.42/1.43  tff(c_388, plain, (![C_101, D_102]: (r2_hidden('#skF_1'('#skF_6', '#skF_4', '#skF_5'), C_101) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(C_101, D_102))))), inference(resolution, [status(thm)], [c_331, c_6])).
% 2.42/1.43  tff(c_392, plain, (r2_hidden('#skF_1'('#skF_6', '#skF_4', '#skF_5'), '#skF_2')), inference(resolution, [status(thm)], [c_34, c_388])).
% 2.42/1.43  tff(c_30, plain, (![F_31]: (k1_funct_1('#skF_5', F_31)!='#skF_6' | ~r2_hidden(F_31, '#skF_4') | ~r2_hidden(F_31, '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.42/1.43  tff(c_435, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_6', '#skF_4', '#skF_5'))!='#skF_6' | ~r2_hidden('#skF_1'('#skF_6', '#skF_4', '#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_392, c_30])).
% 2.42/1.43  tff(c_441, plain, (~r2_hidden('#skF_1'('#skF_6', '#skF_4', '#skF_5'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_262, c_435])).
% 2.42/1.43  tff(c_444, plain, (~r2_hidden('#skF_6', k9_relat_1('#skF_5', '#skF_4')) | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_16, c_441])).
% 2.42/1.43  tff(c_448, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_95, c_444])).
% 2.42/1.43  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.42/1.43  
% 2.42/1.43  Inference rules
% 2.42/1.43  ----------------------
% 2.42/1.43  #Ref     : 0
% 2.42/1.43  #Sup     : 90
% 2.42/1.43  #Fact    : 0
% 2.42/1.43  #Define  : 0
% 2.42/1.43  #Split   : 3
% 2.42/1.43  #Chain   : 0
% 2.42/1.43  #Close   : 0
% 2.42/1.43  
% 2.42/1.43  Ordering : KBO
% 2.42/1.43  
% 2.42/1.43  Simplification rules
% 2.42/1.43  ----------------------
% 2.42/1.43  #Subsume      : 2
% 2.42/1.43  #Demod        : 26
% 2.42/1.43  #Tautology    : 10
% 2.42/1.43  #SimpNegUnit  : 0
% 2.42/1.43  #BackRed      : 2
% 2.42/1.43  
% 2.42/1.43  #Partial instantiations: 0
% 2.42/1.43  #Strategies tried      : 1
% 2.42/1.43  
% 2.42/1.43  Timing (in seconds)
% 2.42/1.43  ----------------------
% 2.42/1.43  Preprocessing        : 0.32
% 2.42/1.43  Parsing              : 0.17
% 2.42/1.43  CNF conversion       : 0.02
% 2.42/1.43  Main loop            : 0.27
% 2.42/1.43  Inferencing          : 0.10
% 2.42/1.43  Reduction            : 0.07
% 2.42/1.43  Demodulation         : 0.06
% 2.42/1.43  BG Simplification    : 0.02
% 2.42/1.43  Subsumption          : 0.06
% 2.42/1.43  Abstraction          : 0.02
% 2.42/1.43  MUC search           : 0.00
% 2.42/1.43  Cooper               : 0.00
% 2.42/1.43  Total                : 0.61
% 2.42/1.43  Index Insertion      : 0.00
% 2.42/1.43  Index Deletion       : 0.00
% 2.42/1.43  Index Matching       : 0.00
% 2.42/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
