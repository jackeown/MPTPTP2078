%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:26 EST 2020

% Result     : Theorem 2.58s
% Output     : CNFRefutation 2.58s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 158 expanded)
%              Number of leaves         :   28 (  69 expanded)
%              Depth                    :   15
%              Number of atoms          :   92 ( 407 expanded)
%              Number of equality atoms :   11 (  58 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   2 average)

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

tff(f_86,negated_conjecture,(
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

tff(f_63,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_67,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_59,axiom,(
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

tff(c_32,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_37,plain,(
    ! [C_30,A_31,B_32] :
      ( v1_relat_1(C_30)
      | ~ m1_subset_1(C_30,k1_zfmisc_1(k2_zfmisc_1(A_31,B_32))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_41,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_32,c_37])).

tff(c_81,plain,(
    ! [A_59,B_60,C_61,D_62] :
      ( k7_relset_1(A_59,B_60,C_61,D_62) = k9_relat_1(C_61,D_62)
      | ~ m1_subset_1(C_61,k1_zfmisc_1(k2_zfmisc_1(A_59,B_60))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_84,plain,(
    ! [D_62] : k7_relset_1('#skF_2','#skF_3','#skF_5',D_62) = k9_relat_1('#skF_5',D_62) ),
    inference(resolution,[status(thm)],[c_32,c_81])).

tff(c_30,plain,(
    r2_hidden('#skF_6',k7_relset_1('#skF_2','#skF_3','#skF_5','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_86,plain,(
    r2_hidden('#skF_6',k9_relat_1('#skF_5','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_30])).

tff(c_12,plain,(
    ! [A_9,B_10,C_11] :
      ( r2_hidden('#skF_1'(A_9,B_10,C_11),B_10)
      | ~ r2_hidden(A_9,k9_relat_1(C_11,B_10))
      | ~ v1_relat_1(C_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_36,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_105,plain,(
    ! [A_70,B_71,C_72] :
      ( r2_hidden(k4_tarski('#skF_1'(A_70,B_71,C_72),A_70),C_72)
      | ~ r2_hidden(A_70,k9_relat_1(C_72,B_71))
      | ~ v1_relat_1(C_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_20,plain,(
    ! [C_17,A_15,B_16] :
      ( k1_funct_1(C_17,A_15) = B_16
      | ~ r2_hidden(k4_tarski(A_15,B_16),C_17)
      | ~ v1_funct_1(C_17)
      | ~ v1_relat_1(C_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_195,plain,(
    ! [C_83,A_84,B_85] :
      ( k1_funct_1(C_83,'#skF_1'(A_84,B_85,C_83)) = A_84
      | ~ v1_funct_1(C_83)
      | ~ r2_hidden(A_84,k9_relat_1(C_83,B_85))
      | ~ v1_relat_1(C_83) ) ),
    inference(resolution,[status(thm)],[c_105,c_20])).

tff(c_203,plain,
    ( k1_funct_1('#skF_5','#skF_1'('#skF_6','#skF_4','#skF_5')) = '#skF_6'
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_86,c_195])).

tff(c_211,plain,(
    k1_funct_1('#skF_5','#skF_1'('#skF_6','#skF_4','#skF_5')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_41,c_36,c_203])).

tff(c_16,plain,(
    ! [A_9,B_10,C_11] :
      ( r2_hidden('#skF_1'(A_9,B_10,C_11),k1_relat_1(C_11))
      | ~ r2_hidden(A_9,k9_relat_1(C_11,B_10))
      | ~ v1_relat_1(C_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_18,plain,(
    ! [A_15,C_17] :
      ( r2_hidden(k4_tarski(A_15,k1_funct_1(C_17,A_15)),C_17)
      | ~ r2_hidden(A_15,k1_relat_1(C_17))
      | ~ v1_funct_1(C_17)
      | ~ v1_relat_1(C_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_216,plain,
    ( r2_hidden(k4_tarski('#skF_1'('#skF_6','#skF_4','#skF_5'),'#skF_6'),'#skF_5')
    | ~ r2_hidden('#skF_1'('#skF_6','#skF_4','#skF_5'),k1_relat_1('#skF_5'))
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_211,c_18])).

tff(c_220,plain,
    ( r2_hidden(k4_tarski('#skF_1'('#skF_6','#skF_4','#skF_5'),'#skF_6'),'#skF_5')
    | ~ r2_hidden('#skF_1'('#skF_6','#skF_4','#skF_5'),k1_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_41,c_36,c_216])).

tff(c_222,plain,(
    ~ r2_hidden('#skF_1'('#skF_6','#skF_4','#skF_5'),k1_relat_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_220])).

tff(c_226,plain,
    ( ~ r2_hidden('#skF_6',k9_relat_1('#skF_5','#skF_4'))
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_16,c_222])).

tff(c_230,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_41,c_86,c_226])).

tff(c_231,plain,(
    r2_hidden(k4_tarski('#skF_1'('#skF_6','#skF_4','#skF_5'),'#skF_6'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_220])).

tff(c_8,plain,(
    ! [C_8,A_5,B_6] :
      ( r2_hidden(C_8,A_5)
      | ~ r2_hidden(C_8,B_6)
      | ~ m1_subset_1(B_6,k1_zfmisc_1(A_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_284,plain,(
    ! [A_91] :
      ( r2_hidden(k4_tarski('#skF_1'('#skF_6','#skF_4','#skF_5'),'#skF_6'),A_91)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_91)) ) ),
    inference(resolution,[status(thm)],[c_231,c_8])).

tff(c_6,plain,(
    ! [A_1,C_3,B_2,D_4] :
      ( r2_hidden(A_1,C_3)
      | ~ r2_hidden(k4_tarski(A_1,B_2),k2_zfmisc_1(C_3,D_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_336,plain,(
    ! [C_95,D_96] :
      ( r2_hidden('#skF_1'('#skF_6','#skF_4','#skF_5'),C_95)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(C_95,D_96))) ) ),
    inference(resolution,[status(thm)],[c_284,c_6])).

tff(c_340,plain,(
    r2_hidden('#skF_1'('#skF_6','#skF_4','#skF_5'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_336])).

tff(c_28,plain,(
    ! [F_29] :
      ( k1_funct_1('#skF_5',F_29) != '#skF_6'
      | ~ r2_hidden(F_29,'#skF_4')
      | ~ r2_hidden(F_29,'#skF_2') ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_345,plain,
    ( k1_funct_1('#skF_5','#skF_1'('#skF_6','#skF_4','#skF_5')) != '#skF_6'
    | ~ r2_hidden('#skF_1'('#skF_6','#skF_4','#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_340,c_28])).

tff(c_351,plain,(
    ~ r2_hidden('#skF_1'('#skF_6','#skF_4','#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_211,c_345])).

tff(c_358,plain,
    ( ~ r2_hidden('#skF_6',k9_relat_1('#skF_5','#skF_4'))
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_12,c_351])).

tff(c_365,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_41,c_86,c_358])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:07:47 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.58/1.33  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.58/1.34  
% 2.58/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.58/1.34  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4
% 2.58/1.34  
% 2.58/1.34  %Foreground sorts:
% 2.58/1.34  
% 2.58/1.34  
% 2.58/1.34  %Background operators:
% 2.58/1.34  
% 2.58/1.34  
% 2.58/1.34  %Foreground operators:
% 2.58/1.34  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.58/1.34  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.58/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.58/1.34  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.58/1.34  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.58/1.34  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.58/1.34  tff('#skF_5', type, '#skF_5': $i).
% 2.58/1.34  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.58/1.34  tff('#skF_6', type, '#skF_6': $i).
% 2.58/1.34  tff('#skF_2', type, '#skF_2': $i).
% 2.58/1.34  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.58/1.34  tff('#skF_3', type, '#skF_3': $i).
% 2.58/1.34  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.58/1.34  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.58/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.58/1.34  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.58/1.34  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.58/1.34  tff('#skF_4', type, '#skF_4': $i).
% 2.58/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.58/1.34  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.58/1.34  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.58/1.34  
% 2.58/1.36  tff(f_86, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: ~(r2_hidden(E, k7_relset_1(A, B, D, C)) & (![F]: ~((r2_hidden(F, A) & r2_hidden(F, C)) & (E = k1_funct_1(D, F)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t115_funct_2)).
% 2.58/1.36  tff(f_63, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.58/1.36  tff(f_67, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 2.58/1.36  tff(f_49, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t143_relat_1)).
% 2.58/1.36  tff(f_59, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_funct_1)).
% 2.58/1.36  tff(f_38, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 2.58/1.36  tff(f_31, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 2.58/1.36  tff(c_32, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.58/1.36  tff(c_37, plain, (![C_30, A_31, B_32]: (v1_relat_1(C_30) | ~m1_subset_1(C_30, k1_zfmisc_1(k2_zfmisc_1(A_31, B_32))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.58/1.36  tff(c_41, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_32, c_37])).
% 2.58/1.36  tff(c_81, plain, (![A_59, B_60, C_61, D_62]: (k7_relset_1(A_59, B_60, C_61, D_62)=k9_relat_1(C_61, D_62) | ~m1_subset_1(C_61, k1_zfmisc_1(k2_zfmisc_1(A_59, B_60))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.58/1.36  tff(c_84, plain, (![D_62]: (k7_relset_1('#skF_2', '#skF_3', '#skF_5', D_62)=k9_relat_1('#skF_5', D_62))), inference(resolution, [status(thm)], [c_32, c_81])).
% 2.58/1.36  tff(c_30, plain, (r2_hidden('#skF_6', k7_relset_1('#skF_2', '#skF_3', '#skF_5', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.58/1.36  tff(c_86, plain, (r2_hidden('#skF_6', k9_relat_1('#skF_5', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_30])).
% 2.58/1.36  tff(c_12, plain, (![A_9, B_10, C_11]: (r2_hidden('#skF_1'(A_9, B_10, C_11), B_10) | ~r2_hidden(A_9, k9_relat_1(C_11, B_10)) | ~v1_relat_1(C_11))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.58/1.36  tff(c_36, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.58/1.36  tff(c_105, plain, (![A_70, B_71, C_72]: (r2_hidden(k4_tarski('#skF_1'(A_70, B_71, C_72), A_70), C_72) | ~r2_hidden(A_70, k9_relat_1(C_72, B_71)) | ~v1_relat_1(C_72))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.58/1.36  tff(c_20, plain, (![C_17, A_15, B_16]: (k1_funct_1(C_17, A_15)=B_16 | ~r2_hidden(k4_tarski(A_15, B_16), C_17) | ~v1_funct_1(C_17) | ~v1_relat_1(C_17))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.58/1.36  tff(c_195, plain, (![C_83, A_84, B_85]: (k1_funct_1(C_83, '#skF_1'(A_84, B_85, C_83))=A_84 | ~v1_funct_1(C_83) | ~r2_hidden(A_84, k9_relat_1(C_83, B_85)) | ~v1_relat_1(C_83))), inference(resolution, [status(thm)], [c_105, c_20])).
% 2.58/1.36  tff(c_203, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_6', '#skF_4', '#skF_5'))='#skF_6' | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_86, c_195])).
% 2.58/1.36  tff(c_211, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_6', '#skF_4', '#skF_5'))='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_41, c_36, c_203])).
% 2.58/1.36  tff(c_16, plain, (![A_9, B_10, C_11]: (r2_hidden('#skF_1'(A_9, B_10, C_11), k1_relat_1(C_11)) | ~r2_hidden(A_9, k9_relat_1(C_11, B_10)) | ~v1_relat_1(C_11))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.58/1.36  tff(c_18, plain, (![A_15, C_17]: (r2_hidden(k4_tarski(A_15, k1_funct_1(C_17, A_15)), C_17) | ~r2_hidden(A_15, k1_relat_1(C_17)) | ~v1_funct_1(C_17) | ~v1_relat_1(C_17))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.58/1.36  tff(c_216, plain, (r2_hidden(k4_tarski('#skF_1'('#skF_6', '#skF_4', '#skF_5'), '#skF_6'), '#skF_5') | ~r2_hidden('#skF_1'('#skF_6', '#skF_4', '#skF_5'), k1_relat_1('#skF_5')) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_211, c_18])).
% 2.58/1.36  tff(c_220, plain, (r2_hidden(k4_tarski('#skF_1'('#skF_6', '#skF_4', '#skF_5'), '#skF_6'), '#skF_5') | ~r2_hidden('#skF_1'('#skF_6', '#skF_4', '#skF_5'), k1_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_41, c_36, c_216])).
% 2.58/1.36  tff(c_222, plain, (~r2_hidden('#skF_1'('#skF_6', '#skF_4', '#skF_5'), k1_relat_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_220])).
% 2.58/1.36  tff(c_226, plain, (~r2_hidden('#skF_6', k9_relat_1('#skF_5', '#skF_4')) | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_16, c_222])).
% 2.58/1.36  tff(c_230, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_41, c_86, c_226])).
% 2.58/1.36  tff(c_231, plain, (r2_hidden(k4_tarski('#skF_1'('#skF_6', '#skF_4', '#skF_5'), '#skF_6'), '#skF_5')), inference(splitRight, [status(thm)], [c_220])).
% 2.58/1.36  tff(c_8, plain, (![C_8, A_5, B_6]: (r2_hidden(C_8, A_5) | ~r2_hidden(C_8, B_6) | ~m1_subset_1(B_6, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.58/1.36  tff(c_284, plain, (![A_91]: (r2_hidden(k4_tarski('#skF_1'('#skF_6', '#skF_4', '#skF_5'), '#skF_6'), A_91) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_91)))), inference(resolution, [status(thm)], [c_231, c_8])).
% 2.58/1.36  tff(c_6, plain, (![A_1, C_3, B_2, D_4]: (r2_hidden(A_1, C_3) | ~r2_hidden(k4_tarski(A_1, B_2), k2_zfmisc_1(C_3, D_4)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.58/1.36  tff(c_336, plain, (![C_95, D_96]: (r2_hidden('#skF_1'('#skF_6', '#skF_4', '#skF_5'), C_95) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(C_95, D_96))))), inference(resolution, [status(thm)], [c_284, c_6])).
% 2.58/1.36  tff(c_340, plain, (r2_hidden('#skF_1'('#skF_6', '#skF_4', '#skF_5'), '#skF_2')), inference(resolution, [status(thm)], [c_32, c_336])).
% 2.58/1.36  tff(c_28, plain, (![F_29]: (k1_funct_1('#skF_5', F_29)!='#skF_6' | ~r2_hidden(F_29, '#skF_4') | ~r2_hidden(F_29, '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.58/1.36  tff(c_345, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_6', '#skF_4', '#skF_5'))!='#skF_6' | ~r2_hidden('#skF_1'('#skF_6', '#skF_4', '#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_340, c_28])).
% 2.58/1.36  tff(c_351, plain, (~r2_hidden('#skF_1'('#skF_6', '#skF_4', '#skF_5'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_211, c_345])).
% 2.58/1.36  tff(c_358, plain, (~r2_hidden('#skF_6', k9_relat_1('#skF_5', '#skF_4')) | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_12, c_351])).
% 2.58/1.36  tff(c_365, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_41, c_86, c_358])).
% 2.58/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.58/1.36  
% 2.58/1.36  Inference rules
% 2.58/1.36  ----------------------
% 2.58/1.36  #Ref     : 0
% 2.58/1.36  #Sup     : 73
% 2.58/1.36  #Fact    : 0
% 2.58/1.36  #Define  : 0
% 2.58/1.36  #Split   : 3
% 2.58/1.36  #Chain   : 0
% 2.58/1.36  #Close   : 0
% 2.58/1.36  
% 2.58/1.36  Ordering : KBO
% 2.58/1.36  
% 2.58/1.36  Simplification rules
% 2.58/1.36  ----------------------
% 2.58/1.36  #Subsume      : 2
% 2.58/1.36  #Demod        : 19
% 2.58/1.36  #Tautology    : 10
% 2.58/1.36  #SimpNegUnit  : 0
% 2.58/1.36  #BackRed      : 2
% 2.58/1.36  
% 2.58/1.36  #Partial instantiations: 0
% 2.58/1.36  #Strategies tried      : 1
% 2.58/1.36  
% 2.58/1.36  Timing (in seconds)
% 2.58/1.36  ----------------------
% 2.58/1.36  Preprocessing        : 0.32
% 2.58/1.36  Parsing              : 0.16
% 2.58/1.36  CNF conversion       : 0.02
% 2.58/1.36  Main loop            : 0.28
% 2.58/1.36  Inferencing          : 0.10
% 2.58/1.36  Reduction            : 0.07
% 2.58/1.36  Demodulation         : 0.06
% 2.58/1.36  BG Simplification    : 0.02
% 2.58/1.36  Subsumption          : 0.05
% 2.58/1.36  Abstraction          : 0.02
% 2.58/1.36  MUC search           : 0.00
% 2.58/1.36  Cooper               : 0.00
% 2.58/1.36  Total                : 0.63
% 2.58/1.36  Index Insertion      : 0.00
% 2.58/1.36  Index Deletion       : 0.00
% 2.58/1.36  Index Matching       : 0.00
% 2.58/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
