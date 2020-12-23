%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:33 EST 2020

% Result     : Theorem 2.28s
% Output     : CNFRefutation 2.51s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 133 expanded)
%              Number of leaves         :   33 (  61 expanded)
%              Depth                    :   10
%              Number of atoms          :   91 ( 267 expanded)
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

tff(f_91,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ~ ( r2_hidden(C,k2_relset_1(A,B,D))
            & ! [E] :
                ~ ( r2_hidden(E,A)
                  & k1_funct_1(D,E) = C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_funct_2)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_34,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

tff(c_34,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_83,plain,(
    ! [A_42,B_43,C_44] :
      ( k2_relset_1(A_42,B_43,C_44) = k2_relat_1(C_44)
      | ~ m1_subset_1(C_44,k1_zfmisc_1(k2_zfmisc_1(A_42,B_43))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_87,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_34,c_83])).

tff(c_32,plain,(
    r2_hidden('#skF_4',k2_relset_1('#skF_2','#skF_3','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_92,plain,(
    r2_hidden('#skF_4',k2_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_32])).

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_41,plain,(
    ! [B_30,A_31] :
      ( v1_relat_1(B_30)
      | ~ m1_subset_1(B_30,k1_zfmisc_1(A_31))
      | ~ v1_relat_1(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_44,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_34,c_41])).

tff(c_47,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_44])).

tff(c_63,plain,(
    ! [C_39,A_40,B_41] :
      ( v4_relat_1(C_39,A_40)
      | ~ m1_subset_1(C_39,k1_zfmisc_1(k2_zfmisc_1(A_40,B_41))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_67,plain,(
    v4_relat_1('#skF_5','#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_63])).

tff(c_16,plain,(
    ! [B_15,A_14] :
      ( k7_relat_1(B_15,A_14) = B_15
      | ~ v4_relat_1(B_15,A_14)
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_70,plain,
    ( k7_relat_1('#skF_5','#skF_2') = '#skF_5'
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_67,c_16])).

tff(c_73,plain,(
    k7_relat_1('#skF_5','#skF_2') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_47,c_70])).

tff(c_14,plain,(
    ! [B_13,A_12] :
      ( k2_relat_1(k7_relat_1(B_13,A_12)) = k9_relat_1(B_13,A_12)
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_77,plain,
    ( k9_relat_1('#skF_5','#skF_2') = k2_relat_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_73,c_14])).

tff(c_81,plain,(
    k9_relat_1('#skF_5','#skF_2') = k2_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_47,c_77])).

tff(c_99,plain,(
    ! [A_51,B_52,C_53] :
      ( r2_hidden('#skF_1'(A_51,B_52,C_53),B_52)
      | ~ r2_hidden(A_51,k9_relat_1(C_53,B_52))
      | ~ v1_relat_1(C_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_30,plain,(
    ! [E_26] :
      ( k1_funct_1('#skF_5',E_26) != '#skF_4'
      | ~ r2_hidden(E_26,'#skF_2') ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_106,plain,(
    ! [A_57,C_58] :
      ( k1_funct_1('#skF_5','#skF_1'(A_57,'#skF_2',C_58)) != '#skF_4'
      | ~ r2_hidden(A_57,k9_relat_1(C_58,'#skF_2'))
      | ~ v1_relat_1(C_58) ) ),
    inference(resolution,[status(thm)],[c_99,c_30])).

tff(c_113,plain,(
    ! [A_57] :
      ( k1_funct_1('#skF_5','#skF_1'(A_57,'#skF_2','#skF_5')) != '#skF_4'
      | ~ r2_hidden(A_57,k2_relat_1('#skF_5'))
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_81,c_106])).

tff(c_117,plain,(
    ! [A_59] :
      ( k1_funct_1('#skF_5','#skF_1'(A_59,'#skF_2','#skF_5')) != '#skF_4'
      | ~ r2_hidden(A_59,k2_relat_1('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_47,c_113])).

tff(c_126,plain,(
    k1_funct_1('#skF_5','#skF_1'('#skF_4','#skF_2','#skF_5')) != '#skF_4' ),
    inference(resolution,[status(thm)],[c_92,c_117])).

tff(c_38,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_152,plain,(
    ! [A_62,B_63,C_64] :
      ( r2_hidden(k4_tarski('#skF_1'(A_62,B_63,C_64),A_62),C_64)
      | ~ r2_hidden(A_62,k9_relat_1(C_64,B_63))
      | ~ v1_relat_1(C_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_20,plain,(
    ! [C_18,A_16,B_17] :
      ( k1_funct_1(C_18,A_16) = B_17
      | ~ r2_hidden(k4_tarski(A_16,B_17),C_18)
      | ~ v1_funct_1(C_18)
      | ~ v1_relat_1(C_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_178,plain,(
    ! [C_65,A_66,B_67] :
      ( k1_funct_1(C_65,'#skF_1'(A_66,B_67,C_65)) = A_66
      | ~ v1_funct_1(C_65)
      | ~ r2_hidden(A_66,k9_relat_1(C_65,B_67))
      | ~ v1_relat_1(C_65) ) ),
    inference(resolution,[status(thm)],[c_152,c_20])).

tff(c_189,plain,(
    ! [A_66] :
      ( k1_funct_1('#skF_5','#skF_1'(A_66,'#skF_2','#skF_5')) = A_66
      | ~ v1_funct_1('#skF_5')
      | ~ r2_hidden(A_66,k2_relat_1('#skF_5'))
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_81,c_178])).

tff(c_195,plain,(
    ! [A_68] :
      ( k1_funct_1('#skF_5','#skF_1'(A_68,'#skF_2','#skF_5')) = A_68
      | ~ r2_hidden(A_68,k2_relat_1('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_47,c_38,c_189])).

tff(c_210,plain,(
    k1_funct_1('#skF_5','#skF_1'('#skF_4','#skF_2','#skF_5')) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_92,c_195])).

tff(c_217,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_126,c_210])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:25:55 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.28/1.36  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.28/1.37  
% 2.28/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.28/1.37  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k9_relat_1 > k7_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4
% 2.28/1.37  
% 2.28/1.37  %Foreground sorts:
% 2.28/1.37  
% 2.28/1.37  
% 2.28/1.37  %Background operators:
% 2.28/1.37  
% 2.28/1.37  
% 2.28/1.37  %Foreground operators:
% 2.28/1.37  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.28/1.37  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.28/1.37  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.28/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.28/1.37  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.28/1.37  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.28/1.37  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.28/1.37  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.28/1.37  tff('#skF_5', type, '#skF_5': $i).
% 2.28/1.37  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.28/1.37  tff('#skF_2', type, '#skF_2': $i).
% 2.28/1.37  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.28/1.37  tff('#skF_3', type, '#skF_3': $i).
% 2.28/1.37  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.28/1.37  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.28/1.37  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.28/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.28/1.37  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.28/1.37  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.28/1.37  tff('#skF_4', type, '#skF_4': $i).
% 2.28/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.28/1.37  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.28/1.37  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.28/1.37  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.28/1.37  
% 2.51/1.38  tff(f_91, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ~(r2_hidden(C, k2_relset_1(A, B, D)) & (![E]: ~(r2_hidden(E, A) & (k1_funct_1(D, E) = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_funct_2)).
% 2.51/1.38  tff(f_75, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.51/1.38  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.51/1.38  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.51/1.38  tff(f_71, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.51/1.38  tff(f_55, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 2.51/1.38  tff(f_49, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 2.51/1.38  tff(f_45, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_relat_1)).
% 2.51/1.38  tff(f_65, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_1)).
% 2.51/1.38  tff(c_34, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.51/1.38  tff(c_83, plain, (![A_42, B_43, C_44]: (k2_relset_1(A_42, B_43, C_44)=k2_relat_1(C_44) | ~m1_subset_1(C_44, k1_zfmisc_1(k2_zfmisc_1(A_42, B_43))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.51/1.38  tff(c_87, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_34, c_83])).
% 2.51/1.38  tff(c_32, plain, (r2_hidden('#skF_4', k2_relset_1('#skF_2', '#skF_3', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.51/1.38  tff(c_92, plain, (r2_hidden('#skF_4', k2_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_87, c_32])).
% 2.51/1.38  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.51/1.38  tff(c_41, plain, (![B_30, A_31]: (v1_relat_1(B_30) | ~m1_subset_1(B_30, k1_zfmisc_1(A_31)) | ~v1_relat_1(A_31))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.51/1.38  tff(c_44, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_34, c_41])).
% 2.51/1.38  tff(c_47, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_44])).
% 2.51/1.38  tff(c_63, plain, (![C_39, A_40, B_41]: (v4_relat_1(C_39, A_40) | ~m1_subset_1(C_39, k1_zfmisc_1(k2_zfmisc_1(A_40, B_41))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.51/1.38  tff(c_67, plain, (v4_relat_1('#skF_5', '#skF_2')), inference(resolution, [status(thm)], [c_34, c_63])).
% 2.51/1.38  tff(c_16, plain, (![B_15, A_14]: (k7_relat_1(B_15, A_14)=B_15 | ~v4_relat_1(B_15, A_14) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.51/1.38  tff(c_70, plain, (k7_relat_1('#skF_5', '#skF_2')='#skF_5' | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_67, c_16])).
% 2.51/1.38  tff(c_73, plain, (k7_relat_1('#skF_5', '#skF_2')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_47, c_70])).
% 2.51/1.38  tff(c_14, plain, (![B_13, A_12]: (k2_relat_1(k7_relat_1(B_13, A_12))=k9_relat_1(B_13, A_12) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.51/1.38  tff(c_77, plain, (k9_relat_1('#skF_5', '#skF_2')=k2_relat_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_73, c_14])).
% 2.51/1.38  tff(c_81, plain, (k9_relat_1('#skF_5', '#skF_2')=k2_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_47, c_77])).
% 2.51/1.38  tff(c_99, plain, (![A_51, B_52, C_53]: (r2_hidden('#skF_1'(A_51, B_52, C_53), B_52) | ~r2_hidden(A_51, k9_relat_1(C_53, B_52)) | ~v1_relat_1(C_53))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.51/1.38  tff(c_30, plain, (![E_26]: (k1_funct_1('#skF_5', E_26)!='#skF_4' | ~r2_hidden(E_26, '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.51/1.38  tff(c_106, plain, (![A_57, C_58]: (k1_funct_1('#skF_5', '#skF_1'(A_57, '#skF_2', C_58))!='#skF_4' | ~r2_hidden(A_57, k9_relat_1(C_58, '#skF_2')) | ~v1_relat_1(C_58))), inference(resolution, [status(thm)], [c_99, c_30])).
% 2.51/1.38  tff(c_113, plain, (![A_57]: (k1_funct_1('#skF_5', '#skF_1'(A_57, '#skF_2', '#skF_5'))!='#skF_4' | ~r2_hidden(A_57, k2_relat_1('#skF_5')) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_81, c_106])).
% 2.51/1.38  tff(c_117, plain, (![A_59]: (k1_funct_1('#skF_5', '#skF_1'(A_59, '#skF_2', '#skF_5'))!='#skF_4' | ~r2_hidden(A_59, k2_relat_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_47, c_113])).
% 2.51/1.38  tff(c_126, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_4', '#skF_2', '#skF_5'))!='#skF_4'), inference(resolution, [status(thm)], [c_92, c_117])).
% 2.51/1.38  tff(c_38, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.51/1.38  tff(c_152, plain, (![A_62, B_63, C_64]: (r2_hidden(k4_tarski('#skF_1'(A_62, B_63, C_64), A_62), C_64) | ~r2_hidden(A_62, k9_relat_1(C_64, B_63)) | ~v1_relat_1(C_64))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.51/1.38  tff(c_20, plain, (![C_18, A_16, B_17]: (k1_funct_1(C_18, A_16)=B_17 | ~r2_hidden(k4_tarski(A_16, B_17), C_18) | ~v1_funct_1(C_18) | ~v1_relat_1(C_18))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.51/1.38  tff(c_178, plain, (![C_65, A_66, B_67]: (k1_funct_1(C_65, '#skF_1'(A_66, B_67, C_65))=A_66 | ~v1_funct_1(C_65) | ~r2_hidden(A_66, k9_relat_1(C_65, B_67)) | ~v1_relat_1(C_65))), inference(resolution, [status(thm)], [c_152, c_20])).
% 2.51/1.38  tff(c_189, plain, (![A_66]: (k1_funct_1('#skF_5', '#skF_1'(A_66, '#skF_2', '#skF_5'))=A_66 | ~v1_funct_1('#skF_5') | ~r2_hidden(A_66, k2_relat_1('#skF_5')) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_81, c_178])).
% 2.51/1.38  tff(c_195, plain, (![A_68]: (k1_funct_1('#skF_5', '#skF_1'(A_68, '#skF_2', '#skF_5'))=A_68 | ~r2_hidden(A_68, k2_relat_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_47, c_38, c_189])).
% 2.51/1.38  tff(c_210, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_4', '#skF_2', '#skF_5'))='#skF_4'), inference(resolution, [status(thm)], [c_92, c_195])).
% 2.51/1.38  tff(c_217, plain, $false, inference(negUnitSimplification, [status(thm)], [c_126, c_210])).
% 2.51/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.51/1.38  
% 2.51/1.38  Inference rules
% 2.51/1.38  ----------------------
% 2.51/1.38  #Ref     : 0
% 2.51/1.38  #Sup     : 37
% 2.51/1.38  #Fact    : 0
% 2.51/1.38  #Define  : 0
% 2.51/1.38  #Split   : 2
% 2.51/1.38  #Chain   : 0
% 2.51/1.38  #Close   : 0
% 2.51/1.38  
% 2.51/1.38  Ordering : KBO
% 2.51/1.38  
% 2.51/1.38  Simplification rules
% 2.51/1.38  ----------------------
% 2.51/1.38  #Subsume      : 2
% 2.51/1.38  #Demod        : 7
% 2.51/1.38  #Tautology    : 10
% 2.51/1.38  #SimpNegUnit  : 1
% 2.51/1.38  #BackRed      : 1
% 2.51/1.38  
% 2.51/1.38  #Partial instantiations: 0
% 2.51/1.38  #Strategies tried      : 1
% 2.51/1.38  
% 2.51/1.38  Timing (in seconds)
% 2.51/1.38  ----------------------
% 2.51/1.39  Preprocessing        : 0.35
% 2.51/1.39  Parsing              : 0.19
% 2.51/1.39  CNF conversion       : 0.02
% 2.51/1.39  Main loop            : 0.20
% 2.51/1.39  Inferencing          : 0.07
% 2.51/1.39  Reduction            : 0.06
% 2.51/1.39  Demodulation         : 0.04
% 2.51/1.39  BG Simplification    : 0.02
% 2.51/1.39  Subsumption          : 0.04
% 2.51/1.39  Abstraction          : 0.01
% 2.51/1.39  MUC search           : 0.00
% 2.51/1.39  Cooper               : 0.00
% 2.51/1.39  Total                : 0.59
% 2.51/1.39  Index Insertion      : 0.00
% 2.51/1.39  Index Deletion       : 0.00
% 2.51/1.39  Index Matching       : 0.00
% 2.51/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
