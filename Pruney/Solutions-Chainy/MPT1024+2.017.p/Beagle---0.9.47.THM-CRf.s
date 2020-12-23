%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:24 EST 2020

% Result     : Theorem 2.14s
% Output     : CNFRefutation 2.14s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 100 expanded)
%              Number of leaves         :   32 (  50 expanded)
%              Depth                    :   13
%              Number of atoms          :   97 ( 218 expanded)
%              Number of equality atoms :   18 (  32 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k9_relat_1 > k7_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4

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

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

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

tff(f_93,negated_conjecture,(
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

tff(f_74,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k1_relat_1(k7_relat_1(C,B)))
      <=> ( r2_hidden(A,B)
          & r2_hidden(A,k1_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_relat_1)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

tff(c_36,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_105,plain,(
    ! [A_60,B_61,C_62,D_63] :
      ( k7_relset_1(A_60,B_61,C_62,D_63) = k9_relat_1(C_62,D_63)
      | ~ m1_subset_1(C_62,k1_zfmisc_1(k2_zfmisc_1(A_60,B_61))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_108,plain,(
    ! [D_63] : k7_relset_1('#skF_2','#skF_3','#skF_5',D_63) = k9_relat_1('#skF_5',D_63) ),
    inference(resolution,[status(thm)],[c_36,c_105])).

tff(c_34,plain,(
    r2_hidden('#skF_6',k7_relset_1('#skF_2','#skF_3','#skF_5','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_109,plain,(
    r2_hidden('#skF_6',k9_relat_1('#skF_5','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_34])).

tff(c_41,plain,(
    ! [C_30,A_31,B_32] :
      ( v1_relat_1(C_30)
      | ~ m1_subset_1(C_30,k1_zfmisc_1(k2_zfmisc_1(A_31,B_32))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_45,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_36,c_41])).

tff(c_4,plain,(
    ! [A_1,B_2,C_3] :
      ( r2_hidden('#skF_1'(A_1,B_2,C_3),B_2)
      | ~ r2_hidden(A_1,k9_relat_1(C_3,B_2))
      | ~ v1_relat_1(C_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_119,plain,(
    ! [A_65,B_66,C_67] :
      ( r2_hidden('#skF_1'(A_65,B_66,C_67),k1_relat_1(C_67))
      | ~ r2_hidden(A_65,k9_relat_1(C_67,B_66))
      | ~ v1_relat_1(C_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_51,plain,(
    ! [C_36,A_37,B_38] :
      ( v4_relat_1(C_36,A_37)
      | ~ m1_subset_1(C_36,k1_zfmisc_1(k2_zfmisc_1(A_37,B_38))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_55,plain,(
    v4_relat_1('#skF_5','#skF_2') ),
    inference(resolution,[status(thm)],[c_36,c_51])).

tff(c_57,plain,(
    ! [B_40,A_41] :
      ( k7_relat_1(B_40,A_41) = B_40
      | ~ v4_relat_1(B_40,A_41)
      | ~ v1_relat_1(B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_60,plain,
    ( k7_relat_1('#skF_5','#skF_2') = '#skF_5'
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_55,c_57])).

tff(c_63,plain,(
    k7_relat_1('#skF_5','#skF_2') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_45,c_60])).

tff(c_68,plain,(
    ! [A_42,B_43,C_44] :
      ( r2_hidden(A_42,B_43)
      | ~ r2_hidden(A_42,k1_relat_1(k7_relat_1(C_44,B_43)))
      | ~ v1_relat_1(C_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_71,plain,(
    ! [A_42] :
      ( r2_hidden(A_42,'#skF_2')
      | ~ r2_hidden(A_42,k1_relat_1('#skF_5'))
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_63,c_68])).

tff(c_73,plain,(
    ! [A_42] :
      ( r2_hidden(A_42,'#skF_2')
      | ~ r2_hidden(A_42,k1_relat_1('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_45,c_71])).

tff(c_127,plain,(
    ! [A_65,B_66] :
      ( r2_hidden('#skF_1'(A_65,B_66,'#skF_5'),'#skF_2')
      | ~ r2_hidden(A_65,k9_relat_1('#skF_5',B_66))
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_119,c_73])).

tff(c_137,plain,(
    ! [A_68,B_69] :
      ( r2_hidden('#skF_1'(A_68,B_69,'#skF_5'),'#skF_2')
      | ~ r2_hidden(A_68,k9_relat_1('#skF_5',B_69)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_45,c_127])).

tff(c_32,plain,(
    ! [F_29] :
      ( k1_funct_1('#skF_5',F_29) != '#skF_6'
      | ~ r2_hidden(F_29,'#skF_4')
      | ~ r2_hidden(F_29,'#skF_2') ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_230,plain,(
    ! [A_80,B_81] :
      ( k1_funct_1('#skF_5','#skF_1'(A_80,B_81,'#skF_5')) != '#skF_6'
      | ~ r2_hidden('#skF_1'(A_80,B_81,'#skF_5'),'#skF_4')
      | ~ r2_hidden(A_80,k9_relat_1('#skF_5',B_81)) ) ),
    inference(resolution,[status(thm)],[c_137,c_32])).

tff(c_234,plain,(
    ! [A_1] :
      ( k1_funct_1('#skF_5','#skF_1'(A_1,'#skF_4','#skF_5')) != '#skF_6'
      | ~ r2_hidden(A_1,k9_relat_1('#skF_5','#skF_4'))
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_4,c_230])).

tff(c_238,plain,(
    ! [A_82] :
      ( k1_funct_1('#skF_5','#skF_1'(A_82,'#skF_4','#skF_5')) != '#skF_6'
      | ~ r2_hidden(A_82,k9_relat_1('#skF_5','#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_45,c_234])).

tff(c_256,plain,(
    k1_funct_1('#skF_5','#skF_1'('#skF_6','#skF_4','#skF_5')) != '#skF_6' ),
    inference(resolution,[status(thm)],[c_109,c_238])).

tff(c_40,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_166,plain,(
    ! [A_73,B_74,C_75] :
      ( r2_hidden(k4_tarski('#skF_1'(A_73,B_74,C_75),A_73),C_75)
      | ~ r2_hidden(A_73,k9_relat_1(C_75,B_74))
      | ~ v1_relat_1(C_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_20,plain,(
    ! [C_14,A_12,B_13] :
      ( k1_funct_1(C_14,A_12) = B_13
      | ~ r2_hidden(k4_tarski(A_12,B_13),C_14)
      | ~ v1_funct_1(C_14)
      | ~ v1_relat_1(C_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_258,plain,(
    ! [C_83,A_84,B_85] :
      ( k1_funct_1(C_83,'#skF_1'(A_84,B_85,C_83)) = A_84
      | ~ v1_funct_1(C_83)
      | ~ r2_hidden(A_84,k9_relat_1(C_83,B_85))
      | ~ v1_relat_1(C_83) ) ),
    inference(resolution,[status(thm)],[c_166,c_20])).

tff(c_266,plain,
    ( k1_funct_1('#skF_5','#skF_1'('#skF_6','#skF_4','#skF_5')) = '#skF_6'
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_109,c_258])).

tff(c_274,plain,(
    k1_funct_1('#skF_5','#skF_1'('#skF_6','#skF_4','#skF_5')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_45,c_40,c_266])).

tff(c_276,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_256,c_274])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 19:52:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.14/1.28  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.14/1.29  
% 2.14/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.14/1.29  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k9_relat_1 > k7_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4
% 2.14/1.29  
% 2.14/1.29  %Foreground sorts:
% 2.14/1.29  
% 2.14/1.29  
% 2.14/1.29  %Background operators:
% 2.14/1.29  
% 2.14/1.29  
% 2.14/1.29  %Foreground operators:
% 2.14/1.29  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.14/1.29  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.14/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.14/1.29  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.14/1.29  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.14/1.29  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.14/1.29  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.14/1.29  tff('#skF_5', type, '#skF_5': $i).
% 2.14/1.29  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.14/1.29  tff('#skF_6', type, '#skF_6': $i).
% 2.14/1.29  tff('#skF_2', type, '#skF_2': $i).
% 2.14/1.29  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.14/1.29  tff('#skF_3', type, '#skF_3': $i).
% 2.14/1.29  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.14/1.29  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.14/1.29  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.14/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.14/1.29  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.14/1.29  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.14/1.29  tff('#skF_4', type, '#skF_4': $i).
% 2.14/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.14/1.29  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.14/1.29  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.14/1.29  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.14/1.29  
% 2.14/1.31  tff(f_93, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: ~(r2_hidden(E, k7_relset_1(A, B, D, C)) & (![F]: ~((r2_hidden(F, A) & r2_hidden(F, C)) & (E = k1_funct_1(D, F)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t115_funct_2)).
% 2.14/1.31  tff(f_74, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 2.14/1.31  tff(f_64, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.14/1.31  tff(f_36, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t143_relat_1)).
% 2.14/1.31  tff(f_70, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.14/1.31  tff(f_42, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 2.14/1.31  tff(f_50, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k1_relat_1(k7_relat_1(C, B))) <=> (r2_hidden(A, B) & r2_hidden(A, k1_relat_1(C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_relat_1)).
% 2.14/1.31  tff(f_60, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_funct_1)).
% 2.14/1.31  tff(c_36, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.14/1.31  tff(c_105, plain, (![A_60, B_61, C_62, D_63]: (k7_relset_1(A_60, B_61, C_62, D_63)=k9_relat_1(C_62, D_63) | ~m1_subset_1(C_62, k1_zfmisc_1(k2_zfmisc_1(A_60, B_61))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.14/1.31  tff(c_108, plain, (![D_63]: (k7_relset_1('#skF_2', '#skF_3', '#skF_5', D_63)=k9_relat_1('#skF_5', D_63))), inference(resolution, [status(thm)], [c_36, c_105])).
% 2.14/1.31  tff(c_34, plain, (r2_hidden('#skF_6', k7_relset_1('#skF_2', '#skF_3', '#skF_5', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.14/1.31  tff(c_109, plain, (r2_hidden('#skF_6', k9_relat_1('#skF_5', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_108, c_34])).
% 2.14/1.31  tff(c_41, plain, (![C_30, A_31, B_32]: (v1_relat_1(C_30) | ~m1_subset_1(C_30, k1_zfmisc_1(k2_zfmisc_1(A_31, B_32))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.14/1.31  tff(c_45, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_36, c_41])).
% 2.14/1.31  tff(c_4, plain, (![A_1, B_2, C_3]: (r2_hidden('#skF_1'(A_1, B_2, C_3), B_2) | ~r2_hidden(A_1, k9_relat_1(C_3, B_2)) | ~v1_relat_1(C_3))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.14/1.31  tff(c_119, plain, (![A_65, B_66, C_67]: (r2_hidden('#skF_1'(A_65, B_66, C_67), k1_relat_1(C_67)) | ~r2_hidden(A_65, k9_relat_1(C_67, B_66)) | ~v1_relat_1(C_67))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.14/1.31  tff(c_51, plain, (![C_36, A_37, B_38]: (v4_relat_1(C_36, A_37) | ~m1_subset_1(C_36, k1_zfmisc_1(k2_zfmisc_1(A_37, B_38))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.14/1.31  tff(c_55, plain, (v4_relat_1('#skF_5', '#skF_2')), inference(resolution, [status(thm)], [c_36, c_51])).
% 2.14/1.31  tff(c_57, plain, (![B_40, A_41]: (k7_relat_1(B_40, A_41)=B_40 | ~v4_relat_1(B_40, A_41) | ~v1_relat_1(B_40))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.14/1.31  tff(c_60, plain, (k7_relat_1('#skF_5', '#skF_2')='#skF_5' | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_55, c_57])).
% 2.14/1.31  tff(c_63, plain, (k7_relat_1('#skF_5', '#skF_2')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_45, c_60])).
% 2.14/1.31  tff(c_68, plain, (![A_42, B_43, C_44]: (r2_hidden(A_42, B_43) | ~r2_hidden(A_42, k1_relat_1(k7_relat_1(C_44, B_43))) | ~v1_relat_1(C_44))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.14/1.31  tff(c_71, plain, (![A_42]: (r2_hidden(A_42, '#skF_2') | ~r2_hidden(A_42, k1_relat_1('#skF_5')) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_63, c_68])).
% 2.14/1.31  tff(c_73, plain, (![A_42]: (r2_hidden(A_42, '#skF_2') | ~r2_hidden(A_42, k1_relat_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_45, c_71])).
% 2.14/1.31  tff(c_127, plain, (![A_65, B_66]: (r2_hidden('#skF_1'(A_65, B_66, '#skF_5'), '#skF_2') | ~r2_hidden(A_65, k9_relat_1('#skF_5', B_66)) | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_119, c_73])).
% 2.14/1.31  tff(c_137, plain, (![A_68, B_69]: (r2_hidden('#skF_1'(A_68, B_69, '#skF_5'), '#skF_2') | ~r2_hidden(A_68, k9_relat_1('#skF_5', B_69)))), inference(demodulation, [status(thm), theory('equality')], [c_45, c_127])).
% 2.14/1.31  tff(c_32, plain, (![F_29]: (k1_funct_1('#skF_5', F_29)!='#skF_6' | ~r2_hidden(F_29, '#skF_4') | ~r2_hidden(F_29, '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.14/1.31  tff(c_230, plain, (![A_80, B_81]: (k1_funct_1('#skF_5', '#skF_1'(A_80, B_81, '#skF_5'))!='#skF_6' | ~r2_hidden('#skF_1'(A_80, B_81, '#skF_5'), '#skF_4') | ~r2_hidden(A_80, k9_relat_1('#skF_5', B_81)))), inference(resolution, [status(thm)], [c_137, c_32])).
% 2.14/1.31  tff(c_234, plain, (![A_1]: (k1_funct_1('#skF_5', '#skF_1'(A_1, '#skF_4', '#skF_5'))!='#skF_6' | ~r2_hidden(A_1, k9_relat_1('#skF_5', '#skF_4')) | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_4, c_230])).
% 2.14/1.31  tff(c_238, plain, (![A_82]: (k1_funct_1('#skF_5', '#skF_1'(A_82, '#skF_4', '#skF_5'))!='#skF_6' | ~r2_hidden(A_82, k9_relat_1('#skF_5', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_45, c_234])).
% 2.14/1.31  tff(c_256, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_6', '#skF_4', '#skF_5'))!='#skF_6'), inference(resolution, [status(thm)], [c_109, c_238])).
% 2.14/1.31  tff(c_40, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.14/1.31  tff(c_166, plain, (![A_73, B_74, C_75]: (r2_hidden(k4_tarski('#skF_1'(A_73, B_74, C_75), A_73), C_75) | ~r2_hidden(A_73, k9_relat_1(C_75, B_74)) | ~v1_relat_1(C_75))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.14/1.31  tff(c_20, plain, (![C_14, A_12, B_13]: (k1_funct_1(C_14, A_12)=B_13 | ~r2_hidden(k4_tarski(A_12, B_13), C_14) | ~v1_funct_1(C_14) | ~v1_relat_1(C_14))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.14/1.31  tff(c_258, plain, (![C_83, A_84, B_85]: (k1_funct_1(C_83, '#skF_1'(A_84, B_85, C_83))=A_84 | ~v1_funct_1(C_83) | ~r2_hidden(A_84, k9_relat_1(C_83, B_85)) | ~v1_relat_1(C_83))), inference(resolution, [status(thm)], [c_166, c_20])).
% 2.14/1.31  tff(c_266, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_6', '#skF_4', '#skF_5'))='#skF_6' | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_109, c_258])).
% 2.14/1.31  tff(c_274, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_6', '#skF_4', '#skF_5'))='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_45, c_40, c_266])).
% 2.14/1.31  tff(c_276, plain, $false, inference(negUnitSimplification, [status(thm)], [c_256, c_274])).
% 2.14/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.14/1.31  
% 2.14/1.31  Inference rules
% 2.14/1.31  ----------------------
% 2.14/1.31  #Ref     : 0
% 2.14/1.31  #Sup     : 46
% 2.14/1.31  #Fact    : 0
% 2.14/1.31  #Define  : 0
% 2.14/1.31  #Split   : 0
% 2.14/1.31  #Chain   : 0
% 2.14/1.31  #Close   : 0
% 2.14/1.31  
% 2.14/1.31  Ordering : KBO
% 2.14/1.31  
% 2.14/1.31  Simplification rules
% 2.14/1.31  ----------------------
% 2.14/1.31  #Subsume      : 1
% 2.14/1.31  #Demod        : 9
% 2.14/1.31  #Tautology    : 10
% 2.14/1.31  #SimpNegUnit  : 1
% 2.14/1.31  #BackRed      : 1
% 2.14/1.31  
% 2.14/1.31  #Partial instantiations: 0
% 2.14/1.31  #Strategies tried      : 1
% 2.14/1.31  
% 2.14/1.31  Timing (in seconds)
% 2.14/1.31  ----------------------
% 2.14/1.31  Preprocessing        : 0.32
% 2.14/1.31  Parsing              : 0.17
% 2.14/1.31  CNF conversion       : 0.02
% 2.14/1.31  Main loop            : 0.21
% 2.14/1.31  Inferencing          : 0.08
% 2.14/1.31  Reduction            : 0.06
% 2.14/1.31  Demodulation         : 0.04
% 2.14/1.31  BG Simplification    : 0.02
% 2.14/1.31  Subsumption          : 0.04
% 2.14/1.31  Abstraction          : 0.01
% 2.14/1.31  MUC search           : 0.00
% 2.14/1.31  Cooper               : 0.00
% 2.14/1.31  Total                : 0.56
% 2.14/1.31  Index Insertion      : 0.00
% 2.14/1.31  Index Deletion       : 0.00
% 2.14/1.31  Index Matching       : 0.00
% 2.14/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
