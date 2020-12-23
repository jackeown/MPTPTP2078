%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:34 EST 2020

% Result     : Theorem 2.25s
% Output     : CNFRefutation 2.25s
% Verified   : 
% Statistics : Number of formulae       :   61 (  98 expanded)
%              Number of leaves         :   30 (  48 expanded)
%              Depth                    :   10
%              Number of atoms          :   92 ( 217 expanded)
%              Number of equality atoms :   17 (  35 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4

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

tff(f_87,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [E] :
            ~ ( r2_hidden(E,k7_relset_1(A,B,D,C))
              & ! [F] :
                  ( m1_subset_1(F,A)
                 => ~ ( r2_hidden(F,C)
                      & E = k1_funct_1(D,F) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t116_funct_2)).

tff(f_68,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

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

tff(c_30,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_111,plain,(
    ! [A_62,B_63,C_64,D_65] :
      ( k7_relset_1(A_62,B_63,C_64,D_65) = k9_relat_1(C_64,D_65)
      | ~ m1_subset_1(C_64,k1_zfmisc_1(k2_zfmisc_1(A_62,B_63))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_118,plain,(
    ! [D_65] : k7_relset_1('#skF_2','#skF_3','#skF_5',D_65) = k9_relat_1('#skF_5',D_65) ),
    inference(resolution,[status(thm)],[c_30,c_111])).

tff(c_28,plain,(
    r2_hidden('#skF_6',k7_relset_1('#skF_2','#skF_3','#skF_5','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_119,plain,(
    r2_hidden('#skF_6',k9_relat_1('#skF_5','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_28])).

tff(c_35,plain,(
    ! [C_31,A_32,B_33] :
      ( v1_relat_1(C_31)
      | ~ m1_subset_1(C_31,k1_zfmisc_1(k2_zfmisc_1(A_32,B_33))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_39,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_30,c_35])).

tff(c_91,plain,(
    ! [A_55,B_56,C_57] :
      ( r2_hidden('#skF_1'(A_55,B_56,C_57),k1_relat_1(C_57))
      | ~ r2_hidden(A_55,k9_relat_1(C_57,B_56))
      | ~ v1_relat_1(C_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_46,plain,(
    ! [A_39,B_40,C_41] :
      ( k1_relset_1(A_39,B_40,C_41) = k1_relat_1(C_41)
      | ~ m1_subset_1(C_41,k1_zfmisc_1(k2_zfmisc_1(A_39,B_40))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_50,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_30,c_46])).

tff(c_62,plain,(
    ! [A_48,B_49,C_50] :
      ( m1_subset_1(k1_relset_1(A_48,B_49,C_50),k1_zfmisc_1(A_48))
      | ~ m1_subset_1(C_50,k1_zfmisc_1(k2_zfmisc_1(A_48,B_49))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_75,plain,
    ( m1_subset_1(k1_relat_1('#skF_5'),k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_62])).

tff(c_80,plain,(
    m1_subset_1(k1_relat_1('#skF_5'),k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_75])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( m1_subset_1(A_1,C_3)
      | ~ m1_subset_1(B_2,k1_zfmisc_1(C_3))
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_83,plain,(
    ! [A_1] :
      ( m1_subset_1(A_1,'#skF_2')
      | ~ r2_hidden(A_1,k1_relat_1('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_80,c_2])).

tff(c_95,plain,(
    ! [A_55,B_56] :
      ( m1_subset_1('#skF_1'(A_55,B_56,'#skF_5'),'#skF_2')
      | ~ r2_hidden(A_55,k9_relat_1('#skF_5',B_56))
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_91,c_83])).

tff(c_98,plain,(
    ! [A_55,B_56] :
      ( m1_subset_1('#skF_1'(A_55,B_56,'#skF_5'),'#skF_2')
      | ~ r2_hidden(A_55,k9_relat_1('#skF_5',B_56)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_39,c_95])).

tff(c_138,plain,(
    m1_subset_1('#skF_1'('#skF_6','#skF_4','#skF_5'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_119,c_98])).

tff(c_56,plain,(
    ! [A_45,B_46,C_47] :
      ( r2_hidden('#skF_1'(A_45,B_46,C_47),B_46)
      | ~ r2_hidden(A_45,k9_relat_1(C_47,B_46))
      | ~ v1_relat_1(C_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_26,plain,(
    ! [F_30] :
      ( k1_funct_1('#skF_5',F_30) != '#skF_6'
      | ~ r2_hidden(F_30,'#skF_4')
      | ~ m1_subset_1(F_30,'#skF_2') ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_61,plain,(
    ! [A_45,C_47] :
      ( k1_funct_1('#skF_5','#skF_1'(A_45,'#skF_4',C_47)) != '#skF_6'
      | ~ m1_subset_1('#skF_1'(A_45,'#skF_4',C_47),'#skF_2')
      | ~ r2_hidden(A_45,k9_relat_1(C_47,'#skF_4'))
      | ~ v1_relat_1(C_47) ) ),
    inference(resolution,[status(thm)],[c_56,c_26])).

tff(c_131,plain,
    ( k1_funct_1('#skF_5','#skF_1'('#skF_6','#skF_4','#skF_5')) != '#skF_6'
    | ~ m1_subset_1('#skF_1'('#skF_6','#skF_4','#skF_5'),'#skF_2')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_119,c_61])).

tff(c_137,plain,
    ( k1_funct_1('#skF_5','#skF_1'('#skF_6','#skF_4','#skF_5')) != '#skF_6'
    | ~ m1_subset_1('#skF_1'('#skF_6','#skF_4','#skF_5'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_39,c_131])).

tff(c_140,plain,(
    k1_funct_1('#skF_5','#skF_1'('#skF_6','#skF_4','#skF_5')) != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_137])).

tff(c_34,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_171,plain,(
    ! [A_69,B_70,C_71] :
      ( r2_hidden(k4_tarski('#skF_1'(A_69,B_70,C_71),A_69),C_71)
      | ~ r2_hidden(A_69,k9_relat_1(C_71,B_70))
      | ~ v1_relat_1(C_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_14,plain,(
    ! [C_12,A_10,B_11] :
      ( k1_funct_1(C_12,A_10) = B_11
      | ~ r2_hidden(k4_tarski(A_10,B_11),C_12)
      | ~ v1_funct_1(C_12)
      | ~ v1_relat_1(C_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_240,plain,(
    ! [C_82,A_83,B_84] :
      ( k1_funct_1(C_82,'#skF_1'(A_83,B_84,C_82)) = A_83
      | ~ v1_funct_1(C_82)
      | ~ r2_hidden(A_83,k9_relat_1(C_82,B_84))
      | ~ v1_relat_1(C_82) ) ),
    inference(resolution,[status(thm)],[c_171,c_14])).

tff(c_248,plain,
    ( k1_funct_1('#skF_5','#skF_1'('#skF_6','#skF_4','#skF_5')) = '#skF_6'
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_119,c_240])).

tff(c_256,plain,(
    k1_funct_1('#skF_5','#skF_1'('#skF_6','#skF_4','#skF_5')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_39,c_34,c_248])).

tff(c_258,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_140,c_256])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:19:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.25/1.38  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.25/1.38  
% 2.25/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.25/1.39  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4
% 2.25/1.39  
% 2.25/1.39  %Foreground sorts:
% 2.25/1.39  
% 2.25/1.39  
% 2.25/1.39  %Background operators:
% 2.25/1.39  
% 2.25/1.39  
% 2.25/1.39  %Foreground operators:
% 2.25/1.39  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.25/1.39  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.25/1.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.25/1.39  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.25/1.39  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.25/1.39  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.25/1.39  tff('#skF_5', type, '#skF_5': $i).
% 2.25/1.39  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.25/1.39  tff('#skF_6', type, '#skF_6': $i).
% 2.25/1.39  tff('#skF_2', type, '#skF_2': $i).
% 2.25/1.39  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.25/1.39  tff('#skF_3', type, '#skF_3': $i).
% 2.25/1.39  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.25/1.39  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.25/1.39  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.25/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.25/1.39  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.25/1.39  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.25/1.39  tff('#skF_4', type, '#skF_4': $i).
% 2.25/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.25/1.39  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.25/1.39  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.25/1.39  
% 2.25/1.40  tff(f_87, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: ~(r2_hidden(E, k7_relset_1(A, B, D, C)) & (![F]: (m1_subset_1(F, A) => ~(r2_hidden(F, C) & (E = k1_funct_1(D, F))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t116_funct_2)).
% 2.25/1.40  tff(f_68, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 2.25/1.40  tff(f_56, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.25/1.40  tff(f_42, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_relat_1)).
% 2.25/1.40  tff(f_64, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.25/1.40  tff(f_60, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k1_relset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_relset_1)).
% 2.25/1.40  tff(f_31, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 2.25/1.40  tff(f_52, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_1)).
% 2.25/1.40  tff(c_30, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.25/1.40  tff(c_111, plain, (![A_62, B_63, C_64, D_65]: (k7_relset_1(A_62, B_63, C_64, D_65)=k9_relat_1(C_64, D_65) | ~m1_subset_1(C_64, k1_zfmisc_1(k2_zfmisc_1(A_62, B_63))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.25/1.40  tff(c_118, plain, (![D_65]: (k7_relset_1('#skF_2', '#skF_3', '#skF_5', D_65)=k9_relat_1('#skF_5', D_65))), inference(resolution, [status(thm)], [c_30, c_111])).
% 2.25/1.40  tff(c_28, plain, (r2_hidden('#skF_6', k7_relset_1('#skF_2', '#skF_3', '#skF_5', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.25/1.40  tff(c_119, plain, (r2_hidden('#skF_6', k9_relat_1('#skF_5', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_118, c_28])).
% 2.25/1.40  tff(c_35, plain, (![C_31, A_32, B_33]: (v1_relat_1(C_31) | ~m1_subset_1(C_31, k1_zfmisc_1(k2_zfmisc_1(A_32, B_33))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.25/1.40  tff(c_39, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_30, c_35])).
% 2.25/1.40  tff(c_91, plain, (![A_55, B_56, C_57]: (r2_hidden('#skF_1'(A_55, B_56, C_57), k1_relat_1(C_57)) | ~r2_hidden(A_55, k9_relat_1(C_57, B_56)) | ~v1_relat_1(C_57))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.25/1.40  tff(c_46, plain, (![A_39, B_40, C_41]: (k1_relset_1(A_39, B_40, C_41)=k1_relat_1(C_41) | ~m1_subset_1(C_41, k1_zfmisc_1(k2_zfmisc_1(A_39, B_40))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.25/1.40  tff(c_50, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_30, c_46])).
% 2.25/1.40  tff(c_62, plain, (![A_48, B_49, C_50]: (m1_subset_1(k1_relset_1(A_48, B_49, C_50), k1_zfmisc_1(A_48)) | ~m1_subset_1(C_50, k1_zfmisc_1(k2_zfmisc_1(A_48, B_49))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.25/1.40  tff(c_75, plain, (m1_subset_1(k1_relat_1('#skF_5'), k1_zfmisc_1('#skF_2')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_50, c_62])).
% 2.25/1.40  tff(c_80, plain, (m1_subset_1(k1_relat_1('#skF_5'), k1_zfmisc_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_75])).
% 2.25/1.40  tff(c_2, plain, (![A_1, C_3, B_2]: (m1_subset_1(A_1, C_3) | ~m1_subset_1(B_2, k1_zfmisc_1(C_3)) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.25/1.40  tff(c_83, plain, (![A_1]: (m1_subset_1(A_1, '#skF_2') | ~r2_hidden(A_1, k1_relat_1('#skF_5')))), inference(resolution, [status(thm)], [c_80, c_2])).
% 2.25/1.40  tff(c_95, plain, (![A_55, B_56]: (m1_subset_1('#skF_1'(A_55, B_56, '#skF_5'), '#skF_2') | ~r2_hidden(A_55, k9_relat_1('#skF_5', B_56)) | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_91, c_83])).
% 2.25/1.40  tff(c_98, plain, (![A_55, B_56]: (m1_subset_1('#skF_1'(A_55, B_56, '#skF_5'), '#skF_2') | ~r2_hidden(A_55, k9_relat_1('#skF_5', B_56)))), inference(demodulation, [status(thm), theory('equality')], [c_39, c_95])).
% 2.25/1.40  tff(c_138, plain, (m1_subset_1('#skF_1'('#skF_6', '#skF_4', '#skF_5'), '#skF_2')), inference(resolution, [status(thm)], [c_119, c_98])).
% 2.25/1.40  tff(c_56, plain, (![A_45, B_46, C_47]: (r2_hidden('#skF_1'(A_45, B_46, C_47), B_46) | ~r2_hidden(A_45, k9_relat_1(C_47, B_46)) | ~v1_relat_1(C_47))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.25/1.40  tff(c_26, plain, (![F_30]: (k1_funct_1('#skF_5', F_30)!='#skF_6' | ~r2_hidden(F_30, '#skF_4') | ~m1_subset_1(F_30, '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.25/1.40  tff(c_61, plain, (![A_45, C_47]: (k1_funct_1('#skF_5', '#skF_1'(A_45, '#skF_4', C_47))!='#skF_6' | ~m1_subset_1('#skF_1'(A_45, '#skF_4', C_47), '#skF_2') | ~r2_hidden(A_45, k9_relat_1(C_47, '#skF_4')) | ~v1_relat_1(C_47))), inference(resolution, [status(thm)], [c_56, c_26])).
% 2.25/1.40  tff(c_131, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_6', '#skF_4', '#skF_5'))!='#skF_6' | ~m1_subset_1('#skF_1'('#skF_6', '#skF_4', '#skF_5'), '#skF_2') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_119, c_61])).
% 2.25/1.40  tff(c_137, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_6', '#skF_4', '#skF_5'))!='#skF_6' | ~m1_subset_1('#skF_1'('#skF_6', '#skF_4', '#skF_5'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_39, c_131])).
% 2.25/1.40  tff(c_140, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_6', '#skF_4', '#skF_5'))!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_138, c_137])).
% 2.25/1.40  tff(c_34, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.25/1.40  tff(c_171, plain, (![A_69, B_70, C_71]: (r2_hidden(k4_tarski('#skF_1'(A_69, B_70, C_71), A_69), C_71) | ~r2_hidden(A_69, k9_relat_1(C_71, B_70)) | ~v1_relat_1(C_71))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.25/1.40  tff(c_14, plain, (![C_12, A_10, B_11]: (k1_funct_1(C_12, A_10)=B_11 | ~r2_hidden(k4_tarski(A_10, B_11), C_12) | ~v1_funct_1(C_12) | ~v1_relat_1(C_12))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.25/1.40  tff(c_240, plain, (![C_82, A_83, B_84]: (k1_funct_1(C_82, '#skF_1'(A_83, B_84, C_82))=A_83 | ~v1_funct_1(C_82) | ~r2_hidden(A_83, k9_relat_1(C_82, B_84)) | ~v1_relat_1(C_82))), inference(resolution, [status(thm)], [c_171, c_14])).
% 2.25/1.40  tff(c_248, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_6', '#skF_4', '#skF_5'))='#skF_6' | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_119, c_240])).
% 2.25/1.40  tff(c_256, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_6', '#skF_4', '#skF_5'))='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_39, c_34, c_248])).
% 2.25/1.40  tff(c_258, plain, $false, inference(negUnitSimplification, [status(thm)], [c_140, c_256])).
% 2.25/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.25/1.40  
% 2.25/1.40  Inference rules
% 2.25/1.40  ----------------------
% 2.25/1.40  #Ref     : 0
% 2.25/1.40  #Sup     : 45
% 2.25/1.40  #Fact    : 0
% 2.25/1.40  #Define  : 0
% 2.25/1.40  #Split   : 1
% 2.25/1.40  #Chain   : 0
% 2.25/1.40  #Close   : 0
% 2.25/1.40  
% 2.25/1.40  Ordering : KBO
% 2.25/1.40  
% 2.25/1.40  Simplification rules
% 2.25/1.40  ----------------------
% 2.25/1.40  #Subsume      : 2
% 2.25/1.40  #Demod        : 8
% 2.25/1.40  #Tautology    : 6
% 2.25/1.40  #SimpNegUnit  : 1
% 2.25/1.40  #BackRed      : 1
% 2.25/1.40  
% 2.25/1.40  #Partial instantiations: 0
% 2.25/1.40  #Strategies tried      : 1
% 2.25/1.40  
% 2.25/1.40  Timing (in seconds)
% 2.25/1.40  ----------------------
% 2.25/1.41  Preprocessing        : 0.32
% 2.25/1.41  Parsing              : 0.17
% 2.25/1.41  CNF conversion       : 0.02
% 2.25/1.41  Main loop            : 0.20
% 2.25/1.41  Inferencing          : 0.08
% 2.25/1.41  Reduction            : 0.06
% 2.25/1.41  Demodulation         : 0.04
% 2.25/1.41  BG Simplification    : 0.01
% 2.25/1.41  Subsumption          : 0.04
% 2.25/1.41  Abstraction          : 0.01
% 2.25/1.41  MUC search           : 0.00
% 2.25/1.41  Cooper               : 0.00
% 2.25/1.41  Total                : 0.55
% 2.25/1.41  Index Insertion      : 0.00
% 2.25/1.41  Index Deletion       : 0.00
% 2.25/1.41  Index Matching       : 0.00
% 2.25/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
