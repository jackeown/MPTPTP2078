%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:25 EST 2020

% Result     : Theorem 2.73s
% Output     : CNFRefutation 2.73s
% Verified   : 
% Statistics : Number of formulae       :   55 (  73 expanded)
%              Number of leaves         :   31 (  42 expanded)
%              Depth                    :    6
%              Number of atoms          :   86 ( 166 expanded)
%              Number of equality atoms :   14 (  26 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_9 > #skF_4 > #skF_8 > #skF_3

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

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_84,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t115_funct_2)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k1_relset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_relset_1)).

tff(f_49,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B,C] :
          ( C = k9_relat_1(A,B)
        <=> ! [D] :
              ( r2_hidden(D,C)
            <=> ? [E] :
                  ( r2_hidden(E,k1_relat_1(A))
                  & r2_hidden(E,B)
                  & D = k1_funct_1(A,E) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_funct_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_65,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(c_40,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_45,plain,(
    ! [C_65,A_66,B_67] :
      ( v1_relat_1(C_65)
      | ~ m1_subset_1(C_65,k1_zfmisc_1(k2_zfmisc_1(A_66,B_67))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_49,plain,(
    v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_40,c_45])).

tff(c_44,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_56,plain,(
    ! [A_73,B_74,C_75] :
      ( k1_relset_1(A_73,B_74,C_75) = k1_relat_1(C_75)
      | ~ m1_subset_1(C_75,k1_zfmisc_1(k2_zfmisc_1(A_73,B_74))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_60,plain,(
    k1_relset_1('#skF_5','#skF_6','#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_40,c_56])).

tff(c_65,plain,(
    ! [A_76,B_77,C_78] :
      ( m1_subset_1(k1_relset_1(A_76,B_77,C_78),k1_zfmisc_1(A_76))
      | ~ m1_subset_1(C_78,k1_zfmisc_1(k2_zfmisc_1(A_76,B_77))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_76,plain,
    ( m1_subset_1(k1_relat_1('#skF_8'),k1_zfmisc_1('#skF_5'))
    | ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_65])).

tff(c_80,plain,(
    m1_subset_1(k1_relat_1('#skF_8'),k1_zfmisc_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_76])).

tff(c_6,plain,(
    ! [A_5,B_28,D_43] :
      ( k1_funct_1(A_5,'#skF_4'(A_5,B_28,k9_relat_1(A_5,B_28),D_43)) = D_43
      | ~ r2_hidden(D_43,k9_relat_1(A_5,B_28))
      | ~ v1_funct_1(A_5)
      | ~ v1_relat_1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_135,plain,(
    ! [A_98,B_99,D_100] :
      ( r2_hidden('#skF_4'(A_98,B_99,k9_relat_1(A_98,B_99),D_100),k1_relat_1(A_98))
      | ~ r2_hidden(D_100,k9_relat_1(A_98,B_99))
      | ~ v1_funct_1(A_98)
      | ~ v1_relat_1(A_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_2,plain,(
    ! [C_4,A_1,B_2] :
      ( r2_hidden(C_4,A_1)
      | ~ r2_hidden(C_4,B_2)
      | ~ m1_subset_1(B_2,k1_zfmisc_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_138,plain,(
    ! [A_98,B_99,D_100,A_1] :
      ( r2_hidden('#skF_4'(A_98,B_99,k9_relat_1(A_98,B_99),D_100),A_1)
      | ~ m1_subset_1(k1_relat_1(A_98),k1_zfmisc_1(A_1))
      | ~ r2_hidden(D_100,k9_relat_1(A_98,B_99))
      | ~ v1_funct_1(A_98)
      | ~ v1_relat_1(A_98) ) ),
    inference(resolution,[status(thm)],[c_135,c_2])).

tff(c_108,plain,(
    ! [A_88,B_89,D_90] :
      ( r2_hidden('#skF_4'(A_88,B_89,k9_relat_1(A_88,B_89),D_90),B_89)
      | ~ r2_hidden(D_90,k9_relat_1(A_88,B_89))
      | ~ v1_funct_1(A_88)
      | ~ v1_relat_1(A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_36,plain,(
    ! [F_64] :
      ( k1_funct_1('#skF_8',F_64) != '#skF_9'
      | ~ r2_hidden(F_64,'#skF_7')
      | ~ r2_hidden(F_64,'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_272,plain,(
    ! [A_158,D_159] :
      ( k1_funct_1('#skF_8','#skF_4'(A_158,'#skF_7',k9_relat_1(A_158,'#skF_7'),D_159)) != '#skF_9'
      | ~ r2_hidden('#skF_4'(A_158,'#skF_7',k9_relat_1(A_158,'#skF_7'),D_159),'#skF_5')
      | ~ r2_hidden(D_159,k9_relat_1(A_158,'#skF_7'))
      | ~ v1_funct_1(A_158)
      | ~ v1_relat_1(A_158) ) ),
    inference(resolution,[status(thm)],[c_108,c_36])).

tff(c_342,plain,(
    ! [A_173,D_174] :
      ( k1_funct_1('#skF_8','#skF_4'(A_173,'#skF_7',k9_relat_1(A_173,'#skF_7'),D_174)) != '#skF_9'
      | ~ m1_subset_1(k1_relat_1(A_173),k1_zfmisc_1('#skF_5'))
      | ~ r2_hidden(D_174,k9_relat_1(A_173,'#skF_7'))
      | ~ v1_funct_1(A_173)
      | ~ v1_relat_1(A_173) ) ),
    inference(resolution,[status(thm)],[c_138,c_272])).

tff(c_345,plain,(
    ! [D_43] :
      ( D_43 != '#skF_9'
      | ~ m1_subset_1(k1_relat_1('#skF_8'),k1_zfmisc_1('#skF_5'))
      | ~ r2_hidden(D_43,k9_relat_1('#skF_8','#skF_7'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8')
      | ~ r2_hidden(D_43,k9_relat_1('#skF_8','#skF_7'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_342])).

tff(c_348,plain,(
    ~ r2_hidden('#skF_9',k9_relat_1('#skF_8','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_49,c_44,c_49,c_44,c_80,c_345])).

tff(c_81,plain,(
    ! [A_79,B_80,C_81,D_82] :
      ( k7_relset_1(A_79,B_80,C_81,D_82) = k9_relat_1(C_81,D_82)
      | ~ m1_subset_1(C_81,k1_zfmisc_1(k2_zfmisc_1(A_79,B_80))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_88,plain,(
    ! [D_82] : k7_relset_1('#skF_5','#skF_6','#skF_8',D_82) = k9_relat_1('#skF_8',D_82) ),
    inference(resolution,[status(thm)],[c_40,c_81])).

tff(c_38,plain,(
    r2_hidden('#skF_9',k7_relset_1('#skF_5','#skF_6','#skF_8','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_90,plain,(
    r2_hidden('#skF_9',k9_relat_1('#skF_8','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_38])).

tff(c_350,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_348,c_90])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:27:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.73/1.41  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.73/1.42  
% 2.73/1.42  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.73/1.42  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_9 > #skF_4 > #skF_8 > #skF_3
% 2.73/1.42  
% 2.73/1.42  %Foreground sorts:
% 2.73/1.42  
% 2.73/1.42  
% 2.73/1.42  %Background operators:
% 2.73/1.42  
% 2.73/1.42  
% 2.73/1.42  %Foreground operators:
% 2.73/1.42  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.73/1.42  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.73/1.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.73/1.42  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.73/1.42  tff('#skF_7', type, '#skF_7': $i).
% 2.73/1.42  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.73/1.42  tff('#skF_5', type, '#skF_5': $i).
% 2.73/1.42  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.73/1.42  tff('#skF_6', type, '#skF_6': $i).
% 2.73/1.42  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.73/1.42  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.73/1.42  tff('#skF_9', type, '#skF_9': $i).
% 2.73/1.42  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.73/1.42  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.73/1.42  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.73/1.42  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 2.73/1.42  tff('#skF_8', type, '#skF_8': $i).
% 2.73/1.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.73/1.42  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.73/1.42  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.73/1.42  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.73/1.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.73/1.42  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.73/1.42  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.73/1.42  
% 2.73/1.43  tff(f_84, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: ~(r2_hidden(E, k7_relset_1(A, B, D, C)) & (![F]: ~((r2_hidden(F, A) & r2_hidden(F, C)) & (E = k1_funct_1(D, F)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t115_funct_2)).
% 2.73/1.43  tff(f_53, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.73/1.43  tff(f_61, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.73/1.43  tff(f_57, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k1_relset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_relset_1)).
% 2.73/1.43  tff(f_49, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: ((C = k9_relat_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E]: ((r2_hidden(E, k1_relat_1(A)) & r2_hidden(E, B)) & (D = k1_funct_1(A, E)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_funct_1)).
% 2.73/1.43  tff(f_32, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 2.73/1.43  tff(f_65, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 2.73/1.43  tff(c_40, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.73/1.43  tff(c_45, plain, (![C_65, A_66, B_67]: (v1_relat_1(C_65) | ~m1_subset_1(C_65, k1_zfmisc_1(k2_zfmisc_1(A_66, B_67))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.73/1.43  tff(c_49, plain, (v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_40, c_45])).
% 2.73/1.43  tff(c_44, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.73/1.43  tff(c_56, plain, (![A_73, B_74, C_75]: (k1_relset_1(A_73, B_74, C_75)=k1_relat_1(C_75) | ~m1_subset_1(C_75, k1_zfmisc_1(k2_zfmisc_1(A_73, B_74))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.73/1.43  tff(c_60, plain, (k1_relset_1('#skF_5', '#skF_6', '#skF_8')=k1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_40, c_56])).
% 2.73/1.43  tff(c_65, plain, (![A_76, B_77, C_78]: (m1_subset_1(k1_relset_1(A_76, B_77, C_78), k1_zfmisc_1(A_76)) | ~m1_subset_1(C_78, k1_zfmisc_1(k2_zfmisc_1(A_76, B_77))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.73/1.43  tff(c_76, plain, (m1_subset_1(k1_relat_1('#skF_8'), k1_zfmisc_1('#skF_5')) | ~m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_60, c_65])).
% 2.73/1.43  tff(c_80, plain, (m1_subset_1(k1_relat_1('#skF_8'), k1_zfmisc_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_76])).
% 2.73/1.43  tff(c_6, plain, (![A_5, B_28, D_43]: (k1_funct_1(A_5, '#skF_4'(A_5, B_28, k9_relat_1(A_5, B_28), D_43))=D_43 | ~r2_hidden(D_43, k9_relat_1(A_5, B_28)) | ~v1_funct_1(A_5) | ~v1_relat_1(A_5))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.73/1.43  tff(c_135, plain, (![A_98, B_99, D_100]: (r2_hidden('#skF_4'(A_98, B_99, k9_relat_1(A_98, B_99), D_100), k1_relat_1(A_98)) | ~r2_hidden(D_100, k9_relat_1(A_98, B_99)) | ~v1_funct_1(A_98) | ~v1_relat_1(A_98))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.73/1.43  tff(c_2, plain, (![C_4, A_1, B_2]: (r2_hidden(C_4, A_1) | ~r2_hidden(C_4, B_2) | ~m1_subset_1(B_2, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.73/1.43  tff(c_138, plain, (![A_98, B_99, D_100, A_1]: (r2_hidden('#skF_4'(A_98, B_99, k9_relat_1(A_98, B_99), D_100), A_1) | ~m1_subset_1(k1_relat_1(A_98), k1_zfmisc_1(A_1)) | ~r2_hidden(D_100, k9_relat_1(A_98, B_99)) | ~v1_funct_1(A_98) | ~v1_relat_1(A_98))), inference(resolution, [status(thm)], [c_135, c_2])).
% 2.73/1.43  tff(c_108, plain, (![A_88, B_89, D_90]: (r2_hidden('#skF_4'(A_88, B_89, k9_relat_1(A_88, B_89), D_90), B_89) | ~r2_hidden(D_90, k9_relat_1(A_88, B_89)) | ~v1_funct_1(A_88) | ~v1_relat_1(A_88))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.73/1.43  tff(c_36, plain, (![F_64]: (k1_funct_1('#skF_8', F_64)!='#skF_9' | ~r2_hidden(F_64, '#skF_7') | ~r2_hidden(F_64, '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.73/1.43  tff(c_272, plain, (![A_158, D_159]: (k1_funct_1('#skF_8', '#skF_4'(A_158, '#skF_7', k9_relat_1(A_158, '#skF_7'), D_159))!='#skF_9' | ~r2_hidden('#skF_4'(A_158, '#skF_7', k9_relat_1(A_158, '#skF_7'), D_159), '#skF_5') | ~r2_hidden(D_159, k9_relat_1(A_158, '#skF_7')) | ~v1_funct_1(A_158) | ~v1_relat_1(A_158))), inference(resolution, [status(thm)], [c_108, c_36])).
% 2.73/1.43  tff(c_342, plain, (![A_173, D_174]: (k1_funct_1('#skF_8', '#skF_4'(A_173, '#skF_7', k9_relat_1(A_173, '#skF_7'), D_174))!='#skF_9' | ~m1_subset_1(k1_relat_1(A_173), k1_zfmisc_1('#skF_5')) | ~r2_hidden(D_174, k9_relat_1(A_173, '#skF_7')) | ~v1_funct_1(A_173) | ~v1_relat_1(A_173))), inference(resolution, [status(thm)], [c_138, c_272])).
% 2.73/1.43  tff(c_345, plain, (![D_43]: (D_43!='#skF_9' | ~m1_subset_1(k1_relat_1('#skF_8'), k1_zfmisc_1('#skF_5')) | ~r2_hidden(D_43, k9_relat_1('#skF_8', '#skF_7')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~r2_hidden(D_43, k9_relat_1('#skF_8', '#skF_7')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_6, c_342])).
% 2.73/1.43  tff(c_348, plain, (~r2_hidden('#skF_9', k9_relat_1('#skF_8', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_49, c_44, c_49, c_44, c_80, c_345])).
% 2.73/1.43  tff(c_81, plain, (![A_79, B_80, C_81, D_82]: (k7_relset_1(A_79, B_80, C_81, D_82)=k9_relat_1(C_81, D_82) | ~m1_subset_1(C_81, k1_zfmisc_1(k2_zfmisc_1(A_79, B_80))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.73/1.43  tff(c_88, plain, (![D_82]: (k7_relset_1('#skF_5', '#skF_6', '#skF_8', D_82)=k9_relat_1('#skF_8', D_82))), inference(resolution, [status(thm)], [c_40, c_81])).
% 2.73/1.43  tff(c_38, plain, (r2_hidden('#skF_9', k7_relset_1('#skF_5', '#skF_6', '#skF_8', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.73/1.43  tff(c_90, plain, (r2_hidden('#skF_9', k9_relat_1('#skF_8', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_38])).
% 2.73/1.43  tff(c_350, plain, $false, inference(negUnitSimplification, [status(thm)], [c_348, c_90])).
% 2.73/1.43  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.73/1.43  
% 2.73/1.43  Inference rules
% 2.73/1.43  ----------------------
% 2.73/1.43  #Ref     : 0
% 2.73/1.43  #Sup     : 65
% 2.73/1.43  #Fact    : 0
% 2.73/1.43  #Define  : 0
% 2.73/1.43  #Split   : 1
% 2.73/1.43  #Chain   : 0
% 2.73/1.43  #Close   : 0
% 2.73/1.43  
% 2.73/1.43  Ordering : KBO
% 2.73/1.43  
% 2.73/1.43  Simplification rules
% 2.73/1.43  ----------------------
% 2.73/1.43  #Subsume      : 3
% 2.73/1.43  #Demod        : 16
% 2.73/1.43  #Tautology    : 8
% 2.73/1.43  #SimpNegUnit  : 1
% 2.73/1.43  #BackRed      : 3
% 2.73/1.43  
% 2.73/1.43  #Partial instantiations: 0
% 2.73/1.43  #Strategies tried      : 1
% 2.73/1.43  
% 2.73/1.43  Timing (in seconds)
% 2.73/1.43  ----------------------
% 2.73/1.44  Preprocessing        : 0.34
% 2.73/1.44  Parsing              : 0.17
% 2.73/1.44  CNF conversion       : 0.03
% 2.73/1.44  Main loop            : 0.33
% 2.73/1.44  Inferencing          : 0.14
% 2.73/1.44  Reduction            : 0.07
% 2.73/1.44  Demodulation         : 0.05
% 2.73/1.44  BG Simplification    : 0.02
% 2.73/1.44  Subsumption          : 0.07
% 2.73/1.44  Abstraction          : 0.02
% 2.73/1.44  MUC search           : 0.00
% 2.73/1.44  Cooper               : 0.00
% 2.73/1.44  Total                : 0.69
% 2.73/1.44  Index Insertion      : 0.00
% 2.73/1.44  Index Deletion       : 0.00
% 2.73/1.44  Index Matching       : 0.00
% 2.73/1.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
