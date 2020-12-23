%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:00 EST 2020

% Result     : Theorem 2.04s
% Output     : CNFRefutation 2.12s
% Verified   : 
% Statistics : Number of formulae       :   62 (  89 expanded)
%              Number of leaves         :   31 (  46 expanded)
%              Depth                    :    6
%              Number of atoms          :   96 ( 192 expanded)
%              Number of equality atoms :   26 (  41 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_6 > #skF_3 > #skF_4

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_97,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( r2_hidden(C,A)
         => ( B = k1_xboole_0
            | r2_hidden(k1_funct_1(D,C),k2_relset_1(A,B,D)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_funct_2)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => r2_hidden(k1_funct_1(B,A),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_funct_1)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
     => ( ! [D] :
            ~ ( r2_hidden(D,B)
              & ! [E] : ~ r2_hidden(k4_tarski(D,E),C) )
      <=> k1_relset_1(B,A,C) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_relset_1)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
       => ( r2_hidden(A,k1_relat_1(C))
          & r2_hidden(B,k2_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_relat_1)).

tff(f_84,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( ( B = k1_xboole_0
           => A = k1_xboole_0 )
         => ( v1_funct_2(C,A,B)
          <=> A = k1_relset_1(A,B,C) ) )
        & ( B = k1_xboole_0
         => ( A = k1_xboole_0
            | ( v1_funct_2(C,A,B)
            <=> C = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_38,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_44,plain,(
    ! [B_32,A_33] :
      ( v1_relat_1(B_32)
      | ~ m1_subset_1(B_32,k1_zfmisc_1(A_33))
      | ~ v1_relat_1(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_47,plain,
    ( v1_relat_1('#skF_6')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_38,c_44])).

tff(c_50,plain,(
    v1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_47])).

tff(c_42,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_65,plain,(
    ! [B_46,A_47] :
      ( r2_hidden(k1_funct_1(B_46,A_47),k2_relat_1(B_46))
      | ~ r2_hidden(A_47,k1_relat_1(B_46))
      | ~ v1_funct_1(B_46)
      | ~ v1_relat_1(B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_53,plain,(
    ! [A_40,B_41,C_42] :
      ( k2_relset_1(A_40,B_41,C_42) = k2_relat_1(C_42)
      | ~ m1_subset_1(C_42,k1_zfmisc_1(k2_zfmisc_1(A_40,B_41))) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_57,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_38,c_53])).

tff(c_32,plain,(
    ~ r2_hidden(k1_funct_1('#skF_6','#skF_5'),k2_relset_1('#skF_3','#skF_4','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_58,plain,(
    ~ r2_hidden(k1_funct_1('#skF_6','#skF_5'),k2_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_32])).

tff(c_68,plain,
    ( ~ r2_hidden('#skF_5',k1_relat_1('#skF_6'))
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_65,c_58])).

tff(c_71,plain,(
    ~ r2_hidden('#skF_5',k1_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_42,c_68])).

tff(c_81,plain,(
    ! [A_55,B_56,C_57] :
      ( r2_hidden('#skF_1'(A_55,B_56,C_57),B_56)
      | k1_relset_1(B_56,A_55,C_57) = B_56
      | ~ m1_subset_1(C_57,k1_zfmisc_1(k2_zfmisc_1(B_56,A_55))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_84,plain,
    ( r2_hidden('#skF_1'('#skF_4','#skF_3','#skF_6'),'#skF_3')
    | k1_relset_1('#skF_3','#skF_4','#skF_6') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_38,c_81])).

tff(c_85,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_6') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_84])).

tff(c_36,plain,(
    r2_hidden('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_99,plain,(
    ! [D_65,A_66,B_67,C_68] :
      ( r2_hidden(k4_tarski(D_65,'#skF_2'(A_66,B_67,C_68,D_65)),C_68)
      | ~ r2_hidden(D_65,B_67)
      | k1_relset_1(B_67,A_66,C_68) != B_67
      | ~ m1_subset_1(C_68,k1_zfmisc_1(k2_zfmisc_1(B_67,A_66))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_8,plain,(
    ! [A_6,C_8,B_7] :
      ( r2_hidden(A_6,k1_relat_1(C_8))
      | ~ r2_hidden(k4_tarski(A_6,B_7),C_8)
      | ~ v1_relat_1(C_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_113,plain,(
    ! [D_69,C_70,B_71,A_72] :
      ( r2_hidden(D_69,k1_relat_1(C_70))
      | ~ v1_relat_1(C_70)
      | ~ r2_hidden(D_69,B_71)
      | k1_relset_1(B_71,A_72,C_70) != B_71
      | ~ m1_subset_1(C_70,k1_zfmisc_1(k2_zfmisc_1(B_71,A_72))) ) ),
    inference(resolution,[status(thm)],[c_99,c_8])).

tff(c_123,plain,(
    ! [C_73,A_74] :
      ( r2_hidden('#skF_5',k1_relat_1(C_73))
      | ~ v1_relat_1(C_73)
      | k1_relset_1('#skF_3',A_74,C_73) != '#skF_3'
      | ~ m1_subset_1(C_73,k1_zfmisc_1(k2_zfmisc_1('#skF_3',A_74))) ) ),
    inference(resolution,[status(thm)],[c_36,c_113])).

tff(c_126,plain,
    ( r2_hidden('#skF_5',k1_relat_1('#skF_6'))
    | ~ v1_relat_1('#skF_6')
    | k1_relset_1('#skF_3','#skF_4','#skF_6') != '#skF_3' ),
    inference(resolution,[status(thm)],[c_38,c_123])).

tff(c_129,plain,(
    r2_hidden('#skF_5',k1_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_50,c_126])).

tff(c_131,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_71,c_129])).

tff(c_133,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_6') != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_34,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_40,plain,(
    v1_funct_2('#skF_6','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_134,plain,(
    ! [B_75,A_76,C_77] :
      ( k1_xboole_0 = B_75
      | k1_relset_1(A_76,B_75,C_77) = A_76
      | ~ v1_funct_2(C_77,A_76,B_75)
      | ~ m1_subset_1(C_77,k1_zfmisc_1(k2_zfmisc_1(A_76,B_75))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_137,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_6') = '#skF_3'
    | ~ v1_funct_2('#skF_6','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_134])).

tff(c_140,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_6') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_137])).

tff(c_142,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_133,c_34,c_140])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:37:11 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.04/1.20  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.12/1.21  
% 2.12/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.12/1.21  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_6 > #skF_3 > #skF_4
% 2.12/1.21  
% 2.12/1.21  %Foreground sorts:
% 2.12/1.21  
% 2.12/1.21  
% 2.12/1.21  %Background operators:
% 2.12/1.21  
% 2.12/1.21  
% 2.12/1.21  %Foreground operators:
% 2.12/1.21  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.12/1.21  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.12/1.21  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.12/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.12/1.21  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.12/1.21  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.12/1.21  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.12/1.21  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.12/1.21  tff('#skF_5', type, '#skF_5': $i).
% 2.12/1.21  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.12/1.21  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.12/1.21  tff('#skF_6', type, '#skF_6': $i).
% 2.12/1.21  tff('#skF_3', type, '#skF_3': $i).
% 2.12/1.21  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.12/1.21  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.12/1.21  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.12/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.12/1.21  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.12/1.21  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.12/1.21  tff('#skF_4', type, '#skF_4': $i).
% 2.12/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.12/1.21  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.12/1.21  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.12/1.21  
% 2.12/1.22  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.12/1.22  tff(f_97, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), k2_relset_1(A, B, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_funct_2)).
% 2.12/1.22  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.12/1.22  tff(f_50, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, A), k2_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_funct_1)).
% 2.12/1.22  tff(f_54, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.12/1.22  tff(f_66, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => ((![D]: ~(r2_hidden(D, B) & (![E]: ~r2_hidden(k4_tarski(D, E), C)))) <=> (k1_relset_1(B, A, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_relset_1)).
% 2.12/1.22  tff(f_42, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) => (r2_hidden(A, k1_relat_1(C)) & r2_hidden(B, k2_relat_1(C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_relat_1)).
% 2.12/1.22  tff(f_84, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 2.12/1.22  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.12/1.22  tff(c_38, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.12/1.22  tff(c_44, plain, (![B_32, A_33]: (v1_relat_1(B_32) | ~m1_subset_1(B_32, k1_zfmisc_1(A_33)) | ~v1_relat_1(A_33))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.12/1.22  tff(c_47, plain, (v1_relat_1('#skF_6') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_38, c_44])).
% 2.12/1.22  tff(c_50, plain, (v1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_47])).
% 2.12/1.22  tff(c_42, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.12/1.22  tff(c_65, plain, (![B_46, A_47]: (r2_hidden(k1_funct_1(B_46, A_47), k2_relat_1(B_46)) | ~r2_hidden(A_47, k1_relat_1(B_46)) | ~v1_funct_1(B_46) | ~v1_relat_1(B_46))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.12/1.22  tff(c_53, plain, (![A_40, B_41, C_42]: (k2_relset_1(A_40, B_41, C_42)=k2_relat_1(C_42) | ~m1_subset_1(C_42, k1_zfmisc_1(k2_zfmisc_1(A_40, B_41))))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.12/1.22  tff(c_57, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_6')=k2_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_38, c_53])).
% 2.12/1.22  tff(c_32, plain, (~r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k2_relset_1('#skF_3', '#skF_4', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.12/1.22  tff(c_58, plain, (~r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k2_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_57, c_32])).
% 2.12/1.22  tff(c_68, plain, (~r2_hidden('#skF_5', k1_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_65, c_58])).
% 2.12/1.22  tff(c_71, plain, (~r2_hidden('#skF_5', k1_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_42, c_68])).
% 2.12/1.22  tff(c_81, plain, (![A_55, B_56, C_57]: (r2_hidden('#skF_1'(A_55, B_56, C_57), B_56) | k1_relset_1(B_56, A_55, C_57)=B_56 | ~m1_subset_1(C_57, k1_zfmisc_1(k2_zfmisc_1(B_56, A_55))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.12/1.22  tff(c_84, plain, (r2_hidden('#skF_1'('#skF_4', '#skF_3', '#skF_6'), '#skF_3') | k1_relset_1('#skF_3', '#skF_4', '#skF_6')='#skF_3'), inference(resolution, [status(thm)], [c_38, c_81])).
% 2.12/1.22  tff(c_85, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_6')='#skF_3'), inference(splitLeft, [status(thm)], [c_84])).
% 2.12/1.22  tff(c_36, plain, (r2_hidden('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.12/1.22  tff(c_99, plain, (![D_65, A_66, B_67, C_68]: (r2_hidden(k4_tarski(D_65, '#skF_2'(A_66, B_67, C_68, D_65)), C_68) | ~r2_hidden(D_65, B_67) | k1_relset_1(B_67, A_66, C_68)!=B_67 | ~m1_subset_1(C_68, k1_zfmisc_1(k2_zfmisc_1(B_67, A_66))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.12/1.22  tff(c_8, plain, (![A_6, C_8, B_7]: (r2_hidden(A_6, k1_relat_1(C_8)) | ~r2_hidden(k4_tarski(A_6, B_7), C_8) | ~v1_relat_1(C_8))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.12/1.22  tff(c_113, plain, (![D_69, C_70, B_71, A_72]: (r2_hidden(D_69, k1_relat_1(C_70)) | ~v1_relat_1(C_70) | ~r2_hidden(D_69, B_71) | k1_relset_1(B_71, A_72, C_70)!=B_71 | ~m1_subset_1(C_70, k1_zfmisc_1(k2_zfmisc_1(B_71, A_72))))), inference(resolution, [status(thm)], [c_99, c_8])).
% 2.12/1.22  tff(c_123, plain, (![C_73, A_74]: (r2_hidden('#skF_5', k1_relat_1(C_73)) | ~v1_relat_1(C_73) | k1_relset_1('#skF_3', A_74, C_73)!='#skF_3' | ~m1_subset_1(C_73, k1_zfmisc_1(k2_zfmisc_1('#skF_3', A_74))))), inference(resolution, [status(thm)], [c_36, c_113])).
% 2.12/1.22  tff(c_126, plain, (r2_hidden('#skF_5', k1_relat_1('#skF_6')) | ~v1_relat_1('#skF_6') | k1_relset_1('#skF_3', '#skF_4', '#skF_6')!='#skF_3'), inference(resolution, [status(thm)], [c_38, c_123])).
% 2.12/1.22  tff(c_129, plain, (r2_hidden('#skF_5', k1_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_85, c_50, c_126])).
% 2.12/1.22  tff(c_131, plain, $false, inference(negUnitSimplification, [status(thm)], [c_71, c_129])).
% 2.12/1.22  tff(c_133, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_6')!='#skF_3'), inference(splitRight, [status(thm)], [c_84])).
% 2.12/1.22  tff(c_34, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.12/1.22  tff(c_40, plain, (v1_funct_2('#skF_6', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.12/1.22  tff(c_134, plain, (![B_75, A_76, C_77]: (k1_xboole_0=B_75 | k1_relset_1(A_76, B_75, C_77)=A_76 | ~v1_funct_2(C_77, A_76, B_75) | ~m1_subset_1(C_77, k1_zfmisc_1(k2_zfmisc_1(A_76, B_75))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.12/1.22  tff(c_137, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_6')='#skF_3' | ~v1_funct_2('#skF_6', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_38, c_134])).
% 2.12/1.22  tff(c_140, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_6')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_137])).
% 2.12/1.22  tff(c_142, plain, $false, inference(negUnitSimplification, [status(thm)], [c_133, c_34, c_140])).
% 2.12/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.12/1.22  
% 2.12/1.22  Inference rules
% 2.12/1.22  ----------------------
% 2.12/1.22  #Ref     : 0
% 2.12/1.22  #Sup     : 18
% 2.12/1.22  #Fact    : 0
% 2.12/1.22  #Define  : 0
% 2.12/1.22  #Split   : 1
% 2.12/1.22  #Chain   : 0
% 2.12/1.22  #Close   : 0
% 2.12/1.22  
% 2.12/1.22  Ordering : KBO
% 2.12/1.22  
% 2.12/1.22  Simplification rules
% 2.12/1.22  ----------------------
% 2.12/1.22  #Subsume      : 0
% 2.12/1.22  #Demod        : 10
% 2.12/1.22  #Tautology    : 6
% 2.12/1.22  #SimpNegUnit  : 4
% 2.12/1.22  #BackRed      : 1
% 2.12/1.22  
% 2.12/1.22  #Partial instantiations: 0
% 2.12/1.22  #Strategies tried      : 1
% 2.12/1.22  
% 2.12/1.22  Timing (in seconds)
% 2.12/1.22  ----------------------
% 2.12/1.23  Preprocessing        : 0.31
% 2.12/1.23  Parsing              : 0.16
% 2.12/1.23  CNF conversion       : 0.02
% 2.12/1.23  Main loop            : 0.16
% 2.12/1.23  Inferencing          : 0.06
% 2.12/1.23  Reduction            : 0.05
% 2.12/1.23  Demodulation         : 0.04
% 2.12/1.23  BG Simplification    : 0.01
% 2.12/1.23  Subsumption          : 0.03
% 2.12/1.23  Abstraction          : 0.01
% 2.12/1.23  MUC search           : 0.00
% 2.12/1.23  Cooper               : 0.00
% 2.12/1.23  Total                : 0.50
% 2.12/1.23  Index Insertion      : 0.00
% 2.12/1.23  Index Deletion       : 0.00
% 2.12/1.23  Index Matching       : 0.00
% 2.12/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
