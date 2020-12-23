%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:49 EST 2020

% Result     : Theorem 2.23s
% Output     : CNFRefutation 2.53s
% Verified   : 
% Statistics : Number of formulae       :   64 (  86 expanded)
%              Number of leaves         :   33 (  46 expanded)
%              Depth                    :    6
%              Number of atoms          :  114 ( 207 expanded)
%              Number of equality atoms :   32 (  54 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k6_relset_1 > k1_relset_1 > k8_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

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

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k6_relset_1,type,(
    k6_relset_1: ( $i * $i * $i * $i ) > $i )).

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

tff(f_111,negated_conjecture,(
    ~ ! [A,B,C,D,E] :
        ( ( v1_funct_1(E)
          & v1_funct_2(E,A,B)
          & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ( r2_hidden(C,A)
            & r2_hidden(k1_funct_1(E,C),D) )
         => ( B = k1_xboole_0
            | k1_funct_1(k6_relset_1(A,B,D,E),C) = k1_funct_1(E,C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_funct_2)).

tff(f_66,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k6_relset_1(A,B,C,D) = k8_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_relset_1)).

tff(f_34,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(A,k1_relat_1(k8_relat_1(B,C)))
      <=> ( r2_hidden(A,k1_relat_1(C))
          & r2_hidden(k1_funct_1(C,A),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_funct_1)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(A,k1_relat_1(k8_relat_1(B,C)))
       => k1_funct_1(k8_relat_1(B,C),A) = k1_funct_1(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_funct_1)).

tff(f_96,axiom,(
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

tff(f_78,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
     => ( ! [D] :
            ~ ( r2_hidden(D,B)
              & ! [E] : ~ r2_hidden(k4_tarski(D,E),C) )
      <=> k1_relset_1(B,A,C) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_relset_1)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

tff(c_48,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_64,plain,(
    ! [A_46,B_47,C_48,D_49] :
      ( k6_relset_1(A_46,B_47,C_48,D_49) = k8_relat_1(C_48,D_49)
      | ~ m1_subset_1(D_49,k1_zfmisc_1(k2_zfmisc_1(A_46,B_47))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_67,plain,(
    ! [C_48] : k6_relset_1('#skF_3','#skF_4',C_48,'#skF_7') = k8_relat_1(C_48,'#skF_7') ),
    inference(resolution,[status(thm)],[c_48,c_64])).

tff(c_40,plain,(
    k1_funct_1(k6_relset_1('#skF_3','#skF_4','#skF_6','#skF_7'),'#skF_5') != k1_funct_1('#skF_7','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_68,plain,(
    k1_funct_1(k8_relat_1('#skF_6','#skF_7'),'#skF_5') != k1_funct_1('#skF_7','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_40])).

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_54,plain,(
    ! [B_37,A_38] :
      ( v1_relat_1(B_37)
      | ~ m1_subset_1(B_37,k1_zfmisc_1(A_38))
      | ~ v1_relat_1(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_57,plain,
    ( v1_relat_1('#skF_7')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_48,c_54])).

tff(c_60,plain,(
    v1_relat_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_57])).

tff(c_52,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_44,plain,(
    r2_hidden(k1_funct_1('#skF_7','#skF_5'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_140,plain,(
    ! [A_81,B_82,C_83] :
      ( r2_hidden(A_81,k1_relat_1(k8_relat_1(B_82,C_83)))
      | ~ r2_hidden(k1_funct_1(C_83,A_81),B_82)
      | ~ r2_hidden(A_81,k1_relat_1(C_83))
      | ~ v1_funct_1(C_83)
      | ~ v1_relat_1(C_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_12,plain,(
    ! [B_10,C_11,A_9] :
      ( k1_funct_1(k8_relat_1(B_10,C_11),A_9) = k1_funct_1(C_11,A_9)
      | ~ r2_hidden(A_9,k1_relat_1(k8_relat_1(B_10,C_11)))
      | ~ v1_funct_1(C_11)
      | ~ v1_relat_1(C_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_168,plain,(
    ! [B_84,C_85,A_86] :
      ( k1_funct_1(k8_relat_1(B_84,C_85),A_86) = k1_funct_1(C_85,A_86)
      | ~ r2_hidden(k1_funct_1(C_85,A_86),B_84)
      | ~ r2_hidden(A_86,k1_relat_1(C_85))
      | ~ v1_funct_1(C_85)
      | ~ v1_relat_1(C_85) ) ),
    inference(resolution,[status(thm)],[c_140,c_12])).

tff(c_175,plain,
    ( k1_funct_1(k8_relat_1('#skF_6','#skF_7'),'#skF_5') = k1_funct_1('#skF_7','#skF_5')
    | ~ r2_hidden('#skF_5',k1_relat_1('#skF_7'))
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_44,c_168])).

tff(c_179,plain,
    ( k1_funct_1(k8_relat_1('#skF_6','#skF_7'),'#skF_5') = k1_funct_1('#skF_7','#skF_5')
    | ~ r2_hidden('#skF_5',k1_relat_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_52,c_175])).

tff(c_180,plain,(
    ~ r2_hidden('#skF_5',k1_relat_1('#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_179])).

tff(c_42,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_50,plain,(
    v1_funct_2('#skF_7','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_115,plain,(
    ! [B_71,A_72,C_73] :
      ( k1_xboole_0 = B_71
      | k1_relset_1(A_72,B_71,C_73) = A_72
      | ~ v1_funct_2(C_73,A_72,B_71)
      | ~ m1_subset_1(C_73,k1_zfmisc_1(k2_zfmisc_1(A_72,B_71))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_118,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_7') = '#skF_3'
    | ~ v1_funct_2('#skF_7','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_115])).

tff(c_121,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_7') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_118])).

tff(c_122,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_7') = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_121])).

tff(c_46,plain,(
    r2_hidden('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_187,plain,(
    ! [D_90,A_91,B_92,C_93] :
      ( r2_hidden(k4_tarski(D_90,'#skF_2'(A_91,B_92,C_93,D_90)),C_93)
      | ~ r2_hidden(D_90,B_92)
      | k1_relset_1(B_92,A_91,C_93) != B_92
      | ~ m1_subset_1(C_93,k1_zfmisc_1(k2_zfmisc_1(B_92,A_91))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_18,plain,(
    ! [A_12,C_14,B_13] :
      ( r2_hidden(A_12,k1_relat_1(C_14))
      | ~ r2_hidden(k4_tarski(A_12,B_13),C_14)
      | ~ v1_funct_1(C_14)
      | ~ v1_relat_1(C_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_216,plain,(
    ! [D_94,C_95,B_96,A_97] :
      ( r2_hidden(D_94,k1_relat_1(C_95))
      | ~ v1_funct_1(C_95)
      | ~ v1_relat_1(C_95)
      | ~ r2_hidden(D_94,B_96)
      | k1_relset_1(B_96,A_97,C_95) != B_96
      | ~ m1_subset_1(C_95,k1_zfmisc_1(k2_zfmisc_1(B_96,A_97))) ) ),
    inference(resolution,[status(thm)],[c_187,c_18])).

tff(c_232,plain,(
    ! [C_98,A_99] :
      ( r2_hidden('#skF_5',k1_relat_1(C_98))
      | ~ v1_funct_1(C_98)
      | ~ v1_relat_1(C_98)
      | k1_relset_1('#skF_3',A_99,C_98) != '#skF_3'
      | ~ m1_subset_1(C_98,k1_zfmisc_1(k2_zfmisc_1('#skF_3',A_99))) ) ),
    inference(resolution,[status(thm)],[c_46,c_216])).

tff(c_235,plain,
    ( r2_hidden('#skF_5',k1_relat_1('#skF_7'))
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7')
    | k1_relset_1('#skF_3','#skF_4','#skF_7') != '#skF_3' ),
    inference(resolution,[status(thm)],[c_48,c_232])).

tff(c_238,plain,(
    r2_hidden('#skF_5',k1_relat_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_60,c_52,c_235])).

tff(c_240,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_180,c_238])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n018.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:32:41 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.23/1.36  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.23/1.37  
% 2.23/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.23/1.37  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k6_relset_1 > k1_relset_1 > k8_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_3 > #skF_4
% 2.23/1.37  
% 2.23/1.37  %Foreground sorts:
% 2.23/1.37  
% 2.23/1.37  
% 2.23/1.37  %Background operators:
% 2.23/1.37  
% 2.23/1.37  
% 2.23/1.37  %Foreground operators:
% 2.23/1.37  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 2.23/1.37  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.23/1.37  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.23/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.23/1.37  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.23/1.37  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.23/1.37  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.23/1.37  tff('#skF_7', type, '#skF_7': $i).
% 2.23/1.37  tff(k6_relset_1, type, k6_relset_1: ($i * $i * $i * $i) > $i).
% 2.23/1.37  tff('#skF_5', type, '#skF_5': $i).
% 2.23/1.37  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.23/1.37  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.23/1.37  tff('#skF_6', type, '#skF_6': $i).
% 2.23/1.37  tff('#skF_3', type, '#skF_3': $i).
% 2.23/1.37  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.23/1.37  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.23/1.37  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.23/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.23/1.37  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.23/1.37  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.23/1.37  tff('#skF_4', type, '#skF_4': $i).
% 2.23/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.23/1.37  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.23/1.37  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.23/1.37  
% 2.53/1.38  tff(f_111, negated_conjecture, ~(![A, B, C, D, E]: (((v1_funct_1(E) & v1_funct_2(E, A, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((r2_hidden(C, A) & r2_hidden(k1_funct_1(E, C), D)) => ((B = k1_xboole_0) | (k1_funct_1(k6_relset_1(A, B, D, E), C) = k1_funct_1(E, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_funct_2)).
% 2.53/1.38  tff(f_66, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k6_relset_1(A, B, C, D) = k8_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_relset_1)).
% 2.53/1.38  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.53/1.38  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.53/1.38  tff(f_44, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(k8_relat_1(B, C))) <=> (r2_hidden(A, k1_relat_1(C)) & r2_hidden(k1_funct_1(C, A), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_funct_1)).
% 2.53/1.39  tff(f_52, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(k8_relat_1(B, C))) => (k1_funct_1(k8_relat_1(B, C), A) = k1_funct_1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_funct_1)).
% 2.53/1.39  tff(f_96, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 2.53/1.39  tff(f_78, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => ((![D]: ~(r2_hidden(D, B) & (![E]: ~r2_hidden(k4_tarski(D, E), C)))) <=> (k1_relset_1(B, A, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_relset_1)).
% 2.53/1.39  tff(f_62, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_funct_1)).
% 2.53/1.39  tff(c_48, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.53/1.39  tff(c_64, plain, (![A_46, B_47, C_48, D_49]: (k6_relset_1(A_46, B_47, C_48, D_49)=k8_relat_1(C_48, D_49) | ~m1_subset_1(D_49, k1_zfmisc_1(k2_zfmisc_1(A_46, B_47))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.53/1.39  tff(c_67, plain, (![C_48]: (k6_relset_1('#skF_3', '#skF_4', C_48, '#skF_7')=k8_relat_1(C_48, '#skF_7'))), inference(resolution, [status(thm)], [c_48, c_64])).
% 2.53/1.39  tff(c_40, plain, (k1_funct_1(k6_relset_1('#skF_3', '#skF_4', '#skF_6', '#skF_7'), '#skF_5')!=k1_funct_1('#skF_7', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.53/1.39  tff(c_68, plain, (k1_funct_1(k8_relat_1('#skF_6', '#skF_7'), '#skF_5')!=k1_funct_1('#skF_7', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_67, c_40])).
% 2.53/1.39  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.53/1.39  tff(c_54, plain, (![B_37, A_38]: (v1_relat_1(B_37) | ~m1_subset_1(B_37, k1_zfmisc_1(A_38)) | ~v1_relat_1(A_38))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.53/1.39  tff(c_57, plain, (v1_relat_1('#skF_7') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_48, c_54])).
% 2.53/1.39  tff(c_60, plain, (v1_relat_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_57])).
% 2.53/1.39  tff(c_52, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.53/1.39  tff(c_44, plain, (r2_hidden(k1_funct_1('#skF_7', '#skF_5'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.53/1.39  tff(c_140, plain, (![A_81, B_82, C_83]: (r2_hidden(A_81, k1_relat_1(k8_relat_1(B_82, C_83))) | ~r2_hidden(k1_funct_1(C_83, A_81), B_82) | ~r2_hidden(A_81, k1_relat_1(C_83)) | ~v1_funct_1(C_83) | ~v1_relat_1(C_83))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.53/1.39  tff(c_12, plain, (![B_10, C_11, A_9]: (k1_funct_1(k8_relat_1(B_10, C_11), A_9)=k1_funct_1(C_11, A_9) | ~r2_hidden(A_9, k1_relat_1(k8_relat_1(B_10, C_11))) | ~v1_funct_1(C_11) | ~v1_relat_1(C_11))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.53/1.39  tff(c_168, plain, (![B_84, C_85, A_86]: (k1_funct_1(k8_relat_1(B_84, C_85), A_86)=k1_funct_1(C_85, A_86) | ~r2_hidden(k1_funct_1(C_85, A_86), B_84) | ~r2_hidden(A_86, k1_relat_1(C_85)) | ~v1_funct_1(C_85) | ~v1_relat_1(C_85))), inference(resolution, [status(thm)], [c_140, c_12])).
% 2.53/1.39  tff(c_175, plain, (k1_funct_1(k8_relat_1('#skF_6', '#skF_7'), '#skF_5')=k1_funct_1('#skF_7', '#skF_5') | ~r2_hidden('#skF_5', k1_relat_1('#skF_7')) | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_44, c_168])).
% 2.53/1.39  tff(c_179, plain, (k1_funct_1(k8_relat_1('#skF_6', '#skF_7'), '#skF_5')=k1_funct_1('#skF_7', '#skF_5') | ~r2_hidden('#skF_5', k1_relat_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_52, c_175])).
% 2.53/1.39  tff(c_180, plain, (~r2_hidden('#skF_5', k1_relat_1('#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_68, c_179])).
% 2.53/1.39  tff(c_42, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.53/1.39  tff(c_50, plain, (v1_funct_2('#skF_7', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.53/1.39  tff(c_115, plain, (![B_71, A_72, C_73]: (k1_xboole_0=B_71 | k1_relset_1(A_72, B_71, C_73)=A_72 | ~v1_funct_2(C_73, A_72, B_71) | ~m1_subset_1(C_73, k1_zfmisc_1(k2_zfmisc_1(A_72, B_71))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.53/1.39  tff(c_118, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_7')='#skF_3' | ~v1_funct_2('#skF_7', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_48, c_115])).
% 2.53/1.39  tff(c_121, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_7')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_50, c_118])).
% 2.53/1.39  tff(c_122, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_7')='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_42, c_121])).
% 2.53/1.39  tff(c_46, plain, (r2_hidden('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.53/1.39  tff(c_187, plain, (![D_90, A_91, B_92, C_93]: (r2_hidden(k4_tarski(D_90, '#skF_2'(A_91, B_92, C_93, D_90)), C_93) | ~r2_hidden(D_90, B_92) | k1_relset_1(B_92, A_91, C_93)!=B_92 | ~m1_subset_1(C_93, k1_zfmisc_1(k2_zfmisc_1(B_92, A_91))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.53/1.39  tff(c_18, plain, (![A_12, C_14, B_13]: (r2_hidden(A_12, k1_relat_1(C_14)) | ~r2_hidden(k4_tarski(A_12, B_13), C_14) | ~v1_funct_1(C_14) | ~v1_relat_1(C_14))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.53/1.39  tff(c_216, plain, (![D_94, C_95, B_96, A_97]: (r2_hidden(D_94, k1_relat_1(C_95)) | ~v1_funct_1(C_95) | ~v1_relat_1(C_95) | ~r2_hidden(D_94, B_96) | k1_relset_1(B_96, A_97, C_95)!=B_96 | ~m1_subset_1(C_95, k1_zfmisc_1(k2_zfmisc_1(B_96, A_97))))), inference(resolution, [status(thm)], [c_187, c_18])).
% 2.53/1.39  tff(c_232, plain, (![C_98, A_99]: (r2_hidden('#skF_5', k1_relat_1(C_98)) | ~v1_funct_1(C_98) | ~v1_relat_1(C_98) | k1_relset_1('#skF_3', A_99, C_98)!='#skF_3' | ~m1_subset_1(C_98, k1_zfmisc_1(k2_zfmisc_1('#skF_3', A_99))))), inference(resolution, [status(thm)], [c_46, c_216])).
% 2.53/1.39  tff(c_235, plain, (r2_hidden('#skF_5', k1_relat_1('#skF_7')) | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7') | k1_relset_1('#skF_3', '#skF_4', '#skF_7')!='#skF_3'), inference(resolution, [status(thm)], [c_48, c_232])).
% 2.53/1.39  tff(c_238, plain, (r2_hidden('#skF_5', k1_relat_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_122, c_60, c_52, c_235])).
% 2.53/1.39  tff(c_240, plain, $false, inference(negUnitSimplification, [status(thm)], [c_180, c_238])).
% 2.53/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.53/1.39  
% 2.53/1.39  Inference rules
% 2.53/1.39  ----------------------
% 2.53/1.39  #Ref     : 0
% 2.53/1.39  #Sup     : 36
% 2.53/1.39  #Fact    : 0
% 2.53/1.39  #Define  : 0
% 2.53/1.39  #Split   : 1
% 2.53/1.39  #Chain   : 0
% 2.53/1.39  #Close   : 0
% 2.53/1.39  
% 2.53/1.39  Ordering : KBO
% 2.53/1.39  
% 2.53/1.39  Simplification rules
% 2.53/1.39  ----------------------
% 2.53/1.39  #Subsume      : 0
% 2.53/1.39  #Demod        : 10
% 2.53/1.39  #Tautology    : 10
% 2.53/1.39  #SimpNegUnit  : 4
% 2.53/1.39  #BackRed      : 1
% 2.53/1.39  
% 2.53/1.39  #Partial instantiations: 0
% 2.53/1.39  #Strategies tried      : 1
% 2.53/1.39  
% 2.53/1.39  Timing (in seconds)
% 2.53/1.39  ----------------------
% 2.53/1.39  Preprocessing        : 0.35
% 2.53/1.39  Parsing              : 0.19
% 2.53/1.39  CNF conversion       : 0.02
% 2.53/1.39  Main loop            : 0.21
% 2.53/1.39  Inferencing          : 0.07
% 2.53/1.39  Reduction            : 0.06
% 2.53/1.39  Demodulation         : 0.04
% 2.53/1.39  BG Simplification    : 0.02
% 2.53/1.39  Subsumption          : 0.04
% 2.53/1.39  Abstraction          : 0.01
% 2.53/1.39  MUC search           : 0.00
% 2.53/1.39  Cooper               : 0.00
% 2.53/1.39  Total                : 0.59
% 2.53/1.39  Index Insertion      : 0.00
% 2.53/1.39  Index Deletion       : 0.00
% 2.53/1.39  Index Matching       : 0.00
% 2.53/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
