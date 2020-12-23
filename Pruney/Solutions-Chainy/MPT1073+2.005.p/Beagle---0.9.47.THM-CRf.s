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
% DateTime   : Thu Dec  3 10:17:58 EST 2020

% Result     : Theorem 3.17s
% Output     : CNFRefutation 3.38s
% Verified   : 
% Statistics : Number of formulae       :   63 (  83 expanded)
%              Number of leaves         :   35 (  46 expanded)
%              Depth                    :    9
%              Number of atoms          :  108 ( 173 expanded)
%              Number of equality atoms :   13 (  22 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_97,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,B,C)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
       => ~ ( r2_hidden(A,k2_relset_1(B,C,D))
            & ! [E] :
                ( m1_subset_1(E,B)
               => A != k1_funct_1(D,E) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t190_funct_2)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_57,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_36,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(c_42,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_67,plain,(
    ! [C_37,A_38,B_39] :
      ( v1_relat_1(C_37)
      | ~ m1_subset_1(C_37,k1_zfmisc_1(k2_zfmisc_1(A_38,B_39))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_71,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_42,c_67])).

tff(c_46,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_102,plain,(
    ! [C_50,A_51,B_52] :
      ( v4_relat_1(C_50,A_51)
      | ~ m1_subset_1(C_50,k1_zfmisc_1(k2_zfmisc_1(A_51,B_52))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_111,plain,(
    v4_relat_1('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_102])).

tff(c_22,plain,(
    ! [A_16] :
      ( k9_relat_1(A_16,k1_relat_1(A_16)) = k2_relat_1(A_16)
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_301,plain,(
    ! [A_118,B_119,C_120] :
      ( r2_hidden(k4_tarski('#skF_2'(A_118,B_119,C_120),A_118),C_120)
      | ~ r2_hidden(A_118,k9_relat_1(C_120,B_119))
      | ~ v1_relat_1(C_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_26,plain,(
    ! [C_19,A_17,B_18] :
      ( k1_funct_1(C_19,A_17) = B_18
      | ~ r2_hidden(k4_tarski(A_17,B_18),C_19)
      | ~ v1_funct_1(C_19)
      | ~ v1_relat_1(C_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_386,plain,(
    ! [C_130,A_131,B_132] :
      ( k1_funct_1(C_130,'#skF_2'(A_131,B_132,C_130)) = A_131
      | ~ v1_funct_1(C_130)
      | ~ r2_hidden(A_131,k9_relat_1(C_130,B_132))
      | ~ v1_relat_1(C_130) ) ),
    inference(resolution,[status(thm)],[c_301,c_26])).

tff(c_406,plain,(
    ! [A_16,A_131] :
      ( k1_funct_1(A_16,'#skF_2'(A_131,k1_relat_1(A_16),A_16)) = A_131
      | ~ v1_funct_1(A_16)
      | ~ r2_hidden(A_131,k2_relat_1(A_16))
      | ~ v1_relat_1(A_16)
      | ~ v1_relat_1(A_16) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_386])).

tff(c_12,plain,(
    ! [B_9,A_8] :
      ( r1_tarski(k1_relat_1(B_9),A_8)
      | ~ v4_relat_1(B_9,A_8)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_244,plain,(
    ! [A_92,B_93,C_94] :
      ( r2_hidden('#skF_2'(A_92,B_93,C_94),k1_relat_1(C_94))
      | ~ r2_hidden(A_92,k9_relat_1(C_94,B_93))
      | ~ v1_relat_1(C_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_466,plain,(
    ! [A_143,B_144,C_145,B_146] :
      ( r2_hidden('#skF_2'(A_143,B_144,C_145),B_146)
      | ~ r1_tarski(k1_relat_1(C_145),B_146)
      | ~ r2_hidden(A_143,k9_relat_1(C_145,B_144))
      | ~ v1_relat_1(C_145) ) ),
    inference(resolution,[status(thm)],[c_244,c_2])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(A_6,B_7)
      | ~ r2_hidden(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_554,plain,(
    ! [A_154,B_155,C_156,B_157] :
      ( m1_subset_1('#skF_2'(A_154,B_155,C_156),B_157)
      | ~ r1_tarski(k1_relat_1(C_156),B_157)
      | ~ r2_hidden(A_154,k9_relat_1(C_156,B_155))
      | ~ v1_relat_1(C_156) ) ),
    inference(resolution,[status(thm)],[c_466,c_8])).

tff(c_562,plain,(
    ! [A_158,B_159,B_160,A_161] :
      ( m1_subset_1('#skF_2'(A_158,B_159,B_160),A_161)
      | ~ r2_hidden(A_158,k9_relat_1(B_160,B_159))
      | ~ v4_relat_1(B_160,A_161)
      | ~ v1_relat_1(B_160) ) ),
    inference(resolution,[status(thm)],[c_12,c_554])).

tff(c_866,plain,(
    ! [A_215,A_216,A_217] :
      ( m1_subset_1('#skF_2'(A_215,k1_relat_1(A_216),A_216),A_217)
      | ~ r2_hidden(A_215,k2_relat_1(A_216))
      | ~ v4_relat_1(A_216,A_217)
      | ~ v1_relat_1(A_216)
      | ~ v1_relat_1(A_216) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_562])).

tff(c_38,plain,(
    ! [E_30] :
      ( k1_funct_1('#skF_6',E_30) != '#skF_3'
      | ~ m1_subset_1(E_30,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_892,plain,(
    ! [A_218,A_219] :
      ( k1_funct_1('#skF_6','#skF_2'(A_218,k1_relat_1(A_219),A_219)) != '#skF_3'
      | ~ r2_hidden(A_218,k2_relat_1(A_219))
      | ~ v4_relat_1(A_219,'#skF_4')
      | ~ v1_relat_1(A_219) ) ),
    inference(resolution,[status(thm)],[c_866,c_38])).

tff(c_896,plain,(
    ! [A_131] :
      ( A_131 != '#skF_3'
      | ~ r2_hidden(A_131,k2_relat_1('#skF_6'))
      | ~ v4_relat_1('#skF_6','#skF_4')
      | ~ v1_relat_1('#skF_6')
      | ~ v1_funct_1('#skF_6')
      | ~ r2_hidden(A_131,k2_relat_1('#skF_6'))
      | ~ v1_relat_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_406,c_892])).

tff(c_899,plain,(
    ~ r2_hidden('#skF_3',k2_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_71,c_46,c_71,c_111,c_896])).

tff(c_150,plain,(
    ! [A_64,B_65,C_66] :
      ( k2_relset_1(A_64,B_65,C_66) = k2_relat_1(C_66)
      | ~ m1_subset_1(C_66,k1_zfmisc_1(k2_zfmisc_1(A_64,B_65))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_159,plain,(
    k2_relset_1('#skF_4','#skF_5','#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_42,c_150])).

tff(c_40,plain,(
    r2_hidden('#skF_3',k2_relset_1('#skF_4','#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_162,plain,(
    r2_hidden('#skF_3',k2_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_159,c_40])).

tff(c_901,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_899,c_162])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n008.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 20:51:15 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.17/1.51  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.38/1.51  
% 3.38/1.51  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.38/1.51  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4 > #skF_1
% 3.38/1.51  
% 3.38/1.51  %Foreground sorts:
% 3.38/1.51  
% 3.38/1.51  
% 3.38/1.51  %Background operators:
% 3.38/1.51  
% 3.38/1.51  
% 3.38/1.51  %Foreground operators:
% 3.38/1.51  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.38/1.51  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.38/1.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.38/1.51  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.38/1.51  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.38/1.51  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.38/1.51  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.38/1.51  tff('#skF_5', type, '#skF_5': $i).
% 3.38/1.51  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.38/1.51  tff('#skF_6', type, '#skF_6': $i).
% 3.38/1.51  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.38/1.51  tff('#skF_3', type, '#skF_3': $i).
% 3.38/1.51  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.38/1.51  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.38/1.51  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.38/1.51  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.38/1.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.38/1.51  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.38/1.51  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.38/1.51  tff('#skF_4', type, '#skF_4': $i).
% 3.38/1.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.38/1.51  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.38/1.51  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.38/1.51  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.38/1.51  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.38/1.51  
% 3.38/1.53  tff(f_97, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ~(r2_hidden(A, k2_relset_1(B, C, D)) & (![E]: (m1_subset_1(E, B) => ~(A = k1_funct_1(D, E))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t190_funct_2)).
% 3.38/1.53  tff(f_71, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.38/1.53  tff(f_77, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.38/1.53  tff(f_57, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_relat_1)).
% 3.38/1.53  tff(f_53, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_relat_1)).
% 3.38/1.53  tff(f_67, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_1)).
% 3.38/1.53  tff(f_42, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 3.38/1.53  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.38/1.53  tff(f_36, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 3.38/1.53  tff(f_81, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.38/1.53  tff(c_42, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.38/1.53  tff(c_67, plain, (![C_37, A_38, B_39]: (v1_relat_1(C_37) | ~m1_subset_1(C_37, k1_zfmisc_1(k2_zfmisc_1(A_38, B_39))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.38/1.53  tff(c_71, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_42, c_67])).
% 3.38/1.53  tff(c_46, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.38/1.53  tff(c_102, plain, (![C_50, A_51, B_52]: (v4_relat_1(C_50, A_51) | ~m1_subset_1(C_50, k1_zfmisc_1(k2_zfmisc_1(A_51, B_52))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.38/1.53  tff(c_111, plain, (v4_relat_1('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_42, c_102])).
% 3.38/1.53  tff(c_22, plain, (![A_16]: (k9_relat_1(A_16, k1_relat_1(A_16))=k2_relat_1(A_16) | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.38/1.53  tff(c_301, plain, (![A_118, B_119, C_120]: (r2_hidden(k4_tarski('#skF_2'(A_118, B_119, C_120), A_118), C_120) | ~r2_hidden(A_118, k9_relat_1(C_120, B_119)) | ~v1_relat_1(C_120))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.38/1.53  tff(c_26, plain, (![C_19, A_17, B_18]: (k1_funct_1(C_19, A_17)=B_18 | ~r2_hidden(k4_tarski(A_17, B_18), C_19) | ~v1_funct_1(C_19) | ~v1_relat_1(C_19))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.38/1.53  tff(c_386, plain, (![C_130, A_131, B_132]: (k1_funct_1(C_130, '#skF_2'(A_131, B_132, C_130))=A_131 | ~v1_funct_1(C_130) | ~r2_hidden(A_131, k9_relat_1(C_130, B_132)) | ~v1_relat_1(C_130))), inference(resolution, [status(thm)], [c_301, c_26])).
% 3.38/1.53  tff(c_406, plain, (![A_16, A_131]: (k1_funct_1(A_16, '#skF_2'(A_131, k1_relat_1(A_16), A_16))=A_131 | ~v1_funct_1(A_16) | ~r2_hidden(A_131, k2_relat_1(A_16)) | ~v1_relat_1(A_16) | ~v1_relat_1(A_16))), inference(superposition, [status(thm), theory('equality')], [c_22, c_386])).
% 3.38/1.53  tff(c_12, plain, (![B_9, A_8]: (r1_tarski(k1_relat_1(B_9), A_8) | ~v4_relat_1(B_9, A_8) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.38/1.53  tff(c_244, plain, (![A_92, B_93, C_94]: (r2_hidden('#skF_2'(A_92, B_93, C_94), k1_relat_1(C_94)) | ~r2_hidden(A_92, k9_relat_1(C_94, B_93)) | ~v1_relat_1(C_94))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.38/1.53  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.38/1.53  tff(c_466, plain, (![A_143, B_144, C_145, B_146]: (r2_hidden('#skF_2'(A_143, B_144, C_145), B_146) | ~r1_tarski(k1_relat_1(C_145), B_146) | ~r2_hidden(A_143, k9_relat_1(C_145, B_144)) | ~v1_relat_1(C_145))), inference(resolution, [status(thm)], [c_244, c_2])).
% 3.38/1.53  tff(c_8, plain, (![A_6, B_7]: (m1_subset_1(A_6, B_7) | ~r2_hidden(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.38/1.53  tff(c_554, plain, (![A_154, B_155, C_156, B_157]: (m1_subset_1('#skF_2'(A_154, B_155, C_156), B_157) | ~r1_tarski(k1_relat_1(C_156), B_157) | ~r2_hidden(A_154, k9_relat_1(C_156, B_155)) | ~v1_relat_1(C_156))), inference(resolution, [status(thm)], [c_466, c_8])).
% 3.38/1.53  tff(c_562, plain, (![A_158, B_159, B_160, A_161]: (m1_subset_1('#skF_2'(A_158, B_159, B_160), A_161) | ~r2_hidden(A_158, k9_relat_1(B_160, B_159)) | ~v4_relat_1(B_160, A_161) | ~v1_relat_1(B_160))), inference(resolution, [status(thm)], [c_12, c_554])).
% 3.38/1.53  tff(c_866, plain, (![A_215, A_216, A_217]: (m1_subset_1('#skF_2'(A_215, k1_relat_1(A_216), A_216), A_217) | ~r2_hidden(A_215, k2_relat_1(A_216)) | ~v4_relat_1(A_216, A_217) | ~v1_relat_1(A_216) | ~v1_relat_1(A_216))), inference(superposition, [status(thm), theory('equality')], [c_22, c_562])).
% 3.38/1.53  tff(c_38, plain, (![E_30]: (k1_funct_1('#skF_6', E_30)!='#skF_3' | ~m1_subset_1(E_30, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.38/1.53  tff(c_892, plain, (![A_218, A_219]: (k1_funct_1('#skF_6', '#skF_2'(A_218, k1_relat_1(A_219), A_219))!='#skF_3' | ~r2_hidden(A_218, k2_relat_1(A_219)) | ~v4_relat_1(A_219, '#skF_4') | ~v1_relat_1(A_219))), inference(resolution, [status(thm)], [c_866, c_38])).
% 3.38/1.53  tff(c_896, plain, (![A_131]: (A_131!='#skF_3' | ~r2_hidden(A_131, k2_relat_1('#skF_6')) | ~v4_relat_1('#skF_6', '#skF_4') | ~v1_relat_1('#skF_6') | ~v1_funct_1('#skF_6') | ~r2_hidden(A_131, k2_relat_1('#skF_6')) | ~v1_relat_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_406, c_892])).
% 3.38/1.53  tff(c_899, plain, (~r2_hidden('#skF_3', k2_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_71, c_71, c_46, c_71, c_111, c_896])).
% 3.38/1.53  tff(c_150, plain, (![A_64, B_65, C_66]: (k2_relset_1(A_64, B_65, C_66)=k2_relat_1(C_66) | ~m1_subset_1(C_66, k1_zfmisc_1(k2_zfmisc_1(A_64, B_65))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.38/1.53  tff(c_159, plain, (k2_relset_1('#skF_4', '#skF_5', '#skF_6')=k2_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_42, c_150])).
% 3.38/1.53  tff(c_40, plain, (r2_hidden('#skF_3', k2_relset_1('#skF_4', '#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.38/1.53  tff(c_162, plain, (r2_hidden('#skF_3', k2_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_159, c_40])).
% 3.38/1.53  tff(c_901, plain, $false, inference(negUnitSimplification, [status(thm)], [c_899, c_162])).
% 3.38/1.53  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.38/1.53  
% 3.38/1.53  Inference rules
% 3.38/1.53  ----------------------
% 3.38/1.53  #Ref     : 0
% 3.38/1.53  #Sup     : 191
% 3.38/1.53  #Fact    : 0
% 3.38/1.53  #Define  : 0
% 3.38/1.53  #Split   : 1
% 3.38/1.53  #Chain   : 0
% 3.38/1.53  #Close   : 0
% 3.38/1.53  
% 3.38/1.53  Ordering : KBO
% 3.38/1.53  
% 3.38/1.53  Simplification rules
% 3.38/1.53  ----------------------
% 3.38/1.53  #Subsume      : 10
% 3.38/1.53  #Demod        : 11
% 3.38/1.53  #Tautology    : 13
% 3.38/1.53  #SimpNegUnit  : 1
% 3.38/1.53  #BackRed      : 4
% 3.38/1.53  
% 3.38/1.53  #Partial instantiations: 0
% 3.38/1.53  #Strategies tried      : 1
% 3.38/1.53  
% 3.38/1.53  Timing (in seconds)
% 3.38/1.53  ----------------------
% 3.38/1.53  Preprocessing        : 0.33
% 3.38/1.53  Parsing              : 0.17
% 3.38/1.53  CNF conversion       : 0.02
% 3.38/1.53  Main loop            : 0.44
% 3.38/1.53  Inferencing          : 0.17
% 3.38/1.53  Reduction            : 0.11
% 3.38/1.53  Demodulation         : 0.08
% 3.38/1.53  BG Simplification    : 0.02
% 3.38/1.53  Subsumption          : 0.09
% 3.38/1.53  Abstraction          : 0.03
% 3.38/1.53  MUC search           : 0.00
% 3.38/1.53  Cooper               : 0.00
% 3.38/1.53  Total                : 0.80
% 3.38/1.53  Index Insertion      : 0.00
% 3.38/1.53  Index Deletion       : 0.00
% 3.38/1.53  Index Matching       : 0.00
% 3.38/1.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------
