%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:04 EST 2020

% Result     : Theorem 2.24s
% Output     : CNFRefutation 2.24s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 123 expanded)
%              Number of leaves         :   34 (  60 expanded)
%              Depth                    :    9
%              Number of atoms          :   94 ( 287 expanded)
%              Number of equality atoms :   11 (  35 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_4 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_8 > #skF_2 > #skF_1

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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

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

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_50,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_91,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,B,C)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
       => ~ ( r2_hidden(A,k2_relset_1(B,C,D))
            & ! [E] :
                ( m1_subset_1(E,B)
               => A != k1_funct_1(D,E) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t190_funct_2)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_65,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( B = k2_relat_1(A)
        <=> ! [C] :
              ( r2_hidden(C,B)
            <=> ? [D] :
                  ( r2_hidden(D,k1_relat_1(A))
                  & C = k1_funct_1(A,D) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(c_14,plain,(
    ! [A_11,B_12] : v1_relat_1(k2_zfmisc_1(A_11,B_12)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_44,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_61,plain,(
    ! [B_68,A_69] :
      ( v1_relat_1(B_68)
      | ~ m1_subset_1(B_68,k1_zfmisc_1(A_69))
      | ~ v1_relat_1(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_67,plain,
    ( v1_relat_1('#skF_8')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_44,c_61])).

tff(c_71,plain,(
    v1_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_67])).

tff(c_84,plain,(
    ! [C_74,A_75,B_76] :
      ( v4_relat_1(C_74,A_75)
      | ~ m1_subset_1(C_74,k1_zfmisc_1(k2_zfmisc_1(A_75,B_76))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_93,plain,(
    v4_relat_1('#skF_8','#skF_6') ),
    inference(resolution,[status(thm)],[c_44,c_84])).

tff(c_12,plain,(
    ! [B_10,A_9] :
      ( r1_tarski(k1_relat_1(B_10),A_9)
      | ~ v4_relat_1(B_10,A_9)
      | ~ v1_relat_1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_48,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_18,plain,(
    ! [A_13,C_49] :
      ( k1_funct_1(A_13,'#skF_4'(A_13,k2_relat_1(A_13),C_49)) = C_49
      | ~ r2_hidden(C_49,k2_relat_1(A_13))
      | ~ v1_funct_1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_189,plain,(
    ! [A_116,C_117] :
      ( r2_hidden('#skF_4'(A_116,k2_relat_1(A_116),C_117),k1_relat_1(A_116))
      | ~ r2_hidden(C_117,k2_relat_1(A_116))
      | ~ v1_funct_1(A_116)
      | ~ v1_relat_1(A_116) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(A_1,k1_zfmisc_1(B_2))
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_120,plain,(
    ! [A_85,C_86,B_87] :
      ( m1_subset_1(A_85,C_86)
      | ~ m1_subset_1(B_87,k1_zfmisc_1(C_86))
      | ~ r2_hidden(A_85,B_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_125,plain,(
    ! [A_85,B_2,A_1] :
      ( m1_subset_1(A_85,B_2)
      | ~ r2_hidden(A_85,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_4,c_120])).

tff(c_217,plain,(
    ! [A_127,C_128,B_129] :
      ( m1_subset_1('#skF_4'(A_127,k2_relat_1(A_127),C_128),B_129)
      | ~ r1_tarski(k1_relat_1(A_127),B_129)
      | ~ r2_hidden(C_128,k2_relat_1(A_127))
      | ~ v1_funct_1(A_127)
      | ~ v1_relat_1(A_127) ) ),
    inference(resolution,[status(thm)],[c_189,c_125])).

tff(c_40,plain,(
    ! [E_60] :
      ( k1_funct_1('#skF_8',E_60) != '#skF_5'
      | ~ m1_subset_1(E_60,'#skF_6') ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_289,plain,(
    ! [A_141,C_142] :
      ( k1_funct_1('#skF_8','#skF_4'(A_141,k2_relat_1(A_141),C_142)) != '#skF_5'
      | ~ r1_tarski(k1_relat_1(A_141),'#skF_6')
      | ~ r2_hidden(C_142,k2_relat_1(A_141))
      | ~ v1_funct_1(A_141)
      | ~ v1_relat_1(A_141) ) ),
    inference(resolution,[status(thm)],[c_217,c_40])).

tff(c_293,plain,(
    ! [C_49] :
      ( C_49 != '#skF_5'
      | ~ r1_tarski(k1_relat_1('#skF_8'),'#skF_6')
      | ~ r2_hidden(C_49,k2_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8')
      | ~ r2_hidden(C_49,k2_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_289])).

tff(c_295,plain,(
    ! [C_49] :
      ( C_49 != '#skF_5'
      | ~ r1_tarski(k1_relat_1('#skF_8'),'#skF_6')
      | ~ r2_hidden(C_49,k2_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_48,c_71,c_48,c_293])).

tff(c_296,plain,(
    ~ r1_tarski(k1_relat_1('#skF_8'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_295])).

tff(c_299,plain,
    ( ~ v4_relat_1('#skF_8','#skF_6')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_12,c_296])).

tff(c_303,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_93,c_299])).

tff(c_316,plain,(
    ~ r2_hidden('#skF_5',k2_relat_1('#skF_8')) ),
    inference(splitRight,[status(thm)],[c_295])).

tff(c_150,plain,(
    ! [A_98,B_99,C_100] :
      ( k2_relset_1(A_98,B_99,C_100) = k2_relat_1(C_100)
      | ~ m1_subset_1(C_100,k1_zfmisc_1(k2_zfmisc_1(A_98,B_99))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_159,plain,(
    k2_relset_1('#skF_6','#skF_7','#skF_8') = k2_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_44,c_150])).

tff(c_42,plain,(
    r2_hidden('#skF_5',k2_relset_1('#skF_6','#skF_7','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_162,plain,(
    r2_hidden('#skF_5',k2_relat_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_159,c_42])).

tff(c_318,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_316,c_162])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:51:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.24/1.40  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.24/1.41  
% 2.24/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.24/1.41  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_4 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_8 > #skF_2 > #skF_1
% 2.24/1.41  
% 2.24/1.41  %Foreground sorts:
% 2.24/1.41  
% 2.24/1.41  
% 2.24/1.41  %Background operators:
% 2.24/1.41  
% 2.24/1.41  
% 2.24/1.41  %Foreground operators:
% 2.24/1.41  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.24/1.41  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.24/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.24/1.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.24/1.41  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.24/1.41  tff('#skF_7', type, '#skF_7': $i).
% 2.24/1.41  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.24/1.41  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.24/1.41  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.24/1.41  tff('#skF_5', type, '#skF_5': $i).
% 2.24/1.41  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.24/1.41  tff('#skF_6', type, '#skF_6': $i).
% 2.24/1.41  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.24/1.41  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.24/1.41  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.24/1.41  tff('#skF_8', type, '#skF_8': $i).
% 2.24/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.24/1.41  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.24/1.41  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.24/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.24/1.41  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.24/1.41  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.24/1.41  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.24/1.41  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.24/1.41  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.24/1.41  
% 2.24/1.42  tff(f_50, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.24/1.42  tff(f_91, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ~(r2_hidden(A, k2_relset_1(B, C, D)) & (![E]: (m1_subset_1(E, B) => ~(A = k1_funct_1(D, E))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t190_funct_2)).
% 2.24/1.42  tff(f_42, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.24/1.42  tff(f_71, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.24/1.42  tff(f_48, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 2.24/1.42  tff(f_65, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_funct_1)).
% 2.24/1.42  tff(f_29, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.24/1.42  tff(f_35, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 2.24/1.42  tff(f_75, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.24/1.42  tff(c_14, plain, (![A_11, B_12]: (v1_relat_1(k2_zfmisc_1(A_11, B_12)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.24/1.42  tff(c_44, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7')))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.24/1.42  tff(c_61, plain, (![B_68, A_69]: (v1_relat_1(B_68) | ~m1_subset_1(B_68, k1_zfmisc_1(A_69)) | ~v1_relat_1(A_69))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.24/1.42  tff(c_67, plain, (v1_relat_1('#skF_8') | ~v1_relat_1(k2_zfmisc_1('#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_44, c_61])).
% 2.24/1.42  tff(c_71, plain, (v1_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_67])).
% 2.24/1.42  tff(c_84, plain, (![C_74, A_75, B_76]: (v4_relat_1(C_74, A_75) | ~m1_subset_1(C_74, k1_zfmisc_1(k2_zfmisc_1(A_75, B_76))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.24/1.42  tff(c_93, plain, (v4_relat_1('#skF_8', '#skF_6')), inference(resolution, [status(thm)], [c_44, c_84])).
% 2.24/1.42  tff(c_12, plain, (![B_10, A_9]: (r1_tarski(k1_relat_1(B_10), A_9) | ~v4_relat_1(B_10, A_9) | ~v1_relat_1(B_10))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.24/1.42  tff(c_48, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.24/1.42  tff(c_18, plain, (![A_13, C_49]: (k1_funct_1(A_13, '#skF_4'(A_13, k2_relat_1(A_13), C_49))=C_49 | ~r2_hidden(C_49, k2_relat_1(A_13)) | ~v1_funct_1(A_13) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.24/1.42  tff(c_189, plain, (![A_116, C_117]: (r2_hidden('#skF_4'(A_116, k2_relat_1(A_116), C_117), k1_relat_1(A_116)) | ~r2_hidden(C_117, k2_relat_1(A_116)) | ~v1_funct_1(A_116) | ~v1_relat_1(A_116))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.24/1.42  tff(c_4, plain, (![A_1, B_2]: (m1_subset_1(A_1, k1_zfmisc_1(B_2)) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.24/1.42  tff(c_120, plain, (![A_85, C_86, B_87]: (m1_subset_1(A_85, C_86) | ~m1_subset_1(B_87, k1_zfmisc_1(C_86)) | ~r2_hidden(A_85, B_87))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.24/1.42  tff(c_125, plain, (![A_85, B_2, A_1]: (m1_subset_1(A_85, B_2) | ~r2_hidden(A_85, A_1) | ~r1_tarski(A_1, B_2))), inference(resolution, [status(thm)], [c_4, c_120])).
% 2.24/1.42  tff(c_217, plain, (![A_127, C_128, B_129]: (m1_subset_1('#skF_4'(A_127, k2_relat_1(A_127), C_128), B_129) | ~r1_tarski(k1_relat_1(A_127), B_129) | ~r2_hidden(C_128, k2_relat_1(A_127)) | ~v1_funct_1(A_127) | ~v1_relat_1(A_127))), inference(resolution, [status(thm)], [c_189, c_125])).
% 2.24/1.42  tff(c_40, plain, (![E_60]: (k1_funct_1('#skF_8', E_60)!='#skF_5' | ~m1_subset_1(E_60, '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.24/1.42  tff(c_289, plain, (![A_141, C_142]: (k1_funct_1('#skF_8', '#skF_4'(A_141, k2_relat_1(A_141), C_142))!='#skF_5' | ~r1_tarski(k1_relat_1(A_141), '#skF_6') | ~r2_hidden(C_142, k2_relat_1(A_141)) | ~v1_funct_1(A_141) | ~v1_relat_1(A_141))), inference(resolution, [status(thm)], [c_217, c_40])).
% 2.24/1.42  tff(c_293, plain, (![C_49]: (C_49!='#skF_5' | ~r1_tarski(k1_relat_1('#skF_8'), '#skF_6') | ~r2_hidden(C_49, k2_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~r2_hidden(C_49, k2_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_18, c_289])).
% 2.24/1.42  tff(c_295, plain, (![C_49]: (C_49!='#skF_5' | ~r1_tarski(k1_relat_1('#skF_8'), '#skF_6') | ~r2_hidden(C_49, k2_relat_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_71, c_48, c_71, c_48, c_293])).
% 2.24/1.42  tff(c_296, plain, (~r1_tarski(k1_relat_1('#skF_8'), '#skF_6')), inference(splitLeft, [status(thm)], [c_295])).
% 2.24/1.42  tff(c_299, plain, (~v4_relat_1('#skF_8', '#skF_6') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_12, c_296])).
% 2.24/1.42  tff(c_303, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_71, c_93, c_299])).
% 2.24/1.42  tff(c_316, plain, (~r2_hidden('#skF_5', k2_relat_1('#skF_8'))), inference(splitRight, [status(thm)], [c_295])).
% 2.24/1.42  tff(c_150, plain, (![A_98, B_99, C_100]: (k2_relset_1(A_98, B_99, C_100)=k2_relat_1(C_100) | ~m1_subset_1(C_100, k1_zfmisc_1(k2_zfmisc_1(A_98, B_99))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.24/1.42  tff(c_159, plain, (k2_relset_1('#skF_6', '#skF_7', '#skF_8')=k2_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_44, c_150])).
% 2.24/1.42  tff(c_42, plain, (r2_hidden('#skF_5', k2_relset_1('#skF_6', '#skF_7', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.24/1.42  tff(c_162, plain, (r2_hidden('#skF_5', k2_relat_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_159, c_42])).
% 2.24/1.42  tff(c_318, plain, $false, inference(negUnitSimplification, [status(thm)], [c_316, c_162])).
% 2.24/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.24/1.42  
% 2.24/1.42  Inference rules
% 2.24/1.42  ----------------------
% 2.24/1.42  #Ref     : 0
% 2.24/1.42  #Sup     : 53
% 2.24/1.42  #Fact    : 0
% 2.24/1.42  #Define  : 0
% 2.24/1.42  #Split   : 2
% 2.24/1.42  #Chain   : 0
% 2.50/1.42  #Close   : 0
% 2.50/1.42  
% 2.50/1.42  Ordering : KBO
% 2.50/1.42  
% 2.50/1.42  Simplification rules
% 2.50/1.42  ----------------------
% 2.50/1.42  #Subsume      : 2
% 2.50/1.42  #Demod        : 17
% 2.50/1.42  #Tautology    : 14
% 2.50/1.42  #SimpNegUnit  : 1
% 2.50/1.42  #BackRed      : 3
% 2.50/1.42  
% 2.50/1.42  #Partial instantiations: 0
% 2.50/1.42  #Strategies tried      : 1
% 2.50/1.42  
% 2.50/1.42  Timing (in seconds)
% 2.50/1.42  ----------------------
% 2.50/1.43  Preprocessing        : 0.33
% 2.50/1.43  Parsing              : 0.17
% 2.50/1.43  CNF conversion       : 0.03
% 2.50/1.43  Main loop            : 0.23
% 2.50/1.43  Inferencing          : 0.09
% 2.50/1.43  Reduction            : 0.06
% 2.50/1.43  Demodulation         : 0.05
% 2.50/1.43  BG Simplification    : 0.02
% 2.50/1.43  Subsumption          : 0.04
% 2.50/1.43  Abstraction          : 0.01
% 2.50/1.43  MUC search           : 0.00
% 2.50/1.43  Cooper               : 0.00
% 2.50/1.43  Total                : 0.59
% 2.50/1.43  Index Insertion      : 0.00
% 2.50/1.43  Index Deletion       : 0.00
% 2.50/1.43  Index Matching       : 0.00
% 2.50/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
