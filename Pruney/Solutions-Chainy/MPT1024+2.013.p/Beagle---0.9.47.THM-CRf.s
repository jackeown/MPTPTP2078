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
% DateTime   : Thu Dec  3 10:16:23 EST 2020

% Result     : Theorem 3.30s
% Output     : CNFRefutation 3.39s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 112 expanded)
%              Number of leaves         :   34 (  57 expanded)
%              Depth                    :    9
%              Number of atoms          :   98 ( 300 expanded)
%              Number of equality atoms :   12 (  41 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k9_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_9 > #skF_4 > #skF_8 > #skF_3

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_92,negated_conjecture,(
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

tff(f_69,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_59,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_funct_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_73,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(c_48,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_63,plain,(
    ! [C_70,A_71,B_72] :
      ( v1_relat_1(C_70)
      | ~ m1_subset_1(C_70,k1_zfmisc_1(k2_zfmisc_1(A_71,B_72))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_72,plain,(
    v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_48,c_63])).

tff(c_80,plain,(
    ! [C_77,A_78,B_79] :
      ( v4_relat_1(C_77,A_78)
      | ~ m1_subset_1(C_77,k1_zfmisc_1(k2_zfmisc_1(A_78,B_79))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_89,plain,(
    v4_relat_1('#skF_8','#skF_5') ),
    inference(resolution,[status(thm)],[c_48,c_80])).

tff(c_10,plain,(
    ! [B_8,A_7] :
      ( r1_tarski(k1_relat_1(B_8),A_7)
      | ~ v4_relat_1(B_8,A_7)
      | ~ v1_relat_1(B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( m1_subset_1(A_5,k1_zfmisc_1(B_6))
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_52,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_14,plain,(
    ! [A_9,B_32,D_47] :
      ( k1_funct_1(A_9,'#skF_4'(A_9,B_32,k9_relat_1(A_9,B_32),D_47)) = D_47
      | ~ r2_hidden(D_47,k9_relat_1(A_9,B_32))
      | ~ v1_funct_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_200,plain,(
    ! [A_128,B_129,D_130] :
      ( r2_hidden('#skF_4'(A_128,B_129,k9_relat_1(A_128,B_129),D_130),k1_relat_1(A_128))
      | ~ r2_hidden(D_130,k9_relat_1(A_128,B_129))
      | ~ v1_funct_1(A_128)
      | ~ v1_relat_1(A_128) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_2,plain,(
    ! [C_4,A_1,B_2] :
      ( r2_hidden(C_4,A_1)
      | ~ r2_hidden(C_4,B_2)
      | ~ m1_subset_1(B_2,k1_zfmisc_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_203,plain,(
    ! [A_128,B_129,D_130,A_1] :
      ( r2_hidden('#skF_4'(A_128,B_129,k9_relat_1(A_128,B_129),D_130),A_1)
      | ~ m1_subset_1(k1_relat_1(A_128),k1_zfmisc_1(A_1))
      | ~ r2_hidden(D_130,k9_relat_1(A_128,B_129))
      | ~ v1_funct_1(A_128)
      | ~ v1_relat_1(A_128) ) ),
    inference(resolution,[status(thm)],[c_200,c_2])).

tff(c_187,plain,(
    ! [A_122,B_123,D_124] :
      ( r2_hidden('#skF_4'(A_122,B_123,k9_relat_1(A_122,B_123),D_124),B_123)
      | ~ r2_hidden(D_124,k9_relat_1(A_122,B_123))
      | ~ v1_funct_1(A_122)
      | ~ v1_relat_1(A_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_44,plain,(
    ! [F_65] :
      ( k1_funct_1('#skF_8',F_65) != '#skF_9'
      | ~ r2_hidden(F_65,'#skF_7')
      | ~ r2_hidden(F_65,'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_363,plain,(
    ! [A_174,D_175] :
      ( k1_funct_1('#skF_8','#skF_4'(A_174,'#skF_7',k9_relat_1(A_174,'#skF_7'),D_175)) != '#skF_9'
      | ~ r2_hidden('#skF_4'(A_174,'#skF_7',k9_relat_1(A_174,'#skF_7'),D_175),'#skF_5')
      | ~ r2_hidden(D_175,k9_relat_1(A_174,'#skF_7'))
      | ~ v1_funct_1(A_174)
      | ~ v1_relat_1(A_174) ) ),
    inference(resolution,[status(thm)],[c_187,c_44])).

tff(c_379,plain,(
    ! [A_176,D_177] :
      ( k1_funct_1('#skF_8','#skF_4'(A_176,'#skF_7',k9_relat_1(A_176,'#skF_7'),D_177)) != '#skF_9'
      | ~ m1_subset_1(k1_relat_1(A_176),k1_zfmisc_1('#skF_5'))
      | ~ r2_hidden(D_177,k9_relat_1(A_176,'#skF_7'))
      | ~ v1_funct_1(A_176)
      | ~ v1_relat_1(A_176) ) ),
    inference(resolution,[status(thm)],[c_203,c_363])).

tff(c_382,plain,(
    ! [D_47] :
      ( D_47 != '#skF_9'
      | ~ m1_subset_1(k1_relat_1('#skF_8'),k1_zfmisc_1('#skF_5'))
      | ~ r2_hidden(D_47,k9_relat_1('#skF_8','#skF_7'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8')
      | ~ r2_hidden(D_47,k9_relat_1('#skF_8','#skF_7'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_379])).

tff(c_384,plain,(
    ! [D_47] :
      ( D_47 != '#skF_9'
      | ~ m1_subset_1(k1_relat_1('#skF_8'),k1_zfmisc_1('#skF_5'))
      | ~ r2_hidden(D_47,k9_relat_1('#skF_8','#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_52,c_72,c_52,c_382])).

tff(c_385,plain,(
    ~ m1_subset_1(k1_relat_1('#skF_8'),k1_zfmisc_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_384])).

tff(c_390,plain,(
    ~ r1_tarski(k1_relat_1('#skF_8'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_6,c_385])).

tff(c_393,plain,
    ( ~ v4_relat_1('#skF_8','#skF_5')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_10,c_390])).

tff(c_397,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_89,c_393])).

tff(c_412,plain,(
    ~ r2_hidden('#skF_9',k9_relat_1('#skF_8','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_384])).

tff(c_147,plain,(
    ! [A_107,B_108,C_109,D_110] :
      ( k7_relset_1(A_107,B_108,C_109,D_110) = k9_relat_1(C_109,D_110)
      | ~ m1_subset_1(C_109,k1_zfmisc_1(k2_zfmisc_1(A_107,B_108))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_154,plain,(
    ! [D_110] : k7_relset_1('#skF_5','#skF_6','#skF_8',D_110) = k9_relat_1('#skF_8',D_110) ),
    inference(resolution,[status(thm)],[c_48,c_147])).

tff(c_46,plain,(
    r2_hidden('#skF_9',k7_relset_1('#skF_5','#skF_6','#skF_8','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_157,plain,(
    r2_hidden('#skF_9',k9_relat_1('#skF_8','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_46])).

tff(c_414,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_412,c_157])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 21:03:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.30/1.99  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.30/1.99  
% 3.30/1.99  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.30/2.00  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k9_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_9 > #skF_4 > #skF_8 > #skF_3
% 3.30/2.00  
% 3.30/2.00  %Foreground sorts:
% 3.30/2.00  
% 3.30/2.00  
% 3.30/2.00  %Background operators:
% 3.30/2.00  
% 3.30/2.00  
% 3.30/2.00  %Foreground operators:
% 3.30/2.00  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.30/2.00  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.30/2.00  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.30/2.00  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.30/2.00  tff('#skF_7', type, '#skF_7': $i).
% 3.30/2.00  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.30/2.00  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 3.30/2.00  tff('#skF_5', type, '#skF_5': $i).
% 3.30/2.00  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.30/2.00  tff('#skF_6', type, '#skF_6': $i).
% 3.30/2.00  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.30/2.00  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.30/2.00  tff('#skF_9', type, '#skF_9': $i).
% 3.30/2.00  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.30/2.00  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.30/2.00  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.30/2.00  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 3.30/2.00  tff('#skF_8', type, '#skF_8': $i).
% 3.30/2.00  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.30/2.00  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.30/2.00  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.30/2.00  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.30/2.00  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.30/2.00  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.30/2.00  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.30/2.00  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.30/2.00  
% 3.39/2.02  tff(f_92, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: ~(r2_hidden(E, k7_relset_1(A, B, D, C)) & (![F]: ~((r2_hidden(F, A) & r2_hidden(F, C)) & (E = k1_funct_1(D, F)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t115_funct_2)).
% 3.39/2.02  tff(f_63, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.39/2.02  tff(f_69, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.39/2.02  tff(f_42, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 3.39/2.02  tff(f_36, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.39/2.02  tff(f_59, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: ((C = k9_relat_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E]: ((r2_hidden(E, k1_relat_1(A)) & r2_hidden(E, B)) & (D = k1_funct_1(A, E)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d12_funct_1)).
% 3.39/2.02  tff(f_32, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 3.39/2.02  tff(f_73, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 3.39/2.02  tff(c_48, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.39/2.02  tff(c_63, plain, (![C_70, A_71, B_72]: (v1_relat_1(C_70) | ~m1_subset_1(C_70, k1_zfmisc_1(k2_zfmisc_1(A_71, B_72))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.39/2.02  tff(c_72, plain, (v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_48, c_63])).
% 3.39/2.02  tff(c_80, plain, (![C_77, A_78, B_79]: (v4_relat_1(C_77, A_78) | ~m1_subset_1(C_77, k1_zfmisc_1(k2_zfmisc_1(A_78, B_79))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.39/2.02  tff(c_89, plain, (v4_relat_1('#skF_8', '#skF_5')), inference(resolution, [status(thm)], [c_48, c_80])).
% 3.39/2.02  tff(c_10, plain, (![B_8, A_7]: (r1_tarski(k1_relat_1(B_8), A_7) | ~v4_relat_1(B_8, A_7) | ~v1_relat_1(B_8))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.39/2.02  tff(c_6, plain, (![A_5, B_6]: (m1_subset_1(A_5, k1_zfmisc_1(B_6)) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.39/2.02  tff(c_52, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.39/2.02  tff(c_14, plain, (![A_9, B_32, D_47]: (k1_funct_1(A_9, '#skF_4'(A_9, B_32, k9_relat_1(A_9, B_32), D_47))=D_47 | ~r2_hidden(D_47, k9_relat_1(A_9, B_32)) | ~v1_funct_1(A_9) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.39/2.02  tff(c_200, plain, (![A_128, B_129, D_130]: (r2_hidden('#skF_4'(A_128, B_129, k9_relat_1(A_128, B_129), D_130), k1_relat_1(A_128)) | ~r2_hidden(D_130, k9_relat_1(A_128, B_129)) | ~v1_funct_1(A_128) | ~v1_relat_1(A_128))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.39/2.02  tff(c_2, plain, (![C_4, A_1, B_2]: (r2_hidden(C_4, A_1) | ~r2_hidden(C_4, B_2) | ~m1_subset_1(B_2, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.39/2.02  tff(c_203, plain, (![A_128, B_129, D_130, A_1]: (r2_hidden('#skF_4'(A_128, B_129, k9_relat_1(A_128, B_129), D_130), A_1) | ~m1_subset_1(k1_relat_1(A_128), k1_zfmisc_1(A_1)) | ~r2_hidden(D_130, k9_relat_1(A_128, B_129)) | ~v1_funct_1(A_128) | ~v1_relat_1(A_128))), inference(resolution, [status(thm)], [c_200, c_2])).
% 3.39/2.02  tff(c_187, plain, (![A_122, B_123, D_124]: (r2_hidden('#skF_4'(A_122, B_123, k9_relat_1(A_122, B_123), D_124), B_123) | ~r2_hidden(D_124, k9_relat_1(A_122, B_123)) | ~v1_funct_1(A_122) | ~v1_relat_1(A_122))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.39/2.02  tff(c_44, plain, (![F_65]: (k1_funct_1('#skF_8', F_65)!='#skF_9' | ~r2_hidden(F_65, '#skF_7') | ~r2_hidden(F_65, '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.39/2.02  tff(c_363, plain, (![A_174, D_175]: (k1_funct_1('#skF_8', '#skF_4'(A_174, '#skF_7', k9_relat_1(A_174, '#skF_7'), D_175))!='#skF_9' | ~r2_hidden('#skF_4'(A_174, '#skF_7', k9_relat_1(A_174, '#skF_7'), D_175), '#skF_5') | ~r2_hidden(D_175, k9_relat_1(A_174, '#skF_7')) | ~v1_funct_1(A_174) | ~v1_relat_1(A_174))), inference(resolution, [status(thm)], [c_187, c_44])).
% 3.39/2.02  tff(c_379, plain, (![A_176, D_177]: (k1_funct_1('#skF_8', '#skF_4'(A_176, '#skF_7', k9_relat_1(A_176, '#skF_7'), D_177))!='#skF_9' | ~m1_subset_1(k1_relat_1(A_176), k1_zfmisc_1('#skF_5')) | ~r2_hidden(D_177, k9_relat_1(A_176, '#skF_7')) | ~v1_funct_1(A_176) | ~v1_relat_1(A_176))), inference(resolution, [status(thm)], [c_203, c_363])).
% 3.39/2.02  tff(c_382, plain, (![D_47]: (D_47!='#skF_9' | ~m1_subset_1(k1_relat_1('#skF_8'), k1_zfmisc_1('#skF_5')) | ~r2_hidden(D_47, k9_relat_1('#skF_8', '#skF_7')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~r2_hidden(D_47, k9_relat_1('#skF_8', '#skF_7')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_14, c_379])).
% 3.39/2.02  tff(c_384, plain, (![D_47]: (D_47!='#skF_9' | ~m1_subset_1(k1_relat_1('#skF_8'), k1_zfmisc_1('#skF_5')) | ~r2_hidden(D_47, k9_relat_1('#skF_8', '#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_52, c_72, c_52, c_382])).
% 3.39/2.02  tff(c_385, plain, (~m1_subset_1(k1_relat_1('#skF_8'), k1_zfmisc_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_384])).
% 3.39/2.02  tff(c_390, plain, (~r1_tarski(k1_relat_1('#skF_8'), '#skF_5')), inference(resolution, [status(thm)], [c_6, c_385])).
% 3.39/2.02  tff(c_393, plain, (~v4_relat_1('#skF_8', '#skF_5') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_10, c_390])).
% 3.39/2.02  tff(c_397, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_72, c_89, c_393])).
% 3.39/2.02  tff(c_412, plain, (~r2_hidden('#skF_9', k9_relat_1('#skF_8', '#skF_7'))), inference(splitRight, [status(thm)], [c_384])).
% 3.39/2.02  tff(c_147, plain, (![A_107, B_108, C_109, D_110]: (k7_relset_1(A_107, B_108, C_109, D_110)=k9_relat_1(C_109, D_110) | ~m1_subset_1(C_109, k1_zfmisc_1(k2_zfmisc_1(A_107, B_108))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.39/2.02  tff(c_154, plain, (![D_110]: (k7_relset_1('#skF_5', '#skF_6', '#skF_8', D_110)=k9_relat_1('#skF_8', D_110))), inference(resolution, [status(thm)], [c_48, c_147])).
% 3.39/2.02  tff(c_46, plain, (r2_hidden('#skF_9', k7_relset_1('#skF_5', '#skF_6', '#skF_8', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.39/2.02  tff(c_157, plain, (r2_hidden('#skF_9', k9_relat_1('#skF_8', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_154, c_46])).
% 3.39/2.02  tff(c_414, plain, $false, inference(negUnitSimplification, [status(thm)], [c_412, c_157])).
% 3.39/2.02  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.39/2.02  
% 3.39/2.02  Inference rules
% 3.39/2.02  ----------------------
% 3.39/2.02  #Ref     : 0
% 3.39/2.02  #Sup     : 77
% 3.39/2.02  #Fact    : 0
% 3.39/2.02  #Define  : 0
% 3.39/2.02  #Split   : 2
% 3.39/2.02  #Chain   : 0
% 3.39/2.02  #Close   : 0
% 3.39/2.02  
% 3.39/2.02  Ordering : KBO
% 3.39/2.02  
% 3.39/2.02  Simplification rules
% 3.39/2.02  ----------------------
% 3.39/2.02  #Subsume      : 2
% 3.39/2.02  #Demod        : 15
% 3.39/2.02  #Tautology    : 13
% 3.39/2.02  #SimpNegUnit  : 1
% 3.39/2.02  #BackRed      : 4
% 3.39/2.02  
% 3.39/2.02  #Partial instantiations: 0
% 3.39/2.02  #Strategies tried      : 1
% 3.39/2.02  
% 3.39/2.02  Timing (in seconds)
% 3.39/2.02  ----------------------
% 3.44/2.03  Preprocessing        : 0.54
% 3.44/2.03  Parsing              : 0.25
% 3.44/2.03  CNF conversion       : 0.06
% 3.44/2.03  Main loop            : 0.54
% 3.44/2.03  Inferencing          : 0.21
% 3.44/2.03  Reduction            : 0.12
% 3.44/2.03  Demodulation         : 0.09
% 3.44/2.03  BG Simplification    : 0.05
% 3.44/2.03  Subsumption          : 0.12
% 3.44/2.03  Abstraction          : 0.03
% 3.44/2.03  MUC search           : 0.00
% 3.44/2.03  Cooper               : 0.00
% 3.44/2.03  Total                : 1.12
% 3.44/2.03  Index Insertion      : 0.00
% 3.44/2.03  Index Deletion       : 0.00
% 3.44/2.03  Index Matching       : 0.00
% 3.44/2.03  BG Taut test         : 0.00
%------------------------------------------------------------------------------
