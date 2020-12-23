%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:32 EST 2020

% Result     : Theorem 2.73s
% Output     : CNFRefutation 2.73s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 115 expanded)
%              Number of leaves         :   34 (  58 expanded)
%              Depth                    :    9
%              Number of atoms          :  100 ( 309 expanded)
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

tff(f_91,negated_conjecture,(
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

tff(f_62,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_58,axiom,(
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

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_72,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(c_48,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_63,plain,(
    ! [C_69,A_70,B_71] :
      ( v1_relat_1(C_69)
      | ~ m1_subset_1(C_69,k1_zfmisc_1(k2_zfmisc_1(A_70,B_71))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_72,plain,(
    v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_48,c_63])).

tff(c_80,plain,(
    ! [C_76,A_77,B_78] :
      ( v4_relat_1(C_76,A_77)
      | ~ m1_subset_1(C_76,k1_zfmisc_1(k2_zfmisc_1(A_77,B_78))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_89,plain,(
    v4_relat_1('#skF_8','#skF_5') ),
    inference(resolution,[status(thm)],[c_48,c_80])).

tff(c_10,plain,(
    ! [B_7,A_6] :
      ( r1_tarski(k1_relat_1(B_7),A_6)
      | ~ v4_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_52,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_14,plain,(
    ! [A_8,B_31,D_46] :
      ( k1_funct_1(A_8,'#skF_4'(A_8,B_31,k9_relat_1(A_8,B_31),D_46)) = D_46
      | ~ r2_hidden(D_46,k9_relat_1(A_8,B_31))
      | ~ v1_funct_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_195,plain,(
    ! [A_129,B_130,D_131] :
      ( r2_hidden('#skF_4'(A_129,B_130,k9_relat_1(A_129,B_130),D_131),k1_relat_1(A_129))
      | ~ r2_hidden(D_131,k9_relat_1(A_129,B_130))
      | ~ v1_funct_1(A_129)
      | ~ v1_relat_1(A_129) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(A_1,k1_zfmisc_1(B_2))
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_133,plain,(
    ! [A_92,C_93,B_94] :
      ( m1_subset_1(A_92,C_93)
      | ~ m1_subset_1(B_94,k1_zfmisc_1(C_93))
      | ~ r2_hidden(A_92,B_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_138,plain,(
    ! [A_92,B_2,A_1] :
      ( m1_subset_1(A_92,B_2)
      | ~ r2_hidden(A_92,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_4,c_133])).

tff(c_198,plain,(
    ! [A_129,B_130,D_131,B_2] :
      ( m1_subset_1('#skF_4'(A_129,B_130,k9_relat_1(A_129,B_130),D_131),B_2)
      | ~ r1_tarski(k1_relat_1(A_129),B_2)
      | ~ r2_hidden(D_131,k9_relat_1(A_129,B_130))
      | ~ v1_funct_1(A_129)
      | ~ v1_relat_1(A_129) ) ),
    inference(resolution,[status(thm)],[c_195,c_138])).

tff(c_182,plain,(
    ! [A_123,B_124,D_125] :
      ( r2_hidden('#skF_4'(A_123,B_124,k9_relat_1(A_123,B_124),D_125),B_124)
      | ~ r2_hidden(D_125,k9_relat_1(A_123,B_124))
      | ~ v1_funct_1(A_123)
      | ~ v1_relat_1(A_123) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_44,plain,(
    ! [F_64] :
      ( k1_funct_1('#skF_8',F_64) != '#skF_9'
      | ~ r2_hidden(F_64,'#skF_7')
      | ~ m1_subset_1(F_64,'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_437,plain,(
    ! [A_177,D_178] :
      ( k1_funct_1('#skF_8','#skF_4'(A_177,'#skF_7',k9_relat_1(A_177,'#skF_7'),D_178)) != '#skF_9'
      | ~ m1_subset_1('#skF_4'(A_177,'#skF_7',k9_relat_1(A_177,'#skF_7'),D_178),'#skF_5')
      | ~ r2_hidden(D_178,k9_relat_1(A_177,'#skF_7'))
      | ~ v1_funct_1(A_177)
      | ~ v1_relat_1(A_177) ) ),
    inference(resolution,[status(thm)],[c_182,c_44])).

tff(c_449,plain,(
    ! [A_179,D_180] :
      ( k1_funct_1('#skF_8','#skF_4'(A_179,'#skF_7',k9_relat_1(A_179,'#skF_7'),D_180)) != '#skF_9'
      | ~ r1_tarski(k1_relat_1(A_179),'#skF_5')
      | ~ r2_hidden(D_180,k9_relat_1(A_179,'#skF_7'))
      | ~ v1_funct_1(A_179)
      | ~ v1_relat_1(A_179) ) ),
    inference(resolution,[status(thm)],[c_198,c_437])).

tff(c_453,plain,(
    ! [D_46] :
      ( D_46 != '#skF_9'
      | ~ r1_tarski(k1_relat_1('#skF_8'),'#skF_5')
      | ~ r2_hidden(D_46,k9_relat_1('#skF_8','#skF_7'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8')
      | ~ r2_hidden(D_46,k9_relat_1('#skF_8','#skF_7'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_449])).

tff(c_455,plain,(
    ! [D_46] :
      ( D_46 != '#skF_9'
      | ~ r1_tarski(k1_relat_1('#skF_8'),'#skF_5')
      | ~ r2_hidden(D_46,k9_relat_1('#skF_8','#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_52,c_72,c_52,c_453])).

tff(c_456,plain,(
    ~ r1_tarski(k1_relat_1('#skF_8'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_455])).

tff(c_459,plain,
    ( ~ v4_relat_1('#skF_8','#skF_5')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_10,c_456])).

tff(c_463,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_89,c_459])).

tff(c_473,plain,(
    ~ r2_hidden('#skF_9',k9_relat_1('#skF_8','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_455])).

tff(c_148,plain,(
    ! [A_106,B_107,C_108,D_109] :
      ( k7_relset_1(A_106,B_107,C_108,D_109) = k9_relat_1(C_108,D_109)
      | ~ m1_subset_1(C_108,k1_zfmisc_1(k2_zfmisc_1(A_106,B_107))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_155,plain,(
    ! [D_109] : k7_relset_1('#skF_5','#skF_6','#skF_8',D_109) = k9_relat_1('#skF_8',D_109) ),
    inference(resolution,[status(thm)],[c_48,c_148])).

tff(c_46,plain,(
    r2_hidden('#skF_9',k7_relset_1('#skF_5','#skF_6','#skF_8','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_157,plain,(
    r2_hidden('#skF_9',k9_relat_1('#skF_8','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_46])).

tff(c_475,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_473,c_157])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 13:31:57 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.73/1.37  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.73/1.37  
% 2.73/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.73/1.38  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k9_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_9 > #skF_4 > #skF_8 > #skF_3
% 2.73/1.38  
% 2.73/1.38  %Foreground sorts:
% 2.73/1.38  
% 2.73/1.38  
% 2.73/1.38  %Background operators:
% 2.73/1.38  
% 2.73/1.38  
% 2.73/1.38  %Foreground operators:
% 2.73/1.38  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.73/1.38  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.73/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.73/1.38  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.73/1.38  tff('#skF_7', type, '#skF_7': $i).
% 2.73/1.38  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.73/1.38  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.73/1.38  tff('#skF_5', type, '#skF_5': $i).
% 2.73/1.38  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.73/1.38  tff('#skF_6', type, '#skF_6': $i).
% 2.73/1.38  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.73/1.38  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.73/1.38  tff('#skF_9', type, '#skF_9': $i).
% 2.73/1.38  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.73/1.38  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.73/1.38  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.73/1.38  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 2.73/1.38  tff('#skF_8', type, '#skF_8': $i).
% 2.73/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.73/1.38  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.73/1.38  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.73/1.38  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.73/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.73/1.38  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.73/1.38  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.73/1.38  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.73/1.38  
% 2.73/1.39  tff(f_91, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: ~(r2_hidden(E, k7_relset_1(A, B, D, C)) & (![F]: (m1_subset_1(F, A) => ~(r2_hidden(F, C) & (E = k1_funct_1(D, F))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t116_funct_2)).
% 2.73/1.39  tff(f_62, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.73/1.39  tff(f_68, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.73/1.39  tff(f_41, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 2.73/1.39  tff(f_58, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: ((C = k9_relat_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E]: ((r2_hidden(E, k1_relat_1(A)) & r2_hidden(E, B)) & (D = k1_funct_1(A, E)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_funct_1)).
% 2.73/1.39  tff(f_29, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.73/1.39  tff(f_35, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 2.73/1.39  tff(f_72, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 2.73/1.39  tff(c_48, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.73/1.39  tff(c_63, plain, (![C_69, A_70, B_71]: (v1_relat_1(C_69) | ~m1_subset_1(C_69, k1_zfmisc_1(k2_zfmisc_1(A_70, B_71))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.73/1.39  tff(c_72, plain, (v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_48, c_63])).
% 2.73/1.39  tff(c_80, plain, (![C_76, A_77, B_78]: (v4_relat_1(C_76, A_77) | ~m1_subset_1(C_76, k1_zfmisc_1(k2_zfmisc_1(A_77, B_78))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.73/1.39  tff(c_89, plain, (v4_relat_1('#skF_8', '#skF_5')), inference(resolution, [status(thm)], [c_48, c_80])).
% 2.73/1.39  tff(c_10, plain, (![B_7, A_6]: (r1_tarski(k1_relat_1(B_7), A_6) | ~v4_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.73/1.39  tff(c_52, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.73/1.39  tff(c_14, plain, (![A_8, B_31, D_46]: (k1_funct_1(A_8, '#skF_4'(A_8, B_31, k9_relat_1(A_8, B_31), D_46))=D_46 | ~r2_hidden(D_46, k9_relat_1(A_8, B_31)) | ~v1_funct_1(A_8) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.73/1.39  tff(c_195, plain, (![A_129, B_130, D_131]: (r2_hidden('#skF_4'(A_129, B_130, k9_relat_1(A_129, B_130), D_131), k1_relat_1(A_129)) | ~r2_hidden(D_131, k9_relat_1(A_129, B_130)) | ~v1_funct_1(A_129) | ~v1_relat_1(A_129))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.73/1.39  tff(c_4, plain, (![A_1, B_2]: (m1_subset_1(A_1, k1_zfmisc_1(B_2)) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.73/1.39  tff(c_133, plain, (![A_92, C_93, B_94]: (m1_subset_1(A_92, C_93) | ~m1_subset_1(B_94, k1_zfmisc_1(C_93)) | ~r2_hidden(A_92, B_94))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.73/1.39  tff(c_138, plain, (![A_92, B_2, A_1]: (m1_subset_1(A_92, B_2) | ~r2_hidden(A_92, A_1) | ~r1_tarski(A_1, B_2))), inference(resolution, [status(thm)], [c_4, c_133])).
% 2.73/1.39  tff(c_198, plain, (![A_129, B_130, D_131, B_2]: (m1_subset_1('#skF_4'(A_129, B_130, k9_relat_1(A_129, B_130), D_131), B_2) | ~r1_tarski(k1_relat_1(A_129), B_2) | ~r2_hidden(D_131, k9_relat_1(A_129, B_130)) | ~v1_funct_1(A_129) | ~v1_relat_1(A_129))), inference(resolution, [status(thm)], [c_195, c_138])).
% 2.73/1.39  tff(c_182, plain, (![A_123, B_124, D_125]: (r2_hidden('#skF_4'(A_123, B_124, k9_relat_1(A_123, B_124), D_125), B_124) | ~r2_hidden(D_125, k9_relat_1(A_123, B_124)) | ~v1_funct_1(A_123) | ~v1_relat_1(A_123))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.73/1.39  tff(c_44, plain, (![F_64]: (k1_funct_1('#skF_8', F_64)!='#skF_9' | ~r2_hidden(F_64, '#skF_7') | ~m1_subset_1(F_64, '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.73/1.39  tff(c_437, plain, (![A_177, D_178]: (k1_funct_1('#skF_8', '#skF_4'(A_177, '#skF_7', k9_relat_1(A_177, '#skF_7'), D_178))!='#skF_9' | ~m1_subset_1('#skF_4'(A_177, '#skF_7', k9_relat_1(A_177, '#skF_7'), D_178), '#skF_5') | ~r2_hidden(D_178, k9_relat_1(A_177, '#skF_7')) | ~v1_funct_1(A_177) | ~v1_relat_1(A_177))), inference(resolution, [status(thm)], [c_182, c_44])).
% 2.73/1.39  tff(c_449, plain, (![A_179, D_180]: (k1_funct_1('#skF_8', '#skF_4'(A_179, '#skF_7', k9_relat_1(A_179, '#skF_7'), D_180))!='#skF_9' | ~r1_tarski(k1_relat_1(A_179), '#skF_5') | ~r2_hidden(D_180, k9_relat_1(A_179, '#skF_7')) | ~v1_funct_1(A_179) | ~v1_relat_1(A_179))), inference(resolution, [status(thm)], [c_198, c_437])).
% 2.73/1.39  tff(c_453, plain, (![D_46]: (D_46!='#skF_9' | ~r1_tarski(k1_relat_1('#skF_8'), '#skF_5') | ~r2_hidden(D_46, k9_relat_1('#skF_8', '#skF_7')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~r2_hidden(D_46, k9_relat_1('#skF_8', '#skF_7')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_14, c_449])).
% 2.73/1.39  tff(c_455, plain, (![D_46]: (D_46!='#skF_9' | ~r1_tarski(k1_relat_1('#skF_8'), '#skF_5') | ~r2_hidden(D_46, k9_relat_1('#skF_8', '#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_52, c_72, c_52, c_453])).
% 2.73/1.39  tff(c_456, plain, (~r1_tarski(k1_relat_1('#skF_8'), '#skF_5')), inference(splitLeft, [status(thm)], [c_455])).
% 2.73/1.39  tff(c_459, plain, (~v4_relat_1('#skF_8', '#skF_5') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_10, c_456])).
% 2.73/1.39  tff(c_463, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_72, c_89, c_459])).
% 2.73/1.39  tff(c_473, plain, (~r2_hidden('#skF_9', k9_relat_1('#skF_8', '#skF_7'))), inference(splitRight, [status(thm)], [c_455])).
% 2.73/1.39  tff(c_148, plain, (![A_106, B_107, C_108, D_109]: (k7_relset_1(A_106, B_107, C_108, D_109)=k9_relat_1(C_108, D_109) | ~m1_subset_1(C_108, k1_zfmisc_1(k2_zfmisc_1(A_106, B_107))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.73/1.39  tff(c_155, plain, (![D_109]: (k7_relset_1('#skF_5', '#skF_6', '#skF_8', D_109)=k9_relat_1('#skF_8', D_109))), inference(resolution, [status(thm)], [c_48, c_148])).
% 2.73/1.39  tff(c_46, plain, (r2_hidden('#skF_9', k7_relset_1('#skF_5', '#skF_6', '#skF_8', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.73/1.39  tff(c_157, plain, (r2_hidden('#skF_9', k9_relat_1('#skF_8', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_155, c_46])).
% 2.73/1.39  tff(c_475, plain, $false, inference(negUnitSimplification, [status(thm)], [c_473, c_157])).
% 2.73/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.73/1.39  
% 2.73/1.39  Inference rules
% 2.73/1.39  ----------------------
% 2.73/1.39  #Ref     : 0
% 2.73/1.39  #Sup     : 85
% 2.73/1.39  #Fact    : 0
% 2.73/1.39  #Define  : 0
% 2.73/1.39  #Split   : 2
% 2.73/1.39  #Chain   : 0
% 2.73/1.39  #Close   : 0
% 2.73/1.39  
% 2.73/1.39  Ordering : KBO
% 2.73/1.39  
% 2.73/1.39  Simplification rules
% 2.73/1.39  ----------------------
% 2.73/1.39  #Subsume      : 1
% 2.73/1.39  #Demod        : 14
% 2.73/1.39  #Tautology    : 13
% 2.73/1.39  #SimpNegUnit  : 1
% 2.73/1.39  #BackRed      : 3
% 2.73/1.39  
% 2.73/1.39  #Partial instantiations: 0
% 2.73/1.39  #Strategies tried      : 1
% 2.73/1.39  
% 2.73/1.39  Timing (in seconds)
% 2.73/1.39  ----------------------
% 2.73/1.39  Preprocessing        : 0.33
% 2.73/1.39  Parsing              : 0.17
% 2.73/1.39  CNF conversion       : 0.03
% 2.73/1.39  Main loop            : 0.30
% 2.73/1.39  Inferencing          : 0.12
% 2.73/1.39  Reduction            : 0.07
% 2.73/1.39  Demodulation         : 0.05
% 2.73/1.39  BG Simplification    : 0.02
% 2.73/1.39  Subsumption          : 0.06
% 2.73/1.39  Abstraction          : 0.02
% 2.73/1.39  MUC search           : 0.00
% 2.73/1.39  Cooper               : 0.00
% 2.73/1.39  Total                : 0.67
% 2.73/1.39  Index Insertion      : 0.00
% 2.73/1.39  Index Deletion       : 0.00
% 2.73/1.39  Index Matching       : 0.00
% 2.73/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
