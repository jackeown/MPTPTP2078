%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:26 EST 2020

% Result     : Theorem 2.77s
% Output     : CNFRefutation 2.77s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 127 expanded)
%              Number of leaves         :   35 (  62 expanded)
%              Depth                    :    9
%              Number of atoms          :  104 ( 330 expanded)
%              Number of equality atoms :   12 (  41 expanded)
%              Maximal formula depth    :   14 (   4 average)
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

tff(f_51,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_97,negated_conjecture,(
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

tff(f_43,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_68,axiom,(
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

tff(f_78,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(c_14,plain,(
    ! [A_12,B_13] : v1_relat_1(k2_zfmisc_1(A_12,B_13)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_50,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_66,plain,(
    ! [B_74,A_75] :
      ( v1_relat_1(B_74)
      | ~ m1_subset_1(B_74,k1_zfmisc_1(A_75))
      | ~ v1_relat_1(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_72,plain,
    ( v1_relat_1('#skF_8')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_50,c_66])).

tff(c_76,plain,(
    v1_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_72])).

tff(c_95,plain,(
    ! [C_83,A_84,B_85] :
      ( v4_relat_1(C_83,A_84)
      | ~ m1_subset_1(C_83,k1_zfmisc_1(k2_zfmisc_1(A_84,B_85))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_104,plain,(
    v4_relat_1('#skF_8','#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_95])).

tff(c_12,plain,(
    ! [B_11,A_10] :
      ( r1_tarski(k1_relat_1(B_11),A_10)
      | ~ v4_relat_1(B_11,A_10)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( m1_subset_1(A_5,k1_zfmisc_1(B_6))
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_54,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_18,plain,(
    ! [A_14,B_37,D_52] :
      ( k1_funct_1(A_14,'#skF_4'(A_14,B_37,k9_relat_1(A_14,B_37),D_52)) = D_52
      | ~ r2_hidden(D_52,k9_relat_1(A_14,B_37))
      | ~ v1_funct_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_222,plain,(
    ! [A_133,B_134,D_135] :
      ( r2_hidden('#skF_4'(A_133,B_134,k9_relat_1(A_133,B_134),D_135),k1_relat_1(A_133))
      | ~ r2_hidden(D_135,k9_relat_1(A_133,B_134))
      | ~ v1_funct_1(A_133)
      | ~ v1_relat_1(A_133) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_2,plain,(
    ! [C_4,A_1,B_2] :
      ( r2_hidden(C_4,A_1)
      | ~ r2_hidden(C_4,B_2)
      | ~ m1_subset_1(B_2,k1_zfmisc_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_322,plain,(
    ! [A_164,B_165,D_166,A_167] :
      ( r2_hidden('#skF_4'(A_164,B_165,k9_relat_1(A_164,B_165),D_166),A_167)
      | ~ m1_subset_1(k1_relat_1(A_164),k1_zfmisc_1(A_167))
      | ~ r2_hidden(D_166,k9_relat_1(A_164,B_165))
      | ~ v1_funct_1(A_164)
      | ~ v1_relat_1(A_164) ) ),
    inference(resolution,[status(thm)],[c_222,c_2])).

tff(c_195,plain,(
    ! [A_118,B_119,D_120] :
      ( r2_hidden('#skF_4'(A_118,B_119,k9_relat_1(A_118,B_119),D_120),B_119)
      | ~ r2_hidden(D_120,k9_relat_1(A_118,B_119))
      | ~ v1_funct_1(A_118)
      | ~ v1_relat_1(A_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_46,plain,(
    ! [F_67] :
      ( k1_funct_1('#skF_8',F_67) != '#skF_9'
      | ~ r2_hidden(F_67,'#skF_7')
      | ~ r2_hidden(F_67,'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_203,plain,(
    ! [A_118,D_120] :
      ( k1_funct_1('#skF_8','#skF_4'(A_118,'#skF_7',k9_relat_1(A_118,'#skF_7'),D_120)) != '#skF_9'
      | ~ r2_hidden('#skF_4'(A_118,'#skF_7',k9_relat_1(A_118,'#skF_7'),D_120),'#skF_5')
      | ~ r2_hidden(D_120,k9_relat_1(A_118,'#skF_7'))
      | ~ v1_funct_1(A_118)
      | ~ v1_relat_1(A_118) ) ),
    inference(resolution,[status(thm)],[c_195,c_46])).

tff(c_389,plain,(
    ! [A_180,D_181] :
      ( k1_funct_1('#skF_8','#skF_4'(A_180,'#skF_7',k9_relat_1(A_180,'#skF_7'),D_181)) != '#skF_9'
      | ~ m1_subset_1(k1_relat_1(A_180),k1_zfmisc_1('#skF_5'))
      | ~ r2_hidden(D_181,k9_relat_1(A_180,'#skF_7'))
      | ~ v1_funct_1(A_180)
      | ~ v1_relat_1(A_180) ) ),
    inference(resolution,[status(thm)],[c_322,c_203])).

tff(c_392,plain,(
    ! [D_52] :
      ( D_52 != '#skF_9'
      | ~ m1_subset_1(k1_relat_1('#skF_8'),k1_zfmisc_1('#skF_5'))
      | ~ r2_hidden(D_52,k9_relat_1('#skF_8','#skF_7'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8')
      | ~ r2_hidden(D_52,k9_relat_1('#skF_8','#skF_7'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_389])).

tff(c_394,plain,(
    ! [D_52] :
      ( D_52 != '#skF_9'
      | ~ m1_subset_1(k1_relat_1('#skF_8'),k1_zfmisc_1('#skF_5'))
      | ~ r2_hidden(D_52,k9_relat_1('#skF_8','#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_54,c_76,c_54,c_392])).

tff(c_395,plain,(
    ~ m1_subset_1(k1_relat_1('#skF_8'),k1_zfmisc_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_394])).

tff(c_401,plain,(
    ~ r1_tarski(k1_relat_1('#skF_8'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_6,c_395])).

tff(c_404,plain,
    ( ~ v4_relat_1('#skF_8','#skF_5')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_12,c_401])).

tff(c_408,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_104,c_404])).

tff(c_429,plain,(
    ~ r2_hidden('#skF_9',k9_relat_1('#skF_8','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_394])).

tff(c_154,plain,(
    ! [A_101,B_102,C_103,D_104] :
      ( k7_relset_1(A_101,B_102,C_103,D_104) = k9_relat_1(C_103,D_104)
      | ~ m1_subset_1(C_103,k1_zfmisc_1(k2_zfmisc_1(A_101,B_102))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_161,plain,(
    ! [D_104] : k7_relset_1('#skF_5','#skF_6','#skF_8',D_104) = k9_relat_1('#skF_8',D_104) ),
    inference(resolution,[status(thm)],[c_50,c_154])).

tff(c_48,plain,(
    r2_hidden('#skF_9',k7_relset_1('#skF_5','#skF_6','#skF_8','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_163,plain,(
    r2_hidden('#skF_9',k9_relat_1('#skF_8','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_161,c_48])).

tff(c_431,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_429,c_163])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:39:32 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.77/1.40  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.77/1.41  
% 2.77/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.77/1.41  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k9_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_9 > #skF_4 > #skF_8 > #skF_3
% 2.77/1.41  
% 2.77/1.41  %Foreground sorts:
% 2.77/1.41  
% 2.77/1.41  
% 2.77/1.41  %Background operators:
% 2.77/1.41  
% 2.77/1.41  
% 2.77/1.41  %Foreground operators:
% 2.77/1.41  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.77/1.41  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.77/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.77/1.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.77/1.41  tff('#skF_7', type, '#skF_7': $i).
% 2.77/1.41  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.77/1.41  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.77/1.41  tff('#skF_5', type, '#skF_5': $i).
% 2.77/1.41  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.77/1.41  tff('#skF_6', type, '#skF_6': $i).
% 2.77/1.41  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.77/1.41  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.77/1.41  tff('#skF_9', type, '#skF_9': $i).
% 2.77/1.41  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.77/1.41  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.77/1.41  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.77/1.41  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 2.77/1.41  tff('#skF_8', type, '#skF_8': $i).
% 2.77/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.77/1.41  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.77/1.41  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.77/1.41  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.77/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.77/1.41  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.77/1.41  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.77/1.41  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.77/1.41  
% 2.77/1.42  tff(f_51, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.77/1.42  tff(f_97, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: ~(r2_hidden(E, k7_relset_1(A, B, D, C)) & (![F]: ~((r2_hidden(F, A) & r2_hidden(F, C)) & (E = k1_funct_1(D, F)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t115_funct_2)).
% 2.77/1.42  tff(f_43, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.77/1.42  tff(f_74, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.77/1.42  tff(f_49, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 2.77/1.42  tff(f_36, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.77/1.42  tff(f_68, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: ((C = k9_relat_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E]: ((r2_hidden(E, k1_relat_1(A)) & r2_hidden(E, B)) & (D = k1_funct_1(A, E)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_funct_1)).
% 2.77/1.42  tff(f_32, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 2.77/1.42  tff(f_78, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 2.77/1.42  tff(c_14, plain, (![A_12, B_13]: (v1_relat_1(k2_zfmisc_1(A_12, B_13)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.77/1.42  tff(c_50, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.77/1.42  tff(c_66, plain, (![B_74, A_75]: (v1_relat_1(B_74) | ~m1_subset_1(B_74, k1_zfmisc_1(A_75)) | ~v1_relat_1(A_75))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.77/1.42  tff(c_72, plain, (v1_relat_1('#skF_8') | ~v1_relat_1(k2_zfmisc_1('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_50, c_66])).
% 2.77/1.42  tff(c_76, plain, (v1_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_72])).
% 2.77/1.42  tff(c_95, plain, (![C_83, A_84, B_85]: (v4_relat_1(C_83, A_84) | ~m1_subset_1(C_83, k1_zfmisc_1(k2_zfmisc_1(A_84, B_85))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.77/1.42  tff(c_104, plain, (v4_relat_1('#skF_8', '#skF_5')), inference(resolution, [status(thm)], [c_50, c_95])).
% 2.77/1.42  tff(c_12, plain, (![B_11, A_10]: (r1_tarski(k1_relat_1(B_11), A_10) | ~v4_relat_1(B_11, A_10) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.77/1.42  tff(c_6, plain, (![A_5, B_6]: (m1_subset_1(A_5, k1_zfmisc_1(B_6)) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.77/1.42  tff(c_54, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.77/1.42  tff(c_18, plain, (![A_14, B_37, D_52]: (k1_funct_1(A_14, '#skF_4'(A_14, B_37, k9_relat_1(A_14, B_37), D_52))=D_52 | ~r2_hidden(D_52, k9_relat_1(A_14, B_37)) | ~v1_funct_1(A_14) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.77/1.42  tff(c_222, plain, (![A_133, B_134, D_135]: (r2_hidden('#skF_4'(A_133, B_134, k9_relat_1(A_133, B_134), D_135), k1_relat_1(A_133)) | ~r2_hidden(D_135, k9_relat_1(A_133, B_134)) | ~v1_funct_1(A_133) | ~v1_relat_1(A_133))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.77/1.42  tff(c_2, plain, (![C_4, A_1, B_2]: (r2_hidden(C_4, A_1) | ~r2_hidden(C_4, B_2) | ~m1_subset_1(B_2, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.77/1.42  tff(c_322, plain, (![A_164, B_165, D_166, A_167]: (r2_hidden('#skF_4'(A_164, B_165, k9_relat_1(A_164, B_165), D_166), A_167) | ~m1_subset_1(k1_relat_1(A_164), k1_zfmisc_1(A_167)) | ~r2_hidden(D_166, k9_relat_1(A_164, B_165)) | ~v1_funct_1(A_164) | ~v1_relat_1(A_164))), inference(resolution, [status(thm)], [c_222, c_2])).
% 2.77/1.42  tff(c_195, plain, (![A_118, B_119, D_120]: (r2_hidden('#skF_4'(A_118, B_119, k9_relat_1(A_118, B_119), D_120), B_119) | ~r2_hidden(D_120, k9_relat_1(A_118, B_119)) | ~v1_funct_1(A_118) | ~v1_relat_1(A_118))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.77/1.42  tff(c_46, plain, (![F_67]: (k1_funct_1('#skF_8', F_67)!='#skF_9' | ~r2_hidden(F_67, '#skF_7') | ~r2_hidden(F_67, '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.77/1.42  tff(c_203, plain, (![A_118, D_120]: (k1_funct_1('#skF_8', '#skF_4'(A_118, '#skF_7', k9_relat_1(A_118, '#skF_7'), D_120))!='#skF_9' | ~r2_hidden('#skF_4'(A_118, '#skF_7', k9_relat_1(A_118, '#skF_7'), D_120), '#skF_5') | ~r2_hidden(D_120, k9_relat_1(A_118, '#skF_7')) | ~v1_funct_1(A_118) | ~v1_relat_1(A_118))), inference(resolution, [status(thm)], [c_195, c_46])).
% 2.77/1.42  tff(c_389, plain, (![A_180, D_181]: (k1_funct_1('#skF_8', '#skF_4'(A_180, '#skF_7', k9_relat_1(A_180, '#skF_7'), D_181))!='#skF_9' | ~m1_subset_1(k1_relat_1(A_180), k1_zfmisc_1('#skF_5')) | ~r2_hidden(D_181, k9_relat_1(A_180, '#skF_7')) | ~v1_funct_1(A_180) | ~v1_relat_1(A_180))), inference(resolution, [status(thm)], [c_322, c_203])).
% 2.77/1.42  tff(c_392, plain, (![D_52]: (D_52!='#skF_9' | ~m1_subset_1(k1_relat_1('#skF_8'), k1_zfmisc_1('#skF_5')) | ~r2_hidden(D_52, k9_relat_1('#skF_8', '#skF_7')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~r2_hidden(D_52, k9_relat_1('#skF_8', '#skF_7')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_18, c_389])).
% 2.77/1.42  tff(c_394, plain, (![D_52]: (D_52!='#skF_9' | ~m1_subset_1(k1_relat_1('#skF_8'), k1_zfmisc_1('#skF_5')) | ~r2_hidden(D_52, k9_relat_1('#skF_8', '#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_54, c_76, c_54, c_392])).
% 2.77/1.42  tff(c_395, plain, (~m1_subset_1(k1_relat_1('#skF_8'), k1_zfmisc_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_394])).
% 2.77/1.42  tff(c_401, plain, (~r1_tarski(k1_relat_1('#skF_8'), '#skF_5')), inference(resolution, [status(thm)], [c_6, c_395])).
% 2.77/1.42  tff(c_404, plain, (~v4_relat_1('#skF_8', '#skF_5') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_12, c_401])).
% 2.77/1.42  tff(c_408, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_76, c_104, c_404])).
% 2.77/1.42  tff(c_429, plain, (~r2_hidden('#skF_9', k9_relat_1('#skF_8', '#skF_7'))), inference(splitRight, [status(thm)], [c_394])).
% 2.77/1.42  tff(c_154, plain, (![A_101, B_102, C_103, D_104]: (k7_relset_1(A_101, B_102, C_103, D_104)=k9_relat_1(C_103, D_104) | ~m1_subset_1(C_103, k1_zfmisc_1(k2_zfmisc_1(A_101, B_102))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.77/1.42  tff(c_161, plain, (![D_104]: (k7_relset_1('#skF_5', '#skF_6', '#skF_8', D_104)=k9_relat_1('#skF_8', D_104))), inference(resolution, [status(thm)], [c_50, c_154])).
% 2.77/1.42  tff(c_48, plain, (r2_hidden('#skF_9', k7_relset_1('#skF_5', '#skF_6', '#skF_8', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.77/1.42  tff(c_163, plain, (r2_hidden('#skF_9', k9_relat_1('#skF_8', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_161, c_48])).
% 2.77/1.42  tff(c_431, plain, $false, inference(negUnitSimplification, [status(thm)], [c_429, c_163])).
% 2.77/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.77/1.42  
% 2.77/1.42  Inference rules
% 2.77/1.42  ----------------------
% 2.77/1.42  #Ref     : 0
% 2.77/1.42  #Sup     : 80
% 2.77/1.42  #Fact    : 0
% 2.77/1.42  #Define  : 0
% 2.77/1.42  #Split   : 3
% 2.77/1.42  #Chain   : 0
% 2.77/1.42  #Close   : 0
% 2.77/1.42  
% 2.77/1.42  Ordering : KBO
% 2.77/1.42  
% 2.77/1.42  Simplification rules
% 2.77/1.42  ----------------------
% 2.77/1.42  #Subsume      : 5
% 2.77/1.42  #Demod        : 18
% 2.77/1.42  #Tautology    : 13
% 2.77/1.42  #SimpNegUnit  : 1
% 2.77/1.42  #BackRed      : 3
% 2.77/1.42  
% 2.77/1.42  #Partial instantiations: 0
% 2.77/1.42  #Strategies tried      : 1
% 2.77/1.42  
% 2.77/1.42  Timing (in seconds)
% 2.77/1.42  ----------------------
% 2.77/1.43  Preprocessing        : 0.32
% 2.77/1.43  Parsing              : 0.16
% 2.77/1.43  CNF conversion       : 0.03
% 2.77/1.43  Main loop            : 0.32
% 2.77/1.43  Inferencing          : 0.12
% 2.77/1.43  Reduction            : 0.08
% 2.77/1.43  Demodulation         : 0.06
% 2.77/1.43  BG Simplification    : 0.02
% 2.77/1.43  Subsumption          : 0.07
% 2.77/1.43  Abstraction          : 0.02
% 2.77/1.43  MUC search           : 0.00
% 2.77/1.43  Cooper               : 0.00
% 2.77/1.43  Total                : 0.67
% 2.77/1.43  Index Insertion      : 0.00
% 2.77/1.43  Index Deletion       : 0.00
% 2.77/1.43  Index Matching       : 0.00
% 2.77/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
