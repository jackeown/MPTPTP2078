%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:34 EST 2020

% Result     : Theorem 3.58s
% Output     : CNFRefutation 3.67s
% Verified   : 
% Statistics : Number of formulae       :   64 (  95 expanded)
%              Number of leaves         :   32 (  49 expanded)
%              Depth                    :   13
%              Number of atoms          :  115 ( 230 expanded)
%              Number of equality atoms :   13 (  27 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_9 > #skF_4 > #skF_8 > #skF_3

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

tff(f_92,negated_conjecture,(
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

tff(f_69,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_55,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( C = k9_relat_1(A,B)
        <=> ! [D] :
              ( r2_hidden(D,C)
            <=> ? [E] :
                  ( r2_hidden(k4_tarski(E,D),A)
                  & r2_hidden(E,B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_relat_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_31,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_73,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(c_44,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_54,plain,(
    ! [C_70,A_71,B_72] :
      ( v1_relat_1(C_70)
      | ~ m1_subset_1(C_70,k1_zfmisc_1(k2_zfmisc_1(A_71,B_72))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_58,plain,(
    v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_44,c_54])).

tff(c_48,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_238,plain,(
    ! [A_135,B_136,D_137] :
      ( r2_hidden(k4_tarski('#skF_4'(A_135,B_136,k9_relat_1(A_135,B_136),D_137),D_137),A_135)
      | ~ r2_hidden(D_137,k9_relat_1(A_135,B_136))
      | ~ v1_relat_1(A_135) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_32,plain,(
    ! [C_55,A_53,B_54] :
      ( k1_funct_1(C_55,A_53) = B_54
      | ~ r2_hidden(k4_tarski(A_53,B_54),C_55)
      | ~ v1_funct_1(C_55)
      | ~ v1_relat_1(C_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_270,plain,(
    ! [A_135,B_136,D_137] :
      ( k1_funct_1(A_135,'#skF_4'(A_135,B_136,k9_relat_1(A_135,B_136),D_137)) = D_137
      | ~ v1_funct_1(A_135)
      | ~ r2_hidden(D_137,k9_relat_1(A_135,B_136))
      | ~ v1_relat_1(A_135) ) ),
    inference(resolution,[status(thm)],[c_238,c_32])).

tff(c_34,plain,(
    ! [A_53,C_55,B_54] :
      ( r2_hidden(A_53,k1_relat_1(C_55))
      | ~ r2_hidden(k4_tarski(A_53,B_54),C_55)
      | ~ v1_funct_1(C_55)
      | ~ v1_relat_1(C_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_271,plain,(
    ! [A_135,B_136,D_137] :
      ( r2_hidden('#skF_4'(A_135,B_136,k9_relat_1(A_135,B_136),D_137),k1_relat_1(A_135))
      | ~ v1_funct_1(A_135)
      | ~ r2_hidden(D_137,k9_relat_1(A_135,B_136))
      | ~ v1_relat_1(A_135) ) ),
    inference(resolution,[status(thm)],[c_238,c_34])).

tff(c_126,plain,(
    ! [A_110,C_111] :
      ( r2_hidden(k4_tarski(A_110,k1_funct_1(C_111,A_110)),C_111)
      | ~ r2_hidden(A_110,k1_relat_1(C_111))
      | ~ v1_funct_1(C_111)
      | ~ v1_relat_1(C_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_8,plain,(
    ! [C_8,A_5,B_6] :
      ( r2_hidden(C_8,A_5)
      | ~ r2_hidden(C_8,B_6)
      | ~ m1_subset_1(B_6,k1_zfmisc_1(A_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_493,plain,(
    ! [A_169,C_170,A_171] :
      ( r2_hidden(k4_tarski(A_169,k1_funct_1(C_170,A_169)),A_171)
      | ~ m1_subset_1(C_170,k1_zfmisc_1(A_171))
      | ~ r2_hidden(A_169,k1_relat_1(C_170))
      | ~ v1_funct_1(C_170)
      | ~ v1_relat_1(C_170) ) ),
    inference(resolution,[status(thm)],[c_126,c_8])).

tff(c_6,plain,(
    ! [A_1,C_3,B_2,D_4] :
      ( r2_hidden(A_1,C_3)
      | ~ r2_hidden(k4_tarski(A_1,B_2),k2_zfmisc_1(C_3,D_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_538,plain,(
    ! [A_174,C_175,C_176,D_177] :
      ( r2_hidden(A_174,C_175)
      | ~ m1_subset_1(C_176,k1_zfmisc_1(k2_zfmisc_1(C_175,D_177)))
      | ~ r2_hidden(A_174,k1_relat_1(C_176))
      | ~ v1_funct_1(C_176)
      | ~ v1_relat_1(C_176) ) ),
    inference(resolution,[status(thm)],[c_493,c_6])).

tff(c_561,plain,(
    ! [A_174] :
      ( r2_hidden(A_174,'#skF_5')
      | ~ r2_hidden(A_174,k1_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_44,c_538])).

tff(c_572,plain,(
    ! [A_178] :
      ( r2_hidden(A_178,'#skF_5')
      | ~ r2_hidden(A_178,k1_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_48,c_561])).

tff(c_580,plain,(
    ! [B_136,D_137] :
      ( r2_hidden('#skF_4'('#skF_8',B_136,k9_relat_1('#skF_8',B_136),D_137),'#skF_5')
      | ~ v1_funct_1('#skF_8')
      | ~ r2_hidden(D_137,k9_relat_1('#skF_8',B_136))
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_271,c_572])).

tff(c_625,plain,(
    ! [B_179,D_180] :
      ( r2_hidden('#skF_4'('#skF_8',B_179,k9_relat_1('#skF_8',B_179),D_180),'#skF_5')
      | ~ r2_hidden(D_180,k9_relat_1('#skF_8',B_179)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_48,c_580])).

tff(c_10,plain,(
    ! [A_9,B_10] :
      ( m1_subset_1(A_9,B_10)
      | ~ r2_hidden(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_635,plain,(
    ! [B_179,D_180] :
      ( m1_subset_1('#skF_4'('#skF_8',B_179,k9_relat_1('#skF_8',B_179),D_180),'#skF_5')
      | ~ r2_hidden(D_180,k9_relat_1('#skF_8',B_179)) ) ),
    inference(resolution,[status(thm)],[c_625,c_10])).

tff(c_194,plain,(
    ! [A_118,B_119,D_120] :
      ( r2_hidden('#skF_4'(A_118,B_119,k9_relat_1(A_118,B_119),D_120),B_119)
      | ~ r2_hidden(D_120,k9_relat_1(A_118,B_119))
      | ~ v1_relat_1(A_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_40,plain,(
    ! [F_67] :
      ( k1_funct_1('#skF_8',F_67) != '#skF_9'
      | ~ r2_hidden(F_67,'#skF_7')
      | ~ m1_subset_1(F_67,'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_1144,plain,(
    ! [A_224,D_225] :
      ( k1_funct_1('#skF_8','#skF_4'(A_224,'#skF_7',k9_relat_1(A_224,'#skF_7'),D_225)) != '#skF_9'
      | ~ m1_subset_1('#skF_4'(A_224,'#skF_7',k9_relat_1(A_224,'#skF_7'),D_225),'#skF_5')
      | ~ r2_hidden(D_225,k9_relat_1(A_224,'#skF_7'))
      | ~ v1_relat_1(A_224) ) ),
    inference(resolution,[status(thm)],[c_194,c_40])).

tff(c_1152,plain,(
    ! [D_180] :
      ( k1_funct_1('#skF_8','#skF_4'('#skF_8','#skF_7',k9_relat_1('#skF_8','#skF_7'),D_180)) != '#skF_9'
      | ~ v1_relat_1('#skF_8')
      | ~ r2_hidden(D_180,k9_relat_1('#skF_8','#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_635,c_1144])).

tff(c_1159,plain,(
    ! [D_226] :
      ( k1_funct_1('#skF_8','#skF_4'('#skF_8','#skF_7',k9_relat_1('#skF_8','#skF_7'),D_226)) != '#skF_9'
      | ~ r2_hidden(D_226,k9_relat_1('#skF_8','#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_1152])).

tff(c_1163,plain,(
    ! [D_137] :
      ( D_137 != '#skF_9'
      | ~ r2_hidden(D_137,k9_relat_1('#skF_8','#skF_7'))
      | ~ v1_funct_1('#skF_8')
      | ~ r2_hidden(D_137,k9_relat_1('#skF_8','#skF_7'))
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_270,c_1159])).

tff(c_1166,plain,(
    ~ r2_hidden('#skF_9',k9_relat_1('#skF_8','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_48,c_1163])).

tff(c_94,plain,(
    ! [A_100,B_101,C_102,D_103] :
      ( k7_relset_1(A_100,B_101,C_102,D_103) = k9_relat_1(C_102,D_103)
      | ~ m1_subset_1(C_102,k1_zfmisc_1(k2_zfmisc_1(A_100,B_101))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_97,plain,(
    ! [D_103] : k7_relset_1('#skF_5','#skF_6','#skF_8',D_103) = k9_relat_1('#skF_8',D_103) ),
    inference(resolution,[status(thm)],[c_44,c_94])).

tff(c_42,plain,(
    r2_hidden('#skF_9',k7_relset_1('#skF_5','#skF_6','#skF_8','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_100,plain,(
    r2_hidden('#skF_9',k9_relat_1('#skF_8','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_42])).

tff(c_1168,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1166,c_100])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:43:08 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.58/1.57  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.58/1.57  
% 3.58/1.57  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.58/1.58  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_9 > #skF_4 > #skF_8 > #skF_3
% 3.58/1.58  
% 3.58/1.58  %Foreground sorts:
% 3.58/1.58  
% 3.58/1.58  
% 3.58/1.58  %Background operators:
% 3.58/1.58  
% 3.58/1.58  
% 3.58/1.58  %Foreground operators:
% 3.58/1.58  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.58/1.58  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.58/1.58  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.58/1.58  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.58/1.58  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.58/1.58  tff('#skF_7', type, '#skF_7': $i).
% 3.58/1.58  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 3.58/1.58  tff('#skF_5', type, '#skF_5': $i).
% 3.58/1.58  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.58/1.58  tff('#skF_6', type, '#skF_6': $i).
% 3.58/1.58  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.58/1.58  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.58/1.58  tff('#skF_9', type, '#skF_9': $i).
% 3.58/1.58  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.58/1.58  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.58/1.58  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 3.58/1.58  tff('#skF_8', type, '#skF_8': $i).
% 3.58/1.58  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.58/1.58  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.58/1.58  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.58/1.58  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.58/1.58  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.58/1.58  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.58/1.58  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.58/1.58  
% 3.67/1.59  tff(f_92, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: ~(r2_hidden(E, k7_relset_1(A, B, D, C)) & (![F]: (m1_subset_1(F, A) => ~(r2_hidden(F, C) & (E = k1_funct_1(D, F))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t116_funct_2)).
% 3.67/1.59  tff(f_69, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.67/1.59  tff(f_55, axiom, (![A]: (v1_relat_1(A) => (![B, C]: ((C = k9_relat_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E]: (r2_hidden(k4_tarski(E, D), A) & r2_hidden(E, B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d13_relat_1)).
% 3.67/1.59  tff(f_65, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_1)).
% 3.67/1.59  tff(f_38, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 3.67/1.59  tff(f_31, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 3.67/1.59  tff(f_42, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 3.67/1.59  tff(f_73, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 3.67/1.59  tff(c_44, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.67/1.59  tff(c_54, plain, (![C_70, A_71, B_72]: (v1_relat_1(C_70) | ~m1_subset_1(C_70, k1_zfmisc_1(k2_zfmisc_1(A_71, B_72))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.67/1.59  tff(c_58, plain, (v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_44, c_54])).
% 3.67/1.59  tff(c_48, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.67/1.59  tff(c_238, plain, (![A_135, B_136, D_137]: (r2_hidden(k4_tarski('#skF_4'(A_135, B_136, k9_relat_1(A_135, B_136), D_137), D_137), A_135) | ~r2_hidden(D_137, k9_relat_1(A_135, B_136)) | ~v1_relat_1(A_135))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.67/1.59  tff(c_32, plain, (![C_55, A_53, B_54]: (k1_funct_1(C_55, A_53)=B_54 | ~r2_hidden(k4_tarski(A_53, B_54), C_55) | ~v1_funct_1(C_55) | ~v1_relat_1(C_55))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.67/1.59  tff(c_270, plain, (![A_135, B_136, D_137]: (k1_funct_1(A_135, '#skF_4'(A_135, B_136, k9_relat_1(A_135, B_136), D_137))=D_137 | ~v1_funct_1(A_135) | ~r2_hidden(D_137, k9_relat_1(A_135, B_136)) | ~v1_relat_1(A_135))), inference(resolution, [status(thm)], [c_238, c_32])).
% 3.67/1.59  tff(c_34, plain, (![A_53, C_55, B_54]: (r2_hidden(A_53, k1_relat_1(C_55)) | ~r2_hidden(k4_tarski(A_53, B_54), C_55) | ~v1_funct_1(C_55) | ~v1_relat_1(C_55))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.67/1.59  tff(c_271, plain, (![A_135, B_136, D_137]: (r2_hidden('#skF_4'(A_135, B_136, k9_relat_1(A_135, B_136), D_137), k1_relat_1(A_135)) | ~v1_funct_1(A_135) | ~r2_hidden(D_137, k9_relat_1(A_135, B_136)) | ~v1_relat_1(A_135))), inference(resolution, [status(thm)], [c_238, c_34])).
% 3.67/1.59  tff(c_126, plain, (![A_110, C_111]: (r2_hidden(k4_tarski(A_110, k1_funct_1(C_111, A_110)), C_111) | ~r2_hidden(A_110, k1_relat_1(C_111)) | ~v1_funct_1(C_111) | ~v1_relat_1(C_111))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.67/1.59  tff(c_8, plain, (![C_8, A_5, B_6]: (r2_hidden(C_8, A_5) | ~r2_hidden(C_8, B_6) | ~m1_subset_1(B_6, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.67/1.59  tff(c_493, plain, (![A_169, C_170, A_171]: (r2_hidden(k4_tarski(A_169, k1_funct_1(C_170, A_169)), A_171) | ~m1_subset_1(C_170, k1_zfmisc_1(A_171)) | ~r2_hidden(A_169, k1_relat_1(C_170)) | ~v1_funct_1(C_170) | ~v1_relat_1(C_170))), inference(resolution, [status(thm)], [c_126, c_8])).
% 3.67/1.59  tff(c_6, plain, (![A_1, C_3, B_2, D_4]: (r2_hidden(A_1, C_3) | ~r2_hidden(k4_tarski(A_1, B_2), k2_zfmisc_1(C_3, D_4)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.67/1.59  tff(c_538, plain, (![A_174, C_175, C_176, D_177]: (r2_hidden(A_174, C_175) | ~m1_subset_1(C_176, k1_zfmisc_1(k2_zfmisc_1(C_175, D_177))) | ~r2_hidden(A_174, k1_relat_1(C_176)) | ~v1_funct_1(C_176) | ~v1_relat_1(C_176))), inference(resolution, [status(thm)], [c_493, c_6])).
% 3.67/1.59  tff(c_561, plain, (![A_174]: (r2_hidden(A_174, '#skF_5') | ~r2_hidden(A_174, k1_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_44, c_538])).
% 3.67/1.59  tff(c_572, plain, (![A_178]: (r2_hidden(A_178, '#skF_5') | ~r2_hidden(A_178, k1_relat_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_48, c_561])).
% 3.67/1.59  tff(c_580, plain, (![B_136, D_137]: (r2_hidden('#skF_4'('#skF_8', B_136, k9_relat_1('#skF_8', B_136), D_137), '#skF_5') | ~v1_funct_1('#skF_8') | ~r2_hidden(D_137, k9_relat_1('#skF_8', B_136)) | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_271, c_572])).
% 3.67/1.59  tff(c_625, plain, (![B_179, D_180]: (r2_hidden('#skF_4'('#skF_8', B_179, k9_relat_1('#skF_8', B_179), D_180), '#skF_5') | ~r2_hidden(D_180, k9_relat_1('#skF_8', B_179)))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_48, c_580])).
% 3.67/1.59  tff(c_10, plain, (![A_9, B_10]: (m1_subset_1(A_9, B_10) | ~r2_hidden(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.67/1.59  tff(c_635, plain, (![B_179, D_180]: (m1_subset_1('#skF_4'('#skF_8', B_179, k9_relat_1('#skF_8', B_179), D_180), '#skF_5') | ~r2_hidden(D_180, k9_relat_1('#skF_8', B_179)))), inference(resolution, [status(thm)], [c_625, c_10])).
% 3.67/1.59  tff(c_194, plain, (![A_118, B_119, D_120]: (r2_hidden('#skF_4'(A_118, B_119, k9_relat_1(A_118, B_119), D_120), B_119) | ~r2_hidden(D_120, k9_relat_1(A_118, B_119)) | ~v1_relat_1(A_118))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.67/1.59  tff(c_40, plain, (![F_67]: (k1_funct_1('#skF_8', F_67)!='#skF_9' | ~r2_hidden(F_67, '#skF_7') | ~m1_subset_1(F_67, '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.67/1.59  tff(c_1144, plain, (![A_224, D_225]: (k1_funct_1('#skF_8', '#skF_4'(A_224, '#skF_7', k9_relat_1(A_224, '#skF_7'), D_225))!='#skF_9' | ~m1_subset_1('#skF_4'(A_224, '#skF_7', k9_relat_1(A_224, '#skF_7'), D_225), '#skF_5') | ~r2_hidden(D_225, k9_relat_1(A_224, '#skF_7')) | ~v1_relat_1(A_224))), inference(resolution, [status(thm)], [c_194, c_40])).
% 3.67/1.59  tff(c_1152, plain, (![D_180]: (k1_funct_1('#skF_8', '#skF_4'('#skF_8', '#skF_7', k9_relat_1('#skF_8', '#skF_7'), D_180))!='#skF_9' | ~v1_relat_1('#skF_8') | ~r2_hidden(D_180, k9_relat_1('#skF_8', '#skF_7')))), inference(resolution, [status(thm)], [c_635, c_1144])).
% 3.67/1.59  tff(c_1159, plain, (![D_226]: (k1_funct_1('#skF_8', '#skF_4'('#skF_8', '#skF_7', k9_relat_1('#skF_8', '#skF_7'), D_226))!='#skF_9' | ~r2_hidden(D_226, k9_relat_1('#skF_8', '#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_1152])).
% 3.67/1.59  tff(c_1163, plain, (![D_137]: (D_137!='#skF_9' | ~r2_hidden(D_137, k9_relat_1('#skF_8', '#skF_7')) | ~v1_funct_1('#skF_8') | ~r2_hidden(D_137, k9_relat_1('#skF_8', '#skF_7')) | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_270, c_1159])).
% 3.67/1.59  tff(c_1166, plain, (~r2_hidden('#skF_9', k9_relat_1('#skF_8', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_48, c_1163])).
% 3.67/1.59  tff(c_94, plain, (![A_100, B_101, C_102, D_103]: (k7_relset_1(A_100, B_101, C_102, D_103)=k9_relat_1(C_102, D_103) | ~m1_subset_1(C_102, k1_zfmisc_1(k2_zfmisc_1(A_100, B_101))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.67/1.59  tff(c_97, plain, (![D_103]: (k7_relset_1('#skF_5', '#skF_6', '#skF_8', D_103)=k9_relat_1('#skF_8', D_103))), inference(resolution, [status(thm)], [c_44, c_94])).
% 3.67/1.59  tff(c_42, plain, (r2_hidden('#skF_9', k7_relset_1('#skF_5', '#skF_6', '#skF_8', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.67/1.59  tff(c_100, plain, (r2_hidden('#skF_9', k9_relat_1('#skF_8', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_97, c_42])).
% 3.67/1.59  tff(c_1168, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1166, c_100])).
% 3.67/1.59  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.67/1.59  
% 3.67/1.59  Inference rules
% 3.67/1.59  ----------------------
% 3.67/1.59  #Ref     : 0
% 3.67/1.59  #Sup     : 241
% 3.67/1.59  #Fact    : 0
% 3.67/1.59  #Define  : 0
% 3.67/1.59  #Split   : 4
% 3.67/1.59  #Chain   : 0
% 3.67/1.59  #Close   : 0
% 3.67/1.59  
% 3.67/1.59  Ordering : KBO
% 3.67/1.59  
% 3.67/1.59  Simplification rules
% 3.67/1.59  ----------------------
% 3.67/1.59  #Subsume      : 11
% 3.67/1.59  #Demod        : 27
% 3.67/1.59  #Tautology    : 9
% 3.67/1.59  #SimpNegUnit  : 1
% 3.67/1.59  #BackRed      : 4
% 3.67/1.59  
% 3.67/1.59  #Partial instantiations: 0
% 3.67/1.59  #Strategies tried      : 1
% 3.67/1.59  
% 3.67/1.59  Timing (in seconds)
% 3.67/1.59  ----------------------
% 3.67/1.59  Preprocessing        : 0.34
% 3.67/1.59  Parsing              : 0.17
% 3.67/1.59  CNF conversion       : 0.03
% 3.67/1.59  Main loop            : 0.49
% 3.67/1.59  Inferencing          : 0.18
% 3.67/1.59  Reduction            : 0.13
% 3.67/1.59  Demodulation         : 0.09
% 3.67/1.59  BG Simplification    : 0.03
% 3.67/1.59  Subsumption          : 0.11
% 3.67/1.59  Abstraction          : 0.03
% 3.67/1.59  MUC search           : 0.00
% 3.67/1.59  Cooper               : 0.00
% 3.67/1.59  Total                : 0.85
% 3.67/1.59  Index Insertion      : 0.00
% 3.67/1.59  Index Deletion       : 0.00
% 3.67/1.59  Index Matching       : 0.00
% 3.67/1.59  BG Taut test         : 0.00
%------------------------------------------------------------------------------
