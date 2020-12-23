%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:29 EST 2020

% Result     : Theorem 3.42s
% Output     : CNFRefutation 3.42s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 100 expanded)
%              Number of leaves         :   32 (  51 expanded)
%              Depth                    :   12
%              Number of atoms          :  109 ( 241 expanded)
%              Number of equality atoms :   13 (  28 expanded)
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

tff(f_47,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t115_funct_2)).

tff(f_45,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_64,axiom,(
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

tff(f_74,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_31,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(f_78,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(c_12,plain,(
    ! [A_12,B_13] : v1_relat_1(k2_zfmisc_1(A_12,B_13)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_50,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_56,plain,(
    ! [B_70,A_71] :
      ( v1_relat_1(B_70)
      | ~ m1_subset_1(B_70,k1_zfmisc_1(A_71))
      | ~ v1_relat_1(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_59,plain,
    ( v1_relat_1('#skF_8')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_50,c_56])).

tff(c_62,plain,(
    v1_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_59])).

tff(c_54,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_16,plain,(
    ! [A_14,B_37,D_52] :
      ( k1_funct_1(A_14,'#skF_4'(A_14,B_37,k9_relat_1(A_14,B_37),D_52)) = D_52
      | ~ r2_hidden(D_52,k9_relat_1(A_14,B_37))
      | ~ v1_funct_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_20,plain,(
    ! [A_14,B_37,D_52] :
      ( r2_hidden('#skF_4'(A_14,B_37,k9_relat_1(A_14,B_37),D_52),k1_relat_1(A_14))
      | ~ r2_hidden(D_52,k9_relat_1(A_14,B_37))
      | ~ v1_funct_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_116,plain,(
    ! [A_101,C_102] :
      ( r2_hidden(k4_tarski(A_101,k1_funct_1(C_102,A_101)),C_102)
      | ~ r2_hidden(A_101,k1_relat_1(C_102))
      | ~ v1_funct_1(C_102)
      | ~ v1_relat_1(C_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_8,plain,(
    ! [C_8,A_5,B_6] :
      ( r2_hidden(C_8,A_5)
      | ~ r2_hidden(C_8,B_6)
      | ~ m1_subset_1(B_6,k1_zfmisc_1(A_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_264,plain,(
    ! [A_136,C_137,A_138] :
      ( r2_hidden(k4_tarski(A_136,k1_funct_1(C_137,A_136)),A_138)
      | ~ m1_subset_1(C_137,k1_zfmisc_1(A_138))
      | ~ r2_hidden(A_136,k1_relat_1(C_137))
      | ~ v1_funct_1(C_137)
      | ~ v1_relat_1(C_137) ) ),
    inference(resolution,[status(thm)],[c_116,c_8])).

tff(c_6,plain,(
    ! [A_1,C_3,B_2,D_4] :
      ( r2_hidden(A_1,C_3)
      | ~ r2_hidden(k4_tarski(A_1,B_2),k2_zfmisc_1(C_3,D_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_302,plain,(
    ! [A_139,C_140,C_141,D_142] :
      ( r2_hidden(A_139,C_140)
      | ~ m1_subset_1(C_141,k1_zfmisc_1(k2_zfmisc_1(C_140,D_142)))
      | ~ r2_hidden(A_139,k1_relat_1(C_141))
      | ~ v1_funct_1(C_141)
      | ~ v1_relat_1(C_141) ) ),
    inference(resolution,[status(thm)],[c_264,c_6])).

tff(c_304,plain,(
    ! [A_139] :
      ( r2_hidden(A_139,'#skF_5')
      | ~ r2_hidden(A_139,k1_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_50,c_302])).

tff(c_314,plain,(
    ! [A_146] :
      ( r2_hidden(A_146,'#skF_5')
      | ~ r2_hidden(A_146,k1_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_54,c_304])).

tff(c_322,plain,(
    ! [B_37,D_52] :
      ( r2_hidden('#skF_4'('#skF_8',B_37,k9_relat_1('#skF_8',B_37),D_52),'#skF_5')
      | ~ r2_hidden(D_52,k9_relat_1('#skF_8',B_37))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_20,c_314])).

tff(c_338,plain,(
    ! [B_37,D_52] :
      ( r2_hidden('#skF_4'('#skF_8',B_37,k9_relat_1('#skF_8',B_37),D_52),'#skF_5')
      | ~ r2_hidden(D_52,k9_relat_1('#skF_8',B_37)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_54,c_322])).

tff(c_182,plain,(
    ! [A_117,B_118,D_119] :
      ( r2_hidden('#skF_4'(A_117,B_118,k9_relat_1(A_117,B_118),D_119),B_118)
      | ~ r2_hidden(D_119,k9_relat_1(A_117,B_118))
      | ~ v1_funct_1(A_117)
      | ~ v1_relat_1(A_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_46,plain,(
    ! [F_67] :
      ( k1_funct_1('#skF_8',F_67) != '#skF_9'
      | ~ r2_hidden(F_67,'#skF_7')
      | ~ r2_hidden(F_67,'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_1335,plain,(
    ! [A_254,D_255] :
      ( k1_funct_1('#skF_8','#skF_4'(A_254,'#skF_7',k9_relat_1(A_254,'#skF_7'),D_255)) != '#skF_9'
      | ~ r2_hidden('#skF_4'(A_254,'#skF_7',k9_relat_1(A_254,'#skF_7'),D_255),'#skF_5')
      | ~ r2_hidden(D_255,k9_relat_1(A_254,'#skF_7'))
      | ~ v1_funct_1(A_254)
      | ~ v1_relat_1(A_254) ) ),
    inference(resolution,[status(thm)],[c_182,c_46])).

tff(c_1343,plain,(
    ! [D_52] :
      ( k1_funct_1('#skF_8','#skF_4'('#skF_8','#skF_7',k9_relat_1('#skF_8','#skF_7'),D_52)) != '#skF_9'
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8')
      | ~ r2_hidden(D_52,k9_relat_1('#skF_8','#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_338,c_1335])).

tff(c_1350,plain,(
    ! [D_256] :
      ( k1_funct_1('#skF_8','#skF_4'('#skF_8','#skF_7',k9_relat_1('#skF_8','#skF_7'),D_256)) != '#skF_9'
      | ~ r2_hidden(D_256,k9_relat_1('#skF_8','#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_54,c_1343])).

tff(c_1354,plain,(
    ! [D_52] :
      ( D_52 != '#skF_9'
      | ~ r2_hidden(D_52,k9_relat_1('#skF_8','#skF_7'))
      | ~ r2_hidden(D_52,k9_relat_1('#skF_8','#skF_7'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_1350])).

tff(c_1357,plain,(
    ~ r2_hidden('#skF_9',k9_relat_1('#skF_8','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_54,c_1354])).

tff(c_97,plain,(
    ! [A_95,B_96,C_97,D_98] :
      ( k7_relset_1(A_95,B_96,C_97,D_98) = k9_relat_1(C_97,D_98)
      | ~ m1_subset_1(C_97,k1_zfmisc_1(k2_zfmisc_1(A_95,B_96))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_100,plain,(
    ! [D_98] : k7_relset_1('#skF_5','#skF_6','#skF_8',D_98) = k9_relat_1('#skF_8',D_98) ),
    inference(resolution,[status(thm)],[c_50,c_97])).

tff(c_48,plain,(
    r2_hidden('#skF_9',k7_relset_1('#skF_5','#skF_6','#skF_8','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_102,plain,(
    r2_hidden('#skF_9',k9_relat_1('#skF_8','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_48])).

tff(c_1359,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1357,c_102])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:28:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.42/1.60  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.42/1.61  
% 3.42/1.61  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.42/1.61  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_9 > #skF_4 > #skF_8 > #skF_3
% 3.42/1.61  
% 3.42/1.61  %Foreground sorts:
% 3.42/1.61  
% 3.42/1.61  
% 3.42/1.61  %Background operators:
% 3.42/1.61  
% 3.42/1.61  
% 3.42/1.61  %Foreground operators:
% 3.42/1.61  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.42/1.61  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.42/1.61  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.42/1.61  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.42/1.61  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.42/1.61  tff('#skF_7', type, '#skF_7': $i).
% 3.42/1.61  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 3.42/1.61  tff('#skF_5', type, '#skF_5': $i).
% 3.42/1.61  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.42/1.61  tff('#skF_6', type, '#skF_6': $i).
% 3.42/1.61  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.42/1.61  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.42/1.61  tff('#skF_9', type, '#skF_9': $i).
% 3.42/1.61  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.42/1.61  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.42/1.61  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 3.42/1.61  tff('#skF_8', type, '#skF_8': $i).
% 3.42/1.61  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.42/1.61  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.42/1.61  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.42/1.61  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.42/1.61  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.42/1.61  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.42/1.61  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.42/1.61  
% 3.42/1.62  tff(f_47, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.42/1.62  tff(f_97, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: ~(r2_hidden(E, k7_relset_1(A, B, D, C)) & (![F]: ~((r2_hidden(F, A) & r2_hidden(F, C)) & (E = k1_funct_1(D, F)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t115_funct_2)).
% 3.42/1.62  tff(f_45, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.42/1.62  tff(f_64, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: ((C = k9_relat_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E]: ((r2_hidden(E, k1_relat_1(A)) & r2_hidden(E, B)) & (D = k1_funct_1(A, E)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d12_funct_1)).
% 3.42/1.62  tff(f_74, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_funct_1)).
% 3.42/1.62  tff(f_38, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 3.42/1.62  tff(f_31, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 3.42/1.62  tff(f_78, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 3.42/1.62  tff(c_12, plain, (![A_12, B_13]: (v1_relat_1(k2_zfmisc_1(A_12, B_13)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.42/1.62  tff(c_50, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.42/1.62  tff(c_56, plain, (![B_70, A_71]: (v1_relat_1(B_70) | ~m1_subset_1(B_70, k1_zfmisc_1(A_71)) | ~v1_relat_1(A_71))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.42/1.62  tff(c_59, plain, (v1_relat_1('#skF_8') | ~v1_relat_1(k2_zfmisc_1('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_50, c_56])).
% 3.42/1.62  tff(c_62, plain, (v1_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_59])).
% 3.42/1.62  tff(c_54, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.42/1.62  tff(c_16, plain, (![A_14, B_37, D_52]: (k1_funct_1(A_14, '#skF_4'(A_14, B_37, k9_relat_1(A_14, B_37), D_52))=D_52 | ~r2_hidden(D_52, k9_relat_1(A_14, B_37)) | ~v1_funct_1(A_14) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.42/1.62  tff(c_20, plain, (![A_14, B_37, D_52]: (r2_hidden('#skF_4'(A_14, B_37, k9_relat_1(A_14, B_37), D_52), k1_relat_1(A_14)) | ~r2_hidden(D_52, k9_relat_1(A_14, B_37)) | ~v1_funct_1(A_14) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.42/1.62  tff(c_116, plain, (![A_101, C_102]: (r2_hidden(k4_tarski(A_101, k1_funct_1(C_102, A_101)), C_102) | ~r2_hidden(A_101, k1_relat_1(C_102)) | ~v1_funct_1(C_102) | ~v1_relat_1(C_102))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.42/1.62  tff(c_8, plain, (![C_8, A_5, B_6]: (r2_hidden(C_8, A_5) | ~r2_hidden(C_8, B_6) | ~m1_subset_1(B_6, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.42/1.62  tff(c_264, plain, (![A_136, C_137, A_138]: (r2_hidden(k4_tarski(A_136, k1_funct_1(C_137, A_136)), A_138) | ~m1_subset_1(C_137, k1_zfmisc_1(A_138)) | ~r2_hidden(A_136, k1_relat_1(C_137)) | ~v1_funct_1(C_137) | ~v1_relat_1(C_137))), inference(resolution, [status(thm)], [c_116, c_8])).
% 3.42/1.62  tff(c_6, plain, (![A_1, C_3, B_2, D_4]: (r2_hidden(A_1, C_3) | ~r2_hidden(k4_tarski(A_1, B_2), k2_zfmisc_1(C_3, D_4)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.42/1.62  tff(c_302, plain, (![A_139, C_140, C_141, D_142]: (r2_hidden(A_139, C_140) | ~m1_subset_1(C_141, k1_zfmisc_1(k2_zfmisc_1(C_140, D_142))) | ~r2_hidden(A_139, k1_relat_1(C_141)) | ~v1_funct_1(C_141) | ~v1_relat_1(C_141))), inference(resolution, [status(thm)], [c_264, c_6])).
% 3.42/1.62  tff(c_304, plain, (![A_139]: (r2_hidden(A_139, '#skF_5') | ~r2_hidden(A_139, k1_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_50, c_302])).
% 3.42/1.62  tff(c_314, plain, (![A_146]: (r2_hidden(A_146, '#skF_5') | ~r2_hidden(A_146, k1_relat_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_54, c_304])).
% 3.42/1.62  tff(c_322, plain, (![B_37, D_52]: (r2_hidden('#skF_4'('#skF_8', B_37, k9_relat_1('#skF_8', B_37), D_52), '#skF_5') | ~r2_hidden(D_52, k9_relat_1('#skF_8', B_37)) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_20, c_314])).
% 3.42/1.62  tff(c_338, plain, (![B_37, D_52]: (r2_hidden('#skF_4'('#skF_8', B_37, k9_relat_1('#skF_8', B_37), D_52), '#skF_5') | ~r2_hidden(D_52, k9_relat_1('#skF_8', B_37)))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_54, c_322])).
% 3.42/1.62  tff(c_182, plain, (![A_117, B_118, D_119]: (r2_hidden('#skF_4'(A_117, B_118, k9_relat_1(A_117, B_118), D_119), B_118) | ~r2_hidden(D_119, k9_relat_1(A_117, B_118)) | ~v1_funct_1(A_117) | ~v1_relat_1(A_117))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.42/1.62  tff(c_46, plain, (![F_67]: (k1_funct_1('#skF_8', F_67)!='#skF_9' | ~r2_hidden(F_67, '#skF_7') | ~r2_hidden(F_67, '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.42/1.62  tff(c_1335, plain, (![A_254, D_255]: (k1_funct_1('#skF_8', '#skF_4'(A_254, '#skF_7', k9_relat_1(A_254, '#skF_7'), D_255))!='#skF_9' | ~r2_hidden('#skF_4'(A_254, '#skF_7', k9_relat_1(A_254, '#skF_7'), D_255), '#skF_5') | ~r2_hidden(D_255, k9_relat_1(A_254, '#skF_7')) | ~v1_funct_1(A_254) | ~v1_relat_1(A_254))), inference(resolution, [status(thm)], [c_182, c_46])).
% 3.42/1.62  tff(c_1343, plain, (![D_52]: (k1_funct_1('#skF_8', '#skF_4'('#skF_8', '#skF_7', k9_relat_1('#skF_8', '#skF_7'), D_52))!='#skF_9' | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~r2_hidden(D_52, k9_relat_1('#skF_8', '#skF_7')))), inference(resolution, [status(thm)], [c_338, c_1335])).
% 3.42/1.62  tff(c_1350, plain, (![D_256]: (k1_funct_1('#skF_8', '#skF_4'('#skF_8', '#skF_7', k9_relat_1('#skF_8', '#skF_7'), D_256))!='#skF_9' | ~r2_hidden(D_256, k9_relat_1('#skF_8', '#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_54, c_1343])).
% 3.42/1.62  tff(c_1354, plain, (![D_52]: (D_52!='#skF_9' | ~r2_hidden(D_52, k9_relat_1('#skF_8', '#skF_7')) | ~r2_hidden(D_52, k9_relat_1('#skF_8', '#skF_7')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_16, c_1350])).
% 3.42/1.62  tff(c_1357, plain, (~r2_hidden('#skF_9', k9_relat_1('#skF_8', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_54, c_1354])).
% 3.42/1.62  tff(c_97, plain, (![A_95, B_96, C_97, D_98]: (k7_relset_1(A_95, B_96, C_97, D_98)=k9_relat_1(C_97, D_98) | ~m1_subset_1(C_97, k1_zfmisc_1(k2_zfmisc_1(A_95, B_96))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.42/1.62  tff(c_100, plain, (![D_98]: (k7_relset_1('#skF_5', '#skF_6', '#skF_8', D_98)=k9_relat_1('#skF_8', D_98))), inference(resolution, [status(thm)], [c_50, c_97])).
% 3.42/1.62  tff(c_48, plain, (r2_hidden('#skF_9', k7_relset_1('#skF_5', '#skF_6', '#skF_8', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.42/1.62  tff(c_102, plain, (r2_hidden('#skF_9', k9_relat_1('#skF_8', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_100, c_48])).
% 3.42/1.62  tff(c_1359, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1357, c_102])).
% 3.42/1.62  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.42/1.62  
% 3.42/1.62  Inference rules
% 3.42/1.62  ----------------------
% 3.42/1.62  #Ref     : 0
% 3.42/1.62  #Sup     : 273
% 3.42/1.62  #Fact    : 0
% 3.42/1.62  #Define  : 0
% 3.42/1.62  #Split   : 14
% 3.42/1.62  #Chain   : 0
% 3.42/1.62  #Close   : 0
% 3.42/1.62  
% 3.42/1.62  Ordering : KBO
% 3.42/1.62  
% 3.42/1.62  Simplification rules
% 3.42/1.62  ----------------------
% 3.42/1.62  #Subsume      : 35
% 3.42/1.62  #Demod        : 63
% 3.42/1.62  #Tautology    : 14
% 3.42/1.62  #SimpNegUnit  : 4
% 3.42/1.62  #BackRed      : 6
% 3.42/1.62  
% 3.42/1.62  #Partial instantiations: 0
% 3.42/1.62  #Strategies tried      : 1
% 3.42/1.62  
% 3.42/1.62  Timing (in seconds)
% 3.42/1.62  ----------------------
% 3.42/1.63  Preprocessing        : 0.32
% 3.42/1.63  Parsing              : 0.16
% 3.42/1.63  CNF conversion       : 0.03
% 3.42/1.63  Main loop            : 0.51
% 3.42/1.63  Inferencing          : 0.19
% 3.42/1.63  Reduction            : 0.13
% 3.42/1.63  Demodulation         : 0.09
% 3.42/1.63  BG Simplification    : 0.03
% 3.42/1.63  Subsumption          : 0.12
% 3.42/1.63  Abstraction          : 0.03
% 3.42/1.63  MUC search           : 0.00
% 3.42/1.63  Cooper               : 0.00
% 3.42/1.63  Total                : 0.86
% 3.42/1.63  Index Insertion      : 0.00
% 3.42/1.63  Index Deletion       : 0.00
% 3.42/1.63  Index Matching       : 0.00
% 3.42/1.63  BG Taut test         : 0.00
%------------------------------------------------------------------------------
