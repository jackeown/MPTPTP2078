%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:26 EST 2020

% Result     : Theorem 2.44s
% Output     : CNFRefutation 2.44s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 193 expanded)
%              Number of leaves         :   34 (  84 expanded)
%              Depth                    :   13
%              Number of atoms          :  108 ( 478 expanded)
%              Number of equality atoms :   12 (  60 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(f_47,axiom,(
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

tff(f_39,axiom,(
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

tff(f_45,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_78,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(c_14,plain,(
    ! [A_11,B_12] : v1_relat_1(k2_zfmisc_1(A_11,B_12)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_40,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_46,plain,(
    ! [B_36,A_37] :
      ( v1_relat_1(B_36)
      | ~ m1_subset_1(B_36,k1_zfmisc_1(A_37))
      | ~ v1_relat_1(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_49,plain,
    ( v1_relat_1('#skF_6')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_40,c_46])).

tff(c_52,plain,(
    v1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_49])).

tff(c_67,plain,(
    ! [C_44,A_45,B_46] :
      ( v4_relat_1(C_44,A_45)
      | ~ m1_subset_1(C_44,k1_zfmisc_1(k2_zfmisc_1(A_45,B_46))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_71,plain,(
    v4_relat_1('#skF_6','#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_67])).

tff(c_12,plain,(
    ! [B_10,A_9] :
      ( r1_tarski(k1_relat_1(B_10),A_9)
      | ~ v4_relat_1(B_10,A_9)
      | ~ v1_relat_1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_128,plain,(
    ! [A_71,B_72,C_73,D_74] :
      ( k7_relset_1(A_71,B_72,C_73,D_74) = k9_relat_1(C_73,D_74)
      | ~ m1_subset_1(C_73,k1_zfmisc_1(k2_zfmisc_1(A_71,B_72))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_131,plain,(
    ! [D_74] : k7_relset_1('#skF_3','#skF_4','#skF_6',D_74) = k9_relat_1('#skF_6',D_74) ),
    inference(resolution,[status(thm)],[c_40,c_128])).

tff(c_38,plain,(
    r2_hidden('#skF_7',k7_relset_1('#skF_3','#skF_4','#skF_6','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_137,plain,(
    r2_hidden('#skF_7',k9_relat_1('#skF_6','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_38])).

tff(c_44,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_189,plain,(
    ! [A_87,B_88,C_89] :
      ( r2_hidden(k4_tarski('#skF_2'(A_87,B_88,C_89),A_87),C_89)
      | ~ r2_hidden(A_87,k9_relat_1(C_89,B_88))
      | ~ v1_relat_1(C_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_26,plain,(
    ! [C_21,A_19,B_20] :
      ( k1_funct_1(C_21,A_19) = B_20
      | ~ r2_hidden(k4_tarski(A_19,B_20),C_21)
      | ~ v1_funct_1(C_21)
      | ~ v1_relat_1(C_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_215,plain,(
    ! [C_94,A_95,B_96] :
      ( k1_funct_1(C_94,'#skF_2'(A_95,B_96,C_94)) = A_95
      | ~ v1_funct_1(C_94)
      | ~ r2_hidden(A_95,k9_relat_1(C_94,B_96))
      | ~ v1_relat_1(C_94) ) ),
    inference(resolution,[status(thm)],[c_189,c_26])).

tff(c_226,plain,
    ( k1_funct_1('#skF_6','#skF_2'('#skF_7','#skF_5','#skF_6')) = '#skF_7'
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_137,c_215])).

tff(c_241,plain,(
    k1_funct_1('#skF_6','#skF_2'('#skF_7','#skF_5','#skF_6')) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_44,c_226])).

tff(c_22,plain,(
    ! [A_13,B_14,C_15] :
      ( r2_hidden('#skF_2'(A_13,B_14,C_15),k1_relat_1(C_15))
      | ~ r2_hidden(A_13,k9_relat_1(C_15,B_14))
      | ~ v1_relat_1(C_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_24,plain,(
    ! [A_19,C_21] :
      ( r2_hidden(k4_tarski(A_19,k1_funct_1(C_21,A_19)),C_21)
      | ~ r2_hidden(A_19,k1_relat_1(C_21))
      | ~ v1_funct_1(C_21)
      | ~ v1_relat_1(C_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_248,plain,
    ( r2_hidden(k4_tarski('#skF_2'('#skF_7','#skF_5','#skF_6'),'#skF_7'),'#skF_6')
    | ~ r2_hidden('#skF_2'('#skF_7','#skF_5','#skF_6'),k1_relat_1('#skF_6'))
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_241,c_24])).

tff(c_252,plain,
    ( r2_hidden(k4_tarski('#skF_2'('#skF_7','#skF_5','#skF_6'),'#skF_7'),'#skF_6')
    | ~ r2_hidden('#skF_2'('#skF_7','#skF_5','#skF_6'),k1_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_44,c_248])).

tff(c_266,plain,(
    ~ r2_hidden('#skF_2'('#skF_7','#skF_5','#skF_6'),k1_relat_1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_252])).

tff(c_272,plain,
    ( ~ r2_hidden('#skF_7',k9_relat_1('#skF_6','#skF_5'))
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_22,c_266])).

tff(c_279,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_137,c_272])).

tff(c_281,plain,(
    r2_hidden('#skF_2'('#skF_7','#skF_5','#skF_6'),k1_relat_1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_252])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_284,plain,(
    ! [B_2] :
      ( r2_hidden('#skF_2'('#skF_7','#skF_5','#skF_6'),B_2)
      | ~ r1_tarski(k1_relat_1('#skF_6'),B_2) ) ),
    inference(resolution,[status(thm)],[c_281,c_2])).

tff(c_119,plain,(
    ! [A_68,B_69,C_70] :
      ( r2_hidden('#skF_2'(A_68,B_69,C_70),B_69)
      | ~ r2_hidden(A_68,k9_relat_1(C_70,B_69))
      | ~ v1_relat_1(C_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_36,plain,(
    ! [F_33] :
      ( k1_funct_1('#skF_6',F_33) != '#skF_7'
      | ~ r2_hidden(F_33,'#skF_5')
      | ~ r2_hidden(F_33,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_350,plain,(
    ! [A_104,C_105] :
      ( k1_funct_1('#skF_6','#skF_2'(A_104,'#skF_5',C_105)) != '#skF_7'
      | ~ r2_hidden('#skF_2'(A_104,'#skF_5',C_105),'#skF_3')
      | ~ r2_hidden(A_104,k9_relat_1(C_105,'#skF_5'))
      | ~ v1_relat_1(C_105) ) ),
    inference(resolution,[status(thm)],[c_119,c_36])).

tff(c_354,plain,
    ( k1_funct_1('#skF_6','#skF_2'('#skF_7','#skF_5','#skF_6')) != '#skF_7'
    | ~ r2_hidden('#skF_7',k9_relat_1('#skF_6','#skF_5'))
    | ~ v1_relat_1('#skF_6')
    | ~ r1_tarski(k1_relat_1('#skF_6'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_284,c_350])).

tff(c_361,plain,(
    ~ r1_tarski(k1_relat_1('#skF_6'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_137,c_241,c_354])).

tff(c_365,plain,
    ( ~ v4_relat_1('#skF_6','#skF_3')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_12,c_361])).

tff(c_369,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_71,c_365])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n020.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 20:16:52 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.44/1.33  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.44/1.34  
% 2.44/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.44/1.34  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4 > #skF_1
% 2.44/1.34  
% 2.44/1.34  %Foreground sorts:
% 2.44/1.34  
% 2.44/1.34  
% 2.44/1.34  %Background operators:
% 2.44/1.34  
% 2.44/1.34  
% 2.44/1.34  %Foreground operators:
% 2.44/1.34  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.44/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.44/1.34  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.44/1.34  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.44/1.34  tff('#skF_7', type, '#skF_7': $i).
% 2.44/1.34  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.44/1.34  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.44/1.34  tff('#skF_5', type, '#skF_5': $i).
% 2.44/1.34  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.44/1.34  tff('#skF_6', type, '#skF_6': $i).
% 2.44/1.34  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.44/1.34  tff('#skF_3', type, '#skF_3': $i).
% 2.44/1.34  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.44/1.34  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.44/1.34  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.44/1.34  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.44/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.44/1.34  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.44/1.34  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.44/1.34  tff('#skF_4', type, '#skF_4': $i).
% 2.44/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.44/1.34  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.44/1.34  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.44/1.34  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.44/1.34  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.44/1.34  
% 2.44/1.35  tff(f_47, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.44/1.35  tff(f_97, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: ~(r2_hidden(E, k7_relset_1(A, B, D, C)) & (![F]: ~((r2_hidden(F, A) & r2_hidden(F, C)) & (E = k1_funct_1(D, F)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t115_funct_2)).
% 2.44/1.35  tff(f_39, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.44/1.35  tff(f_74, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.44/1.35  tff(f_45, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 2.44/1.35  tff(f_78, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 2.44/1.35  tff(f_58, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_relat_1)).
% 2.44/1.35  tff(f_68, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_1)).
% 2.44/1.35  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.44/1.35  tff(c_14, plain, (![A_11, B_12]: (v1_relat_1(k2_zfmisc_1(A_11, B_12)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.44/1.35  tff(c_40, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.44/1.35  tff(c_46, plain, (![B_36, A_37]: (v1_relat_1(B_36) | ~m1_subset_1(B_36, k1_zfmisc_1(A_37)) | ~v1_relat_1(A_37))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.44/1.35  tff(c_49, plain, (v1_relat_1('#skF_6') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_40, c_46])).
% 2.44/1.35  tff(c_52, plain, (v1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_49])).
% 2.44/1.35  tff(c_67, plain, (![C_44, A_45, B_46]: (v4_relat_1(C_44, A_45) | ~m1_subset_1(C_44, k1_zfmisc_1(k2_zfmisc_1(A_45, B_46))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.44/1.35  tff(c_71, plain, (v4_relat_1('#skF_6', '#skF_3')), inference(resolution, [status(thm)], [c_40, c_67])).
% 2.44/1.35  tff(c_12, plain, (![B_10, A_9]: (r1_tarski(k1_relat_1(B_10), A_9) | ~v4_relat_1(B_10, A_9) | ~v1_relat_1(B_10))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.44/1.35  tff(c_128, plain, (![A_71, B_72, C_73, D_74]: (k7_relset_1(A_71, B_72, C_73, D_74)=k9_relat_1(C_73, D_74) | ~m1_subset_1(C_73, k1_zfmisc_1(k2_zfmisc_1(A_71, B_72))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.44/1.35  tff(c_131, plain, (![D_74]: (k7_relset_1('#skF_3', '#skF_4', '#skF_6', D_74)=k9_relat_1('#skF_6', D_74))), inference(resolution, [status(thm)], [c_40, c_128])).
% 2.44/1.35  tff(c_38, plain, (r2_hidden('#skF_7', k7_relset_1('#skF_3', '#skF_4', '#skF_6', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.44/1.35  tff(c_137, plain, (r2_hidden('#skF_7', k9_relat_1('#skF_6', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_131, c_38])).
% 2.44/1.35  tff(c_44, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.44/1.35  tff(c_189, plain, (![A_87, B_88, C_89]: (r2_hidden(k4_tarski('#skF_2'(A_87, B_88, C_89), A_87), C_89) | ~r2_hidden(A_87, k9_relat_1(C_89, B_88)) | ~v1_relat_1(C_89))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.44/1.35  tff(c_26, plain, (![C_21, A_19, B_20]: (k1_funct_1(C_21, A_19)=B_20 | ~r2_hidden(k4_tarski(A_19, B_20), C_21) | ~v1_funct_1(C_21) | ~v1_relat_1(C_21))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.44/1.35  tff(c_215, plain, (![C_94, A_95, B_96]: (k1_funct_1(C_94, '#skF_2'(A_95, B_96, C_94))=A_95 | ~v1_funct_1(C_94) | ~r2_hidden(A_95, k9_relat_1(C_94, B_96)) | ~v1_relat_1(C_94))), inference(resolution, [status(thm)], [c_189, c_26])).
% 2.44/1.35  tff(c_226, plain, (k1_funct_1('#skF_6', '#skF_2'('#skF_7', '#skF_5', '#skF_6'))='#skF_7' | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_137, c_215])).
% 2.44/1.35  tff(c_241, plain, (k1_funct_1('#skF_6', '#skF_2'('#skF_7', '#skF_5', '#skF_6'))='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_44, c_226])).
% 2.44/1.35  tff(c_22, plain, (![A_13, B_14, C_15]: (r2_hidden('#skF_2'(A_13, B_14, C_15), k1_relat_1(C_15)) | ~r2_hidden(A_13, k9_relat_1(C_15, B_14)) | ~v1_relat_1(C_15))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.44/1.35  tff(c_24, plain, (![A_19, C_21]: (r2_hidden(k4_tarski(A_19, k1_funct_1(C_21, A_19)), C_21) | ~r2_hidden(A_19, k1_relat_1(C_21)) | ~v1_funct_1(C_21) | ~v1_relat_1(C_21))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.44/1.35  tff(c_248, plain, (r2_hidden(k4_tarski('#skF_2'('#skF_7', '#skF_5', '#skF_6'), '#skF_7'), '#skF_6') | ~r2_hidden('#skF_2'('#skF_7', '#skF_5', '#skF_6'), k1_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_241, c_24])).
% 2.44/1.35  tff(c_252, plain, (r2_hidden(k4_tarski('#skF_2'('#skF_7', '#skF_5', '#skF_6'), '#skF_7'), '#skF_6') | ~r2_hidden('#skF_2'('#skF_7', '#skF_5', '#skF_6'), k1_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_44, c_248])).
% 2.44/1.35  tff(c_266, plain, (~r2_hidden('#skF_2'('#skF_7', '#skF_5', '#skF_6'), k1_relat_1('#skF_6'))), inference(splitLeft, [status(thm)], [c_252])).
% 2.44/1.35  tff(c_272, plain, (~r2_hidden('#skF_7', k9_relat_1('#skF_6', '#skF_5')) | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_22, c_266])).
% 2.44/1.35  tff(c_279, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_137, c_272])).
% 2.44/1.35  tff(c_281, plain, (r2_hidden('#skF_2'('#skF_7', '#skF_5', '#skF_6'), k1_relat_1('#skF_6'))), inference(splitRight, [status(thm)], [c_252])).
% 2.44/1.35  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.44/1.35  tff(c_284, plain, (![B_2]: (r2_hidden('#skF_2'('#skF_7', '#skF_5', '#skF_6'), B_2) | ~r1_tarski(k1_relat_1('#skF_6'), B_2))), inference(resolution, [status(thm)], [c_281, c_2])).
% 2.44/1.35  tff(c_119, plain, (![A_68, B_69, C_70]: (r2_hidden('#skF_2'(A_68, B_69, C_70), B_69) | ~r2_hidden(A_68, k9_relat_1(C_70, B_69)) | ~v1_relat_1(C_70))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.44/1.35  tff(c_36, plain, (![F_33]: (k1_funct_1('#skF_6', F_33)!='#skF_7' | ~r2_hidden(F_33, '#skF_5') | ~r2_hidden(F_33, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.44/1.35  tff(c_350, plain, (![A_104, C_105]: (k1_funct_1('#skF_6', '#skF_2'(A_104, '#skF_5', C_105))!='#skF_7' | ~r2_hidden('#skF_2'(A_104, '#skF_5', C_105), '#skF_3') | ~r2_hidden(A_104, k9_relat_1(C_105, '#skF_5')) | ~v1_relat_1(C_105))), inference(resolution, [status(thm)], [c_119, c_36])).
% 2.44/1.35  tff(c_354, plain, (k1_funct_1('#skF_6', '#skF_2'('#skF_7', '#skF_5', '#skF_6'))!='#skF_7' | ~r2_hidden('#skF_7', k9_relat_1('#skF_6', '#skF_5')) | ~v1_relat_1('#skF_6') | ~r1_tarski(k1_relat_1('#skF_6'), '#skF_3')), inference(resolution, [status(thm)], [c_284, c_350])).
% 2.44/1.35  tff(c_361, plain, (~r1_tarski(k1_relat_1('#skF_6'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_137, c_241, c_354])).
% 2.44/1.35  tff(c_365, plain, (~v4_relat_1('#skF_6', '#skF_3') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_12, c_361])).
% 2.44/1.35  tff(c_369, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_71, c_365])).
% 2.44/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.44/1.35  
% 2.44/1.35  Inference rules
% 2.44/1.35  ----------------------
% 2.44/1.35  #Ref     : 0
% 2.44/1.35  #Sup     : 69
% 2.44/1.35  #Fact    : 0
% 2.44/1.35  #Define  : 0
% 2.44/1.35  #Split   : 4
% 2.44/1.35  #Chain   : 0
% 2.44/1.35  #Close   : 0
% 2.44/1.35  
% 2.44/1.35  Ordering : KBO
% 2.44/1.35  
% 2.44/1.35  Simplification rules
% 2.44/1.35  ----------------------
% 2.44/1.35  #Subsume      : 4
% 2.44/1.35  #Demod        : 25
% 2.44/1.35  #Tautology    : 12
% 2.44/1.35  #SimpNegUnit  : 0
% 2.44/1.35  #BackRed      : 2
% 2.44/1.35  
% 2.44/1.35  #Partial instantiations: 0
% 2.44/1.35  #Strategies tried      : 1
% 2.44/1.35  
% 2.44/1.35  Timing (in seconds)
% 2.44/1.35  ----------------------
% 2.44/1.36  Preprocessing        : 0.32
% 2.44/1.36  Parsing              : 0.17
% 2.44/1.36  CNF conversion       : 0.02
% 2.44/1.36  Main loop            : 0.27
% 2.44/1.36  Inferencing          : 0.10
% 2.44/1.36  Reduction            : 0.07
% 2.44/1.36  Demodulation         : 0.06
% 2.44/1.36  BG Simplification    : 0.02
% 2.44/1.36  Subsumption          : 0.06
% 2.44/1.36  Abstraction          : 0.02
% 2.44/1.36  MUC search           : 0.00
% 2.44/1.36  Cooper               : 0.00
% 2.44/1.36  Total                : 0.63
% 2.44/1.36  Index Insertion      : 0.00
% 2.44/1.36  Index Deletion       : 0.00
% 2.44/1.36  Index Matching       : 0.00
% 2.44/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
