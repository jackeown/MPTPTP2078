%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:40 EST 2020

% Result     : Theorem 2.39s
% Output     : CNFRefutation 2.64s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 131 expanded)
%              Number of leaves         :   43 (  65 expanded)
%              Depth                    :    9
%              Number of atoms          :  104 ( 241 expanded)
%              Number of equality atoms :   50 (  95 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k3_enumset1 > k2_enumset1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_1 > #skF_4

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

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i * $i ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k11_relat_1,type,(
    k11_relat_1: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i * $i ) > $i )).

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

tff(f_65,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_119,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_tarski(A),B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => k2_relset_1(k1_tarski(A),B,C) = k1_tarski(k1_funct_1(C,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_funct_2)).

tff(f_58,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_85,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_107,axiom,(
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

tff(f_27,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_29,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_51,axiom,(
    ! [A,B,C,D,E] :
      ( E = k2_enumset1(A,B,C,D)
    <=> ! [F] :
          ( r2_hidden(F,E)
        <=> ~ ( F != A
              & F != B
              & F != C
              & F != D ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_enumset1)).

tff(f_81,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => k11_relat_1(B,A) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_funct_1)).

tff(f_89,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_63,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] : k11_relat_1(A,B) = k9_relat_1(A,k1_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).

tff(f_73,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k7_relat_1(A,k1_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_relat_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(c_44,plain,(
    ! [A_25,B_26] : v1_relat_1(k2_zfmisc_1(A_25,B_26)) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_72,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_3'),'#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_109,plain,(
    ! [B_63,A_64] :
      ( v1_relat_1(B_63)
      | ~ m1_subset_1(B_63,k1_zfmisc_1(A_64))
      | ~ v1_relat_1(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_112,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1(k1_tarski('#skF_3'),'#skF_4')) ),
    inference(resolution,[status(thm)],[c_72,c_109])).

tff(c_115,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_112])).

tff(c_76,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_70,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_74,plain,(
    v1_funct_2('#skF_5',k1_tarski('#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_201,plain,(
    ! [A_93,B_94,C_95] :
      ( k1_relset_1(A_93,B_94,C_95) = k1_relat_1(C_95)
      | ~ m1_subset_1(C_95,k1_zfmisc_1(k2_zfmisc_1(A_93,B_94))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_205,plain,(
    k1_relset_1(k1_tarski('#skF_3'),'#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_72,c_201])).

tff(c_294,plain,(
    ! [B_123,A_124,C_125] :
      ( k1_xboole_0 = B_123
      | k1_relset_1(A_124,B_123,C_125) = A_124
      | ~ v1_funct_2(C_125,A_124,B_123)
      | ~ m1_subset_1(C_125,k1_zfmisc_1(k2_zfmisc_1(A_124,B_123))) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_297,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1(k1_tarski('#skF_3'),'#skF_4','#skF_5') = k1_tarski('#skF_3')
    | ~ v1_funct_2('#skF_5',k1_tarski('#skF_3'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_72,c_294])).

tff(c_300,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_tarski('#skF_3') = k1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_205,c_297])).

tff(c_301,plain,(
    k1_tarski('#skF_3') = k1_relat_1('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_300])).

tff(c_2,plain,(
    ! [A_1] : k2_tarski(A_1,A_1) = k1_tarski(A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_2,B_3] : k1_enumset1(A_2,A_2,B_3) = k2_tarski(A_2,B_3) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_137,plain,(
    ! [A_69,B_70,C_71] : k2_enumset1(A_69,A_69,B_70,C_71) = k1_enumset1(A_69,B_70,C_71) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_16,plain,(
    ! [F_18,A_11,C_13,D_14] : r2_hidden(F_18,k2_enumset1(A_11,F_18,C_13,D_14)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_158,plain,(
    ! [A_72,B_73,C_74] : r2_hidden(A_72,k1_enumset1(A_72,B_73,C_74)) ),
    inference(superposition,[status(thm),theory(equality)],[c_137,c_16])).

tff(c_171,plain,(
    ! [A_79,B_80] : r2_hidden(A_79,k2_tarski(A_79,B_80)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_158])).

tff(c_174,plain,(
    ! [A_1] : r2_hidden(A_1,k1_tarski(A_1)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_171])).

tff(c_312,plain,(
    r2_hidden('#skF_3',k1_relat_1('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_301,c_174])).

tff(c_50,plain,(
    ! [B_31,A_30] :
      ( k1_tarski(k1_funct_1(B_31,A_30)) = k11_relat_1(B_31,A_30)
      | ~ r2_hidden(A_30,k1_relat_1(B_31))
      | ~ v1_funct_1(B_31)
      | ~ v1_relat_1(B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_321,plain,
    ( k1_tarski(k1_funct_1('#skF_5','#skF_3')) = k11_relat_1('#skF_5','#skF_3')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_312,c_50])).

tff(c_324,plain,(
    k1_tarski(k1_funct_1('#skF_5','#skF_3')) = k11_relat_1('#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_115,c_76,c_321])).

tff(c_186,plain,(
    ! [A_88,B_89,C_90] :
      ( k2_relset_1(A_88,B_89,C_90) = k2_relat_1(C_90)
      | ~ m1_subset_1(C_90,k1_zfmisc_1(k2_zfmisc_1(A_88,B_89))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_190,plain,(
    k2_relset_1(k1_tarski('#skF_3'),'#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_72,c_186])).

tff(c_68,plain,(
    k2_relset_1(k1_tarski('#skF_3'),'#skF_4','#skF_5') != k1_tarski(k1_funct_1('#skF_5','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_196,plain,(
    k1_tarski(k1_funct_1('#skF_5','#skF_3')) != k2_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_190,c_68])).

tff(c_364,plain,(
    k11_relat_1('#skF_5','#skF_3') != k2_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_324,c_196])).

tff(c_42,plain,(
    ! [A_22,B_24] :
      ( k9_relat_1(A_22,k1_tarski(B_24)) = k11_relat_1(A_22,B_24)
      | ~ v1_relat_1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_378,plain,(
    ! [A_131] :
      ( k9_relat_1(A_131,k1_relat_1('#skF_5')) = k11_relat_1(A_131,'#skF_3')
      | ~ v1_relat_1(A_131) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_301,c_42])).

tff(c_48,plain,(
    ! [A_29] :
      ( k7_relat_1(A_29,k1_relat_1(A_29)) = A_29
      | ~ v1_relat_1(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_125,plain,(
    ! [B_67,A_68] :
      ( k2_relat_1(k7_relat_1(B_67,A_68)) = k9_relat_1(B_67,A_68)
      | ~ v1_relat_1(B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_134,plain,(
    ! [A_29] :
      ( k9_relat_1(A_29,k1_relat_1(A_29)) = k2_relat_1(A_29)
      | ~ v1_relat_1(A_29)
      | ~ v1_relat_1(A_29) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_125])).

tff(c_385,plain,
    ( k11_relat_1('#skF_5','#skF_3') = k2_relat_1('#skF_5')
    | ~ v1_relat_1('#skF_5')
    | ~ v1_relat_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_378,c_134])).

tff(c_395,plain,(
    k11_relat_1('#skF_5','#skF_3') = k2_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_115,c_115,c_115,c_385])).

tff(c_397,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_364,c_395])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 19:06:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.39/1.47  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.64/1.48  
% 2.64/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.64/1.48  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k3_enumset1 > k2_enumset1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_1 > #skF_4
% 2.64/1.48  
% 2.64/1.48  %Foreground sorts:
% 2.64/1.48  
% 2.64/1.48  
% 2.64/1.48  %Background operators:
% 2.64/1.48  
% 2.64/1.48  
% 2.64/1.48  %Foreground operators:
% 2.64/1.48  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.64/1.48  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.64/1.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.64/1.48  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.64/1.48  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.64/1.48  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i) > $i).
% 2.64/1.48  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.64/1.48  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.64/1.48  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.64/1.48  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.64/1.48  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.64/1.48  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.64/1.48  tff('#skF_5', type, '#skF_5': $i).
% 2.64/1.48  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.64/1.48  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 2.64/1.48  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.64/1.48  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.64/1.48  tff('#skF_3', type, '#skF_3': $i).
% 2.64/1.48  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.64/1.48  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.64/1.48  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.64/1.48  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i) > $i).
% 2.64/1.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.64/1.48  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.64/1.48  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.64/1.48  tff('#skF_4', type, '#skF_4': $i).
% 2.64/1.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.64/1.48  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.64/1.48  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.64/1.48  
% 2.64/1.49  tff(f_65, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.64/1.49  tff(f_119, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_tarski(A), B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => (k2_relset_1(k1_tarski(A), B, C) = k1_tarski(k1_funct_1(C, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_funct_2)).
% 2.64/1.49  tff(f_58, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.64/1.49  tff(f_85, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.64/1.49  tff(f_107, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 2.64/1.49  tff(f_27, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.64/1.49  tff(f_29, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.64/1.49  tff(f_31, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 2.64/1.49  tff(f_51, axiom, (![A, B, C, D, E]: ((E = k2_enumset1(A, B, C, D)) <=> (![F]: (r2_hidden(F, E) <=> ~(((~(F = A) & ~(F = B)) & ~(F = C)) & ~(F = D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_enumset1)).
% 2.64/1.49  tff(f_81, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => (k11_relat_1(B, A) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t117_funct_1)).
% 2.64/1.49  tff(f_89, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.64/1.49  tff(f_63, axiom, (![A]: (v1_relat_1(A) => (![B]: (k11_relat_1(A, B) = k9_relat_1(A, k1_tarski(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d16_relat_1)).
% 2.64/1.49  tff(f_73, axiom, (![A]: (v1_relat_1(A) => (k7_relat_1(A, k1_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_relat_1)).
% 2.64/1.49  tff(f_69, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 2.64/1.49  tff(c_44, plain, (![A_25, B_26]: (v1_relat_1(k2_zfmisc_1(A_25, B_26)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.64/1.49  tff(c_72, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_3'), '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_119])).
% 2.64/1.49  tff(c_109, plain, (![B_63, A_64]: (v1_relat_1(B_63) | ~m1_subset_1(B_63, k1_zfmisc_1(A_64)) | ~v1_relat_1(A_64))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.64/1.49  tff(c_112, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1(k1_tarski('#skF_3'), '#skF_4'))), inference(resolution, [status(thm)], [c_72, c_109])).
% 2.64/1.49  tff(c_115, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_112])).
% 2.64/1.49  tff(c_76, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_119])).
% 2.64/1.49  tff(c_70, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_119])).
% 2.64/1.49  tff(c_74, plain, (v1_funct_2('#skF_5', k1_tarski('#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_119])).
% 2.64/1.49  tff(c_201, plain, (![A_93, B_94, C_95]: (k1_relset_1(A_93, B_94, C_95)=k1_relat_1(C_95) | ~m1_subset_1(C_95, k1_zfmisc_1(k2_zfmisc_1(A_93, B_94))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.64/1.49  tff(c_205, plain, (k1_relset_1(k1_tarski('#skF_3'), '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_72, c_201])).
% 2.64/1.49  tff(c_294, plain, (![B_123, A_124, C_125]: (k1_xboole_0=B_123 | k1_relset_1(A_124, B_123, C_125)=A_124 | ~v1_funct_2(C_125, A_124, B_123) | ~m1_subset_1(C_125, k1_zfmisc_1(k2_zfmisc_1(A_124, B_123))))), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.64/1.49  tff(c_297, plain, (k1_xboole_0='#skF_4' | k1_relset_1(k1_tarski('#skF_3'), '#skF_4', '#skF_5')=k1_tarski('#skF_3') | ~v1_funct_2('#skF_5', k1_tarski('#skF_3'), '#skF_4')), inference(resolution, [status(thm)], [c_72, c_294])).
% 2.64/1.49  tff(c_300, plain, (k1_xboole_0='#skF_4' | k1_tarski('#skF_3')=k1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_205, c_297])).
% 2.64/1.49  tff(c_301, plain, (k1_tarski('#skF_3')=k1_relat_1('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_70, c_300])).
% 2.64/1.49  tff(c_2, plain, (![A_1]: (k2_tarski(A_1, A_1)=k1_tarski(A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.64/1.49  tff(c_4, plain, (![A_2, B_3]: (k1_enumset1(A_2, A_2, B_3)=k2_tarski(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.64/1.49  tff(c_137, plain, (![A_69, B_70, C_71]: (k2_enumset1(A_69, A_69, B_70, C_71)=k1_enumset1(A_69, B_70, C_71))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.64/1.49  tff(c_16, plain, (![F_18, A_11, C_13, D_14]: (r2_hidden(F_18, k2_enumset1(A_11, F_18, C_13, D_14)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.64/1.49  tff(c_158, plain, (![A_72, B_73, C_74]: (r2_hidden(A_72, k1_enumset1(A_72, B_73, C_74)))), inference(superposition, [status(thm), theory('equality')], [c_137, c_16])).
% 2.64/1.49  tff(c_171, plain, (![A_79, B_80]: (r2_hidden(A_79, k2_tarski(A_79, B_80)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_158])).
% 2.64/1.49  tff(c_174, plain, (![A_1]: (r2_hidden(A_1, k1_tarski(A_1)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_171])).
% 2.64/1.49  tff(c_312, plain, (r2_hidden('#skF_3', k1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_301, c_174])).
% 2.64/1.49  tff(c_50, plain, (![B_31, A_30]: (k1_tarski(k1_funct_1(B_31, A_30))=k11_relat_1(B_31, A_30) | ~r2_hidden(A_30, k1_relat_1(B_31)) | ~v1_funct_1(B_31) | ~v1_relat_1(B_31))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.64/1.49  tff(c_321, plain, (k1_tarski(k1_funct_1('#skF_5', '#skF_3'))=k11_relat_1('#skF_5', '#skF_3') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_312, c_50])).
% 2.64/1.49  tff(c_324, plain, (k1_tarski(k1_funct_1('#skF_5', '#skF_3'))=k11_relat_1('#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_115, c_76, c_321])).
% 2.64/1.49  tff(c_186, plain, (![A_88, B_89, C_90]: (k2_relset_1(A_88, B_89, C_90)=k2_relat_1(C_90) | ~m1_subset_1(C_90, k1_zfmisc_1(k2_zfmisc_1(A_88, B_89))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.64/1.49  tff(c_190, plain, (k2_relset_1(k1_tarski('#skF_3'), '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_72, c_186])).
% 2.64/1.49  tff(c_68, plain, (k2_relset_1(k1_tarski('#skF_3'), '#skF_4', '#skF_5')!=k1_tarski(k1_funct_1('#skF_5', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_119])).
% 2.64/1.49  tff(c_196, plain, (k1_tarski(k1_funct_1('#skF_5', '#skF_3'))!=k2_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_190, c_68])).
% 2.64/1.49  tff(c_364, plain, (k11_relat_1('#skF_5', '#skF_3')!=k2_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_324, c_196])).
% 2.64/1.49  tff(c_42, plain, (![A_22, B_24]: (k9_relat_1(A_22, k1_tarski(B_24))=k11_relat_1(A_22, B_24) | ~v1_relat_1(A_22))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.64/1.49  tff(c_378, plain, (![A_131]: (k9_relat_1(A_131, k1_relat_1('#skF_5'))=k11_relat_1(A_131, '#skF_3') | ~v1_relat_1(A_131))), inference(superposition, [status(thm), theory('equality')], [c_301, c_42])).
% 2.64/1.49  tff(c_48, plain, (![A_29]: (k7_relat_1(A_29, k1_relat_1(A_29))=A_29 | ~v1_relat_1(A_29))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.64/1.49  tff(c_125, plain, (![B_67, A_68]: (k2_relat_1(k7_relat_1(B_67, A_68))=k9_relat_1(B_67, A_68) | ~v1_relat_1(B_67))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.64/1.49  tff(c_134, plain, (![A_29]: (k9_relat_1(A_29, k1_relat_1(A_29))=k2_relat_1(A_29) | ~v1_relat_1(A_29) | ~v1_relat_1(A_29))), inference(superposition, [status(thm), theory('equality')], [c_48, c_125])).
% 2.64/1.49  tff(c_385, plain, (k11_relat_1('#skF_5', '#skF_3')=k2_relat_1('#skF_5') | ~v1_relat_1('#skF_5') | ~v1_relat_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_378, c_134])).
% 2.64/1.49  tff(c_395, plain, (k11_relat_1('#skF_5', '#skF_3')=k2_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_115, c_115, c_115, c_385])).
% 2.64/1.49  tff(c_397, plain, $false, inference(negUnitSimplification, [status(thm)], [c_364, c_395])).
% 2.64/1.49  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.64/1.49  
% 2.64/1.49  Inference rules
% 2.64/1.49  ----------------------
% 2.64/1.49  #Ref     : 0
% 2.64/1.49  #Sup     : 72
% 2.64/1.49  #Fact    : 0
% 2.64/1.49  #Define  : 0
% 2.64/1.49  #Split   : 0
% 2.64/1.49  #Chain   : 0
% 2.64/1.49  #Close   : 0
% 2.64/1.49  
% 2.64/1.49  Ordering : KBO
% 2.64/1.49  
% 2.64/1.49  Simplification rules
% 2.64/1.49  ----------------------
% 2.64/1.49  #Subsume      : 0
% 2.64/1.49  #Demod        : 27
% 2.64/1.49  #Tautology    : 48
% 2.64/1.49  #SimpNegUnit  : 5
% 2.64/1.49  #BackRed      : 6
% 2.64/1.49  
% 2.64/1.49  #Partial instantiations: 0
% 2.64/1.49  #Strategies tried      : 1
% 2.64/1.49  
% 2.64/1.49  Timing (in seconds)
% 2.64/1.49  ----------------------
% 2.64/1.50  Preprocessing        : 0.39
% 2.64/1.50  Parsing              : 0.18
% 2.64/1.50  CNF conversion       : 0.03
% 2.64/1.50  Main loop            : 0.23
% 2.64/1.50  Inferencing          : 0.08
% 2.64/1.50  Reduction            : 0.07
% 2.64/1.50  Demodulation         : 0.05
% 2.64/1.50  BG Simplification    : 0.02
% 2.64/1.50  Subsumption          : 0.04
% 2.64/1.50  Abstraction          : 0.01
% 2.64/1.50  MUC search           : 0.00
% 2.64/1.50  Cooper               : 0.00
% 2.64/1.50  Total                : 0.65
% 2.64/1.50  Index Insertion      : 0.00
% 2.64/1.50  Index Deletion       : 0.00
% 2.64/1.50  Index Matching       : 0.00
% 2.64/1.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
