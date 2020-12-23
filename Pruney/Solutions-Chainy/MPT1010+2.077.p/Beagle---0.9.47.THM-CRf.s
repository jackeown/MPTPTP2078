%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:15 EST 2020

% Result     : Theorem 2.62s
% Output     : CNFRefutation 2.62s
% Verified   : 
% Statistics : Number of formulae       :   72 (  82 expanded)
%              Number of leaves         :   43 (  50 expanded)
%              Depth                    :    8
%              Number of atoms          :   92 ( 130 expanded)
%              Number of equality atoms :   39 (  46 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_122,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,k1_tarski(B))
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
       => ( r2_hidden(C,A)
         => k1_funct_1(D,C) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_2)).

tff(f_89,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_31,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_93,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_111,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_85,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B,C] :
          ( ( r2_hidden(B,k1_relat_1(A))
           => ( C = k1_funct_1(A,B)
            <=> r2_hidden(k4_tarski(B,C),A) ) )
          & ( ~ r2_hidden(B,k1_relat_1(A))
           => ( C = k1_funct_1(A,B)
            <=> C = k1_xboole_0 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_funct_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_51,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,k1_tarski(D)))
    <=> ( r2_hidden(A,C)
        & B = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t129_zfmisc_1)).

tff(c_62,plain,(
    k1_funct_1('#skF_4','#skF_3') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_64,plain,(
    r2_hidden('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_66,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1',k1_tarski('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_158,plain,(
    ! [C_76,A_77,B_78] :
      ( v1_relat_1(C_76)
      | ~ m1_subset_1(C_76,k1_zfmisc_1(k2_zfmisc_1(A_77,B_78))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_162,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_66,c_158])).

tff(c_70,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_6,plain,(
    ! [A_5] : k5_xboole_0(A_5,A_5) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_137,plain,(
    ! [A_73,B_74] : k5_xboole_0(A_73,k3_xboole_0(A_73,B_74)) = k4_xboole_0(A_73,B_74) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_146,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k4_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_137])).

tff(c_149,plain,(
    ! [A_1] : k4_xboole_0(A_1,A_1) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_146])).

tff(c_28,plain,(
    ! [B_39] : k4_xboole_0(k1_tarski(B_39),k1_tarski(B_39)) != k1_tarski(B_39) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_150,plain,(
    ! [B_39] : k1_tarski(B_39) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_149,c_28])).

tff(c_68,plain,(
    v1_funct_2('#skF_4','#skF_1',k1_tarski('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_228,plain,(
    ! [A_106,B_107,C_108] :
      ( k1_relset_1(A_106,B_107,C_108) = k1_relat_1(C_108)
      | ~ m1_subset_1(C_108,k1_zfmisc_1(k2_zfmisc_1(A_106,B_107))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_232,plain,(
    k1_relset_1('#skF_1',k1_tarski('#skF_2'),'#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_66,c_228])).

tff(c_290,plain,(
    ! [B_139,A_140,C_141] :
      ( k1_xboole_0 = B_139
      | k1_relset_1(A_140,B_139,C_141) = A_140
      | ~ v1_funct_2(C_141,A_140,B_139)
      | ~ m1_subset_1(C_141,k1_zfmisc_1(k2_zfmisc_1(A_140,B_139))) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_293,plain,
    ( k1_tarski('#skF_2') = k1_xboole_0
    | k1_relset_1('#skF_1',k1_tarski('#skF_2'),'#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1',k1_tarski('#skF_2')) ),
    inference(resolution,[status(thm)],[c_66,c_290])).

tff(c_296,plain,
    ( k1_tarski('#skF_2') = k1_xboole_0
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_232,c_293])).

tff(c_297,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_150,c_296])).

tff(c_250,plain,(
    ! [B_121,A_122] :
      ( r2_hidden(k4_tarski(B_121,k1_funct_1(A_122,B_121)),A_122)
      | ~ r2_hidden(B_121,k1_relat_1(A_122))
      | ~ v1_funct_1(A_122)
      | ~ v1_relat_1(A_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_32,plain,(
    ! [C_43,A_40,B_41] :
      ( r2_hidden(C_43,A_40)
      | ~ r2_hidden(C_43,B_41)
      | ~ m1_subset_1(B_41,k1_zfmisc_1(A_40)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_344,plain,(
    ! [B_155,A_156,A_157] :
      ( r2_hidden(k4_tarski(B_155,k1_funct_1(A_156,B_155)),A_157)
      | ~ m1_subset_1(A_156,k1_zfmisc_1(A_157))
      | ~ r2_hidden(B_155,k1_relat_1(A_156))
      | ~ v1_funct_1(A_156)
      | ~ v1_relat_1(A_156) ) ),
    inference(resolution,[status(thm)],[c_250,c_32])).

tff(c_24,plain,(
    ! [D_37,B_35,A_34,C_36] :
      ( D_37 = B_35
      | ~ r2_hidden(k4_tarski(A_34,B_35),k2_zfmisc_1(C_36,k1_tarski(D_37))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_368,plain,(
    ! [A_162,B_163,D_164,C_165] :
      ( k1_funct_1(A_162,B_163) = D_164
      | ~ m1_subset_1(A_162,k1_zfmisc_1(k2_zfmisc_1(C_165,k1_tarski(D_164))))
      | ~ r2_hidden(B_163,k1_relat_1(A_162))
      | ~ v1_funct_1(A_162)
      | ~ v1_relat_1(A_162) ) ),
    inference(resolution,[status(thm)],[c_344,c_24])).

tff(c_370,plain,(
    ! [B_163] :
      ( k1_funct_1('#skF_4',B_163) = '#skF_2'
      | ~ r2_hidden(B_163,k1_relat_1('#skF_4'))
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_66,c_368])).

tff(c_374,plain,(
    ! [B_166] :
      ( k1_funct_1('#skF_4',B_166) = '#skF_2'
      | ~ r2_hidden(B_166,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_162,c_70,c_297,c_370])).

tff(c_388,plain,(
    k1_funct_1('#skF_4','#skF_3') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_64,c_374])).

tff(c_395,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_388])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:59:20 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.62/1.33  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.62/1.33  
% 2.62/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.62/1.34  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.62/1.34  
% 2.62/1.34  %Foreground sorts:
% 2.62/1.34  
% 2.62/1.34  
% 2.62/1.34  %Background operators:
% 2.62/1.34  
% 2.62/1.34  
% 2.62/1.34  %Foreground operators:
% 2.62/1.34  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.62/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.62/1.34  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.62/1.34  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.62/1.34  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.62/1.34  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.62/1.34  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.62/1.34  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.62/1.34  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.62/1.34  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.62/1.34  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.62/1.34  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.62/1.34  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.62/1.34  tff('#skF_2', type, '#skF_2': $i).
% 2.62/1.34  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 2.62/1.34  tff('#skF_3', type, '#skF_3': $i).
% 2.62/1.34  tff('#skF_1', type, '#skF_1': $i).
% 2.62/1.34  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.62/1.34  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.62/1.34  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.62/1.34  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.62/1.34  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.62/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.62/1.34  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.62/1.34  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.62/1.34  tff('#skF_4', type, '#skF_4': $i).
% 2.62/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.62/1.34  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.62/1.34  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.62/1.34  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.62/1.34  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.62/1.34  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.62/1.34  
% 2.62/1.35  tff(f_122, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_funct_2)).
% 2.62/1.35  tff(f_89, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.62/1.35  tff(f_31, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 2.62/1.35  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 2.62/1.35  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.62/1.35  tff(f_56, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 2.62/1.35  tff(f_93, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.62/1.35  tff(f_111, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 2.62/1.35  tff(f_85, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: ((r2_hidden(B, k1_relat_1(A)) => ((C = k1_funct_1(A, B)) <=> r2_hidden(k4_tarski(B, C), A))) & (~r2_hidden(B, k1_relat_1(A)) => ((C = k1_funct_1(A, B)) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_funct_1)).
% 2.62/1.35  tff(f_63, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 2.62/1.35  tff(f_51, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, k1_tarski(D))) <=> (r2_hidden(A, C) & (B = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t129_zfmisc_1)).
% 2.62/1.35  tff(c_62, plain, (k1_funct_1('#skF_4', '#skF_3')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_122])).
% 2.62/1.35  tff(c_64, plain, (r2_hidden('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_122])).
% 2.62/1.35  tff(c_66, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', k1_tarski('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_122])).
% 2.62/1.35  tff(c_158, plain, (![C_76, A_77, B_78]: (v1_relat_1(C_76) | ~m1_subset_1(C_76, k1_zfmisc_1(k2_zfmisc_1(A_77, B_78))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.62/1.35  tff(c_162, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_66, c_158])).
% 2.62/1.35  tff(c_70, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_122])).
% 2.62/1.35  tff(c_6, plain, (![A_5]: (k5_xboole_0(A_5, A_5)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.62/1.35  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.62/1.35  tff(c_137, plain, (![A_73, B_74]: (k5_xboole_0(A_73, k3_xboole_0(A_73, B_74))=k4_xboole_0(A_73, B_74))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.62/1.35  tff(c_146, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k4_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_137])).
% 2.62/1.35  tff(c_149, plain, (![A_1]: (k4_xboole_0(A_1, A_1)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_146])).
% 2.62/1.35  tff(c_28, plain, (![B_39]: (k4_xboole_0(k1_tarski(B_39), k1_tarski(B_39))!=k1_tarski(B_39))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.62/1.35  tff(c_150, plain, (![B_39]: (k1_tarski(B_39)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_149, c_28])).
% 2.62/1.35  tff(c_68, plain, (v1_funct_2('#skF_4', '#skF_1', k1_tarski('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_122])).
% 2.62/1.35  tff(c_228, plain, (![A_106, B_107, C_108]: (k1_relset_1(A_106, B_107, C_108)=k1_relat_1(C_108) | ~m1_subset_1(C_108, k1_zfmisc_1(k2_zfmisc_1(A_106, B_107))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.62/1.35  tff(c_232, plain, (k1_relset_1('#skF_1', k1_tarski('#skF_2'), '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_66, c_228])).
% 2.62/1.35  tff(c_290, plain, (![B_139, A_140, C_141]: (k1_xboole_0=B_139 | k1_relset_1(A_140, B_139, C_141)=A_140 | ~v1_funct_2(C_141, A_140, B_139) | ~m1_subset_1(C_141, k1_zfmisc_1(k2_zfmisc_1(A_140, B_139))))), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.62/1.35  tff(c_293, plain, (k1_tarski('#skF_2')=k1_xboole_0 | k1_relset_1('#skF_1', k1_tarski('#skF_2'), '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', k1_tarski('#skF_2'))), inference(resolution, [status(thm)], [c_66, c_290])).
% 2.62/1.35  tff(c_296, plain, (k1_tarski('#skF_2')=k1_xboole_0 | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_232, c_293])).
% 2.62/1.35  tff(c_297, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_150, c_296])).
% 2.62/1.35  tff(c_250, plain, (![B_121, A_122]: (r2_hidden(k4_tarski(B_121, k1_funct_1(A_122, B_121)), A_122) | ~r2_hidden(B_121, k1_relat_1(A_122)) | ~v1_funct_1(A_122) | ~v1_relat_1(A_122))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.62/1.35  tff(c_32, plain, (![C_43, A_40, B_41]: (r2_hidden(C_43, A_40) | ~r2_hidden(C_43, B_41) | ~m1_subset_1(B_41, k1_zfmisc_1(A_40)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.62/1.35  tff(c_344, plain, (![B_155, A_156, A_157]: (r2_hidden(k4_tarski(B_155, k1_funct_1(A_156, B_155)), A_157) | ~m1_subset_1(A_156, k1_zfmisc_1(A_157)) | ~r2_hidden(B_155, k1_relat_1(A_156)) | ~v1_funct_1(A_156) | ~v1_relat_1(A_156))), inference(resolution, [status(thm)], [c_250, c_32])).
% 2.62/1.35  tff(c_24, plain, (![D_37, B_35, A_34, C_36]: (D_37=B_35 | ~r2_hidden(k4_tarski(A_34, B_35), k2_zfmisc_1(C_36, k1_tarski(D_37))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.62/1.35  tff(c_368, plain, (![A_162, B_163, D_164, C_165]: (k1_funct_1(A_162, B_163)=D_164 | ~m1_subset_1(A_162, k1_zfmisc_1(k2_zfmisc_1(C_165, k1_tarski(D_164)))) | ~r2_hidden(B_163, k1_relat_1(A_162)) | ~v1_funct_1(A_162) | ~v1_relat_1(A_162))), inference(resolution, [status(thm)], [c_344, c_24])).
% 2.62/1.35  tff(c_370, plain, (![B_163]: (k1_funct_1('#skF_4', B_163)='#skF_2' | ~r2_hidden(B_163, k1_relat_1('#skF_4')) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_66, c_368])).
% 2.62/1.35  tff(c_374, plain, (![B_166]: (k1_funct_1('#skF_4', B_166)='#skF_2' | ~r2_hidden(B_166, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_162, c_70, c_297, c_370])).
% 2.62/1.35  tff(c_388, plain, (k1_funct_1('#skF_4', '#skF_3')='#skF_2'), inference(resolution, [status(thm)], [c_64, c_374])).
% 2.62/1.35  tff(c_395, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_388])).
% 2.62/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.62/1.35  
% 2.62/1.35  Inference rules
% 2.62/1.35  ----------------------
% 2.62/1.35  #Ref     : 0
% 2.62/1.35  #Sup     : 69
% 2.62/1.35  #Fact    : 0
% 2.62/1.35  #Define  : 0
% 2.62/1.35  #Split   : 1
% 2.62/1.35  #Chain   : 0
% 2.62/1.35  #Close   : 0
% 2.62/1.35  
% 2.62/1.35  Ordering : KBO
% 2.62/1.35  
% 2.62/1.35  Simplification rules
% 2.62/1.35  ----------------------
% 2.62/1.35  #Subsume      : 3
% 2.62/1.35  #Demod        : 18
% 2.62/1.35  #Tautology    : 43
% 2.62/1.35  #SimpNegUnit  : 5
% 2.62/1.35  #BackRed      : 2
% 2.62/1.35  
% 2.62/1.35  #Partial instantiations: 0
% 2.62/1.35  #Strategies tried      : 1
% 2.62/1.35  
% 2.62/1.35  Timing (in seconds)
% 2.62/1.35  ----------------------
% 2.62/1.35  Preprocessing        : 0.34
% 2.62/1.35  Parsing              : 0.18
% 2.62/1.35  CNF conversion       : 0.02
% 2.62/1.35  Main loop            : 0.23
% 2.62/1.35  Inferencing          : 0.09
% 2.62/1.35  Reduction            : 0.07
% 2.62/1.35  Demodulation         : 0.05
% 2.62/1.35  BG Simplification    : 0.02
% 2.62/1.35  Subsumption          : 0.05
% 2.62/1.35  Abstraction          : 0.02
% 2.62/1.35  MUC search           : 0.00
% 2.62/1.35  Cooper               : 0.00
% 2.62/1.35  Total                : 0.61
% 2.62/1.35  Index Insertion      : 0.00
% 2.62/1.35  Index Deletion       : 0.00
% 2.62/1.35  Index Matching       : 0.00
% 2.62/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
