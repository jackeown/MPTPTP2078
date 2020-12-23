%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:11 EST 2020

% Result     : Theorem 2.50s
% Output     : CNFRefutation 2.81s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 103 expanded)
%              Number of leaves         :   39 (  54 expanded)
%              Depth                    :    9
%              Number of atoms          :  114 ( 216 expanded)
%              Number of equality atoms :   34 (  57 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_111,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,k1_tarski(B))
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
       => ( r2_hidden(C,A)
         => k1_funct_1(D,C) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_2)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_88,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_68,axiom,(
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

tff(f_78,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v5_relat_1(C,A)
        & v1_funct_1(C) )
     => ( r2_hidden(B,k1_relat_1(C))
       => m1_subset_1(k1_funct_1(C,B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t176_funct_1)).

tff(f_41,axiom,(
    ! [A] : ~ v1_xboole_0(k1_tarski(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_xboole_0)).

tff(f_50,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_32,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_100,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_funct_2)).

tff(f_43,axiom,(
    ! [A] : k1_setfam_1(k1_tarski(A)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_setfam_1)).

tff(f_44,axiom,(
    k1_setfam_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_setfam_1)).

tff(c_46,plain,(
    k1_funct_1('#skF_6','#skF_5') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_50,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3',k1_tarski('#skF_4')))) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_94,plain,(
    ! [C_42,A_43,B_44] :
      ( v1_relat_1(C_42)
      | ~ m1_subset_1(C_42,k1_zfmisc_1(k2_zfmisc_1(A_43,B_44))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_98,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_50,c_94])).

tff(c_54,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_107,plain,(
    ! [C_47,B_48,A_49] :
      ( v5_relat_1(C_47,B_48)
      | ~ m1_subset_1(C_47,k1_zfmisc_1(k2_zfmisc_1(A_49,B_48))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_111,plain,(
    v5_relat_1('#skF_6',k1_tarski('#skF_4')) ),
    inference(resolution,[status(thm)],[c_50,c_107])).

tff(c_34,plain,(
    ! [A_16,B_19] :
      ( k1_funct_1(A_16,B_19) = k1_xboole_0
      | r2_hidden(B_19,k1_relat_1(A_16))
      | ~ v1_funct_1(A_16)
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_182,plain,(
    ! [C_74,B_75,A_76] :
      ( m1_subset_1(k1_funct_1(C_74,B_75),A_76)
      | ~ r2_hidden(B_75,k1_relat_1(C_74))
      | ~ v1_funct_1(C_74)
      | ~ v5_relat_1(C_74,A_76)
      | ~ v1_relat_1(C_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_209,plain,(
    ! [A_79,B_80,A_81] :
      ( m1_subset_1(k1_funct_1(A_79,B_80),A_81)
      | ~ v5_relat_1(A_79,A_81)
      | k1_funct_1(A_79,B_80) = k1_xboole_0
      | ~ v1_funct_1(A_79)
      | ~ v1_relat_1(A_79) ) ),
    inference(resolution,[status(thm)],[c_34,c_182])).

tff(c_20,plain,(
    ! [A_12] : ~ v1_xboole_0(k1_tarski(A_12)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_99,plain,(
    ! [A_45,B_46] :
      ( r2_hidden(A_45,B_46)
      | v1_xboole_0(B_46)
      | ~ m1_subset_1(A_45,B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_2,plain,(
    ! [C_5,A_1] :
      ( C_5 = A_1
      | ~ r2_hidden(C_5,k1_tarski(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_103,plain,(
    ! [A_45,A_1] :
      ( A_45 = A_1
      | v1_xboole_0(k1_tarski(A_1))
      | ~ m1_subset_1(A_45,k1_tarski(A_1)) ) ),
    inference(resolution,[status(thm)],[c_99,c_2])).

tff(c_106,plain,(
    ! [A_45,A_1] :
      ( A_45 = A_1
      | ~ m1_subset_1(A_45,k1_tarski(A_1)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_103])).

tff(c_231,plain,(
    ! [A_84,B_85,A_86] :
      ( k1_funct_1(A_84,B_85) = A_86
      | ~ v5_relat_1(A_84,k1_tarski(A_86))
      | k1_funct_1(A_84,B_85) = k1_xboole_0
      | ~ v1_funct_1(A_84)
      | ~ v1_relat_1(A_84) ) ),
    inference(resolution,[status(thm)],[c_209,c_106])).

tff(c_233,plain,(
    ! [B_85] :
      ( k1_funct_1('#skF_6',B_85) = '#skF_4'
      | k1_funct_1('#skF_6',B_85) = k1_xboole_0
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_111,c_231])).

tff(c_241,plain,(
    ! [B_87] :
      ( k1_funct_1('#skF_6',B_87) = '#skF_4'
      | k1_funct_1('#skF_6',B_87) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_54,c_233])).

tff(c_253,plain,
    ( k1_xboole_0 != '#skF_4'
    | k1_funct_1('#skF_6','#skF_5') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_241,c_46])).

tff(c_262,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_253])).

tff(c_52,plain,(
    v1_funct_2('#skF_6','#skF_3',k1_tarski('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_48,plain,(
    r2_hidden('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_292,plain,(
    ! [D_92,C_93,B_94,A_95] :
      ( r2_hidden(k1_funct_1(D_92,C_93),B_94)
      | k1_xboole_0 = B_94
      | ~ r2_hidden(C_93,A_95)
      | ~ m1_subset_1(D_92,k1_zfmisc_1(k2_zfmisc_1(A_95,B_94)))
      | ~ v1_funct_2(D_92,A_95,B_94)
      | ~ v1_funct_1(D_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_376,plain,(
    ! [D_107,B_108] :
      ( r2_hidden(k1_funct_1(D_107,'#skF_5'),B_108)
      | k1_xboole_0 = B_108
      | ~ m1_subset_1(D_107,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_108)))
      | ~ v1_funct_2(D_107,'#skF_3',B_108)
      | ~ v1_funct_1(D_107) ) ),
    inference(resolution,[status(thm)],[c_48,c_292])).

tff(c_383,plain,
    ( r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_tarski('#skF_4'))
    | k1_tarski('#skF_4') = k1_xboole_0
    | ~ v1_funct_2('#skF_6','#skF_3',k1_tarski('#skF_4'))
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_50,c_376])).

tff(c_387,plain,
    ( r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_tarski('#skF_4'))
    | k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_383])).

tff(c_419,plain,(
    k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_387])).

tff(c_22,plain,(
    ! [A_13] : k1_setfam_1(k1_tarski(A_13)) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_457,plain,(
    k1_setfam_1(k1_xboole_0) = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_419,c_22])).

tff(c_24,plain,(
    k1_setfam_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_470,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_457,c_24])).

tff(c_472,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_262,c_470])).

tff(c_473,plain,(
    r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_tarski('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_387])).

tff(c_479,plain,(
    k1_funct_1('#skF_6','#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_473,c_2])).

tff(c_487,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_479])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:06:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.50/1.37  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.50/1.38  
% 2.50/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.50/1.38  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.50/1.38  
% 2.50/1.38  %Foreground sorts:
% 2.50/1.38  
% 2.50/1.38  
% 2.50/1.38  %Background operators:
% 2.50/1.38  
% 2.50/1.38  
% 2.50/1.38  %Foreground operators:
% 2.50/1.38  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.50/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.50/1.38  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.50/1.38  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.50/1.38  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.50/1.38  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.50/1.38  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.50/1.38  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.50/1.38  tff('#skF_5', type, '#skF_5': $i).
% 2.50/1.38  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.50/1.38  tff('#skF_6', type, '#skF_6': $i).
% 2.50/1.38  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.50/1.38  tff('#skF_3', type, '#skF_3': $i).
% 2.50/1.38  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.50/1.38  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.50/1.38  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.50/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.50/1.38  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.50/1.38  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.50/1.38  tff('#skF_4', type, '#skF_4': $i).
% 2.50/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.50/1.38  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.50/1.38  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.50/1.38  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.50/1.38  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.50/1.38  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.50/1.38  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.50/1.38  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.50/1.38  
% 2.81/1.39  tff(f_111, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_funct_2)).
% 2.81/1.39  tff(f_82, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.81/1.39  tff(f_88, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.81/1.39  tff(f_68, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: ((r2_hidden(B, k1_relat_1(A)) => ((C = k1_funct_1(A, B)) <=> r2_hidden(k4_tarski(B, C), A))) & (~r2_hidden(B, k1_relat_1(A)) => ((C = k1_funct_1(A, B)) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_funct_1)).
% 2.81/1.39  tff(f_78, axiom, (![A, B, C]: (((v1_relat_1(C) & v5_relat_1(C, A)) & v1_funct_1(C)) => (r2_hidden(B, k1_relat_1(C)) => m1_subset_1(k1_funct_1(C, B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t176_funct_1)).
% 2.81/1.39  tff(f_41, axiom, (![A]: ~v1_xboole_0(k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_xboole_0)).
% 2.81/1.39  tff(f_50, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 2.81/1.39  tff(f_32, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 2.81/1.39  tff(f_100, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_funct_2)).
% 2.81/1.39  tff(f_43, axiom, (![A]: (k1_setfam_1(k1_tarski(A)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_setfam_1)).
% 2.81/1.39  tff(f_44, axiom, (k1_setfam_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_setfam_1)).
% 2.81/1.39  tff(c_46, plain, (k1_funct_1('#skF_6', '#skF_5')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.81/1.39  tff(c_50, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', k1_tarski('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.81/1.39  tff(c_94, plain, (![C_42, A_43, B_44]: (v1_relat_1(C_42) | ~m1_subset_1(C_42, k1_zfmisc_1(k2_zfmisc_1(A_43, B_44))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.81/1.39  tff(c_98, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_50, c_94])).
% 2.81/1.39  tff(c_54, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.81/1.39  tff(c_107, plain, (![C_47, B_48, A_49]: (v5_relat_1(C_47, B_48) | ~m1_subset_1(C_47, k1_zfmisc_1(k2_zfmisc_1(A_49, B_48))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.81/1.39  tff(c_111, plain, (v5_relat_1('#skF_6', k1_tarski('#skF_4'))), inference(resolution, [status(thm)], [c_50, c_107])).
% 2.81/1.39  tff(c_34, plain, (![A_16, B_19]: (k1_funct_1(A_16, B_19)=k1_xboole_0 | r2_hidden(B_19, k1_relat_1(A_16)) | ~v1_funct_1(A_16) | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.81/1.39  tff(c_182, plain, (![C_74, B_75, A_76]: (m1_subset_1(k1_funct_1(C_74, B_75), A_76) | ~r2_hidden(B_75, k1_relat_1(C_74)) | ~v1_funct_1(C_74) | ~v5_relat_1(C_74, A_76) | ~v1_relat_1(C_74))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.81/1.39  tff(c_209, plain, (![A_79, B_80, A_81]: (m1_subset_1(k1_funct_1(A_79, B_80), A_81) | ~v5_relat_1(A_79, A_81) | k1_funct_1(A_79, B_80)=k1_xboole_0 | ~v1_funct_1(A_79) | ~v1_relat_1(A_79))), inference(resolution, [status(thm)], [c_34, c_182])).
% 2.81/1.39  tff(c_20, plain, (![A_12]: (~v1_xboole_0(k1_tarski(A_12)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.81/1.39  tff(c_99, plain, (![A_45, B_46]: (r2_hidden(A_45, B_46) | v1_xboole_0(B_46) | ~m1_subset_1(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.81/1.39  tff(c_2, plain, (![C_5, A_1]: (C_5=A_1 | ~r2_hidden(C_5, k1_tarski(A_1)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.81/1.39  tff(c_103, plain, (![A_45, A_1]: (A_45=A_1 | v1_xboole_0(k1_tarski(A_1)) | ~m1_subset_1(A_45, k1_tarski(A_1)))), inference(resolution, [status(thm)], [c_99, c_2])).
% 2.81/1.39  tff(c_106, plain, (![A_45, A_1]: (A_45=A_1 | ~m1_subset_1(A_45, k1_tarski(A_1)))), inference(negUnitSimplification, [status(thm)], [c_20, c_103])).
% 2.81/1.39  tff(c_231, plain, (![A_84, B_85, A_86]: (k1_funct_1(A_84, B_85)=A_86 | ~v5_relat_1(A_84, k1_tarski(A_86)) | k1_funct_1(A_84, B_85)=k1_xboole_0 | ~v1_funct_1(A_84) | ~v1_relat_1(A_84))), inference(resolution, [status(thm)], [c_209, c_106])).
% 2.81/1.39  tff(c_233, plain, (![B_85]: (k1_funct_1('#skF_6', B_85)='#skF_4' | k1_funct_1('#skF_6', B_85)=k1_xboole_0 | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_111, c_231])).
% 2.81/1.39  tff(c_241, plain, (![B_87]: (k1_funct_1('#skF_6', B_87)='#skF_4' | k1_funct_1('#skF_6', B_87)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_98, c_54, c_233])).
% 2.81/1.39  tff(c_253, plain, (k1_xboole_0!='#skF_4' | k1_funct_1('#skF_6', '#skF_5')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_241, c_46])).
% 2.81/1.39  tff(c_262, plain, (k1_xboole_0!='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_46, c_253])).
% 2.81/1.39  tff(c_52, plain, (v1_funct_2('#skF_6', '#skF_3', k1_tarski('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.81/1.39  tff(c_48, plain, (r2_hidden('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.81/1.39  tff(c_292, plain, (![D_92, C_93, B_94, A_95]: (r2_hidden(k1_funct_1(D_92, C_93), B_94) | k1_xboole_0=B_94 | ~r2_hidden(C_93, A_95) | ~m1_subset_1(D_92, k1_zfmisc_1(k2_zfmisc_1(A_95, B_94))) | ~v1_funct_2(D_92, A_95, B_94) | ~v1_funct_1(D_92))), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.81/1.39  tff(c_376, plain, (![D_107, B_108]: (r2_hidden(k1_funct_1(D_107, '#skF_5'), B_108) | k1_xboole_0=B_108 | ~m1_subset_1(D_107, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_108))) | ~v1_funct_2(D_107, '#skF_3', B_108) | ~v1_funct_1(D_107))), inference(resolution, [status(thm)], [c_48, c_292])).
% 2.81/1.39  tff(c_383, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4')) | k1_tarski('#skF_4')=k1_xboole_0 | ~v1_funct_2('#skF_6', '#skF_3', k1_tarski('#skF_4')) | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_50, c_376])).
% 2.81/1.39  tff(c_387, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4')) | k1_tarski('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_383])).
% 2.81/1.39  tff(c_419, plain, (k1_tarski('#skF_4')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_387])).
% 2.81/1.39  tff(c_22, plain, (![A_13]: (k1_setfam_1(k1_tarski(A_13))=A_13)), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.81/1.39  tff(c_457, plain, (k1_setfam_1(k1_xboole_0)='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_419, c_22])).
% 2.81/1.39  tff(c_24, plain, (k1_setfam_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.81/1.39  tff(c_470, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_457, c_24])).
% 2.81/1.39  tff(c_472, plain, $false, inference(negUnitSimplification, [status(thm)], [c_262, c_470])).
% 2.81/1.39  tff(c_473, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4'))), inference(splitRight, [status(thm)], [c_387])).
% 2.81/1.39  tff(c_479, plain, (k1_funct_1('#skF_6', '#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_473, c_2])).
% 2.81/1.39  tff(c_487, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_479])).
% 2.81/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.81/1.39  
% 2.81/1.39  Inference rules
% 2.81/1.39  ----------------------
% 2.81/1.39  #Ref     : 0
% 2.81/1.39  #Sup     : 94
% 2.81/1.39  #Fact    : 1
% 2.81/1.39  #Define  : 0
% 2.81/1.39  #Split   : 1
% 2.81/1.39  #Chain   : 0
% 2.81/1.39  #Close   : 0
% 2.81/1.39  
% 2.81/1.39  Ordering : KBO
% 2.81/1.39  
% 2.81/1.39  Simplification rules
% 2.81/1.39  ----------------------
% 2.81/1.39  #Subsume      : 4
% 2.81/1.39  #Demod        : 39
% 2.81/1.39  #Tautology    : 24
% 2.81/1.39  #SimpNegUnit  : 5
% 2.81/1.39  #BackRed      : 4
% 2.81/1.39  
% 2.81/1.39  #Partial instantiations: 0
% 2.81/1.39  #Strategies tried      : 1
% 2.81/1.39  
% 2.81/1.39  Timing (in seconds)
% 2.81/1.39  ----------------------
% 2.81/1.40  Preprocessing        : 0.32
% 2.81/1.40  Parsing              : 0.17
% 2.81/1.40  CNF conversion       : 0.02
% 2.81/1.40  Main loop            : 0.31
% 2.81/1.40  Inferencing          : 0.11
% 2.81/1.40  Reduction            : 0.09
% 2.81/1.40  Demodulation         : 0.06
% 2.81/1.40  BG Simplification    : 0.02
% 2.81/1.40  Subsumption          : 0.07
% 2.81/1.40  Abstraction          : 0.02
% 2.81/1.40  MUC search           : 0.00
% 2.81/1.40  Cooper               : 0.00
% 2.81/1.40  Total                : 0.66
% 2.81/1.40  Index Insertion      : 0.00
% 2.81/1.40  Index Deletion       : 0.00
% 2.81/1.40  Index Matching       : 0.00
% 2.81/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
