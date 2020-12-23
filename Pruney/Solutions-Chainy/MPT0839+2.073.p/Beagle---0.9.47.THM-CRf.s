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
% DateTime   : Thu Dec  3 10:08:31 EST 2020

% Result     : Theorem 2.43s
% Output     : CNFRefutation 2.74s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 131 expanded)
%              Number of leaves         :   31 (  57 expanded)
%              Depth                    :    8
%              Number of atoms          :   91 ( 252 expanded)
%              Number of equality atoms :   29 (  67 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_93,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ~ v1_xboole_0(B)
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
               => ~ ( k2_relset_1(B,A,C) != k1_xboole_0
                    & ! [D] :
                        ( m1_subset_1(D,B)
                       => ~ r2_hidden(D,k1_relset_1(B,A,C)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_relset_1)).

tff(f_49,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_47,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_55,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k1_relat_1(A) = k1_xboole_0
      <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

tff(f_34,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
        <=> r2_hidden(C,B) )
     => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).

tff(f_60,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k1_relset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_relset_1)).

tff(f_40,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(c_32,plain,(
    k2_relset_1('#skF_4','#skF_3','#skF_5') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_16,plain,(
    ! [A_11,B_12] : v1_relat_1(k2_zfmisc_1(A_11,B_12)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_34,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_47,plain,(
    ! [B_43,A_44] :
      ( v1_relat_1(B_43)
      | ~ m1_subset_1(B_43,k1_zfmisc_1(A_44))
      | ~ v1_relat_1(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_50,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_4','#skF_3')) ),
    inference(resolution,[status(thm)],[c_34,c_47])).

tff(c_53,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_50])).

tff(c_18,plain,(
    ! [A_13] :
      ( k1_relat_1(A_13) = k1_xboole_0
      | k2_relat_1(A_13) != k1_xboole_0
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_58,plain,
    ( k1_relat_1('#skF_5') = k1_xboole_0
    | k2_relat_1('#skF_5') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_53,c_18])).

tff(c_59,plain,(
    k2_relat_1('#skF_5') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_60,plain,(
    ! [A_46] :
      ( k2_relat_1(A_46) = k1_xboole_0
      | k1_relat_1(A_46) != k1_xboole_0
      | ~ v1_relat_1(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_63,plain,
    ( k2_relat_1('#skF_5') = k1_xboole_0
    | k1_relat_1('#skF_5') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_53,c_60])).

tff(c_69,plain,(
    k1_relat_1('#skF_5') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_59,c_63])).

tff(c_10,plain,(
    ! [A_4] : r1_tarski(k1_xboole_0,A_4) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_129,plain,(
    ! [A_68,B_69] :
      ( r2_hidden('#skF_1'(A_68,B_69),B_69)
      | r2_hidden('#skF_2'(A_68,B_69),A_68)
      | B_69 = A_68 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_22,plain,(
    ! [B_15,A_14] :
      ( ~ r1_tarski(B_15,A_14)
      | ~ r2_hidden(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_205,plain,(
    ! [A_77,B_78] :
      ( ~ r1_tarski(A_77,'#skF_2'(A_77,B_78))
      | r2_hidden('#skF_1'(A_77,B_78),B_78)
      | B_78 = A_77 ) ),
    inference(resolution,[status(thm)],[c_129,c_22])).

tff(c_262,plain,(
    ! [B_83] :
      ( r2_hidden('#skF_1'(k1_xboole_0,B_83),B_83)
      | k1_xboole_0 = B_83 ) ),
    inference(resolution,[status(thm)],[c_10,c_205])).

tff(c_102,plain,(
    ! [A_62,B_63,C_64] :
      ( k1_relset_1(A_62,B_63,C_64) = k1_relat_1(C_64)
      | ~ m1_subset_1(C_64,k1_zfmisc_1(k2_zfmisc_1(A_62,B_63))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_106,plain,(
    k1_relset_1('#skF_4','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_34,c_102])).

tff(c_30,plain,(
    ! [D_36] :
      ( ~ r2_hidden(D_36,k1_relset_1('#skF_4','#skF_3','#skF_5'))
      | ~ m1_subset_1(D_36,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_107,plain,(
    ! [D_36] :
      ( ~ r2_hidden(D_36,k1_relat_1('#skF_5'))
      | ~ m1_subset_1(D_36,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_30])).

tff(c_270,plain,
    ( ~ m1_subset_1('#skF_1'(k1_xboole_0,k1_relat_1('#skF_5')),'#skF_4')
    | k1_relat_1('#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_262,c_107])).

tff(c_283,plain,(
    ~ m1_subset_1('#skF_1'(k1_xboole_0,k1_relat_1('#skF_5')),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_69,c_270])).

tff(c_209,plain,(
    ! [B_78] :
      ( r2_hidden('#skF_1'(k1_xboole_0,B_78),B_78)
      | k1_xboole_0 = B_78 ) ),
    inference(resolution,[status(thm)],[c_10,c_205])).

tff(c_210,plain,(
    ! [A_79,B_80,C_81] :
      ( m1_subset_1(k1_relset_1(A_79,B_80,C_81),k1_zfmisc_1(A_79))
      | ~ m1_subset_1(C_81,k1_zfmisc_1(k2_zfmisc_1(A_79,B_80))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_226,plain,
    ( m1_subset_1(k1_relat_1('#skF_5'),k1_zfmisc_1('#skF_4'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_106,c_210])).

tff(c_232,plain,(
    m1_subset_1(k1_relat_1('#skF_5'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_226])).

tff(c_12,plain,(
    ! [A_5,C_7,B_6] :
      ( m1_subset_1(A_5,C_7)
      | ~ m1_subset_1(B_6,k1_zfmisc_1(C_7))
      | ~ r2_hidden(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_287,plain,(
    ! [A_84] :
      ( m1_subset_1(A_84,'#skF_4')
      | ~ r2_hidden(A_84,k1_relat_1('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_232,c_12])).

tff(c_291,plain,
    ( m1_subset_1('#skF_1'(k1_xboole_0,k1_relat_1('#skF_5')),'#skF_4')
    | k1_relat_1('#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_209,c_287])).

tff(c_319,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_69,c_283,c_291])).

tff(c_321,plain,(
    k2_relat_1('#skF_5') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_410,plain,(
    ! [A_105,B_106,C_107] :
      ( k2_relset_1(A_105,B_106,C_107) = k2_relat_1(C_107)
      | ~ m1_subset_1(C_107,k1_zfmisc_1(k2_zfmisc_1(A_105,B_106))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_413,plain,(
    k2_relset_1('#skF_4','#skF_3','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_34,c_410])).

tff(c_415,plain,(
    k2_relset_1('#skF_4','#skF_3','#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_321,c_413])).

tff(c_417,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_415])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 13:09:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.43/1.46  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.71/1.46  
% 2.71/1.46  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.74/1.47  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.74/1.47  
% 2.74/1.47  %Foreground sorts:
% 2.74/1.47  
% 2.74/1.47  
% 2.74/1.47  %Background operators:
% 2.74/1.47  
% 2.74/1.47  
% 2.74/1.47  %Foreground operators:
% 2.74/1.47  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.74/1.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.74/1.47  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.74/1.47  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.74/1.47  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.74/1.47  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.74/1.47  tff('#skF_5', type, '#skF_5': $i).
% 2.74/1.47  tff('#skF_3', type, '#skF_3': $i).
% 2.74/1.47  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.74/1.47  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.74/1.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.74/1.47  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.74/1.47  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.74/1.47  tff('#skF_4', type, '#skF_4': $i).
% 2.74/1.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.74/1.47  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.74/1.47  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.74/1.47  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.74/1.47  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.74/1.47  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.74/1.47  
% 2.74/1.48  tff(f_93, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => ~(~(k2_relset_1(B, A, C) = k1_xboole_0) & (![D]: (m1_subset_1(D, B) => ~r2_hidden(D, k1_relset_1(B, A, C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_relset_1)).
% 2.74/1.48  tff(f_49, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.74/1.48  tff(f_47, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.74/1.48  tff(f_55, axiom, (![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_relat_1)).
% 2.74/1.48  tff(f_34, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.74/1.48  tff(f_32, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) <=> r2_hidden(C, B))) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tarski)).
% 2.74/1.48  tff(f_60, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 2.74/1.48  tff(f_68, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.74/1.48  tff(f_64, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k1_relset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_relset_1)).
% 2.74/1.48  tff(f_40, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 2.74/1.48  tff(f_72, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.74/1.48  tff(c_32, plain, (k2_relset_1('#skF_4', '#skF_3', '#skF_5')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.74/1.48  tff(c_16, plain, (![A_11, B_12]: (v1_relat_1(k2_zfmisc_1(A_11, B_12)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.74/1.48  tff(c_34, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.74/1.48  tff(c_47, plain, (![B_43, A_44]: (v1_relat_1(B_43) | ~m1_subset_1(B_43, k1_zfmisc_1(A_44)) | ~v1_relat_1(A_44))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.74/1.48  tff(c_50, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_4', '#skF_3'))), inference(resolution, [status(thm)], [c_34, c_47])).
% 2.74/1.48  tff(c_53, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_50])).
% 2.74/1.48  tff(c_18, plain, (![A_13]: (k1_relat_1(A_13)=k1_xboole_0 | k2_relat_1(A_13)!=k1_xboole_0 | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.74/1.48  tff(c_58, plain, (k1_relat_1('#skF_5')=k1_xboole_0 | k2_relat_1('#skF_5')!=k1_xboole_0), inference(resolution, [status(thm)], [c_53, c_18])).
% 2.74/1.48  tff(c_59, plain, (k2_relat_1('#skF_5')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_58])).
% 2.74/1.48  tff(c_60, plain, (![A_46]: (k2_relat_1(A_46)=k1_xboole_0 | k1_relat_1(A_46)!=k1_xboole_0 | ~v1_relat_1(A_46))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.74/1.48  tff(c_63, plain, (k2_relat_1('#skF_5')=k1_xboole_0 | k1_relat_1('#skF_5')!=k1_xboole_0), inference(resolution, [status(thm)], [c_53, c_60])).
% 2.74/1.48  tff(c_69, plain, (k1_relat_1('#skF_5')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_59, c_63])).
% 2.74/1.48  tff(c_10, plain, (![A_4]: (r1_tarski(k1_xboole_0, A_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.74/1.48  tff(c_129, plain, (![A_68, B_69]: (r2_hidden('#skF_1'(A_68, B_69), B_69) | r2_hidden('#skF_2'(A_68, B_69), A_68) | B_69=A_68)), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.74/1.48  tff(c_22, plain, (![B_15, A_14]: (~r1_tarski(B_15, A_14) | ~r2_hidden(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.74/1.48  tff(c_205, plain, (![A_77, B_78]: (~r1_tarski(A_77, '#skF_2'(A_77, B_78)) | r2_hidden('#skF_1'(A_77, B_78), B_78) | B_78=A_77)), inference(resolution, [status(thm)], [c_129, c_22])).
% 2.74/1.48  tff(c_262, plain, (![B_83]: (r2_hidden('#skF_1'(k1_xboole_0, B_83), B_83) | k1_xboole_0=B_83)), inference(resolution, [status(thm)], [c_10, c_205])).
% 2.74/1.48  tff(c_102, plain, (![A_62, B_63, C_64]: (k1_relset_1(A_62, B_63, C_64)=k1_relat_1(C_64) | ~m1_subset_1(C_64, k1_zfmisc_1(k2_zfmisc_1(A_62, B_63))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.74/1.48  tff(c_106, plain, (k1_relset_1('#skF_4', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_34, c_102])).
% 2.74/1.48  tff(c_30, plain, (![D_36]: (~r2_hidden(D_36, k1_relset_1('#skF_4', '#skF_3', '#skF_5')) | ~m1_subset_1(D_36, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.74/1.48  tff(c_107, plain, (![D_36]: (~r2_hidden(D_36, k1_relat_1('#skF_5')) | ~m1_subset_1(D_36, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_106, c_30])).
% 2.74/1.48  tff(c_270, plain, (~m1_subset_1('#skF_1'(k1_xboole_0, k1_relat_1('#skF_5')), '#skF_4') | k1_relat_1('#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_262, c_107])).
% 2.74/1.48  tff(c_283, plain, (~m1_subset_1('#skF_1'(k1_xboole_0, k1_relat_1('#skF_5')), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_69, c_270])).
% 2.74/1.48  tff(c_209, plain, (![B_78]: (r2_hidden('#skF_1'(k1_xboole_0, B_78), B_78) | k1_xboole_0=B_78)), inference(resolution, [status(thm)], [c_10, c_205])).
% 2.74/1.48  tff(c_210, plain, (![A_79, B_80, C_81]: (m1_subset_1(k1_relset_1(A_79, B_80, C_81), k1_zfmisc_1(A_79)) | ~m1_subset_1(C_81, k1_zfmisc_1(k2_zfmisc_1(A_79, B_80))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.74/1.48  tff(c_226, plain, (m1_subset_1(k1_relat_1('#skF_5'), k1_zfmisc_1('#skF_4')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_106, c_210])).
% 2.74/1.48  tff(c_232, plain, (m1_subset_1(k1_relat_1('#skF_5'), k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_226])).
% 2.74/1.48  tff(c_12, plain, (![A_5, C_7, B_6]: (m1_subset_1(A_5, C_7) | ~m1_subset_1(B_6, k1_zfmisc_1(C_7)) | ~r2_hidden(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.74/1.48  tff(c_287, plain, (![A_84]: (m1_subset_1(A_84, '#skF_4') | ~r2_hidden(A_84, k1_relat_1('#skF_5')))), inference(resolution, [status(thm)], [c_232, c_12])).
% 2.74/1.48  tff(c_291, plain, (m1_subset_1('#skF_1'(k1_xboole_0, k1_relat_1('#skF_5')), '#skF_4') | k1_relat_1('#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_209, c_287])).
% 2.74/1.48  tff(c_319, plain, $false, inference(negUnitSimplification, [status(thm)], [c_69, c_283, c_291])).
% 2.74/1.48  tff(c_321, plain, (k2_relat_1('#skF_5')=k1_xboole_0), inference(splitRight, [status(thm)], [c_58])).
% 2.74/1.48  tff(c_410, plain, (![A_105, B_106, C_107]: (k2_relset_1(A_105, B_106, C_107)=k2_relat_1(C_107) | ~m1_subset_1(C_107, k1_zfmisc_1(k2_zfmisc_1(A_105, B_106))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.74/1.48  tff(c_413, plain, (k2_relset_1('#skF_4', '#skF_3', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_34, c_410])).
% 2.74/1.48  tff(c_415, plain, (k2_relset_1('#skF_4', '#skF_3', '#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_321, c_413])).
% 2.74/1.48  tff(c_417, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_415])).
% 2.74/1.48  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.74/1.48  
% 2.74/1.48  Inference rules
% 2.74/1.48  ----------------------
% 2.74/1.48  #Ref     : 0
% 2.74/1.48  #Sup     : 74
% 2.74/1.48  #Fact    : 0
% 2.74/1.48  #Define  : 0
% 2.74/1.48  #Split   : 2
% 2.74/1.48  #Chain   : 0
% 2.74/1.48  #Close   : 0
% 2.74/1.48  
% 2.74/1.48  Ordering : KBO
% 2.74/1.48  
% 2.74/1.48  Simplification rules
% 2.74/1.48  ----------------------
% 2.74/1.48  #Subsume      : 2
% 2.74/1.48  #Demod        : 9
% 2.74/1.48  #Tautology    : 27
% 2.74/1.48  #SimpNegUnit  : 5
% 2.74/1.48  #BackRed      : 2
% 2.74/1.48  
% 2.74/1.48  #Partial instantiations: 0
% 2.74/1.48  #Strategies tried      : 1
% 2.74/1.48  
% 2.74/1.48  Timing (in seconds)
% 2.74/1.48  ----------------------
% 2.74/1.48  Preprocessing        : 0.40
% 2.74/1.48  Parsing              : 0.24
% 2.74/1.48  CNF conversion       : 0.02
% 2.74/1.48  Main loop            : 0.25
% 2.74/1.48  Inferencing          : 0.10
% 2.74/1.48  Reduction            : 0.07
% 2.74/1.48  Demodulation         : 0.04
% 2.74/1.48  BG Simplification    : 0.01
% 2.74/1.48  Subsumption          : 0.04
% 2.74/1.48  Abstraction          : 0.02
% 2.74/1.49  MUC search           : 0.00
% 2.74/1.49  Cooper               : 0.00
% 2.74/1.49  Total                : 0.68
% 2.74/1.49  Index Insertion      : 0.00
% 2.74/1.49  Index Deletion       : 0.00
% 2.74/1.49  Index Matching       : 0.00
% 2.74/1.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
